{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes    #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds     #-}
{-# LANGUAGE PolyKinds     #-}
{-# LANGUAGE GADTs         #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Data.Digems.Patch.Merge where

import Data.Proxy
import Data.Type.Equality
import Data.Functor.Const
import Data.Functor.Sum
import qualified Data.Map as M
import qualified Data.Set as S
import Data.List (nub, sort)

import Control.Monad
import Control.Monad.State
import Control.Monad.Writer hiding (Sum)
import Control.Monad.Identity
import Control.Monad.Except

import Generics.MRSOP.Util
import Generics.MRSOP.Base
import Generics.MRSOP.Digems.Treefix
import Generics.MRSOP.Digems.Digest

import Data.Exists
import qualified Data.WordTrie as T
import Data.Digems.Patch
import Data.Digems.Patch.Diff
import Data.Digems.Change
import Data.Digems.Change.Apply
import Data.Digems.Change.Classify
import Data.Digems.MetaVar

import Debug.Trace


-- * Merging Treefixes
--
-- $mergingtreefixes
--
-- After merging two patches, we might end up with a conflict.
-- That is, two changes that can't be reconciled.

-- |Hence, a conflict is simply two changes together.
data Conflict :: (kon -> *) -> [[[Atom kon]]] -> Atom kon -> * where
  Conflict :: String
           -> RawPatch ki codes at
           -> RawPatch ki codes at
           -> Conflict ki codes at

-- |A 'PatchC' is a patch with potential conflicts inside
type PatchC ki codes ix
  = UTx ki codes (Sum (Conflict ki codes) (CChange ki codes)) (I ix)

-- |Tries to cast a 'PatchC' back to a 'Patch'. Naturally,
--  this is only possible if the patch has no conflicts.
noConflicts :: PatchC ki codes ix -> Maybe (Patch ki codes ix)
noConflicts = utxMapM rmvInL
  where
    rmvInL (InL _) = Nothing
    rmvInL (InR x) = Just x

-- |Returns the labels of the conflicts ina a patch.
getConflicts :: (ShowHO ki) => PatchC ki codes ix -> [String]
getConflicts = snd . runWriter . utxMapM go
  where
    go x@(InL (Conflict str _ _)) = tell [show str] >> return x
    go x                          = return x

-- |We might need to issue new variables, hence we need a 'FreshM'
-- monad do issue them correctly;
type FreshM = State Int

-- |runs a 'FreshM' computation over the names of a patch
withFreshNamesFrom :: FreshM a -> Patch ki codes ix -> a
withFreshNamesFrom comp p = evalState comp maxVar
  where
    maxVar = let vs = S.unions $ utxGetHolesWith' (S.map (exElim metavarGet) . cCtxVars) p
              in maybe 0 id $ S.lookupMax vs 

freshMetaVar :: FreshM Int
freshMetaVar = modify (+1) >> get

-- |A merge of @p@ over @q@, denoted @p // q@, is the adaptation
--  of @p@ so that it could be applied to an element in the
--  image of @q@.
(//) :: ( Applicable ki codes (UTx2 ki codes)
        , HasDatatypeInfo ki fam codes 
        )
     => Patch ki codes ix
     -> Patch ki codes ix
     -> PatchC ki codes ix
p // q = utxJoin $ (utxMapM (uncurry' reconcile) $ utxLCP p q)
                   `withFreshNamesFrom` p

-- |The 'reconcile' function will try to reconcile disagreeing
--  patches.
--
--  Precondition: before calling @reconcile p q@, make sure
--                @p@ and @q@ are different.
reconcile :: forall ki codes fam at
           . ( Applicable ki codes (UTx2 ki codes)
             , HasDatatypeInfo ki fam codes 
             ) 
          => RawPatch ki codes at
          -> RawPatch ki codes at
          -> FreshM (UTx ki codes (Sum (Conflict ki codes) (CChange ki codes)) at)
reconcile p q
  -- If both patches are alpha-equivalent, we return a copy.
  | patchEq p q  = return $ UTxHole $ InR $ makeCopyFrom (distrCChange p)
{-
  -- TODO: check that these are guaranteed by the algo below
  -- When one of the patches is a copy, this is easy. We borrow
  -- from residual theory and return the first one.
  | patchIsCpy p = trace "1" $ utxMap InR p
  | patchIsCpy q = trace "2" $ utxMap InR p
-}
-- Otherwise, this is slightly more involved, but it is intuitively simple.
  | otherwise    =
    -- First we translate both patches to a 'spined change' representation.
    let sp = utxJoin $ utxMap (uncurry' utxLCP . unCMatch) p
        sq = utxJoin $ utxMap (uncurry' utxLCP . unCMatch) q -- spinedChange q
     in do
      res0 <- process sp sq
      case res0 of
          CantReconcile     -> return $ UTxHole $ InL $ Conflict "conf" p q
          ReturnNominator   -> return $ utxMap InR p
          InstDenominator v -> return $ UTxHole $
            case runExcept $ transport (scIns sq) v of
              Left err -> InL $ Conflict (show err) p q
              Right r  -> case utx2change r of
                            Nothing  -> InL $ Conflict "chg" p q
                            Just res -> InR res 

type UTx2 ki codes
  = UTx ki codes (MetaVarIK ki) :*: UTx ki codes (MetaVarIK ki)
type UTxUTx2 ki codes
  = UTx ki codes (UTx2 ki codes)

utx2distr :: UTxUTx2 ki codes at -> UTx2 ki codes at
utx2distr x = (scDel x :*: scIns x)

instance (TestEquality f) => TestEquality (f :*: g) where
  testEquality x y = testEquality (fst' x) (fst' y)

instance HasIKProjInj ki (UTx2 ki codes) where
  konInj  ki = (konInj ki :*: konInj ki)
  varProj p (Pair f _) = varProj p f

utx2change :: UTxUTx2 ki codes at -> Maybe (CChange ki codes at)
utx2change x = cmatch' (scDel x) (scIns x)

data ProcessOutcome ki codes
  = ReturnNominator
  | InstDenominator (Subst ki codes (UTx2 ki codes))
  | CantReconcile

fst' :: (f :*: g) x -> f x
fst' (Pair a _) = a

snd' :: (f :*: g) x -> g x
snd' (Pair _ b) = b

scDel :: UTxUTx2 ki codes at
      -> UTx ki codes (MetaVarIK ki) at
scDel = utxJoin . utxMap fst' 

scIns :: UTxUTx2 ki codes at
      -> UTx ki codes (MetaVarIK ki) at
scIns = utxJoin . utxMap snd'

-- |Checks whether a variable is a rawCpy, note that we need
--  a map that checks occurences of this variable.
rawCpy :: M.Map Int Int
       -> (UTx ki codes (MetaVarIK ki) :*: UTx ki codes (MetaVarIK ki)) at
       -> Bool
rawCpy ar (UTxHole v1 :*: UTxHole v2) = metavarGet v1 == metavarGet v2
                                     && M.lookup (metavarGet v1) ar == Just 1
rawCpy ar _                           = False

simpleCopy :: (UTx ki codes (MetaVarIK ki) :*: UTx ki codes (MetaVarIK ki)) at -> Bool
simpleCopy (UTxHole v1 :*: UTxHole v2) = metavarGet v1 == metavarGet v2
simpleCopy _ = False

isLocalIns :: UTx2 ki codes at -> Bool
isLocalIns (UTxHole _ :*: UTxPeel _ _) = True
isLocalIns _                           = False

arityMap :: UTx ki codes (MetaVarIK ki) at -> M.Map Int Int
arityMap = go . utxGetHolesWith' metavarGet
  where
    go []     = M.empty
    go (v:vs) = M.alter (Just . maybe 1 (+1)) v (go vs)


instance ShowHO x => Show (Exists x) where
  show (Exists x) = showHO x

-- |This will process two changes, represented as a spine and
-- inner changes, into a potential merged patch. The result of @process sp sq@
-- is supposed to instruct how to construct a patch that
-- can be applied to the image @sq@.
--
-- We do so by traversing the places where both @sp@ and @sq@ differ.
-- While we perform this traversal we instantiate a valuation of
-- potential substitutions, which might be needed in case we
-- need to adapt @sp@ to @sq@. After we are done, we know whether
-- we need to adapt @sp@, return @sp@ as is, or there is a conflict.
--
process :: (Applicable ki codes (UTx2 ki codes))
        => UTxUTx2 ki codes at -> UTxUTx2 ki codes at
        -> FreshM (ProcessOutcome ki codes)
process sp sq =
  case and <$> mapM (exElim $ uncurry' step1) phiD of
    Nothing    -> return CantReconcile
    Just True  -> if any (exElim $ uncurry' insins) phiID
                  then return CantReconcile
                  else return ReturnNominator
    Just False -> do
      partial <- runStateT (and <$> mapM (exElim $ uncurry' step2) phiID) M.empty
      case partial of
        (False , _) -> return CantReconcile
        (True  , s) -> return $ InstDenominator s
  where
    (delsp :*: _) = utx2distr sp
    phiD  = utxGetHolesWith' Exists $ utxLCP delsp sq
    phiID = utxGetHolesWith' Exists $ utxLCP sp sq

    -- The thing is, 'chg' is a true copy only if v2 occurs only once
    -- within the whole of 'sq'
    -- counts how many times a variable appears in 'sq'
    varmap = arityMap (snd' (utx2distr sq))
    m var = maybe 0 id $ M.lookup var varmap

    maxVar = case M.toDescList varmap of
               []        -> 0
               ((v,_):_) -> v

    -- |Step1 checks that the own-variable mappings of the
    -- anti-unification of (scDel p) and q is of a specific shape.
    step1 :: UTx ki codes (MetaVarIK ki) at -> UTxUTx2 ki codes at
          -> Maybe Bool
    -- If the deletion context of the numerator requires an opaque
    -- fixed value and the denominator performs any change other
    -- than a copy, this is a del/mod conflict.
    step1 (UTxOpq _) (UTxHole chg)
      | simpleCopy chg = Just True
      | otherwise      = Nothing
    -- If the numerator imposes no restriction in what it accepts here,
    -- we return true for this hole
    step1 (UTxHole _) _   = Just True
    -- If the numerator expects something specific but the denominator
    -- merely copies, we still return true
    step1 _ (UTxHole chg) = Just $ rawCpy varmap chg
    -- Any other situation requires further analisys.
    step1 _ _ = Just False

    -- |Step2 checks a condition for the own-variable mappints
    -- of the anti-unification of p and q! note this is different
    -- altogether from step 1!!!
    step2 :: (Applicable ki codes (UTx2 ki codes))
          => UTxUTx2 ki codes at -> UTxUTx2 ki codes at
          -> StateT (Subst ki codes (UTx2 ki codes)) FreshM Bool
    step2 pp qq = do
      s <- get
      let del = scDel qq
      pp' <- lift (refinedFor varmap pp del)
      case runExcept (pmatch' s del pp) of
        Left  _  -> return False
        Right s' -> put s' >> return True

    insins :: UTxUTx2 ki codes at -> UTxUTx2 ki codes at -> Bool
    insins (UTxHole pp) (UTxHole qq) = isLocalIns pp && isLocalIns qq
    insins _ _ = False

-- |Given a change in its spined-representation and a domain,
-- we attempt to refine the change to the domain in question.
-- The idea is that if the change copies information, but the domain
-- restricts the shape, we can also specialize the change.
--
-- > (Hole (Hole 0 :*: Hole 0)) `refinedFor` ((:) (Hole 1) [])
-- >   == ((:) (Hole 2 :*: Hole 2) [])
--
-- In the above example, the change was a copy, but the domain
-- required a `cons' node. No problem, if we copied anything, we can
-- copy cons nodes in particular.
--
refinedFor :: (ShowHO ki , EqHO ki)
           => M.Map Int Int
           -> UTxUTx2 ki codes at
           -> UTx ki codes (MetaVarIK ki) at
           -> FreshM (UTxUTx2 ki codes at)
refinedFor varmap s = fmap utxJoin . utxMapM (uncurry' go) . utxLCP s
  where
    go :: (ShowHO ki)
       => UTxUTx2 ki codes at
       -> UTx ki codes (MetaVarIK ki) at
       -> FreshM (UTxUTx2 ki codes at)
    go (UTxHole chgP) codQ
      | simpleCopy chgP = do v <- freshMetaVar
                             return $ utxMap (delta . UTxHole . metavarAdd v) codQ
      | otherwise          = return $ UTxHole chgP
    go sP      codQ = return sP

    delta x = (x :*: x)

    rawCpyVar (UTxHole v :*: _) = metavarGet v
         
