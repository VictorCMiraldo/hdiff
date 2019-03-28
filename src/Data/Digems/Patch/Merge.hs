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
    

-- |A merge of @p@ over @q@, denoted @p // q@, is the adaptation
--  of @p@ so that it could be applied to an element in the
--  image of @q@.
(//) :: ( Applicable ki codes (UTx2 ki codes)
        , HasDatatypeInfo ki fam codes 
        )
     => Patch ki codes ix
     -> Patch ki codes ix
     -> PatchC ki codes ix
p // q = utxJoin . utxMap (uncurry' reconcile) $ utxLCP p q

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
          -> UTx ki codes (Sum (Conflict ki codes) (CChange ki codes)) at
reconcile p q
  -- If both patches are alpha-equivalent, we return a copy.
  | patchEq p q  = UTxHole $ InR $ makeCopyFrom (distrCChange p)
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
     in case process sp sq of
          CantReconcile     -> UTxHole $ InL $ Conflict "conf" p q
          ReturnNominator   -> utxMap InR p
          InstDenominator v -> UTxHole $
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

rawCpy :: (UTx ki codes (MetaVarIK ki) :*: UTx ki codes (MetaVarIK ki)) at -> Bool
rawCpy (UTxHole v1 :*: UTxHole v2) = metavarGet v1 == metavarGet v2
rawCpy _                           = False

-- |compat makes sure that we don't have diverging opaque changes nor
-- insertions insertions conflicts. We do so by checking where the codomains
-- diverge. If they diverge only on holes, the codomains are compatible.
compat :: (EqHO ki)
       => UTx ki codes (MetaVarIK ki) at -> UTx ki codes (MetaVarIK ki) at -> Bool
compat codP codQ = and $ utxGetHolesWith' (uncurry' ok) (utxLCP codP codQ)
  where ok _ (UTxHole _) = True
        ok (UTxHole _) _ = True
        ok _ _           = False

-- |A deletion context has no del/mod conflict with a change when we
-- can pattern match the deletion context in the refined spine of
-- the change without problems.
delmod :: (Applicable ki codes (UTx2 ki codes))
         => UTxUTx2 ki codes at -> UTxUTx2 ki codes at -> Bool
delmod (UTxHole (delCtx :*: _)) denom
  = case runExcept (pmatch delCtx (denom `refinedFor` delCtx)) of
          Left err -> True
          Right _  -> False
delmod _ _ = False

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
        -> ProcessOutcome ki codes
process sp sq =
  case and <$> mapM (exElim $ uncurry' step1) phiD of
    Nothing    -> CantReconcile
    Just True  -> if any (exElim $ uncurry' insins) phiID
                  then CantReconcile
                  else ReturnNominator
    Just False ->
      case runState (and <$> mapM (exElim $ uncurry' step2) phiID) M.empty of
        (False , _) -> CantReconcile
        (True  , s) -> InstDenominator s
  where
    (delsp :*: _) = utx2distr sp
    phiD  = utxGetHolesWith' Exists $ utxLCP delsp sq
    phiID = utxGetHolesWith' Exists $ utxLCP sp sq

    -- counts how many times a variable appears in 'sq'
    m var = maybe 0 id $ M.lookup var (arityMap (snd' (utx2distr sq)))

    -- |Step1 checks that the own-variable mappings of the
    -- anti-unification of (scDel p) and q is of a specific shape.
    step1 :: UTx ki codes (MetaVarIK ki) at -> UTxUTx2 ki codes at
          -> Maybe Bool
    -- If the deletion context of the numerator requires an opaque
    -- fixed value and the denominator performs any change other
    -- than a copy, this is a del/mod conflict.
    step1 (UTxOpq _) (UTxHole chg)
      | rawCpy chg = Just True
      | otherwise  = Nothing
    -- If the numerator imposes no restriction in what it accepts here,
    -- we return true for this hole
    step1 (UTxHole _) _   = Just True
    -- If the numerator expects something specific but the denominator
    -- merely copies, we still return true
    step1 _ (UTxHole chg) = Just $
      case chg of
        -- The thing is, 'chg' is a true copy only if v2 occurs only once
        -- within the whole of 'sq'
        (UTxHole v1 :*: UTxHole v2)
          -> metavarGet v1 == metavarGet v2 && m (metavarGet v2) == 1
        _ -> False
    -- Any other situation requires further analisys.
    step1 _ _ = Just False

    -- |Step2 checks a condition for the own-variable mappints
    -- of the anti-unification of p and q! note this is different
    -- altogether from step 1!!!
    step2 :: (Applicable ki codes (UTx2 ki codes))
          => UTxUTx2 ki codes at -> UTxUTx2 ki codes at
          -> State (Subst ki codes (UTx2 ki codes)) Bool
    step2 pp qq = do
      s <- get
      let del = scDel qq
      case runExcept (pmatch' s del (pp `refinedFor` del)) of
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
           => UTxUTx2 ki codes at
           -> UTx ki codes (MetaVarIK ki) at
           -> UTxUTx2 ki codes at
refinedFor s = utxJoin . utxMap (uncurry' go) . utxLCP s
  where
    maxVar = maximum $ 0 : utxGetHolesWith' metavarGet (snd' $ utx2distr s)
    
    go :: (ShowHO ki)
       => UTxUTx2 ki codes at
       -> UTx ki codes (MetaVarIK ki) at
       -> UTxUTx2 ki codes at
    go (UTxHole chgP) codQ
      | rawCpy chgP = let v = rawCpyVar chgP + maxVar + 1
                       in utxMap (\i -> delta (UTxHole $ metavarAdd v i)) codQ
      | otherwise   = UTxHole chgP
    go sP             codQ = sP

    delta x = (x :*: x)

    rawCpyVar (UTxHole v :*: _) = metavarGet v
         
