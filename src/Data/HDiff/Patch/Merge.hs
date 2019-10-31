{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE TypeSynonymInstances  #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# OPTIONS_GHC -Wno-orphans       #-}
module Data.HDiff.Patch.Merge where

import Data.Functor.Sum
import qualified Data.Map as M

import Control.Monad.State
import Control.Monad.Writer hiding (Sum)
import Control.Monad.Except

import Generics.MRSOP.Util
import Generics.MRSOP.Base
import Generics.MRSOP.Holes

import Data.Exists
import Data.HDiff.Patch
import Data.HDiff.Change
import Data.HDiff.Change.Apply
import Data.HDiff.Change.Thinning
import Data.HDiff.MetaVar

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
  = Holes ki codes (Sum (Conflict ki codes) (CChange ki codes)) ('I ix)

-- |Tries to cast a 'PatchC' back to a 'Patch'. Naturally,
--  this is only possible if the patch has no conflicts.
noConflicts :: PatchC ki codes ix -> Maybe (Patch ki codes ix)
noConflicts = holesMapM rmvInL
  where
    rmvInL (InL _) = Nothing
    rmvInL (InR x) = Just x

-- |Returns the labels of the conflicts ina a patch.
getConflicts :: (ShowHO ki) => PatchC ki codes ix -> [String]
getConflicts = snd . runWriter . holesMapM go
  where
    go x@(InL (Conflict str _ _)) = tell [str] >> return x
    go x                          = return x


-- |A merge of @p@ over @q@, denoted @p // q@, is the adaptation
--  of @p@ so that it could be applied to an element in the
--  image of @q@.
(//) :: ( Applicable ki codes (Holes2 ki codes)
        , EqHO ki , ShowHO ki
        , HasDatatypeInfo ki fam codes 
        )
     => Patch ki codes ix
     -> Patch ki codes ix
     -> PatchC ki codes ix
p // q = holesJoin $ holesMap (uncurry' reconcile)
                   $ holesLCP p
                   $ q `withFreshNamesFrom` p


-- |The 'reconcile' function will try to reconcile disagreeing
--  patches.
--
--  Precondition: before calling @reconcile p q@, make sure
--                @p@ and @q@ are different.
reconcile :: forall ki codes fam at
           . ( Applicable ki codes (Holes2 ki codes) , EqHO ki , ShowHO ki
             , HasDatatypeInfo ki fam codes 
             ) 
          => RawPatch ki codes at
          -> RawPatch ki codes at
          -> Holes ki codes (Sum (Conflict ki codes) (CChange ki codes)) at
reconcile p q
  -- If both patches are alpha-equivalent, we return a copy.
  | patchEq p q = Hole' $ InR $ makeCopyFrom (distrCChange p)
  -- Otherwise, this is slightly more involved, but it is intuitively simple.
  | otherwise    =
    -- First we translate both patches to a 'spined change' representation.
    let sp = holesJoin $ holesMap (uncurry' holesLCP . unCMatch) p
        sq = holesJoin $ holesMap (uncurry' holesLCP . unCMatch) q -- spinedChange q
     in case process sp sq of
          CantReconcile err -> Hole' $ InL $ Conflict err p q
          ReturnNominator   -> holesMap InR p
          InstDenominator v -> Hole' $
            case runExcept $ transport (scIns sq) v of
              Left err -> InL $ Conflict (show err) p q
              Right r  -> case utx22change r of
                            Nothing  -> InL $ Conflict "chg" p q
                            Just res -> InR res 

data ProcessOutcome ki codes
  = ReturnNominator
  | InstDenominator (Subst ki codes (Holes2 ki codes))
  | CantReconcile String

-- |Checks whether a variable is a rawCpy, note that we need
--  a map that checks occurences of this variable.
rawCpy :: M.Map Int Int
       -> Holes2 ki codes at
       -> Bool
rawCpy ar (Hole' v1 :*: Hole' v2) = metavarGet v1 == metavarGet v2
                                 && M.lookup (metavarGet v1) ar == Just 1
rawCpy _  _                       = False

simpleCopy :: Holes2 ki codes at -> Bool
simpleCopy (Hole' v1 :*: Hole' v2) = metavarGet v1 == metavarGet v2
simpleCopy _ = False

isLocalIns :: Holes2 ki codes at -> Bool
isLocalIns (Hole _ _ :*: HPeel _ _ _) = True
isLocalIns _                          = False

arityMap :: Holes ki codes (MetaVarIK ki) at -> M.Map Int Int
arityMap = go . holesGetHolesAnnWith' metavarGet
  where
    go []     = M.empty
    go (v:vs) = M.alter (Just . maybe 1 (+1)) v (go vs)

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
process :: ( HasDatatypeInfo ki fam codes
           , Applicable ki codes (Holes2 ki codes) , EqHO ki , ShowHO ki)
        => HolesHoles2 ki codes at -> HolesHoles2 ki codes at
        -> ProcessOutcome ki codes
process sp sq =
  case and <$> mapM (exElim $ uncurry' step1) phiD of
    Nothing    -> CantReconcile "p1n"
    Just True  -> if any (exElim $ uncurry' insins) phiID
                  then CantReconcile "p1ii"
                  else ReturnNominator
    Just False -> 
      let partial = runState (runExceptT $ mapM_ (exElim $ uncurry' step2) phiID) M.empty
       in case partial of
            (Left err  , _) -> CantReconcile $ "p2n: " ++ err
            (Right ()  , s) -> InstDenominator s
  where
    (delsp :*: _) = utx2distr sp
    phiD  = holesGetHolesAnnWith' Exists $ holesLCP delsp sq
    phiID = holesGetHolesAnnWith' Exists $ holesLCP sp sq

    -- The thing is, 'chg' is a true copy only if v2 occurs only once
    -- within the whole of 'sq'
    -- counts how many times a variable appears in 'sq'
    varmap = arityMap (snd' (utx2distr sq))
    {-
    m var = maybe 0 id $ M.lookup var varmap

    maxVar = case M.toDescList varmap of
               []        -> 0
               ((v,_):_) -> v
    -}

    -- |Step1 checks that the own-variable mappings of the
    -- anti-unification of (scDel p) and q is of a specific shape.
    step1 :: Holes ki codes (MetaVarIK ki) at -> HolesHoles2 ki codes at
          -> Maybe Bool
    -- If the deletion context of the numerator requires an opaque
    -- fixed value and the denominator performs any change other
    -- than a copy, this is a del/mod conflict.
    step1 (HOpq _ _) (Hole _ chg)
      | simpleCopy chg = Just True
      | otherwise      = Nothing
    -- If the numerator imposes no restriction in what it accepts here,
    -- we return true for this hole
    step1 (Hole _ _) _   = Just True
    -- If the numerator expects something specific but the denominator
    -- merely copies, we still return true
    step1 _ (Hole _ chg) = Just $ rawCpy varmap chg
    -- Any other situation requires further analisys.
    step1 _ _ = Just False

    -- |Step2 checks a condition for the own-variable mappints
    -- of the anti-unification of p and q! note this is different
    -- altogether from step 1!!!
    step2 :: ( HasDatatypeInfo ki fam codes
             , Applicable ki codes (Holes2 ki codes) , EqHO ki , ShowHO ki)
          => HolesHoles2 ki codes at -> HolesHoles2 ki codes at
          -> ExceptT String (State (Subst ki codes (Holes2 ki codes))) ()
    step2 pp qq = do
      s <- lift get
      let del = scDel qq
      case thinHoles2 (utx2distr pp) del of
        Left e          -> throwError ("th: " ++ show e)
        Right (pp0 , _) -> do
          let pp' = uncurry' holesLCP pp0
          case runExcept (pmatch' s (\_ _ _ -> Nothing) del pp') of
            Left  e  -> throwError (show e)
            Right s' -> put s' >> return ()

    insins :: HolesHoles2 ki codes at -> HolesHoles2 ki codes at -> Bool
    insins (Hole _ pp) (Hole _ qq) = isLocalIns pp && isLocalIns qq
    insins _ _ = False
