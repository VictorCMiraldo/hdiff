{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE GADTs                 #-}
{-# OPTIONS_GHC -Wno-orphans       #-}
-- |change classification algorithm
module Data.HDiff.Change.Classify where

import Data.List (nub)
import Data.Proxy
import Data.Type.Equality
-------------------------------
import Generics.MRSOP.Util
import Generics.MRSOP.Base
import Generics.MRSOP.Holes
-------------------------------
import Data.Exists
import Data.HDiff.Change
import Data.HDiff.MetaVar

-----------------------------------------
-- Change Classification algo

instance (EqHO ki , TestEquality ki) => Eq (Exists (Holes ki codes (MetaVarIK ki))) where
  (Exists v) == (Exists u) =
    case testEquality v u of
      Nothing   -> False
      Just Refl -> eqHO v u

getConstrSNat :: (IsNat n) => Constr sum n -> SNat n
getConstrSNat _ = getSNat (Proxy :: Proxy n)

holesGetMultiplicities :: Int -> Holes ki codes f at -> [Exists (Holes ki codes f)]
holesGetMultiplicities k utx
  | holesArity utx == k = [Exists utx]
  | otherwise = case utx of
      HPeel _ _ p -> concat $ elimNP (holesGetMultiplicities k) p
      _           -> []


data ChangeClass
  = CPerm | CMod | CId | CIns | CDel
  deriving (Eq , Show , Ord)

changeClassify :: (EqHO ki , TestEquality ki)
               => CChange ki codes at -> ChangeClass
changeClassify c
  | isCpy c   = CId
  | otherwise =
  let mis = holesGetMultiplicities 0 (cCtxIns c)
      mds = holesGetMultiplicities 0 (cCtxDel c)
      vi = holesGetHolesAnnWith' metavarGet (cCtxIns c)
      vd = holesGetHolesAnnWith' metavarGet (cCtxDel c)
      -- permutes = vi == vd
      dups     = vi /= nub vi || vd /= nub vd
   in case (length mis , length mds) of
        (0 , 0) -> CPerm -- can't duplicate as one variable on one side would
                         -- be left unused; Can't have that so a tree with
                         -- multiplicity 0 would be there
        (0 , _) -> if dups       then CMod else CDel
        (_ , 0) -> if dups       then CMod else CIns
        (_ , _) -> if mis == mds then CPerm else CMod

isIns , isDel :: (TestEquality ki , EqHO ki) => CChange ki codes ix -> Bool
isIns c = changeClassify c == CIns
isDel c = changeClassify c == CDel

