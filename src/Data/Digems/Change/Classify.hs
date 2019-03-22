{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PolyKinds     #-}
{-# LANGUAGE GADTs         #-}
-- |change classification algorithm
module Data.Digems.Change.Classify where

import Data.List (sort,nub)
import Data.Proxy
import Data.Type.Equality
-------------------------------
import Generics.MRSOP.Util
import Generics.MRSOP.Base
-------------------------------
import Data.Exists
import Data.Digems.Change
import Data.Digems.MetaVar
import Data.Digems.Change.Apply
import Generics.MRSOP.Digems.Treefix

-----------------------------------------
-- Change Classification algo

instance (EqHO ki , TestEquality ki) => Eq (Exists (UTx ki codes (MetaVarIK ki))) where
  (Exists v) == (Exists u) =
    case testEquality v u of
      Nothing   -> False
      Just Refl -> v == u

getConstrSNat :: (IsNat n) => Constr sum n -> SNat n
getConstrSNat _ = getSNat (Proxy :: Proxy n)

utxGetMultiplicities :: Int -> UTx ki codes f at -> [Exists (UTx ki codes f)]
utxGetMultiplicities k utx
  | utxArity utx == k = [Exists utx]
  | otherwise = case utx of
      UTxPeel c p -> concat $ elimNP (utxGetMultiplicities k) p
      _           -> []


data ChangeClass
  = CPerm | CMod | CId | CIns | CDel
  deriving (Eq , Show , Ord)

changeClassify :: (EqHO ki , TestEquality ki)
               => CChange ki codes at -> ChangeClass
changeClassify c
  | isCpy c   = CId
  | otherwise =
  let mis = utxGetMultiplicities 0 (cCtxIns c)
      mds = utxGetMultiplicities 0 (cCtxDel c)
      vi = utxGetHolesWith' metavarGet (cCtxIns c)
      vd = utxGetHolesWith' metavarGet (cCtxDel c)
      permutes = vi == vd
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

