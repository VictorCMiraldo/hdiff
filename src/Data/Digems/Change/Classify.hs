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

---------------------
-- Experimental!!!
---------------------

class (Eq1 phi) => Ord1 (phi :: k -> *) where
  compare1 :: phi ix -> phi ix -> Ordering

instance (Ord1 phi , Ord1 ki) => Ord (UTx ki codes phi ix) where
  compare (UTxOpq kx)   (UTxOpq ky)   = compare1 kx ky
  compare (UTxHole _)   (UTxPeel _ _) = LT
  compare (UTxPeel _ _) (UTxHole _)   = GT
  compare (UTxHole phi) (UTxHole psi) = compare1 phi psi
  compare x@(UTxPeel c1 p1) y@(UTxPeel c2 p2)
    | x == y    = EQ
    | otherwise =
      let idx1 = getUTxSNat x
          idx2 = getUTxSNat y
       in case testEquality idx1 idx2 of
         Nothing -> error "impossible"
         Just Refl -> case testEquality c1 c2 of
           Just Refl -> head $ filter (/= EQ)
                             $ elimNP (uncurry' compare) (zipNP p1 p2)
           Nothing   -> let d1 = getConstrSNat c1
                            d2 = getConstrSNat c2
                       in case compare (snat2int d1) (snat2int d2) of
                            EQ -> error "unreachable"
                            x  -> x

getConstrSNat :: (IsNat n) => Constr sum n -> SNat n
getConstrSNat _ = getSNat (Proxy :: Proxy n)

utxGetMultiplicities :: Int -> UTx ki codes f at -> [Exists (UTx ki codes f)]
utxGetMultiplicities k utx
  | utxArity utx == k = [Exists utx]
  | otherwise = case utx of
      UTxPeel c p -> concat $ elimNP (utxGetMultiplicities k) p
      _           -> []

instance (Eq1 ki , TestEquality ki) => Eq (Exists (UTx ki codes (MetaVarIK ki))) where
  (Exists v) == (Exists u) =
    case testEquality v u of
      Nothing   -> False
      Just Refl -> v == u

instance (Ord1 ki , Eq1 ki , TestEquality ki) => Ord (Exists (UTx ki codes (MetaVarIK ki))) where
  compare (Exists v) (Exists u) =
    case testEquality v u of
      Nothing   -> LT -- this does NOT give an order relation, but hey, it's just a hack!
                      -- the question is, does it work?
      Just Refl -> compare v u

instance (Eq1 ki) => Ord1 (MetaVarIK ki) where
  compare1 x y = compare (metavarGet x) (metavarGet y)
-----------------------------------------
-- Change Classification algo

data ChangeClass
  = CPerm | CMod | CId | CIns | CDel
  deriving (Eq , Show)

changeClassify :: (Eq1 ki , TestEquality ki)
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

isIns , isDel :: (TestEquality ki , Eq1 ki) => CChange ki codes ix -> Bool
isIns c = changeClassify c == CIns
isDel c = changeClassify c == CDel

-- OLD COLD CODE BELOW HERE!! READ AT OWN RISK

{-
isIns chg =
  let vd = utxGetHolesWith' metavarGet (cCtxDel chg)
      vi = utxGetHolesWith' metavarGet (cCtxIns chg)
   in length vd == 1 && vd == vi && isHole (cCtxDel chg)
      && not (isCpy chg)
  where
    isHole (UTxHole _) = True
    isHole _           = False

isDel :: (Eq1 ki) => CChange ki codes ix -> Bool
isDel (CMatch vars del ins) = isIns (CMatch vars ins del)

spineIsInsertion :: (Eq1 ki) => UTx ki codes (CChange ki codes) ix -> Bool
spineIsInsertion = all (exElim (\c -> isCpy c || isIns c))
                 . utxGetHolesWith' Exists


-}
{-
changeClassify :: (Eq1 ki) => CChange ki codes at -> ChangeClass
changeClassify c
  | isCpy c   = CId
  | otherwise =
  let holes    = utxGetHolesWith' Exists (utxLCP (cCtxDel c) (cCtxIns c))
   in classify' [] holes
  where
    classify' :: [ChangeClass] -- possible classes so far 
              -> [Exists (UTx ki codes (MetaVarIK ki) :*: UTx ki codes (MetaVarIK ki))]
              -> ChangeClass
    -- We are done seeing the holes, there's only one possible classification
    classify' [x] [] = x
    classify' _   [] = CMod
    classify' cs (Exists hole : holes) =
      case hole of
        -- if the two vars are different, there's a permutation.
        -- Don't forget we assume that all bindings that are defined
        -- are used and vice-versa
        (UTxHole var1 :*: UTxHole var2) 
          | metavarGet var1 /= metavarGet var2 -> classify' (nub (CPerm : cs)) holes
          | otherwise -> classify' cs holes
        -- If we see a variable and a term, but the variable occurs
        -- within the term, this could be an insertion
        (UTxHole var1 :*: term2) ->
          if metavarGet var1 `elem` utxGetHolesWith metavarGet term2
          then classify' (nub (CIns : cs)) holes
          else classify' cs holes
        -- Dually, this could be a deletion
        (term1 :*: UTxHole var2) ->
          if metavarGet var2 `elem` utxGetHolesWith metavarGet term1
          then classify' (nub (CDel : cs)) holes
          else classify' cs holes
        -- If we see two terms, it's a modification
        (_ :*: _) -> CMod
-}
