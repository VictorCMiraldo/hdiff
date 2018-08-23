{-# LANGUAGE RankNTypes    #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds     #-}
{-# LANGUAGE PolyKinds     #-}
{-# LANGUAGE GADTs         #-}
module Data.Digems.Diff.Merge where

import Data.Proxy
import Data.Type.Equality
import Data.Functor.Const
import Data.Functor.Sum
import qualified Data.Map as M
import qualified Data.Set as S

import Control.Monad
import Control.Monad.State
import Control.Monad.Identity

import Generics.MRSOP.Util
import Generics.MRSOP.Base
import Generics.MRSOP.Digems.Treefix
import Generics.MRSOP.Digems.Digest

import qualified Data.WordTrie as T
import Data.Digems.Diff.Preprocess
import Data.Digems.Diff.Patch

-- * Merging

data Conflict :: (kon -> *) -> [[[Atom kon]]] -> Nat -> * where
  Conflict :: (IsNat v , IsNat c)
           => UTx ki codes (Const Int) v
           -> UTx ki codes (Const Int) c
           -> Conflict ki codes v

type PatchC ki codes = RawPatch (Sum (Const Int) (Conflict ki codes)) ki codes

-- |Merge two patches into a patch that may have conflicts.
--
--  There is a preprocessing step to ensure that the holes in both
--  patches are disjoint. We basically add the maximum hole number
--  of p o every hole of q.
merge :: (Eq1 ki , IsNat v)
      => Patch ki codes v
      -> Patch ki codes v
      -> PatchC ki codes v
merge p q
  = let maxP = 1 + execState (patchMap getMax p) 0
        q'   = runIdentity (patchMap (return . (addC maxP)) q)
     in merge' p q'
  where
    addC :: Int -> Const Int ix -> Const Int iz
    addC y (Const x) = Const (x + y)
    
    getMax :: Const Int ix -> State Int (Const Int ix)
    getMax i = modify (max $ getConst i) >> return i

-- |Merge two patches into a patch that may have conflicts.
--
--  PRECONDITION: assumes that the holes in both patches
--                have disjoint names
merge' :: (Eq1 ki, IsNat v)
       => Patch ki codes v
       -> Patch ki codes v
       -> PatchC ki codes v
merge' (Patch dx ix) (Patch dy iy)
  = Patch (mergeUTx dx dy) (mergeUTx ix iy)

mergeUTx :: (Eq1 ki , IsNat v)
         => UTx ki codes (Const Int) v
         -> UTx ki codes (Const Int) v
         -> UTx ki codes (Sum (Const Int) (Conflict ki codes)) v
mergeUTx (UTxHere hx) y = utxMap InL y
mergeUTx x (UTxHere hy) = utxMap InL x
mergeUTx x@(UTxPeel c utx) y@(UTxPeel d uty)
  = case testEquality c d of
      Nothing   -> UTxHere (InR $ Conflict x y)
      Just Refl -> case mapNPM (uncurry' mergeNA) $ zipNP utx uty of
        -- Some opaque value was different in utx and uty
        Nothing -> UTxHere (InR (Conflict x y))
        Just r  -> UTxPeel c r
  where
    mergeNA :: (Eq1 ki)
            => NA ki (UTx ki codes (Const Int)) ix
            -> NA ki (UTx ki codes (Const Int)) ix
            -> Maybe (NA ki (UTx ki codes (Sum (Const Int) (Conflict ki codes))) ix)
    mergeNA (NA_K k1) (NA_K k2)
      | eq1 k1 k2 = Just (NA_K k1)
      | otherwise = Nothing
    mergeNA (NA_I i1) (NA_I i2) = Just (NA_I $ mergeUTx i1 i2)
