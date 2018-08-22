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
           => UTx ki codes v (Const Int)
           -> UTx ki codes c (Const Int)
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
         => UTx ki codes v (Const Int)
         -> UTx ki codes v (Const Int)
         -> UTx ki codes v (Sum (Const Int) (Conflict ki codes))
mergeUTx (UTxHere hx) y = utxMapI InL y
mergeUTx x (UTxHere hy) = utxMapI InL x
mergeUTx x@(UTxPeel c utx) y@(UTxPeel d uty)
  = case testEquality c d of
      Nothing   -> UTxHere (InR $ Conflict x y)
      Just Refl -> if utxnpAgree utx uty
                   then UTxPeel c (mergeUTxNP utx uty)
                   else UTxHere (InR (Conflict x y))

-- |Precondition: both treefixes agree on their
--  opaque values
mergeUTxNP :: (Eq1 ki)
           => UTxNP ki codes prod (Const Int)
           -> UTxNP ki codes prod (Const Int)
           -> UTxNP ki codes prod (Sum (Const Int) (Conflict ki codes))
mergeUTxNP UTxNPNil UTxNPNil = UTxNPNil
mergeUTxNP (UTxNPSolid kx utx) (UTxNPSolid _ uty)
  = UTxNPSolid kx (mergeUTxNP utx uty)
mergeUTxNP (UTxNPPath x utx) (UTxNPPath y uty)
  = UTxNPPath (mergeUTx x y) (mergeUTxNP utx uty)

-- |Does two product of treefixes agree on their opaque values?
utxnpAgree :: (Eq1 ki)
           => UTxNP ki codes prod f
           -> UTxNP ki codes prod g
           -> Bool
utxnpAgree UTxNPNil UTxNPNil
  = True
utxnpAgree (UTxNPPath _ utx)   (UTxNPPath _ uty)
  = utxnpAgree utx uty
utxnpAgree (UTxNPSolid kx utx) (UTxNPSolid ky uty)
  = eq1 kx ky && utxnpAgree utx uty
