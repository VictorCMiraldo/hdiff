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

-- TODO: flip Conflict and MetaVar; it is common to have the 'right'
--       result on the right side of the coproduct

data Conflict :: (kon -> *) -> [[[Atom kon]]] -> Atom kon -> * where
  Conflict :: GUTx ki codes (TxAtom ki codes MetaVar) v
           -> GUTx ki codes (TxAtom ki codes MetaVar) v
           -> Conflict ki codes v

type PatchC ki codes = RawPatch (Sum MetaVar (Conflict ki codes)) ki codes

-- |Merge two patches into a patch that may have conflicts.
--  TODO: prove @(q // p) . p == (p // q) . p@ in the absence of conflicts
--
(//) :: (Eq1 ki , IsNat v)
      => Patch ki codes v
      -> Patch ki codes v
      -> PatchC ki codes v
(Patch pd pi) // (Patch _ qi) = Patch (qi `transport` pd)
                                      (gtxMap (txatomMap InL) pi)

-- |Transports a deletion context (second arg) to work
--  on top of a insertion context.
--  We must produce a valuation in case the deletion context
--  copies some constants that need to be plugged into the
--  insertion context.
transport :: (Eq1 ki)
          => GUTx ki codes (TxAtom ki codes MetaVar) v -- holes0
          -> GUTx ki codes (TxAtom ki codes MetaVar) v -- holes1
          -> GUTx ki codes (TxAtom ki codes (Sum MetaVar (Conflict ki codes))) v -- holes1
-- transport preserves holes on the right
transport tx (GUTxHere (Meta v))
  = GUTxHere $ Meta (InL v)
-- ignores holes on the left
transport (GUTxHere (Meta _)) ty
  = gtxMap (txatomMap InL) ty
-- Checks constants for equality
transport tx@(GUTxHere (SolidK kx)) ty@(GUTxHere (SolidK ky))
  | eq1 kx ky = GUTxHere (SolidK kx)
  | otherwise = GUTxHere (Meta $ InR $ Conflict tx ty)
-- Checks trees for equality
transport tx@(GUTxHere (SolidI vx)) ty@(GUTxHere (SolidI vy))
  | eqFix eq1 vx vy = GUTxHere (SolidI vx)
  | otherwise       = GUTxHere (Meta $ InR $ Conflict tx ty)
-- Recurses over fixes trees
transport tx@(GUTxHere (SolidI vx)) ty@(GUTxPeel cy dy)
  | Tag cx dx <- sop (unFix vx)
  = case testEquality cx cy of
      Nothing   -> GUTxHere (Meta $ InR $ Conflict tx ty)
      Just Refl -> GUTxPeel cx (mapNP (uncurry' go) $ zipNP dx dy)
  where
    go :: (Eq1 ki)
       => NA ki (Fix ki codes) at
       -> GUTx ki codes (TxAtom ki codes MetaVar) at
       -> GUTx ki codes (TxAtom ki codes (Sum MetaVar (Conflict ki codes))) at
    go (NA_K k) = transport (GUTxHere (SolidK k))
    go (NA_I i) = transport (GUTxHere (SolidI i))
-- Goes over constructors, preserving data on the right
transport tx@(GUTxPeel cx dx) ty@(GUTxPeel cy dy)
  = case testEquality cx cy of
      Nothing   -> GUTxHere (Meta $ InR $ Conflict tx ty)
      Just Refl -> GUTxPeel cx (mapNP (uncurry' transport) $ zipNP dx dy)
