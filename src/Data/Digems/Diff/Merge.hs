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
(//) :: (Eq1 ki , IsNat v)
      => Patch ki codes v
      -> Patch ki codes v
      -> PatchC ki codes v
(Patch pd pi) // (Patch _ qi) = Patch (qi `transport` pd)
                                      (utxMap InL pi)

-- |Transports a deletion context (second arg) to work
--  on top of a insertion context.
transport :: (IsNat v)
          => UTx ki codes (Const Int) v -- holes0
          -> UTx ki codes (Const Int) v -- holes1
          -> UTx ki codes (Sum (Const Int) (Conflict ki codes)) v -- holes1
-- ignores holes on the left
transport (UTxHere _) ty
  = utxMap InL ty
-- transport preserves holes on the right
transport tx (UTxHere i)
  = UTxHere (InL i)
-- Goes over constructors, preserving data on the right
transport tx@(UTxPeel cx dx) ty@(UTxPeel cy dy)
  = case testEquality cx cy of
      Nothing   -> UTxHere (InR $ Conflict tx ty)
      Just Refl -> UTxPeel cx (mapNP (uncurry' transportNA) $ zipNP dx dy)
  where
    transportNA :: NA ki (UTx ki codes (Const Int)) a
                -> NA ki (UTx ki codes (Const Int)) a
                -> NA ki (UTx ki codes (Sum (Const Int) (Conflict ki codes))) a
    transportNA (NA_K _) (NA_K k) = NA_K k
    transportNA (NA_I i) (NA_I j) = NA_I $ transport i j
