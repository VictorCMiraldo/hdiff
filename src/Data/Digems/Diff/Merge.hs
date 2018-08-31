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
transport :: (IsNat v , Eq1 ki)
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
      Just Refl -> case mapNPM (uncurry' transportNA) $ zipNP dx dy of
        Nothing -> UTxHere (InR $ Conflict tx ty)
        Just d  -> UTxPeel cx d
  where
    transportNA :: (Eq1 ki)
                => NA ki (UTx ki codes (Const Int)) a
                -> NA ki (UTx ki codes (Const Int)) a
                -> Maybe (NA ki (UTx ki codes (Sum (Const Int) (Conflict ki codes))) a)
    transportNA (NA_K k) (NA_K l)
      -- = Just $ NA_K k
      | eq1 k l   = Just $ NA_K k
      | otherwise = Nothing
    transportNA (NA_I i) (NA_I j) = Just $ NA_I $ transport i j
