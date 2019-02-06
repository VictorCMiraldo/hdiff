{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE PolyKinds        #-}
{-# LANGUAGE GADTs            #-}
module Data.Digems.Patch.Specialize where

import           Control.Monad.State
import           Control.Monad.Except
import           Data.Type.Equality
import qualified Data.Set as S
import qualified Data.Map as M
------------------------------------
import Generics.MRSOP.Util
import Generics.MRSOP.Base
------------------------------------
import Data.Exists
import Generics.MRSOP.Digems.Treefix
import qualified Data.WordTrie as T
import Data.Digems.MetaVar
import Data.Digems.Patch
import Data.Digems.Patch.Diff
import Data.Digems.Change
import Data.Digems.Change.Classify
import Data.Digems.Change.Apply


-- ** Specializing a Patch

-- |Specializing will attempt to adjust a spine with changes to be properly
-- adapted by a change.
specialize :: ( Show1 ki , Eq1 ki , TestEquality ki)
           => RawPatch ki codes at
           -> UTx ki codes (MetaVarIK ki) at
           -> RawPatch ki codes at
specialize spine cc
  = utxRefine (uncurry' go) UTxOpq $ utxLCP spine cc
  where
    vmax = patchMaxVar spine

    go :: (Eq1 ki , Show1 ki , TestEquality ki)
       => UTx ki codes (CChange ki codes) at
       -> UTx ki codes (MetaVarIK ki) at
       -> UTx ki codes (CChange ki codes) at
    go (UTxHole c1) (UTxHole _) = UTxHole c1
    go (UTxHole c@(CMatch _ (UTxHole var) ins)) c2
      = let tgt = utxMap (metavarAdd vmax) c2
         in case runExcept (transport ins $ M.singleton (metavarGet var) (Exists tgt)) of
              Left err   -> error "invariant break"
              Right ins' -> UTxHole $ cmatch tgt ins'
      {-
      | isCpy c1 || isIns c1 =
        -- lemma: transporting over insertions or copies never fails
        let Right res = genericApply c1 c2
            del = utxMap (metavarAdd vmax) c2
            ins = utxMap (metavarAdd vmax) res
         -- problem: we should be either returning the GCP of del ins
         -- or modify the transport function to allow it to match
         -- Just using:  UTxHole $ CMatch S.empty del ins
         -- does not cut it
         in UTxHole $ CMatch S.empty del ins
          -- close (extractSpine id (vmax + 100) del ins)

          -- UTxHole (CMatch S.empty del ins) --  utxMap (uncurry' (CMatch S.empty)) $ utxLCP del ins
          -- UTxHole $ _ $ utxTransport c1 c2 -- _ -- utxMap (changeCopy . metavarAdd vmax) c2
      | otherwise = UTxHole c1
-}
    go sp _ = sp
