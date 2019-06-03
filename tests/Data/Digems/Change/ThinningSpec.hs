{-# LANGUAGE PolyKinds        #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE GADTs            #-}
module Data.Digems.Change.ThinningSpec (spec) where

import qualified Data.Set as S

import Generics.MRSOP.Base
import Generics.MRSOP.Util
import Generics.MRSOP.Digems.Treefix

import Data.Functor.Const
import Data.Exists
import Data.Digems.Patch
import Data.Digems.Patch.Diff
import Data.Digems.Patch.Show
import Data.Digems.MetaVar
import Data.Digems.Change
import Data.Digems.Change.Thinning
import Languages.RTree
import Languages.RTree.Diff

import Test.QuickCheck
import Test.Hspec

import Control.Monad.Except
import Control.Monad.State
import qualified Data.Map as M

---------

type ContextRTree = UTx W CodesRTree (MetaVarIK W) ('I 'Z)

bin :: ContextRTree -> ContextRTree -> ContextRTree
bin l r = UTxPeel CZ (UTxOpq (W_String "bin") :* bin' :* NP0)
  where bin' = UTxPeel (CS CZ) (l :* (UTxPeel (CS CZ)
                                        (r :* UTxPeel CZ NP0 :* NP0)
                                  :* NP0))

mvar :: Int -> ContextRTree
mvar = UTxHole . NA_I . Const

p1, q1 :: ContextRTree
p1 = bin (mvar 0) (mvar 0)
q1 = bin (bin (mvar 1)                (mvar 2))
         (bin (bin (mvar 3) (mvar 4)) (mvar 2))
         
run x y = runExcept $ runStateT (thin' x y) M.empty


spec :: Spec
spec = undefined


