{-# LANGUAGE TypeApplications #-}
module Data.Digems.Patch.DiffSpec (spec) where

import qualified Data.Set as S

import Generics.MRSOP.Base
import Generics.MRSOP.Util
import Generics.MRSOP.Holes

import Data.Digems.Patch
import Data.Digems.Patch.Diff
import Data.Digems.MetaVar
import Data.Digems.Change
import Languages.RTree
import Languages.RTree.Diff

import Test.QuickCheck
import Test.Hspec


diff_wellscoped_changes :: Property
diff_wellscoped_changes = forAll genSimilarTrees' $ \(t1 , t2)
  -> let patch = digemRTree t1 t2
      in conjoin $ holesGetHolesAnnWith' go patch
  where
    go :: CChange W CodesRTree ix -> Property
    go (CMatch vars del ins)
      = let vd = holesGetHolesAnnWith'' metavarGet del
            vi = holesGetHolesAnnWith'' metavarGet ins
            v  = S.map metavarIK2Int vars
         in v === vd .&&. vi === v

apply_correctness :: Property
apply_correctness = forAll genSimilarTrees' $ \(t1 , t2)
  -> let patch = digemRTree t1 t2
      in case applyRTree patch t1 of
           Left err -> counterexample ("Apply failed with: " ++ err) False
           Right r  -> property $ t2 == r
           
spec :: Spec
spec = do
  describe "diff" $ do
    it "produce well-scoped changes" $ do
      diff_wellscoped_changes
  
  describe "apply" $ do
    it "is correct" $ do
      apply_correctness
