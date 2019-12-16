{-# LANGUAGE TypeApplications #-}
module Data.HDiff.DiffSpec (spec) where

import Generics.MRSOP.Holes

import Data.HDiff.Base
import Data.HDiff.Diff
import Data.HDiff.MetaVar
import Languages.RTree
import Languages.RTree.Diff

import Test.QuickCheck
import Test.Hspec


diff_wellscoped_changes :: DiffMode -> Property
diff_wellscoped_changes mode = forAll genSimilarTrees' $ \(t1 , t2)
  -> let patch = hdiffRTreeHM mode 1 t1 t2
      in go $ chgDistr patch
  where
    go :: Chg W CodesRTree ix -> Property
    go (Chg del ins)
      = let vd = holesGetHolesAnnWith'' metavarGet del
            vi = holesGetHolesAnnWith'' metavarGet ins
         in vd === vi

apply_correctness :: DiffMode -> Property
apply_correctness mode = forAll genSimilarTrees' $ \(t1 , t2)
  -> let patch = hdiffRTreeHM mode 1 t1 t2
      in case applyRTree patch t1 of
           Left err -> counterexample ("Apply failed with: " ++ err) False
           Right r  -> property $ t2 == r
           
diffModeSpec :: DiffMode -> Spec
diffModeSpec mode = do
  describe "diff" $ do
    it "produce well-scoped changes" $ do
      diff_wellscoped_changes mode
  describe "apply" $ do
    it "is correct" $ do
      apply_correctness mode

spec :: Spec
spec = do
 flip mapM_ (enumFrom (toEnum 0)) $ \m ->
   describe ("Extraction (" ++ show m ++ ")") $ diffModeSpec m
