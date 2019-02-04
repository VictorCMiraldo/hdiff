{-# LANGUAGE TypeApplications #-}
module Data.Digems.Patch.DiffSpec (spec) where

import qualified Data.Set as S

import Generics.MRSOP.Base
import Generics.MRSOP.Util
import Generics.MRSOP.Digems.Treefix

import Data.Digems.Patch
import Data.Digems.Patch.Diff
import Data.Digems.MetaVar
import Data.Digems.Change
import Languages.RTree

import Test.QuickCheck
import Test.Hspec

genSimilarTrees' :: Gen (RTree , RTree)
genSimilarTrees' = choose (0 , 4) >>= genSimilarTrees

diff_wellscoped_changes :: Property
diff_wellscoped_changes = forAll genSimilarTrees' $ \(t1 , t2)
  -> let gt1   = dfrom (into @FamRTree t1)
         gt2   = dfrom (into @FamRTree t2)
         patch = diff 1 gt1 gt2
      in conjoin $ utxGetHolesWith' go patch
  where
    go :: CChange W CodesRTree ix -> Property
    go (CMatch vars del ins)
      = let vd = utxGetHolesWith metavarGet del
            vi = utxGetHolesWith metavarGet ins
            v  = S.map metavarIK2Int vars
         in v === vd .&&. vi === v

apply_correctness :: Property
apply_correctness = forAll genSimilarTrees' $ \(t1 , t2)
  -> let gt1   = dfrom (into @FamRTree t1)
         gt2   = dfrom (into @FamRTree t2)
         patch = diff 1 gt1 gt2
      in case apply patch gt1 of
           Left err -> counterexample ("Apply failed with: " ++ err) False
           Right r  -> property $ eqFix eq1 gt2 r
           
spec :: Spec
spec = do
  describe "diff" $ do
    it "produce well-scoped changes" $ do
      diff_wellscoped_changes
  
  describe "apply" $ do
    it "is correct" $ do
      apply_correctness
