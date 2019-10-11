{-# LANGUAGE PolyKinds        #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE GADTs            #-}
module Data.HDiff.Change.TreeEditDistanceSpec (spec) where

import Generics.MRSOP.Base
import Generics.MRSOP.Util
import qualified Generics.MRSOP.GDiff    as GDiff

import Data.HDiff.Patch
import Data.HDiff.Patch.Show
import Data.HDiff.MetaVar
import Data.HDiff.Change
import qualified Data.HDiff.Change.TreeEditDistance as TED

import Languages.RTree
import Languages.RTree.Diff

import Test.QuickCheck
import Test.Hspec

a1 , b1 :: RTree
a1 = "m" :>: ["m" :>: [],"b" :>: [],"d" :>: [],"a" :>: []]
b1 = "j" :>: ["m" :>: [],"l" :>: ["k" :>: [],"k" :>: [],"k" :>: [],"b" :>: []],"k" :>: [],"d" :>: ["f" :>: [],"i" :>: []]]

a2 , b2 :: RTree
a2 = "i" :>: []
b2 = "h" :>: [ "i" :>: []]

is_the_same_as_gdiff :: Property
is_the_same_as_gdiff = forAll genSimilarTrees' $ \(t1 , t2)
  -> let patch = hdiffRTree t1 t2
         es0   = GDiff.diff @FamRTree @_ @CodesRTree t1 t2
      in case TED.toES (distrCChange patch) (NA_I $ deep t1) of
           Left err  -> counterexample err False
           Right es1 -> GDiff.cost es1 === GDiff.cost es0

is_better_than_gdiff :: Property
is_better_than_gdiff = forAll genSimilarTrees' $ \(t1 , t2)
  -> let patch = hdiffRTree t1 t2
         es0   = GDiff.diff @FamRTree @_ @CodesRTree t1 t2
      in patchCost patch <= GDiff.cost es0


spec :: Spec
spec = do
  describe "Change.toES" $ do
    xit "computes the same distance as generics-mrsop-gdiff" $
      property is_better_than_gdiff
