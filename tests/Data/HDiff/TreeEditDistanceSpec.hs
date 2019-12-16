{-# LANGUAGE PolyKinds        #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE GADTs            #-}
module Data.HDiff.TreeEditDistanceSpec (spec) where

import Generics.MRSOP.Base
import qualified Generics.MRSOP.GDiff    as GDiff

import Data.HDiff
import qualified Data.HDiff.TreeEditDistance as TED

import Languages.RTree
import Languages.RTree.Diff

import Test.QuickCheck
import Test.Hspec

{-
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
      in case TED.toES (chgDistr patch) (NA_I $ deep t1) of
           Left err  -> counterexample err False
           Right es1 -> GDiff.cost es1 === GDiff.cost es0
-}

hdiff_better_than_gdiff :: DiffMode -> Property
hdiff_better_than_gdiff mode = forAll genSimilarTrees' $ \(t1 , t2)
  -> let patch = hdiffRTreeHM mode 1 t1 t2
         es0   = GDiff.diff @FamRTree @_ @CodesRTree t1 t2
      in TED.patchCost patch <= GDiff.cost es0


spec :: Spec
spec = do
  flip mapM_ (enumFrom (toEnum 0)) $ \m -> do
    describe ("Patch to ES (" ++ show m ++ ")") $ do
      it "computes worst distance than generics-mrsop-gdiff" $
        property (expectFailure $ hdiff_better_than_gdiff m)
