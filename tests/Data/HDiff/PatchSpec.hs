{-# LANGUAGE PolyKinds        #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE GADTs            #-}
module Data.HDiff.PatchSpec (spec) where

import qualified Data.Set as S
import Data.Functor.Const

import Generics.MRSOP.Base
import Generics.MRSOP.Util
import Generics.MRSOP.Holes

import Data.Exists
import Data.HDiff.Patch
import Data.HDiff.Diff
import Data.HDiff.Patch.Show
import Data.HDiff.Patch.Compose
import Data.HDiff.MetaVar
import Data.HDiff.Change
import Data.HDiff.Change.Compose
import Languages.RTree
import Languages.RTree.Diff

import Test.QuickCheck
import Test.Hspec hiding (after)

----------------------------------------------

copy_composes :: Property
copy_composes = forAll genSimilarTrees' $ \(t1 , t2)
  -> let patch = hdiffRTree t1 t2
         cpy   = Hole' (changeCopy (NA_I (Const 0))) :: PatchRTree
      in composes patch cpy .&&. composes cpy patch

composes_correct :: Property
composes_correct = forAll (choose (0 , 4) >>= genSimilarTreesN 3)
  $ \[a , b , c] ->
  let ab = hdiffRTree a b
      bc = hdiffRTree b c
   in composes bc ab

a = "i" :>: []
b = "l" :>: ["i" :>: [],"c" :>: [],"l" :>: []]
c = "b" :>: ["g" :>: [],"c" :>: [],"g" :>: [],"f" :>: []]

ab = distrCChange $ hdiffRTree a b
bc = distrCChange $ hdiffRTree b c


{-
  NOT TRUE!!!!

  check: ("f" :>: ["i" :>: [],"j" :>: [],"a" :>: []],"j" :>: [])

composes_non_reflexive :: Property
composes_non_reflexive = forAll (genSimilarTrees' `suchThat` uncurry (/=))
  $ \(t1 , t2)
  -> let patch = hdiffRTree t1 t2
      in composes patch patch === False
-}

spec :: Spec
spec = do
  describe "composes" $ do
    -- it "has copy as left and right id" $ property copy_composes
    it "is correct"                    $ property composes_correct

