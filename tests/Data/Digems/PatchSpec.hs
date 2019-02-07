{-# LANGUAGE PolyKinds        #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE GADTs            #-}
module Data.Digems.PatchSpec (spec) where

import qualified Data.Set as S
import Data.Functor.Const

import Generics.MRSOP.Base
import Generics.MRSOP.Util
import Generics.MRSOP.Digems.Treefix

import Data.Exists
import Data.Digems.Patch
import Data.Digems.Patch.Diff
import Data.Digems.Patch.Show
import Data.Digems.MetaVar
import Data.Digems.Change
import Languages.RTree

import Test.QuickCheck
import Test.Hspec

----------------------------------------------

copy_composes :: Property
copy_composes = forAll genSimilarTrees' $ \(t1 , t2)
  -> let patch = digemRTree t1 t2
         cpy   = UTxHole (changeCopy (NA_I (Const 0))) :: PatchRTree
      in composes patch cpy .&&. composes cpy patch

composes_correct :: Property
composes_correct = forAll (choose (0 , 4) >>= genSimilarTreesN 3)
  $ \[a , b , c] ->
  let ab = digemRTree a b
      bc = digemRTree b c
   in composes bc ab

{-
  NOT TRUE!!!!

  check: ("f" :>: ["i" :>: [],"j" :>: [],"a" :>: []],"j" :>: [])

composes_non_reflexive :: Property
composes_non_reflexive = forAll (genSimilarTrees' `suchThat` uncurry (/=))
  $ \(t1 , t2)
  -> let patch = digemRTree t1 t2
      in composes patch patch === False
-}

spec :: Spec
spec = do
  describe "composes" $ do
    it "has copy as left and right id" $ property copy_composes
    it "is correct"                    $ property composes_correct

