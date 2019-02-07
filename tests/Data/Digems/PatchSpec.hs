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

type PatchRTree = Patch W CodesRTree Z

digemRTree :: RTree -> RTree -> PatchRTree
digemRTree a b = diff 1 (dfrom $ into @FamRTree a)
                          (dfrom $ into @FamRTree b)

applyRTree :: PatchRTree -> RTree -> Either String RTree
applyRTree p x = either Left (Right . unEl . dto @Z . unFix)
               $ apply p (dfrom $ into @FamRTree x)

applyRTree' :: PatchRTree -> RTree -> Maybe RTree
applyRTree' p = either (const Nothing) Just . applyRTree p

genSimilarTrees' :: Gen (RTree , RTree)
genSimilarTrees' = choose (0 , 4) >>= genSimilarTrees

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


spec :: Spec
spec = do
  describe "composes" $ do
    it "has copy as left and right id" $ property copy_composes
    it "is correct" $ property composes_correct

{-
[a , b , c] = ["k" :>: ["g" :>: ["l" :>: ["k" :>: []],"b" :>: []],"b" :>: ["b" :>: ["d" :>: [],"g" :>: [],"f" :>: [],"d" :>: []]],"e" :>: ["j" :>: ["e" :>: []],"h" :>: ["e" :>: [],"a" :>: []],"c" :>: ["m" :>: [],"i" :>: []]]],"m" :>: ["k" :>: ["c" :>: ["h" :>: []],"e" :>: ["d" :>: ["h" :>: ["m" :>: ["f" :>: []],"a" :>: ["g" :>: [],"g" :>: [],"e" :>: []],"j" :>: [],"i" :>: []],"h" :>: ["m" :>: ["f" :>: []],"a" :>: ["g" :>: [],"g" :>: [],"e" :>: []],"j" :>: [],"i" :>: []],"d" :>: ["d" :>: ["e" :>: [],"i" :>: []],"c" :>: ["j" :>: [],"l" :>: []]],"g" :>: ["g" :>: ["i" :>: [],"h" :>: [],"d" :>: []],"i" :>: [],"j" :>: ["e" :>: []],"g" :>: ["k" :>: [],"d" :>: [],"l" :>: []]]]],"a" :>: ["e" :>: ["e" :>: [],"e" :>: [],"e" :>: [],"b" :>: []],"m" :>: ["g" :>: ["g" :>: ["e" :>: [],"e" :>: [],"m" :>: [],"d" :>: []],"a" :>: ["a" :>: [],"a" :>: [],"a" :>: []]],"a" :>: ["m" :>: ["b" :>: [],"c" :>: [],"m" :>: [],"d" :>: []],"m" :>: ["a" :>: [],"l" :>: [],"h" :>: [],"g" :>: []]],"j" :>: []],"m" :>: ["i" :>: ["m" :>: [],"i" :>: ["i" :>: [],"i" :>: [],"f" :>: []]]]]]],"k" :>: ["g" :>: ["g" :>: ["l" :>: ["d" :>: [],"d" :>: [],"l" :>: [],"l" :>: []]],"b" :>: ["b" :>: [],"l" :>: []]],"b" :>: ["g" :>: ["b" :>: ["h" :>: [],"c" :>: [],"f" :>: [],"m" :>: []],"b" :>: ["j" :>: []],"l" :>: []]],"e" :>: ["i" :>: ["e" :>: [],"c" :>: []],"h" :>: ["a" :>: ["e" :>: [],"b" :>: [],"h" :>: [],"b" :>: []],"a" :>: []],"a" :>: ["m" :>: [],"m" :>: [],"m" :>: [],"g" :>: []]]]] 
-}

[a,b,c] = ["d" :>: ["j" :>: [],"f" :>: [],"e" :>: ["d" :>: [],"i" :>: [],"m" :>: []]]
          ,"h" :>: ["d" :>: ["b" :>: ["m" :>: [],"l" :>: [],"b" :>: [],"g" :>: []],"m" :>: ["g" :>: [],"g" :>: [],"g" :>: [],"d" :>: []],"j" :>: ["d" :>: [],"i" :>: [],"a" :>: ["k" :>: [],"a" :>: [],"f" :>: []]]],"d" :>: ["b" :>: ["m" :>: [],"l" :>: [],"b" :>: [],"g" :>: []],"m" :>: ["g" :>: [],"g" :>: [],"g" :>: [],"d" :>: []],"j" :>: ["d" :>: [],"i" :>: [],"a" :>: ["k" :>: [],"a" :>: [],"f" :>: []]]],"e" :>: ["e" :>: []],"c" :>: ["k" :>: ["a" :>: ["i" :>: [],"e" :>: [],"b" :>: [],"d" :>: []],"k" :>: ["g" :>: [],"l" :>: []],"g" :>: ["k" :>: []]]]]
          ,"f" :>: ["h" :>: ["h" :>: [],"a" :>: ["f" :>: [],"c" :>: []],"e" :>: ["d" :>: ["b" :>: []],"f" :>: ["k" :>: []],"m" :>: []]]]] 

check :: Bool
check = composes (digemRTree b c) (digemRTree a b)
