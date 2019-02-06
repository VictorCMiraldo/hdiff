{-# LANGUAGE PolyKinds        #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE GADTs            #-}
module Data.Digems.Change.ClassifySpec (spec) where

import qualified Data.Set as S

import Generics.MRSOP.Base
import Generics.MRSOP.Util
import Generics.MRSOP.Digems.Treefix

import Data.Exists
import Data.Digems.Patch
import Data.Digems.Patch.Diff
import Data.Digems.Patch.Show
import Data.Digems.MetaVar
import Data.Digems.Change
import Data.Digems.Change.Classify
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

--------------------------------------------
-- ** Change Classification Unit Tests

changeClassDual :: ChangeClass -> ChangeClass
changeClassDual CDel = CIns
changeClassDual CIns = CDel
changeClassDual x    = x

mustClassifyAs :: String ->  RTree -> RTree -> [ChangeClass] -> SpecWith (Arg Bool)
mustClassifyAs lbl a b cls = do
  it (lbl ++ ": change class") $ do
    let patch = digemRTree a b
     in cls == utxGetHolesWith' changeClassify patch
     
  
----------------
-- Example 1

a1 , b1 :: RTree
a1 = "a" :>: [ "b" :>: []
             , "c" :>: []
             , "d" :>: []
             ]

b1 = "a" :>: [ "b'" :>: []
             , "d" :>: []
             ]


---------------
-- Example 2

a2 , b2 :: RTree
a2 = "x" :>: [ "k" :>: [] , "u" :>: []]
b2 = "x" :>: [ "u" :>: [] , "k" :>: []]


---------------
-- Example 3

a3 , b3 :: RTree
a3 = "x" :>: [ "k" :>: [ "a" :>: [] ] ]
b3 = "x" :>: [ "k" :>: [] , "a" :>: [] ]

----------------
-- Example 4

a4 , b4 :: RTree
a4 = "x" :>: [ "a" :>: [ "b" :>: [] ] , "c" :>: [] ]
b4 = "x" :>: [ "a" :>: [ "b" :>: ["c" :>: []]]]

----------------
-- Example 5

a5 , b5 :: RTree
a5 = "x" :>: [ "a" :>: [] , "b" :>: [] ]
b5 = "x" :>: [ "a" :>: [] , "new" :>: [] , "b" :>: [] ]

----------------
-- Example 6

a6 , b6 :: RTree
a6 = "x" :>: [ "a" :>: [] , "b" :>: [ "k" :>: [] ] ]
b6 = "x" :>: [ "a" :>: [] , "new" :>: [] , "b'" :>: [ "k" :>: [] ] ]

----------------
-- Example 7

a7 , b7 :: RTree
a7 = "x" :>: [ "a" :>: [ "aa" :>: [] , "ab" :>: []] , "b" :>: [ "bb" :>: [] ] ]
b7 = "x" :>: [ "a" :>: [ "aa" :>: [] , "ab" :>: [] , "bb" :>: [] ] , "bb" :>: [] ]

----------------
-- Example 8

a8 , b8 :: RTree
a8 = "x" :>: [ "y" :>: [] ] 
b8 = "a" :>: [ "b" :>: [] , "x" :>: [ "y" :>: [] ] , "c" :>: [] ]


spec :: Spec
spec = do
  describe "changeClassify: manual examples" $ do
    mustClassifyAs "1" a1 b1 [CDel , CMod , CId]
    mustClassifyAs "2" a2 b2 [CPerm , CId]
    mustClassifyAs "3" a3 b3 [CPerm , CId]
    mustClassifyAs "4" a4 b4 [CPerm , CId]
    mustClassifyAs "5" a5 b5 [CIns , CId , CId]
    mustClassifyAs "6" a6 b6 [CMod , CId , CId]
    mustClassifyAs "7" a7 b7 [CMod , CId]
    mustClassifyAs "8" a8 b8 [CIns]

