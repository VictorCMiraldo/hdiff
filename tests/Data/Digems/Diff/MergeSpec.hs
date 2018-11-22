{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DataKinds #-}
module Data.Digems.Diff.MergeSpec (spec) where

import qualified Data.Set as S

import Generics.MRSOP.Base
import Generics.MRSOP.Util
import Generics.MRSOP.Digems.Treefix

import Data.Digems.Diff.Patch
import Data.Digems.Diff.MetaVar
import Data.Digems.Diff.Merge
import Data.Digems.Diff.Show
import Languages.RTree

import Test.QuickCheck
import Test.Hspec

type PatchRTree = Patch W CodesRTree Z

digemRTree :: RTree -> RTree -> PatchRTree
digemRTree a b = digems 1 (dfrom $ into @FamRTree a)
                          (dfrom $ into @FamRTree b)

applyRTree :: PatchRTree -> RTree -> Either String RTree
applyRTree p x = either Left (Right . unEl . dto @Z . unFix)
               $ apply p (dfrom $ into @FamRTree x)

applyRTree' :: PatchRTree -> RTree -> Maybe RTree
applyRTree' p = either (const Nothing) Just . applyRTree p

--------------------------------------------
-- ** Manual Merge Examples

mustMerge :: String -> RTree -> RTree -> RTree -> SpecWith (Arg Property)
mustMerge lbl a o b
  = let a' = dfrom $ into @FamRTree a
        b' = dfrom $ into @FamRTree b
        o' = dfrom $ into @FamRTree o
        oa = digems 1 o' a'
        ob = digems 1 o' b'
        oaob = noConflicts (oa // ob)
        oboa = noConflicts (ob // oa)
     in do it (lbl ++ ": merge square commutes") $ do
             case (oaob , oboa) of
               (Just ab , Just ba)
                 -> case (apply ab a' , apply ba b') of
                     (Right c1 , Right c2)
                       -> eqFix eq1 c1 c2 `shouldBe` True
                     _ -> expectationFailure "apply failed"
               _ -> expectationFailure "has conflicts"

----------------------
-- Example 1

a1 , o1 , b1 :: RTree
a1 = "a" :>: [ "b" :>: []
             , "c" :>: []
             , "d" :>: []
             ]

o1 = "a" :>: [ "b" :>: []
             , "d" :>: []
             ]

b1 = "a" :>: [ "b'" :>: []
             , "d" :>: []
             ]

-------------------
-- Example 2

a2, o2, b2 :: RTree
a2 = "b" :>: [ "u" :>: [ "3" :>: [] ] , ".." :>: [] ]

o2 = "b" :>: [ "b" :>: [ "u" :>: [ "3" :>: [] ] , ".." :>: [] ]
             , "." :>: []
             ]

b2 = "b" :>: [ "b" :>: [ "u" :>: [ "4" :>: [] ] , "u" :>: [ ".." :>: [] ] ]
             , "." :>: []
             ]



spec :: Spec
spec = do
  describe "manual examples" $ do
    mustMerge "1" a1 o1 b1
    mustMerge "2" a2 o2 b2
