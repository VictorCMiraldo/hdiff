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
-- ** Merge Properties

genSimilarTrees' :: Gen (RTree , RTree)
genSimilarTrees' = choose (0 , 4) >>= genSimilarTrees

merge_id :: Property
merge_id = forAll genSimilarTrees' $ \(t1 , t2)
  -> let patch = digemRTree t1 t2
         iden  = digemRTree t1 t1
         mpid  = noConflicts (patch // iden)
         midp  = noConflicts (iden  // patch)
      in case (,) <$> mpid <*> midp of
           Nothing -> expectationFailure "has conflicts"
           Just (pid , idp) ->
             case (,) <$> applyRTree' pid t1 <*> applyRTree' idp t2 of
               Nothing -> expectationFailure "apply failed"
               Just (r1 , r2) -> (r1 , r2) `shouldBe` (t2 , t2)
         

merge_diag :: Property
merge_diag = forAll genSimilarTrees' $ \(t1 , t2)
  -> let patch = digemRTree t1 t2
      in case noConflicts (patch // patch) of
           Nothing -> expectationFailure "has conflicts"
           Just p  -> case applyRTree' p t2 of
             Nothing -> expectationFailure "apply failed"
             Just r  -> r `shouldBe` t2

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

-----------------
-- Example 3

a3 , o3 , b3 :: RTree
a3 = "x'" :>: [ "y" :>: [] , "z" :>: [] ]

o3 = "x" :>: [ "y" :>: [] , "z" :>: [] ]

b3 = "x" :>: [ "y'" :>: [] ]

---------------------------------
-- Example 4

a4 , o4 , b4 :: RTree
a4 = "y" :>: []
o4 = "x" :>: []
b4 = "y" :>: []

spec :: Spec
spec = do
  describe "properties" $ do
    it "p // id == p && id // p == id" $ merge_id
  
  describe "manual examples" $ do
    mustMerge "1" a1 o1 b1
    mustMerge "2" a2 o2 b2
    mustMerge "3" a3 o3 b3
    mustMerge "4" a4 o4 b4
