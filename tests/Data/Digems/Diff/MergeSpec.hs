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
import Languages.RTree

import Test.QuickCheck
import Test.Hspec

type PatchRTree = Patch W CodesRTree Z

digemRTree :: RTree -> RTree -> PatchRTree
digemRTree a b = digems 1 (dfrom $ into @FamRTree a)
                          (dfrom $ into @FamRTree b)

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
     in do it (lbl ++ ": has no conflicts") $ do
             isJust oaob .&&. isJust oboa
           it (lbl ++ ": apply commutes") $ do
             case (oaob , oboa) of
               (Just ab , Just ba)
                 -> case (apply ab b' , apply ba a') of
                     (Right c1 , Right c2) -> property (eqFix eq1 c1 c2)
                     _ -> counterexample "apply failed" False
               _ -> property True -- the test above must have failed already!
  where
    isJust :: Maybe a -> Property
    isJust (Just _) = property True
    isJust Nothing  = counterexample "isJust: Nothing" False

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

spec :: Spec
spec = do
  describe "manual examples" $ do
    mustMerge "1" a1 o1 b1
