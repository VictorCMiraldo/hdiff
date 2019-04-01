{-# LANGUAGE PolyKinds        #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE GADTs            #-}
module Data.Digems.Patch.UnifySpec (spec) where

import qualified Data.Set as S

import Generics.MRSOP.Base
import Generics.MRSOP.Util
import Generics.MRSOP.Digems.Treefix

import Data.Digems.Patch
import Data.Digems.Patch.Diff
import Data.Digems.Patch.Show
import Data.Digems.MetaVar
import Data.Digems.Change
import Data.Digems.Change.Unify
import Languages.RTree
import Languages.RTree.Diff

import Test.QuickCheck
import Test.Hspec

gen3Trees :: Gen (RTree , RTree , RTree)
gen3Trees = choose (0 , 1)
        >>= genSimilarTreesN 3
        >>= \[a , o , b] -> return (a , o , b)

a9 , o9 , b9 :: RTree
-- a9 = "x" :>: [ "k" :>: []  , "u" :>: []]
-- o9 = "x" :>: [ "u" :>: []  , "k" :>: []]
-- b9 = "x" :>: [ "u'" :>: [] , "k" :>: []]

a9 = "x" :>: []
o9 = "x" :>: [ "y" :>: [] ]
b9 = "x" :>: [ "b" :>: [] ]

oa = distrCChange $ digemRTree o9 a9
ob = distrCChange $ digemRTree o9 b9

Right (Just (ca , cb)) = unify oa ob

ra , rb :: PatchRTree

ra = UTxHole ca
rb = UTxHole cb

spec :: Spec
spec = do
  describe "Unification" $ do
    it "is correct for all spans" $ property $
      forAll gen3Trees $ \(a , o , b)
        -> let oa = distrCChange $ digemRTree o a
               ob = distrCChange $ digemRTree o b
            in case unify oa ob of
                 Left  err -> counterexample "Unify failed" False
                 Right r   -> maybe False (const True) r
                   ==> let Just (ca , cb) = r
                        in case (,) <$> applyRTreeC ca o <*> applyRTreeC cb o of
                             Right (a' , b') -> a' == a .&&. b' == b
                             Left err          -> counterexample (show err) False
    
