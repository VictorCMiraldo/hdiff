{-# LANGUAGE PolyKinds        #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE GADTs            #-}
module Data.Digems.Change.ThinningSpec (spec) where

import qualified Data.Set as S

import Generics.MRSOP.Base
import Generics.MRSOP.Util
import Generics.MRSOP.Digems.Treefix

import Data.Functor.Const
import Data.Exists
import Data.Digems.Patch
import Data.Digems.Patch.Diff
import Data.Digems.Patch.Show
import Data.Digems.Patch.Thinning as PT
import qualified Data.Digems.Change.Thinning as CT
import Data.Digems.MetaVar
import Data.Digems.Change
import Languages.RTree
import Languages.RTree.Diff

import Test.QuickCheck
import Test.Hspec

import Control.Monad.Except
import Control.Monad.State
import qualified Data.Map as M

thin_respect_spans :: Property
thin_respect_spans = forAll genSimilarTrees'' $ \(a , o , b)
  -> let oa = digemRTree o a
         ob = digemRTree o b
      in case PT.thin oa ob of
           Left err -> counterexample ("Thinninh failed with: " ++ show err) False
           Right oa' -> property $ applyRTree oa' o == Right a
               
-------------------------------

lf :: String -> RTree
lf x = x :>: []

bin :: RTree -> RTree -> RTree
bin l r = "bin" :>: [l , r]

a1 , o1 , b1 :: RTree
a1 = bin (bin (lf "w") (lf "z")) (bin (lf "x") (lf "y")) 
o1 = bin (bin (lf "x") (lf "y")) (bin (lf "w") (lf "z"))
b1 = bin (bin (lf "y") (lf "x")) (bin (lf "w") (lf "z"))

oa1 = digemRTree o1 a1
ob1 = digemRTree o1 b1

coa1 = distrCChange oa1
cob1 = distrCChange ob1 `withDisjNamesFrom` coa1

---------------------

a2 , o2 , b2 :: RTree
a2 = "e" :>: ["j" :>: []]
o2 = "e" :>: ["a" :>: ["j" :>: []],"a" :>: ["j" :>: []]]
b2 = "a" :>: ["j" :>: [],"e" :>: []]

oa2 = digemRTree o2 a2
ob2 = digemRTree o2 b2

coa2 = distrCChange oa2
cob2 = distrCChange ob2 `withDisjNamesFrom` coa2



spec :: Spec
spec = do
  describe "thin" $
    it "respects spans" $
      property thin_respect_spans


