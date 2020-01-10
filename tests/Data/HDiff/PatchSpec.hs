{-# LANGUAGE PolyKinds        #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE GADTs            #-}
module Data.HDiff.PatchSpec (spec) where

import Data.Functor.Const

import Data.HDiff.Diff
import Data.HDiff.Base
import Data.HDiff.Compose
import Languages.RTree
import Languages.RTree.Diff

import GHC.Generics
import Generics.Simplistic

import Test.QuickCheck
import Test.Hspec hiding (after)

----------------------------------------------

copy_composes :: DiffMode -> Property
copy_composes mode = forAll genSimilarTrees' $ \(t1 , t2)
  -> let patch = hdiffRTreeHM mode 1 t1 t2
         mcpy  = Hole changeCopy :: PatchRTree
      in composes patch mcpy .&&. composes mcpy patch
 where
   changeCopy :: Chg RTreePrims RTree
   changeCopy = Chg (Hole $ Const 0) (Hole $ Const 0)

composes_correct :: DiffMode -> Property
composes_correct mode = forAll (choose (0 , 2) >>= genSimilarTreesN 3)
  $ \[a , b , c] ->
  let ab = hdiffRTreeHM mode 1 a b
      bc = hdiffRTreeHM mode 1 b c
   in case bc .! ab of
        Nothing -> counterexample "Not composable" False
        Just ac -> applyRTree ac a === Right c

composes_assoc :: DiffMode -> Property
composes_assoc mode = forAll (choose (0 , 2) >>= genSimilarTreesN 4)
  $ \[a , b , c , d] ->
  let ab = hdiffRTreeHM mode 1 a b
      bc = hdiffRTreeHM mode 1 b c
      cd = hdiffRTreeHM mode 1 c d
   in case (,) <$> (bc .! ab >>= (cd .!))
               <*> (cd .! bc >>= (.! ab))
          of
        Nothing          -> counterexample "Not composable" False
        Just (ad0 , ad1) -> property $ patchEq ad0 ad1


{-
  NOT TRUE!!!!

  check: ("f" :>: ["i" :>: [],"j" :>: [],"a" :>: []],"j" :>: [])

composes_non_reflexive :: Property
composes_non_reflexive = forAll (genSimilarTrees' `suchThat` uncurry (/=))
  $ \(t1 , t2)
  -> let patch = hdiffRTree t1 t2
      in composes patch patch === False
-}
           
diffModeSpec :: DiffMode -> Spec
diffModeSpec mode = do
  describe "composes" $ do
    it "has copy as left and right id" $ property (copy_composes mode)
    it "is correct"                    $ property (composes_correct mode)
    it "is associative"                $ property (composes_assoc mode)

spec :: Spec
spec = do
 flip mapM_ (enumFrom (toEnum 0)) $ \m ->
   describe ("Extraction (" ++ show m ++ ")") $ diffModeSpec m
