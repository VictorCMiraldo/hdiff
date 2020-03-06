{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE StandaloneDeriving    #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE TypeSynonymInstances  #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE DeriveDataTypeable    #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# OPTIONS_GHC -Wno-missing-signatures                 #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns                #-}
{-# OPTIONS_GHC -Wno-missing-pattern-synonym-signatures #-}
module Languages.RTree where

import Data.Type.Equality

import GHC.Generics
import Generics.Simplistic
import Generics.Simplistic.TH
import Generics.Simplistic.Digest

import Data.Text.Prettyprint.Doc (pretty)

import Control.Monad
import Test.QuickCheck

data RTree = String :>: [RTree]
  deriving (Eq , Show)

height :: RTree -> Int
height (_ :>: []) = 0
height (_ :>: ns) = 1 + maximum (map height ns)

-- Workflow: use
--   getTypesInvolved [ ''String ] [t| RTree |]
-- Then inspect the result,
--   :i TypesInvolved
-- get the list of types; then use emacs macros!

type RTreePrims = '[ String ]
type RTreeFam   = '[ RTree , [RTree] ]

deriving instance Generic RTree
instance Deep RTreePrims RTreeFam RTree 
instance Deep RTreePrims RTreeFam [ RTree ]

dfromRTree :: RTree -> SFix RTreePrims RTreeFam RTree
dfromRTree = dfrom

dtoRTree :: SFix RTreePrims RTreeFam RTree -> RTree
dtoRTree = dto


genConName :: Gen String
genConName = (:[]) <$> choose ('a' , 'm')

genTree :: Int -> Gen RTree
genTree h
  | h <= 0    = (:>:) <$> genConName <*> pure []
  | otherwise = (:>:) <$> genConName <*> genChildren
  where
    genChildren = do
      x <- choose (0, 4)
      vectorOf x $ genTree (h-1)

insertAt :: Int -> a -> [a] -> [a]
insertAt 0 x xs       = x : xs
insertAt n x (y : ys) = y : insertAt (n-1) x ys

genInsHere :: RTree -> Gen RTree
genInsHere t = do
  n  <- genConName
  k  <- choose (0 , 3)
  ns <- vectorOf k (genTree (height t))
  k' <- if length ns == 0
        then return 0
        else choose (0 , length ns - 1)
  return (n :>: insertAt k' t ns)

genSimilarTrees :: Int -> Gen (RTree , RTree)
genSimilarTrees h = do
  l <- genSimilarTreesN 2 h
  let [t1 , t2] = l
  return (t1 , t2)

genSimilarTreesN :: Int -> Int -> Gen [RTree]
genSimilarTreesN n0 h = do
  t  <- genTree h
  (t:) <$> replicateM (n0-1) (go (height t) 1 t)
  where
    go :: Int -> Int -> RTree -> Gen RTree
    go ht ch (n :>: ns) = do
      ns' <- mapM (go ht (ch + 1)) ns
      n'  <- frequency [ (ht , return n)
                       , (ch  , genConName) ]
      frequency $ [ (ch , genInsHere (n' :>: ns'))
                  , (ht , return (n' :>: ns'))
                  ] ++ (if length ns > 0
                      then [ (ch , elements ns') ] -- genDelHere 
                      else [] )

instance Arbitrary RTree where
  arbitrary = sized $ \n -> choose (1 , n `div` 2) >>= genTree

genSimilarTrees' :: Gen (RTree , RTree)
genSimilarTrees' = choose (0 , 4) >>= genSimilarTrees
 
genSimilarTrees'' :: Gen (RTree , RTree , RTree)
genSimilarTrees'' = choose (0 , 4) >>= genSimilarTreesN 3
                                   >>= \[t1 , t2 , t3] -> return (t1 , t2 , t3)


