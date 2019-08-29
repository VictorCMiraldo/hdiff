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
module Languages.RTree where

import Data.Type.Equality

import Generics.MRSOP.Base
import Generics.MRSOP.TH
import Generics.MRSOP.Digems.Digest
import Generics.MRSOP.Digems.Renderer

import Data.Text.Prettyprint.Doc (pretty)

import Control.Monad
import Test.QuickCheck

data RTree = String :>: [RTree]
  deriving (Eq , Show)

height :: RTree -> Int
height (_ :>: []) = 0
height (_ :>: ns) = 1 + maximum (map height ns)

data WKon = WString

data W :: WKon -> * where
  W_String  :: String  -> W 'WString

instance EqHO W where
  eqHO (W_String s)  (W_String ss) = s == ss

instance DigestibleHO W where
  digestHO (W_String s)  = hashStr s

instance RendererHO W where
  renderHO (W_String s) = pretty s

instance ShowHO W where
  showHO (W_String s)  = s

instance TestEquality W where
  testEquality (W_String _)  (W_String _)  = Just Refl

deriveFamilyWith ''W [t| RTree |]

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
insertAt n x (y : ys) = x : insertAt (n-1) x ys

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
  case l of
    [t1 , t2] -> return (t1 , t2)
    _         -> error "impossible"

genSimilarTreesN :: Int -> Int -> Gen [RTree]
genSimilarTreesN n h = do
  t  <- genTree h
  (t:) <$> replicateM (n-1) (go (height t) 1 t)
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


