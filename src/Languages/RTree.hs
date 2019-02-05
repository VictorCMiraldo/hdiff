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
import Generics.MRSOP.Util
import Generics.MRSOP.TH
import Generics.MRSOP.Digems.Digest
import Generics.MRSOP.Digems.Renderer

import Data.Digems.Change.Classify (Ord1(..))

import Data.Text.Prettyprint.Doc (pretty)

import Control.Monad
import Test.QuickCheck

data RTree = String :>: [RTree]
  deriving (Eq , Show)

height :: RTree -> Int
height (n :>: []) = 0
height (n :>: ns) = 1 + maximum (map height ns)

data WKon = WString

data W :: WKon -> * where
  W_String  :: String  -> W WString

instance Eq1 W where
  eq1 (W_String s)  (W_String ss) = s == ss

instance Ord1 W where
  compare1 (W_String s) (W_String t) = compare s t

instance Digestible1 W where
  digest1 (W_String s)  = hashStr s

instance Renderer1 W where
  render1 (W_String s) = pretty s

instance Show1 W where
  show1 (W_String s)  = s

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
  t  <- genTree h
  t' <- go (height t) 1 t 
  return (t , t')
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

{-
genTree' :: Int -> Gen RTree
genTree' h
  | h >= 3    = choose (h - 3 , h + 3) >>= genTree
  | otherwise = genTree h

genPartition :: [a] -> Gen [Either a a]
genPartition = mapM coinflip
  where
    coinflip x = choose (True , False) >>= \c
      -> return $ if c then Left x else Right x

genDisjTrees :: RTree -> Gen (RTree , RTree)
genDisjTrees rt = oneof [ ins rt , del rt , mod rt ]
  where
    -- Generates an insertion
    ins :: RTree -> Gen (RTree , RTree)
    ins t = do
      n  <- genConName
      k  <- choose (1 , 3)
      ts <- vectorOf k (genTree' (height t))
-}
       


