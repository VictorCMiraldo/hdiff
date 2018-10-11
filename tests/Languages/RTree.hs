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

import Generics.MRSOP.Base
import Generics.MRSOP.Util
import Generics.MRSOP.TH
import Generics.MRSOP.Digems.Digest

import Control.Monad
import Control.Monad.Identity
import Test.QuickCheck

data RTree = String :>: [RTree]
  deriving (Eq , Show)

genConName :: Gen String
genConName = resize 3 (listOf (choose ('a' , 'z')))

genTree :: Int -> Gen RTree
genTree h
  | h <= 0    = (:>:) <$> genConName <*> pure []
  | otherwise = (:>:) <$> genConName <*> genChildren
  where
    genChildren = do
      x <- choose (0, 4)
      vectorOf x $ genTree (h-1)

genPartition :: [a] -> Gen [Either a a]
genPartition = mapM coinflip
  where
    coinflip x = choose (True , False) >>= \c
      -> return $ if c then Left x else Right x

genMutatedTree :: RTree -> Gen RTree
genMutatedTree = undefined

codeltaMapM :: (Monad m) => (a -> m b) -> Either a a -> m (Either b b)
codeltaMapM f (Left x)  = Left <$> f x
codeltaMapM f (Right x) = Right <$> f x

onlyOne :: [a] -> Gen [Either a a]
onlyOne xs = go xs >>= oneof . map return
  where
    go []     = return []
    go (x:xs) = do
      xs' <- go xs
      return ((Right x : map Left xs) : map ((Left x) :) xs')


option :: Float -> (a -> Gen a) -> a -> Gen a
option thr f x = do
  let thrI :: Int = round (thr * 100)
  t <- choose (0 , 100)
  if t <= thrI
  then f x
  else return x

-- |Given a tree and a final result, give two trees
--  that could be merged into it.
genMerge :: RTree -> RTree -> Gen (RTree , RTree)
genMerge o ab
  = oneof [ ins o ab
          , del o ab
          , mod o ab
          ]
  where
    getRight (Right x : _)  = x
    getRight (_       : xs) = getRight xs
    
    ins o (ab :>: [])  = return (o , ab :>: [])
    ins o (ab :>: abs) = do
      abs' <- onlyOne abs
      let sel = getRight abs'
      (selA , selB) <- genMerge o sel
      let bs = map (either id (const selB)) abs'
      return (selA , ab :>: bs)

    del (o :>: []) ab = return (o :>: [] , ab)
    del (o :>: os) ab = do
      os' <- onlyOne os
      let sel = getRight os'
      (selA , selB) <- genMerge sel ab
      let as = map (either id (const selA)) os'
      return (o :>: as , selB)

    mod (o :>: os) (ab :>: abs)
      | length os /= length abs = oneof [ del (o :>: os)  (ab :>: abs)
                                        , ins (o :>: os)  (ab :>: abs)
                                        , ins (ab :>: os) (o  :>: abs)
                                        , del (ab :>: os) (o  :>: abs) ]
      | otherwise = do
          (as , bs) <- unzip <$> mapM (uncurry genMerge) (zip os abs)
          elements [ (o :>: as , ab :>: bs) , (ab :>: as , o :>: bs) ]
      
t1 = "Add" :>: [ "Var" :>: [ "x" :>: [] ] , "Var" :>: [ "y" :>: [] ] ]
t2 = "Sub" :>: [ "LOL" :>: [ "x" :>: [] ] ]
                   

{-

  do
  (a  , b)  <- elements [(o , ab) , (ab , o)]
  (as , bs) <- unzip <$> mapM (uncurry genMerge) (zip os abs)
-}

{-
genTreeMerge :: RTree -> Gen (RTree , RTree)
genTreeMerge (c :>: cs) = do
  cs' <- genPartition cs >>= mapM (codeltaMapM (option 0.5 genMutatedTree))
  let csA = map keepLefts  (zip cs cs')
  let csB = map keepRights (zip cs cs')
  _
  where
    keepLefts :: (a , Either a x) -> a
    keepLefts  (x , yx) = either id (const x) yx

    keepRights :: (a , Either x a) -> a
    keepRights (x , xy) = either (const x) id xy
-}





