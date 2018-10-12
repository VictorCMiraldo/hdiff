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
module Languages.BinTree where

import Generics.MRSOP.Base
import Generics.MRSOP.Util
import Generics.MRSOP.TH
import Generics.MRSOP.Digems.Digest

import Control.Monad
import Control.Monad.Identity
import Test.QuickCheck

data Tree
  = Bin Int Tree Tree
  | Leaf
  deriving (Eq , Show)

height :: Tree -> Int
height Leaf = 0
height (Bin _ l r) = 1 + max (height l) (height r)

genTree :: Int -> Gen Tree
genTree h
  | h <= 0    = return Leaf
  | otherwise = frequency [ (1 , return Leaf)
                          , (4 , Bin <$> arbitrary
                                     <*> genTree (h-1)
                                     <*> genTree (h-1))
                          ]

genSimilarTree :: Tree -> Gen Tree
genSimilarTree t = go 1 t
  where
    maxH = 3 + height t

    dst x y = abs (x - y)

    go ch Leaf = frequency [ (ch  , return Leaf)
                           , (maxH - ch, choose (0 , 3) >>= genTree)
                           ]
    go ch (Bin i l r) = do
      l' <- go (ch+1) l
      r' <- go (ch+1) r
      i' <- frequency [(maxH, return i)
                      ,(ch  , arbitrary)]
      frequency [(ch  , elements [l' , r'])
                ,(maxH, return $ Bin i' l' r')
                ,(maxH, return $ Bin i' l r')
                ,(maxH, return $ Bin i' l' r)
                ]

genOrthogonalTree :: Tree -> Tree -> Gen Tree
genOrthogonalTree Leaf Leaf = choose (0 , 3) >>= genTree
genOrthogonalTree (Bin i1 l1 r1) (Bin i2 l2 r2)
  | i1 /= i2 = Bin i1 <$> genOrthogonalTree l1 l2 <*> genOrthogonalTree r1 r2
  | i1 == i2 = do
    genL <- if l1 == l2
            then return [ return r1 ]
            else return []
    genR <- if r1 == r2
            then return [ return l1 ]
            else return []
    oneof $ genL
         ++ genR
         ++ [ Bin i1 <$> genOrthogonalTree l1 l2
                     <*> genOrthogonalTree r1 r2
            ]
genOrthogonalTree t _ = return t
               


      
