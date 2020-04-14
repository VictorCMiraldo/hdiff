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
module Languages.RTree.Diff where

import Languages.RTree
import Data.HDiff.Base
import Data.HDiff.Apply
import Data.HDiff.Diff

import Generics.Simplistic.Deep

type PatchRTree = Patch RTreePrims RTreeFam RTree

hdiffRTreeH :: Int -> RTree -> RTree -> PatchRTree
hdiffRTreeH h a b = diff h (dfromRTree a) (dfromRTree b)

hdiffRTreeHM :: DiffMode -> Int -> RTree -> RTree -> PatchRTree
hdiffRTreeHM m h a b = diffOpts (diffOptionsDefault { doMode = m
                                                    , doMinHeight = h
                                                    })
                                (dfromRTree a)
                                (dfromRTree b)

hdiffRTree :: RTree -> RTree -> PatchRTree
hdiffRTree a b = hdiffRTreeH 1 a b

applyRTree :: PatchRTree -> RTree -> Either String RTree
applyRTree p x = maybe (Left "applyRTree")
                       (Right . dtoRTree)
               $ patchApply p (dfromRTree x)

applyRTreeC :: Chg RTreePrims RTreeFam RTree -> RTree -> Either String RTree
applyRTreeC p x = applyRTree (Hole p) x

applyRTree' :: PatchRTree -> RTree -> Maybe RTree
applyRTree' p = either (const Nothing) Just . applyRTree p


{-

rbin :: RTree -> RTree -> RTree
rbin l r = "bin" :>: [l , r]

rlf :: String -> RTree
rlf = (:>: [])

x1 , y1 :: RTree
x1 = rbin (rbin (rlf "t") (rbin (rlf "u") (rlf "f"))) (rlf "k")
y1 = rbin (rbin (rlf "t") (rbin (rlf "u") (rlf "f"))) (rlf "t")

a = "m" :>: []
b = "l" :>: ["l" :>: [],"m" :>: [],"m" :>: []]
c = "a" :>: ["j" :>: [],"i" :>: [],"m" :>: []]

ab = chgDistr $ hdiffRTreeHM DM_NoNested 1 a b
bc = chgDistr $ hdiffRTreeHM DM_NoNested 1 b c

xx , yy :: Holes W CodesRTree (MetaVarIK W) ('I 'Z)
xx = Hole' (NA_I (Const 0))

yy = HPeel' CZ (Hole' (NA_K (Annotate 3 (W_String "lala")
                          )) :* HPeel' CZ Nil :* Nil)

-}
