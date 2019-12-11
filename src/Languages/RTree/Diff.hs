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

import Data.Functor.Const
import Data.Void
import Control.Monad.Except

import Generics.MRSOP.Base
import Generics.MRSOP.Holes
import Generics.MRSOP.HDiff.Digest

import Languages.RTree
import Data.HDiff.Base
import Data.HDiff.Base.Show
import Data.HDiff.Base.Apply
import Data.HDiff.Diff
import Data.HDiff.Diff.Preprocess

type PatchRTree = Patch W CodesRTree (I 'Z)

rbin :: RTree -> RTree -> RTree
rbin l r = "bin" :>: [l , r]

rlf :: String -> RTree
rlf = (:>: [])

x1 , y1 :: RTree
x1 = rbin (rbin (rlf "t") (rbin (rlf "u") (rlf "f"))) (rlf "k")
y1 = rbin (rbin (rlf "t") (rbin (rlf "u") (rlf "f"))) (rlf "t")

hdiffRTreeH :: Int -> RTree -> RTree -> PatchRTree
hdiffRTreeH h a b = diff h (dfrom $ into @FamRTree a)
                           (dfrom $ into @FamRTree b)

hdiffRTreeHM :: DiffMode -> Int -> RTree -> RTree -> PatchRTree
hdiffRTreeHM m h a b = diffOpts (diffOptionsDefault { doMode = m
                                                    , doMinHeight = h
                                                    , doOpaqueHandling = DO_OnSpine })
                                (dfrom $ into @FamRTree a)
                                (dfrom $ into @FamRTree b)

rtreeMerkle :: RTree -> Digest
rtreeMerkle a = getDig $ preprocess (na2holes $ NA_I $ dfrom $ into @FamRTree a)
  where
    getDig :: PrepFix a ki codes (Const Void) ix -> Digest
    getDig = treeDigest . getConst . holesAnn

hdiffRTree :: RTree -> RTree -> PatchRTree
hdiffRTree a b = diff 1 (dfrom $ into @FamRTree a)
                        (dfrom $ into @FamRTree b)

applyRTree :: PatchRTree -> RTree -> Either String RTree
applyRTree p x = maybe (Left "apply") (Right . unEl . dto @'Z . unFix . unNAI)
               $ patchApply p (NA_I . dfrom . into @FamRTree $ x)
  where
    unNAI :: NA f g ('I ix) -> g ix
    unNAI (NA_I r) = r

applyRTreeC :: Chg W CodesRTree ('I 'Z) -> RTree -> Either String RTree
applyRTreeC p x = applyRTree (Hole' p) x

applyRTree' :: PatchRTree -> RTree -> Maybe RTree
applyRTree' p = either (const Nothing) Just . applyRTree p


--------------


a = "m" :>: []
b = "l" :>: ["l" :>: [],"m" :>: [],"m" :>: []]
c = "a" :>: ["j" :>: [],"i" :>: [],"m" :>: []]

ab = chgDistr $ hdiffRTreeHM DM_NoNested 1 a b
bc = chgDistr $ hdiffRTreeHM DM_NoNested 1 b c
