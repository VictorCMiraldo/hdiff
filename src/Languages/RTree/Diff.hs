{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE TypeApplications      #-}
module Languages.RTree.Diff where

import Data.Functor.Const
import Data.Void

import Generics.MRSOP.Base
import Generics.MRSOP.Holes
import Generics.MRSOP.HDiff.Digest

import Languages.RTree
import Data.HDiff.Patch
import Data.HDiff.Change
import Data.HDiff.Diff
import Data.HDiff.Diff.Preprocess

type PatchRTree = Patch W CodesRTree 'Z

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
applyRTree p x = either Left (Right . unEl . dto @'Z . unFix)
               $ apply p (dfrom $ into @FamRTree x)

applyRTreeC :: CChange W CodesRTree ('I 'Z) -> RTree -> Either String RTree
applyRTreeC p x = applyRTree (Hole' p) x

applyRTree' :: PatchRTree -> RTree -> Maybe RTree
applyRTree' p = either (const Nothing) Just . applyRTree p
