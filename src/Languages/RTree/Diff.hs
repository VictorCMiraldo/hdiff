{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE TypeApplications      #-}
module Languages.RTree.Diff where

import Generics.MRSOP.Base
import Generics.MRSOP.Util
import Generics.MRSOP.Holes

import Languages.RTree
import Data.Digems.Patch
import Data.Digems.Change
import Data.Digems.Diff
import Data.Digems.Patch.Show

type PatchRTree = Patch W CodesRTree Z

rbin :: RTree -> RTree -> RTree
rbin l r = "bin" :>: [l , r]

rlf :: String -> RTree
rlf = (:>: [])

x1 = rbin (rbin (rlf "t") (rbin (rlf "u") (rlf "k"))) (rlf "k")
y1 = rbin (rbin (rlf "t") (rbin (rlf "u") (rlf "k"))) (rlf "t")

digemRTreeH :: Int -> RTree -> RTree -> PatchRTree
digemRTreeH h a b = diff h (dfrom $ into @FamRTree a)
                           (dfrom $ into @FamRTree b)

digemRTreeHM :: DiffMode -> Int -> RTree -> RTree -> PatchRTree
digemRTreeHM m h a b = diffMode m h (dfrom $ into @FamRTree a)
                                    (dfrom $ into @FamRTree b)

digemRTree :: RTree -> RTree -> PatchRTree
digemRTree a b = diff 1 (dfrom $ into @FamRTree a)
                        (dfrom $ into @FamRTree b)

applyRTree :: PatchRTree -> RTree -> Either String RTree
applyRTree p x = either Left (Right . unEl . dto @Z . unFix)
               $ apply p (dfrom $ into @FamRTree x)

applyRTreeC :: CChange W CodesRTree (I Z) -> RTree -> Either String RTree
applyRTreeC p x = applyRTree (Hole' p) x

applyRTree' :: PatchRTree -> RTree -> Maybe RTree
applyRTree' p = either (const Nothing) Just . applyRTree p
