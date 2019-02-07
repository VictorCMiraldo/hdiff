{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE TypeApplications      #-}
module Languages.RTree.Diff where

import Generics.MRSOP.Base
import Generics.MRSOP.Util

import Languages.RTree
import Data.Digems.Patch
import Data.Digems.Patch.Diff

type PatchRTree = Patch W CodesRTree Z

digemRTree :: RTree -> RTree -> PatchRTree
digemRTree a b = diff 1 (dfrom $ into @FamRTree a)
                          (dfrom $ into @FamRTree b)

applyRTree :: PatchRTree -> RTree -> Either String RTree
applyRTree p x = either Left (Right . unEl . dto @Z . unFix)
               $ apply p (dfrom $ into @FamRTree x)

applyRTree' :: PatchRTree -> RTree -> Maybe RTree
applyRTree' p = either (const Nothing) Just . applyRTree p
