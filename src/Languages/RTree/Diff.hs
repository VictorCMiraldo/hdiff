{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE TypeApplications      #-}
module Languages.RTree.Diff where

import Generics.MRSOP.Base
import Generics.MRSOP.Util
import Generics.MRSOP.Digems.Treefix

import Languages.RTree
import Data.Digems.Patch
import Data.Digems.Change
import Data.Digems.Patch.Diff
import Data.Digems.Patch.Show

type PatchRTree = Patch W CodesRTree Z

rbin :: RTree -> RTree -> RTree
rbin l r = "bin" :>: [l , r]

rblock :: RTree -> RTree -> RTree
rblock l r = "ZZZ" :>: [l , r]

rlf :: String -> RTree
rlf = (:>: [])

x1 = rbin (rblock (rlf "t") (rbin (rlf "u") (rlf "l"))) (rlf "k")
y1 = rbin (rblock (rlf "t") (rbin (rlf "u") (rlf "l"))) (rlf "t")

digemRTree :: RTree -> RTree -> PatchRTree
digemRTree a b = diff 1 (dfrom $ into @FamRTree a)
                        (dfrom $ into @FamRTree b)

block :: (IsNat ix) => Fix W CodesRTree ix -> Maybe String
block xo@(Fix x) = case getFixSNat xo of
  IdxRTree -> case sop x of
                Tag CZ (NA_K (W_String str) :* _)
                  -> if str == "ZZZ" then Just str else Nothing
  _        -> Nothing

digemRTree' :: RTree -> RTree -> PatchRTree
digemRTree' a b = diff' 1 block
                          (dfrom $ into @FamRTree a)
                          (dfrom $ into @FamRTree b)


applyRTree :: PatchRTree -> RTree -> Either String RTree
applyRTree p x = either Left (Right . unEl . dto @Z . unFix)
               $ apply p (dfrom $ into @FamRTree x)

applyRTreeC :: CChange W CodesRTree (I Z) -> RTree -> Either String RTree
applyRTreeC p x = applyRTree (UTxHole p) x

applyRTree' :: PatchRTree -> RTree -> Maybe RTree
applyRTree' p = either (const Nothing) Just . applyRTree p

