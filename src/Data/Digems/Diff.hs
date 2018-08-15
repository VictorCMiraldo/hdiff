{-# LANGUAGE GADTs     #-}
{-# LANGUAGE PolyKinds #-}
module Data.Digems.Diff where

import Data.Functor.Const

import Generics.MRSOP.Util
import Generics.MRSOP.Base

import qualified Data.WordTrie as T
import Data.Digems.Diff.Patch
import Data.Digems.Generic.Treefix
import Data.Digems.Generic.Digest

-- |Given a merkelized fixpoint, builds a trie of hashes of
--  every subtree.
buildTrie :: DigFix ki codes ix -> T.Trie ()
buildTrie df = go df T.empty
  where
    go :: DigFix ki codes ix -> T.Trie () -> T.Trie ()
    go (AnnFix (Const dig) rep) t
      = case sop rep of
          Tag _ p -> T.insert () (toW64s dig)
                   . getConst
                   $ cataNP (elimNA (const (Const . getConst))
                                    (\af -> Const . go af . getConst))
                            (Const t) p

-- |The data structure that captures which subtrees are shared
--  between source and destination. Besides providing an efficient
--  answer to the query: "is this tree shared?", it also gives a
--  unique identifier to that tree, allowing us to easily
--  build our n-holed treefix.
type IsSharedMap = T.Trie Int

-- |Given two merkelized trees, returns the trie that indexes
--  the subtrees that belong in both, ie,
--
--  @forall t . t `elem` buildSharingTrie x y
--        ==> t `subtree` x && t `subtree` y@
--
--  Moreover, the Int that the Trie maps to indicates
--  the metavariable we should choose for that tree.
--
buildSharingTrie :: DigFix ki codes ix
                 -> DigFix ki codes ix
                 -> IsSharedMap
buildSharingTrie x y
  = snd . T.mapAccum (\i _ -> (i+1 , i)) 0
  $ T.zipWith (\_ _ -> ()) (buildTrie x) (buildTrie y)

-- |Given the sharing mapping between source and destination,
--  we extract a tree prefix from a tree substituting every
--  shared subtree by a hole with its respective identifier.
extractUTx :: (IsNat ix)
           => IsSharedMap
           -> DigFix ki codes ix
           -> UTx ki codes ix (Const Int)
extractUTx tr (AnnFix (Const dig) rep)
  = case T.lookup (toW64s dig) tr of
      Nothing | Tag c p <- sop rep
              -> UTxPeel c (extractUTxNP tr p)
      Just i  -> UTxHere (Const i)
  where
    extractUTxNP :: T.Trie Int
                 -> PoA ki (DigFix ki codes) prod
                 -> UTxNP ki codes prod (Const Int)
    extractUTxNP tr NP0 = UTxNPNil
    extractUTxNP tr (NA_K ki :* ps)
      = UTxNPSolid ki (extractUTxNP tr ps)
    extractUTxNP tr (NA_I vi :* ps)
      = UTxNPPath (extractUTx tr vi) (extractUTxNP tr ps)

-- |Given a sharing map and a merkelized tree,
--  will return a treefix with 

-- |Diffs two generic merkelized structures.
digems :: (Digestible1 ki , IsNat ix)
       => Fix ki codes ix
       -> Fix ki codes ix
       -> Patch ki codes ix
digems x y
  = let dx      = auth x
        dy      = auth y
        sharing = buildSharingTrie dx dy
        del     = extractUTx sharing dx
        ins     = extractUTx sharing dy
     in Patch ins del
