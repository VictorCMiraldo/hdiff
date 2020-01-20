{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE GADTs                 #-}
module Data.HDiff.Diff
  ( diffOpts'
  , diffOpts
  , diff
  , DiffMode(..)
  , module Data.HDiff.Diff.Types
  ) where

import           Data.Functor.Const

import           Control.Monad.State

import           Generics.Simplistic
import           Generics.Simplistic.Util
import           Generics.Simplistic.Digest

import qualified Data.WordTrie as T
import           Data.HDiff.Diff.Types
import           Data.HDiff.Diff.Modes
import           Data.HDiff.Diff.Preprocess
import           Data.HDiff.Diff.Closure
import           Data.HDiff.Base
import           Data.HDiff.MetaVar

-- * Diffing
--

-- |Given a merkelized fixpoint, builds a trie of hashes of
--  every subtree, as long as they are taller than
--  minHeight. This trie keeps track of the arity, so
--  we can later annotate the trees that can be propper shares.
buildArityTrie :: DiffOptions -> PrepFix a prim ix -> T.Trie Int
buildArityTrie opts df = go df T.empty
  where
    ins :: Digest -> T.Trie Int -> T.Trie Int
    ins = T.insertWith 1 (+1) . toW64s

    minHeight = doMinHeight opts
    
    go :: PrepFix a prim ix -> T.Trie Int -> T.Trie Int
    go (PrimAnn (Const prep) _) t
      -- We only populat the sharing map if opaques are supposed
      -- to be handled as recursive trees
      | doOpaqueHandling opts == DO_AsIs = ins (treeDigest prep) t
      | otherwise                        = t
    -- TODO: think about holes. I'm posponing this until
    -- we actually use diffing things holes.
    -- go (Hole' (Const  _)    _) t = t
    go (SFixAnn (Const prep) p) t
      | treeHeight prep <= minHeight = t
      | otherwise = ins (treeDigest prep) (goR p t)

    goR :: SRep (PrepFix a prim) ix -> T.Trie Int -> T.Trie Int
    goR S_U1 t = t
    goR (S_L1 x) t = goR x t
    goR (S_R1 x) t = goR x t
    goR (S_M1 _ x) t = goR x t
    goR (x :**: y) t = goR y (goR x t)
    goR (S_K1 x) t = go x t
   
-- |Given two merkelized trees, returns the trie that indexes
--  the subtrees that belong in both, ie,
--
--  @forall t . t `elem` buildSharingTrie x y
--        ==> t `subtree` x && t `subtree` y@
--
--  Moreover, we keep track of both the metavariable supposed
--  to be associated with a tree and the tree's arity.
--
buildSharingTrie :: DiffOptions
                 -> PrepFix a prim ix
                 -> PrepFix a prim ix
                 -> (Int , IsSharedMap)
buildSharingTrie opts x y
  = T.mapAccum (\i ar -> (i+1 , MAA i ar) ) 0
  $ T.zipWith (+) (buildArityTrie opts x)
                  (buildArityTrie opts y)

-- |Given two treefixes, we will compute the longest path from
--  the root that they overlap and will factor it out.
--  This is somehow analogous to a @zipWith@. Moreover, however,
--  we also copy the opaque values present in the spine by issuing
--  /"copy"/ changes
extractSpine :: forall prim phi at
              . DiffOpaques
             -> (forall ix . phi ix -> MetaVar ix)
             -> Int
             -> Holes prim phi at
             -> Holes prim phi at
             -> Holes prim (Chg prim) at
extractSpine dopq meta maxI dx dy
  = holesMap (uncurry' Chg)
  $ issueOpqCopiesSpine
  $ lcp dx dy
 where
   issueOpqCopiesSpine :: Holes prim (Holes2 prim phi) at
                       -> Holes prim (Holes2 prim (MetaVar)) at
   issueOpqCopiesSpine
     = flip evalState maxI
     . holesRefineM (\(x :*: y) -> return $ Hole $ holesMap meta x
                                               :*: holesMap meta y)
                    (if dopq == DO_OnSpine
                         then doCopy
                         else noCopy)

   noCopy :: (PrimCnstr b prim)
          => b
          -> State Int (Holes prim (Holes2 prim (MetaVar)) b)
   noCopy kik = return (Prim kik)
                        
   doCopy :: (Elem b prim)
          => b -> State Int (Holes prim (Holes2 prim (MetaVar)) b)
   doCopy _ = do
     i <- get
     put (i+1)
     return $ Hole (Hole (Const i) :*: Hole (Const i))


-- |Diffs two generic merkelized structures.
--  The outline of the process is:
--
--    i)   Annotate each tree with the info we need (digest and height)
--    ii)  Build the sharing trie
--    iii) Identify the proper shares
--    iv)  Substitute the proper shares by a metavar in
--         both the source and deletion context
--    v)   Extract the spine and compute the closure.
--
diffOpts' :: forall prim at
           . (All Digestible prim)
          => DiffOptions
          -> SFix prim at
          -> SFix prim at
          -> (Int , Delta (Holes prim MetaVar) at)
diffOpts' opts x y
  = let dx      = preprocess x
        dy      = preprocess y
        (i, sh) = buildSharingTrie opts dx dy
        dx'     = tagProperShare sh dx
        dy'     = tagProperShare sh dy
        delins  = extractHoles (doMode opts) mkCanShare sh (dx' :*: dy')
     in (i , delins)
 where
   mkCanShare :: forall a ix
               . PrepFix a prim ix
              -> Bool
   mkCanShare (PrimAnn _ _)
     = doOpaqueHandling opts == DO_AsIs
   mkCanShare pr
     = doMinHeight opts < treeHeight (getConst $ getAnn pr)

-- |When running the diff for two fixpoints, we can
-- cast the resulting deletion and insertion context into
-- an actual patch.
diffOpts :: (All Digestible prim)
         => DiffOptions
         -> SFix prim ix
         -> SFix prim ix
         -> Patch prim ix
diffOpts opts x y
  = let (i , del :*: ins) = diffOpts' opts x y
     in case close $ extractSpine (doOpaqueHandling opts) id i del ins of
          Nothing -> error "invariant broke: has open variables"
          Just r  -> r

diff :: forall prim ix
      . (All Digestible prim)
     => MinHeight
     -> SFix prim ix
     -> SFix prim ix
     -> Patch prim ix
diff h = diffOpts (diffOptionsDefault { doMinHeight = h})
