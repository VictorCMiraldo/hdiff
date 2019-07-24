{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators   #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes      #-}
{-# LANGUAGE DataKinds       #-}
{-# LANGUAGE PolyKinds       #-}
{-# LANGUAGE GADTs           #-}
module Data.Digems.Diff
  ( diffMode'
  , diffMode
  , diff
  , DiffMode(..)
  , module Data.Digems.Diff.Types
  ) where

import qualified Data.Set as S
import           Data.Proxy
import           Data.Void
import           Data.Functor.Const
import           Data.Functor.Sum

import           Control.Monad.State

import           Generics.MRSOP.Base
import           Generics.MRSOP.Holes
import           Generics.MRSOP.Digems.Digest

import qualified Data.WordTrie as T
import           Data.Digems.Diff.Types
import           Data.Digems.Diff.Modes
import           Data.Digems.Diff.Preprocess
import           Data.Digems.Patch
import           Data.Digems.MetaVar
import           Data.Digems.Change

-- |We use a number of 'PrePatch'es, that is, a utx with a distinguished prefix
-- and some pair of 'Holes's inside.
type PrePatch ki codes phi = Holes ki codes (Holes ki codes phi :*: Holes ki codes phi)

-- * Diffing
--

-- |Given a merkelized fixpoint, builds a trie of hashes of
--  every subtree, as long as they are taller than
--  minHeight. This trie keeps track of the arity, so
--  we can later annotate the trees that can be propper shares.
buildArityTrie :: MinHeight -> PrepFix a ki codes phi ix -> T.Trie Int
buildArityTrie minHeight df = go df T.empty
  where
    ins :: Digest -> T.Trie Int -> T.Trie Int
    ins = T.insertWith 1 (+1) . toW64s
    
    go :: PrepFix a ki codes phi ix -> T.Trie Int -> T.Trie Int
    go (Hole (Const prep) x) t
      | treeHeight prep <= minHeight = t
      -- shall we insert holes?
      | otherwise                    = t -- ins (treeDigest prep) t
    go (HOpq (Const prep) x) t
      | treeHeight prep <= minHeight = t
      -- shall we insert constants?
      | otherwise                    = t -- ins (treeDigest prep) t
    go (HPeel (Const prep) c p) t
      | treeHeight prep <= minHeight = t
      | otherwise
      = ins (treeDigest prep) $ getConst
      $ cataNP (\af -> Const . go af . getConst) (Const t) p
   
-- |Given two merkelized trees, returns the trie that indexes
--  the subtrees that belong in both, ie,
--
--  @forall t . t `elem` buildSharingTrie x y
--        ==> t `subtree` x && t `subtree` y@
--
--  Moreover, we keep track of both the metavariable supposed
--  to be associated with a tree and the tree's arity.
--
buildSharingTrie :: MinHeight
                 -> PrepFix a ki codes phi ix
                 -> PrepFix a ki codes phi ix
                 -> (Int , IsSharedMap)
buildSharingTrie minHeight x y
  = T.mapAccum (\i ar -> (i+1 , MAA i ar) ) 0
  $ T.zipWith (+) (buildArityTrie minHeight x)
                  (buildArityTrie minHeight y)

-- |Copy every 'HolesOpq' value in the outermost 'Holes', aka, the spine
issueOpqCopies :: forall ki codes phi at
                . (forall ix . phi ix -> MetaVarIK ki ix)
               -> Int
               -> PrePatch ki codes phi at
               -> PrePatch ki codes (MetaVarIK ki) at
issueOpqCopies meta maxvar
  = flip evalState maxvar
  . holesRefineAnnM (\_ (x :*: y) -> return $ Hole' $ holesMap meta x :*: holesMap meta y)
                    (const opqCopy)
  where
    opqCopy :: ki k -> State Int (PrePatch ki codes (MetaVarIK ki) ('K k))
    opqCopy ki = do
      i <- get
      put (i+1)
      let ann = NA_K . Annotate i $ ki
      return $ Hole' (Hole' ann :*: Hole' ann)

-- |Given two treefixes, we will compute the longest path from
--  the root that they overlap and will factor it out.
--  This is somehow analogous to a @zipWith@. Moreover, however,
--  we also copy the opaque values present in the spine by issuing
--  /"copy"/ changes
extractSpine :: forall ki codes phi at
              . (EqHO ki)
             => (forall ix . phi ix -> MetaVarIK ki ix)
             -> Int
             -> Holes ki codes phi at
             -> Holes ki codes phi at
             -> Holes ki codes (Sum (OChange ki codes) (CChange ki codes)) at
extractSpine meta i dx dy
  = holesMap (uncurry' change)
  $ issueOpqCopies meta i
  $ holesLCP dx dy

-- |Combines changes until they are closed
close :: Holes ki codes (Sum (OChange ki codes) (CChange ki codes)) at
      -> Holes ki codes (CChange ki codes) at
close utx = case closure utx of
              InR cc -> cc
              InL (OMatch used unused del ins)
                -> Hole' $ CMatch (S.union used unused) del ins
  where
    closure :: Holes ki codes (Sum (OChange ki codes) (CChange ki codes)) at
            -> Sum (OChange ki codes) (Holes ki codes (CChange ki codes)) at
    closure (HOpq _ k)       = InR $ HOpq' k
    closure (Hole' (InL oc)) = InL oc
    closure (Hole' (InR cc)) = InR $ Hole' cc
    -- There is some magic going on here. First we compute
    -- the recursive closures and check whether any of them is open.
    -- If not, we are done.
    -- Otherwise, we apply a bunch of "monad distributive properties" around.
    closure (HPeel _ cx dx)
      = let aux = mapNP closure dx
         in case mapNPM fromInR aux of
              Just np -> InR $ HPeel' cx np
              Nothing -> let chgs = mapNP (either' InL (InR . distrCChange)) aux
                             dels = mapNP (either' oCtxDel cCtxDel) chgs
                             inss = mapNP (either' oCtxIns cCtxIns) chgs
                             vx   = S.unions $ elimNP (either'' oCtxVDel cCtxVars) chgs 
                             vy   = S.unions $ elimNP (either'' oCtxVIns cCtxVars) chgs
                          in if vx == vy
                             then InR (Hole' $ CMatch vx (HPeel' cx dels) (HPeel' cx inss))
                             else InL (OMatch vx vy (HPeel' cx dels) (HPeel' cx inss))

    fromInR :: Sum f g x -> Maybe (g x)
    fromInR (InL _) = Nothing
    fromInR (InR x) = Just x

instance DigestibleHO (Const Void) where
  digestHO (Const imp) = error "DigestibleHO (Const Void)"

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
diffMode' :: (EqHO ki , DigestibleHO ki , DigestibleHO phi)
          => DiffMode
          -> MinHeight
          -> Holes ki codes phi at
          -> Holes ki codes phi at
          -> (Int , Delta (Holes ki codes (Sum phi (MetaVarIK ki))) at)
diffMode' mode mh x y
  = let dx      = preprocess x
        dy      = preprocess y
        (i, sh) = buildSharingTrie mh dx dy
        dx'     = tagProperShare sh dx
        dy'     = tagProperShare sh dy
        delins  = extractHoles mode mh sh (dx' :*: dy')
     in (i , delins)

-- |When running the diff for two fixpoints, we can
-- cast the resulting deletion and insertion context into
-- an actual patch.
diffMode :: (EqHO ki , DigestibleHO ki , IsNat ix)
         => DiffMode
         -> MinHeight
         -> Fix ki codes ix
         -> Fix ki codes ix
         -> Patch ki codes ix
diffMode mode mh x y
  = let (i , del :*: ins) = diffMode' mode mh (na2holes $ NA_I x)
                                              (na2holes $ NA_I y)
     in close (extractSpine cast i del ins)
 where 
   cast :: Sum (Const Void) f i -> f i
   cast (InR fi) = fi

diff :: (EqHO ki , DigestibleHO ki , IsNat ix)
     => MinHeight
     -> Fix ki codes ix
     -> Fix ki codes ix
     -> Patch ki codes ix
diff = diffMode DM_ProperShare
