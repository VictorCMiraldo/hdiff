{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes    #-}
{-# LANGUAGE DataKinds     #-}
{-# LANGUAGE PolyKinds     #-}
{-# LANGUAGE GADTs         #-}
module Data.Digems.Patch.Diff where

import           Data.Function (on)
import qualified Data.Set as S
import           Data.Proxy
import           Data.Functor.Const
import           Data.Functor.Sum

import           Control.Monad.State

import           Generics.MRSOP.Base
import           Generics.MRSOP.AG 
import           Generics.MRSOP.Digems.Treefix
import           Generics.MRSOP.Digems.Digest

import qualified Data.WordTrie as T
import           Data.Digems.Patch
import           Data.Digems.Patch.Preprocess
import           Data.Digems.MetaVar
import           Data.Digems.Change

-- * Utils
--
-- $utils
--

-- TODO: bubble this up to generics-mrsop
getFixSNat :: (IsNat ix) => Fix ki codes ix -> SNat ix
getFixSNat _ = getSNat (Proxy :: Proxy ix)

-- |We use a number of 'PrePatch'es, that is, a utx with a distinguished prefix
-- and some pair of 'UTx's inside.
type PrePatch ki codes phi = UTx ki codes (UTx ki codes phi :*: UTx ki codes phi)

-- * Diffing

-- |The data structure that captures which subtrees are shared
--  between source and destination. Besides providing an efficient
--  answer to the query: "is this tree shared?", it also gives a
--  unique identifier to that tree, allowing us to easily
--  build our n-holed treefix.
type IsSharedMap = T.Trie MetavarAndArity

data MetavarAndArity = MAA { getMetavar :: Int , getArity :: Int }
  deriving (Eq , Show)
           

-- |A tree smaller than the minimum height will never be shared.
type MinHeight = Int

-- |Given a merkelized fixpoint, builds a trie of hashes of
--  every subtree, as long as they are taller than
--  minHeight. This trie keeps track of the arity, so
--  we can later annotate the trees that can be propper shares.
buildArityTrie :: (DigestibleHO ki)
               => MinHeight -> PrepFix a ki codes ix -> T.Trie Int
buildArityTrie minHeight df = go df T.empty
  where
    go :: (DigestibleHO ki)
       => PrepFix a ki codes ix -> T.Trie Int -> T.Trie Int
    go (AnnFix (Const prep) rep) t
      = case sop rep of
          Tag _ p -> (if (treeHeight prep <= minHeight)
                      then id
                      else T.insertWith 1 (+1) (toW64s $ treeDigest prep))
                   . getConst
                   $ cataNP (elimNA (\k  -> Const . insConst k . getConst)
                                    (\af -> Const . go af . getConst))
                            (Const t) p

    insConst :: (DigestibleHO ki) => ki k -> T.Trie Int -> T.Trie Int
    insConst opq = T.insertWith 1 (+1) $ toW64s (digestHO opq)

-- |Given two merkelized trees, returns the trie that indexes
--  the subtrees that belong in both, ie,
--
--  @forall t . t `elem` buildSharingTrie x y
--        ==> t `subtree` x && t `subtree` y@
--
--  Moreover, we keep track of both the metavariable supposed
--  to be associated with a tree and the tree's arity.
--
buildSharingTrie :: (DigestibleHO ki)
                 => MinHeight
                 -> PrepFix a ki codes ix
                 -> PrepFix a ki codes ix
                 -> (Int , IsSharedMap)
buildSharingTrie minHeight x y
  = T.mapAccum (\i ar -> (i+1 , MAA i ar) ) 0
  $ T.zipWith (+) (buildArityTrie minHeight x)
                  (buildArityTrie minHeight y)

tagProperShare :: forall a ki codes ix
                . (IsNat ix)
               => IsSharedMap
               -> PrepFix a ki codes ix
               -> PrepFix (Int , Bool) ki codes ix
tagProperShare ism = synthesizeAnn alg
  where
    alg :: Const (PrepData a) iy
        -> Rep ki (Const (PrepData (Int , Bool))) sum
        -> Const (PrepData (Int , Bool)) iy
    alg (Const oldPD) withArity =
      let -- First we lookup our current arity
          myar  = maybe 0 getArity $ T.lookup (toW64s $ treeDigest oldPD) ism
          -- then we get the maximum of the recursive arities
          -- note we add a '0' there to make sure this doesn't crash
          maxar = maximum (0 : elimRep (const 0) (fst . treeParm . getConst) id withArity)
          -- Finally, we are at a proper share IFF its subtrees
          -- show up at most as much as I do. The 'at most' is pretty
          -- important here for not all subtrees might have been put
          -- on the sharing map.
          isPS  = myar >= maxar
       in Const $ oldPD { treeParm = (max maxar myar , isPS) }
     
-- |Given the sharing mapping between source and destination,
--  we extract a tree prefix from a tree substituting every
--  shared subtree by a hole with its respective identifier.
--
--  In this fist iteration, opaque values are not shared.
--  This can be seen on the type-level since we are
--  using the 'ForceI' type.
extractUTx :: (DigestibleHO ki , IsNat ix)
           => MinHeight
           -> IsSharedMap
           -> PrepFix (Int , Bool) ki codes ix
           -> UTx ki codes (MetaVarIK ki) ('I ix)
extractUTx minHeight tr (AnnFix (Const prep) rep)
  -- TODO: if the tree's height is smaller than minHeight we don't
  --       even have to look it up on the map
  = let isPS  = snd $ treeParm prep
        isBig = minHeight < treeHeight prep
     in if not (isPS && isBig)
        then extractUTx' rep
        else case T.lookup (toW64s $ treeDigest prep) tr of
               Nothing -> extractUTx' rep
               Just i  -> UTxHole (NA_I $ Const $ getMetavar i)
  where
    extractUTx' rep = case sop rep of
                        Tag c p -> UTxPeel c $ mapNP extractAtom p
    
    extractAtom :: (DigestibleHO ki)
                => NA ki (PrepFix (Int , Bool) ki codes) at
                -> UTx ki codes (MetaVarIK ki) at
    extractAtom (NA_I i) = extractUTx minHeight tr i
    extractAtom (NA_K k) = case T.lookup (toW64s $ digestHO k) tr of
                             Just i  -> UTxHole (NA_K $ Annotate (getMetavar i) k)
                             Nothing -> UTxOpq k

{-
-- |Copy every 'UTxOpq' value in the outermost 'UTx', aka, the spine
issueOpqCopies :: forall ki codes phi at
                . (forall ix . phi ix -> MetaVarIK ki ix)
               -> Int
               -> PrePatch ki codes phi at
               -> PrePatch ki codes (MetaVarIK ki) at
issueOpqCopies meta maxvar
  = flip evalState maxvar
  . utxRefineM (\(x :*: y) -> return $ UTxHole $ utxMap meta x :*: utxMap meta y)
               opqCopy
  where
    opqCopy :: ki k -> State Int (PrePatch ki codes (MetaVarIK ki) ('K k))
    opqCopy ki = do
      i <- get
      put (i+1)
      let ann = NA_K . Annotate i $ ki
      return $ UTxHole (UTxHole ann :*: UTxHole ann)
-}

-- |Given two treefixes, we will compute the longest path from
--  the root that they overlap and will factor it out.
--  This is somehow analogous to a @zipWith@. Moreover, however,
--  we also copy the opaque values present in the spine by issuing
--  /"copy"/ changes
extractSpine :: forall ki codes at
              . (EqHO ki)
             => UTx ki codes (MetaVarIK ki) at
             -> UTx ki codes (MetaVarIK ki) at
             -> UTx ki codes (Sum (OChange ki codes) (CChange ki codes)) at
extractSpine dx dy
  = utxMap (uncurry' change)
  -- $ issueOpqCopies meta i
  $ utxLCP dx dy

-- |Combines changes until they are closed
close :: UTx ki codes (Sum (OChange ki codes) (CChange ki codes)) at
      -> UTx ki codes (CChange ki codes) at
close utx = case closure utx of
              InR cc -> cc
              InL (OMatch used unused del ins)
                -> UTxHole $ CMatch (S.union used unused) del ins
  where
    closure :: UTx ki codes (Sum (OChange ki codes) (CChange ki codes)) at
            -> Sum (OChange ki codes) (UTx ki codes (CChange ki codes)) at
    closure (UTxOpq k)         = InR $ UTxOpq k
    closure (UTxHole (InL oc)) = InL oc
    closure (UTxHole (InR cc)) = InR $ UTxHole cc
    -- There is some magic going on here. First we compute
    -- the recursive closures and check whether any of them is open.
    -- If not, we are done.
    -- Otherwise, we apply a bunch of "monad distributive properties" around.
    closure (UTxPeel cx dx)
      = let aux = mapNP closure dx
         in case mapNPM fromInR aux of
              Just np -> InR $ UTxPeel cx np
              Nothing -> let chgs = mapNP (either' InL (InR . distrCChange)) aux
                             dels = mapNP (either' oCtxDel cCtxDel) chgs
                             inss = mapNP (either' oCtxIns cCtxIns) chgs
                             vx   = S.unions $ elimNP (either'' oCtxVDel cCtxVars) chgs 
                             vy   = S.unions $ elimNP (either'' oCtxVIns cCtxVars) chgs
                          in if vx == vy
                             then InR (UTxHole $ CMatch vx (UTxPeel cx dels) (UTxPeel cx inss))
                             else InL (OMatch vx vy (UTxPeel cx dels) (UTxPeel cx inss))

    fromInR :: Sum f g x -> Maybe (g x)
    fromInR (InL _) = Nothing
    fromInR (InR x) = Just x

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
diff :: (EqHO ki , DigestibleHO ki , IsNat ix)
     => MinHeight
     -> Fix ki codes ix
     -> Fix ki codes ix
     -> Patch ki codes ix
diff mh x y
  = let dx      = preprocess x
        dy      = preprocess y
        (i, sh) = buildSharingTrie mh dx dy
        dx'     = tagProperShare sh dx
        dy'     = tagProperShare sh dy
        del     = extractUTx mh sh dx'
        ins     = extractUTx mh sh dy'
     in close (extractSpine del ins)
