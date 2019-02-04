{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE TypeSynonymInstances  #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Data.Digems.Diff where

import Data.Proxy
import Data.Type.Equality
import Data.Function (on)
import Data.Functor.Const
import Data.Functor.Sum
import qualified Data.Map as M
import qualified Data.Set as S

import Control.Monad
import Control.Monad.State
import Control.Monad.Cont
import Control.Monad.Identity

import Generics.MRSOP.Util
import Generics.MRSOP.Base
import Generics.MRSOP.Digems.Treefix
import Generics.MRSOP.Digems.Digest

import qualified Data.WordTrie as T
import Data.Digems.Diff.Preprocess
import Data.Digems.MetaVar
import Data.Digems.Change
import Data.Digems.Change.Apply
import Unsafe.Coerce

-- * Utils
--
-- $utils
--

-- TODO: bubble this up to generics-mrsop
getFixSNat :: (IsNat ix) => Fix ki codes ix -> SNat ix
getFixSNat _ = getSNat (Proxy :: Proxy ix)

-- * Patches
--
--  $patchintro
-- 
--  A patch consists in two treefixes, for deletion
--  and insertion respectively and a set of swaps
--  and contractions of their holes. In Haskell, this
--  is too intricate to write on the type level, so
--  we place unique identifiers in the holes
--  and work with the invariant:
--
--  >  nub (forget ctxDel :: [Int]) == nub (forget ctxIns)
--
--  Where @forget@ returns the values in the holes.
--

-- |Instead of keeping unecessary information, a 'RawPatch' will
--  factor out the common prefix before the actual changes.
--
type RawPatch ki codes = UTx ki codes (CChange ki codes)

-- |A 'Patch' is a 'RawPatch' instantiated to 'I' atoms.
type Patch ki codes ix = UTx ki codes (CChange ki codes) (I ix)

-- * Diffing

-- |The data structure that captures which subtrees are shared
--  between source and destination. Besides providing an efficient
--  answer to the query: "is this tree shared?", it also gives a
--  unique identifier to that tree, allowing us to easily
--  build our n-holed treefix.
type IsSharedMap = T.Trie Int

-- |A tree smaller than the minimum height will never be shared.
type MinHeight = Int

-- |Given a merkelized fixpoint, builds a trie of hashes of
--  every subtree, as long as they are taller than
--  minHeight.
buildTrie :: MinHeight -> PrepFix ki codes ix -> T.Trie ()
buildTrie minHeight df = go df T.empty
  where
    go :: PrepFix ki codes ix -> T.Trie () -> T.Trie ()
    go (AnnFix (Const prep) rep) t
      = case sop rep of
          Tag _ p -> (if (treeHeight prep <= minHeight)
                      then id
                      else T.insert () (toW64s $ treeDigest prep))
                   . getConst
                   $ cataNP (elimNA (const (Const . getConst))
                                    (\af -> Const . go af . getConst))
                            (Const t) p

-- |Given two merkelized trees, returns the trie that indexes
--  the subtrees that belong in both, ie,
--
--  @forall t . t `elem` buildSharingTrie x y
--        ==> t `subtree` x && t `subtree` y@
--
--  Moreover, the Int that the Trie maps to indicates
--  the metavariable we should choose for that tree.
--
buildSharingTrie :: MinHeight
                 -> PrepFix ki codes ix
                 -> PrepFix ki codes ix
                 -> (Int , IsSharedMap)
buildSharingTrie minHeight x y
  = T.mapAccum (\i _ -> (i+1 , i)) 0
  $ T.zipWith (\_ _ -> ()) (buildTrie minHeight x)
                           (buildTrie minHeight y)

-- |Given the sharing mapping between source and destination,
--  we extract a tree prefix from a tree substituting every
--  shared subtree by a hole with its respective identifier.
--
--  In this fist iteration, opaque values are not shared.
--  This can be seen on the type-level since we are
--  using the 'ForceI' type.
extractUTx :: (IsNat ix)
           => MinHeight
           -> IsSharedMap
           -> PrepFix ki codes ix
           -> UTx ki codes (ForceI (Const Int :*: (Fix ki codes))) (I ix)
extractUTx minHeight tr (AnnFix (Const prep) rep)
  -- TODO: if the tree's height is smaller than minHeight we don't
  --       even have to look it up on the map
  = case T.lookup (toW64s $ treeDigest prep) tr of
      Nothing | Tag c p <- sop rep
              -> UTxPeel c $ mapNP extractAtom p
      Just i  -> UTxHole (ForceI $ Const i :*: Fix (mapRep forgetAnn rep))
  where
    extractAtom :: NA ki (PrepFix ki codes) at
                  -> UTx ki codes (ForceI (Const Int :*: Fix ki codes)) at
    extractAtom (NA_I i) = extractUTx minHeight tr i
    extractAtom (NA_K k) = UTxOpq k

-- |Given two treefixes, we will compute the longest path from
--  the root that they overlap and will factor it out.
--  This is somehow analogous to a @zipWith@
extractSpine :: forall ki codes ix
              . (Eq1 ki)
             => Int
             -> UTx ki codes MetaVarI (I ix)
             -> UTx ki codes MetaVarI (I ix)
             -> UTx ki codes (Sum (OChange ki codes) (CChange ki codes)) (I ix)
extractSpine i dx dy = utxMap (uncurry' go) $ utxLCP dx dy
  where
    go :: UTx ki codes MetaVarI at
       -> UTx ki codes MetaVarI at
       -> Sum (OChange ki codes) (CChange ki codes) at
    -- precond utx and uty are different
    go utx uty = let vx = utxGetHolesWith Exists utx
                     vy = utxGetHolesWith Exists uty
                     evx = toEx vx
                     evy = toEx vy
                  in if vy `S.isSubsetOf` vx
                     then InR $ CMatch evx (tr utx) (tr uty)
                     else InL $ OMatch evx (toEx $ S.difference vy vx) (tr utx) (tr uty)
    
    tr :: UTx ki codes MetaVarI at
       -> UTx ki codes (MetaVarIK ki) at
    tr = utxMap (\(ForceI x) -> NA_I x)

    toEx :: S.Set (Exists MetaVarI) -> S.Set (Exists (MetaVarIK ki))
    toEx = S.map (\(Exists (ForceI x)) -> Exists $ NA_I x)


-- |Combines changes until they are closed
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
                         fvs  = S.unions $ elimNP (either'' oCtxFree (const $ S.empty)) chgs 
                         bvs  = S.unions $ elimNP (either'' oCtxVars cCtxVars) chgs
                         fvs' = S.difference fvs bvs
                      in if S.null fvs'
                         then InR (UTxHole $ CMatch bvs (UTxPeel cx dels) (UTxPeel cx inss))
                         else InL (OMatch bvs fvs' (UTxPeel cx dels) (UTxPeel cx inss))
  where
    -- TODO: refactor this to Util
    either' :: (f x -> a x) -> (g x -> a x) -> Sum f g x -> a x
    either' l r (InL x) = l x
    either' l r (InR x) = r x

    either'' :: (f x -> a) -> (g x -> a) -> Sum f g x -> a
    either'' f g = getConst . either' (Const . f) (Const . g)
    
    fromInR :: Sum f g x -> Maybe (g x)
    fromInR (InL _) = Nothing
    fromInR (InR x) = Just x
    


-- |Diffs two generic merkelized structures.
--  The outline of the process is:
--
--    i)   Annotate each tree with the info we need (digest and height)
--    ii)  Build the sharing trie
--    iii) traverse both trees substituting each subtree
--         that is an element of the sharing trie by a hole
--    iv)  keep the holes that appear both in the insertion and
--         deletion treefixes
--
digems :: (Eq1 ki , Digestible1 ki , IsNat ix)
       => MinHeight
       -> Fix ki codes ix
       -> Fix ki codes ix
       -> Patch ki codes ix
digems mh x y
  = let dx      = preprocess x
        dy      = preprocess y
        (i, sh) = buildSharingTrie mh dx dy
        del'    = extractUTx mh sh dx
        ins'    = extractUTx mh sh dy
        holes   = utxGetHolesWith unForceI' del'
                    `S.intersection`
                  utxGetHolesWith unForceI' ins'
        ins     = utxRefine (refineHole holes) UTxOpq ins'
        del     = utxRefine (refineHole holes) UTxOpq del'
     in case closure (extractSpine i del ins) of
          -- TODO: prove in agda this is unreachable
          InL oc -> error "There are open changes"
          InR cc -> flip evalState i
                  $ utxRefineM (return . UTxHole) opqCopy cc
  where
    unForceI' :: ForceI (Const Int :*: x) at -> Int
    unForceI' (ForceI (Const i :*: _)) = i

    opqCopy :: ki k
            -> State Int (UTx ki codes (CChange ki codes) (K k))
    opqCopy ki = do
      i <- get
      put (i+1)
      return . UTxHole . changeCopy . NA_K . Annotate i $ ki

    -- Given a set of holes that show up in both the insertion
    -- and deletion treefixes, we traverse a treefix and keep only
    -- those. All other places where there could be a hole are
    -- translated to a 'SolidI'
    refineHole :: S.Set Int
               -> ForceI (Const Int :*: Fix ki codes) ix
               -> UTx ki codes MetaVarI ix
    refineHole s (ForceI (Const i :*: f))
      | i `S.member` s = UTxHole (ForceI $ Const i)
      | otherwise      = utxStiff (NA_I f)

-- ** Applying a Patch
--
-- $applyingapatch
--
-- Patch application really is trivial. Say we
-- are applying a patch @p@ against an element @x@,
-- first we match @x@ with the @ctxDel p@; upon
-- a succesfull match we record, in a 'Valuation',
-- which tree fell in which hole.
-- Then, we use the same valuation to inject
-- those trees into @ctxIns p@.
--
-- The only slight trick is that we need to
-- wrap our trees in existentials inside our valuation.

-- |Applying a patch is trivial, we simply project the
--  deletion treefix and inject the valuation into the insertion.
apply :: (TestEquality ki , Eq1 ki , Show1 ki, IsNat ix)
      => Patch ki codes ix
      -> Fix ki codes ix
      -> Either String (Fix ki codes ix)
apply patch x 
    -- since all our changes are closed, we can apply them locally
    -- over the spine.
    =   utxZipRep patch (NA_I x)
    >>= utxMapM (uncurry' termApply)
    >>= return . unNA_I . utxForget
  where
    unNA_I :: NA f g (I i) -> g i
    unNA_I (NA_I x) = x
