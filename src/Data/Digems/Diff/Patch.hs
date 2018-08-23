{-# LANGUAGE RankNTypes    #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds     #-}
{-# LANGUAGE PolyKinds     #-}
{-# LANGUAGE GADTs         #-}
module Data.Digems.Diff.Patch where

import Data.Proxy
import Data.Type.Equality
import Data.Functor.Const
import qualified Data.Map as M
import qualified Data.Set as S

import Control.Monad
import Control.Monad.State
import Control.Monad.Identity

import Generics.MRSOP.Util
import Generics.MRSOP.Base
import Generics.MRSOP.Digems.Treefix
import Generics.MRSOP.Digems.Digest

import qualified Data.WordTrie as T
import Data.Digems.Diff.Preprocess

-- * Utils
--
-- $utils
--

getFixSNat :: (IsNat ix) => Fix ki codes ix -> SNat ix
getFixSNat _ = getSNat (Proxy :: Proxy ix)

-- |A patch consists in two treefixes, for deletion
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
type Patch = RawPatch (Const Int)

data RawPatch phi ki codes v
  = Patch { ctxDel :: UTx ki codes phi v
          , ctxIns :: UTx ki codes phi v
          }


patchMap :: (Monad m)
         => (forall ix . IsNat ix => phi ix -> m (chi ix))
         -> RawPatch phi ki codes v
         -> m (RawPatch chi ki codes v)
patchMap f (Patch d i) = Patch <$> utxMapM f d <*> utxMapM f i

-- * Diffing

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

-- |The data structure that captures which subtrees are shared
--  between source and destination. Besides providing an efficient
--  answer to the query: "is this tree shared?", it also gives a
--  unique identifier to that tree, allowing us to easily
--  build our n-holed treefix.
type IsSharedMap = T.Trie Int

-- |A tree smaller than the minimum height will never be shared.
type MinHeight = Int

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
                 -> IsSharedMap
buildSharingTrie minHeight x y
  = snd . T.mapAccum (\i _ -> (i+1 , i)) 0
  $ T.zipWith (\_ _ -> ()) (buildTrie minHeight x)
                           (buildTrie minHeight y)

-- |Given the sharing mapping between source and destination,
--  we extract a tree prefix from a tree substituting every
--  shared subtree by a hole with its respective identifier.
extractUTx :: (IsNat ix)
           => MinHeight
           -> IsSharedMap
           -> PrepFix ki codes ix
           -> UTx ki codes (Const Int :*: Fix ki codes) ix
extractUTx minHeight tr (AnnFix (Const prep) rep)
  -- TODO: if the tree's height is smaller than minHeight we don't
  --       even have to look it up on the map
  = case T.lookup (toW64s $ treeDigest prep) tr of
      Nothing | Tag c p <- sop rep
              -> UTxPeel c (mapNP (mapNA id (extractUTx minHeight tr)) p) 
      Just i  -> UTxHere (Const i :*: Fix (mapRep forgetAnn rep))

-- |Given a sharing map and a merkelized tree,
--  will return a treefix with 

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
digems :: (Digestible1 ki , IsNat ix)
       => MinHeight
       -> Fix ki codes ix
       -> Fix ki codes ix
       -> Patch ki codes ix
digems mh x y
  = let dx      = preprocess x
        dy      = preprocess y
        sharing = buildSharingTrie mh dx dy
        del'    = extractUTx mh sharing dx
        ins'    = extractUTx mh sharing dy
        holes   = execState (utxMapM getHole del') S.empty
                    `S.intersection`
                  execState (utxMapM getHole ins') S.empty
        ins     = runIdentity $ utxRefine (refineHole holes) ins'
        del     = runIdentity $ utxRefine (refineHole holes) del'
     in Patch del ins
  where
    getHole :: (Const Int :*: f) ix
            -> State (S.Set Int) ((Const Int :*: f) ix)
    getHole x@(Const i :*: f) = modify (S.insert i) >> return x

    refineHole :: (IsNat ix)
               => S.Set Int
               -> (Const Int :*: Fix ki codes) ix
               -> Identity (UTx ki codes (Const Int) ix)
    refineHole s (Const i :*: f)
      | i `S.member` s = return $ UTxHere (Const i)
      | otherwise      = return $ utxStiff f

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

-- |We start by wrapping the index of the fixpoint into
--  an existential.
data FixE :: (kon -> *) -> [[[Atom kon]]] -> * where
  SomeFix :: (IsNat ix) => Fix ki codes ix -> FixE ki codes

-- |A call to @fixeMatch fe f@ returns true when @fe == Somefix f@
fixeMatch :: (IsNat v , Eq1 ki)
          => FixE ki codes
          -> Fix ki codes v
          -> Bool
fixeMatch (SomeFix x) y
  = case heqFixIx x y of
      Nothing   -> False
      Just Refl -> eqFix eq1 x y

-- |And have our valuation be an assignment from
--  hole-id's to trees.
type Valuation ki codes
  = M.Map Int (FixE ki codes)

-- |Projects an assignment out of a treefix. This
--  function is inherently partial because the constructors
--  specified on a treefix might be different than
--  those present in the value we are using.
utxProj :: (Eq1 ki)
        => UTx ki codes (Const Int) ix
        -> Fix ki codes ix 
        -> Maybe (Valuation ki codes)
utxProj = go M.empty
  where    
    go :: (Eq1 ki)
       => Valuation ki codes
       -> UTx ki codes (Const Int) ix
       -> Fix ki codes ix
       -> Maybe (Valuation ki codes)
    go m (UTxHere (Const n)) t
      -- We have already seen this hole; we need to make
      -- sure the tree's match. We are performing the
      -- 'contraction' step here.
      | Just fixe <- M.lookup n m
      = guard (fixeMatch fixe t) >> return m
      -- Its the first time we see this hole id,
      -- we will just insert a new tree.
      | otherwise
      = Just (M.insert n (SomeFix t) m)
    go m (UTxPeel c utxnp) (Fix t)
      | Tag ct pt <- sop t
      = do Refl <- testEquality c ct
           getConst <$> cataNPM aux (return $ Const m) (zipNP utxnp pt)

    aux :: (Eq1 ki)
        => (NA ki (UTx ki codes (Const Int)) :*: NA ki (Fix ki codes)) ix
        -> Const (Valuation ki codes) xs
        -> Maybe (Const (Valuation ki codes) (ix : xs))
    aux (NA_K k1 :*: NA_K k2) (Const val)
      | eq1 k1 k2 = Just (Const val)
      | otherwise = Nothing
    aux (NA_I i1 :*: NA_I i2) (Const val) 
      = case testEquality (getUTxSNat i1) (getFixSNat i2) of
          Nothing   -> Nothing
          Just Refl -> Const <$> go val i1 i2

-- |Injects a valuation into a treefix producing a value,
--  when possible.
utxInj :: (IsNat ix)
       => UTx ki codes (Const Int) ix
       -> Valuation ki codes
       -> Maybe (Fix ki codes ix)
utxInj utx@(UTxHere (Const n)) m
  = do SomeFix y <- M.lookup n m
       Refl      <- testEquality (getFixSNat y) (getUTxSNat utx)
       return y
utxInj (UTxPeel c utxnp) m
  = (Fix . inj c) <$> mapNPM (mapNAM return (flip utxInj m)) utxnp

-- |Applying a patch is trivial, we simply project the
--  deletion treefix and inject the valuation into the insertion.
apply :: (Eq1 ki , IsNat ix)
      => Patch ki codes ix
      -> Fix ki codes ix
      -> Maybe (Fix ki codes ix)
apply (Patch del ins) x = utxProj del x >>= utxInj ins
