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

import qualified Data.WordTrie as T
import Data.Digems.Generic.Treefix
import Data.Digems.Generic.Digest
import Data.Digems.Diff.Preprocess

-- * Utils
--
-- $utils
--

getFixSNat :: (IsNat ix) => Fix ki codes ix -> SNat ix
getFixSNat _ = getSNat (Proxy :: Proxy ix)

getUTxSNat :: (IsNat ix) => UTx ki codes ix f -> SNat ix
getUTxSNat _ = getSNat (Proxy :: Proxy ix)

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
data Patch ki codes v
  = Patch { ctxDel :: UTx ki codes v (Const Int)
          , ctxIns :: UTx ki codes v (Const Int)
          }

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
           -> UTx ki codes ix (Const Int :*: Fix ki codes)
extractUTx minHeight tr (AnnFix (Const prep) rep)
  -- TODO: if the tree's height is smaller than minHeight we don't
  --       even have to look it up on the map
  = case T.lookup (toW64s $ treeDigest prep) tr of
      Nothing | Tag c p <- sop rep
              -> UTxPeel c (extractUTxNP tr p)
      Just i  -> UTxHere (Const i :*: Fix (mapRep forgetAnn rep))
  where
    extractUTxNP :: T.Trie Int
                 -> PoA ki (PrepFix ki codes) prod
                 -> UTxNP ki codes prod (Const Int :*: Fix ki codes)
    extractUTxNP tr NP0 = UTxNPNil
    extractUTxNP tr (NA_K ki :* ps)
      = UTxNPSolid ki (extractUTxNP tr ps)
    extractUTxNP tr (NA_I vi :* ps)
      = UTxNPPath (extractUTx minHeight tr vi) (extractUTxNP tr ps)

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
       => Fix ki codes ix
       -> Fix ki codes ix
       -> Patch ki codes ix
digems x y
  = let dx      = preprocess x
        dy      = preprocess y
        sharing = buildSharingTrie 1 dx dy
        del'    = extractUTx 1 sharing dx
        ins'    = extractUTx 1 sharing dy
        holes   = execState (utxMap getHole del') S.empty
                    `S.intersection`
                  execState (utxMap getHole ins') S.empty
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
               -> Identity (UTx ki codes ix (Const Int))
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
        => UTx ki codes ix (Const Int)
        -> Fix ki codes ix
        -> Maybe (Valuation ki codes)
utxProj = go M.empty
  where    
    go :: (Eq1 ki)
       => Valuation ki codes
       -> UTx ki codes i (Const Int)
       -> Fix ki codes i
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
      = case sop t of
          Tag ct pt -> testEquality c ct
                   >>= \Refl -> goNP m utxnp pt

    goNP :: (Eq1 ki)
         => Valuation ki codes
         -> UTxNP ki codes prod (Const Int)
         -> PoA ki (Fix ki codes) prod
         -> Maybe (Valuation ki codes)
    goNP m UTxNPNil _           = return m
    goNP m (UTxNPSolid k utxnp) (NA_K ak :* p)
      | eq1 k ak  = goNP m utxnp p
      | otherwise = Nothing
    goNP m (UTxNPPath utx utxnp) (NA_I i :* p)
      = case testEquality (getFixSNat i) (getUTxSNat utx) of
          Nothing   -> Nothing
          Just Refl -> go m utx i >>= \m' -> goNP m' utxnp p
                     
-- |Injects a valuation into a treefix producing a value,
--  when possible.
utxInj :: (IsNat ix)
       => UTx ki codes ix (Const Int)
       -> Valuation ki codes
       -> Maybe (Fix ki codes ix)
utxInj utx@(UTxHere (Const n)) m
  = do SomeFix y <- M.lookup n m
       Refl      <- testEquality (getFixSNat y) (getUTxSNat utx)
       return y
utxInj (UTxPeel c utxnp) m
  = (Fix . inj c) <$> utxnpInj utxnp m
  where
    utxnpInj :: UTxNP ki codes prod (Const Int)
             -> Valuation ki codes
             -> Maybe (PoA ki (Fix ki codes) prod)
    utxnpInj UTxNPNil _
      = return NP0
    utxnpInj (UTxNPSolid k utxnp) m
      = (NA_K k :*) <$> utxnpInj utxnp m
    utxnpInj (UTxNPPath utx utxnp) m
      = (:*) <$> (NA_I <$> utxInj utx m) <*> utxnpInj utxnp m

-- |Applying a patch is trivial, we simply project the
--  deletion treefix and inject the valuation into the insertion.
apply :: (Eq1 ki , IsNat ix)
      => Patch ki codes ix
      -> Fix ki codes ix
      -> Maybe (Fix ki codes ix)
apply (Patch del ins) x = utxProj del x >>= utxInj ins
