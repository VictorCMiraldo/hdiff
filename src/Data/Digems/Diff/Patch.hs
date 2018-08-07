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

import Control.Monad

import Generics.MRSOP.Util
import Generics.MRSOP.Base

import Data.Digems.Generic.Treefix
import Data.Digems.Generic.Digest

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

-- * Auxiliary Treefix Functionality
--
-- Injecting and projecting our Treefixes will
-- return maps from numbers to trees.

-- |We start by wrapping the index of the fixpoint into
--  an existential.
data FixE :: (kon -> *) -> [[[Atom kon]]] -> * where
  SomeFix :: (IsNat ix) => Fix ki codes ix -> FixE ki codes

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

getFixSNat :: (IsNat ix) => Fix ki codes ix -> SNat ix
getFixSNat _ = getSNat (Proxy :: Proxy ix)

getUTxSNat :: (IsNat ix) => UTx ki codes ix f -> SNat ix
getUTxSNat _ = getSNat (Proxy :: Proxy ix)

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
