{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}
module Generics.MRSOP.Digems.Treefix where

import Data.Proxy
import Data.Functor.Const

import Control.Monad.Identity

import Data.Text.Prettyprint.Doc

import Generics.MRSOP.Util
import Generics.MRSOP.Base
import Generics.MRSOP.Digems.Renderer

-- |An untyped tree prefix, 'UTx' is basically an n-hole context. The untyped
--  refers to the lack of an index that maintains the type of
--  the holes. This is an issue with Haskell in general. The Agda equivalent
--  keeps such index.
data UTx :: (kon -> *) -> [[[Atom kon]]] -> (Nat -> *) -> Nat -> *  where
  UTxHere :: (IsNat i)
          => phi i -> UTx ki codes phi i
  UTxPeel :: (IsNat n)
          => Constr (Lkup i codes) n
          -> NP (NA ki (UTx ki codes phi)) (Lkup n (Lkup i codes))
          -> UTx ki codes phi i

-- |Returns the index of the UTx as a singleton.
getUTxSNat :: (IsNat ix) => UTx ki codes f ix -> SNat ix
getUTxSNat _ = getSNat (Proxy :: Proxy ix)

-- |Our 'UTx' is a higher order functor and can be mapped over.
utxMapM :: (Monad m)
        => (forall i . IsNat i => f i -> m (g i))
        -> UTx ki codes f i  
        -> m (UTx ki codes g i)
utxMapM f (UTxHere x)       = UTxHere   <$> f x
utxMapM f (UTxPeel c utxnp) = UTxPeel c <$> mapNPM (mapNAM return (utxMapM f)) utxnp

utxMap :: (forall i . IsNat i => f i -> g i)
       -> UTx ki codes f ix
       -> UTx ki codes g ix
utxMap f = runIdentity . utxMapM (return . f)

-- |Similar to 'utxMap', but allows to refine the structure of
--  a treefix if need be
utxRefine :: (Monad m)
       => (forall iy . IsNat iy => f iy -> m (UTx ki codes g iy))
       -> UTx ki codes f iy 
       -> m (UTx ki codes g iy)
utxRefine f (UTxHere x)
  = f x
utxRefine f (UTxPeel c utxnp)
  = UTxPeel c <$> mapNPM (mapNAM return (utxRefine f)) utxnp

-- |A stiff treefix is one with no holes
utxStiff :: Fix ki codes ix -> UTx ki codes f ix
utxStiff (Fix x) = case sop x of
  Tag c p -> UTxPeel c (mapNP (mapNA id utxStiff) p)

-- * Pretty Printing

utxPretty :: forall ki fam codes f ix ann
           . (Show1 ki , Renderer ki fam codes , IsNat ix)
          => Proxy fam
          -> (forall iy . IsNat iy => f iy -> Doc ann)
          -> UTx ki codes f ix
          -> Doc ann
utxPretty pfam sx (UTxHere x)
  = braces (brackets $ sx x)
utxPretty pfam sx utx@(UTxPeel c rest)
  = render pfam (getUTxSNat utx)
                (Tag c $ mapNP (mapNA id (Const . (1000,) . utxPretty pfam sx)) rest)

-- * Show instances

instance (Show1 ki , Show1 phi) => Show1 (NA ki phi) where
  show1 (NA_K ki) = show1 ki
  show1 (NA_I i)  = show1 i

instance Show1 p => Show1 (NP p) where
  show1 NP0 = "NP0"
  show1 (v :* vs)
    = show1 v ++ " :* " ++ show1 vs

instance (Show1 ki , Show1 f) => Show1 (UTx ki codes f) where
  show1 (UTxHere x)      = "[" ++ show1 x ++ "]"
  show1 (UTxPeel c rest) = "(" ++ show c ++ "| " ++ show1 rest ++ ")"
