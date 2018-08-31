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

import Generics.MRSOP.Util
import Generics.MRSOP.Base
import Generics.MRSOP.Digems.Renderer

-- * Generic Treefixes

-- |An untyped tree prefix, 'GUTx' is basically an n-hole context. The untyped
--  refers to the lack of an index that maintains the type of
--  the holes. This is an issue with Haskell in general. The Agda equivalent
--  keeps such index.
data GUTx :: (kon -> *) -> [[[Atom kon]]] -> (Atom kon -> *) -> Atom kon -> *  where
  GUTxHere :: phi i -> GUTx ki codes phi i
  GUTxPeel :: (IsNat n , IsNat i)
          => Constr (Lkup i codes) n
          -> NP (GUTx ki codes phi) (Lkup n (Lkup i codes))
          -> GUTx ki codes phi (I i)

-- |Returns the index of the GUTx as a singleton.
getGUTxSNat :: (IsNat ix) => GUTx ki codes f (I ix) -> SNat ix
getGUTxSNat _ = getSNat (Proxy :: Proxy ix)

-- |Our 'GUTx' is a higher order functor and can be mapped over.
gtxMapM :: (Monad m)
        => (forall i . f i -> m (g i))
        -> GUTx ki codes f i  
        -> m (GUTx ki codes g i)
gtxMapM f (GUTxHere x)       = GUTxHere   <$> f x
gtxMapM f (GUTxPeel c gtxnp) = GUTxPeel c <$> mapNPM (gtxMapM f) gtxnp

gtxMap :: (forall i . f i -> g i)
       -> GUTx ki codes f ix
       -> GUTx ki codes g ix
gtxMap f = runIdentity . gtxMapM (return . f)

-- |Similar to 'gtxMap', but allows to refine the structure of
--  a treefix if need be
gtxRefine :: (Monad m)
       => (forall iy . f iy -> m (GUTx ki codes g iy))
       -> GUTx ki codes f iy 
       -> m (GUTx ki codes g iy)
gtxRefine f (GUTxHere x)
  = f x
gtxRefine f (GUTxPeel c gtxnp)
  = GUTxPeel c <$> mapNPM (gtxRefine f) gtxnp

-- * Show instances

instance (Show1 ki , Show1 phi) => Show1 (NA ki phi) where
  show1 (NA_K ki) = show1 ki
  show1 (NA_I i)  = show1 i

instance Show1 p => Show1 (NP p) where
  show1 NP0 = "NP0"
  show1 (v :* vs)
    = show1 v ++ " :* " ++ show1 vs

instance (Show1 ki , Show1 f) => Show1 (GUTx ki codes f) where
  show1 (GUTxHere x)      = "[" ++ show1 x ++ "]"
  show1 (GUTxPeel c rest) = "(" ++ show c ++ "| " ++ show1 rest ++ ")"

-- * Untyped Treefixes

-- |The atoms of a treefix, 'TxAtom' can be either a solid value
--  or a metavariable. 
data TxAtom :: (kon -> *) -> [[[Atom kon]]]
            -> (Atom kon -> *)
            -> Atom kon -> * where
  Meta   :: phi a           -> TxAtom ki codes phi a
  SolidK :: ki k            -> TxAtom ki codes phi (K k)
  SolidI :: (IsNat ix)
         => Fix ki codes ix -> TxAtom ki codes phi (I ix) 

-- |MapMs over a 'TxAtom'
txatomMapM :: (Monad m)
           => (forall x . phi x -> m (chi x))
           -> TxAtom ki codes phi ix
           -> m (TxAtom ki codes chi ix)
txatomMapM f (Meta   x) = Meta <$> f x
txatomMapM f (SolidK x) = return $ SolidK x
txatomMapM f (SolidI x) = return $ SolidI x
 
-- |Maps over a 'TxAtom'
txatomMap :: (forall x . phi x -> chi x)
          -> TxAtom ki codes phi ix
          -> TxAtom ki codes chi ix
txatomMap f (Meta   x) = Meta (f x)
txatomMap f (SolidK x) = SolidK x
txatomMap f (SolidI x) = SolidI x
  
-- |A threefix, henceforth, is a value that can contain @phi@s
--  in its leaves.
type UTx ki codes phi ix = GUTx ki codes (TxAtom ki codes phi) (I ix)

-- |Maps a monadic action over a 'UTx'
utxMapM :: (Monad m)
        => (forall x . phi x -> m (chi x))
        -> UTx ki codes phi ix
        -> m (UTx ki codes chi ix)
utxMapM f = gtxMapM (txatomMapM f)
        
-- |A stiff treefix is one with no holes
utxStiff :: (IsNat ix) => Fix ki codes ix -> UTx ki codes f ix
utxStiff  = GUTxHere . SolidI

-- * Pretty Printing

{-
utxPretty :: forall ki fam codes f ix ann
           . (Show1 ki , Renderer ki fam codes)
          => Proxy fam
          -> (forall iy . f iy -> Chunk)
          -> UTx ki codes f ix
          -> Chunk
utxPretty pfam sx (GUTxHere x)
  = braces (brackets $ _)
utxPretty pfam sx gtx@(GUTxPeel c rest)
  = render pfam (getGUTxSNat gtx)
                (Tag c $ mapNP (_ . utxPretty pfam sx) rest)
                -- (Tag c $ mapNP (mapNA id (Const . (1000,) . gtxPretty pfam sx)) rest)

-}
