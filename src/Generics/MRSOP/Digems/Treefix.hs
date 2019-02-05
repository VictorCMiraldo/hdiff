{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ConstraintKinds       #-}
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
import Data.Void
import Data.Type.Equality
import qualified Data.Set as S (insert , empty , Set)

import Control.Monad.Identity
import Control.Monad.State

import qualified Data.Text.Prettyprint.Doc as PP
--------------------------------
import Generics.MRSOP.Util
import Generics.MRSOP.Base
--------------------------------
import Data.Exists
import Generics.MRSOP.Digems.Renderer

-- * Generic Treefixes

-- |An untyped tree prefix, 'UTx' is basically an n-hole context. The untyped
--  refers to the lack of an index that maintains the type of
--  the holes. This is an issue with Haskell in general. The Agda equivalent
--  keeps such indexes.
--
--  Essentially, we have the following isomorphism:
--
--  > UTx ki codes phi at =~= (phi :+: NA ki (Rep ki (UTx ki codes phi)))
--
--  That is, we are extending the representations with values of
--  type @phi@.
--
data UTx :: (kon -> *) -> [[[Atom kon]]] -> (Atom kon -> *) -> Atom kon -> *  where
  -- |A "hole" contains something of type @phi@ 
  UTxHole :: phi at -> UTx ki codes phi at
  -- |An opaque value
  UTxOpq  :: ki k   -> UTx ki codes phi (K k) 
  -- |A view over a constructor with its fields replaced
  --  by treefixes.
  UTxPeel :: (IsNat n , IsNat i)
          => Constr (Lkup i codes) n
          -> NP (UTx ki codes phi) (Lkup n (Lkup i codes))
          -> UTx ki codes phi (I i)

instance (Eq1 phi , Eq1 ki) => Eq (UTx ki codes phi ix) where
  utx == uty = and $ utxGetHolesWith' (uncurry' cmp) $ utxLCP utx uty
    where
      cmp :: UTx ki codes phi at -> UTx ki codes phi at -> Bool
      cmp (UTxHole x) (UTxHole y) = eq1 x y
      cmp (UTxOpq  x) (UTxOpq  y) = eq1 x y
      cmp _           _           = False

-- |Returns the index of the UTx as a singleton.
getUTxSNat :: (IsNat ix) => UTx ki codes f (I ix) -> SNat ix
getUTxSNat _ = getSNat (Proxy :: Proxy ix)

-- |Our 'UTx' is a higher order functor and can be mapped over.
utxMapM :: (Monad m)
        => (forall a . f a -> m (g a))
        -> UTx ki codes f at
        -> m (UTx ki codes g at)
utxMapM f (UTxHole x)       = UTxHole   <$> f x
utxMapM _ (UTxOpq k)        = return $ UTxOpq k
utxMapM f (UTxPeel c utxnp) = UTxPeel c <$> mapNPM (utxMapM f) utxnp

-- |Non-monadic version
utxMap :: (forall a . f a -> g a)
       -> UTx ki codes f at
       -> UTx ki codes g at
utxMap f = runIdentity . utxMapM (return . f)

-- |Since 'UTx' is just a free monad, we can join them!
utxJoin :: UTx ki codes (UTx ki codes f) at -> UTx ki codes f at
utxJoin (UTxHole x)   = x
utxJoin (UTxOpq  k)   = UTxOpq k
utxJoin (UTxPeel c p) = UTxPeel c (mapNP utxJoin p)

-- |Factors out the largest common prefix of two treefixes
--
--  It enjoys naturality properties with utxJoin:
--
--  >  utxJoin (utxMap fst (utxLCP p q)) == p
--  >  utxJoin (utxMap snd (utxLCP p q)) == q
--
utxLCP :: (Eq1 ki)
       => UTx ki codes f at
       -> UTx ki codes g at
       -> UTx ki codes (UTx ki codes f :*: UTx ki codes g) at
utxLCP (UTxOpq kx) (UTxOpq ky)
  | eq1 kx ky = UTxOpq kx
  | otherwise = UTxHole (UTxOpq kx :*: UTxOpq ky)
utxLCP (UTxPeel cx px) (UTxPeel cy py)
  = case testEquality cx cy of
      Nothing   -> UTxHole (UTxPeel cx px :*: UTxPeel cy py)
      Just Refl -> UTxPeel cx $ mapNP (uncurry' utxLCP) (zipNP px py)
utxLCP x y
  = UTxHole (x :*: y)

-- |Similar to 'gtxMap', but allows to refine the structure of
--  a treefix if need be
utxRefineM :: (Monad m)
           => (forall ix . f ix -> m (UTx ki codes g ix))
           -> (forall k  . ki k -> m (UTx ki codes g ('K k)))
           -> UTx ki codes f at
           -> m (UTx ki codes g at)
utxRefineM f _ (UTxHole x) = f x
utxRefineM _ g (UTxOpq k)  = g k
utxRefineM f g (UTxPeel c utxnp)
  = UTxPeel c <$> mapNPM (utxRefineM f g) utxnp

-- |Pure version of 'utxRefineM'
utxRefine :: (forall ix . f ix -> UTx ki codes g ix)
          -> (forall k  . ki k -> UTx ki codes g ('K k))
          -> UTx ki codes f at 
          -> UTx ki codes g at
utxRefine f g = runIdentity . utxRefineM (return . f) (return . g)

-- |Zips a UTx and a generic value together
utxZipRep :: (MonadPlus m)
          => UTx ki codes f at
          -> NA ki (Fix ki codes) at
          -> m (UTx ki codes (f :*: NA ki (Fix ki codes)) at)
utxZipRep (UTxHole i) x = return $ UTxHole (i :*: x)
utxZipRep (UTxOpq k)  _ = return $ UTxOpq k
utxZipRep (UTxPeel c d) (NA_I x)
  | Tag cx dx <- sop (unFix x)
  = case testEquality c cx of
      Nothing   -> mzero
      Just Refl -> UTxPeel cx <$> mapNPM (uncurry' utxZipRep) (zipNP d dx)

utxForget :: UTx ki codes (NA ki (Fix ki codes)) at
          -> NA ki (Fix ki codes) at
utxForget (UTxHole x)   = x
utxForget (UTxOpq k)    = NA_K k
utxForget (UTxPeel c d) = NA_I . Fix . inj c $ mapNP utxForget d
          
-- |Returns the metavariables in a UTx
utxGetHolesWith :: (Ord r) => (forall ix . f ix -> r) -> UTx ki codes f at -> S.Set r
utxGetHolesWith tr = flip execState S.empty . utxMapM (getHole tr)
  where
    -- Gets all holes from a treefix.
    getHole :: (Ord r)
            => (forall at . f at -> r)
            -> f ix
            -> State (S.Set r) (f ix)
    getHole f x = modify (S.insert $ f x) >> return x

utxGetHolesWith' :: (forall ix . f ix -> r) -> UTx ki codes f at -> [r]
utxGetHolesWith' tr = flip execState [] . utxMapM (getHole tr)
  where
    -- Gets all holes from a treefix.
    getHole :: (forall at . f at -> r)
            -> f ix
            -> State [r] (f ix)
    getHole f x = modify (f x :) >> return x

-- |Returns how many holes are inside a treefix
utxArity :: UTx ki codes f at -> Int
utxArity = length . utxGetHolesWith' (const ())

-- |Counts the number of subtrees with a given arity
utxMultiplicity :: Int -> UTx ki codes f at -> Int
utxMultiplicity k utx
  | utxArity utx == k = 1
  | otherwise = case utx of
      UTxPeel c p -> sum $ elimNP (utxMultiplicity k) p
      _           -> 0


-- * Show instances

instance (Show1 ki , Show1 phi) => Show1 (NA ki phi) where
  show1 (NA_K ki) = show1 ki
  show1 (NA_I i)  = show1 i

instance Show1 p => Show1 (NP p) where
  show1 NP0 = "NP0"
  show1 (v :* vs)
    = show1 v ++ " :* " ++ show1 vs

instance (Show1 ki , Show1 f) => Show1 (UTx ki codes f) where
  show1 (UTxHole x)      = "[" ++ show1 x ++ "]"
  show1 (UTxOpq k)       = show1 k
  show1 (UTxPeel c rest) = "(" ++ show c ++ "| " ++ show1 rest ++ ")"

-- |A stiff treefix is one with no holes anywhere.
utxStiff :: NA ki (Fix ki codes) at -> UTx ki codes f at
utxStiff (NA_I x) = case sop (unFix x) of
  Tag cx px -> UTxPeel cx (mapNP utxStiff px)
utxStiff (NA_K k) = UTxOpq k

-- |Reduces a treefix back to a tree
utxUnstiffM :: (Monad m)
           => (forall ix . f ix -> m (NA ki (Fix ki codes) ix))
           -> UTx ki codes f at
           -> m (NA ki (Fix ki codes) at)
utxUnstiffM red (UTxHole x)   = red x
utxUnstiffM _   (UTxOpq  k)   = return (NA_K k)
utxUnstiffM red (UTxPeel c p) = (NA_I . Fix . inj c) <$> mapNPM (utxUnstiffM red) p

-- |Pretty-prints a treefix using a specific function to
--  print holes.
utxPretty :: forall ki fam codes f at ann
           . (HasDatatypeInfo ki fam codes , Renderer1 ki)
          => Proxy fam
          -> (PP.Doc ann -> PP.Doc ann) -- ^ styling
          -> (forall at . f at -> PP.Doc ann)
          -> UTx ki codes f at
          -> PP.Doc ann
utxPretty pfam sty sx (UTxHole x)
  = sty $ sx x
utxPretty pfam sty sx (UTxOpq k)
  = sty $ render1 k
utxPretty pfam sty sx utx@(UTxPeel c rest)
  = renderNP pfam sty (getUTxSNat utx) c
  $ mapNP (Const . utxPretty pfam sty sx) rest

-- * Test Equality Instance
--
-- Are two treefixes indexes over the same atom?


-- TODO: remove this class too!
--       this is the same hack as Data.Digems.Diff.MetaVar.Annotate
--       All we need is a class 'IsOpq' comming from mrsop that
--       allows us to compare the indexes of 'ki' for equality.
class HasIKProjInj (ki :: kon -> *) (f :: Atom kon -> *) where
  konInj  :: ki k -> f (K k)
  varProj :: Proxy ki -> f x -> Maybe (IsI x)

instance (HasIKProjInj ki phi) => HasIKProjInj ki (UTx ki codes phi) where
  konInj                   = UTxOpq
  varProj pr (UTxHole h)   = varProj pr h
  varProj pr (UTxPeel _ _) = Just IsI
  varProj pr (UTxOpq _)    = Nothing

data IsI :: Atom kon -> * where
  IsI :: (IsNat i) => IsI (I i)

getIsISNat :: IsI (I i) -> SNat i
getIsISNat IsI = getSNat (Proxy :: Proxy i)

type UTxTestEqualityCnstr ki f
  = (TestEquality ki , TestEquality f , HasIKProjInj ki f)

instance (UTxTestEqualityCnstr ki f)
    => TestEquality (UTx ki codes f) where
  testEquality (UTxOpq kx) (UTxOpq ky)
    = testEquality kx ky >>= return . apply (Refl :: K :~: K)
  testEquality (UTxHole v) (UTxHole u)
    = testEquality v u
  testEquality (UTxOpq kx) (UTxHole v)
    = testEquality (konInj kx) v
  testEquality (UTxHole v) (UTxOpq ky)
    = testEquality v (konInj ky)
  testEquality x@(UTxPeel c p) (UTxHole u)
    = do i@IsI <- varProj (Proxy :: Proxy ki) u
         Refl  <- testEquality (getUTxSNat x) (getIsISNat i)
         return Refl
  testEquality (UTxHole u) x@(UTxPeel c p)
    = do i@IsI <- varProj (Proxy :: Proxy ki) u
         Refl  <- testEquality (getUTxSNat x) (getIsISNat i)
         return Refl
  testEquality x@(UTxPeel _ _) y@(UTxPeel _ _)
    = do Refl <- testEquality (getUTxSNat x) (getUTxSNat y)
         return Refl

