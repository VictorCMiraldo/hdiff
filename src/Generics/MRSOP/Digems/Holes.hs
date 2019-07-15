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
module Generics.MRSOP.Digems.Holes where

import Data.Proxy
import Data.Functor.Const
import Data.Type.Equality
import qualified Data.Set as S (insert , empty , Set)

import Control.Monad.Identity
import Control.Monad.State

import qualified Data.Text.Prettyprint.Doc as PP
--------------------------------
import Generics.MRSOP.Util
import Generics.MRSOP.Base
import Generics.MRSOP.Holes
--------------------------------
import Generics.MRSOP.Digems.Renderer

holesSNat :: (IsNat ix)
          => HolesAnn ann ki codes f ('I ix)
          -> SNat ix
holesSNat _ = getSNat (Proxy :: Proxy ix)

-- |Returns how many holes are inside a treefix
holesArity :: Holes ki codes f at -> Int
holesArity = length . holesGetHolesAnnWith' (const ())

{-
-- |Counts the number of subtrees with a given arity
utxMultiplicity :: Int -> Holes ki codes f at -> Int
utxMultiplicity k utx
  | utxArity utx == k = 1
  | otherwise = case utx of
      HPeel _ _ p -> sum $ elimNP (utxMultiplicity k) p
      _           -> 0
-}

-- |Returns the size of a treefix. Holes have size 0.
holesSize :: Holes ki codes f at -> Int
holesSize (Hole _ _) = 0
holesSize (HOpq _  _) = 1
holesSize (HPeel _ _ p) = 1 + sum (elimNP holesSize p)

-- * Show instances

instance (ShowHO ki , ShowHO f) => ShowHO (Holes ki codes f) where
  showHO (Hole _ x)      = "[" ++ showHO x ++ "]"
  showHO (HOpq _ k)       = showHO k
  showHO (HPeel _ c rest) = "(" ++ show c ++ "| " ++ showHO rest ++ ")"

-- |Pretty-prints a treefix using a specific function to
--  print holes.
holesPretty :: forall ki fam codes f at ann
             . (HasDatatypeInfo ki fam codes , RendererHO ki)
            => Proxy fam
            -> (PP.Doc ann -> PP.Doc ann) -- ^ styling
            -> (forall at' . f at' -> PP.Doc ann)
            -> Holes ki codes f at
            -> PP.Doc ann
holesPretty _pfam sty sx  (Hole _ x)
  = sty $ sx x
holesPretty _pfam sty _sx (HOpq _ k)
  = sty $ renderHO k
holesPretty pfam sty sx utx@(HPeel _ c rest)
  = renderNP pfam sty (holesSNat utx) c
  $ mapNP (Const . holesPretty pfam sty sx) rest

-- * Test Equality Instance
--
-- Are two treefixes indexes over the same atom?

-- TODO: remove this class too!
--       this is the same hack as Data.Digems.Diff.MetaVar.Annotate
--       All we need is a class 'IsOpq' comming from mrsop that
--       allows us to compare the indexes of 'ki' for equality.
class HasIKProjInj (ki :: kon -> *) (f :: Atom kon -> *) where
  konInj  :: ki k -> f ('K k)
  varProj :: Proxy ki -> f x -> Maybe (IsI x)

instance (HasIKProjInj ki phi) => HasIKProjInj ki (Holes ki codes phi) where
  konInj                   = HOpq'
  varProj pr (Hole _ h)    = varProj pr h
  varProj _  (HPeel _ _ _) = Just IsI
  varProj _  (HOpq _ _)    = Nothing

data IsI :: Atom kon -> * where
  IsI :: (IsNat i) => IsI ('I i)

getIsISNat :: IsI ('I i) -> SNat i
getIsISNat IsI = getSNat (Proxy :: Proxy i)

type HolesTestEqualityCnstr ki f
  = (TestEquality ki , TestEquality f , HasIKProjInj ki f)

instance (HolesTestEqualityCnstr ki f)
    => TestEquality (Holes ki codes f) where
  testEquality (HOpq _ kx) (HOpq _ ky)
    = testEquality kx ky >>= return . apply (Refl :: 'K :~: 'K)
  testEquality (Hole _ v) (Hole _ u)
    = testEquality v u
  testEquality (HOpq _ kx) (Hole _ v)
    = testEquality (konInj kx) v
  testEquality (Hole _ v) (HOpq _ ky)
    = testEquality v (konInj ky)
  testEquality x@(HPeel _ _ _) (Hole _ u)
    = do i@IsI <- varProj (Proxy :: Proxy ki) u
         Refl  <- testEquality (holesSNat x) (getIsISNat i)
         return Refl
  testEquality (Hole _ u) x@(HPeel _ _ _)
    = do i@IsI <- varProj (Proxy :: Proxy ki) u
         Refl  <- testEquality (holesSNat x) (getIsISNat i)
         return Refl
  testEquality x@(HPeel _ _ _) y@(HPeel _ _ _)
    = do Refl <- testEquality (holesSNat x) (holesSNat y)
         return Refl
  testEquality (HOpq _ _) (HPeel _ _ _) = Nothing
  testEquality (HPeel _ _ _) (HOpq _ _) = Nothing

