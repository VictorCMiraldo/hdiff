{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE TypeSynonymInstances  #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
-- |Exports a bunch of functionality for handling metavariables
--  both over recursive positions only, with 'MetaVarI' and over
--  recursive positions and constants, 'MetaVarIK'.
module Data.Digems.MetaVar where

import Data.Function (on)
import Data.Functor.Const
import Data.Type.Equality

import Generics.MRSOP.Util
import Generics.MRSOP.Base
import Generics.MRSOP.Digems.Treefix

-- |Given a functor from @Nat@ to @*@, lift it to work over @Atom@
--  by forcing the atom to be an 'I'.
data ForceI :: (Nat -> *) -> Atom kon -> * where
  ForceI :: (IsNat i) => { unForceI :: f i } -> ForceI f (I i)

-- |A 'MetaVarI' can only take place of a recursive position.
type MetaVarI  = ForceI (Const Int)

-- |This is isomorphic to @const x &&& f@ on the type level.
data Annotate (x :: *) (f :: k -> *) :: k -> * where
  Annotate :: x -> f i -> Annotate x f i

instance (Show1 f , Show x) => Show1 (Annotate x f) where
  show1 (Annotate i f)
    = show1 f ++ "[" ++ show i ++ "]"

instance (Eq1 f , Eq x) => Eq1 (Annotate x f) where
  eq1 (Annotate x1 f1) (Annotate x2 f2) = x1 == x2 && eq1 f1 f2

instance (Eq x) => Eq1 (Const x) where
  eq1 (Const x) (Const y) = x == y

instance (TestEquality ki) => TestEquality (Annotate x ki) where
  testEquality (Annotate _ x) (Annotate _ y)
    = testEquality x y

-- |A 'MetaVarIK' can be over a opaque type and a recursive position
--
--  We keep the actual value of the constant around purely because
--  sometimes we need to compare the indexes for equality. It is possible
--  to remove that but this will require some instance like 'IsNat'
--  to be bubbled up all the way to generics-mrsop.
--
--  TODO: add a 'IsOpq' instance and remove Annotate altogether.
--        we need a method with type @defOpq :: Proxy k -> ki k@,
--        we can then piggyback on 'testEquality' for ki.
--        The 'HasIKProjInj' instance is part of this same hack.
type MetaVarIK ki = NA (Annotate Int ki) (Const Int)

-- |Returns the metavariable forgetting about type information
metavarGet :: MetaVarIK ki at -> Int
metavarGet = elimNA go getConst
  where go (Annotate x _) = x

-- |Adds a number to a metavar
metavarAdd :: Int -> MetaVarIK ki at -> MetaVarIK ki at
metavarAdd n (NA_K (Annotate i x)) = NA_K $ Annotate (n + i) x
metavarAdd n (NA_I (Const i))      = NA_I $ Const    (n + i)

instance Show (MetaVarIK ki at) where
  show (NA_I (Const v))      = "i" ++ show v
  show (NA_K (Annotate v _)) = "k" ++ show v

instance Eq (MetaVarIK ki at) where
  (NA_I (Const i))      == (NA_I (Const j))      = i == j
  (NA_K (Annotate v _)) == (NA_K (Annotate u _)) = v == u

-- TODO: Goes away with Annotate
instance HasIKProjInj ki (MetaVarIK ki) where
  konInj    k        = NA_K (Annotate 0 k)
  varProj _ (NA_I _) = Just IsI
  varProj _ _        = Nothing

-- * Existential MetaVars

data Exists (f :: k -> *) :: * where
  Exists :: f x -> Exists f

exMap :: (forall x . f x -> g x) -> Exists f -> Exists g
exMap f (Exists x) = Exists (f x)

exElim :: (forall x . f x -> a) -> Exists f -> a
exElim f (Exists x) = f x

-- |Retrieves the int inside a existential 'MetaVarIK'
metavarIK2Int :: Exists (MetaVarIK ki) -> Int
metavarIK2Int (Exists (NA_I (Const i))) = i
metavarIK2Int (Exists (NA_K (Annotate i _))) = i

-- |Retrieves the int inside a existential 'MetaVarI'
metavarI2Int :: Exists MetaVarI -> Int
metavarI2Int (Exists (ForceI (Const i))) = i

-- ** Instances over 'Exists'

instance Eq (Exists MetaVarI) where
  (==) = (==) `on` metavarI2Int

instance Ord (Exists MetaVarI) where
  compare = compare `on` metavarI2Int

instance Eq (Exists (MetaVarIK ki)) where
  (==) = (==) `on` metavarIK2Int

instance Ord (Exists (MetaVarIK ki)) where
  compare = compare `on` metavarIK2Int

