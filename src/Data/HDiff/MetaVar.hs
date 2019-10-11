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
module Data.HDiff.MetaVar where

import Data.Function (on)
import Data.Functor.Const
import Data.Type.Equality
--------------------------------------
import Generics.MRSOP.Util
import Generics.MRSOP.Base
--------------------------------------
import Data.Exists
import Generics.MRSOP.HDiff.Digest
import Generics.MRSOP.HDiff.Holes

-- |Given a functor from @Nat@ to @*@, lift it to work over @Atom@
--  by forcing the atom to be an 'I'.
data ForceI :: (Nat -> *) -> Atom kon -> * where
  ForceI :: (IsNat i) => { unForceI :: f i } -> ForceI f ('I i)

-- |A 'MetaVarI' can only take place of a recursive position.
type MetaVarI  = ForceI (Const Int)

-- |This is isomorphic to @const x &&& f@ on the type level.
data Annotate (x :: *) (f :: k -> *) :: k -> * where
  Annotate :: x -> f i -> Annotate x f i

instance (ShowHO f , Show x) => ShowHO (Annotate x f) where
  showHO (Annotate i f)
    = showHO f ++ "[" ++ show i ++ "]"

instance (EqHO f , Eq x) => EqHO (Annotate x f) where
  eqHO (Annotate x1 f1) (Annotate x2 f2) = x1 == x2 && eqHO f1 f2

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

instance (DigestibleHO ki) => DigestibleHO (MetaVarIK ki) where
  digestHO (NA_I (Const i))      = hashStr ("vari" ++ show i)
  digestHO (NA_K (Annotate i _)) = hashStr ("vark" ++ show i)

-- |Returns the metavariable forgetting about type information
metavarGet :: MetaVarIK ki at -> Int
metavarGet = elimNA go getConst
  where go (Annotate x _) = x

-- |Adds a number to a metavar
metavarAdd :: Int -> MetaVarIK ki at -> MetaVarIK ki at
metavarAdd n (NA_K (Annotate i x)) = NA_K $ Annotate (n + i) x
metavarAdd n (NA_I (Const i))      = NA_I $ Const    (n + i)

-- TODO: Goes away with Annotate
instance HasIKProjInj ki (MetaVarIK ki) where
  konInj    k        = NA_K (Annotate 0 k)
  varProj _ (NA_I _) = Just IsI
  varProj _ _        = Nothing

-- * Existential MetaVars

-- |Retrieves the int inside a existential 'MetaVarIK'
metavarIK2Int :: Exists (MetaVarIK ki) -> Int
metavarIK2Int (Exists (NA_I (Const i))) = i
metavarIK2Int (Exists (NA_K (Annotate i _))) = i

-- |Retrieves the int inside a existential 'MetaVarI'
metavarI2Int :: Exists MetaVarI -> Int
metavarI2Int (Exists (ForceI (Const i))) = i

-- |Injects a metavar over recursive positions
-- into one over opaque types and recursive positions
metavarI2IK :: MetaVarI ix -> MetaVarIK ki ix
metavarI2IK (ForceI x) = NA_I x

-- ** Instances over 'Exists'

instance Eq (Exists MetaVarI) where
  (==) = (==) `on` metavarI2Int

instance Ord (Exists MetaVarI) where
  compare = compare `on` metavarI2Int

instance Eq (Exists (MetaVarIK ki)) where
  (==) = (==) `on` metavarIK2Int

instance Ord (Exists (MetaVarIK ki)) where
  compare = compare `on` metavarIK2Int

