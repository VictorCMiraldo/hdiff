{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE UndecidableSuperClasses  #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DefaultSignatures     #-}
{-# LANGUAGE StandaloneDeriving    #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}
module Generics.Simplistic.Constraints where

import Data.Proxy
import Data.Kind

-- Boolean predicate about being element of a list
type family IsElem (a :: k) (as :: [ k ]) :: Bool where
  IsElem a (a ': as) = 'True
  IsElem a (b ': as) = IsElem a as
  IsElem a '[]       = 'False

-- An actual proof that something is an element
data ElemPrf a as where
  Here  :: ElemPrf a (a ': as)
  There :: ElemPrf a as -> ElemPrf a (b ': as)

-- Constructing these proofs
class HasElem a as where
  hasElem :: ElemPrf a as
instance {-# OVERLAPPING #-} HasElem a (a ': as) where
  hasElem = Here
instance {-# OVERLAPPABLE #-}
    (HasElem a as) => HasElem a (b ': as) where
  hasElem = There hasElem

-- We will carry constructive information on the
-- constraint. Forcing IsElem to true 
type Elem    a as = (IsElem a as ~ 'True , HasElem a as)
type NotElem a as = IsElem a as ~ 'False

type family All (c :: k -> Constraint) (xs :: [k]) :: Constraint where
  All c '[]       = ()
  All c (x ': xs) = (c x , All c xs)

witness :: forall x xs c
         . (HasElem x xs , All c xs)
        => Proxy xs -> Witness c x
witness _ = witnessPrf (hasElem :: ElemPrf x xs)

witnessPrf :: (All c xs) => ElemPrf x xs -> Witness c x
witnessPrf Here      = Witness
witnessPrf (There p) = witnessPrf p

data Witness c x where
  Witness :: (c x) => Witness c x


{-

-- |An inhabitant of @ListPrf ls@ is *not* a singleton!
--  It only proves that @ls@ is, in fact, a type level list.
--  This is useful since it enables us to pattern match on
--  type-level lists whenever we see fit.
data ListPrf :: [k] -> * where
  LP_Nil  :: ListPrf '[]
  LP_Cons :: ListPrf l ->  ListPrf (x ': l)

-- |The @IsList@ class allows us to construct
--  'ListPrf's in a straight forward fashion.
class IsList (xs :: [k]) where
  listPrf :: ListPrf xs
instance IsList '[] where
  listPrf = LP_Nil
instance IsList xs => IsList (x ': xs) where
  listPrf = LP_Cons listPrf

class HasElemPrf x xs where
  elemPrf :: (Elem x xs) => ListPrf xs -> ElemPrf x xs
instance HasElemPrf x (x ': xs) where
  elemPrf _ = Here
instance (Elem x xs , HasElemPrf x xs) => HasElemPrf x (y ': xs) where
  elemPrf (LP_Cons rest) = There $ elemPrf rest

{-
class All c xs => WithWitness c xs where
  witness :: (Elem x xs) => Witness c x xs

instance (c x , All c xs) => WithWitness c (x ': xs) where
  witness = Witness (Proxy :: Proxy x)

data ElemPrf a as where
  EP_Yes :: Elem a as    => ElemPrf a as
  EP_No  :: NotElem a as => ElemPrf a as

class DecideElem a as where
  isElem :: ElemPrf a as

instance DecideElem a '[] where
  isElem = EP_No

instance {-# OVERLAPPING #-} DecideElem a (a ': as) where
  isElem = EP_Yes

instance {-# OVERLAPPABLE #-}
    (DecideElem a as) => DecideElem a (b ': as) where
  isElem = isElem
-}

-}
