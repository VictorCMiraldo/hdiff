{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE TypeSynonymInstances  #-}
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# OPTIONS_GHC -Wno-orphans       #-}
-- |Useful utilities we need accross multiple modules.
module Generics.Simplistic.Util
  ( -- * Utility Functions and Types
    (&&&) , (***)
  , (:->) , (<.>)

    -- * Poly-kind indexed product functionality
  , (:*:)(..) , Delta , curry' , uncurry' , delta , deltaMap

    -- * Poly-kind indexed sums
  , Sum(..) , either' , either''

    -- * Type-level Naturals
  , Nat(..) , proxyUnsuc
  , SNat(..) , snat2int
  , IsNat(..) , getNat , getSNat'

    -- * Higher-order Eq and Show
  , EqHO(..) , ShowHO(..)

    -- * Existential type
  , Exists(..) , exElim , exMapM , exMap

    -- * Elem functionality
  , Elem , NotElem , HasElem(..) , ElemPrf(..) , IsElem

    -- * Witnessing and All constraints
  , All , Witness(..) , witness , witnessPrf
  ) where

import Data.Proxy
import Data.Kind
import Data.Type.Equality
import Data.Functor.Sum
import Data.Functor.Const
import Control.Arrow ((***) , (&&&))
import GHC.Generics ((:*:)(..))


-- |Lifted curry
curry' :: ((f :*: g) x -> a) -> f x -> g x -> a
curry' f fx gx = f (fx :*: gx)

-- |Lifted uncurry
uncurry' :: (f x -> g x -> a) -> (f :*: g) x -> a
uncurry' f (fx :*: gx) = f fx gx

-- |Natural transformations
type f :-> g = forall n . f n -> g n

-- |Diagonal indexed functor
type Delta f = f :*: f

-- |Duplicates its argument
delta :: f :-> Delta f
delta fx = fx :*: fx

-- |Applies the same function to both components of the pair
deltaMap :: (f :-> g) -> Delta f :-> Delta g
deltaMap f (x :*: y) = f x :*: f y

-- |Higher-order sum eliminator
either' :: (f :-> r) -> (g :-> r) -> Sum f g :-> r
either' f _ (InL x) = f x
either' _ g (InR x) = g x

-- |Just like 'either'', but the result type is of kind Star
either'' :: (forall x . f x -> a) -> (forall y . g y -> a) -> Sum f g r -> a
either'' f g = getConst . either' (Const . f) (Const . g)

infixr 8 <.>
-- |Kleisli Composition
(<.>) :: (Monad m) => (b -> m c) -> (a -> m b) -> a -> m c
f <.> g = (>>= f) . g

-- |Type-level Peano Naturals
data Nat = S Nat | Z
  deriving (Eq , Show)

-- |Typelevel predecessor operation
proxyUnsuc :: Proxy ('S n) -> Proxy n
proxyUnsuc _ = Proxy

-- |Singleton Term-level natural
data SNat :: Nat -> * where
  SZ ::           SNat 'Z
  SS :: SNat n -> SNat ('S n)

-- |Returns @n@ as a first class integer.
snat2int :: SNat n -> Integer
snat2int SZ     = 0
snat2int (SS n) = 1 + snat2int n

-- |And their conversion to term-level integers.
class IsNat (n :: Nat) where
  getSNat :: Proxy n -> SNat n
instance IsNat 'Z where
  getSNat _ = SZ
instance IsNat n => IsNat ('S n) where
  getSNat p = SS (getSNat $ proxyUnsuc p)

getNat :: (IsNat n) => Proxy n -> Integer
getNat = snat2int . getSNat

getSNat' :: forall (n :: Nat). IsNat n => SNat n
getSNat' = getSNat (Proxy :: Proxy n)

instance TestEquality SNat where
  testEquality SZ     SZ     = Just Refl
  testEquality (SS n) (SS m)
    = case testEquality n m of
        Nothing   -> Nothing
        Just Refl -> Just Refl
  testEquality _      _      = Nothing

-- |Higher order , poly kinded, version of 'Eq'
class EqHO (f :: ki -> *) where
  eqHO :: forall k . f k -> f k -> Bool

instance Eq a => EqHO (Const a) where
  eqHO (Const a) (Const b) = a == b

instance (EqHO f, EqHO g) => EqHO (f :*: g) where
  eqHO (fx :*: gx) (fy :*: gy) = eqHO fx fy && eqHO gx gy

instance (EqHO f, EqHO g) => EqHO (Sum f g) where
  eqHO (InL fx) (InL fy) = eqHO fx fy
  eqHO (InR gx) (InR gy) = eqHO gx gy
  eqHO _        _        = False

-- |Higher order, poly kinded, version of 'Show'; We provide
-- the same 'showsPrec' mechanism. The documentation of "Text.Show"
-- has a good example of the correct usage of 'showsPrec':
--
-- > 
-- > infixr 5 :^:
-- > data Tree a =  Leaf a  |  Tree a :^: Tree a
-- >
-- > instance (Show a) => Show (Tree a) where
-- >   showsPrec d (Leaf m) = showParen (d > app_prec) $
-- >        showString "Leaf " . showsPrec (app_prec+1) m
-- >     where app_prec = 10
-- > 
-- >   showsPrec d (u :^: v) = showParen (d > up_prec) $
-- >        showsPrec (up_prec+1) u .
-- >        showString " :^: "      .
-- >        showsPrec (up_prec+1) v
-- >     where up_prec = 5
--
class ShowHO (f :: ki -> *) where
  showHO      :: forall k . f k -> String
  showsPrecHO :: forall k . Int -> f k -> ShowS
  {-# MINIMAL showHO | showsPrecHO #-}

  showHO fx          = showsPrecHO 0 fx ""
  showsPrecHO _ fx s = showHO fx ++ s

instance Show a => ShowHO (Const a) where
  showsPrecHO d (Const a) = showParen (d > app_prec) $
      showString "Const " . showsPrec (app_prec + 1) a
    where app_prec = 10

instance (ShowHO f , ShowHO g) => ShowHO (f :*: g) where
  showsPrecHO d (x :*: y) = showParen (d > app_prec) $
                            showsPrecHO (app_prec+1) x
                          . showString " :*: "
                          . showsPrecHO (app_prec+1) y
    where app_prec = 10

instance (ShowHO f , ShowHO g) => ShowHO (Sum f g) where
  showsPrecHO d (InL fx) = showParen (d > app_prec) $
      showString "InL " . showsPrecHO (app_prec + 1) fx
    where app_prec = 10
  showsPrecHO d (InR gx) = showParen (d > app_prec) $
      showString "InR " . showsPrecHO (app_prec + 1) gx
    where app_prec = 10

-- |Existential type wrapper. This comesin particularly
-- handy when we want to add mrsop terms to
-- some container. See "Generics.MRSOP.Holes.Unify" for example.
data Exists (f :: k -> *) :: * where
  Exists :: f x -> Exists f

-- |Maps over 'Exists'
exMap :: (forall x . f x -> g x) -> Exists f -> Exists g
exMap f (Exists x) = Exists (f x)

-- |Maps a monadic actino over 'Exists'
exMapM :: (Monad m) => (forall x . f x -> m (g x)) -> Exists f -> m (Exists g)
exMapM f (Exists x) = Exists <$> f x

-- |eliminates an 'Exists'
exElim :: (forall x . f x -> a) -> Exists f -> a
exElim f (Exists x) = f x

instance ShowHO x => Show (Exists x) where
  show (Exists x) = showHO x

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

didn't need ListPrf; but ElemPrf is paramount.

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
