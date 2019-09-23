{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE GADTs                 #-}
module Data.Exists where

data Exists (f :: k -> *) :: * where
  Exists :: f x -> Exists f

exMap :: (forall x . f x -> g x) -> Exists f -> Exists g
exMap f (Exists x) = Exists (f x)

exMapM :: (Monad m) => (forall x . f x -> m (g x)) -> Exists f -> m (Exists g)
exMapM f (Exists x) = Exists <$> f x

exElim :: (forall x . f x -> a) -> Exists f -> a
exElim f (Exists x) = f x

instance (forall i . Show (x i)) => Show (Exists x) where
  show (Exists x) = show x

