{-# LANGUAGE PolyKinds  #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs      #-}
module Data.Exists where

data Exists (f :: k -> *) :: * where
  Exists :: f x -> Exists f

exMap :: (forall x . f x -> g x) -> Exists f -> Exists g
exMap f (Exists x) = Exists (f x)

exElim :: (forall x . f x -> a) -> Exists f -> a
exElim f (Exists x) = f x

