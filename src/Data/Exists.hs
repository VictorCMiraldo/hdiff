{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE GADTs                 #-}
module Data.Exists where

import Generics.MRSOP.Base (ShowHO(..))

data Exists (f :: k -> *) :: * where
  Exists :: f x -> Exists f

exMap :: (forall x . f x -> g x) -> Exists f -> Exists g
exMap f (Exists x) = Exists (f x)

exMapM :: (Monad m) => (forall x . f x -> m (g x)) -> Exists f -> m (Exists g)
exMapM f (Exists x) = Exists <$> f x

exElim :: (forall x . f x -> a) -> Exists f -> a
exElim f (Exists x) = f x

instance ShowHO x => Show (Exists x) where
  show (Exists x) = showHO x

