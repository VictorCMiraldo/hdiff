{-# LANGUAGE QuantifiedConstraints #-}
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
{-# OPTIONS_GHC -Wno-orphans #-}
module Generics.Simplistic.Zipper where

import Data.Proxy
import Data.Type.Equality
import GHC.Generics
import Data.Functor.Sum
import Control.Monad.State

import qualified Data.Set as S

import Generics.Simplistic
import Generics.Simplistic.Util

import Debug.Trace

data SZip h w f where
  Z_U1    ::                              SZip h w U1
  Z_L1    ::                SZip h w f -> SZip h w (f :+: g)
  Z_R1    ::                SZip h w g -> SZip h w (f :+: g)
  Z_PairL :: SZip h w f  -> SRep   w g -> SZip h w (f :*: g)
  Z_PairR :: SRep   w f  -> SZip h w g -> SZip h w (f :*: g)
  Z_M1    :: SMeta i t   -> SZip h w f -> SZip h w (M1 i t f)
  Z_KH    :: h a         -> SZip h w (K1 i a)
  Z_KT    :: w a         -> SZip h w (K1 i a)
deriving instance (forall a. Show (w a) , forall a . Show (h a)) => Show (SZip h w f)


zipperMap :: (forall x . h x -> g x)
          -> SZip h w f -> SZip g w f
zipperMap _ Z_U1     = Z_U1          
zipperMap f (Z_L1 x) = Z_L1 (zipperMap f x)
zipperMap f (Z_R1 x) = Z_R1 (zipperMap f x)
zipperMap f (Z_M1 c x) = Z_M1 c (zipperMap f x)
zipperMap f (Z_PairL x y) = Z_PairL (zipperMap f x) y
zipperMap f (Z_PairR x y) = Z_PairR x (zipperMap f y)
zipperMap f (Z_KH x) = Z_KH (f x)
zipperMap _ (Z_KT x) = Z_KT x

{-
zipperFrom :: forall phi h psi t
            . (forall x . phi x -> Maybe (h x))
           -> (forall x . phi x -> psi x)
           -> SRep phi t
           -> Maybe (SZip h psi t)
zipperFrom f g r = case runState (go r) False of
                     (Just res , True) -> Just res
                     _                 -> Nothing
  where
    go :: SRep phi g -> State Bool (Maybe (SZip h psi g))
    go  S_U1      = return (Just Z_U1)
    go (S_L1 x)   = fmap Z_L1     <$> go x
    go (S_R1 x)   = fmap Z_R1     <$> go x
    go (S_M1 c x) = fmap (Z_M1 c) <$> go x
    go (S_K1 x) = case f x of
        Nothing -> return (Just $ Z_KT $ g x)
        Just x' -> do
          rdy <- get
          if rdy then return Nothing -- we already found sthing
                 else put True >> return (Just $ Z_KH x')
    go (x :**: y) = do
      x' <- go x
      case x' of
        Nothing -> fmap (Z_PairR (repMap g x)) <$> go y
        Just rx -> do
          y' <- go y
          case y' of
            Just _  -> return Nothing -- two were found
            Nothing -> return (Just $ Z_PairL rx (repMap g y))
-}

zipperFrom :: forall phi h psi t
            . (forall x . phi x -> Maybe (h x))
           -> (forall x . phi x -> psi x)
           -> SRep phi t
           -> Maybe (SZip h psi t)
zipperFrom f g r = case runStateT (go r) False of
                     Just (res , True) -> Just res
                     _                 -> Nothing
  where
    go :: SRep phi g -> StateT Bool Maybe (SZip h psi g)
    go  S_U1      = return Z_U1
    go (S_L1 x)   = Z_L1   <$> go x
    go (S_R1 x)   = Z_R1   <$> go x
    go (S_M1 c x) = Z_M1 c <$> go x
    go (S_K1 x) = case f x of
        Nothing -> return (Z_KT $ g x)
        Just x' -> do
          found <- get
          if found then lift Nothing -- we already found sthing
                   else (put True) >> return (Z_KH x')
    go (x :**: y) = do
      x' <- go x
      xfound <- get
      y' <- go y
      if xfound
      then return (Z_PairL x' (repMap g y))
      else return (Z_PairR (repMap g x) y')


-------------------
-- Prtty

zipConstructorName :: SZip h w f -> String
zipConstructorName (Z_M1 x@SM_C _)
  = getConstructorName x
zipConstructorName (Z_M1 _ x)
  = zipConstructorName x
zipConstructorName (Z_L1 x)
  = zipConstructorName x
zipConstructorName (Z_R1 x)
  = zipConstructorName x
zipConstructorName _
  = error "Please; use GHC's deriving mechanism. This keeps M1's at the top of the Rep"

zipLeavesList :: SZip h w f -> [Exists (Sum h w)]
zipLeavesList Z_U1 = []
zipLeavesList (Z_M1 _ x) = zipLeavesList x
zipLeavesList (Z_L1 x) = zipLeavesList x
zipLeavesList (Z_R1 x) = zipLeavesList x
zipLeavesList (Z_KH x) = [Exists (InL x)]
zipLeavesList (Z_KT x) = [Exists (InR x)]
zipLeavesList (Z_PairL x y) = zipLeavesList x ++ map (exMap InR) (repLeavesList y)
zipLeavesList (Z_PairR x y) = map (exMap InR) (repLeavesList x) ++ zipLeavesList y

