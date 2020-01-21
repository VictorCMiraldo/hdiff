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
import Control.Arrow (first)

import qualified Data.Set as S

import Generics.Simplistic
import Generics.Simplistic.Util

import Unsafe.Coerce
import Debug.Trace

data SZip ty w f where
  Z_L1    ::                SZip ty w f -> SZip ty w (f :+: g)
  Z_R1    ::                SZip ty w g -> SZip ty w (f :+: g)
  Z_PairL :: SZip ty w f -> SRep    w g -> SZip ty w (f :*: g)
  Z_PairR :: SRep   w f  -> SZip ty w g -> SZip ty w (f :*: g)
  Z_M1    :: SMeta i t   -> SZip ty w f -> SZip ty w (M1 i t f)
  Z_KH     :: a :~: ty   -> SZip ty w (K1 i a)
deriving instance (forall a. Show (w a)) => Show (SZip h w f)

zipperMap :: (forall x . h x -> g x)
          -> SZip ty h f -> SZip ty g f
zipperMap f (Z_L1 x) = Z_L1 (zipperMap f x)
zipperMap f (Z_R1 x) = Z_R1 (zipperMap f x)
zipperMap f (Z_M1 c x) = Z_M1 c (zipperMap f x)
zipperMap f (Z_PairL x y) = Z_PairL (zipperMap f x) (repMap f y)
zipperMap f (Z_PairR x y) = Z_PairR (repMap f x) (zipperMap f y)
zipperMap f (Z_KH x) = Z_KH x

data Zipper f g t where
  Zipper :: { zipper :: SZip t f (Rep t)
            , plug   :: g t
            }
         -> Zipper f g t

type Zipper' prim ann phi
  = Zipper (HolesAnn prim ann phi) (HolesAnn prim ann phi)

zippers :: forall prim ann phi t
         . HolesAnn prim ann phi t
        -> [Zipper' prim ann phi t] 
zippers (Prim' _ _) = []
zippers (Hole' _ _) = []
zippers (Roll' _ r) = map (uncurry Zipper) (go r)
  where
    go :: SRep (HolesAnn prim ann phi) f
       -> [(SZip t (HolesAnn prim ann phi) f
          , HolesAnn prim ann phi t)]
    go S_U1       = []
    go (S_L1 x)   = first Z_L1 <$> go x
    go (S_R1 x)   = first Z_R1 <$> go x
    go (S_M1 c x) = first (Z_M1 c) <$> go x
    go (x :**: y) = (first (flip Z_PairL y) <$> go x)
                 ++ (first (Z_PairR x)      <$> go y)
    go (S_K1 x@(Roll' _ r')) =
      if repDatatypeName r == repDatatypeName r'
      then unsafeCoerce [(Z_KH Refl , unsafeCoerce x)]
      else []
    go (S_K1 _) = []

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

zipLeavesList :: SZip ty w f -> [Maybe (Exists w)]
zipLeavesList (Z_L1 x) = zipLeavesList x
zipLeavesList (Z_R1 x) = zipLeavesList x
zipLeavesList (Z_M1 _ x) = zipLeavesList x
zipLeavesList (Z_PairL l x) = zipLeavesList l ++ map Just (repLeavesList x)
zipLeavesList (Z_PairR x l) = map Just (repLeavesList x) ++ zipLeavesList l
zipLeavesList (Z_KH _)      = [Nothing]
