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

import Generics.Simplistic
import Generics.Simplistic.Util

data SZip ty w f where
  Z_L1    ::                SZip ty w f -> SZip ty w (f :+: g)
  Z_R1    ::                SZip ty w g -> SZip ty w (f :+: g)
  Z_PairL :: SZip ty w f -> SRep    w g -> SZip ty w (f :*: g)
  Z_PairR :: SRep   w f  -> SZip ty w g -> SZip ty w (f :*: g)
  Z_M1    :: SMeta i t   -> SZip ty w f -> SZip ty w (M1 i t f)
  Z_KH     :: a :~: ty   -> SZip ty w (K1 i a)
deriving instance (forall a. Show (w a)) => Show (SZip h w f)
deriving instance (forall a. Eq (w a)) => Eq   (SZip h w f)

zipperMap :: (forall x . h x -> g x)
          -> SZip ty h f -> SZip ty g f
zipperMap f (Z_L1 x)      = Z_L1 (zipperMap f x)
zipperMap f (Z_R1 x)      = Z_R1 (zipperMap f x)
zipperMap f (Z_M1 c x)    = Z_M1 c (zipperMap f x)
zipperMap f (Z_PairL x y) = Z_PairL (zipperMap f x) (repMap f y)
zipperMap f (Z_PairR x y) = Z_PairR (repMap f x) (zipperMap f y)
zipperMap _ (Z_KH x)      = Z_KH x

inr1 :: (x :*: y) t -> (Sum z x :*: y) t
inr1 (x :*: y) = (InR x :*: y)

zipperRepZip :: SZip ty h f -> SRep w f -> Maybe (SRep ((Sum ((:~:) ty) h) :*: w) f)
zipperRepZip (Z_KH Refl)   (S_K1 y)   = return $ S_K1 (InL Refl :*: y)
zipperRepZip (Z_L1 x)      (S_L1 y)   = S_L1 <$> zipperRepZip x y
zipperRepZip (Z_R1 x)      (S_R1 y)   = S_R1 <$> zipperRepZip x y
zipperRepZip (Z_M1 c x)    (S_M1 _ y) = S_M1 c <$> zipperRepZip x y
zipperRepZip (Z_PairL x y) (y1 :**: y2)
  = (:**:) <$> zipperRepZip x y1 <*> (repMap inr1 <$> zipSRep y y2)
zipperRepZip (Z_PairR x y) (y1 :**: y2)
  = (:**:) <$> (repMap inr1 <$> zipSRep x y1) <*> zipperRepZip y y2
zipperRepZip _ _ = Nothing

zipSZip :: SZip ty h f -> SZip ty w f -> Maybe (SZip ty (h :*: w) f)
zipSZip (Z_KH _)    (Z_KH Refl) = Just (Z_KH Refl)
zipSZip (Z_L1 x)      (Z_L1 y)   = Z_L1 <$> zipSZip x y
zipSZip (Z_R1 x)      (Z_R1 y)   = Z_R1 <$> zipSZip x y
zipSZip (Z_M1 c x)    (Z_M1 _ y) = Z_M1 c <$> zipSZip x y
zipSZip (Z_PairL x y) (Z_PairL w z)
  = Z_PairL <$> zipSZip x w <*> zipSRep y z
zipSZip (Z_PairR x y) (Z_PairR w z)
  = Z_PairR <$> zipSRep x w <*> zipSZip y z
zipSZip _ _ = Nothing


data Zipper c f g t where
  Zipper :: c
         => { zipper :: SZip t f (Rep t)
            , sel    :: g t
            }
         -> Zipper c f g t

plug :: SZip ty phi f -> phi ty -> SRep phi f
plug (Z_KH Refl)   k = S_K1 k
plug (Z_L1 x)      k = S_L1 $ plug x k
plug (Z_R1 x)      k = S_R1 $ plug x k
plug (Z_M1 c x)    k = S_M1 c $ plug x k
plug (Z_PairL x y) k = (plug x k) :**: y
plug (Z_PairR x y) k = x :**: (plug y k)

type Zipper' kappa fam ann phi t
  = Zipper (CompoundCnstr kappa fam t)
           (HolesAnn kappa fam ann phi)
           (HolesAnn kappa fam ann phi) t

zippers :: forall kappa fam ann phi t
         . (forall a . (Elem t fam) => phi a -> Maybe (a :~: t)) 
        -> HolesAnn kappa fam ann phi t
        -> [Zipper' kappa fam ann phi t] 
zippers _   (Prim' _ _) = []
zippers _   (Hole' _ _) = []
zippers aux (Roll' _ r) = map (uncurry Zipper) (go r)
  where
    pf :: Proxy fam
    pf = Proxy

    pa :: HolesAnn kappa fam ann phi a -> Proxy a
    pa _ = Proxy

    go :: SRep (HolesAnn kappa fam ann phi) f
       -> [(SZip t (HolesAnn kappa fam ann phi) f
          , HolesAnn kappa fam ann phi t)]
    go S_U1       = []
    go (S_L1 x)   = first Z_L1 <$> go x
    go (S_R1 x)   = first Z_R1 <$> go x
    go (S_M1 c x) = first (Z_M1 c) <$> go x
    go (x :**: y) = (first (flip Z_PairL y) <$> go x)
                 ++ (first (Z_PairR x)      <$> go y)
    go (S_K1 x@(Roll' _ _)) =
      case sameTy pf (Proxy :: Proxy t) (pa x) of
        Just Refl -> return $ (Z_KH Refl , x)
        Nothing   -> []
    go (S_K1 x@(Hole' _ xh)) = 
      case aux xh of
        Just Refl -> return $ (Z_KH Refl , x)
        Nothing   -> []
    go _ = []
      
      
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
