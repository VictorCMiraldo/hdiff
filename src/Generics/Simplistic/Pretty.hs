{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE RankNTypes           #-}
{-# OPTIONS_GHC -Wno-orphans      #-}
module Generics.Simplistic.Pretty where

import           Data.Text.Prettyprint.Doc    (Doc)
import qualified Data.Text.Prettyprint.Doc as PP

import Generics.Simplistic
import Generics.Simplistic.Zipper
import Generics.Simplistic.Util

repPretty :: (forall x . phi x -> Doc ann)
          -> SRep phi f -> Doc ann
repPretty f x =
  let c  = repConstructorName x
      xs = repLeavesList x
      parens = if length xs == 0 then id else PP.parens
   in PP.group $ parens
               $ PP.nest 1
               $ PP.sep
               $ (PP.pretty c:)
               $ map (exElim f) xs

holesAnnPretty
  :: (forall x . h   x -> Doc ann)
  -> (forall x . phi x -> Doc ann -> Doc ann) 
  -> HolesAnn prim phi h a
  -> Doc ann
holesAnnPretty f g (Hole' ann x) = g ann (f x)
holesAnnPretty _ g (Prim' ann x) = g ann (PP.pretty $ show x)
holesAnnPretty f g (Roll' ann x)
  = g ann (repPretty (holesAnnPretty f g) x)

holesPretty
  :: (forall x . h x -> Doc ann) 
  -> Holes prim h a
  -> Doc ann
holesPretty f = holesAnnPretty f (const id)

sfixAnnPretty
  :: (forall x . phi x -> Doc ann -> Doc ann) 
  -> SFixAnn prim phi a
  -> Doc ann
sfixAnnPretty f = holesAnnPretty (error "imp") f

sfixPretty :: SFix prim a -> Doc ann
sfixPretty = sfixAnnPretty  (const id)

instance Show (SFix prim a) where
  show = show . sfixPretty 

-----------------------------
-- Zipper stuff

szipPretty :: (forall x . phi x -> Doc ann)
             -> SZip h phi f -> Doc ann
szipPretty f x =
  let c  = zipConstructorName x
      xs = zipLeavesList x
      parens = if length xs == 0 then id else PP.parens
   in PP.group $ parens
               $ PP.nest 1
               $ PP.sep
               $ (PP.pretty c:)
               $ map (maybe doHole (exElim f)) xs
  where
    doHole :: Doc ann
    doHole = PP.pretty "[#]"

zipperPretty :: (forall x . f x -> Doc ann)
             -> (forall x . g x -> Doc ann)
             -> Zipper f g t -> Doc ann
zipperPretty pf pg (Zipper z x)
  = PP.group $ PP.sep [szipPretty pf z
                     , PP.group (PP.sep [PP.pretty "# =" , pg x])]

