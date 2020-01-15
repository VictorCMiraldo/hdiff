{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE GADTs                 #-}
{-# OPTIONS_GHC -Wno-orphans       #-}
module Data.HDiff.Show where

import           Data.Functor.Sum
import           Data.Functor.Const
import           Data.Text.Prettyprint.Doc
import           Data.Text.Prettyprint.Doc.Render.Terminal
import qualified Data.Text as T

import Generics.Simplistic
import Generics.Simplistic.Util
import Generics.Simplistic.Pretty

import qualified Data.HDiff.Base    as D
import qualified Data.HDiff.Merge   as D
import qualified Data.HDiff.MetaVar as D


myRender :: Doc AnsiStyle -> String
myRender =
  let maxWidth = 80
      pgdim = LayoutOptions (AvailablePerLine maxWidth 1)
      lyout = layoutSmart pgdim
   in T.unpack . renderStrict . lyout

-- |Given a label and a doc, @spliced l d = "[" ++ l ++ "|" ++ d ++ "|]"@
spliced :: Doc ann -> Doc ann
spliced d = pretty "#" <> d

metavarPretty :: (Doc AnsiStyle -> Doc AnsiStyle)
              -> D.MetaVar ix -> Doc AnsiStyle
metavarPretty sty (Const i) 
  = sty $ spliced (pretty i)

instance Show (Holes prim D.MetaVar x) where
  show = myRender . holesPretty (metavarPretty id)

-- when using emacs, the output of the repl is in red;
-- hence, life is easier when we show a different color isntead.
-- btw, emacs only interprets dull colors.
myred , mygreen , mydullred , mydullgreen :: AnsiStyle
myred       = colorDull Yellow
mygreen     = colorDull Green
mydullred   = colorDull Yellow
mydullgreen = colorDull Green

chgPretty :: D.Chg prim x
          -> Doc AnsiStyle
chgPretty (D.Chg d i)
  = group $ sep [group (chgD d) , group (chgI i) ]
 where
   chgD = chg (annotate myred)   (pretty "{-") (pretty "-}")
   chgI = chg (annotate mygreen) (pretty "{+") (pretty "+}")
   
   chg f o c h
     = (f o) <+> holesPretty (metavarPretty f) h <+> (f c)

confPretty :: D.Conflict prim x
           -> Doc AnsiStyle
confPretty (D.FailedContr vars)
  = group (pretty "{!!" <+> sep (map (pretty . exElim D.metavarGet) vars) <+> pretty "!!}")
confPretty (D.Conflict _ c d)
  = vcat [ pretty "{!! >>>>>>>"
         , chgPretty c
         , pretty "==========="
         , chgPretty d
         , pretty "<<<<<<< !!}"]

instance Show (D.Chg prim x) where
  show = myRender . chgPretty

instance Show (D.Patch prim x) where
  show = myRender . holesPretty chgPretty

instance Show (D.PatchC prim x) where
  show = myRender . holesPretty go
    where
      go x = case x of
               InL c -> confPretty c
               InR c -> chgPretty c
