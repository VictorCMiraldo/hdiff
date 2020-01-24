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
import qualified Data.HDiff.MetaVar as D
import qualified Data.HDiff.Merge.Align as D

-- import qualified Data.HDiff.Merge   as D

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
              -> D.MetaVar fam prim ix -> Doc AnsiStyle
metavarPretty sty v
  = sty $ spliced (pretty (D.metavarGet v))

{-
instance {-# OVERLAPING #-} (ShowHO phi)
    => Show (Holes prim phi x) where
  show = myRender . holesPretty (pretty . showHO)
-}

instance {-# OVERLAPPABLE #-} (ShowHO ann , ShowHO phi)
    => Show (HolesAnn fam prim ann phi x) where
  show = myRender . holesAnnPretty (pretty . showHO) addAnn
    where
      addAnn ann d = sep [pretty "<" , pretty (showHO ann) , pretty "|" , d , pretty ">"]

instance ShowHO (D.HolesMV fam prim) where
  showHO = myRender . holesPretty (metavarPretty id)



instance Show (D.HolesMV fam prim x) where
  show = myRender . holesPretty (metavarPretty id)

-- when using emacs, the output of the repl is in red;
-- hence, life is easier when we show a different color isntead.
-- btw, emacs only interprets dull colors.
myred , mygreen , mydullred , mydullgreen :: AnsiStyle
myred       = colorDull Yellow
mygreen     = colorDull Green
mydullred   = colorDull Yellow
mydullgreen = colorDull Green

chgPretty :: D.Chg fam prim x
          -> Doc AnsiStyle
chgPretty (D.Chg d i)
  = group $ braces $ sep [group (chgD d) , group (chgI i) ]
 where
   chgD = chg (annotate myred)   (pretty "{-") (pretty "-}")
   chgI = chg (annotate mygreen) (pretty "{+") (pretty "+}")
   
   chg f o c h
     = (f o) <+> holesPretty (metavarPretty f) h <+> (f c)

instance Show (D.Chg fam prim x) where
  show = myRender . chgPretty

instance Show (D.Patch fam prim x) where
  show = myRender . holesPretty chgPretty

asrD :: Doc AnsiStyle -> Doc AnsiStyle
asrD d = annotate myred $ group
       $ sep [pretty "[-" , d , pretty "-]"]

asrI :: Doc AnsiStyle -> Doc AnsiStyle
asrI d = annotate mygreen $ group
       $ sep [pretty "[+" , d , pretty "+]"]

alignedPretty :: D.Aligned fam prim x -> Doc AnsiStyle
alignedPretty (D.Del x)
  = zipperPretty sfixPretty alignedPretty asrD x
alignedPretty (D.Ins x)
  = zipperPretty sfixPretty alignedPretty asrI x
alignedPretty (D.Spn x)
  = repPretty alignedPretty x
alignedPretty (D.Mod c)
  = chgPretty c

alignedPretty' :: D.Aligned fam prim x -> Doc AnsiStyle
alignedPretty' a = group $ sep [pretty "{-#" , alignedPretty a , pretty "#-}"]

instance Show (D.Aligned fam prim x) where
  show = myRender . alignedPretty'

instance Show (Holes fam prim (D.Aligned fam prim) x) where
  show = myRender . holesPretty alignedPretty'


{-

instance Show (D.PatchC fam prim x) where
  show = myRender . holesPretty go
    where
      go x = case x of
               InL c -> confPretty c
               InR c -> chgPretty c

confPretty :: D.Conflict fam prim x
           -> Doc AnsiStyle
confPretty (D.FailedContr vars)
  = group (pretty "{!!" <+> sep (map (pretty . exElim D.metavarGet) vars) <+> pretty "!!}")
confPretty (D.Conflict lbl c d)
  = vcat [ pretty "{!! >>>>>>>" <+> pretty lbl <+> pretty "<<<<<<<"
         , alignedPretty c
         , pretty "==========="
         , alignedPretty d
         , pretty ">>>>>>>" <+> pretty lbl <+> pretty "<<<<<<< !!}"]
-}
