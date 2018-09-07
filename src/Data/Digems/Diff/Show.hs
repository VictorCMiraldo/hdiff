{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE PolyKinds  #-}
{-# LANGUAGE DataKinds  #-}
{-# LANGUAGE GADTs      #-}
module Data.Digems.Diff.Show where

import           System.IO
import           Data.Proxy
import           Data.Functor.Const
import           Data.Functor.Sum
import           Data.Text.Prettyprint.Doc
import           Data.Text.Prettyprint.Doc.Render.Terminal
import qualified Data.Text.Prettyprint.Doc.Render.Text as Text
import qualified Data.Text as T

import Generics.MRSOP.Base hiding (Infix)
import Generics.MRSOP.Util
import Generics.MRSOP.TH
import Generics.MRSOP.Digems.Renderer
import Generics.MRSOP.Digems.Digest
import Generics.MRSOP.Digems.Treefix hiding (parens)

import qualified Data.Digems.Diff.Patch as D
-- import qualified Data.Digems.Diff.Merge as D

-- |Given a label and a doc, @spliced l d = "[" ++ l ++ "|" ++ d ++ "|]"@
spliced :: Doc ann -> Doc ann
spliced d = brackets (surround d (pretty "| ") (pretty " |")) 

metavarPretty :: (Doc AnsiStyle -> Doc AnsiStyle) -> D.MetaVar ix -> Doc AnsiStyle
metavarPretty sty (D.ForceI (Const i)) 
  = sty $ spliced (pretty i)

{-
-- |Shows a conflict in a pretty fashion  
conflictPretty :: (HasDatatypeInfo ki fam codes)
               => (forall k . ki k -> Doc AnsiStyle)
               -> Sum D.MetaVar (D.Conflict ki codes) at -> Doc AnsiStyle
conflictPretty renderK (InL v)
  = metavarPretty v
conflictPretty renderK (InR (D.Conflict l r))
  = let dl = utxPretty (Proxy :: Proxy fam) metavarPretty renderK l
        dr = utxPretty (Proxy :: Proxy fam) metavarPretty renderK r
     in annotate (color Red)
      $ spliced (annotate bold $ pretty "C")
                (hsep [dl , pretty "<|>" , dr ])
-}

-- |Pretty prints a patch on the terminal
displayRawPatch :: (HasDatatypeInfo ki fam codes , IsNat v , Renderer1 ki)
                => Handle
                -> D.Patch ki codes v
                -> IO ()
displayRawPatch hdl patch 
  = doubleColumn hdl 75
      (utxPretty (Proxy :: Proxy fam) id prettyChangeDel patch)
      (utxPretty (Proxy :: Proxy fam) id prettyChangeIns patch)

prettyChangeDel :: (HasDatatypeInfo ki fam codes , Renderer1 ki)
                => D.Change ki codes at
                -> Doc AnsiStyle
prettyChangeDel (D.SameMetaVar i)
  = annotate (color Blue) $ spliced (pretty i)
prettyChangeDel (D.Match del ins)
  = utxPretty (Proxy :: Proxy fam)
              (annotate (color Red))
              (metavarPretty (annotate $ colorDull Red))
              del

prettyChangeIns :: (HasDatatypeInfo ki fam codes , Renderer1 ki)
                => D.Change ki codes at
                -> Doc AnsiStyle
prettyChangeIns (D.SameMetaVar i)
  = annotate (color Blue) $ spliced (pretty i)
prettyChangeIns (D.Match del ins)
  = utxPretty (Proxy :: Proxy fam)
              (annotate (color Green))
              (metavarPretty (annotate $ colorDull Green))
              ins

-- |Displays two docs in a double column fashion
--
--  This is a hacky function. We need to render both the colored
--  and the non-colored versions to calculate
--  the width spacing correctly (see @complete@ in the where clause)
--
doubleColumn :: Handle -> Int -> Doc AnsiStyle -> Doc AnsiStyle -> IO ()
doubleColumn hdl maxWidth da db
  = let pgdim = LayoutOptions (AvailablePerLine maxWidth 1)
        lyout = layoutSmart pgdim
        -- colored versions
        ta    = T.lines . renderStrict $ lyout da
        tb    = T.lines . renderStrict $ lyout db
        -- non colored versions
        sta   = T.lines . Text.renderStrict $ lyout da
        width = 1 + maximum (0 : map T.length sta)
        stb   = T.lines . Text.renderStrict $ lyout db
        compA = if length ta >= length tb
                then 0
                else length tb - length ta
        compB = if length tb >= length ta
                then 0
                else length ta - length tb
        fta   = (zip ta sta) ++ replicate compA ((id &&& id) $ T.replicate width $ T.singleton ' ')
        ftb   = (zip tb stb) ++ replicate compB ((id &&& id) $ T.empty)
     in mapM_ (\(la , lb) -> hPutStrLn hdl . T.unpack . T.concat
                           $ [ complete width la
                             , T.pack " -|+ "
                             , fst lb
                             ])
              (zip fta ftb)
  where
    complete n (color , nocolor)
      = T.concat [color , T.replicate (n - T.length nocolor) $ T.singleton ' ']
