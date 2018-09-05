{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE PolyKinds  #-}
{-# LANGUAGE DataKinds  #-}
{-# LANGUAGE GADTs      #-}
module Data.Digems.Diff.Show where

import           System.IO
import           Data.Proxy
import           Data.Functor.Const
import           Data.Functor.Sum
import           Data.Text.Prettyprint.Doc hiding (Doc)
import           Data.Text.Prettyprint.Doc.Render.Text
import qualified Data.Text as T

import Generics.MRSOP.Base hiding (Infix)
import Generics.MRSOP.Util
import Generics.MRSOP.TH
import Generics.MRSOP.Digems.Renderer
import Generics.MRSOP.Digems.Digest
import Generics.MRSOP.Digems.Treefix hiding (parens)

import qualified Data.Digems.Diff.Patch as D
import qualified Data.Digems.Diff.Merge as D

-- |Given a label and a doc, @spliced l d = "[" ++ l ++ "|" ++ d ++ "|]"@
spliced :: String -> Doc -> Doc
spliced lbl d = brackets (pretty lbl <> surround d (pretty "| ") (pretty " |")) 

-- |Prints a metavariable
metavarPretty :: D.MetaVar ix -> Doc
metavarPretty (NA_I v) = spliced "I" (pretty $ getConst v)
metavarPretty (NA_K v) = spliced "K" (pretty $ getConst v)

-- |Shows a conflict in a pretty fashion  
conflictPretty :: (HasDatatypeInfo ki fam codes)
               => (forall k . ki k -> Doc)
               -> Sum D.MetaVar (D.Conflict ki codes) at -> Doc
conflictPretty renderK (InL v) = metavarPretty v
conflictPretty renderK (InR (D.Conflict l r))
  = let dl = utxPretty (Proxy :: Proxy fam) metavarPretty renderK l
        dr = utxPretty (Proxy :: Proxy fam) metavarPretty renderK r
     in spliced "C" (hsep [dl , pretty "<|>" , dr ])

-- |Pretty prints a patch on the terminal
displayRawPatch :: (HasDatatypeInfo ki fam codes , IsNat v)
                => Handle
                -> (forall i . x i  -> Doc)
                -> (forall k . ki k -> Doc)
                -> D.RawPatch x ki codes v
                -> IO ()
displayRawPatch hdl showX renderK patch
  = doubleColumn hdl 75
      (utxPretty (Proxy :: Proxy fam) showX renderK (D.ctxDel patch))
      (utxPretty (Proxy :: Proxy fam) showX renderK (D.ctxIns patch))

-- |displays two docs in a double column fashion
doubleColumn :: Handle -> Int -> Doc -> Doc -> IO ()
doubleColumn hdl width da db
  = let pgdim = LayoutOptions (AvailablePerLine width 1)
        lyout = layoutSmart pgdim
        ta    = T.lines . renderStrict $ lyout da
        tb    = T.lines . renderStrict $ lyout db
        compA = if length ta >= length tb
                then 0
                else length tb - length ta
        compB = if length tb >= length ta
                then 0
                else length ta - length tb
        fta   = ta ++ replicate compA (T.replicate width $ T.singleton ' ')
        ftb   = tb ++ replicate compB T.empty
     in mapM_ (\(la , lb) -> hPutStrLn hdl . T.unpack . T.concat
                           $ [ complete width la
                             , T.pack " -|+ "
                             , lb
                             ])
              (zip fta ftb)
  where
    complete n t = T.concat [t , T.replicate (n - T.length t) $ T.singleton ' ']
