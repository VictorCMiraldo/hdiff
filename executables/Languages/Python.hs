{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE StandaloneDeriving    #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeSynonymInstances  #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE CPP                   #-}

module Languages.Python where


import           Data.Type.Equality
import           Data.Proxy
import           Data.Functor.Const
import           Data.Functor.Sum
import           Data.Text.Prettyprint.Doc hiding (braces,parens,semi)
import qualified Data.Text.Prettyprint.Doc as PP  (braces,parens,semi) 
import           Data.Text.Prettyprint.Doc.Render.Text
import qualified Data.Text as T

import System.Exit
import System.IO

import Generics.MRSOP.TH
import Generics.MRSOP.Base
import Generics.MRSOP.Util
import Generics.MRSOP.Opaque

import Generics.MRSOP.HDiff.Digest
import Generics.MRSOP.HDiff.Renderer

import Language.Python.Common.AST
import Language.Python.Common.SrcLocation
import Language.Python.Version3.Parser

{-
data PyKon = PyString | PyBool
data PySingl (kon :: PyKon) :: * where
  SPyString       :: String -> PySingl PyString
  SPyBool         :: Bool   -> PySingl PyBool
  SPyInt          :: Int    -> PySingl PyInt
  SPyInteger      :: Integer-> PySingl PyInteger
  SPyDouble       :: Double -> PySingl PyDouble
  SPyChar         :: Char -> PySingl PyChar
-}
{-

instance RendererHO PySingl where
  renderHO (SPyString str) = pretty str
  renderHO (SPyBool   b)   = pretty b
  renderHO (SPyInt    b)   = pretty b

instance DigestibleHO PySingl where
  digestHO (SPyString str) = hashStr str
  digestHO (SPyBool   b)   = hashStr (show b)
  digestHO (SPyInt    b)   = hashStr (show b)

-}

deriveFamilyWith ''Singl [t| Module SrcSpan |]
