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

import Generics.MRSOP.HDiff.Digest
import Generics.MRSOP.HDiff.Renderer

import Language.Python.Common.AST
import Language.Python.Common.SrcLocation
import Language.Python.Version3.Parser

data PyKon = PyString | PyBool
data PySingl (kon :: PyKon) :: * where
  SPyString :: String -> PySingl PyString
  SPyBool   :: Bool   -> PySingl PyBool

instance RendererHO PySingl where
  renderHO (SPyString str) = pretty str
  renderHO (SPyBool   b)   = pretty b

instance DigestibleHO PySingl where
  digestHO (SPyString str) = hashStr str
  digestHO (SPyBool   b)   = hashStr (show b)

deriving instance Show (PySingl k)
deriving instance Eq   (PySingl k)

instance TestEquality PySingl where
  testEquality (SPyBool _) (SPyBool _) = Just Refl
  testEquality (SPyString _) (SPyString _) = Just Refl
  testEquality _ _ = Nothing

deriveFamilyWith ''PySingl [t| Module SrcSpan |]
