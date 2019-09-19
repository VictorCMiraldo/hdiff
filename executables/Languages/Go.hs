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


-- |
-- Module      : Language.Go
-- Copyright   : (c) 2011 Andrew Robbins
-- License     : GPLv3 (see COPYING)
-- 
-- x
module Languages.Go where

import Data.Type.Equality

import           Data.Text.Prettyprint.Doc hiding (braces,parens,semi)

import System.Exit
import System.IO

import Generics.MRSOP.TH
import Generics.MRSOP.Base
import Generics.MRSOP.Util

import Generics.MRSOP.HDiff.Digest
import Generics.MRSOP.HDiff.Renderer

import Languages.Go.Parser.Parser
import Languages.Go.Syntax.AST


data GoKon = GoString | GoBool | GoInt | GoInteger | GoFloat | GoChar
data GoSingl (kon :: GoKon) :: * where
  SGoString  :: String  -> GoSingl GoString
  SGoBool    :: Bool    -> GoSingl GoBool
  SGoInt     :: Int     -> GoSingl GoInt
  SGoInteger :: Integer -> GoSingl GoInteger
  SGoFloat   :: Float   -> GoSingl GoFloat
  SGoChar    :: Char    -> GoSingl GoChar

instance RendererHO GoSingl where
  renderHO (SGoString  t) = pretty t
  renderHO (SGoBool    b) = pretty b
  renderHO (SGoInt     b) = pretty b
  renderHO (SGoInteger b) = pretty b
  renderHO (SGoFloat   b) = pretty b
  renderHO (SGoChar    b) = pretty b
  

instance Digestible String where
  digest = hashStr

instance DigestibleHO GoSingl where
  digestHO (SGoString text)  = digest text
  digestHO (SGoBool bool)    = hashStr (show bool)
  digestHO (SGoInt  int)     = hashStr (show int)
  digestHO (SGoInteger  int) = hashStr (show int)
  digestHO (SGoFloat  int)   = hashStr (show int)
  digestHO (SGoChar  int)    = hashStr (show int)

deriving instance Show (GoSingl k)
deriving instance Eq (GoSingl k)

instance TestEquality GoSingl where
  testEquality (SGoString _) (SGoString _) = Just Refl
  testEquality (SGoBool _) (SGoBool _) = Just Refl
  testEquality (SGoInt _) (SGoInt _) = Just Refl
  testEquality (SGoInteger _) (SGoInteger _) = Just Refl
  testEquality (SGoFloat _) (SGoFloat _) = Just Refl
  testEquality (SGoChar _) (SGoChar _) = Just Refl
  testEquality _ _ = Nothing

deriveFamilyWith ''GoSingl [t| GoSource |]

parseFile :: String -> IO GoSource
parseFile file = do
  res <- readFile file
  case goParse file res of
    Left e  -> hPutStrLn stderr (show e) >> exitWith (ExitFailure 10)
    Right r -> return r

type W = GoSingl
type Stmt = GoSource
type FamStmt = FamGoSource
type CodesStmt = CodesGoSource
