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
{-# OPTIONS_GHC -Wno-orphans                            #-}
{-# OPTIONS_GHC -Wno-missing-signatures                 #-}
{-# OPTIONS_GHC -Wno-missing-pattern-synonym-signatures #-}
module Languages.Clojure.Interface where

import Languages.Clojure.Syntax
import qualified Languages.Clojure.Parser as Clj

import Data.Text (Text)
import Data.Text.Encoding (encodeUtf8)
import Data.Type.Equality

import           Data.Text.Prettyprint.Doc hiding (braces,parens,semi)
import qualified Data.Text as T

import Control.Monad.Except

import Generics.MRSOP.TH
import Generics.MRSOP.Base

import Generics.MRSOP.HDiff.Digest
import Generics.MRSOP.HDiff.Renderer

data CljKon = CljText | CljBool
data CljSingl (kon :: CljKon) :: * where
  SCljText :: Text -> CljSingl 'CljText

instance RendererHO CljSingl where
  renderHO (SCljText t) = pretty (T.unpack t)

instance Digestible Text where
  digest = hash . encodeUtf8

instance DigestibleHO CljSingl where
  digestHO (SCljText text) = hash (encodeUtf8 text)

deriving instance Show (CljSingl k)
deriving instance Eq (CljSingl k)

instance EqHO CljSingl where
  eqHO = (==)

instance ShowHO CljSingl where
  showHO = show

instance TestEquality CljSingl where
  testEquality (SCljText _) (SCljText _) = Just Refl
  testEquality _ _ = Nothing

deriveFamilyWith ''CljSingl [t| Expr |]

parseFile :: String -> ExceptT String IO Expr
parseFile file = do
  res <- lift $ readFile file
  case Clj.parse Clj.parseTop file res of
    Left e  -> throwError (show e) 
    Right r -> return r

type FamStmt = FamExpr
