{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Languages.Clojure.AST where

import Data.Type.Equality

import           Data.Text.Prettyprint.Doc (pretty)

import Data.Text
import Data.Text.Encoding (encodeUtf8)
import Generics.MRSOP.TH
import Generics.MRSOP.Base
import Generics.MRSOP.Digems.Digest
import Generics.MRSOP.Digems.Renderer


data SepExprList =
   Nil 
 | Cons Expr !Sep SepExprList 
 deriving (Show)

data Sep = Space | Comma | NewLine | EmptySep deriving (Show, Eq)

data Expr = Special !FormTy Expr 
          | Dispatch Expr 
          | Collection !CollTy SepExprList 
          | Term Term 
          | Comment !Text 
          | Seq Expr Expr 
          | Empty 
          deriving (Show)

data FormTy = Quote | SQuote | UnQuote | DeRef | Meta deriving (Show, Eq)

data CollTy = Vec | Set | Parens deriving (Show, Eq)

data Term = TaggedString !Tag !Text 
  deriving (Show)

data Tag = String | Var  deriving (Show, Eq)



data ConflictResult a = NoConflict | ConflictAt a
  deriving (Show, Eq)

data CljKon = CljText
data CljSingl (kon :: CljKon) :: * where
  SCljText :: Text -> CljSingl 'CljText

instance RendererHO CljSingl where
  renderHO (SCljText t) = pretty (unpack t)

instance Digestible Text where
  digest = hash . encodeUtf8

instance DigestibleHO CljSingl where
  digestHO (SCljText text) = digest text
  

deriving instance Show (CljSingl k)
deriving instance Eq (CljSingl k)
instance ShowHO CljSingl where showHO = show
instance EqHO CljSingl where eqHO = (==)

instance TestEquality CljSingl where
  testEquality (SCljText _) (SCljText _) = Just Refl


deriveFamilyWith ''CljSingl [t| Expr |]
