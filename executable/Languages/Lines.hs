{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE StandaloneDeriving    #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE TypeSynonymInstances  #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE DeriveDataTypeable    #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeApplications      #-}
{-# OPTIONS_GHC -Wno-missing-signatures                 #-}
{-# OPTIONS_GHC -Wno-missing-pattern-synonym-signatures #-}
module Languages.Lines where

import           Data.Type.Equality
import           Data.Text.Prettyprint.Doc (pretty)

import           Control.Monad.Except

import GHC.Generics
import Generics.Simplistic
import Generics.Simplistic.Deep
import Generics.Simplistic.Digest

-----------------------
-- * Parser

-- |We must have a dedicated type 'Line' to make sure
-- we duplicate lines. If we use just @Stmt [String]@
-- the content of the lines will be seen as an opaque type.
-- Opaque values are NOT shared by design.
data Stmt = Stmt [Line]
  deriving Generic

data Line = Line String
  deriving Generic

type LinesPrims = '[ String ]
type LinesFam   = '[Stmt , Line , [Line]]
instance Deep LinesPrims LinesFam Line
instance Deep LinesPrims LinesFam [Line]
instance Deep LinesPrims LinesFam Stmt

dfromLines :: Stmt -> SFix LinesPrims LinesFam Stmt
dfromLines = dfrom

dtoLines   :: SFix LinesPrims LinesFam Stmt -> Stmt
dtoLines   = dto

parseFile :: String -> ExceptT String IO Stmt
parseFile file =
  do program  <- lift $ readFile file
     return (Stmt $ map Line $ lines program)
