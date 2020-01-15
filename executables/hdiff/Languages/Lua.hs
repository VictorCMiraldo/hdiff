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
module Languages.Lua where

import Language.Lua.Syntax
import qualified Language.Lua.Parser as Lua

import Data.Text (Text)
import Data.Text.Encoding (encodeUtf8)
import Data.Type.Equality

import           Data.Text.Prettyprint.Doc hiding (braces,parens,semi)
import qualified Data.Text as T

import Control.Monad.Except

import Generics.Simplistic
import Generics.Simplistic.Digest

import Data.HDiff.Diff

type LuaPrim = '[ Text , Bool ]
instance Deep LuaPrim Block
instance Deep LuaPrim (Maybe Block)
instance Deep LuaPrim [Stat]
instance Deep LuaPrim Stat
instance Deep LuaPrim [(Exp , Block)]
instance Deep LuaPrim (Exp , Block)
instance Deep LuaPrim Exp
instance Deep LuaPrim (Maybe Exp)
instance Deep LuaPrim [TableField]
instance Deep LuaPrim TableField
instance Deep LuaPrim Name
instance Deep LuaPrim NumberType
instance Deep LuaPrim FunBody
instance Deep LuaPrim [Name]
instance Deep LuaPrim PrefixExp
instance Deep LuaPrim Var
instance Deep LuaPrim FunCall
instance Deep LuaPrim FunArg
instance Deep LuaPrim FunName
instance Deep LuaPrim (Maybe Name)
instance Deep LuaPrim [Exp]
instance Deep LuaPrim (Maybe [Exp])
instance Deep LuaPrim Binop
instance Deep LuaPrim Unop
instance Deep LuaPrim [Var]

parseFile :: String -> ExceptT String IO Block
parseFile file = do
  res <- lift $ Lua.parseFile file
  case res of
    Left e  -> throwError (show e) 
    Right r -> return r

twofiles :: ExceptT String IO (Block , Block)
twofiles = (,) <$> parseFile "examples/Lua/parser/binsearch.lua"
               <*> parseFile "examples/Lua/parser/binsearch2.lua"

dfromLua :: Block -> SFix LuaPrim Block
dfromLua = dfrom
