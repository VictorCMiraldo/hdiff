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
import Control.Monad.Except

import Generics.Simplistic

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

dfromLua :: Block -> SFix LuaPrim Block
dfromLua = dfrom
