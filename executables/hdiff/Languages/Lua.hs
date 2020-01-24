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

instance Deep LuaFam LuaPrim Block
instance Deep LuaFam LuaPrim (Maybe Block)
instance Deep LuaFam LuaPrim [Stat]
instance Deep LuaFam LuaPrim Stat
instance Deep LuaFam LuaPrim [(Exp , Block)]
instance Deep LuaFam LuaPrim (Exp , Block)
instance Deep LuaFam LuaPrim Exp
instance Deep LuaFam LuaPrim (Maybe Exp)
instance Deep LuaFam LuaPrim [TableField]
instance Deep LuaFam LuaPrim TableField
instance Deep LuaFam LuaPrim Name
instance Deep LuaFam LuaPrim NumberType
instance Deep LuaFam LuaPrim FunBody
instance Deep LuaFam LuaPrim [Name]
instance Deep LuaFam LuaPrim PrefixExp
instance Deep LuaFam LuaPrim Var
instance Deep LuaFam LuaPrim FunCall
instance Deep LuaFam LuaPrim FunArg
instance Deep LuaFam LuaPrim FunName
instance Deep LuaFam LuaPrim (Maybe Name)
instance Deep LuaFam LuaPrim [Exp]
instance Deep LuaFam LuaPrim (Maybe [Exp])
instance Deep LuaFam LuaPrim Binop
instance Deep LuaFam LuaPrim Unop
instance Deep LuaFam LuaPrim [Var]

instance HasDecEq LuaFam where

type LuaFam = 
  [ Block
  , (Maybe Block)
  , [Stat]
  , Stat
  , [(Exp , Block)]
  , (Exp , Block)
  , Exp
  , (Maybe Exp)
  , [TableField]
  , TableField
  , Name
  , NumberType
  , FunBody
  , [Name]
  , PrefixExp
  , Var
  , FunCall
  , FunArg
  , FunName
  , (Maybe Name)
  , [Exp]
  , (Maybe [Exp])
  , Binop
  , Unop
  , [Var]
  ]


parseFile :: String -> ExceptT String IO Block
parseFile file = do
  res <- lift $ Lua.parseFile file
  case res of
    Left e  -> throwError (show e) 
    Right r -> return r

dfromLua :: Block -> SFix LuaFam LuaPrim Block
dfromLua = dfrom
