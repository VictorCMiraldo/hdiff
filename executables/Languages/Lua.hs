{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
module Languages.Lua where

import Language.Lua.Syntax
import qualified Language.Lua.Parser as Lua

import Data.Text (Text)
import Data.Text.Encoding (encodeUtf8)
import Data.Type.Equality

import           Data.Proxy
import           Data.Functor.Const
import           Data.Functor.Sum
import           Data.Text.Prettyprint.Doc hiding (braces,parens,semi)
import qualified Data.Text.Prettyprint.Doc as PP  (braces,parens,semi) 
import           Data.Text.Prettyprint.Doc.Render.Text
import qualified Data.Text as T

import Generics.MRSOP.TH
import Generics.MRSOP.Base
import Generics.MRSOP.Util

import Generics.MRSOP.Digems.Digest
import Generics.MRSOP.Digems.Renderer

data LuaKon = LuaText | LuaBool
data LuaSingl (kon :: LuaKon) :: * where
  SLuaText :: Text -> LuaSingl LuaText
  SLuaBool :: Bool -> LuaSingl LuaBool

instance Renderer1 LuaSingl where
  render1 (SLuaText t) = pretty (T.unpack t)
  render1 (SLuaBool b) = pretty b

instance Digestible Text where
  digest = hash . encodeUtf8

instance Digestible1 LuaSingl where
  digest1 (SLuaText text) = digest text
  digest1 (SLuaBool bool) = hashStr (show bool)

deriving instance Show (LuaSingl k)
deriving instance Eq (LuaSingl k)
instance Show1 LuaSingl where show1 = show
instance Eq1 LuaSingl where eq1 = (==)

instance TestEquality LuaSingl where
  testEquality (SLuaText _) (SLuaText _) = Just Refl
  testEquality (SLuaBool _) (SLuaBool _) = Just Refl
  testEquality _ _ = Nothing

deriveFamilyWith ''LuaSingl [t| Block |]

parseFile :: String -> IO Block
parseFile file =
  do program  <- Lua.parseFile file
     case program of
       Left e  -> print e >> fail "parse error"
       Right r -> return r

type W = LuaSingl
type Stmt = Block
type FamStmt = FamBlock
type CodesStmt = CodesBlock
