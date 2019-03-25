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
{-# LANGUAGE CPP #-}
module Languages.Lua where

#ifdef ENABLE_LUA_SUPPORT

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

import System.Exit
import System.IO

import Generics.MRSOP.TH
import Generics.MRSOP.Base
import Generics.MRSOP.Util

import Generics.MRSOP.Digems.Digest
import Generics.MRSOP.Digems.Renderer

data LuaKon = LuaText | LuaBool
data LuaSingl (kon :: LuaKon) :: * where
  SLuaText :: Text -> LuaSingl LuaText
  SLuaBool :: Bool -> LuaSingl LuaBool

instance RendererHO LuaSingl where
  renderHO (SLuaText t) = pretty (T.unpack t)
  renderHO (SLuaBool b) = pretty b

instance Digestible Text where
  digest = hash . encodeUtf8

instance DigestibleHO LuaSingl where
  digestHO (SLuaText text) = digest text
  digestHO (SLuaBool bool) = hashStr (show bool)

deriving instance Show (LuaSingl k)
deriving instance Eq (LuaSingl k)
instance ShowHO LuaSingl where showHO = show
instance EqHO LuaSingl where eqHO = (==)

instance TestEquality LuaSingl where
  testEquality (SLuaText _) (SLuaText _) = Just Refl
  testEquality (SLuaBool _) (SLuaBool _) = Just Refl
  testEquality _ _ = Nothing

deriveFamilyWith ''LuaSingl [t| Block |]

parseFile :: String -> IO Block
parseFile file = do
  res <- Lua.parseFile file
  case res of
    Left e  -> hPutStrLn stderr (show e) >> exitWith (ExitFailure 10)
    Right r -> return r

type W = LuaSingl
type Stmt = Block
type FamStmt = FamBlock
type CodesStmt = CodesBlock

#endif
