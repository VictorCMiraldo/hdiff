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

import Data.Text (Text)
import Data.Text.Encoding (encodeUtf8)
import Data.Type.Equality

import Generics.MRSOP.TH
import Generics.MRSOP.Base
import Generics.MRSOP.Util

import Generics.MRSOP.Digems.Digest

data LuaKon = LuaText
data LuaSingl (kon :: LuaKon) :: * where
  SLuaText :: Text -> LuaSingl LuaText

instance Digestible Text where
  digest = hash . encodeUtf8

instance Digestible1 LuaSingl where
  digest1 (SLuaText text) = digest text

deriving instance Show (LuaSingl k)
deriving instance Eq (LuaSingl k)
instance Show1 LuaSingl where show1 = show
instance Eq1 LuaSingl where eq1 = (==)

instance TestEquality LuaSingl where
  testEquality (SLuaText _) (SLuaText _) = Just Refl

deriveFamilyWith ''LuaSingl [t| Block |]
