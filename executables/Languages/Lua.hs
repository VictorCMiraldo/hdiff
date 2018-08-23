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

import Generics.MRSOP.Digems.Renderer
import Generics.MRSOP.Digems.Digest

data LuaKon = LuaText | LuaBool
data W (kon :: LuaKon) :: * where
  SLuaText :: Text -> W LuaText
  SLuaBool :: Bool -> W LuaBool

instance Digestible Text where
  digest = hash . encodeUtf8

instance Digestible1 W where
  digest1 (SLuaText text) = digest text
  digest1 (SLuaBool bool) = hashStr (show bool)

deriving instance Show (W k)
deriving instance Eq (W k)
instance Show1 W where show1 = show
instance Eq1 W where eq1 = (==)

instance TestEquality W where
  testEquality (SLuaText _) (SLuaText _) = Just Refl
  testEquality (SLuaBool _) (SLuaBool _) = Just Refl
  testEquality _ _ = Nothing

deriveFamilyWith ''W [t| Block |]

parseFile :: String -> IO Block
parseFile file =
  do program  <- Lua.parseFile file
     case program of
       Left e  -> print e >> fail "parse error"
       Right r -> return r

-- Renderer instance

instance Renderer W FamBlock CodesBlock where
  renderK _ (SLuaText s) = pretty (T.unpack s)
  renderK _ (SLuaBool b) = pretty b

  renderI pf idx (Tag c NP0)
    = pretty (constructorName (constrInfoFor pf idx c))
  renderI pf idx (Tag c p)
    = let ci = constrInfoFor pf idx c
       in PP.parens $ vsep
          ( pretty (constructorName ci)
          : elimNP (elimNA (renderK pf) getConst) p
          )
    

type Stmt = Block
type FamStmt = FamBlock
type CodesStmt = CodesBlock
