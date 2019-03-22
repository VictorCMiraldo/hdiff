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
module Languages.Lines where

import System.IO
import           Data.Type.Equality
import           Data.Text.Prettyprint.Doc (pretty)
import           Data.Text.Prettyprint.Doc.Render.Text
import qualified Data.Text as T

import Generics.MRSOP.Base hiding (Infix)
import Generics.MRSOP.Util
import Generics.MRSOP.TH
import Generics.MRSOP.Digems.Renderer
import Generics.MRSOP.Digems.Digest

import Debug.Trace

-----------------------
-- * Parser

data Stmt = Stmt [String]

-- |Custom Opaque type
data WKon = WString 

-- |And their singletons.
--
--  Note we need instances of Eq1, Show1 and Digestible1
data W :: WKon -> * where
  W_String  :: String  -> W WString

instance EqHO W where
  eqHO (W_String s)  (W_String ss) = s == ss

instance Digestible1 W where
  digest1 (W_String s)  = hashStr s

instance ShowHO W where
  showHO (W_String s)  = s

-- Now we derive the 'Family' instance
-- using 'W' for the constants.
deriveFamilyWithTy [t| W |] [t| Stmt |]

instance RendererHO W where
  renderHO (W_String s)  = pretty s

instance TestEquality W where
  testEquality (W_String _)  (W_String _)  = Just Refl

parseFile :: String -> IO Stmt
parseFile file =
  do program  <- readFile file
     return (Stmt $ lines program)

