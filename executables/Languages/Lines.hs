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
import Generics.MRSOP.HDiff.Renderer
import Generics.MRSOP.HDiff.Digest

import Debug.Trace

-----------------------
-- * Parser

-- |We must have a dedicated type 'Line' to make sure
-- we duplicate lines. If we use just @Stmt [String]@ 
-- the content of the lines will be seen as an opaque type.
-- Opaque values are NOT shared by design.
data Stmt = Stmt [Line]

data Line = Line String

-- |Custom Opaque type
data WKon = WString 

-- |And their singletons.
--
--  Note we need instances of Eq1, Show1 and DigestibleHO
data W :: WKon -> * where
  W_String  :: String  -> W WString

instance EqHO W where
  eqHO (W_String s)  (W_String ss) = s == ss

instance DigestibleHO W where
  digestHO (W_String s)  = hashStr s

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
     return (Stmt $ map Line $ lines program)

