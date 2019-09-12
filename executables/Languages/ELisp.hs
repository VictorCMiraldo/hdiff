{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Languages.ELisp where

import System.IO
import Control.Monad

import           Data.Proxy
import           Data.Functor.Const
import           Data.Functor.Sum
import           Data.Type.Equality
import           Data.Text.Prettyprint.Doc (pretty)
import           Data.Text.Prettyprint.Doc.Render.Text
import qualified Data.Text as T

import Generics.MRSOP.Base hiding (Infix)
import Generics.MRSOP.Util
import Generics.MRSOP.TH
import Generics.MRSOP.HDiff.Renderer
import Generics.MRSOP.HDiff.Digest

import System.Exit

import           Language.ELisp
import qualified Language.ELisp.Parser as P

-- |Custom Opaque type
data WKon = WInteger | WString | WDouble | WChar

-- |And their singletons.
--
--  Note we need instances of EqHO, ShowHO and DigestibleHO
data W :: WKon -> * where
  W_Integer :: Integer -> W WInteger
  W_Char    :: Char    -> W WChar
  W_String  :: String  -> W WString
  W_Double  :: Double  -> W WDouble

instance EqHO W where
  eqHO (W_Integer i) (W_Integer j) = i == j
  eqHO (W_String s)  (W_String ss) = s == ss
  eqHO (W_Double b)  (W_Double c)  = b == c
  eqHO (W_Char b)    (W_Char c)    = b == c

instance DigestibleHO W where
  digestHO (W_Integer i) = hashStr (show i)
  digestHO (W_String s)  = hashStr s
  digestHO (W_Char s)    = hashStr [s]
  digestHO (W_Double b)  = hashStr (show b)

instance ShowHO W where
  showHO (W_Integer i) = show i
  showHO (W_String s)  = s
  showHO (W_Char s)    = show s
  showHO (W_Double b)  = show b

instance RendererHO W where
  renderHO (W_Integer i) = pretty i
  renderHO (W_String s)  = pretty s
  renderHO (W_Char c)    = pretty c
  renderHO (W_Double b)  = pretty b

instance TestEquality W where
  testEquality (W_Integer _) (W_Integer _) = Just Refl
  testEquality (W_String _)  (W_String _)  = Just Refl
  testEquality (W_Double _)  (W_Double _)  = Just Refl
  testEquality (W_Char _)    (W_Char _)    = Just Refl
  testEquality _             _             = Nothing


-- Now we derive the 'Family' instance
-- using 'W' for the constants.
deriveFamilyWith ''W [t| [ESExp] |]

type Block = [ESExp]

parseFile :: String -> IO Block
parseFile file =
  do program  <- P.parseFile file
     case program of
       Left e  -> hPutStrLn stderr (show e) >> exitWith (ExitFailure 10)
       Right r -> return r

