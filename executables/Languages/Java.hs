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
module Languages.Java where

import qualified Language.Java.Syntax as Java
import qualified Language.Java.Parser as Java
import Control.Monad.Except

import           Data.Text.Prettyprint.Doc (pretty)

import Generics.MRSOP.Base
import Generics.MRSOP.Opaque
import Generics.MRSOP.TH
import Generics.MRSOP.HDiff.Renderer
import Generics.MRSOP.HDiff.Digest

instance RendererHO Singl where
  renderHO = pretty . showHO

instance DigestibleHO Singl where
  digestHO (SInt      a) = hashStr $ "I" ++ show a
  digestHO (SInteger  a) = hashStr $ "i" ++ show a
  digestHO (SFloat    a) = hashStr $ "F" ++ show a
  digestHO (SDouble   a) = hashStr $ "D" ++ show a
  digestHO (SBool     a) = hashStr $ "B" ++ show a
  digestHO (SChar     a) = hashStr $ "C" ++ show a
  digestHO (SString   a) = hashStr $ "S" ++ show a

deriveFamilyWith ''Singl [t| Java.CompilationUnit |]

parseFile :: String -> ExceptT String IO Java.CompilationUnit
parseFile file = do
  res <- lift $ readFile file
  case Java.parser Java.compilationUnit res of
    Left e  -> throwError (show e) 
    Right r -> return r
