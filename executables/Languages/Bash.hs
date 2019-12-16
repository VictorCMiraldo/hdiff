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
module Languages.Bash where

import qualified Language.Bash.Syntax as Bash
import qualified Language.Bash.Parse as Bash
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

deriveFamilyWith ''Singl [t| Bash.List |]

parseFile :: String -> ExceptT String IO Bash.List
parseFile file = do
  res <- lift $ readFile file
  case Bash.parse file res of
    Left e  -> throwError (show e) 
    Right r -> return r
