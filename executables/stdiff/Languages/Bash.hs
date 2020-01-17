{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE StandaloneDeriving    #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeSynonymInstances  #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE CPP                   #-}
{-# OPTIONS_GHC -Wno-orphans                            #-}
{-# OPTIONS_GHC -Wno-missing-signatures                 #-}
{-# OPTIONS_GHC -Wno-missing-pattern-synonym-signatures #-}
module Languages.Bash where

#ifdef WITH_BASH

import qualified Language.Bash.Syntax as Bash
import qualified Language.Bash.Parse as Bash
import Control.Monad.Except

import           Data.Text.Prettyprint.Doc (pretty)

import Generics.MRSOP.Base
import Generics.MRSOP.Opaque
import Generics.MRSOP.TH

deriveFamilyWith ''Singl [t| Bash.List |]

type FamStmt = Bash.List

parseFile :: String -> ExceptT String IO Bash.List
parseFile file = do
  res <- lift $ readFile file
  case Bash.parse file res of
    Left e  -> throwError (show e) 
    Right r -> return r

#endif
