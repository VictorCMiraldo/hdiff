{-# LANGUAGE DeriveGeneric #-}
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
module Languages.Clojure.Interface where

import Languages.Clojure.Syntax
import qualified Languages.Clojure.Parser as Clj

import Data.Text (Text)
import Control.Monad.Except

import GHC.Generics
import Generics.Simplistic.Deep
import Generics.Simplistic.Deep.TH

type CljPrims = '[ Text ]

-- import Generics.Simplistic.TH
-- Got types with: getTypesInvolved [ ''Text ] [t| Expr |]


deriving instance Generic Expr
deriving instance Generic FormTy
deriving instance Generic CollTy
deriving instance Generic SepExprList
deriving instance Generic Term
deriving instance Generic Sep
deriving instance Generic Tag

type CljFam = 
  [ Expr
  , FormTy
  , CollTy
  , SepExprList
  , Term
  , Sep
  , Tag
  ]

deriveDeepFor ''CljPrims ''CljFam

-- -- The TH above generates:
-- instance Deep CljPrims CljFam Expr
-- instance Deep CljPrims CljFam FormTy
-- instance Deep CljPrims CljFam CollTy
-- instance Deep CljPrims CljFam SepExprList
-- instance Deep CljPrims CljFam Term
-- instance Deep CljPrims CljFam Sep
-- instance Deep CljPrims CljFam Tag



dfromClj :: Expr -> SFix CljPrims CljFam Expr
dfromClj = dfrom

dtoClj   :: SFix CljPrims CljFam Expr -> Expr
dtoClj   = dto

parseFile :: String -> ExceptT String IO Expr
parseFile file = do
  res <- lift $ readFile file
  case Clj.parse Clj.parseTop file res of
    Left e  -> throwError (show e) 
    Right r -> return r
