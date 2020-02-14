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
import Generics.Simplistic

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

instance Deep CljFam CljPrims Expr
instance Deep CljFam CljPrims FormTy
instance Deep CljFam CljPrims CollTy
instance Deep CljFam CljPrims SepExprList
instance Deep CljFam CljPrims Term
instance Deep CljFam CljPrims Sep
instance Deep CljFam CljPrims Tag

instance HasDecEq CljFam where

type CljFam = 
  [ Expr
  , FormTy
  , CollTy
  , SepExprList
  , Term
  , Sep
  , Tag
  ]

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
