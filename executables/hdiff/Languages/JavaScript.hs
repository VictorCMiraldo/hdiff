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
module Languages.JavaScript where

import Language.JavaScript.Parser.AST
import Language.JavaScript.Parser

import System.IO

import Data.Text (Text)
import Control.Monad.Except

import GHC.Generics
import Generics.Simplistic

type JSPrim = '[ String , Int ]

deriving instance Generic JSAST
deriving instance Generic JSAnnot
deriving instance Generic JSStatement
deriving instance Generic JSExpression
deriving instance Generic JSSemi
deriving instance Generic JSIdent
deriving instance Generic (JSCommaList JSExpression)
deriving instance Generic JSBinOp
deriving instance Generic (JSCommaList JSIdent)
deriving instance Generic JSBlock
deriving instance Generic JSAssignOp
deriving instance Generic JSTryFinally
deriving instance Generic TokenPosn
deriving instance Generic CommentAnnotation
deriving instance Generic JSUnaryOp
deriving instance Generic JSArrowParameterList
deriving instance Generic JSObjectPropertyList
deriving instance Generic JSVarInitializer
deriving instance Generic JSArrayElement
deriving instance Generic (JSCommaList JSObjectProperty)
deriving instance Generic JSObjectProperty
deriving instance Generic JSAccessor
deriving instance Generic JSPropertyName
deriving instance Generic JSSwitchParts
deriving instance Generic JSTryCatch
deriving instance Generic JSModuleItem
deriving instance Generic JSImportDeclaration
deriving instance Generic JSExportDeclaration
deriving instance Generic JSImportClause
deriving instance Generic JSFromClause
deriving instance Generic JSImportNameSpace
deriving instance Generic JSImportsNamed
deriving instance Generic (JSCommaList JSImportSpecifier)
deriving instance Generic JSImportSpecifier
deriving instance Generic JSExportClause
deriving instance Generic (JSCommaList JSExportSpecifier)
deriving instance Generic JSExportSpecifier

instance Deep JSPrim JSAST
instance Deep JSPrim [JSStatement]
instance Deep JSPrim JSAnnot
instance Deep JSPrim [JSModuleItem]
instance Deep JSPrim JSStatement
instance Deep JSPrim JSExpression
instance Deep JSPrim JSSemi
instance Deep JSPrim JSIdent
instance Deep JSPrim (JSCommaList JSExpression)
instance Deep JSPrim JSBinOp
instance Deep JSPrim (JSCommaList JSIdent)
instance Deep JSPrim JSBlock
instance Deep JSPrim JSAssignOp
instance Deep JSPrim (Maybe JSExpression)
instance Deep JSPrim [JSSwitchParts]
instance Deep JSPrim [JSTryCatch]
instance Deep JSPrim JSTryFinally
instance Deep JSPrim TokenPosn
instance Deep JSPrim [CommentAnnotation]
instance Deep JSPrim CommentAnnotation
instance Deep JSPrim [JSArrayElement]
instance Deep JSPrim JSUnaryOp
instance Deep JSPrim JSArrowParameterList
instance Deep JSPrim JSObjectPropertyList
instance Deep JSPrim JSVarInitializer
instance Deep JSPrim JSArrayElement
instance Deep JSPrim (JSCommaList JSObjectProperty)
instance Deep JSPrim JSObjectProperty
instance Deep JSPrim JSAccessor
instance Deep JSPrim JSPropertyName
instance Deep JSPrim [JSExpression]
instance Deep JSPrim JSSwitchParts
instance Deep JSPrim JSTryCatch
instance Deep JSPrim JSModuleItem
instance Deep JSPrim JSImportDeclaration
instance Deep JSPrim JSExportDeclaration
instance Deep JSPrim JSImportClause
instance Deep JSPrim JSFromClause
instance Deep JSPrim JSImportNameSpace
instance Deep JSPrim JSImportsNamed
instance Deep JSPrim (JSCommaList JSImportSpecifier)
instance Deep JSPrim JSImportSpecifier
instance Deep JSPrim JSExportClause
instance Deep JSPrim (JSCommaList JSExportSpecifier)
instance Deep JSPrim JSExportSpecifier

parseFile :: String -> ExceptT String IO JSAST
parseFile file = do
  res <- lift $
    -- TODO: do I care for utf8?
    do h <- openFile file ReadMode
       hSetEncoding h utf8
       hGetContents h
  case parseModule res file of
    Left e  -> throwError (show e) 
    Right r -> return r

dfromJS :: JSAST -> SFix JSPrim JSAST
dfromJS = dfrom
