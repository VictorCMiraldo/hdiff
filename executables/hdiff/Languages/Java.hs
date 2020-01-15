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

import Generics.Simplistic

type JavaPrim = '[ Int , Integer , Double , Bool, Char , String ]

instance Deep JavaPrim Java.CompilationUnit
instance Deep JavaPrim (Maybe Java.PackageDecl)
instance Deep JavaPrim [Java.ImportDecl]
instance Deep JavaPrim [Java.TypeDecl]
instance Deep JavaPrim Java.PackageDecl
instance Deep JavaPrim Java.Name
instance Deep JavaPrim [Java.Ident]
instance Deep JavaPrim Java.Ident
instance Deep JavaPrim Java.ImportDecl
instance Deep JavaPrim Java.TypeDecl
instance Deep JavaPrim Java.ClassDecl
instance Deep JavaPrim Java.InterfaceDecl
instance Deep JavaPrim [Java.Modifier]
instance Deep JavaPrim [Java.TypeParam]
instance Deep JavaPrim (Maybe Java.RefType)
instance Deep JavaPrim Java.ClassBody
instance Deep JavaPrim Java.EnumBody
instance Deep JavaPrim Java.Modifier
instance Deep JavaPrim Java.Annotation
instance Deep JavaPrim [(Java.Ident, Java.ElementValue)]
instance Deep JavaPrim Java.ElementValue
instance Deep JavaPrim (Java.Ident, Java.ElementValue)
instance Deep JavaPrim Java.VarInit
instance Deep JavaPrim Java.ArrayInit
instance Deep JavaPrim Java.Literal
instance Deep JavaPrim (Maybe Java.Type)
instance Deep JavaPrim [Java.TypeArgument]
instance Deep JavaPrim Java.TypeDeclSpecifier
instance Deep JavaPrim (Maybe Java.ClassBody)
instance Deep JavaPrim Java.Type
instance Deep JavaPrim [Java.Exp]
instance Deep JavaPrim Java.FieldAccess
instance Deep JavaPrim Java.MethodInvocation
instance Deep JavaPrim Java.ArrayIndex
instance Deep JavaPrim Java.Op
instance Deep JavaPrim Java.Lhs
instance Deep JavaPrim Java.AssignOp
instance Deep JavaPrim Java.LambdaParams
instance Deep JavaPrim Java.LambdaExpression
instance Deep JavaPrim Java.PrimType
instance Deep JavaPrim Java.ClassType
instance Deep JavaPrim [(Java.Ident, [Java.TypeArgument])]
instance Deep JavaPrim (Java.Ident, [Java.TypeArgument])
instance Deep JavaPrim Java.TypeArgument
instance Deep JavaPrim (Maybe Java.WildcardBound)
instance Deep JavaPrim Java.WildcardBound
instance Deep JavaPrim Java.Diamond
instance Deep JavaPrim Java.Argument
instance Deep JavaPrim [Java.Decl]
instance Deep JavaPrim Java.Decl
instance Deep JavaPrim Java.MemberDecl
instance Deep JavaPrim Java.Block
instance Deep JavaPrim [Java.VarDecl]
instance Deep JavaPrim [Java.FormalParam]
instance Deep JavaPrim [Java.ExceptionType]
instance Deep JavaPrim (Maybe Java.Exp)
instance Deep JavaPrim Java.MethodBody
instance Deep JavaPrim Java.ConstructorBody
instance Deep JavaPrim Java.VarDecl
instance Deep JavaPrim Java.VarDeclId
instance Deep JavaPrim (Maybe Java.VarInit)
instance Deep JavaPrim Java.TypeParam
instance Deep JavaPrim Java.FormalParam
instance Deep JavaPrim Java.ExceptionType
instance Deep JavaPrim (Maybe Java.Block)
instance Deep JavaPrim [Java.BlockStmt]
instance Deep JavaPrim Java.BlockStmt
instance Deep JavaPrim Java.Stmt
instance Deep JavaPrim (Maybe Java.ForInit)
instance Deep JavaPrim (Maybe [Java.Exp])
instance Deep JavaPrim [Java.SwitchBlock]
instance Deep JavaPrim (Maybe Java.Ident)
instance Deep JavaPrim [Java.Catch]
instance Deep JavaPrim Java.ForInit
instance Deep JavaPrim Java.SwitchBlock
instance Deep JavaPrim Java.SwitchLabel
instance Deep JavaPrim Java.Catch
instance Deep JavaPrim (Maybe Java.ExplConstrInv)
instance Deep JavaPrim Java.ExplConstrInv
instance Deep JavaPrim Java.InterfaceKind
instance Deep JavaPrim Java.InterfaceBody
instance Deep JavaPrim [Java.MemberDecl]
instance Deep JavaPrim [Java.VarInit]
instance Deep JavaPrim [Java.EnumConstant]
instance Deep JavaPrim Java.EnumConstant

parseFile :: String -> ExceptT String IO Java.CompilationUnit
parseFile file = do
  res <- lift $ readFile file
  case Java.parser Java.compilationUnit res of
    Left e  -> throwError (show e) 
    Right r -> return r

dfromJava :: Java.CompilationUnit
          -> SFix JavaPrim Java.CompilationUnit
dfromJava = dfrom
