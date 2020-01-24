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

type JavaFam =
  [ Java.CompilationUnit
  , (Maybe Java.PackageDecl)
  , [Java.ImportDecl]
  , [Java.TypeDecl]
  , Java.PackageDecl
  , Java.Name
  , [Java.Ident]
  , Java.Ident
  , Java.ImportDecl
  , Java.TypeDecl
  , Java.ClassDecl
  , Java.InterfaceDecl
  , [Java.Modifier]
  , [Java.TypeParam]
  , (Maybe Java.RefType)
  , Java.ClassBody
  , Java.EnumBody
  , Java.Modifier
  , Java.Annotation
  , [(Java.Ident, Java.ElementValue)]
  , Java.ElementValue
  , (Java.Ident, Java.ElementValue)
  , Java.VarInit
  , Java.ArrayInit
  , Java.Literal
  , (Maybe Java.Type)
  , [Java.TypeArgument]
  , Java.TypeDeclSpecifier
  , (Maybe Java.ClassBody)
  , Java.Type
  , [Java.Exp]
  , Java.FieldAccess
  , Java.MethodInvocation
  , Java.ArrayIndex
  , Java.Op
  , Java.Lhs
  , Java.AssignOp
  , Java.LambdaParams
  , Java.LambdaExpression
  , Java.PrimType
  , Java.ClassType
  , [(Java.Ident, [Java.TypeArgument])]
  , (Java.Ident, [Java.TypeArgument])
  , Java.TypeArgument
  , (Maybe Java.WildcardBound)
  , Java.WildcardBound
  , Java.Diamond
  , Java.Argument
  , [Java.Decl]
  , Java.Decl
  , Java.MemberDecl
  , Java.Block
  , [Java.VarDecl]
  , [Java.FormalParam]
  , [Java.ExceptionType]
  , (Maybe Java.Exp)
  , Java.MethodBody
  , Java.ConstructorBody
  , Java.VarDecl
  , Java.VarDeclId
  , (Maybe Java.VarInit)
  , Java.TypeParam
  , Java.FormalParam
  , Java.ExceptionType
  , (Maybe Java.Block)
  , [Java.BlockStmt]
  , Java.BlockStmt
  , Java.Stmt
  , (Maybe Java.ForInit)
  , (Maybe [Java.Exp])
  , [Java.SwitchBlock]
  , (Maybe Java.Ident)
  , [Java.Catch]
  , Java.ForInit
  , Java.SwitchBlock
  , Java.SwitchLabel
  , Java.Catch
  , (Maybe Java.ExplConstrInv)
  , Java.ExplConstrInv
  , Java.InterfaceKind
  , Java.InterfaceBody
  , [Java.MemberDecl]
  , [Java.VarInit]
  , [Java.EnumConstant]
  , Java.EnumConstant
  ]



instance Deep JavaFam JavaPrim Java.CompilationUnit
instance Deep JavaFam JavaPrim (Maybe Java.PackageDecl)
instance Deep JavaFam JavaPrim [Java.ImportDecl]
instance Deep JavaFam JavaPrim [Java.TypeDecl]
instance Deep JavaFam JavaPrim Java.PackageDecl
instance Deep JavaFam JavaPrim Java.Name
instance Deep JavaFam JavaPrim [Java.Ident]
instance Deep JavaFam JavaPrim Java.Ident
instance Deep JavaFam JavaPrim Java.ImportDecl
instance Deep JavaFam JavaPrim Java.TypeDecl
instance Deep JavaFam JavaPrim Java.ClassDecl
instance Deep JavaFam JavaPrim Java.InterfaceDecl
instance Deep JavaFam JavaPrim [Java.Modifier]
instance Deep JavaFam JavaPrim [Java.TypeParam]
instance Deep JavaFam JavaPrim (Maybe Java.RefType)
instance Deep JavaFam JavaPrim Java.ClassBody
instance Deep JavaFam JavaPrim Java.EnumBody
instance Deep JavaFam JavaPrim Java.Modifier
instance Deep JavaFam JavaPrim Java.Annotation
instance Deep JavaFam JavaPrim [(Java.Ident, Java.ElementValue)]
instance Deep JavaFam JavaPrim Java.ElementValue
instance Deep JavaFam JavaPrim (Java.Ident, Java.ElementValue)
instance Deep JavaFam JavaPrim Java.VarInit
instance Deep JavaFam JavaPrim Java.ArrayInit
instance Deep JavaFam JavaPrim Java.Literal
instance Deep JavaFam JavaPrim (Maybe Java.Type)
instance Deep JavaFam JavaPrim [Java.TypeArgument]
instance Deep JavaFam JavaPrim Java.TypeDeclSpecifier
instance Deep JavaFam JavaPrim (Maybe Java.ClassBody)
instance Deep JavaFam JavaPrim Java.Type
instance Deep JavaFam JavaPrim [Java.Exp]
instance Deep JavaFam JavaPrim Java.FieldAccess
instance Deep JavaFam JavaPrim Java.MethodInvocation
instance Deep JavaFam JavaPrim Java.ArrayIndex
instance Deep JavaFam JavaPrim Java.Op
instance Deep JavaFam JavaPrim Java.Lhs
instance Deep JavaFam JavaPrim Java.AssignOp
instance Deep JavaFam JavaPrim Java.LambdaParams
instance Deep JavaFam JavaPrim Java.LambdaExpression
instance Deep JavaFam JavaPrim Java.PrimType
instance Deep JavaFam JavaPrim Java.ClassType
instance Deep JavaFam JavaPrim [(Java.Ident, [Java.TypeArgument])]
instance Deep JavaFam JavaPrim (Java.Ident, [Java.TypeArgument])
instance Deep JavaFam JavaPrim Java.TypeArgument
instance Deep JavaFam JavaPrim (Maybe Java.WildcardBound)
instance Deep JavaFam JavaPrim Java.WildcardBound
instance Deep JavaFam JavaPrim Java.Diamond
instance Deep JavaFam JavaPrim Java.Argument
instance Deep JavaFam JavaPrim [Java.Decl]
instance Deep JavaFam JavaPrim Java.Decl
instance Deep JavaFam JavaPrim Java.MemberDecl
instance Deep JavaFam JavaPrim Java.Block
instance Deep JavaFam JavaPrim [Java.VarDecl]
instance Deep JavaFam JavaPrim [Java.FormalParam]
instance Deep JavaFam JavaPrim [Java.ExceptionType]
instance Deep JavaFam JavaPrim (Maybe Java.Exp)
instance Deep JavaFam JavaPrim Java.MethodBody
instance Deep JavaFam JavaPrim Java.ConstructorBody
instance Deep JavaFam JavaPrim Java.VarDecl
instance Deep JavaFam JavaPrim Java.VarDeclId
instance Deep JavaFam JavaPrim (Maybe Java.VarInit)
instance Deep JavaFam JavaPrim Java.TypeParam
instance Deep JavaFam JavaPrim Java.FormalParam
instance Deep JavaFam JavaPrim Java.ExceptionType
instance Deep JavaFam JavaPrim (Maybe Java.Block)
instance Deep JavaFam JavaPrim [Java.BlockStmt]
instance Deep JavaFam JavaPrim Java.BlockStmt
instance Deep JavaFam JavaPrim Java.Stmt
instance Deep JavaFam JavaPrim (Maybe Java.ForInit)
instance Deep JavaFam JavaPrim (Maybe [Java.Exp])
instance Deep JavaFam JavaPrim [Java.SwitchBlock]
instance Deep JavaFam JavaPrim (Maybe Java.Ident)
instance Deep JavaFam JavaPrim [Java.Catch]
instance Deep JavaFam JavaPrim Java.ForInit
instance Deep JavaFam JavaPrim Java.SwitchBlock
instance Deep JavaFam JavaPrim Java.SwitchLabel
instance Deep JavaFam JavaPrim Java.Catch
instance Deep JavaFam JavaPrim (Maybe Java.ExplConstrInv)
instance Deep JavaFam JavaPrim Java.ExplConstrInv
instance Deep JavaFam JavaPrim Java.InterfaceKind
instance Deep JavaFam JavaPrim Java.InterfaceBody
instance Deep JavaFam JavaPrim [Java.MemberDecl]
instance Deep JavaFam JavaPrim [Java.VarInit]
instance Deep JavaFam JavaPrim [Java.EnumConstant]
instance Deep JavaFam JavaPrim Java.EnumConstant

instance HasDecEq JavaFam where

parseFile :: String -> ExceptT String IO Java.CompilationUnit
parseFile file = do
  res <- lift $ readFile file
  case Java.parser Java.compilationUnit res of
    Left e  -> throwError (show e) 
    Right r -> return r

dfromJava :: Java.CompilationUnit
          -> SFix JavaFam JavaPrim Java.CompilationUnit
dfromJava = dfrom
