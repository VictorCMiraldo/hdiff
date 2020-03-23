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

#ifdef REAL_LANGUAGES

import qualified Language.Java.Syntax as Java
import qualified Language.Java.Parser as Java
import Control.Monad.Except

import Generics.Simplistic
import Generics.Simplistic.Deep
import Generics.Simplistic.Deep.TH

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

deriveDeepFor ''JavaPrim ''JavaFam
-- 
-- instance Deep JavaPrim JavaFam Java.CompilationUnit
-- instance Deep JavaPrim JavaFam (Maybe Java.PackageDecl)
-- instance Deep JavaPrim JavaFam [Java.ImportDecl]
-- instance Deep JavaPrim JavaFam [Java.TypeDecl]
-- instance Deep JavaPrim JavaFam Java.PackageDecl
-- instance Deep JavaPrim JavaFam Java.Name
-- instance Deep JavaPrim JavaFam [Java.Ident]
-- instance Deep JavaPrim JavaFam Java.Ident
-- instance Deep JavaPrim JavaFam Java.ImportDecl
-- instance Deep JavaPrim JavaFam Java.TypeDecl
-- instance Deep JavaPrim JavaFam Java.ClassDecl
-- instance Deep JavaPrim JavaFam Java.InterfaceDecl
-- instance Deep JavaPrim JavaFam [Java.Modifier]
-- instance Deep JavaPrim JavaFam [Java.TypeParam]
-- instance Deep JavaPrim JavaFam (Maybe Java.RefType)
-- instance Deep JavaPrim JavaFam Java.ClassBody
-- instance Deep JavaPrim JavaFam Java.EnumBody
-- instance Deep JavaPrim JavaFam Java.Modifier
-- instance Deep JavaPrim JavaFam Java.Annotation
-- instance Deep JavaPrim JavaFam [(Java.Ident, Java.ElementValue)]
-- instance Deep JavaPrim JavaFam Java.ElementValue
-- instance Deep JavaPrim JavaFam (Java.Ident, Java.ElementValue)
-- instance Deep JavaPrim JavaFam Java.VarInit
-- instance Deep JavaPrim JavaFam Java.ArrayInit
-- instance Deep JavaPrim JavaFam Java.Literal
-- instance Deep JavaPrim JavaFam (Maybe Java.Type)
-- instance Deep JavaPrim JavaFam [Java.TypeArgument]
-- instance Deep JavaPrim JavaFam Java.TypeDeclSpecifier
-- instance Deep JavaPrim JavaFam (Maybe Java.ClassBody)
-- instance Deep JavaPrim JavaFam Java.Type
-- instance Deep JavaPrim JavaFam [Java.Exp]
-- instance Deep JavaPrim JavaFam Java.FieldAccess
-- instance Deep JavaPrim JavaFam Java.MethodInvocation
-- instance Deep JavaPrim JavaFam Java.ArrayIndex
-- instance Deep JavaPrim JavaFam Java.Op
-- instance Deep JavaPrim JavaFam Java.Lhs
-- instance Deep JavaPrim JavaFam Java.AssignOp
-- instance Deep JavaPrim JavaFam Java.LambdaParams
-- instance Deep JavaPrim JavaFam Java.LambdaExpression
-- instance Deep JavaPrim JavaFam Java.PrimType
-- instance Deep JavaPrim JavaFam Java.ClassType
-- instance Deep JavaPrim JavaFam [(Java.Ident, [Java.TypeArgument])]
-- instance Deep JavaPrim JavaFam (Java.Ident, [Java.TypeArgument])
-- instance Deep JavaPrim JavaFam Java.TypeArgument
-- instance Deep JavaPrim JavaFam (Maybe Java.WildcardBound)
-- instance Deep JavaPrim JavaFam Java.WildcardBound
-- instance Deep JavaPrim JavaFam Java.Diamond
-- instance Deep JavaPrim JavaFam Java.Argument
-- instance Deep JavaPrim JavaFam [Java.Decl]
-- instance Deep JavaPrim JavaFam Java.Decl
-- instance Deep JavaPrim JavaFam Java.MemberDecl
-- instance Deep JavaPrim JavaFam Java.Block
-- instance Deep JavaPrim JavaFam [Java.VarDecl]
-- instance Deep JavaPrim JavaFam [Java.FormalParam]
-- instance Deep JavaPrim JavaFam [Java.ExceptionType]
-- instance Deep JavaPrim JavaFam (Maybe Java.Exp)
-- instance Deep JavaPrim JavaFam Java.MethodBody
-- instance Deep JavaPrim JavaFam Java.ConstructorBody
-- instance Deep JavaPrim JavaFam Java.VarDecl
-- instance Deep JavaPrim JavaFam Java.VarDeclId
-- instance Deep JavaPrim JavaFam (Maybe Java.VarInit)
-- instance Deep JavaPrim JavaFam Java.TypeParam
-- instance Deep JavaPrim JavaFam Java.FormalParam
-- instance Deep JavaPrim JavaFam Java.ExceptionType
-- instance Deep JavaPrim JavaFam (Maybe Java.Block)
-- instance Deep JavaPrim JavaFam [Java.BlockStmt]
-- instance Deep JavaPrim JavaFam Java.BlockStmt
-- instance Deep JavaPrim JavaFam Java.Stmt
-- instance Deep JavaPrim JavaFam (Maybe Java.ForInit)
-- instance Deep JavaPrim JavaFam (Maybe [Java.Exp])
-- instance Deep JavaPrim JavaFam [Java.SwitchBlock]
-- instance Deep JavaPrim JavaFam (Maybe Java.Ident)
-- instance Deep JavaPrim JavaFam [Java.Catch]
-- instance Deep JavaPrim JavaFam Java.ForInit
-- instance Deep JavaPrim JavaFam Java.SwitchBlock
-- instance Deep JavaPrim JavaFam Java.SwitchLabel
-- instance Deep JavaPrim JavaFam Java.Catch
-- instance Deep JavaPrim JavaFam (Maybe Java.ExplConstrInv)
-- instance Deep JavaPrim JavaFam Java.ExplConstrInv
-- instance Deep JavaPrim JavaFam Java.InterfaceKind
-- instance Deep JavaPrim JavaFam Java.InterfaceBody
-- instance Deep JavaPrim JavaFam [Java.MemberDecl]
-- instance Deep JavaPrim JavaFam [Java.VarInit]
-- instance Deep JavaPrim JavaFam [Java.EnumConstant]
-- instance Deep JavaPrim JavaFam Java.EnumConstant
-- 

parseFile :: String -> ExceptT String IO Java.CompilationUnit
parseFile file = do
  res <- lift $ readFile file
  case Java.parser Java.compilationUnit res of
    Left e  -> throwError (show e) 
    Right r -> return r

dfromJava :: Java.CompilationUnit
          -> SFix JavaPrim JavaFam Java.CompilationUnit
dfromJava = dfrom

#endif
