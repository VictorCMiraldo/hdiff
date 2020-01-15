{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE StandaloneDeriving    #-}
{-# LANGUAGE TypeSynonymInstances  #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE DataKinds             #-}
{-# OPTIONS_GHC -Wno-orphans       #-}
module Languages.Python where

import Control.Monad.Except

import GHC.Generics
import Generics.Simplistic

import Language.Python.Common.AST
import Language.Python.Common.SrcLocation
import Language.Python.Version3.Parser

type PyPrim = '[ String , Int , Integer , Double , Bool ]

deriving instance Generic SrcSpan
deriving instance Generic a => Generic (Module a)
deriving instance Generic a => Generic (Statement a)
deriving instance Generic a => Generic (ImportRelative a)
deriving instance Generic a => Generic (FromItems a)
deriving instance Generic a => Generic (Expr a)
deriving instance Generic a => Generic (Ident a)
deriving instance Generic a => Generic (AssignOp a)
deriving instance Generic a => Generic (RaiseExpr a)
deriving instance Generic a => Generic (ImportItem a)
deriving instance Generic a => Generic (FromItem a)
deriving instance Generic a => Generic (Op a)
deriving instance Generic a => Generic (Comprehension a)
deriving instance Generic a => Generic (Argument a)
deriving instance Generic a => Generic (Slice a)
deriving instance Generic a => Generic (Parameter a)
deriving instance Generic a => Generic (ParamTuple a)
deriving instance Generic a => Generic (YieldArg a)
deriving instance Generic a => Generic (ComprehensionExpr a)
deriving instance Generic a => Generic (CompFor a)
deriving instance Generic a => Generic (DictKeyDatumList a)
deriving instance Generic a => Generic (CompIter a)
deriving instance Generic a => Generic (CompIf a)
deriving instance Generic a => Generic (Decorator a)
deriving instance Generic a => Generic (Handler a)
deriving instance Generic a => Generic (ExceptClause a)

instance Deep PyPrim ()
instance Deep PyPrim SrcSpan
instance Deep PyPrim [String]
instance Deep PyPrim a => Deep PyPrim (Module a)
instance Deep PyPrim a => Deep PyPrim (Statement a)
instance Deep PyPrim a => Deep PyPrim ([ImportItem a])
instance Deep PyPrim a => Deep PyPrim (ImportRelative a)
instance Deep PyPrim a => Deep PyPrim (FromItems a)
instance Deep PyPrim a => Deep PyPrim (Expr a)
instance Deep PyPrim a => Deep PyPrim (Suite a)
instance Deep PyPrim a => Deep PyPrim ([Expr a])
instance Deep PyPrim a => Deep PyPrim (Ident a)
instance Deep PyPrim a => Deep PyPrim ([Parameter a])
instance Deep PyPrim a => Deep PyPrim (Maybe (Expr a))
instance Deep PyPrim a => Deep PyPrim ([Argument a])
instance Deep PyPrim a => Deep PyPrim ([(Expr a, Suite a)])
instance Deep PyPrim a => Deep PyPrim (AssignOp a)
instance Deep PyPrim a => Deep PyPrim ([Decorator a])
instance Deep PyPrim a => Deep PyPrim ([Handler a])
instance Deep PyPrim a => Deep PyPrim (RaiseExpr a)
instance Deep PyPrim a => Deep PyPrim ([(Expr a, Maybe (Expr a))])
instance Deep PyPrim a => Deep PyPrim (Maybe (Expr a, Maybe (Expr a)))
instance Deep PyPrim a => Deep PyPrim (ImportItem a)
instance Deep PyPrim a => Deep PyPrim (DottedName a)
instance Deep PyPrim a => Deep PyPrim (Maybe (Ident a))
instance Deep PyPrim a => Deep PyPrim (Maybe (DottedName a))
instance Deep PyPrim a => Deep PyPrim ([FromItem a])
instance Deep PyPrim a => Deep PyPrim (FromItem a)
instance Deep PyPrim a => Deep PyPrim ([Slice a])
instance Deep PyPrim a => Deep PyPrim (Op a)
instance Deep PyPrim a => Deep PyPrim (Maybe (YieldArg a))
instance Deep PyPrim a => Deep PyPrim (Comprehension a)
instance Deep PyPrim a => Deep PyPrim ([DictKeyDatumList a])
instance Deep PyPrim a => Deep PyPrim (Argument a)
instance Deep PyPrim a => Deep PyPrim (Slice a)
instance Deep PyPrim a => Deep PyPrim (Maybe (Maybe (Expr a)))
instance Deep PyPrim a => Deep PyPrim (Parameter a)
instance Deep PyPrim a => Deep PyPrim (ParamTuple a)
instance Deep PyPrim a => Deep PyPrim ([ParamTuple a])
instance Deep PyPrim a => Deep PyPrim (YieldArg a)
instance Deep PyPrim a => Deep PyPrim (ComprehensionExpr a)
instance Deep PyPrim a => Deep PyPrim (CompFor a)
instance Deep PyPrim a => Deep PyPrim (DictKeyDatumList a)
instance Deep PyPrim a => Deep PyPrim (Maybe (CompIter a))
instance Deep PyPrim a => Deep PyPrim (CompIter a)
instance Deep PyPrim a => Deep PyPrim (CompIf a)
instance Deep PyPrim a => Deep PyPrim ((Expr a , Suite a))
instance Deep PyPrim a => Deep PyPrim (Decorator a)
instance Deep PyPrim a => Deep PyPrim (Handler a)
instance Deep PyPrim a => Deep PyPrim (ExceptClause a)
instance Deep PyPrim a => Deep PyPrim ((Expr a, Maybe (Expr a)))
instance Deep PyPrim a => Deep PyPrim (Maybe (Expr a, Maybe (Expr a, Maybe (Expr a))))
instance Deep PyPrim a => Deep PyPrim ((Expr a, Maybe (Expr a, Maybe (Expr a))))

parseFile :: String -> ExceptT String IO (Module SrcSpan)
parseFile file = do
  res <- lift $ readFile file
  case parseModule res file of
    Left e  -> throwError (show e) 
    Right r -> return (fst r)

dfromPy :: Module SrcSpan -> SFix PyPrim (Module SrcSpan)
dfromPy = dfrom

-- Forgets source location information
dfromPy' :: Module SrcSpan -> SFix PyPrim (Module ())
dfromPy' = dfrom . fmap (const ())
