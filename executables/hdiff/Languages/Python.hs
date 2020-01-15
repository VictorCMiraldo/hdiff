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
module Languages.Python where

import Data.Text (Text)
import Control.Monad.Except

import GHC.Generics
import Generics.Simplistic

import Language.Python.Common.AST
import Language.Python.Common.SrcLocation
import Language.Python.Version3.Parser

type PyPrim = '[ String , Int , Integer , Double , Bool ]
deriving instance Generic (Module SrcSpan)
deriving instance Generic (Statement SrcSpan)
deriving instance Generic SrcSpan
deriving instance Generic (ImportRelative SrcSpan)
deriving instance Generic (FromItems SrcSpan)
deriving instance Generic (Expr SrcSpan)
deriving instance Generic (Ident SrcSpan)
deriving instance Generic (AssignOp SrcSpan)
deriving instance Generic (RaiseExpr SrcSpan)
deriving instance Generic (ImportItem SrcSpan)
deriving instance Generic (FromItem SrcSpan)
deriving instance Generic (Op SrcSpan)
deriving instance Generic (Comprehension SrcSpan)
deriving instance Generic (Argument SrcSpan)
deriving instance Generic (Slice SrcSpan)
deriving instance Generic (Parameter SrcSpan)
deriving instance Generic (ParamTuple SrcSpan)
deriving instance Generic (YieldArg SrcSpan)
deriving instance Generic (ComprehensionExpr SrcSpan)
deriving instance Generic (CompFor SrcSpan)
deriving instance Generic (DictKeyDatumList SrcSpan)
deriving instance Generic (CompIter SrcSpan)
deriving instance Generic (CompIf SrcSpan)
deriving instance Generic (Decorator SrcSpan)
deriving instance Generic (Handler SrcSpan)
deriving instance Generic (ExceptClause SrcSpan)

instance Deep PyPrim (Module SrcSpan)
instance Deep PyPrim (Statement SrcSpan)
instance Deep PyPrim ([ImportItem SrcSpan])
instance Deep PyPrim SrcSpan
instance Deep PyPrim (ImportRelative SrcSpan)
instance Deep PyPrim (FromItems SrcSpan)
instance Deep PyPrim (Expr SrcSpan)
instance Deep PyPrim (Suite SrcSpan)
instance Deep PyPrim ([Expr SrcSpan])
instance Deep PyPrim (Ident SrcSpan)
instance Deep PyPrim ([Parameter SrcSpan])
instance Deep PyPrim (Maybe (Expr SrcSpan))
instance Deep PyPrim ([Argument SrcSpan])
instance Deep PyPrim ([(Expr SrcSpan, Suite SrcSpan)])
instance Deep PyPrim (AssignOp SrcSpan)
instance Deep PyPrim ([Decorator SrcSpan])
instance Deep PyPrim ([Handler SrcSpan])
instance Deep PyPrim (RaiseExpr SrcSpan)
instance Deep PyPrim ([(Expr SrcSpan, Maybe (Expr SrcSpan))])
instance Deep PyPrim (Maybe (Expr SrcSpan, Maybe (Expr SrcSpan)))
instance Deep PyPrim (ImportItem SrcSpan)
instance Deep PyPrim (DottedName SrcSpan)
instance Deep PyPrim (Maybe (Ident SrcSpan))
instance Deep PyPrim (Maybe (DottedName SrcSpan))
instance Deep PyPrim ([FromItem SrcSpan])
instance Deep PyPrim (FromItem SrcSpan)
instance Deep PyPrim [String]
instance Deep PyPrim ([Slice SrcSpan])
instance Deep PyPrim (Op SrcSpan)
instance Deep PyPrim (Maybe (YieldArg SrcSpan))
instance Deep PyPrim (Comprehension SrcSpan)
instance Deep PyPrim ([DictKeyDatumList SrcSpan])
instance Deep PyPrim (Argument SrcSpan)
instance Deep PyPrim (Slice SrcSpan)
instance Deep PyPrim (Maybe (Maybe (Expr SrcSpan)))
instance Deep PyPrim (Parameter SrcSpan)
instance Deep PyPrim (ParamTuple SrcSpan)
instance Deep PyPrim ([ParamTuple SrcSpan])
instance Deep PyPrim (YieldArg SrcSpan)
instance Deep PyPrim (ComprehensionExpr SrcSpan)
instance Deep PyPrim (CompFor SrcSpan)
instance Deep PyPrim (DictKeyDatumList SrcSpan)
instance Deep PyPrim (Maybe (CompIter SrcSpan))
instance Deep PyPrim (CompIter SrcSpan)
instance Deep PyPrim (CompIf SrcSpan)
instance Deep PyPrim ((Expr SrcSpan , Suite SrcSpan))
instance Deep PyPrim (Decorator SrcSpan)
instance Deep PyPrim (Handler SrcSpan)
instance Deep PyPrim (ExceptClause SrcSpan)
instance Deep PyPrim ((Expr SrcSpan, Maybe (Expr SrcSpan)))
instance Deep PyPrim (Maybe (Expr SrcSpan, Maybe (Expr SrcSpan, Maybe (Expr SrcSpan))))
instance Deep PyPrim ((Expr SrcSpan, Maybe (Expr SrcSpan, Maybe (Expr SrcSpan))))

parseFile :: String -> ExceptT String IO (Module SrcSpan)
parseFile file = do
  res <- lift $ readFile file
  case parseModule res file of
    Left e  -> throwError (show e) 
    Right r -> return (fst r)

dfromPy :: Module SrcSpan -> SFix PyPrim (Module SrcSpan)
dfromPy = dfrom
