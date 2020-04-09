{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE StandaloneDeriving    #-}
{-# LANGUAGE TypeSynonymInstances  #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# OPTIONS_GHC -Wno-orphans       #-}
module Languages.Python where

#ifdef REAL_LANGUAGES

import Control.Monad.Except

import GHC.Generics
import Generics.Simplistic
import Generics.Simplistic.Deep
import Generics.Simplistic.Deep.TH

import Language.Python.Common.AST
import Language.Python.Common.SrcLocation
import Language.Python.Version3.Parser

type PyPrim = '[ String , Int , Integer , Double , Bool ]

deriving instance Generic SrcSpan
deriving instance Generic (Module ())
deriving instance Generic (Statement ())
deriving instance Generic (ImportRelative ())
deriving instance Generic (FromItems ())
deriving instance Generic (Expr ())
deriving instance Generic (Ident ())
deriving instance Generic (AssignOp ())
deriving instance Generic (RaiseExpr ())
deriving instance Generic (ImportItem ())
deriving instance Generic (FromItem ())
deriving instance Generic (Op ())
deriving instance Generic (Comprehension ())
deriving instance Generic (Argument ())
deriving instance Generic (Slice ())
deriving instance Generic (Parameter ())
deriving instance Generic (ParamTuple ())
deriving instance Generic (YieldArg ())
deriving instance Generic (ComprehensionExpr ())
deriving instance Generic (CompFor ())
deriving instance Generic (DictKeyDatumList ())
deriving instance Generic (CompIter ())
deriving instance Generic (CompIf ())
deriving instance Generic (Decorator ())
deriving instance Generic (Handler ())
deriving instance Generic (ExceptClause ())

type PyFam = '[ () , [String] , SrcSpan,
     Module ()
  ,  Statement ()
  ,  [ImportItem ()]
  ,  ImportRelative ()
  ,  FromItems ()
  ,  Expr ()
  ,  Suite ()
  ,  [Expr ()]
  ,  Ident ()
  ,  [Parameter ()]
  ,  Maybe (Expr ())
  ,  [Argument ()]
  ,  [(Expr (), Suite ())]
  ,  AssignOp ()
  ,  [Decorator ()]
  ,  [Handler ()]
  ,  RaiseExpr ()
  ,  [(Expr (), Maybe (Expr ()))]
  ,  Maybe (Expr (), Maybe (Expr ()))
  ,  ImportItem ()
  ,  DottedName ()
  ,  Maybe (Ident ())
  ,  Maybe (DottedName ())
  ,  [FromItem ()]
  ,  FromItem ()
  ,  [Slice ()]
  ,  Op ()
  ,  Maybe (YieldArg ())
  ,  Comprehension ()
  ,  [DictKeyDatumList ()]
  ,  Argument ()
  ,  Slice ()
  ,  Maybe (Maybe (Expr ()))
  ,  Parameter ()
  ,  ParamTuple ()
  ,  [ParamTuple ()]
  ,  YieldArg ()
  ,  ComprehensionExpr ()
  ,  CompFor ()
  ,  DictKeyDatumList ()
  ,  Maybe (CompIter ())
  ,  CompIter ()
  ,  CompIf ()
  ,  (Expr () , Suite ())
  ,  Decorator ()
  ,  Handler ()
  ,  ExceptClause ()
  ,  (Expr (), Maybe (Expr ()))
  ,  Maybe (Expr (), Maybe (Expr (), Maybe (Expr ())))
  ,  (Expr (), Maybe (Expr (), Maybe (Expr ())))
  ]

deriveDeepFor ''PyPrim ''PyFam

-- instance Deep PyPrim PyFam ()
-- instance Deep PyPrim PyFam SrcSpan
-- instance Deep PyPrim PyFam [String]
-- instance Deep PyPrim PyFam (Module ())
-- instance Deep PyPrim PyFam (Statement ())
-- instance Deep PyPrim PyFam ([ImportItem ()])
-- instance Deep PyPrim PyFam (ImportRelative ())
-- instance Deep PyPrim PyFam (FromItems ())
-- instance Deep PyPrim PyFam (Expr ())
-- instance Deep PyPrim PyFam (Suite ())
-- instance Deep PyPrim PyFam ([Expr ()])
-- instance Deep PyPrim PyFam (Ident ())
-- instance Deep PyPrim PyFam ([Parameter ()])
-- instance Deep PyPrim PyFam (Maybe (Expr ()))
-- instance Deep PyPrim PyFam ([Argument ()])
-- instance Deep PyPrim PyFam ([(Expr (), Suite ())])
-- instance Deep PyPrim PyFam (AssignOp ())
-- instance Deep PyPrim PyFam ([Decorator ()])
-- instance Deep PyPrim PyFam ([Handler ()])
-- instance Deep PyPrim PyFam (RaiseExpr ())
-- instance Deep PyPrim PyFam ([(Expr (), Maybe (Expr ()))])
-- instance Deep PyPrim PyFam (Maybe (Expr (), Maybe (Expr ())))
-- instance Deep PyPrim PyFam (ImportItem ())
-- instance Deep PyPrim PyFam (DottedName ())
-- instance Deep PyPrim PyFam (Maybe (Ident ()))
-- instance Deep PyPrim PyFam (Maybe (DottedName ()))
-- instance Deep PyPrim PyFam ([FromItem ()])
-- instance Deep PyPrim PyFam (FromItem ())
-- instance Deep PyPrim PyFam ([Slice ()])
-- instance Deep PyPrim PyFam (Op ())
-- instance Deep PyPrim PyFam (Maybe (YieldArg ()))
-- instance Deep PyPrim PyFam (Comprehension ())
-- instance Deep PyPrim PyFam ([DictKeyDatumList ()])
-- instance Deep PyPrim PyFam (Argument ())
-- instance Deep PyPrim PyFam (Slice ())
-- instance Deep PyPrim PyFam (Maybe (Maybe (Expr ())))
-- instance Deep PyPrim PyFam (Parameter ())
-- instance Deep PyPrim PyFam (ParamTuple ())
-- instance Deep PyPrim PyFam ([ParamTuple ()])
-- instance Deep PyPrim PyFam (YieldArg ())
-- instance Deep PyPrim PyFam (ComprehensionExpr ())
-- instance Deep PyPrim PyFam (CompFor ())
-- instance Deep PyPrim PyFam (DictKeyDatumList ())
-- instance Deep PyPrim PyFam (Maybe (CompIter ()))
-- instance Deep PyPrim PyFam (CompIter ())
-- instance Deep PyPrim PyFam (CompIf ())
-- instance Deep PyPrim PyFam ((Expr () , Suite ()))
-- instance Deep PyPrim PyFam (Decorator ())
-- instance Deep PyPrim PyFam (Handler ())
-- instance Deep PyPrim PyFam (ExceptClause ())
-- instance Deep PyPrim PyFam ((Expr (), Maybe (Expr ())))
-- instance Deep PyPrim PyFam (Maybe (Expr (), Maybe (Expr (), Maybe (Expr ()))))
-- instance Deep PyPrim PyFam ((Expr (), Maybe (Expr (), Maybe (Expr ()))))


parseFile :: String -> ExceptT String IO (Module SrcSpan)
parseFile file = do
  res <- lift $ readFile file
  case parseModule res file of
    Left e  -> throwError (show e)
    Right r -> return (fst r)

-- Forgets source location information
dfromPy' :: Module SrcSpan -> SFix PyPrim PyFam (Module ())
dfromPy' = dfrom . fmap (const ())


{-


dfromPy :: Module SrcSpan -> SFix PyPrim PyFam (Module SrcSpan)
dfromPy = dfrom

SrcLocations only makes things worse; no need to pay off
compilation time.

deriving instance Generic (Module SrcSpan)
deriving instance Generic (Statement SrcSpan)
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
instance Deep PyPrim PyFam (Module SrcSpan)
instance Deep PyPrim PyFam (Statement SrcSpan)
instance Deep PyPrim PyFam ([ImportItem SrcSpan])
instance Deep PyPrim PyFam (ImportRelative SrcSpan)
instance Deep PyPrim PyFam (FromItems SrcSpan)
instance Deep PyPrim PyFam (Expr SrcSpan)
instance Deep PyPrim PyFam (Suite SrcSpan)
instance Deep PyPrim PyFam ([Expr SrcSpan])
instance Deep PyPrim PyFam (Ident SrcSpan)
instance Deep PyPrim PyFam ([Parameter SrcSpan])
instance Deep PyPrim PyFam (Maybe (Expr SrcSpan))
instance Deep PyPrim PyFam ([Argument SrcSpan])
instance Deep PyPrim PyFam ([(Expr SrcSpan, Suite SrcSpan)])
instance Deep PyPrim PyFam (AssignOp SrcSpan)
instance Deep PyPrim PyFam ([Decorator SrcSpan])
instance Deep PyPrim PyFam ([Handler SrcSpan])
instance Deep PyPrim PyFam (RaiseExpr SrcSpan)
instance Deep PyPrim PyFam ([(Expr SrcSpan, Maybe (Expr SrcSpan))])
instance Deep PyPrim PyFam (Maybe (Expr SrcSpan, Maybe (Expr SrcSpan)))
instance Deep PyPrim PyFam (ImportItem SrcSpan)
instance Deep PyPrim PyFam (DottedName SrcSpan)
instance Deep PyPrim PyFam (Maybe (Ident SrcSpan))
instance Deep PyPrim PyFam (Maybe (DottedName SrcSpan))
instance Deep PyPrim PyFam ([FromItem SrcSpan])
instance Deep PyPrim PyFam (FromItem SrcSpan)
instance Deep PyPrim PyFam ([Slice SrcSpan])
instance Deep PyPrim PyFam (Op SrcSpan)
instance Deep PyPrim PyFam (Maybe (YieldArg SrcSpan))
instance Deep PyPrim PyFam (Comprehension SrcSpan)
instance Deep PyPrim PyFam ([DictKeyDatumList SrcSpan])
instance Deep PyPrim PyFam (Argument SrcSpan)
instance Deep PyPrim PyFam (Slice SrcSpan)
instance Deep PyPrim PyFam (Maybe (Maybe (Expr SrcSpan)))
instance Deep PyPrim PyFam (Parameter SrcSpan)
instance Deep PyPrim PyFam (ParamTuple SrcSpan)
instance Deep PyPrim PyFam ([ParamTuple SrcSpan])
instance Deep PyPrim PyFam (YieldArg SrcSpan)
instance Deep PyPrim PyFam (ComprehensionExpr SrcSpan)
instance Deep PyPrim PyFam (CompFor SrcSpan)
instance Deep PyPrim PyFam (DictKeyDatumList SrcSpan)
instance Deep PyPrim PyFam (Maybe (CompIter SrcSpan))
instance Deep PyPrim PyFam (CompIter SrcSpan)
instance Deep PyPrim PyFam (CompIf SrcSpan)
instance Deep PyPrim PyFam ((Expr SrcSpan , Suite SrcSpan))
instance Deep PyPrim PyFam (Decorator SrcSpan)
instance Deep PyPrim PyFam (Handler SrcSpan)
instance Deep PyPrim PyFam (ExceptClause SrcSpan)
instance Deep PyPrim PyFam ((Expr SrcSpan, Maybe (Expr SrcSpan)))
instance Deep PyPrim PyFam (Maybe (Expr SrcSpan, Maybe (Expr SrcSpan, Maybe (Expr SrcSpan))))
instance Deep PyPrim PyFam ((Expr SrcSpan, Maybe (Expr SrcSpan, Maybe (Expr SrcSpan))))


  ,  Module SrcSpan
  ,  Statement SrcSpan
  ,  [ImportItem SrcSpan]
  ,  ImportRelative SrcSpan
  ,  FromItems SrcSpan
  ,  Expr SrcSpan
  ,  Suite SrcSpan
  ,  [Expr SrcSpan]
  ,  Ident SrcSpan
  ,  [Parameter SrcSpan]
  ,  Maybe (Expr SrcSpan)
  ,  [Argument SrcSpan]
  ,  [(Expr SrcSpan, Suite SrcSpan)]
  ,  AssignOp SrcSpan
  ,  [Decorator SrcSpan]
  ,  [Handler SrcSpan]
  ,  RaiseExpr SrcSpan
  ,  [(Expr SrcSpan, Maybe (Expr SrcSpan))]
  ,  Maybe (Expr SrcSpan, Maybe (Expr SrcSpan))
  ,  ImportItem SrcSpan
  ,  DottedName SrcSpan
  ,  Maybe (Ident SrcSpan)
  ,  Maybe (DottedName SrcSpan)
  ,  [FromItem SrcSpan]
  ,  FromItem SrcSpan
  ,  [Slice SrcSpan]
  ,  Op SrcSpan
  ,  Maybe (YieldArg SrcSpan)
  ,  Comprehension SrcSpan
  ,  [DictKeyDatumList SrcSpan]
  ,  Argument SrcSpan
  ,  Slice SrcSpan
  ,  Maybe (Maybe (Expr SrcSpan))
  ,  Parameter SrcSpan
  ,  ParamTuple SrcSpan
  ,  [ParamTuple SrcSpan]
  ,  YieldArg SrcSpan
  ,  ComprehensionExpr SrcSpan
  ,  CompFor SrcSpan
  ,  DictKeyDatumList SrcSpan
  ,  Maybe (CompIter SrcSpan)
  ,  CompIter SrcSpan
  ,  CompIf SrcSpan
  ,  (Expr SrcSpan , Suite SrcSpan)
  ,  Decorator SrcSpan
  ,  Handler SrcSpan
  ,  ExceptClause SrcSpan
  ,  (Expr SrcSpan, Maybe (Expr SrcSpan))
  ,  Maybe (Expr SrcSpan, Maybe (Expr SrcSpan, Maybe (Expr SrcSpan)))
  ,  (Expr SrcSpan, Maybe (Expr SrcSpan, Maybe (Expr SrcSpan)))


-}

#endif
