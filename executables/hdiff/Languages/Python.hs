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

instance Deep PyFam PyPrim ()
instance Deep PyFam PyPrim [String]
instance Deep PyFam PyPrim (Module ())
instance Deep PyFam PyPrim (Statement ())
instance Deep PyFam PyPrim ([ImportItem ()])
instance Deep PyFam PyPrim (ImportRelative ())
instance Deep PyFam PyPrim (FromItems ())
instance Deep PyFam PyPrim (Expr ())
instance Deep PyFam PyPrim (Suite ())
instance Deep PyFam PyPrim ([Expr ()])
instance Deep PyFam PyPrim (Ident ())
instance Deep PyFam PyPrim ([Parameter ()])
instance Deep PyFam PyPrim (Maybe (Expr ()))
instance Deep PyFam PyPrim ([Argument ()])
instance Deep PyFam PyPrim ([(Expr (), Suite ())])
instance Deep PyFam PyPrim (AssignOp ())
instance Deep PyFam PyPrim ([Decorator ()])
instance Deep PyFam PyPrim ([Handler ()])
instance Deep PyFam PyPrim (RaiseExpr ())
instance Deep PyFam PyPrim ([(Expr (), Maybe (Expr ()))])
instance Deep PyFam PyPrim (Maybe (Expr (), Maybe (Expr ())))
instance Deep PyFam PyPrim (ImportItem ())
instance Deep PyFam PyPrim (DottedName ())
instance Deep PyFam PyPrim (Maybe (Ident ()))
instance Deep PyFam PyPrim (Maybe (DottedName ()))
instance Deep PyFam PyPrim ([FromItem ()])
instance Deep PyFam PyPrim (FromItem ())
instance Deep PyFam PyPrim ([Slice ()])
instance Deep PyFam PyPrim (Op ())
instance Deep PyFam PyPrim (Maybe (YieldArg ()))
instance Deep PyFam PyPrim (Comprehension ())
instance Deep PyFam PyPrim ([DictKeyDatumList ()])
instance Deep PyFam PyPrim (Argument ())
instance Deep PyFam PyPrim (Slice ())
instance Deep PyFam PyPrim (Maybe (Maybe (Expr ())))
instance Deep PyFam PyPrim (Parameter ())
instance Deep PyFam PyPrim (ParamTuple ())
instance Deep PyFam PyPrim ([ParamTuple ()])
instance Deep PyFam PyPrim (YieldArg ())
instance Deep PyFam PyPrim (ComprehensionExpr ())
instance Deep PyFam PyPrim (CompFor ())
instance Deep PyFam PyPrim (DictKeyDatumList ())
instance Deep PyFam PyPrim (Maybe (CompIter ()))
instance Deep PyFam PyPrim (CompIter ())
instance Deep PyFam PyPrim (CompIf ())
instance Deep PyFam PyPrim ((Expr () , Suite ()))
instance Deep PyFam PyPrim (Decorator ())
instance Deep PyFam PyPrim (Handler ())
instance Deep PyFam PyPrim (ExceptClause ())
instance Deep PyFam PyPrim ((Expr (), Maybe (Expr ())))
instance Deep PyFam PyPrim (Maybe (Expr (), Maybe (Expr (), Maybe (Expr ()))))
instance Deep PyFam PyPrim ((Expr (), Maybe (Expr (), Maybe (Expr ()))))

{-
instance Deep PyFam PyPrim (Module a)
instance Deep PyFam PyPrim (Statement a)
instance Deep PyFam PyPrim ([ImportItem a])
instance Deep PyFam PyPrim (ImportRelative a)
instance Deep PyFam PyPrim (FromItems a)
instance Deep PyFam PyPrim (Expr a)
instance Deep PyFam PyPrim (Suite a)
instance Deep PyFam PyPrim ([Expr a])
instance Deep PyFam PyPrim (Ident a)
instance Deep PyFam PyPrim ([Parameter a])
instance Deep PyFam PyPrim (Maybe (Expr a))
instance Deep PyFam PyPrim ([Argument a])
instance Deep PyFam PyPrim ([(Expr a, Suite a)])
instance Deep PyFam PyPrim (AssignOp a)
instance Deep PyFam PyPrim ([Decorator a])
instance Deep PyFam PyPrim ([Handler a])
instance Deep PyFam PyPrim (RaiseExpr a)
instance Deep PyFam PyPrim ([(Expr a, Maybe (Expr a))])
instance Deep PyFam PyPrim (Maybe (Expr a, Maybe (Expr a)))
instance Deep PyFam PyPrim (ImportItem a)
instance Deep PyFam PyPrim (DottedName a)
instance Deep PyFam PyPrim (Maybe (Ident a))
instance Deep PyFam PyPrim (Maybe (DottedName a))
instance Deep PyFam PyPrim ([FromItem a])
instance Deep PyFam PyPrim (FromItem a)
instance Deep PyFam PyPrim ([Slice a])
instance Deep PyFam PyPrim (Op a)
instance Deep PyFam PyPrim (Maybe (YieldArg a))
instance Deep PyFam PyPrim (Comprehension a)
instance Deep PyFam PyPrim ([DictKeyDatumList a])
instance Deep PyFam PyPrim (Argument a)
instance Deep PyFam PyPrim (Slice a)
instance Deep PyFam PyPrim (Maybe (Maybe (Expr a)))
instance Deep PyFam PyPrim (Parameter a)
instance Deep PyFam PyPrim (ParamTuple a)
instance Deep PyFam PyPrim ([ParamTuple a])
instance Deep PyFam PyPrim (YieldArg a)
instance Deep PyFam PyPrim (ComprehensionExpr a)
instance Deep PyFam PyPrim (CompFor a)
instance Deep PyFam PyPrim (DictKeyDatumList a)
instance Deep PyFam PyPrim (Maybe (CompIter a))
instance Deep PyFam PyPrim (CompIter a)
instance Deep PyFam PyPrim (CompIf a)
instance Deep PyFam PyPrim ((Expr a , Suite a))
instance Deep PyFam PyPrim (Decorator a)
instance Deep PyFam PyPrim (Handler a)
instance Deep PyFam PyPrim (ExceptClause a)
instance Deep PyFam PyPrim ((Expr a, Maybe (Expr a)))
instance Deep PyFam PyPrim (Maybe (Expr a, Maybe (Expr a, Maybe (Expr a))))
instance Deep PyFam PyPrim ((Expr a, Maybe (Expr a, Maybe (Expr a))))
-}

type PyFam = '[ () , [String] ,  
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
{-
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
  ] 

instance HasDecEq PyFam where

parseFile :: String -> ExceptT String IO (Module SrcSpan)
parseFile file = do
  res <- lift $ readFile file
  case parseModule res file of
    Left e  -> throwError (show e) 
    Right r -> return (fst r)

-- dfromPy :: Module SrcSpan -> SFix PyFam PyPrim (Module SrcSpan)
-- dfromPy = dfrom

-- Forgets source location information
dfromPy' :: Module SrcSpan -> SFix PyFam PyPrim (Module ())
dfromPy' = dfrom . fmap (const ())
