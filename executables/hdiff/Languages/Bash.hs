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
module Languages.Bash where

import qualified Language.Bash.Syntax as Bash
import qualified Language.Bash.Parse as Bash
import qualified Language.Bash.Word  as Bash
import qualified Language.Bash.Cond  as Bash
import Control.Monad.Except


import Generics.Simplistic

type ShPrim = '[ Bool , String , Char , Int ]

type ShFam =
  [ Bash.List
  , [Bash.Statement]
  , Bash.Statement
  , Bash.AndOr
  , Bash.ListTerm
  , Bash.Pipeline
  , [Bash.Command]
  , Bash.Command
  , Bash.ShellCommand
  , [Bash.Redir]
  , [Bash.Assign]
  , [Bash.Word]
  , Bash.Word
  , [Either Bash.Assign Bash.Word]
  , (Bash.CondExpr Bash.Word)
  , Bash.WordList
  , [Bash.CaseClause]
  , (Maybe Bash.List)
  , Bash.Assign
  , Bash.Parameter
  , Bash.AssignOp
  , Bash.RValue
  , (Maybe Bash.Word)
  , Bash.Span
  , Bash.ParamSubst
  , Bash.ProcessSubstOp
  , Bash.AltOp
  , Bash.Direction
  , (Maybe Bash.Direction)
  , Bash.LetterCaseOp
  , [(Maybe Bash.Word, Bash.Word)]
  , (Maybe Bash.Word, Bash.Word)
  , (Either Bash.Assign Bash.Word)
  , Bash.UnaryOp
  , Bash.BinaryOp
  , Bash.CaseClause
  , Bash.CaseTerm
  , Bash.Redir
  , (Maybe Bash.IODesc)
  , Bash.RedirOp
  , Bash.HeredocOp
  , Bash.IODesc 
  ]

instance HasDecEq ShFam where

instance Deep ShFam ShPrim Bash.List
instance Deep ShFam ShPrim [Bash.Statement]
instance Deep ShFam ShPrim Bash.Statement
instance Deep ShFam ShPrim Bash.AndOr
instance Deep ShFam ShPrim Bash.ListTerm
instance Deep ShFam ShPrim Bash.Pipeline
instance Deep ShFam ShPrim [Bash.Command]
instance Deep ShFam ShPrim Bash.Command
instance Deep ShFam ShPrim Bash.ShellCommand
instance Deep ShFam ShPrim [Bash.Redir]
instance Deep ShFam ShPrim [Bash.Assign]
instance Deep ShFam ShPrim [Bash.Word]
instance Deep ShFam ShPrim Bash.Word
instance Deep ShFam ShPrim [Either Bash.Assign Bash.Word]
instance Deep ShFam ShPrim (Bash.CondExpr Bash.Word)
instance Deep ShFam ShPrim Bash.WordList
instance Deep ShFam ShPrim [Bash.CaseClause]
instance Deep ShFam ShPrim (Maybe Bash.List)
instance Deep ShFam ShPrim Bash.Assign
instance Deep ShFam ShPrim Bash.Parameter
instance Deep ShFam ShPrim Bash.AssignOp
instance Deep ShFam ShPrim Bash.RValue
instance Deep ShFam ShPrim (Maybe Bash.Word)
instance Deep ShFam ShPrim Bash.Span
instance Deep ShFam ShPrim Bash.ParamSubst
instance Deep ShFam ShPrim Bash.ProcessSubstOp
instance Deep ShFam ShPrim Bash.AltOp
instance Deep ShFam ShPrim Bash.Direction
instance Deep ShFam ShPrim (Maybe Bash.Direction)
instance Deep ShFam ShPrim Bash.LetterCaseOp
instance Deep ShFam ShPrim [(Maybe Bash.Word, Bash.Word)]
instance Deep ShFam ShPrim (Maybe Bash.Word, Bash.Word)
instance Deep ShFam ShPrim (Either Bash.Assign Bash.Word)
instance Deep ShFam ShPrim Bash.UnaryOp
instance Deep ShFam ShPrim Bash.BinaryOp
instance Deep ShFam ShPrim Bash.CaseClause
instance Deep ShFam ShPrim Bash.CaseTerm
instance Deep ShFam ShPrim Bash.Redir
instance Deep ShFam ShPrim (Maybe Bash.IODesc)
instance Deep ShFam ShPrim Bash.RedirOp
instance Deep ShFam ShPrim Bash.HeredocOp
instance Deep ShFam ShPrim Bash.IODesc 

parseFile :: String -> ExceptT String IO Bash.List
parseFile file = do
  res <- lift $ readFile file
  case Bash.parse file res of
    Left e  -> throwError (show e) 
    Right r -> return r

dfromSh :: Bash.List -> SFix ShFam ShPrim Bash.List
dfromSh = dfrom
