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

#ifdef REAL_LANGUAGES

import qualified Language.Bash.Syntax as Bash
import qualified Language.Bash.Parse as Bash
import qualified Language.Bash.Word  as Bash
import qualified Language.Bash.Cond  as Bash
import Control.Monad.Except

import Generics.Simplistic
import Generics.Simplistic.Deep
import Generics.Simplistic.Deep.TH

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

deriveDeepFor ''ShPrim ''ShFam
--
-- instance Deep ShPrim ShFam Bash.List
-- instance Deep ShPrim ShFam [Bash.Statement]
-- instance Deep ShPrim ShFam Bash.Statement
-- instance Deep ShPrim ShFam Bash.AndOr
-- instance Deep ShPrim ShFam Bash.ListTerm
-- instance Deep ShPrim ShFam Bash.Pipeline
-- instance Deep ShPrim ShFam [Bash.Command]
-- instance Deep ShPrim ShFam Bash.Command
-- instance Deep ShPrim ShFam Bash.ShellCommand
-- instance Deep ShPrim ShFam [Bash.Redir]
-- instance Deep ShPrim ShFam [Bash.Assign]
-- instance Deep ShPrim ShFam [Bash.Word]
-- instance Deep ShPrim ShFam Bash.Word
-- instance Deep ShPrim ShFam [Either Bash.Assign Bash.Word]
-- instance Deep ShPrim ShFam (Bash.CondExpr Bash.Word)
-- instance Deep ShPrim ShFam Bash.WordList
-- instance Deep ShPrim ShFam [Bash.CaseClause]
-- instance Deep ShPrim ShFam (Maybe Bash.List)
-- instance Deep ShPrim ShFam Bash.Assign
-- instance Deep ShPrim ShFam Bash.Parameter
-- instance Deep ShPrim ShFam Bash.AssignOp
-- instance Deep ShPrim ShFam Bash.RValue
-- instance Deep ShPrim ShFam (Maybe Bash.Word)
-- instance Deep ShPrim ShFam Bash.Span
-- instance Deep ShPrim ShFam Bash.ParamSubst
-- instance Deep ShPrim ShFam Bash.ProcessSubstOp
-- instance Deep ShPrim ShFam Bash.AltOp
-- instance Deep ShPrim ShFam Bash.Direction
-- instance Deep ShPrim ShFam (Maybe Bash.Direction)
-- instance Deep ShPrim ShFam Bash.LetterCaseOp
-- instance Deep ShPrim ShFam [(Maybe Bash.Word, Bash.Word)]
-- instance Deep ShPrim ShFam (Maybe Bash.Word, Bash.Word)
-- instance Deep ShPrim ShFam (Either Bash.Assign Bash.Word)
-- instance Deep ShPrim ShFam Bash.UnaryOp
-- instance Deep ShPrim ShFam Bash.BinaryOp
-- instance Deep ShPrim ShFam Bash.CaseClause
-- instance Deep ShPrim ShFam Bash.CaseTerm
-- instance Deep ShPrim ShFam Bash.Redir
-- instance Deep ShPrim ShFam (Maybe Bash.IODesc)
-- instance Deep ShPrim ShFam Bash.RedirOp
-- instance Deep ShPrim ShFam Bash.HeredocOp
-- instance Deep ShPrim ShFam Bash.IODesc

parseFile :: String -> ExceptT String IO Bash.List
parseFile file = do
  res <- lift $ readFile file
  case Bash.parse file res of
    Left e  -> throwError (show e)
    Right r -> return r

dfromSh :: Bash.List -> SFix ShPrim ShFam Bash.List
dfromSh = dfrom

#endif
