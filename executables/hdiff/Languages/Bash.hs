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

instance Deep ShPrim Bash.List
instance Deep ShPrim [Bash.Statement]
instance Deep ShPrim Bash.Statement
instance Deep ShPrim Bash.AndOr
instance Deep ShPrim Bash.ListTerm
instance Deep ShPrim Bash.Pipeline
instance Deep ShPrim [Bash.Command]
instance Deep ShPrim Bash.Command
instance Deep ShPrim Bash.ShellCommand
instance Deep ShPrim [Bash.Redir]
instance Deep ShPrim [Bash.Assign]
instance Deep ShPrim [Bash.Word]
instance Deep ShPrim Bash.Word
instance Deep ShPrim [Either Bash.Assign Bash.Word]
instance Deep ShPrim (Bash.CondExpr Bash.Word)
instance Deep ShPrim Bash.WordList
instance Deep ShPrim [Bash.CaseClause]
instance Deep ShPrim (Maybe Bash.List)
instance Deep ShPrim Bash.Assign
instance Deep ShPrim Bash.Parameter
instance Deep ShPrim Bash.AssignOp
instance Deep ShPrim Bash.RValue
instance Deep ShPrim (Maybe Bash.Word)
instance Deep ShPrim Bash.Span
instance Deep ShPrim Bash.ParamSubst
instance Deep ShPrim Bash.ProcessSubstOp
instance Deep ShPrim Bash.AltOp
instance Deep ShPrim Bash.Direction
instance Deep ShPrim (Maybe Bash.Direction)
instance Deep ShPrim Bash.LetterCaseOp
instance Deep ShPrim [(Maybe Bash.Word, Bash.Word)]
instance Deep ShPrim (Maybe Bash.Word, Bash.Word)
instance Deep ShPrim (Either Bash.Assign Bash.Word)
instance Deep ShPrim Bash.UnaryOp
instance Deep ShPrim Bash.BinaryOp
instance Deep ShPrim Bash.CaseClause
instance Deep ShPrim Bash.CaseTerm
instance Deep ShPrim Bash.Redir
instance Deep ShPrim (Maybe Bash.IODesc)
instance Deep ShPrim Bash.RedirOp
instance Deep ShPrim Bash.HeredocOp
instance Deep ShPrim Bash.IODesc 

parseFile :: String -> ExceptT String IO Bash.List
parseFile file = do
  res <- lift $ readFile file
  case Bash.parse file res of
    Left e  -> throwError (show e) 
    Right r -> return r

dfromSh :: Bash.List -> SFix ShPrim Bash.List
dfromSh = dfrom
