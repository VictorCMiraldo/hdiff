{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE StandaloneDeriving    #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeSynonymInstances  #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE DataKinds             #-}
{-# OPTIONS_GHC -Wno-orphans       #-}
module Languages.JavaScript where

import Language.ECMAScript3.Syntax
import Language.ECMAScript3.Parser
import Text.Parsec.Pos 

import Control.Monad.Except

import GHC.Generics
import Generics.Simplistic

type JSPrim = '[ String , Int , Integer , Double , Bool , Char]

data Loc = Loc String Int Int
    deriving ( Eq, Ord , Generic)

deriving instance (Generic a) => Generic (JavaScript a)
deriving instance (Generic a) => Generic (Statement a)
deriving instance (Generic a) => Generic (Expression a)
deriving instance (Generic a) => Generic (Id a)
deriving instance (Generic a) => Generic (ForInInit a)
deriving instance (Generic a) => Generic (ForInit a)
deriving instance Generic PrefixOp
deriving instance Generic UnaryAssignOp
deriving instance (Generic a) => Generic (LValue a)
deriving instance Generic InfixOp
deriving instance Generic AssignOp
deriving instance (Generic a) => Generic (Prop a)
deriving instance (Generic a) => Generic (CaseClause a)
deriving instance (Generic a) => Generic (VarDecl a)
deriving instance (Generic a) => Generic (CatchClause a)

instance Deep JSPrim Loc
instance Deep JSPrim ()
instance (Deep JSPrim a) => Deep JSPrim (JavaScript a)
instance (Deep JSPrim a) => Deep JSPrim [Statement a]
instance (Deep JSPrim a) => Deep JSPrim (Statement a)
instance (Deep JSPrim a) => Deep JSPrim (Expression a)
instance (Deep JSPrim a) => Deep JSPrim [CaseClause a]
instance (Deep JSPrim a) => Deep JSPrim (Maybe (Id a))
instance (Deep JSPrim a) => Deep JSPrim (Id a)
instance (Deep JSPrim a) => Deep JSPrim (ForInInit a)
instance (Deep JSPrim a) => Deep JSPrim (ForInit a)
instance (Deep JSPrim a) => Deep JSPrim (Maybe (Expression a))
instance (Deep JSPrim a) => Deep JSPrim (Maybe (CatchClause a))
instance (Deep JSPrim a) => Deep JSPrim (Maybe (Statement a))
instance (Deep JSPrim a) => Deep JSPrim [VarDecl a]
instance (Deep JSPrim a) => Deep JSPrim [Id a]
instance (Deep JSPrim a) => Deep JSPrim [Expression a]
instance (Deep JSPrim a) => Deep JSPrim [(Prop a, Expression a)]
instance Deep JSPrim PrefixOp
instance Deep JSPrim UnaryAssignOp
instance (Deep JSPrim a) => Deep JSPrim (LValue a)
instance Deep JSPrim InfixOp
instance Deep JSPrim AssignOp
instance (Deep JSPrim a) => Deep JSPrim (Prop a, Expression a)
instance (Deep JSPrim a) => Deep JSPrim (Prop a)
instance (Deep JSPrim a) => Deep JSPrim (CaseClause a)
instance (Deep JSPrim a) => Deep JSPrim (VarDecl a)
instance (Deep JSPrim a) => Deep JSPrim (CatchClause a)


parseFile :: String -> ExceptT String IO (JavaScript Loc)
parseFile file = do
  res <- lift $ readFile file
  case parseFromString res of
    Left e  -> throwError (show e) 
    Right r -> return (fmap mkLoc r)
 where
   mkLoc :: SourcePos -> Loc
   mkLoc sp = Loc (sourceName sp) (sourceLine sp) (sourceColumn sp)

-- Drops location information
dfromJS' :: JavaScript Loc -> SFix JSPrim (JavaScript ())
dfromJS' = dfrom . fmap (const ())

dfromJS :: JavaScript Loc -> SFix JSPrim (JavaScript Loc)
dfromJS = dfrom
