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

instance Deep JSFam JSPrim ()
instance Deep JSFam JSPrim InfixOp
instance Deep JSFam JSPrim AssignOp
instance Deep JSFam JSPrim PrefixOp
instance Deep JSFam JSPrim UnaryAssignOp

instance Deep JSFam JSPrim (JavaScript ())
instance Deep JSFam JSPrim [Statement ()]
instance Deep JSFam JSPrim (Statement ())
instance Deep JSFam JSPrim (Expression ())
instance Deep JSFam JSPrim [CaseClause ()]
instance Deep JSFam JSPrim (Maybe (Id ()))
instance Deep JSFam JSPrim (Id ())
instance Deep JSFam JSPrim (ForInInit ())
instance Deep JSFam JSPrim (ForInit ())
instance Deep JSFam JSPrim (Maybe (Expression ()))
instance Deep JSFam JSPrim (Maybe (CatchClause ()))
instance Deep JSFam JSPrim (Maybe (Statement ()))
instance Deep JSFam JSPrim [VarDecl ()]
instance Deep JSFam JSPrim [Id ()]
instance Deep JSFam JSPrim [Expression ()]
instance Deep JSFam JSPrim [(Prop (), Expression ())]
instance Deep JSFam JSPrim (LValue ())
instance Deep JSFam JSPrim (Prop (), Expression ())
instance Deep JSFam JSPrim (Prop ())
instance Deep JSFam JSPrim (CaseClause ())
instance Deep JSFam JSPrim (VarDecl ())
instance Deep JSFam JSPrim (CatchClause ())


type JSFam =
  [ () , InfixOp , AssignOp , PrefixOp , UnaryAssignOp
  , (JavaScript ())
  , [Statement ()]
  , (Statement ())
  , (Expression ())
  , [CaseClause ()]
  , (Maybe (Id ()))
  , (Id ())
  , (ForInInit ())
  , (ForInit ())
  , (Maybe (Expression ()))
  , (Maybe (CatchClause ()))
  , (Maybe (Statement ()))
  , [VarDecl ()]
  , [Id ()]
  , [Expression ()]
  , [(Prop (), Expression ())]
  , (LValue ())
  , (Prop (), Expression ())
  , (Prop ())
  , (CaseClause ())
  , (VarDecl ())
  , (CatchClause ())
  ]

instance HasDecEq JSFam where

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
dfromJS' :: JavaScript Loc -> SFix JSFam JSPrim (JavaScript ())
dfromJS' = dfrom . fmap (const ())


{-

dfromJS :: JavaScript Loc -> SFix JSFam JSPrim (JavaScript Loc)
dfromJS = dfrom

instance Deep JSFam JSPrim Loc

instance Deep JSFam JSPrim (JavaScript Loc)
instance Deep JSFam JSPrim [Statement Loc]
instance Deep JSFam JSPrim (Statement Loc)
instance Deep JSFam JSPrim (Expression Loc)
instance Deep JSFam JSPrim [CaseClause Loc]
instance Deep JSFam JSPrim (Maybe (Id Loc))
instance Deep JSFam JSPrim (Id Loc)
instance Deep JSFam JSPrim (ForInInit Loc)
instance Deep JSFam JSPrim (ForInit Loc)
instance Deep JSFam JSPrim (Maybe (Expression Loc))
instance Deep JSFam JSPrim (Maybe (CatchClause Loc))
instance Deep JSFam JSPrim (Maybe (Statement Loc))
instance Deep JSFam JSPrim [VarDecl Loc]
instance Deep JSFam JSPrim [Id Loc]
instance Deep JSFam JSPrim [Expression Loc]
instance Deep JSFam JSPrim [(Prop Loc, Expression Loc)]
instance Deep JSFam JSPrim (LValue Loc)
instance Deep JSFam JSPrim (Prop Loc, Expression Loc)
instance Deep JSFam JSPrim (Prop Loc)
instance Deep JSFam JSPrim (CaseClause Loc)
instance Deep JSFam JSPrim (VarDecl Loc)
instance Deep JSFam JSPrim (CatchClause Loc)


  , (JavaScript Loc)
  , [Statement Loc]
  , (Statement Loc)
  , (Expression Loc)
  , [CaseClause Loc]
  , (Maybe (Id Loc))
  , (Id Loc)
  , (ForInInit Loc)
  , (ForInit Loc)
  , (Maybe (Expression Loc))
  , (Maybe (CatchClause Loc))
  , (Maybe (Statement Loc))
  , [VarDecl Loc]
  , [Id Loc]
  , [Expression Loc]
  , [(Prop Loc, Expression Loc)]
  , (LValue Loc)
  , (Prop Loc, Expression Loc)
  , (Prop Loc)
  , (CaseClause Loc)
  , (VarDecl Loc)
  , (CatchClause Loc)

-}
