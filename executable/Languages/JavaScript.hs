{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE StandaloneDeriving    #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeSynonymInstances  #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE DataKinds             #-}
{-# OPTIONS_GHC -Wno-orphans       #-}
module Languages.JavaScript where

#ifdef REAL_LANGUAGES

import Language.ECMAScript3.Syntax
import Language.ECMAScript3.Parser
import Text.Parsec.Pos

import Control.Monad.Except

import GHC.Generics
import Generics.Simplistic
import Generics.Simplistic.Deep
import Generics.Simplistic.Deep.TH

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

deriveDeepFor ''JSPrim ''JSFam
--
-- instance Deep JSPrim JSFam ()
-- instance Deep JSPrim JSFam InfixOp
-- instance Deep JSPrim JSFam AssignOp
-- instance Deep JSPrim JSFam PrefixOp
-- instance Deep JSPrim JSFam UnaryAssignOp
--
-- instance Deep JSPrim JSFam (JavaScript ())
-- instance Deep JSPrim JSFam [Statement ()]
-- instance Deep JSPrim JSFam (Statement ())
-- instance Deep JSPrim JSFam (Expression ())
-- instance Deep JSPrim JSFam [CaseClause ()]
-- instance Deep JSPrim JSFam (Maybe (Id ()))
-- instance Deep JSPrim JSFam (Id ())
-- instance Deep JSPrim JSFam (ForInInit ())
-- instance Deep JSPrim JSFam (ForInit ())
-- instance Deep JSPrim JSFam (Maybe (Expression ()))
-- instance Deep JSPrim JSFam (Maybe (CatchClause ()))
-- instance Deep JSPrim JSFam (Maybe (Statement ()))
-- instance Deep JSPrim JSFam [VarDecl ()]
-- instance Deep JSPrim JSFam [Id ()]
-- instance Deep JSPrim JSFam [Expression ()]
-- instance Deep JSPrim JSFam [(Prop (), Expression ())]
-- instance Deep JSPrim JSFam (LValue ())
-- instance Deep JSPrim JSFam (Prop (), Expression ())
-- instance Deep JSPrim JSFam (Prop ())
-- instance Deep JSPrim JSFam (CaseClause ())
-- instance Deep JSPrim JSFam (VarDecl ())
-- instance Deep JSPrim JSFam (CatchClause ())
--

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
dfromJS' :: JavaScript Loc -> SFix JSPrim JSFam (JavaScript ())
dfromJS' = dfrom . fmap (const ())


{-

dfromJS :: JavaScript Loc -> SFix JSPrim JSFam (JavaScript Loc)
dfromJS = dfrom

instance Deep JSPrim JSFam Loc

instance Deep JSPrim JSFam (JavaScript Loc)
instance Deep JSPrim JSFam [Statement Loc]
instance Deep JSPrim JSFam (Statement Loc)
instance Deep JSPrim JSFam (Expression Loc)
instance Deep JSPrim JSFam [CaseClause Loc]
instance Deep JSPrim JSFam (Maybe (Id Loc))
instance Deep JSPrim JSFam (Id Loc)
instance Deep JSPrim JSFam (ForInInit Loc)
instance Deep JSPrim JSFam (ForInit Loc)
instance Deep JSPrim JSFam (Maybe (Expression Loc))
instance Deep JSPrim JSFam (Maybe (CatchClause Loc))
instance Deep JSPrim JSFam (Maybe (Statement Loc))
instance Deep JSPrim JSFam [VarDecl Loc]
instance Deep JSPrim JSFam [Id Loc]
instance Deep JSPrim JSFam [Expression Loc]
instance Deep JSPrim JSFam [(Prop Loc, Expression Loc)]
instance Deep JSPrim JSFam (LValue Loc)
instance Deep JSPrim JSFam (Prop Loc, Expression Loc)
instance Deep JSPrim JSFam (Prop Loc)
instance Deep JSPrim JSFam (CaseClause Loc)
instance Deep JSPrim JSFam (VarDecl Loc)
instance Deep JSPrim JSFam (CatchClause Loc)


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

#endif
