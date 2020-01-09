{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Generics.Simplistic.Example where

import GHC.Generics
import Generics.Simplistic
import Generics.Simplistic.Util
import Generics.Simplistic.Digest
import Generics.Simplistic.Unify

import Data.HDiff.Diff
import Data.HDiff.Diff.Preprocess

data Exp
  = Add Exp Exp
  | Pow Exp Exp
  | Sqrt Exp
  | Let [Decl] Exp
  | Var String
  | Lit Double
  deriving (Eq , Show , Generic)

data Decl
  = Decl String Exp
  deriving (Eq , Show , Generic)

type Prims = '[ String , Double ]

instance Deep Prims Exp
instance Deep Prims [Decl]
instance Deep Prims Decl

pyth :: Exp
pyth = Let [Decl "hypSq" (Add (Pow (Var "x") (Lit 2)) (Pow (Var "y") (Lit 2)))]
           (Sqrt (Var "hypSq"))

ex1 , ex2 :: Exp
ex1 = (Add (Var "x") (Var "y"))
ex2 = (Add ex1 ex1)

dfromPrim :: (Deep Prims a) => a -> SFix Prims a
dfromPrim = dfrom


a = dfromPrim ex1
b = dfromPrim ex2
