{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE BangPatterns #-}
-- | Taken from
-- https://github.com/nazrhom/vcs-clojure/blob/master/src/Language/Clojure/Syntax.hs
module Languages.Clojure.Syntax where

import Data.Text

data SepExprList =
   Nil 
 | Cons Expr !Sep SepExprList
 deriving (Eq , Show)

data Sep = Space | Comma | NewLine | EmptySep deriving (Show, Eq)

data Expr = Special !FormTy Expr 
          | Dispatch Expr 
          | Collection !CollTy SepExprList 
          | Term Term 
          | Comment !Text 
          | Seq Expr Expr 
          | Empty 
          deriving (Eq, Show)
-- ref: https://8thlight.com/blog/colin-jones/2012/05/22/quoting-without-confusion.html

data FormTy = Quote | SQuote | UnQuote | DeRef | Meta deriving (Show, Eq)

data CollTy = Vec | Set | Parens deriving (Show, Eq)

data Term = TaggedString !Tag !Text 
  deriving (Eq , Show)

data Tag = String | Var  deriving (Show, Eq)

data SubTree = Exp Expr | Sel SepExprList
  deriving (Eq , Show)

{-
collectSubTrees :: Expr -> Int -> [SubTree]
collectSubTrees e i = mbTakeExpr e i

collectSubTreesSel :: SepExprList -> Int -> [SubTree]
collectSubTreesSel (Nil lr) i = []
collectSubTreesSel (Cons e _ sel _) i = collectSubTreesExpr e i ++ mbTakeSel sel i

mbTakeExpr :: Expr -> Int -> [SubTree]
mbTakeExpr e i = if (takeStart $ extractRangeExpr e) == i
  then (Exp e):collectSubTreesExpr e i
  else collectSubTreesExpr e i

mbTakeSel :: SepExprList -> Int -> [SubTree]
mbTakeSel sel@(Cons _ _ _ lr) i = if (takeStart lr) == i
  then (Sel sel):collectSubTreesSel sel i
  else collectSubTreesSel sel i
mbTakeSel sel i = collectSubTreesSel sel i

collectSubTreesExpr :: Expr -> Int -> [SubTree]
collectSubTreesExpr (Collection _ sel _) i = mbTakeSel sel i
collectSubTreesExpr (Seq e1 e2 _) i = collectSubTreesExpr e1 i ++ collectSubTrees e2 i
collectSubTreesExpr (Special _ e _) i = collectSubTreesExpr e i
collectSubTreesExpr (Dispatch e _) i = collectSubTreesExpr e i
collectSubTreesExpr _ i = []

data ConflictResult a = NoConflict | ConflictAt a
  deriving (Show, Eq)
-}

