{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE GADTs                 #-}
module Data.HDiff.Diff.Closure where

import Data.Functor.Sum
import qualified Data.Map as M
import Control.Monad.Writer hiding (Sum)

import Data.Monoid hiding (Sum)
import Data.HDiff.Base
import Data.HDiff.MetaVar

import Generics.Simplistic
import Generics.Simplistic.Util

data ChgVars kappa fam x
  = ChgVars { decls :: M.Map Int Arity
            , uses  :: M.Map Int Arity
            , body  :: Chg kappa fam x
            }

isClosed :: M.Map Int Arity
         -> M.Map Int Arity
         -> M.Map Int Arity
         -> Bool
isClosed global ds us = M.unionWith (+) ds us `M.isSubmapOf` global

newtype MM = MM (M.Map Int Arity)
instance Semigroup MM where
  MM x <> MM y = MM (M.unionWith (+) x y)
instance Monoid MM where
  mempty = MM M.empty

chgVarsDistr :: Holes kappa fam (ChgVars kappa fam) at
             -> ChgVars kappa fam at
chgVarsDistr h =
  let (hD , MM ds) = runWriter $ holesMapM (\(ChgVars d _ c) -> tell (MM d) >> return (chgDel c)) h
      (hI , MM us) = runWriter $ holesMapM (\(ChgVars _ u c) -> tell (MM u) >> return (chgIns c)) h
   in ChgVars ds us (Chg (holesJoin hD) (holesJoin hI))

close :: Holes kappa fam (Chg kappa fam) at
      -> Maybe (Holes kappa fam (Chg kappa fam) at)
close h = case closure global (holesMap getVars h) of
            InL _ -> Nothing
            InR b -> Just (holesMap body b)
  where
    global = patchVars h

    f lbl m = unlines $ [ lbl ++ " " ++ show k ++ ": " ++ show v | (k , v) <- M.toList m]
    
    getVars :: Chg kappa fam x -> ChgVars kappa fam x
    getVars c@(Chg d i) =
      let varsD = holesVars d
          varsI = holesVars i
       in ChgVars varsD varsI c

closure :: M.Map Int Arity
        -> Holes kappa fam (ChgVars kappa fam) at
        -> Sum (ChgVars kappa fam) (Holes kappa fam (ChgVars kappa fam)) at 
closure _  (Prim x)  = InR $ Prim x
closure gl (Hole cv)
  | isClosed gl (decls cv) (uses cv) = InR $ Hole cv
  | otherwise   = InL cv
closure gl (Roll x) =
  let aux = repMap (closure gl) x
   in case repMapM fromInR aux of
        Just res -> InR $ Roll res
        Nothing  ->
          -- Distributing closed changes yields closed changes;
          let chgs = repMap (either' id chgVarsDistr) aux
              cD   = Roll $ repMap (chgDel . body) chgs
              cI   = Roll $ repMap (chgIns . body) chgs
              dels = repLeaves decls (M.unionWith (+)) M.empty chgs
              inss = repLeaves uses  (M.unionWith (+)) M.empty chgs
           in if isClosed gl dels inss
              then InR (Hole $ ChgVars dels inss (Chg cD cI))
              else InL (ChgVars dels inss (Chg cD cI))
 where
  fromInR :: Sum f g x -> Maybe (g x)
  fromInR (InL _) = Nothing
  fromInR (InR c) = Just c
