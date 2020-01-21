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
import qualified Data.Set as S
import Control.Monad.Writer hiding (Sum)

import Data.HDiff.Base
import Data.HDiff.MetaVar

import Generics.Simplistic
import Generics.Simplistic.Util

data ChgVars fam prim x
  = ChgVars { decls :: S.Set Int
            , uses  :: S.Set Int
            , body  :: Chg fam prim x
            }

isClosed :: ChgVars fam prim x -> Bool
isClosed (ChgVars d u _) = d == u

chgVarsDistr :: Holes fam prim (ChgVars fam prim) at
             -> ChgVars fam prim at
chgVarsDistr h =
  let (hD , ds) = runWriter $ holesMapM (\(ChgVars d _ c) -> tell d >> return (chgDel c)) h
      (hI , us) = runWriter $ holesMapM (\(ChgVars _ u c) -> tell u >> return (chgIns c)) h
   in ChgVars ds us (Chg (holesJoin hD) (holesJoin hI))

close :: Holes fam prim (Chg fam prim) at
      -> Maybe (Holes fam prim (Chg fam prim) at)
close h = case closure (holesMap getVars h) of
            InL _ -> Nothing
            InR b -> Just (holesMap body b)
  where
    getVars :: Chg fam prim x -> ChgVars fam prim x
    getVars c@(Chg d i) =
      let varsD = S.fromList . map (exElim metavarGet) $ holesHolesList d
          varsI = S.fromList . map (exElim metavarGet) $ holesHolesList i
       in ChgVars varsD varsI c


closure :: Holes fam prim (ChgVars fam prim) at
        -> Sum (ChgVars fam prim) (Holes fam prim (ChgVars fam prim)) at 
closure (Prim x)  = InR $ Prim x
closure (Hole cv)
  | isClosed cv = InR $ Hole cv
  | otherwise   = InL cv
closure (Roll x) =
  let aux = repMap closure x
   in case repMapM fromInR aux of
        Just res -> InR $ Roll res
        Nothing  ->
          -- Distributing closed changes yields closed changes;
          let chgs = repMap (either' InL (InR . chgVarsDistr)) aux
              cD   = Roll $ repMap (codelta (chgDel . body)) chgs
              cI   = Roll $ repMap (codelta (chgIns . body)) chgs
              dels = repLeaves (codelta decls) S.union S.empty chgs
              inss = repLeaves (codelta uses)  S.union S.empty chgs
           in if dels == inss
              then InR (Hole $ ChgVars dels dels (Chg cD cI))
              else InL (ChgVars dels inss (Chg cD cI))
 where
  codelta :: (f x -> r) -> Sum f f x -> r
  codelta f (InL c) = f c
  codelta f (InR c) = f c
   
  fromInR :: Sum f g x -> Maybe (g x)
  fromInR (InL _) = Nothing
  fromInR (InR c) = Just c
