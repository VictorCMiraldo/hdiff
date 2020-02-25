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

-- |Enable us to annotate a change with the
-- variables it declares in its deletion context
-- and the variables it uses in its insertion context.
data WithVars f x
  = WithVars { decls :: M.Map Int Arity
             , uses  :: M.Map Int Arity
             , body  :: f x
             }

-- |Convenient synonym.
type ChgVars kappa fam = WithVars (Chg kappa fam)

-- |Given a map @global@, accounting for global variable occurences,
-- a 'WithVars' is closed with respect to @global@ whenever
-- the sum of occurences of variables in the 'WithVars'
-- matches that of the same variables globally.
isClosed :: M.Map Int Arity -> WithVars f x -> Bool
isClosed global (WithVars ds us _) = M.unionWith (+) ds us `M.isSubmapOf` global

-- |Distributing a 'ChgVars' can be tricky. We must
-- not forget to compute the multiset union of the arity maps.
chgVarsDistr :: Holes kappa fam (ChgVars kappa fam) at
             -> ChgVars kappa fam at
chgVarsDistr h = 
  let (hD , ds) = runWriter $ holesMapM (\(WithVars d _ c) -> tell [d] >> return (chgDel c)) h
      (hI , us) = runWriter $ holesMapM (\(WithVars _ u c) -> tell [u] >> return (chgIns c)) h
      d'        = M.unionsWith (+) ds
      u'        = M.unionsWith (+) us
   in WithVars d' u' (Chg (holesJoin hD) (holesJoin hI))

close :: Chg kappa fam at
      -> Holes kappa fam (Chg kappa fam) at
close c =
  let gl = chgVars c
   in case closure gl (holesMap withVars (lgg (chgDel c) (chgIns c))) of
        InL _ -> error "inv-failure: c was not well-scoped"
        InR r -> holesMap body r
 where
   withVars :: (HolesMV kappa fam :*: HolesMV kappa fam) at
            -> ChgVars kappa fam at
   withVars (d :*: i) = WithVars (holesVars d) (holesVars i) (Chg d i)
                
closure :: M.Map Int Arity
        -> Holes kappa fam (ChgVars kappa fam) at
        -> Sum (ChgVars kappa fam) (Holes kappa fam (ChgVars kappa fam)) at 
closure _  (Prim x)  = InR $ Prim x
closure gl (Hole cv)
  | isClosed gl cv = InR $ Hole cv
  | otherwise      = InL cv
closure gl (Roll x) =
  let aux = repMap (closure gl) x
   in case repMapM fromInR aux of
        Just res -> InR $ Roll res
        Nothing  -> let res = chgVarsDistr $ Roll $ repMap (either' Hole  id) aux
                     in if isClosed gl res then InR (Hole res) else InL res
 where
  fromInR :: Sum f g x -> Maybe (g x)
  fromInR (InL _) = Nothing
  fromInR (InR c) = Just c
