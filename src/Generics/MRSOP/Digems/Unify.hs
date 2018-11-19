{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}
module Generics.MRSOP.Digems.Unify where

import Data.Type.Equality
import qualified Data.Map as M
import Control.Monad
import Control.Monad.Writer
import Control.Monad.Except
import Control.Monad.State


import Data.Digems.Diff.MetaVar

import Generics.MRSOP.Util
import Generics.MRSOP.Base
import Generics.MRSOP.Digems.Treefix

data UnificationErr
  = OccursCheck
  | IncompatibleTerms
  | IncompatibleTypes
  deriving (Eq , Show)

data UTxE :: (kon -> *) -> [[[Atom kon]]] -> (Atom kon -> *) -> * where
  UTxE :: UTx ki codes f at -> UTxE ki codes f

utxe :: (forall at . UTx ki codes f at -> UTx ki codes f at)
     -> UTxE ki codes f -> UTxE ki codes f
utxe f (UTxE x) = UTxE (f x)

type Subst ki codes = M.Map Int (UTxE ki codes (MetaVarIK ki))
type Term  ki codes = UTx ki codes (MetaVarIK ki)

type UnifyM ki codes = StateT (Subst ki codes)
                              (Except UnificationErr)

type Unifiable ki codes = (Show1 ki , Eq1 ki , TestEquality ki)

utxUnify :: (Unifiable ki codes)
         => Term ki codes ix
         -> Term ki codes ix
         -> Either UnificationErr (Subst ki codes)
utxUnify x y = runExcept $ execStateT (unify x y) M.empty

unify :: (Unifiable ki codes)
      => Term ki codes ix
      -> Term ki codes ix
      -> UnifyM ki codes ()
unify (UTxHole var) y = unifyVar var y
unify x (UTxHole var) = unifyVar var x
unify (UTxOpq ox) (UTxOpq oy)
  | eq1 ox oy = return ()
  | otherwise = throwError IncompatibleTerms
unify (UTxPeel cx px) (UTxPeel cy py) =
  case testEquality cx cy of
    Nothing   -> throwError IncompatibleTerms
    Just Refl -> void $ elimNPM (uncurry' unify) (zipNP px py)

lookupVar :: forall ki codes ix
           . (Unifiable ki codes)
          => MetaVarIK ki ix
          -> Subst ki codes
          -> Maybe (Either UnificationErr (Term ki codes ix))
lookupVar var = fmap cast . M.lookup (metavarGet var)
  where
    cast :: UTxE ki codes (MetaVarIK ki)
         -> Either UnificationErr (Term ki codes ix)
    cast (UTxE res) = case testEquality res (UTxHole var) of
      Nothing   -> Left IncompatibleTypes
      Just Refl -> Right res

replace :: (Unifiable ki codes)
        => MetaVarIK ki ix
        -> Term ki codes ix
        -> Term ki codes iy
        -> Term ki codes iy
replace var x = utxRefine (go x var) UTxOpq
  where
    go :: (Unifiable ki codes)
       => Term ki codes ix
       -> MetaVarIK ki ix
       -> MetaVarIK ki iy
       -> UTx ki codes (MetaVarIK ki) iy
    go x var v = case testEquality var v of
      Nothing   -> UTxHole v
      Just Refl -> if metavarGet v == metavarGet var
                   then x
                   else UTxHole v
  
unifyVar :: forall ki codes ix
          . (Unifiable ki codes)
         => MetaVarIK ki ix
         -> Term ki codes ix
         -> UnifyM ki codes ()
unifyVar var x = get
             >>= maybe notThere (either throwError isThere)
               . lookupVar var
  where
    notThere :: UnifyM ki codes ()
    notThere = if occursCheck var x
               then throwError OccursCheck
               else modify ( M.insert (metavarGet var) (UTxE x)
                           . fmap (utxe $ replace var x))

    isThere :: UTx ki codes (MetaVarIK ki) ix -> UnifyM ki codes ()
    isThere utx = unify utx x


occursCheck :: MetaVarIK ki ix
            -> Term ki codes ix
            -> Bool
occursCheck var = maybe True (const False)
                . utxRefineM (\x -> guard (metavarGet x /= metavarGet var)
                                 >> return (UTxHole x))
                             (return . UTxOpq)
    
