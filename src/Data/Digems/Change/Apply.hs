{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}
-- |Defines the application function for a 'Data.Digems.Change.CChange'
module Data.Digems.Change.Apply where

import           Data.Proxy
import           Data.Type.Equality
import           Data.Functor.Const
import qualified Data.Map as M
import           Control.Monad.Except

import Data.Exists
import Data.Digems.MetaVar
import Data.Digems.Change

import Generics.MRSOP.Util
import Generics.MRSOP.Base
import Generics.MRSOP.Digems.Treefix

-- * Generic Application
--
-- $genapply
--
-- A 'CChange' can be applied to any treefix by pattern matching
-- over the deletion context and instantiating over the insertion context.

-- |Application might fail with some 'ApplicationErr' describing
-- the point of failure.
data ApplicationErr :: (kon -> *) -> [[[Atom kon]]] -> (Atom kon -> *) -> * where
  UndefinedVar      :: Int -> ApplicationErr ki codes phi
  FailedContraction :: Int
                    -> UTx ki codes phi ix
                    -> UTx ki codes phi ix
                    -> ApplicationErr ki codes phi
  IncompatibleTypes :: ApplicationErr ki codes phi
  IncompatibleOpqs  :: ki k
                    -> ki k
                    -> ApplicationErr ki codes phi
  IncompatibleHole  :: UTx ki codes (MetaVarIK ki) ix
                    -> phi ix
                    -> ApplicationErr ki codes phi
  IncompatibleTerms :: UTx ki codes (MetaVarIK ki) ix
                    -> UTx ki codes phi ix
                    -> ApplicationErr ki codes phi

instance Show (ApplicationErr ki codes phi) where
  show (UndefinedVar i)          = "(UndefinedVar " ++ show i ++ ")"
  show (FailedContraction i _ _) = "(FailedContraction " ++ show i ++ ")"
  show (IncompatibleTerms _ _)   = "IncompatibleTerms"
  show (IncompatibleOpqs _ _)    = "IncompatibleOpq"
  show (IncompatibleHole _ _)    = "IncompatibleHole"
  show (IncompatibleTypes)       = "IncompatibleTypes"

-- |A substitution from metavariable numbers to some treefix
type Subst ki codes phi = M.Map Int (Exists (UTx ki codes phi))

type Applicable ki codes phi = (Show1 ki , Eq1 ki , TestEquality ki , TestEquality phi
                              , HasIKProjInj ki phi , Eq1 phi)

-- |We try to unify @pa@ and @pq@ onto @ea@. The idea is that
--  we instantiate the variables of @pa@ with their corresponding expression
--  on @x@, and substitute those in @ea@. Whereas if we reach a variable in @x@
--  we ignore whatever was on @ea@ and give that variable instead.
--
--  We are essentially applying 
genericApply :: (Applicable ki codes phi)
             => CChange ki codes at
             -> UTx ki codes phi at
             -> Either (ApplicationErr ki codes phi) (UTx ki codes phi at)
genericApply chg x = runExcept (pmatch (cCtxDel chg) x >>= transport (cCtxIns chg))

-- |Specializes 'genericApply' to work over terms of our language, ie, 'NA's
termApply :: forall ki codes at
           . (Show1 ki , Eq1 ki , TestEquality ki)
          => CChange ki codes at
          -> NA ki (Fix ki codes) at
          -> Either String (NA ki (Fix ki codes) at)
termApply chg = either (Left . show) (utxUnstiffM cast)
              . genericApply chg
              . utxStiff 
  where
    -- cast is used only to fool the compiler here! Since the
    -- UTx comes from 'utxStiff', it has no occurence of 'UTxHole'
    -- and hence genericApply will return a term with no such
    -- occurence. Yet, it requires a Eq1 instance for phi, so
    -- we provide one
    cast :: MetaVarIK ki ix
         -> Either String (NA ki (Fix ki codes) ix)
    cast _ = Left "Data.Digems.Change.Apply: impossible"


-- |@pmatch pa x@ traverses @pa@ and @x@ instantiating the variables of @pa@.
-- Upon sucessfully instantiating the variables, returns the substitution.
pmatch :: (Applicable ki codes phi)
       => UTx ki codes (MetaVarIK ki) ix
       -> UTx ki codes phi ix
       -> Except (ApplicationErr ki codes phi) (Subst ki codes phi)
pmatch pat = go M.empty pat
  where
    go :: (Applicable ki codes phi)
       => Subst ki codes phi
       -> UTx ki codes (MetaVarIK ki) ix
       -> UTx ki codes phi ix
       -> Except (ApplicationErr ki codes phi) (Subst ki codes phi)
    go s (UTxHole var) x  = substInsert s var x
    go s pa (UTxHole var)
      -- When we are trying to match a pattern @pa@ against a hole
      -- we must make some occurs check over this pattern and make
      -- sure @pa@ does not bind any variable. Otherwise, we'll
      -- end up with an 'UndefinedVariable' in the transport phase.
      | utxArity pa == 0 = return s
      | otherwise        = throwError (IncompatibleHole pa var)
    go s (UTxOpq oa) (UTxOpq ox)
      | eq1 oa ox = return s
      | otherwise = throwError (IncompatibleOpqs oa ox)
    go s pa@(UTxPeel ca ppa) x@(UTxPeel cx px) =
      case testEquality ca cx of
        Nothing   -> throwError (IncompatibleTerms pa x)
        Just Refl -> getConst <$>
          cataNPM (\y (Const val) -> fmap Const (uncurry' (go val) y))
                  (return $ Const s)
                  (zipNP ppa px)

-- |Given a 'MetaVarIK' and a 'UTx', decide whether their indexes
-- are equal.
idxDecEq :: forall ki codes phi at ix
          . (TestEquality ki , TestEquality phi, HasIKProjInj ki phi)
         => UTx ki codes phi at
         -> MetaVarIK ki ix
         -> Maybe (at :~: ix)
idxDecEq utx (NA_K (Annotate _ k)) = testEquality utx (konInj k)
idxDecEq utx i@(NA_I _)
  = case varProj (Proxy :: Proxy ki) utx of
      Nothing      -> Nothing
      Just prf@IsI -> apply (Refl :: 'I :~: 'I)
                  <$> testEquality (getIsISNat prf) (getSNatI i)
  where
    getSNatI :: MetaVarIK ki ('I i) -> SNat i
    getSNatI (NA_I _) = getSNat (Proxy :: Proxy i)

-- |Attempts to insert a new binding into a substitution. If the variable is already
-- bound, we check the existing binding for equality
substInsert :: (Applicable ki codees phi)
            => Subst ki codes phi
            -> MetaVarIK ki ix
            -> UTx ki codes phi ix
            -> Except (ApplicationErr ki codes phi) (Subst ki codes phi)
substInsert s var new = case M.lookup (metavarGet var) s of
  Nothing           -> return $ M.insert (metavarGet var) (Exists new) s
  Just (Exists old) -> case testEquality old new of
    Nothing   -> throwError IncompatibleTypes
    Just Refl -> if old == new
                 then return s
                 else throwError (FailedContraction (metavarGet var) old new)

-- |Instantiates the metavariables in the given term
-- using the substitution in the state
transport :: (Applicable ki codes phi)
          => UTx ki codes (MetaVarIK ki) ix
          -> Subst ki codes phi
          -> Except (ApplicationErr ki codes phi) (UTx ki codes phi ix)
transport (UTxHole var)   s = lookupVar var s
                          >>= maybe (throwError $ UndefinedVar $ metavarGet var)
                                      return
transport (UTxOpq oy)     _ = return $ UTxOpq oy
transport (UTxPeel cy py) s = UTxPeel cy <$> mapNPM (flip transport s) py

-- |Looks for the value of a @MetaVarIK ki ix@ in the substitution
-- in our state. Returns @Nothing@ when the variables is not found
-- or throws 'IncompatibleTypes' when the value registered in the
-- substitution is of type @iy@ with @ix /= iy@.
lookupVar :: forall ki codes phi ix
           . (Applicable ki codes phi)
          => MetaVarIK ki ix
          -> Subst ki codes phi
          -> Except (ApplicationErr ki codes phi) (Maybe (UTx ki codes phi ix))
lookupVar var subst = do
  case M.lookup (metavarGet var) subst of
    Nothing -> return Nothing
    Just r  -> Just <$> cast r
  where
    cast :: Exists (UTx ki codes phi)
         -> Except (ApplicationErr ki codes phi) (UTx ki codes phi ix)
    cast (Exists res) = case idxDecEq res var of
      Nothing   -> throwError IncompatibleTypes
      Just Refl -> return res

