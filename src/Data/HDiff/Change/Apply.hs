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
-- |Defines the application function for a 'Data.HDiff.Change.CChange'
module Data.HDiff.Change.Apply where

import           Data.Proxy
import           Data.Type.Equality
import           Data.Functor.Const
import qualified Data.Map as M
import           Control.Monad.Except

import Data.Exists
import Data.HDiff.MetaVar
import Data.HDiff.Change

import Generics.MRSOP.Util
import Generics.MRSOP.Base
import Generics.MRSOP.Holes
import Generics.MRSOP.HDiff.Holes

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
                    -> Holes ki codes phi ix
                    -> Holes ki codes phi ix
                    -> ApplicationErr ki codes phi
  IncompatibleTypes :: ApplicationErr ki codes phi
  IncompatibleOpqs  :: ki k
                    -> ki k
                    -> ApplicationErr ki codes phi
  IncompatibleHole  :: Holes ki codes (MetaVarIK ki) ix
                    -> phi ix
                    -> ApplicationErr ki codes phi
  IncompatibleTerms :: Holes ki codes (MetaVarIK ki) ix
                    -> Holes ki codes phi ix
                    -> ApplicationErr ki codes phi

instance Show (ApplicationErr ki codes phi) where
  show (UndefinedVar i)          = "(UndefinedVar " ++ show i ++ ")"
  show (FailedContraction i _ _) = "(FailedContraction " ++ show i ++ ")"
  show (IncompatibleTerms _ _)   = "IncompatibleTerms"
  show (IncompatibleOpqs _ _)    = "IncompatibleOpq"
  show (IncompatibleHole _ _)    = "IncompatibleHole"
  show (IncompatibleTypes)       = "IncompatibleTypes"

-- |A instantiation substitution from metavariable numbers to some treefix
type Subst ki codes phi = M.Map Int (Exists (Holes ki codes phi))

type Applicable ki codes phi = (TestEquality ki , TestEquality phi , HasIKProjInj ki phi )

-- |We try to unify @pa@ and @pq@ onto @ea@. The idea is that
--  we instantiate the variables of @pa@ with their corresponding expression
--  on @x@, and substitute those in @ea@. Whereas if we reach a variable in @x@
--  we ignore whatever was on @ea@ and give that variable instead.
--
--  We are essentially applying 
genericApply :: (Applicable ki codes phi , EqHO phi , EqHO ki)
             => CChange ki codes at
             -> Holes ki codes phi at
             -> Either (ApplicationErr ki codes phi) (Holes ki codes phi at)
genericApply chg x = runExcept (pmatch (cCtxDel chg) x >>= transport (cCtxIns chg))

-- |Specializes 'genericApply' to work over terms of our language, ie, 'NA's
termApply :: forall ki codes at
           . (ShowHO ki , EqHO ki , TestEquality ki)
          => CChange ki codes at
          -> NA ki (Fix ki codes) at
          -> Either String (NA ki (Fix ki codes) at)
termApply chg = either (Left . show) (holes2naM cast)
              . genericApply chg
              . na2holes 
  where
    -- cast is used only to fool the compiler here! Since the
    -- Holes comes from 'utxStiff', it has no occurence of 'HolesHole'
    -- and hence genericApply will return a term with no such
    -- occurence. Yet, it requires a EqHO instance for phi, so
    -- we provide one
    cast :: MetaVarIK ki ix
         -> Either String (NA ki (Fix ki codes) ix)
    cast _ = Left "Data.HDiff.Change.Apply: impossible"


-- |@pmatch pa x@ traverses @pa@ and @x@ instantiating the variables of @pa@.
-- Upon sucessfully instantiating the variables, returns the substitution.
pmatch :: (Applicable ki codes phi , EqHO phi , EqHO ki)
       => Holes ki codes (MetaVarIK ki) ix
       -> Holes ki codes phi ix
       -> Except (ApplicationErr ki codes phi) (Subst ki codes phi)
pmatch pat = pmatch' M.empty (\_ _ _ -> Nothing) pat

-- |A more general version of pattern matching which enables finer control.
-- Here we thread a substitution through the function and only throw
-- 'IncompatibleHole' when a given condition is met.
pmatch' :: (Applicable ki codes phi , EqHO phi , EqHO ki)
   => Subst ki codes phi
   -> (forall iy . Holes ki codes (MetaVarIK ki) iy
                -> phi iy
                -> Subst ki codes phi
                -> Maybe (Subst ki codes phi)) -- ^ When this returns @Nothing@ a call to
                                               --   'pmatch'' will fail with 'IncompatibleHole
   -> Holes ki codes (MetaVarIK ki) ix
   -> Holes ki codes phi ix
   -> Except (ApplicationErr ki codes phi) (Subst ki codes phi)
pmatch' s _ (Hole _ var) x  = substInsert s var x
pmatch' s c pa (Hole _ var)
  = maybe (throwError $ IncompatibleHole pa var) return $ c pa var s
pmatch' s _ (HOpq _ oa) (HOpq _ ox)
  | eqHO oa ox  = return s
  | otherwise = throwError (IncompatibleOpqs oa ox)
pmatch' s c pa@(HPeel _ ca ppa) x@(HPeel _ cx px) =
  case testEquality ca cx of
    Nothing   -> throwError (IncompatibleTerms pa x)
    Just Refl -> getConst <$>
      cataNPM (\y (Const val) -> fmap Const (uncurry' (pmatch' val c) y))
              (return $ Const s)
              (zipNP ppa px)

-- |Given a 'MetaVarIK' and a 'Holes', decide whether their indexes
-- are equal.
idxDecEq :: forall ki codes phi at ix
          . (TestEquality ki , TestEquality phi, HasIKProjInj ki phi)
         => Holes ki codes phi at
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
substInsert :: (Applicable ki codes phi , EqHO ki , EqHO phi)
            => Subst ki codes phi
            -> MetaVarIK ki ix
            -> Holes ki codes phi ix
            -> Except (ApplicationErr ki codes phi) (Subst ki codes phi)
substInsert s var new = case M.lookup (metavarGet var) s of
  Nothing           -> return $ M.insert (metavarGet var) (Exists new) s
  Just (Exists old) -> case testEquality old new of
    Nothing   -> throwError IncompatibleTypes
    Just Refl -> if eqHO old new
                 then return s
                 else throwError (FailedContraction (metavarGet var) old new)

-- |Instantiates the metavariables in the given term
-- using the substitution in the state
transport :: (Applicable ki codes phi)
          => Holes ki codes (MetaVarIK ki) ix
          -> Subst ki codes phi
          -> Except (ApplicationErr ki codes phi) (Holes ki codes phi ix)
transport (Hole _ var)   s = lookupVar var s
                          >>= maybe (throwError $ UndefinedVar $ metavarGet var)
                                      return
transport (HOpq _ oy)     _ = return $ HOpq' oy
transport (HPeel _ cy py) s = HPeel' cy <$> mapNPM (flip transport s) py

-- |Looks for the value of a @MetaVarIK ki ix@ in the substitution
-- in our state. Returns @Nothing@ when the variables is not found
-- or throws 'IncompatibleTypes' when the value registered in the
-- substitution is of type @iy@ with @ix /= iy@.
lookupVar :: forall ki codes phi ix
           . (Applicable ki codes phi)
          => MetaVarIK ki ix
          -> Subst ki codes phi
          -> Except (ApplicationErr ki codes phi) (Maybe (Holes ki codes phi ix))
lookupVar var subst = do
  case M.lookup (metavarGet var) subst of
    Nothing -> return Nothing
    Just r  -> Just <$> cast r
  where
    cast :: Exists (Holes ki codes phi)
         -> Except (ApplicationErr ki codes phi) (Holes ki codes phi ix)
    cast (Exists res) = case idxDecEq res var of
      Nothing   -> throwError IncompatibleTypes
      Just Refl -> return res

