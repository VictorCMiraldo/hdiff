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
module Generics.MRSOP.Digems.Instantiate where

import Data.Proxy
import Data.Type.Equality
import Data.Functor.Const
import qualified Data.Map as M
import qualified Data.Set as S
import Control.Monad
import Control.Monad.Writer
import Control.Monad.Except
import Control.Monad.State
import Control.Arrow (first, second)

import Data.Digems.Diff.MetaVar
import Data.Digems.Diff.Patch hiding (apply)

import Generics.MRSOP.Util
import Generics.MRSOP.Base
import Generics.MRSOP.Digems.Treefix

import Debug.Trace

data UnificationErr :: (kon -> *) -> [[[Atom kon]]] -> (Atom kon -> *) -> * where
  UndefinedVar      :: Int -> UnificationErr ki codes phi
  IncompatibleTerms :: String -> Term ki codes ix -> UTx ki codes phi ix
                    -> UnificationErr ki codes phi
  IncompatibleTypes :: UnificationErr ki codes phi

{-
instance (Show1 ki) => Show (UnificationErr ki codes) where
  showsPrec n (UndefinedVar v)
    = showParen (n > 0) $ shows "UndefinedVar "
                        . shows v
  showsPrec n (IncompatibleTerms t u)
    = showParen (n > 0) $ shows "IncompatibleTerms "
                        . shows (show1 t)
                        . shows " "
                        . shows (show1 u)
  showsPrec n IncompatibleTypes
    = shows "IncompatibleTypes"
-}
instance Show (UnificationErr ki codes phi) where
  show (UndefinedVar i)          = "(UndefinedVar " ++ show i ++ ")"
  show (IncompatibleTerms n _ _) = "IncompatibleTerms " ++ n
  show (IncompatibleTypes)       = "IncompatibleTypes"

data UTxE :: (kon -> *) -> [[[Atom kon]]] -> (Atom kon -> *) -> * where
  UTxE :: UTx ki codes f at -> UTxE ki codes f

instance (Show1 ki) => Show (UTxE ki codes (MetaVarIK ki)) where
  show (UTxE utx) = show1 utx

utxe :: (forall at . UTx ki codes f at -> UTx ki codes f at)
     -> UTxE ki codes f -> UTxE ki codes f
utxe f (UTxE x) = UTxE (f x)

type Subst ki codes phi = M.Map Int (UTxE ki codes phi)
type Term  ki codes     = UTx ki codes (MetaVarIK ki)

type UnifyM ki codes phi = StateT (Subst ki codes phi)
                                  (Except (UnificationErr ki codes phi))

type Unifiable ki codes phi = (Show1 ki , Eq1 ki , TestEquality ki , TestEquality phi
                              , HasIKProjInj ki phi)

-- |We try to unify @pa@ and @pq@ onto @ea@. The idea is that
--  we instantiate the variables of @pa@ with their corresponding expression
--  on @x@, and substitute those in @ea@. Whereas if we reach a variable in @x@
--  we ignore whatever was on @ea@ and give that variable instead.
--
--  We are essentially applying 
utxTransport :: (Unifiable ki codes phi)
             => CChange ki codes ix
             -> UTx ki codes phi ix
             -> Either (UnificationErr ki codes phi) (UTx ki codes phi ix)
utxTransport chg x
  = runExcept $ evalStateT (pmatch (cCtxDel chg) x >> transport1 (cCtxIns chg)) M.empty

{-
  = let x' = uniquenessNaming pa x
        maxX' = varmax x'
     in runExcept $ evalStateT (pmatch pa x >> dbg >> transport1 ea) (maxX' , M.empty)
  where
    varmax :: Term ki codes ix -> Int
    varmax = (1+) . maybe 0 id . S.lookupMax . utxGetHolesWith metavarGet
    
    uniquenessNaming :: Term ki codes iy -> Term ki codes ix -> Term ki codes ix
    uniquenessNaming x = utxRefine (UTxHole . metavarAdd (varmax x)) UTxOpq
-}

-- |@pmatch pa x@ traverses @pa@ and @x@ instantiating the variables of @pa@.
pmatch :: (Unifiable ki codes phi)
       => Term ki codes ix
       -> UTx ki codes phi ix
       -> UnifyM ki codes phi ()
pmatch (UTxHole var) x  = modify (M.insert (metavarGet var) (UTxE x))
pmatch pa (UTxHole var) = return ()
pmatch pa@(UTxOpq oa) x@(UTxOpq ox)
  | eq1 oa ox = return ()
  | otherwise = throwError (IncompatibleTerms (show1 oa ++ ";" ++ show1 ox) pa x)
pmatch pa@(UTxPeel ca ppa) x@(UTxPeel cx px) =
  case testEquality ca cx of
    Nothing   -> throwError (IncompatibleTerms "2" pa x)
    Just Refl -> void $ elimNPM (uncurry' pmatch) (zipNP ppa px)

-- |Instantiates the metavariables in the given term
-- using the substitution in the state
transport1 :: (Unifiable ki codes phi)
           => Term ki codes ix
           -> UnifyM ki codes phi (UTx ki codes phi ix)
transport1 (UTxHole var)     = lookupVar var
                           >>= maybe (throwError $ UndefinedVar $ metavarGet var)
                                     return
transport1 (UTxOpq oy)       = return $ UTxOpq oy
transport1 y@(UTxPeel cy py) = UTxPeel cy <$> mapNPM transport1 py

-- |Looks for the value of a @MetaVarIK ki ix@ in the substitution
-- in our state. Returns @Nothing@ when the variables is not found
-- or throws 'IncompatibleTypes' when the value registered in the
-- substitution is of type @iy@ with @ix /= iy@.
lookupVar :: forall ki codes phi ix
           . (Unifiable ki codes phi)
          => MetaVarIK ki ix
          -> UnifyM ki codes phi (Maybe (UTx ki codes phi ix))
lookupVar var = do
  substs <- get
  case M.lookup (metavarGet var) substs of
    Nothing -> return Nothing
    Just r  -> Just <$> cast r
  where
    idxCheck :: forall at . UTx ki codes phi at
             -> MetaVarIK ki ix
             -> Maybe (at :~: ix)
    idxCheck utx (NA_K (Annotate _ k)) = testEquality utx (konInj k)
    idxCheck utx i@(NA_I _)
      = case varProj (Proxy :: Proxy ki) utx of
          Nothing      -> Nothing
          Just prf@IsI -> apply (Refl :: I :~: I)
                      <$> testEquality (getIsISNat prf) (getSNatI i)
    
    getSNatI :: MetaVarIK ki (I i) -> SNat i
    getSNatI (NA_I _) = getSNat (Proxy :: Proxy i)
 
    cast :: UTxE ki codes phi
         -> UnifyM ki codes phi (UTx ki codes phi ix)
    cast (UTxE res) = case idxCheck res var of -- (UTxHole var) of
      Nothing   -> throwError IncompatibleTypes
      Just Refl -> return res

{-
unifyPure :: (Unifiable ki codes phi)
          => Term ki codes ix
          -> Term ki codes ix
          -> Except (UnificationErr ki codes) (Subst ki codes)
unifyPure x y = go M.empty x y
  where
    attemptBind :: (Unifiable ki codes phi)
      => Subst ki codes
      -> Int
      -> UTxE ki codes (MetaVarIK ki)
      -> Except (UnificationErr ki codes) (Subst ki codes) 
    attemptBind s var new = case M.lookup var s of
      Nothing -> return $ M.insert var new s
      Just rs -> error "what?"
    
    go :: (Unifiable ki codes phi)
        => Subst ki codes
        -> Term ki codes ix
        -> Term ki codes ix
        -> Except (UnificationErr ki codes) (Subst ki codes)
    go m (UTxHole var) x  = attemptBind m (metavarGet var) (UTxE x)
    go m pa (UTxHole var) = attemptBind m (metavarGet var) (UTxE pa)
    go m pa@(UTxOpq oa) x@(UTxOpq ox)
      | eq1 oa ox = return $ M.empty
      | otherwise = throwError (IncompatibleTerms (show1 oa ++ ";" ++ show1 ox) pa x)
    go m pa@(UTxPeel ca ppa) x@(UTxPeel cx px) =
      case testEquality ca cx of
        Nothing   -> throwError (IncompatibleTerms "2" pa x)
        Just Refl -> getConst <$> cataNPM (\(x :*: y) cm -> Const <$> go (getConst cm) x y)
                                          (return (Const m))
                                          (zipNP ppa px)
-}
