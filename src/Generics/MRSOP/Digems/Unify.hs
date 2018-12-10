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
module Generics.MRSOP.Digems.Unify where

import Data.Type.Equality
import Data.Functor.Const
import qualified Data.Map as M
import qualified Data.Set as S
import Control.Monad
import Control.Monad.Writer
import Control.Monad.Except
import Control.Monad.State

import Data.Digems.Diff.MetaVar

import Generics.MRSOP.Util
import Generics.MRSOP.Base
import Generics.MRSOP.Digems.Treefix

import Debug.Trace

data UnificationErr :: (kon -> *) -> [[[Atom kon]]] -> * where
  UndefinedVar      :: Int -> UnificationErr ki codes
  IncompatibleTerms :: String -> Term ki codes ix -> Term ki codes ix -> UnificationErr ki codes
  IncompatibleTypes :: UnificationErr ki codes

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
instance Show (UnificationErr ki codes) where
  show (UndefinedVar i) = "(UndefinedVar " ++ show i ++ ")"
  show (IncompatibleTerms n _ _) = "IncompatibleTerms " ++ n
  show (IncompatibleTypes)     = "IncompatibleTypes"

data UTxE :: (kon -> *) -> [[[Atom kon]]] -> (Atom kon -> *) -> * where
  UTxE :: UTx ki codes f at -> UTxE ki codes f

instance (Show1 ki) => Show (UTxE ki codes (MetaVarIK ki)) where
  show (UTxE utx) = show1 utx

utxe :: (forall at . UTx ki codes f at -> UTx ki codes f at)
     -> UTxE ki codes f -> UTxE ki codes f
utxe f (UTxE x) = UTxE (f x)

type Subst ki codes = M.Map Int (UTxE ki codes (MetaVarIK ki))
type Term  ki codes = UTx ki codes (MetaVarIK ki)

type UnifyM ki codes = StateT (Subst ki codes)
                              (Except (UnificationErr ki codes))

type Unifiable ki codes = (Show1 ki , Eq1 ki , TestEquality ki)

-- |We try to unify @pa@ and @pq@ onto @ea@. The idea is that
--  we instantiate the variables of @pa@ with their corresponding expression
--  on @x@, and substitute those in @ea@. Whereas if we reach a variable in @x@
--  we ignore whatever was on @ea@ and give that variable instead.
--
--  We are essentially applying 
utxUnify :: (Unifiable ki codes)
         => Term ki codes ix
         -> Term ki codes ix
         -> Term ki codes ix
         -> Either (UnificationErr ki codes) (Term ki codes ix)
utxUnify pa ea x   
  = let x' = uniquenessNaming pa x
     in runExcept $ evalStateT (pmatch pa x >> dbg >> transport ea) M.empty
  where
    uniquenessNaming :: Term ki codes iy -> Term ki codes ix -> Term ki codes ix
    uniquenessNaming x = let varsx  = utxGetHolesWith metavarGet x
                             varmax = (1+) . maybe 0 id $ S.lookupMax varsx
                          in utxRefine (UTxHole . metavarAdd varmax) UTxOpq

dbg :: (Unifiable ki codes)
    => UnifyM ki code ()
dbg = return () -- get >>= \m -> trace (show m) (return ())

-- |@pmatch pa x@ traverses @pa@ and @x@ instantiating the variables of @pa@.
pmatch :: (Unifiable ki codes)
       => Term ki codes ix
       -> Term ki codes ix
       -> UnifyM ki codes ()
pmatch (UTxHole var) x  = modify (M.insert (metavarGet var) (UTxE x))
pmatch pa (UTxHole var)
  | utxArity pa == 0 = return () -- modify (M.insert (metavarGet var) (UTxE pa)) 
  -- if pa still has variables, this is a problem. Because their occurence
  -- in ea will be undefined... why not carry a map from 'Utx' to var saying
  -- that we shall abstract pa by 'var'?
  | otherwise        = return () -- throwError (IncompatibleTerms "4" pa (UTxHole var))
pmatch pa@(UTxOpq oa) x@(UTxOpq ox)
  | eq1 oa ox = return ()
  | otherwise = throwError (IncompatibleTerms (show1 oa ++ ";" ++ show1 ox) pa x)
pmatch pa@(UTxPeel ca ppa) x@(UTxPeel cx px) =
  case testEquality ca cx of
    Nothing   -> throwError (IncompatibleTerms "2" pa x)
    Just Refl -> void $ elimNPM (uncurry' pmatch) (zipNP ppa px)

{-
-- |The second step is @transport x ea@, where we substitue the variables
--  in @ea@ for the values they were instantiated for in @pa@,
--  but using the variables in @x@ to take precedence.
transport :: (Unifiable ki codes)
       => Term ki codes ix
       -> Term ki codes ix
       -> UnifyM ki codes (Term ki codes ix)
transport x (UTxHole var) = lookupVar var
                     -- >>= return . maybe x id
                        >>= maybe (throwError $ UndefinedVar $ metavarGet var) return
transport (UTxHole var) y = return (UTxHole var)
transport _ (UTxOpq oy)   = return $ UTxOpq oy
transport x@(UTxPeel cx px) y@(UTxPeel cy py) =
  case testEquality cx cy of
    Nothing   -> throwError (IncompatibleTerms "3" x y)
    Just Refl -> UTxPeel cy <$> mapNPM (uncurry' transport) (zipNP px py)
-}
-- |The second step is @transport x ea@, where we substitue the variables
--  in @ea@ for the values they were instantiated for in @pa@,
--  but using the variables in @x@ to take precedence.
transport :: (Unifiable ki codes)
       => Term ki codes ix
       -> UnifyM ki codes (Term ki codes ix)
transport (UTxHole var) = lookupVar var
                     -- >>= return . maybe x id
                     >>= maybe (throwError $ UndefinedVar $ metavarGet var) return
transport (UTxOpq oy)   = return $ UTxOpq oy
transport y@(UTxPeel cy py) =
  UTxPeel cy <$> mapNPM transport py

lookupVar :: forall ki codes ix
           . (Unifiable ki codes)
          => MetaVarIK ki ix
          -> UnifyM ki codes (Maybe (Term ki codes ix))
lookupVar var = do
  substs <- get
  case M.lookup (metavarGet var) substs of
    Nothing -> return Nothing
    Just r  -> Just <$> cast r
  where
    cast :: UTxE ki codes (MetaVarIK ki)
         -> UnifyM ki codes (Term ki codes ix)
    cast (UTxE res) = case testEquality res (UTxHole var) of
      Nothing   -> throwError IncompatibleTypes
      Just Refl -> return res

{-
unifyPure :: (Unifiable ki codes)
          => Term ki codes ix
          -> Term ki codes ix
          -> Except (UnificationErr ki codes) (Subst ki codes)
unifyPure x y = go M.empty x y
  where
    attemptBind :: (Unifiable ki codes)
      => Subst ki codes
      -> Int
      -> UTxE ki codes (MetaVarIK ki)
      -> Except (UnificationErr ki codes) (Subst ki codes) 
    attemptBind s var new = case M.lookup var s of
      Nothing -> return $ M.insert var new s
      Just rs -> error "what?"
    
    go :: (Unifiable ki codes)
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
