{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Generics.MRSOP.Digems.Scoped where

import Data.Proxy
import Data.Functor.Const
import qualified Data.Set as S

import Data.Foldable (asum)
import Control.Applicative
import Control.Monad.State
import Control.Monad.Reader

import Generics.MRSOP.Base
import Generics.MRSOP.AG (AnnFix(..) , synthesize)

type ScopeId = Int

-- |Interface needed for registering names under scopes
class Monad m => MonadScope m where
  -- |Runs a computation under a new scope.
  onFresh   :: m a -> m a

  -- |Registers a name equivalence under the current scope.
  declName  :: String -> m ()

  -- |Looks a name up, returns the scope of the declaration
  lkupName  :: String -> m (Maybe ScopeId)

  -- |What is the identifier of the current scope?
  currScope :: m (ScopeId , S.Set String)

-----------------------------

-- Simple implementation of MonadScope
type Scope = State [(Int , S.Set String)]

instance MonadScope Scope where
  currScope = do
    st <- get
    return $ case st of
      []       -> (0 , S.empty)
      (sids:_) -> sids
  
  onFresh p = do
    (sid , _) <- currScope
    modify ((sid + 1 , S.empty) :)
    res <- p
    modify tail
    return res

  declName name = do
    st <- get
    case st of
      []             -> put [(0 , S.singleton name)]
      ((sid , s):ss) -> put ((sid , S.insert name s):ss)

  lkupName name = asum . map lkup0 <$> get
    where lkup0 (sid , s) = if name `S.member` s
                            then Just sid
                            else Nothing
    
runScope :: Scope a -> a
runScope = flip evalState []


-------------------------
-- Scope information coupled to a family


type ScopedFix ki codes = AnnFix ki codes (Const (Maybe ScopeId))

scopeFix :: (IsNat ix , Scoped ki codes , MonadScope m)
         => Fix ki codes ix
         -> m (ScopedFix ki codes ix)
scopeFix x = do
  (sid , Tag c p) <- scope (fixSNat x) (sop $ unFix x)
  return $ AnnFix (Const $ sid) (inj c p)
 where fixSNat :: (IsNat ix) => Fix ki codes ix -> SNat ix
       fixSNat _ = getSNat Proxy

class Scoped ki codes where
  scope     :: (MonadScope m)
            => SNat iy
            -> View ki (Fix ki codes) (Lkup iy codes)
            -> m (Maybe ScopeId , View ki (ScopedFix ki codes)
                                          (Lkup iy codes))

defaultScope :: (MonadScope m , Scoped ki codes)
             => SNat iy
             -> View ki (Fix ki codes) (Lkup iy codes)
             -> m (Maybe ScopeId , View ki (ScopedFix ki codes)
                                          (Lkup iy codes))
defaultScope _ (Tag c p)
  = (,) Nothing . Tag c <$> mapNPM (mapNAM return scopeFix) p

instance {-# OVERLAPPABLE #-} Scoped ki codes where
   scope = defaultScope
{-
instance Scoped ki WhileCodes where
  process (While cond stmt) = do
    cond' <- process cond
    pushScope
    stmt' <- process stmt
    return $ AnnFix (NotAName , While cond' stmt')

  process (Var i) = do
    return $ AnnFix (lkupScope i , Var i)
-}
