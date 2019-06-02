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

-- |A 'ScopeInfo' will keep track of the current scope stack, the
--  current scope id together with a 'fresh' scope id for newly defined
--  scopes.
data ScopeInfo = ScopeInfo
  { stack :: [(ScopeId , S.Set String)]
  , fresh :: ScopeId
  } deriving (Eq , Show)

pushEmptyScope :: ScopeInfo -> ScopeInfo
pushEmptyScope (ScopeInfo st f)
  = ScopeInfo ((f , S.empty) : st) (f + 1)

popScope :: ScopeInfo -> ScopeInfo
popScope (ScopeInfo []     _) = error "no scope to pop"
popScope (ScopeInfo (_:st) f) = ScopeInfo st f

registerName :: String -> ScopeInfo -> ScopeInfo
registerName x s@(ScopeInfo [] _) = registerName x (pushEmptyScope s)
registerName x (ScopeInfo ((sid , xs):st) f)
  = ScopeInfo ((sid , S.insert x xs) : st) f

lookupName :: String -> ScopeInfo -> Maybe ScopeId
lookupName name = asum . map aux . stack
  where
    aux (sid , s) = if name `S.member` s then Just sid else Nothing
    
-- |Simple implementation of MonadScope, using a 'ScopeInfo' in a state monad.
type Scope = State ScopeInfo

instance MonadScope Scope where
  currScope = do
    st <- gets stack
    return $ case st of
      []       -> (0 , S.empty)
      (sids:_) -> sids
  
  onFresh p     = modify pushEmptyScope *> p <* modify popScope

  declName      = modify . registerName

  lkupName name = lookupName name <$> get
    
runScope :: Scope a -> a
runScope = flip evalState (ScopeInfo [] 0)


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
