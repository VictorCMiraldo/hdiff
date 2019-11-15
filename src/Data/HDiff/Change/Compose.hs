{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE GADTs                 #-}
module Data.HDiff.Change.Compose where

import Data.Type.Equality
import Control.Monad.Except
import qualified Data.Map as M
-------------------------------
import Generics.MRSOP.Util
import Generics.MRSOP.Base
-------------------------------
import Data.HDiff.Change
import Data.HDiff.Change.Thinning


{-
-- TODO: boil this up to mrsop
holesExecStM :: (Monad m)
             => (forall ix . s -> phi ix -> m s)
             -> s
             -> Holes ki codes phi at
             -> m s
holesExecStM f s0 (Hole _ phi)  = f s0 phi
holesExecStM _ s0 (HOpq _ _)    = return s0
holesExecStM f s0 (HPeel _ _ p) 
  = getConst <$> cataNPM (\y (Const val) -> fmap Const $ holesExecStM f val y)
                         (return $ Const s0)
                         p

-}

-- |Running @q `after` p@ will yield a patch, when possible, that
-- changes elements in the domain of @p@ into elements in the
-- codomain of @q@.
--
-- This is just another application of 'thin'. 
--
-- PRECONDITION: Names must be disjoint in both changes; we call thin
--               directly, without checking this.
--
after :: (HasDatatypeInfo ki fam codes , ShowHO ki , EqHO ki , TestEquality ki)
      => CChange ki codes at
      -> CChange ki codes at
      -> Either (ThinningErr ki codes) (CChange ki codes at)
after q p = uncurry' cmatch <$> after' (cCtxDel q :*: cCtxIns q)
                                       (cCtxDel p :*: cCtxIns p)

after' :: (HasDatatypeInfo ki fam codes , ShowHO ki , EqHO ki , TestEquality ki)
       => Holes2 ki codes at
       -> Holes2 ki codes at
       -> Either (ThinningErr ki codes) (Holes2 ki codes at)
after' q (pD :*: pI) = do
  (di , sigma) <- runExcept $ thinHoles2st q pI M.empty
  let _ :*: i' = di
  pD' <- runExcept $ refine pD sigma
  return $ pD' :*: i'
