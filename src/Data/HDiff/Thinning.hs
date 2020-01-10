{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE GADTs                 #-}
module Data.HDiff.Thinning where

import Control.Monad.Except
-------------------------------
import Generics.Simplistic.Unify
-------------------------------
import Data.HDiff.MetaVar
import Data.HDiff.Base

type ThinningErr prim = UnifyErr prim MetaVar

thin :: Patch  prim at
     -> Domain prim at
     -> Except (ThinningErr prim) (Patch prim at)
thin p d = chgPatch <$> chgThin (chgDistr p) d

chgThin :: Chg  prim at
        -> Domain prim at
        -> Except (ThinningErr prim) (Chg prim at)
chgThin (Chg del ins) dom = do
  sigma <- unify del dom
  return $ Chg (substApply sigma del) (substApply sigma ins)

