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

type ThinningErr kappa fam = UnifyErr kappa fam (MetaVar kappa fam)

thin :: Patch  kappa fam at
     -> Domain kappa fam at
     -> Except (ThinningErr kappa fam) (Patch kappa fam at)
thin p d = chgPatch <$> chgThin (chgDistr p) d

chgThin :: Chg  kappa fam at
        -> Domain kappa fam at
        -> Except (ThinningErr kappa fam) (Chg kappa fam at)
chgThin (Chg del ins) dom = do
  sigma <- unify del dom
  return $ Chg (substApply sigma del) (substApply sigma ins)

