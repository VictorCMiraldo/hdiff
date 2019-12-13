{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE GADTs                 #-}
module Data.HDiff.Base.Apply where

import Control.Monad.Except
------------------------------------
import Generics.MRSOP.Util
import Generics.MRSOP.Base
import Generics.MRSOP.Holes
------------------------------------
import Generics.MRSOP.HDiff.Holes.Unify
import Data.HDiff.Base

patchApply :: (EqHO ki)
           => Patch ki codes at
           -> NA ki (Fix ki codes) at
           -> Maybe (NA ki (Fix ki codes) at)
patchApply p = chgApply (chgDistr p) 

chgApply :: (EqHO ki)
         => Chg ki codes at
         -> NA ki (Fix ki codes) at
         -> Maybe (NA ki (Fix ki codes) at)
chgApply chg p = 
  case runExcept $ unify (chgDel chg) (na2holes p) of
    Left  _     -> Nothing
    Right sigma -> holes2naM (const Nothing) $ substApply sigma (chgIns chg)
