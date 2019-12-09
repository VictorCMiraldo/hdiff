{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE GADTs                 #-}
module Data.HDiff.Base.Apply where


import           Control.Monad.Except
import           Data.Functor.Sum
import           Data.Functor.Const
import           Data.Type.Equality
import qualified Data.Map as M
import qualified Data.Set as S
------------------------------------
import Generics.MRSOP.Util
import Generics.MRSOP.Base
import Generics.MRSOP.Holes
------------------------------------
import Generics.MRSOP.HDiff.Holes
import Generics.MRSOP.HDiff.Holes.Unify
import Data.Exists
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
    Right sigma -> holes2naM (holes2naM (const Nothing) <.> substLkup sigma)
                             (chgIns chg)
