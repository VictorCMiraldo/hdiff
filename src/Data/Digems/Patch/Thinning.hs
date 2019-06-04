{-# LANGUAGE FlexibleContexts      #-}
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
module Data.Digems.Patch.Thinning where

import           Data.Proxy
import           Data.Type.Equality
import           Data.Functor.Const
import qualified Data.Map as M
import           Control.Monad.Writer
import           Control.Monad.Except
import           Control.Monad.State
---------------------------------------
import Generics.MRSOP.Util
import Generics.MRSOP.Base
---------------------------------------
import           Data.Exists
import           Data.Digems.MetaVar
import           Data.Digems.Patch
import           Data.Digems.Change
import qualified Data.Digems.Change.Thinning as CT
import           Generics.MRSOP.Digems.Treefix

thin :: (ShowHO ki , TestEquality ki, EqHO ki)
     => RawPatch ki codes at
     -> RawPatch ki codes at
     -> Either (CT.ThinningErr ki codes) (RawPatch ki codes at)
thin p q = utxMapM (uncurry' go) $ utxLCP p q
  where
    go cp cq = let cp' = distrCChange cp
                   cq' = distrCChange cq `withDisjNamesFrom` cp'
                in CT.thin cp' (domain cq')
