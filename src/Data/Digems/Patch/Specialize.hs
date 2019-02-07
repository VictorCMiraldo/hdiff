{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE PolyKinds        #-}
{-# LANGUAGE GADTs            #-}
module Data.Digems.Patch.Specialize where

import           Control.Monad.State
import           Control.Monad.Except
import           Data.Type.Equality
import qualified Data.Set as S
import qualified Data.Map as M
------------------------------------
import Generics.MRSOP.Util
import Generics.MRSOP.Base
------------------------------------
import Data.Exists
import Generics.MRSOP.Digems.Treefix
import qualified Data.WordTrie as T
import Data.Digems.MetaVar
import Data.Digems.Patch
import Data.Digems.Patch.Diff
import Data.Digems.Change
import Data.Digems.Change.Classify
import Data.Digems.Change.Apply

