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
module Data.Digems.Change.Specialize where


import           Data.Proxy
import           Data.Type.Equality
import           Data.Functor.Const
import qualified Data.Map as M
import           Control.Monad.Except
---------------------------------------
import Generics.MRSOP.Util
import Generics.MRSOP.Base
---------------------------------------
import Data.Exists
import Data.Digems.MetaVar
import Data.Digems.Change
import Data.Digems.Change.Apply
import Generics.MRSOP.Digems.Treefix


type Domain ki codes = UTx ki codes (MetaVarIK ki) 

domain :: CChange ki codes at -> Domain ki codes at
domain = cCtxDel

specialize :: (Show1 ki , TestEquality ki, Eq1 ki)
           => CChange ki codes at
           -> Domain ki codes at
           -> Either (ApplicationErr ki codes (MetaVarIK ki)) (CChange ki codes at)
specialize c@(CMatch _ del ins) dom = runExcept $ do
  let vMax = cMaxVar c
  subst <- pmatchRelax del dom 
  let subst' = M.map (exMap $ utxMap (metavarAdd vMax)) subst
  del' <- transport del subst'
  ins' <- transport ins subst'
  return $ cmatch del' ins'

-- TODO: unit pmatchRelax with pmatch
  
-- |This is just like 'Data.Digems.Change.Apply.pmatch' except it does NOT
-- throw 'IncompatibleOpq' nor 'IncompatibleHole' errors.
pmatchRelax :: (Applicable ki codes phi)
            => UTx ki codes (MetaVarIK ki) ix
            -> UTx ki codes phi ix
            -> Except (ApplicationErr ki codes phi) (Subst ki codes phi)
pmatchRelax pat = go M.empty pat
  where
    go :: (Applicable ki codes phi)
       => Subst ki codes phi
       -> UTx ki codes (MetaVarIK ki) ix
       -> UTx ki codes phi ix
       -> Except (ApplicationErr ki codes phi) (Subst ki codes phi)
    go s (UTxHole var) x         = substInsert s var x
    go s pa (UTxHole var)        = return s
    go s (UTxOpq oa) (UTxOpq ox) = return s
    go s pa@(UTxPeel ca ppa) x@(UTxPeel cx px) =
      case testEquality ca cx of
        Nothing   -> throwError (IncompatibleTerms pa x)
        Just Refl -> getConst <$>
          cataNPM (\y (Const val) -> fmap Const (uncurry' (go val) y))
                  (return $ Const s)
                  (zipNP ppa px)

