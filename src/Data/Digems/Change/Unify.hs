{-# LANGUAGE FlexibleContexts #-}
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
-- |Defines the unification function for two 'Data.Digems.Change.CChange'
module Data.Digems.Change.Unify where

import           Data.Proxy
import           Data.Type.Equality
import           Data.Functor.Const
import qualified Data.Map as M
import qualified Data.Set as S
import           Control.Monad.Except

import Data.Exists
import Data.Digems.MetaVar
import Data.Digems.Change
import Data.Digems.Change.Apply hiding (transport)

import Generics.MRSOP.Util
import Generics.MRSOP.Base
import Generics.MRSOP.Digems.Treefix

-- |A unification substitution from metavariable numbers to some treefix.
type USubst ki codes = Subst ki codes (MetaVarIK ki)


unify :: (Applicable ki codes (MetaVarIK ki))
      => CChange ki codes at
      -> CChange ki codes at
      -> Either (ApplicationErr ki codes (MetaVarIK ki))
                (Maybe (CChange ki codes at
                       ,CChange ki codes at))
unify (CMatch vp delp insp) (CMatch vq delq insq) = runExcept $ do
  -- First we guarantee that there will be no name clashing
  let maxVar = (+1) $ maybe 0 id $ S.lookupMax $ S.map (exElim metavarGet) vp
  let delq'  = utxMap (metavarAdd maxVar) delq
  let insq'  = utxMap (metavarAdd maxVar) insq
  -- Now we run the unification. We can skip occurs check because the variables
  -- sets are disjoint.
  u <- umatch M.empty delp delq'
  resd  <- utransport delp  u
  resip <- utransport insp  u
  resiq <- utransport insq' u
  return $ (,) <$> cmatch' resd resip <*> cmatch' resd resiq
 where
   isLeft  = either (const True) (const False)
   isRight = not . isLeft

-- |Very similar to 'pmatch', but this is tailored to
-- unification.
umatch :: (Applicable ki codes (MetaVarIK ki))
   => USubst ki codes
   -> UTx ki codes (MetaVarIK ki) ix
   -> UTx ki codes (MetaVarIK ki) ix
   -> Except (ApplicationErr ki codes (MetaVarIK ki)) (USubst ki codes)
umatch s (UTxHole var) x  = substInsert s var x
umatch s pa (UTxHole var) = substInsert s var pa
umatch s (UTxOpq oa) (UTxOpq ox)
  | eqHO oa ox = return s
  | otherwise = throwError (IncompatibleOpqs oa ox)
umatch s pa@(UTxPeel ca ppa) x@(UTxPeel cx px) =
  case testEquality ca cx of
    Nothing   -> throwError (IncompatibleTerms pa x)
    Just Refl -> getConst <$>
      cataNPM (\y (Const val) -> fmap Const (uncurry' (umatch val) y))
              (return $ Const s)
              (zipNP ppa px)

-- |Similar to 'transport', but does not throw errors on undefined vars
utransport :: (Applicable ki codes (MetaVarIK ki))
           => UTx ki codes (MetaVarIK ki) ix
           -> Subst ki codes (MetaVarIK ki)
           -> Except (ApplicationErr ki codes (MetaVarIK ki))
                     (UTx ki codes (MetaVarIK ki) ix)
utransport (UTxHole var)   s = lookupVar var s
                           >>= maybe (return $ UTxHole var) return
utransport (UTxOpq oy)     _ = return $ UTxOpq oy
utransport (UTxPeel cy py) s = UTxPeel cy <$> mapNPM (flip utransport s) py

