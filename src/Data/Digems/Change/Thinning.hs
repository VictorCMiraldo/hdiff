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
module Data.Digems.Change.Thinning where

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
import Data.Exists
import Data.Digems.MetaVar
import Data.Digems.Change
import Data.Digems.Change.Apply
import Generics.MRSOP.Digems.Treefix

import Debug.Trace

-- |A 'Domain' is just a deletion context. Type-synonym helps us
-- identify what's what on the algorithms below.
type Domain ki codes = UTx ki codes (MetaVarIK ki) 

domain :: CChange ki codes at -> Domain ki codes at
domain = cCtxDel

type ThinningErr ki codes = ApplicationErr ki codes (MetaVarIK ki)

-- Haskell tends to want a type-signature for some non-trivial lifts. 
lift' :: (Monad m) => m a -> StateT (Subst ki codes (MetaVarIK ki)) m a
lift' = lift

thin :: (ShowHO ki , TestEquality ki, EqHO ki)
     => CChange ki codes at
     -> Domain ki codes at
     -> Either (ApplicationErr ki codes (MetaVarIK ki)) (CChange ki codes at)
thin c@(CMatch _ del ins) dom =

-- |The @thin' p q@ function is where work where we produce the
--  map that will be applied to 'p' in order to thin it.
--  This function does /NOT/ minimize this map.
-- 
thin' :: (ShowHO ki , TestEquality ki, EqHO ki)
      => UTx ki codes (MetaVarIK ki) at
      -> Domain ki codes at
      -> StateT (Subst ki codes (MetaVarIK ki))
                (Except (ThinningErr ki codes))
                ()
thin' p q = void $ utxMapM (uncurry' go) $ utxLCP p q
  where
    go :: (ShowHO ki , TestEquality ki, EqHO ki)
       => UTx ki codes (MetaVarIK ki) at
       -> Domain ki codes at
       -> StateT (Subst ki codes (MetaVarIK ki))
                 (Except (ThinningErr ki codes))
                 (UTx ki codes (MetaVarIK ki) at)
    go p@(UTxHole var) q = do
      sigma <- get
      mterm <- lift (lookupVar var sigma)
      case mterm of
        -- First time we see 'var', we instantiate it and get going.
        Nothing ->
          if p /= q
          then modify (M.insert (metavarGet var) (Exists q)) >> return p
          else return p
        -- It's not the first time we thin 'var'; previously, we had
        -- that 'var' was supposed to be p'. We will check whether it
        -- is the same as q, if not, we will have to thin p' with q.
        Just p' | eqHO p' q -> return p
                | otherwise -> thin' p' q >> return p'
    go p q = throwError (IncompatibleTerms p q)

-- |The minimization step performs the 'occurs' check and removes
--  unecessary steps. For example;
--
--  > sigma = fromList
--  >           [ (0 , bin 1 2)
--  >           , (1 , bin 4 4) ]
--
-- Then, @minimize sigma@ will return @fromList [(0 , bin (bin 4 4) 2)]@
--
minimize :: forall ki codes
          . (ShowHO ki, EqHO ki , TestEquality ki)
         => Subst ki codes (MetaVarIK ki)
         -> Except (ThinningErr ki codes) (Subst ki codes (MetaVarIK ki))
minimize sigma = whileM sigma [] $ \s exs
  -> let s' = trace (show exs) $ foldr M.delete s exs
      in M.fromList <$> (mapM (secondF (exMapM go)) (M.toList s'))
  where
    secondF :: (Functor m) => (a -> m b) -> (x , a) -> m (x , b)
    secondF f (x , a) = (x,) <$> f a

    go :: UTx ki codes (MetaVarIK ki) at
       -> WriterT [Int] (Except (ThinningErr ki codes))
                                (UTx ki codes (MetaVarIK ki) at)
    go = utxRefineVarsM $ \var -> do
           mterm <- lift (lookupVar var sigma)
           case mterm of
             Nothing -> return (UTxHole var)
             Just r  -> tell [metavarGet var]
                     >> return r

whileM :: (Monad m, Show x) => a -> [x] -> (a -> [x] -> WriterT [x] m a) -> m a
whileM a xs f = runWriterT (f a xs)
            >>= \(x' , xs') -> if null xs'
                               then return x'
                               else whileM x' xs' f
