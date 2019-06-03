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

type ThinningErr ki codes = ApplicationErr ki codes (MetaVarIK ki)

-- Haskell tends to want a type-signature for some non-trivial lifts. 
lift' :: (Monad m) => m a -> StateT (Subst ki codes (MetaVarIK ki)) m a
lift' = lift

thin :: (ShowHO ki , TestEquality ki, EqHO ki)
     => CChange ki codes at
     -> Domain ki codes at
     -> Either (ApplicationErr ki codes (MetaVarIK ki)) (CChange ki codes at)
thin c@(CMatch _ del ins) dom = runExcept $ do
  sigma  <- flip execStateT M.empty $ utxThin del dom
  sigma' <- minimize sigma
  del'   <- refine del sigma
  ins'   <- refine ins sigma
  return $ cmatch del' ins'

-- |The @thin' p q@ function is where work where we produce the
--  map that will be applied to 'p' in order to thin it.
--  This function does /NOT/ minimize this map.
-- 
utxThin :: (ShowHO ki , TestEquality ki, EqHO ki)
        => UTx ki codes (MetaVarIK ki) at
        -> Domain ki codes at
        -> StateT (Subst ki codes (MetaVarIK ki))
                  (Except (ThinningErr ki codes))
                  ()
utxThin p q = void $ utxMapM (uncurry' go) $ utxLCP p q
  where
    go :: (ShowHO ki , TestEquality ki, EqHO ki)
       => UTx ki codes (MetaVarIK ki) at
       -> Domain ki codes at
       -> StateT (Subst ki codes (MetaVarIK ki))
                 (Except (ThinningErr ki codes))
                 (UTx ki codes (MetaVarIK ki) at)
    go p (UTxHole _) = return p
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
                | otherwise -> utxThin p' q >> return p'
    go p q | eqHO p q  = return p
           | otherwise = trace (showHO p ++ "\n$$$\n" ++ showHO q) $ throwError (IncompatibleTerms p q)

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
  -> M.fromList <$> (mapM (secondF (exMapM go)) (M.toList s))
  where
    secondF :: (Functor m) => (a -> m b) -> (x , a) -> m (x , b)
    secondF f (x , a) = (x,) <$> f a

    -- The actual engine of the 'minimize' function is thinning the
    -- variables that appear in the image of the substitution under production.
    -- We use the writer monad to inform us wich variables have been fully
    -- eliminated. Once this process returns no eliminated variables,
    -- we are done.
    go :: UTx ki codes (MetaVarIK ki) at
       -> WriterT [Int] (Except (ThinningErr ki codes))
                                (UTx ki codes (MetaVarIK ki) at)
    go = utxRefineVarsM $ \var -> do
           mterm <- lift (lookupVar var sigma)
           case mterm of
             Nothing -> return (UTxHole var)
             Just r  -> tell [metavarGet var]
                     >> return r

    whileM :: (Monad m, Show x)
           => a -> [x] -> (a -> [x] -> WriterT [x] m a) -> m a
    whileM a xs f = runWriterT (f a xs)
                >>= \(x' , xs') -> if null xs'
                                   then return x'
                                   else whileM x' xs' f


-- |This is similar to 'transport', but does not throw errors
-- on undefined variables.
refine :: (ShowHO ki , TestEquality ki , EqHO ki)
       => UTx ki codes (MetaVarIK ki) ix
       -> Subst ki codes (MetaVarIK ki)
       -> Except (ThinningErr ki codes) (UTx ki codes (MetaVarIK ki) ix)
refine (UTxHole var)   s = lookupVar var s >>= return . maybe (UTxHole var) id
refine (UTxOpq oy)     _ = return $ UTxOpq oy
refine (UTxPeel cy py) s = UTxPeel cy <$> mapNPM (flip refine s) py

