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
     => UTx2 ki codes at
     -> Domain ki codes at
     -> Either (ApplicationErr ki codes (MetaVarIK ki))
               (UTx2 ki codes at)
thin (del :*: ins) dom = runExcept $ do
  sigma  <- flip execStateT M.empty $ utxThin del dom
  sigma' <- minimize sigma
  del'   <- refine del sigma'
  ins'   <- refine ins sigma'
  return $ del' :*: ins'

thin' :: (ShowHO ki , TestEquality ki, EqHO ki)
     => UTx2 ki codes at
     -> UTx2 ki codes at
     -> Either (ApplicationErr ki codes (MetaVarIK ki))
               (UTx2 ki codes at)
thin' (delP :*: insP) (delQ :*: insQ) = runExcept $ do
  sigma  <- flip execStateT M.empty $ utxThin delP delQ
  sigma' <- minimize sigma
  del    <- refine delP sigma'
  insP'  <- refine insP sigma'
  insQ'  <- refine insQ sigma'
  qi     <- trace "b" $ (pmatch del insQ' >>= transport insP')
  return $ insP' :*: qi





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
    go p q@(UTxHole var) = record_eq var p >> return p
    go p@(UTxHole var) q = record_eq var q >> return p
    go p q | eqHO p q    = return p
           | otherwise   = throwError (IncompatibleTerms p q)

    -- Whenever we see a variable being matched against a term
    -- we record the equivalence. First we make sure we did not
    -- record such equivalence yet, otherwise, we recursively thin
    record_eq :: (ShowHO ki , TestEquality ki, EqHO ki)
              => MetaVarIK ki at
              -> UTx ki codes (MetaVarIK ki) at
              -> StateT (Subst ki codes (MetaVarIK ki))
                        (Except (ThinningErr ki codes))
                        ()
    record_eq var q = do
      sigma <- get
      mterm <- lift (lookupVar var sigma)
      case mterm of
        -- First time we see 'var', we instantiate it and get going.
        Nothing -> when (q /= UTxHole var)
                 $ modify (M.insert (metavarGet var) (Exists q))
        -- It's not the first time we thin 'var'; previously, we had
        -- that 'var' was supposed to be p'. We will check whether it
        -- is the same as q, if not, we will have to thin p' with q.
        Just q' -> unless (eqHO q' q)
                 $ void $ utxThin q' q
          


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

