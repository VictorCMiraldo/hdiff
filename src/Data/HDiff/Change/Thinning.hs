{-# LANGUAGE QuantifiedConstraints #-}
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
module Data.HDiff.Change.Thinning where

import           Data.Type.Equality
import qualified Data.Map as M
import qualified Data.Set as S
import           Control.Monad.Writer
import           Control.Monad.Except
import           Control.Monad.State
---------------------------------------
import Generics.MRSOP.Util
import Generics.MRSOP.Base
import Generics.MRSOP.Holes
---------------------------------------
import Data.Exists
import Data.HDiff.MetaVar
import Data.HDiff.Change
import Data.HDiff.Change.Apply

import Debug.Trace

type ThinningErr ki codes = ApplicationErr ki codes (MetaVarIK ki)

-- Haskell tends to want a type-signature for some non-trivial lifts. 
lift' :: (Monad m) => m a -> StateT (Subst ki codes (MetaVarIK ki)) m a
lift' = lift

thin :: (ShowHO ki , TestEquality ki, EqHO ki)
     => CChange ki codes at
     -> Domain  ki codes at
     -> Either (ApplicationErr ki codes (MetaVarIK ki))
               (CChange ki codes at)
thin chg dom = uncurry' cmatch <$> thinUTx2 (cCtxDel chg :*: cCtxIns chg) dom

instance (EqHO f , EqHO g) => Eq ((f :*: g) x) where
  (==) (fx :*: gx) (fy :*: gy) = fx == fy && gx == gy

tr :: (ShowHO ki , TestEquality ki, EqHO ki)
   => CChange ki codes at
   -> CChange ki codes at
   -> Either (ApplicationErr ki codes (Holes2 ki codes))
             (CChange ki codes at)
tr (CMatch _ dp ip) q = do
  xx <- genericApply q (holesLCP dp ip)
  let xd = holesJoin $ holesMap fst' xx
  let xi = holesJoin $ holesMap snd' xx
  return $ CMatch S.empty xd xi
{-
  sigmaD <- pmatch qd pd
  sigmaI <- pmatch qd pi
  resD   <- transport qi sigmaD
  resI   <- transport qi sigmaI
  return (cmatch resD resI)
-}

thinUTx2 :: (ShowHO ki , TestEquality ki, EqHO ki)
         => Holes2 ki codes at
         -> Domain ki codes at
         -> Either (ApplicationErr ki codes (MetaVarIK ki))
                   (Holes2 ki codes at)
thinUTx2 (del :*: ins) dom = runExcept $ do
  sigma  <- flip execStateT M.empty $ utxThin del dom
  sigma' <- minimize sigma
  del'   <- refine del sigma'
  ins'   <- refine ins sigma'
  return $ del' :*: ins'

thin' :: (ShowHO ki , TestEquality ki, EqHO ki)
     => Holes2 ki codes at
     -> Holes2 ki codes at
     -> Either (ApplicationErr ki codes (MetaVarIK ki))
               (Holes2 ki codes at)
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
        => Holes ki codes (MetaVarIK ki) at
        -> Domain ki codes at
        -> StateT (Subst ki codes (MetaVarIK ki))
                  (Except (ThinningErr ki codes))
                  ()
utxThin p0 q0 = void $ holesMapM (uncurry' go) $ holesLCP p0 q0
  where
    go :: (ShowHO ki , TestEquality ki, EqHO ki)
       => Holes ki codes (MetaVarIK ki) at
       -> Domain ki codes at
       -> StateT (Subst ki codes (MetaVarIK ki))
                 (Except (ThinningErr ki codes))
                 (Holes ki codes (MetaVarIK ki) at)
    go p (Hole _ var)   = record_eq var p >> return p
    go p@(Hole _ var) q = record_eq var q >> return p
    go p q | p == q     = return p
           | otherwise  = throwError (IncompatibleTerms p q)

    -- Whenever we see a variable being matched against a term
    -- we record the equivalence. First we make sure we did not
    -- record such equivalence yet, otherwise, we recursively thin
    record_eq :: (ShowHO ki , TestEquality ki, EqHO ki)
              => MetaVarIK ki at
              -> Holes ki codes (MetaVarIK ki) at
              -> StateT (Subst ki codes (MetaVarIK ki))
                        (Except (ThinningErr ki codes))
                        ()
    record_eq var q = do
      sigma <- get
      mterm <- lift (lookupVar var sigma)
      case mterm of
        -- First time we see 'var', we instantiate it and get going.
        Nothing -> when (q /= Hole' var)
                 $ modify (M.insert (metavarGet var) (Exists q))
        -- It's not the first time we thin 'var'; previously, we had
        -- that 'var' was supposed to be p'. We will check whether it
        -- is the same as q, if not, we will have to thin p' with q.
        Just q' -> unless (q' == q)
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
minimize sigma = whileM sigma [] $ \s _
  -> M.fromList <$> (mapM (secondF (exMapM go)) (M.toList s))
  where
    secondF :: (Functor m) => (a -> m b) -> (x , a) -> m (x , b)
    secondF f (x , a) = (x,) <$> f a

    -- The actual engine of the 'minimize' function is thinning the
    -- variables that appear in the image of the substitution under production.
    -- We use the writer monad to inform us wich variables have been fully
    -- eliminated. Once this process returns no eliminated variables,
    -- we are done.
    go :: Holes ki codes (MetaVarIK ki) at
       -> WriterT [Int] (Except (ThinningErr ki codes))
                                (Holes ki codes (MetaVarIK ki) at)
    go = holesRefineVarsM $ \_ var -> do
           mterm <- lift (lookupVar var sigma)
           case mterm of
             Nothing -> return (Hole' var)
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
       => Holes ki codes (MetaVarIK ki) ix
       -> Subst ki codes (MetaVarIK ki)
       -> Except (ThinningErr ki codes) (Holes ki codes (MetaVarIK ki) ix)
refine (Hole  _ var)   s = lookupVar var s >>= return . maybe (Hole' var) id
refine (HOpq  _ oy)    _ = return $ HOpq' oy
refine (HPeel _ cy py) s = HPeel' cy <$> mapNPM (flip refine s) py

