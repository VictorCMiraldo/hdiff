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
import           Data.List (sort)
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

type ThinningErr ki codes = ApplicationErr ki codes (MetaVarIK ki)

-- |Thinning a change with respect to a domain is the process of restricting
-- said change to elements of said domain. For example,
--
-- > thin (bin 0 K |-> 0) (bin (bin T 4) 5) = bin (bin T 4) K |-> bin T 4
--
-- PRECONDITION: The change and domain have a different set of names.
--               This function will loop if some variable occurs both in the
--               change and domain passed as arguments.
thin :: (TestEquality ki, EqHO ki , ShowHO ki , HasDatatypeInfo ki fam codes)
     => CChange ki codes at
     -> Domain  ki codes at
     -> Either (ThinningErr ki codes) (CChange ki codes at)
thin chg dom = (uncurry' cmatch) <$> thinHoles2 (cCtxDel chg :*: cCtxIns chg) dom

thinHoles2 :: (TestEquality ki, EqHO ki , ShowHO ki , HasDatatypeInfo ki fam codes)
           => Holes2 ki codes at
           -> Domain ki codes at
           -> Either (ThinningErr ki codes) (Holes2 ki codes at) 
thinHoles2 di dom = runExcept (fst <$> thinHoles2st di dom M.empty)

-- |Unwrapped vesion of 'thin'; We also return the subsitution used. An example of
-- where this is needed is patch composition.
-- 
thinHoles2st :: (TestEquality ki, EqHO ki , ShowHO ki , HasDatatypeInfo ki fam codes)
             => Holes2 ki codes at
             -> Domain ki codes at
             -> Subst ki codes (MetaVarIK ki)
             -> Except (ThinningErr ki codes)
                       (Holes2 ki codes at , Subst ki codes (MetaVarIK ki))
thinHoles2st (del :*: ins) dom sigma0 = do
  -- The thinning process is twofold; first we look solely at the deletion
  -- context over the domain we are thinning against and register the equalities
  -- we see.
  sigma  <- flip execStateT sigma0 $ thinGetEquivs del dom
  sigma' <- minimize sigma
  del'   <- refine del sigma'
  ins'   <- refine ins sigma'
  return $ (del' :*: ins' , sigma')

-- |The @thinGetEquivs del dom@ function computes the equivalences between
-- the variables in @del@ and terms in @dom@ and vice versa.
--
-- We first anti-unify @del@ and @dom@ and map over the variable-mapping
-- that is returned by it. In our lingo, this is @holesMap f $ holesLCP del dom@.
-- If we see an anti-unification variable clause in the forms @(Hole x , p)@
-- or @(p , Hole x)@; we register @x = p@.
--
-- When registering @x = p@, however, we must check whether this was the first time we
-- really saw @x@.
thinGetEquivs :: (TestEquality ki, EqHO ki , ShowHO ki , HasDatatypeInfo ki fam codes)
        => Holes ki codes (MetaVarIK ki) at
        -> Domain ki codes at
        -> StateT (Subst ki codes (MetaVarIK ki))
                  (Except (ThinningErr ki codes))
                  ()
thinGetEquivs p0 q0 = void $ holesMapM (uncurry' go) $ holesLCP p0 q0
  where
    go :: (TestEquality ki, EqHO ki , ShowHO ki , HasDatatypeInfo ki fam codes)
       => Holes ki codes (MetaVarIK ki) at
       -> Domain ki codes at
       -> StateT (Subst ki codes (MetaVarIK ki))
                 (Except (ThinningErr ki codes))
                 (Holes ki codes (MetaVarIK ki) at)
    go p (Hole _ var)   = record_eq var p >> return p
    go p@(Hole _ var) q = record_eq var q >> return p
    go p q | eqHO p q   = return p
           | otherwise  = throwError (IncompatibleTerms p q)

    -- Whenever we see a variable being matched against a term
    -- we record the equivalence. First we make sure we did not
    -- record such equivalence yet, otherwise, we recursively thin
    record_eq :: (TestEquality ki, EqHO ki , ShowHO ki , HasDatatypeInfo ki fam codes)
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
        Nothing -> when (not $ eqHO q (Hole' var))
                 $ modify (M.insert (metavarGet var) (Exists q))
        -- It's not the first time we thin 'var'; previously, we had
        -- that 'var' was supposed to be p'. We will check whether it
        -- is the same as q, if not, we will have to thin p' with q.
        Just q' -> unless (eqHO q' q)
                 $ void $ thinGetEquivs q q'
          


-- |The minimization step performs the 'occurs' check and removes
--  unecessary steps. For example;
--
--  > sigma = fromList
--  >           [ (0 , bin 1 2)
--  >           , (1 , bin 4 4) ]
--
-- Then, @minimize sigma@ will return @fromList [(0 , bin (bin 4 4) 2) , (1 , bin 4 4)]@
--
minimize :: forall ki codes
          . (EqHO ki , TestEquality ki)
         => Subst ki codes (MetaVarIK ki)
         -> Except (ThinningErr ki codes) (Subst ki codes (MetaVarIK ki))
minimize sigma = whileM sigma [] $ \s _
  -> M.fromList <$> (mapM (secondF (exMapM go)) (M.toList s))
  where
    secondF :: (Functor m) => (a -> m b) -> (x , a) -> m (x , b)
    secondF f (x , a) = (x,) <$> f a

    -- The actual engine of the 'minimize' function is thinning the
    -- variables that appear in the image of the substitution under production.
    -- We use the writer monad solely to let us know whether some variables have
    -- been substituted in this current term. After one iteration
    -- of the map where no variable is further refined, we are done.
    go :: Holes ki codes (MetaVarIK ki) at
       -> WriterT [Int] (Except (ThinningErr ki codes))
                                (Holes ki codes (MetaVarIK ki) at)
    go = holesRefineVarsM $ \_ var -> do
           mterm <- lift (lookupVar var sigma)
           case mterm of
             Nothing -> return (Hole' var)
             Just r  -> tell [metavarGet var]
                     >> return r

    -- We loop while there is work to be done or no progress
    -- was done.
    whileM :: (Monad m, Show x , Ord x)
           => a -> [x] -> (a -> [x] -> WriterT [x] m a) -> m a
    whileM a xs f = runWriterT (f a xs)
                >>= \(x' , xs') -> if null xs' || (sort xs' == sort xs)
                                   then return x'
                                   else whileM x' xs' f


-- |This is similar to 'transport', but does not throw errors
-- on undefined variables.
refine :: (TestEquality ki , EqHO ki)
       => Holes ki codes (MetaVarIK ki) ix
       -> Subst ki codes (MetaVarIK ki)
       -> Except (ThinningErr ki codes) (Holes ki codes (MetaVarIK ki) ix)
refine (Hole  _ var)   s = lookupVar var s >>= return . maybe (Hole' var) id
refine (HOpq  _ oy)    _ = return $ HOpq' oy
refine (HPeel _ cy py) s = HPeel' cy <$> mapNPM (flip refine s) py

