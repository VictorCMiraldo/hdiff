{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE GADTs                 #-}
{-# OPTIONS_GHC -Wno-orphans       #-}
module Data.HDiff.Change.Merge where

import           Control.Monad.Cont
import           Control.Monad.State
import           Control.Monad.Except
import qualified Data.Map as M
import qualified Data.Set as S
import           Data.Type.Equality
----------------------------------------
import           Generics.MRSOP.Util
import           Generics.MRSOP.Base
----------------------------------------
import           Data.Exists
import           Data.HDiff.MetaVar
import           Data.HDiff.Change
import           Data.HDiff.Change.Apply
import           Data.HDiff.Change.Thinning
import           Generics.MRSOP.Holes
import           Generics.MRSOP.HDiff.Renderer

import Debug.Trace

data Conflict :: (kon -> *) -> [[[Atom kon]]] -> Atom kon -> * where
  Conflict :: CChange ki codes at
           -> CChange ki codes at
           -> String
           -> Conflict ki codes at

type C ki fam codes at = (ShowHO ki , HasDatatypeInfo ki fam codes
                         , RendererHO ki , EqHO ki , TestEquality ki)

isSimpleCpy :: Holes2 ki codes at -> Bool
isSimpleCpy (Hole' x :*: Hole' y) = metavarGet x == metavarGet y
isSimpleCpy _                     = False

-- |Attempts to merges two changes. We conjecture that if two merges
-- are disjoint, that is, operate or distinct parts of a tree.
--
-- This algorithm works in two phases: discovery and propagation.
merge :: forall ki fam codes at
       . (C ki fam codes at)
      => CChange ki codes at
      -> CChange ki codes at
      -> Either (Conflict ki codes at) (CChange ki codes at)
merge p q = either (Left . Conflict p q . unwords) (Right . uncurry' (CMatch S.empty))
          $ mergeWithErr p q

mergeStateEmpty :: MergeState ki codes
mergeStateEmpty = MergeState M.empty M.empty

data MergeState ki codes = MergeState
  { future  :: Subst ki codes (MetaVarIK ki) 
  , past    :: Subst ki codes (MetaVarIK ki)
  } 

showTh :: (C ki fam codes at) => Subst ki codes (MetaVarIK ki) -> String
showTh    = unlines
          . map (\(x , Exists s) -> show x ++ " = " ++ show s)
          . M.toList



type MergeM ki codes = StateT (MergeState ki codes)
                              (Except [String])

mergeWithErr :: forall ki fam codes at
              . (C ki fam codes at)
             => CChange ki codes at
             -> CChange ki codes at
             -> Either [String] (Holes2 ki codes at)
mergeWithErr p q
  = let p0 = holesLCP (cCtxDel p) (cCtxIns p)
        q0 = holesLCP (cCtxDel q) (cCtxIns q)
     in fmap utx2distr . runExcept $ evalStateT (go p0 q0) mergeStateEmpty 
  where
    debug :: MergeM ki codes a -> MergeM ki codes a
    debug m = do
      res <- m
      s <- gets future
      t <- gets past
      trace (showTh s ++ "\n\n" ++ showTh t) (return res)

    go :: HolesHoles2 ki codes at 
       -> HolesHoles2 ki codes at 
       -> MergeM ki codes (HolesHoles2 ki codes at)
    go p0 q0 = debug $ do
       let pq0 = holesLCP p0 q0
       routeError "discover"
         $ mapM_ (exElim (uncurry' discover)) (holesGetHolesAnnWith' Exists pq0)
       routeError "propagate"
         $ holesMapM (uncurry' propagate) pq0

routeError :: String -> MergeM ki codes x -> MergeM ki codes x
routeError msg = mapStateT (withExcept (msg:))
  
discover :: (C ki fam codes at)
            => HolesHoles2 ki codes at
            -> HolesHoles2 ki codes at
            -> MergeM ki codes ()
discover (Hole' p) (Hole' q) = register2 p q
discover (Hole' p)  cq       = register1 p cq
discover cp        (Hole' q) = register1 q cp
discover cp         cq       = throwError []

register2 :: (C ki fam codes at)
          => Holes2 ki codes at
          -> Holes2 ki codes at
          -> MergeM ki codes ()
register2 p q = 
  let scp = isSimpleCpy p
      scq = isSimpleCpy q
   in do
    when (not (scp || scq) && not (holes2Eq p q)) $ throwError ["ins-ins"]

-- The idea here is to match p to q
register1 :: (C ki fam codes at)
          => Holes2 ki codes at
          -> HolesHoles2 ki codes at
          -> MergeM ki codes ()
register1 p q = do
  sigma  <- gets future
  th     <- gets past
  -- first thing is thinning q to p's domain. We know this must be
  -- possible for p and q are a span (PRECONDITION)
  aux    <- lift $ withExcept ((:[]) . show)
                 $ thinHoles2st (scDel q :*: scIns q) (fst' p) th
  let ((_ :*: qi'), th') = aux
  sigma' <- lift $ withExcept ((:[]) . show)
                 $ pmatch' sigma (\_ _ _ -> Nothing) (fst' p) qi'
  put (MergeState sigma' th')

productM :: (Monad m)
         => (forall x . f x -> m (f' x))
         -> (forall x . g x -> m (g' x))
         -> (f :*: g) y
         -> m ((f' :*: g') y)
productM f g (x :*: y) = (:*:) <$> f x <*> g y         

propagate :: (C ki fam codes at)
        => HolesHoles2 ki codes at
        -> HolesHoles2 ki codes at
        -> MergeM ki codes (Holes2 ki codes at)
propagate (Hole' p) (Hole' q) 
  -- Even though we got to this point, we gotta refine the results;
  -- see case #7 on 
  | isSimpleCpy p = productM refinePast refinePast q
  | otherwise     = productM refinePast refinePast p
propagate (Hole' p) _         = inst1 p 
propagate _         (Hole' q) = inst1 q 
propagate _         _         = throwError []

refinePast :: forall ki fam codes at
            . (C ki fam codes at)
           => Holes ki codes (MetaVarIK ki) at
           -> MergeM ki codes (Holes ki codes (MetaVarIK ki) at)
refinePast x = do
  th <- gets past
  lift $ withExcept ((:[]) . show) $ refine x th

refineFuture :: forall ki fam codes at
              . (C ki fam codes at)
             => Holes ki codes (MetaVarIK ki) at
             -> MergeM ki codes (Holes ki codes (MetaVarIK ki) at)
refineFuture x = routeError "refineFuture" $ do
  th <- gets future
  lift $ withExcept ((:[]) . show) $ refine x th

inst1 :: (C ki fam codes at)
      => Holes2 ki codes at
      -> MergeM ki codes (Holes2 ki codes at)
inst1 p = routeError "inst1" $ do
  sigma <- gets future
  case runExcept $ transport (snd' p) sigma of
    Left err -> case snd' p of
      -- In case the instantiation failed, we check wheter we are looking
      -- into transporting a single variable. If that's the case, the transport
      -- might have failed because we failed to discover it during the first phase.
      -- Check test case #9 in MergeSpec for an example of where this is needed.
      -- I do feel we need a better story though
      -- Hole' var -> (:*:) <$> refinePast (fst' p) <*> return (Hole' var)
      _         -> throwError ["transport", show err]
    Right r  -> (:*:) <$> refinePast (fst' p) <*> refineFuture r
