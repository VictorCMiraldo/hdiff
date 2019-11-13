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
merge p q = either (const (Left $ Conflict p q)) (Right . uncurry' (CMatch S.empty))
          $ mergeWithErr p q

mergeStateEmpty :: MergeState ki codes
mergeStateEmpty = MergeState M.empty M.empty

data MergeState ki codes = MergeState
  { subst   :: Subst ki codes (Holes2 ki codes) 
  , thinner :: Subst ki codes (MetaVarIK ki)
  } 

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
    showSigma  = unlines
               . map (\(x , Exists s) -> show x ++ " = " ++ show (scDel s)
                                             ++ "\n  ; " ++ show (scIns s) )
               . M.toList
    
    showTh :: Subst ki codes (MetaVarIK ki) -> String
    showTh    = unlines
              . map (\(x , Exists s) -> show x ++ " = " ++ show s)
              . M.toList

    debug :: MergeM ki codes a -> MergeM ki codes a
    debug m = do
      res <- m
      s <- gets subst
      t <- gets thinner
      trace (showSigma s ++ "\n\n" ++ showTh t) (return res)

    go :: HolesHoles2 ki codes at 
       -> HolesHoles2 ki codes at 
       -> MergeM ki codes (HolesHoles2 ki codes at)
    go p0 q0 = {- debug $ -} do
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

register1 :: (C ki fam codes at)
          => Holes2 ki codes at
          -> HolesHoles2 ki codes at
          -> MergeM ki codes ()
register1 p q = do
  sigma  <- gets subst
  th     <- gets thinner
  aux    <- lift $ withExcept ((:[]) . show)
                 $ thinHoles2st (scDel q :*: scIns q) (fst' p) th
  let ((qd' :*: qi'), th') = aux
  sigma' <- lift $ withExcept ((:[]) . show)
                 $ pmatch' sigma (\_ _ _ -> Nothing) (fst' p) (holesLCP qd' qi')
  put (MergeState sigma' th')

propagate :: (C ki fam codes at)
        => HolesHoles2 ki codes at
        -> HolesHoles2 ki codes at
        -> MergeM ki codes (Holes2 ki codes at)
propagate (Hole' p) (Hole' q) 
  | isSimpleCpy p = refine2 q
  | otherwise     = refine2 p
propagate (Hole' p) _         = inst1 p 
propagate _         (Hole' q) = inst1 q 
propagate _         _         = throwError []

refine1 :: forall ki fam codes at
         . (C ki fam codes at)
        => Holes ki codes (MetaVarIK ki) at
        -> MergeM ki codes (Holes ki codes (MetaVarIK ki) at)
refine1 x = do
  th <- gets thinner
  lift $ withExcept ((:[]) . show) $ refine x th


refine1' :: forall ki fam codes at
          . (C ki fam codes at)
         => Holes ki codes (MetaVarIK ki) at
         -> MergeM ki codes (Holes ki codes (MetaVarIK ki) at)
refine1' x = do
  th <- M.map (exMap scIns) <$> gets subst
  lift $ withExcept ((:[]) . show) $ refine x th

refine2 :: forall ki fam codes at
         . (C ki fam codes at)
        => Holes2 ki codes at
        -> MergeM ki codes (Holes2 ki codes at)
refine2 (d :*: i) = (:*:) <$> refine1 d <*> refine1 i        

inst1 :: (C ki fam codes at)
      => Holes2 ki codes at
      -> MergeM ki codes (Holes2 ki codes at)
inst1 p = routeError "inst1" $ do
  sigma <- gets subst
  case runExcept $ transport (snd' p) sigma of
    Left err -> case snd' p of
      -- In case the instantiation failed, we check wheter we are looking
      -- into transporting a single variable. If that's the case, the transport
      -- might have failed because we failed to discover it during the first phase.
      -- Check test case #9 in MergeSpec for an example of where this is needed.
      -- I do feel we need a better story though
      Hole' var -> (:*:) <$> refine1 (fst' p) <*> return (Hole' var)
      _         -> throwError [show err]
    Right r  -> (:*:) <$> refine1 (fst' p) <*> refine1' (scIns r)
