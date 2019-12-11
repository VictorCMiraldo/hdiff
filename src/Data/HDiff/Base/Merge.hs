{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
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
import           Data.HDiff.Base
import           Generics.MRSOP.Holes
import           Generics.MRSOP.HDiff.Holes.Unify

-- import Debug.Trace

data Conflict :: (kon -> *) -> [[[Atom kon]]] -> Atom kon -> * where
  Conflict :: Chg ki codes at
           -> Chg ki codes at
           -> Conflict ki codes at

data Phase2 :: (kon -> *) -> [[[Atom kon]]] -> Atom kon -> * where
  -- |A instantiation needs to be done after we completed the information
  --  discovery phase.
  P2Instantiate :: Holes2 ki codes (MetaVarIK ki) at
                -> Phase2 ki codes at
  
  -- |Sometimes we must decide whether we are looking into the same change or not.
  P2TestEq      :: Holes2 ki codes (MetaVarIK ki) at
                -> Holes2 ki codes (MetaVarIK ki) at
                -> Phase2 ki codes at

-- TODO: Can't reuse subst here... I must make my own type of subst
data MergeState ki codes = MergeState
  { sigma :: Subst ki codes (Holes2 ki codes (MetaVarIK ki))
  , mdel  :: Subst ki codes (MetaVarIK ki)
  , mins  :: Subst ki codes (MetaVarIK ki)
  } 

instance (ShowHO ki , HasDatatypeInfo ki fam codes) => Show (MergeState ki codes) where
  show (MergeState _ d i)
    = let dl = M.toList d
          il = M.toList i
       in unlines (map (("-- :" ++) . go) dl ++ map (("++ :" ++) . go) il)
    where
      go :: (Int , Exists (Holes ki codes (MetaVarIK ki))) -> String
      go (v , e) = show v ++ " = " ++ show e
   

mergeState0 = MergeState M.empty M.empty M.empty


data MergeError = ME_Conflict | ME_Other
  deriving (Eq , Show)

type MergeM ki codes = StateT (MergeState ki codes) (Except MergeError)

type C ki fam codes at = (ShowHO ki , HasDatatypeInfo ki fam codes
                         , EqHO ki , TestEquality ki)

type HolesHoles2 ki codes = Holes ki codes (Holes2 ki codes (MetaVarIK ki))

-- |Returns 'Nothing' if they are not a span;
-- PRECOND: changes for ma span and have distinct variables.
chgMerge :: (C ki fam codes at)
         => Chg ki codes at
         -> Chg ki codes at
         -> Either (Conflict ki codes at) (Chg ki codes at)
chgMerge oa ob = runExcept $ withExcept (const (Conflict oa ob))
            $ fmap fst
            -- $ fmap (\(x , st) -> trace (show st) x)
            $ flip runStateT mergeState0 $ do
  let ca = holesLCP (cCtxDel oa) (cCtxIns oa)
  let cb = holesLCP (cCtxDel ob) (cCtxIns ob)
  phase1 <- holesMapM (uncurry' reconcile) (holesLCP ca cb)
  makeDelInsMaps
  phase2 <- holesMapM refine phase1
  return $ CMatch S.empty (holesJoin $ holesMap fst' phase2)
                          (holesJoin $ holesMap snd' phase2)

makeDelInsMaps :: (C ki fam codes at) => MergeM ki codes ()
makeDelInsMaps = do
  s <- gets sigma
  let sd = M.toList $ M.map (exMap $ holesJoin . holesMap fst') s
  let si = M.toList $ M.map (exMap $ holesJoin . holesMap snd') s
  d <- gets mdel
  i <- gets mins
  d' <- lift $ foldM (\d0 (v , Exists e) -> substInsert' d0 v e) d sd
  i' <- lift $ foldM (\i0 (v , Exists e) -> substInsert' i0 v e) i si
  d'' <- lift $ withExcept (const ME_Other) $ minimize d'
  i'' <- lift $ withExcept (const ME_Other) $ minimize i'
  put (MergeState s d'' i'')

-- TOTHINK: Should we do multiple rounds?
fullrefine :: (C ki fam codes at)
           => Holes ki codes (MetaVarIK ki) ix
           -> Subst ki codes (MetaVarIK ki)
           -> Except MergeError (Holes ki codes (MetaVarIK ki) ix)
fullrefine (Hole  _ var)   s = (withExcept (const ME_Other) $ lookupVar var s)
                           >>= return . maybe (Hole' var) id
fullrefine (HOpq  _ oy)    _ = return $ HOpq' oy
fullrefine (HPeel _ cy py) s = HPeel' cy <$> mapNPM (flip fullrefine s) py

chgrefine :: (C ki fam codes at)
          => Holes2 ki codes (MetaVarIK ki) at
          -> MergeM ki codes (Holes2 ki codes (MetaVarIK ki) at)
chgrefine (del :*: ins) = do
  d <- gets mdel
  i <- gets mins
  (:*:) <$> lift (fullrefine del d) <*> lift (fullrefine ins i)

chgeq :: (C ki fam codes at)
      => Holes2 ki codes (MetaVarIK ki) at
      -> Holes2 ki codes (MetaVarIK ki) at
      -> MergeM ki codes (Holes2 ki codes (MetaVarIK ki) at)
chgeq ca cb = do
  ca' <- chgrefine ca
  cb' <- chgrefine cb
  when (not (holes2Eq ca' cb')) (throwError ME_Conflict)
  return ca'

refine :: (C ki fam codes at)
       => Phase2 ki codes at
       -> MergeM ki codes (Holes2 ki codes (MetaVarIK ki) at)
refine (P2Instantiate chg) = chgrefine chg
refine (P2TestEq ca cb)    = chgeq ca cb

reconcile :: (C ki fam codes at)
          => HolesHoles2 ki codes at
          -> HolesHoles2 ki codes at
          -> MergeM ki codes (Phase2 ki codes at)
reconcile (Hole' ca) (Hole' cb) = recChgChg ca cb
reconcile ca         (Hole' cb) = recApp    cb ca
reconcile (Hole' ca) cb         = recApp    ca cb
reconcile _          _          = throwError ME_Other
          
cpy :: Holes2 ki codes (MetaVarIK ki) at -> Bool
cpy (Hole' v :*: Hole' u) = metavarGet v == metavarGet u
cpy _                     = False

perm :: Holes2 ki codes (MetaVarIK ki) at -> Bool
perm (Hole' v :*: Hole' u) = True
perm _                     = False

recChgChg :: (C ki fam codes at)
          => Holes2 ki codes (MetaVarIK ki) at
          -> Holes2 ki codes (MetaVarIK ki) at
          -> MergeM ki codes (Phase2 ki codes at)
recChgChg ca cb
  | perm ca   = recApp ca (Hole' cb)
  | perm cb   = recApp cb (Hole' ca)
  | otherwise = return $ P2TestEq ca cb

recApp :: (C ki fam codes at)
       => Holes2 ki codes (MetaVarIK ki) at
       -> HolesHoles2 ki codes at
       -> MergeM ki codes (Phase2 ki codes at)
recApp (del :*: ins) chg = do
  holesMatch del chg
  return $ P2Instantiate (del :*: ins)
  
holesMatch :: (C ki fam codes iy)
           => Holes ki codes (MetaVarIK ki)    ix
           -> Holes ki codes (Holes2 ki codes (MetaVarIK ki)) ix
           -> MergeM ki codes ()
holesMatch (Hole _ var) x  = do
  s  <- gets sigma 
  s' <- maybe (throwError ME_Other) return $ substInsert s var x
  modify (\st -> st { sigma = s' })
holesMatch pa (Hole _ (Hole' var :*: Hole' _)) = do
  d  <- gets mdel
  d' <- maybe (throwError ME_Other) return $ substInsert d var pa
  modify (\st -> st { mdel = d' })
holesMatch pa (Hole _ _) = throwError ME_Other
holesMatch (HOpq _ oa) (HOpq _ ox)
  | eqHO oa ox  = return ()
  | otherwise   = throwError ME_Other
holesMatch pa@(HPeel _ ca ppa) x@(HPeel _ cx px) =
  case testEquality ca cx of
    Nothing   -> throwError ME_Other
    Just Refl -> void $ mapNPM (\x -> uncurry' holesMatch x >> return x) (zipNP ppa px)

-- |Attempts to insert a new point into a substitution.
substInsert :: ( TestEquality ki , TestEquality phi , HasIKProjInj ki phi
               , EqHO ki , EqHO phi , Ord (Exists phi))
            => Subst ki codes phi
            -> phi at
            -> Holes ki codes phi at
            -> Maybe (Subst ki codes phi)
substInsert sigma v x
  = case M.lookup (Exists v) sigma of
     Nothing           -> return $ M.insert (Exists v) (Exists x) sigma
     Just (Exists old) -> case testEquality old x of
       Nothing   -> Nothing
       Just Refl -> if eqHO old x
                    then return sigma
                    else Nothing -- Failed Contraction?


{-
substInsert' :: (Applicable ki codes phi , EqHO ki , EqHO phi)
             => Subst ki codes phi
             -> Int
             -> Holes ki codes phi ix
             -> Except MergeError (Subst ki codes phi)
substInsert' s var new = case M.lookup var s of
  Nothing           -> return $ M.insert var (Exists new) s
  Just (Exists old) -> case testEquality old new of
    Nothing   -> throwError ME_Other
    Just Refl -> if eqHO old new
                 then return s
                 else throwError ME_Other
-}
