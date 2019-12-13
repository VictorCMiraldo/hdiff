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
module Data.HDiff.Base.Merge where

import           Control.Monad.Cont
import           Control.Monad.State
import           Control.Monad.Except
import           Data.Functor.Const
import qualified Data.Map as M
import           Data.Type.Equality
----------------------------------------
import           Generics.MRSOP.Util
import           Generics.MRSOP.Base hiding (match)
----------------------------------------
import           Data.Exists
import           Data.HDiff.MetaVar
import           Data.HDiff.Base
import           Generics.MRSOP.Holes
import           Generics.MRSOP.HDiff.Holes.Unify

import Unsafe.Coerce
-- import Debug.Trace

type Inst phi = M.Map Int (Exists phi)

-- |Attempts to insert a new point into an instantiation.
instAdd :: (EqHO phi)
        => Inst phi
        -> MetaVarIK ki at
        -> phi at
        -> Maybe (Inst phi)
instAdd iota v x
  = case M.lookup (metavarGet v) iota of
     Nothing           -> return $ M.insert (metavarGet v) (Exists x) iota
     Just (Exists old) -> if eqHO x (unsafeCoerce old)
                          then return iota
                          else Nothing

instLkup :: Inst phi -> MetaVarIK ki at -> Maybe (phi at)
instLkup iota v = exElim unsafeCoerce <$> M.lookup (metavarGet v) iota

instApply :: forall ki codes phi at
           . Inst phi
          -> (forall ix . MetaVarIK ki ix -> phi ix) -- ^ injection for undef. vars
          -> Holes ki codes (MetaVarIK ki) at
          -> Holes ki codes phi at
instApply iota inj = holesMap go 
  where
    go :: MetaVarIK ki iy -> phi iy
    go v = maybe (inj v) id . instLkup iota $ v

instM :: forall ki codes phi at . (EqHO ki) 
      => Holes ki codes (MetaVarIK ki) at
      -> Patch ki codes at
      -> ExceptT String (MergeM ki codes) ()
instM x = void . holesMapM (\h -> uncurry' go h >> return h) . holesLCP x
  where
    go :: Holes ki codes (MetaVarIK ki) ix
       -> Patch ki codes ix
       -> ExceptT String (MergeM ki codes) ()
    go (Hole' v) x = do
      iota <- get
      case instAdd iota v x of
        Just iota' -> put iota'
        Nothing    -> throwError $ "Failed contraction: " ++ show (metavarGet v)
    go x (Hole' (Chg (Hole' _) (Hole' _))) = return ()
    go x (Hole' _)                         = throwError $ "Conflict"
    go _ _ = throwError $ "Symbol Clash"

type MergeState ki codes = Inst (Patch ki codes)
mergeState0 = M.empty
type MergeM ki codes = State (MergeState ki codes)


{-
instance (ShowHO ki , HasDatatypeInfo ki fam codes) => Show (MergeState ki codes) where
  show (MergeState _ d i)
    = let dl = M.toList d
          il = M.toList i
       in unlines (map (("-- :" ++) . go) dl ++ map (("++ :" ++) . go) il)
    where
      go :: (Int , Exists (Holes ki codes (MetaVarIK ki))) -> String
      go (v , e) = show v ++ " = " ++ show e
   
-}


data Conflict :: (kon -> *) -> [[[Atom kon]]] -> Atom kon -> * where
  FailedContr :: [Exists (MetaVarIK ki)]
              -> Conflict ki codes at
  
  Conflict :: String
           -> Chg ki codes at
           -> Chg ki codes at
           -> Conflict ki codes at

data Phase2 :: (kon -> *) -> [[[Atom kon]]] -> Atom kon -> * where
  -- |A instantiation needs to be done after we completed the information
  --  discovery phase.
  P2Instantiate :: Chg ki codes at
                -> Phase2 ki codes at
  
  -- |Sometimes we must decide whether we are looking into the same change or not.
  P2TestEq      :: Chg ki codes at
                -> Chg ki codes at
                -> Phase2 ki codes at

type C ki fam codes at = (EqHO ki , TestEquality ki)

merge :: (C ki fam codes at)
      => Patch ki codes at
      -> Patch ki codes at
      -> Holes ki codes (Sum (Conflict ki codes) (Chg ki codes)) at
merge oa ob =
  let oab          = holesLCP oa ob
      (aux , inst) = runState (holesMapM (uncurry' phase1) oab) M.empty
   in case makeDelInsMaps inst of
        Left  vs -> Hole' (InL $ FailedContr vs)
        Right di -> holesMap (phase2' di) aux

-- |A 'PatchC' is a patch with potential conflicts inside
type PatchC ki codes at
  = Holes ki codes (Sum (Conflict ki codes) (Chg ki codes)) at

noConflicts :: PatchC ki codes ix -> Maybe (Patch ki codes ix)
noConflicts = holesMapM rmvInL
  where
    rmvInL (InL _) = Nothing
    rmvInL (InR x) = Just x

getConflicts :: PatchC ki codes ix -> [Exists (Conflict ki codes)]
getConflicts = foldr act [] . holesGetHolesAnnWith' Exists
  where
    act :: Exists (Sum (Conflict ki codes) (Chg ki codes))
        -> [Exists (Conflict ki codes)]
        -> [Exists (Conflict ki codes)]
    act (Exists (InR _)) = id
    act (Exists (InL c)) = (Exists c :)

diff3 :: forall ki fam codes ix
       . (C ki fam codes ix) -- TODO: remove redundant constraints
      => Patch ki codes ix
      -> Patch ki codes ix
      -> PatchC ki codes ix
diff3 oa ob = merge oa (ob `withFreshNamesFrom` oa)

type Subst2 ki codes = ( Subst ki codes (MetaVarIK ki)
                       , Subst ki codes (MetaVarIK ki))

makeDelInsMaps :: (C ki fam codes at)
               => MergeState ki codes
               -> Either [Exists (MetaVarIK ki)]
                         (Subst2 ki codes)
makeDelInsMaps iota =
  let sd = M.toList $ M.map (exMap $ holesJoin . holesMap chgDel) iota
      si = M.toList $ M.map (exMap $ holesJoin . holesMap chgIns) iota
   in do
    d <- minimize (toSubst sd)
    i <- minimize (toSubst si)
    return (d , i)
 where
   toSubst :: [(Int , Exists (Holes ki codes (MetaVarIK ki)))]
           -> Subst ki codes (MetaVarIK ki)
   toSubst = M.fromList
           . map (\(i , Exists h) -> (Exists (mkVar i h) , Exists h))

   mkVar :: Int -> Holes ki codes (MetaVarIK ki) at -> MetaVarIK ki at
   mkVar vx (HOpq _ k)    = NA_K (Annotate vx k)
   mkVar vx (Hole _ v)    = metavarSet vx v
   mkVar vx (HPeel _ _ _) = NA_I (Const vx)
        
{-
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
-}


chgrefine :: (C ki fam codes at)
          => Subst2 ki codes
          -> Chg ki codes at
          -> Chg ki codes at
chgrefine (d , i) (Chg del ins) =
  let del' = substApply d del
      ins' = substApply i ins
   in Chg del' ins'

chgeq :: (C ki fam codes at)
      => Subst2 ki codes
      -> Chg ki codes at
      -> Chg ki codes at
      -> Sum (Conflict ki codes) (Chg ki codes) at
chgeq di ca cb = 
  let ca' = chgrefine di ca
      cb' = chgrefine di cb
  in if changeEq ca' cb'
     then InR ca'
     else InL (Conflict "not-eq" ca' cb')

phase2' :: (C ki fam codes at)
        => Subst2 ki codes
        -> Sum (Conflict ki codes) (Phase2 ki codes) at
        -> Sum (Conflict ki codes) (Chg ki codes) at
phase2' _  (InL c) = InL c
phase2' di (InR x) = phase2 di x


phase2 :: (C ki fam codes at)
       => Subst2 ki codes
       -> Phase2 ki codes at
       -> Sum (Conflict ki codes) (Chg ki codes) at
phase2 di (P2Instantiate chg) = InR $ chgrefine di chg
phase2 di (P2TestEq ca cb)    = chgeq di ca cb

phase1 :: (C ki fam codes at)
       => Patch ki codes at
       -> Patch ki codes at
       -> MergeM ki codes (Sum (Conflict ki codes) (Phase2 ki codes) at)
phase1 ca cb = do
  r <- runExceptT $ discover ca cb
  return $ case r of
    Left err -> InL (Conflict err ca' cb')
    Right p2 -> InR p2
 where
   ca' = chgDistr ca
   cb' = chgDistr cb


discover :: (C ki fam codes at)
         => Patch ki codes at
         -> Patch ki codes at
         -> ExceptT String (MergeM ki codes) (Phase2 ki codes at)
discover (Hole' ca) (Hole' cb) = recChgChg ca cb
discover ca         (Hole' cb) = recApp    cb ca
discover (Hole' ca) cb         = recApp    ca cb
discover _          _          = throwError "Not a span"
          
cpy :: Chg ki codes at -> Bool
cpy (Chg (Hole' v) (Hole' u)) = metavarGet v == metavarGet u
cpy _                         = False

perm :: Chg ki codes at -> Bool
perm (Chg (Hole' v) (Hole' u)) = True
perm _                         = False

recChgChg :: (C ki fam codes at)
          => Chg ki codes at
          -> Chg ki codes at
          -> ExceptT String (MergeM ki codes) (Phase2 ki codes at)
recChgChg ca cb
  | perm ca   = recApp ca (Hole' cb)
  | perm cb   = recApp cb (Hole' ca)
  | otherwise = return $ P2TestEq ca cb

recApp :: (C ki fam codes at)
       => Chg ki codes at
       -> Patch ki codes at
       -> ExceptT String (MergeM ki codes) (Phase2 ki codes at)
recApp (Chg del ins) chg = do
  instM del chg
  return $ P2Instantiate (Chg del ins)
 
{-
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
-}

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

