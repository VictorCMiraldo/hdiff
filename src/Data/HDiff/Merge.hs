{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE StandaloneDeriving    #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE GADTs                 #-}
{-# OPTIONS_GHC -Wno-orphans       #-}
module Data.HDiff.Merge where

import           Control.Monad.Cont
import           Control.Monad.State
import           Control.Monad.Except
import           Data.Functor.Const
import qualified Data.Map as M
import           Data.Type.Equality
----------------------------------------
import           Generics.Simplistic
import           Generics.Simplistic.Util
import           Generics.Simplistic.Unify
----------------------------------------
import           Data.HDiff.MetaVar
import           Data.HDiff.Base
import           Data.HDiff.Instantiate
import           Data.HDiff.Show

import Debug.Trace

-- |This is specific to merging; which is why we left it here.
-- When instantiatting a deletion context against a patch,
-- we do /not/ fail when the deletion context requires something
-- but the patch is a permutation.
instM :: forall prim at  
       . Holes prim MetaVar at
      -> Patch prim at
      -> ExceptT String (MergeM prim) ()
instM p = void . holesMapM (\h -> uncurry' go h >> return h) . lcp p
  where
    go :: Holes prim MetaVar ix
       -> Patch prim ix
       -> ExceptT String (MergeM prim) ()
    go (Hole v) x = do
      iota <- get
      case instAdd iota v x of
        Just iota' -> put iota'
        Nothing    -> throwError $ "Failed contraction: " ++ show (metavarGet v)
    go _ (Hole (Chg (Hole _) (Hole _))) = return ()
    go _ (Hole _)                       = throwError $ "Conflict"
    go _ _ = throwError $ "Symbol Clash"


type MergeState prim = Inst (Patch prim)

mergeState0 :: MergeState prim
mergeState0 = M.empty

type MergeM prim = State (MergeState prim)

data Conflict :: [ * ] -> * -> * where
  FailedContr :: [Exists MetaVar]
              -> Conflict prim at
  
  Conflict :: String
           -> Chg prim at
           -> Chg prim at
           -> Conflict prim at

data Phase2 :: [ * ] -> * -> * where
  -- |A instantiation needs to be done after we completed the information
  --  discovery phase.
  P2Instantiate :: Chg prim at
                -> Phase2 prim at
  
  -- |Sometimes we must decide whether we are looking into the same change or not.
  P2TestEq      :: Chg prim at
                -> Chg prim at
                -> Phase2 prim at

type C ki fam codes at = (EqHO ki , TestEquality ki)

merge :: Patch prim at
      -> Patch prim at
      -> Holes prim (Sum (Conflict prim) (Chg prim)) at
merge oa ob =
  let oab          = lcp oa ob
      (aux , inst) = runState (holesMapM (uncurry' phase1) oab) M.empty
   in case makeDelInsMaps inst of
        Left  vs -> Hole (InL $ FailedContr vs)
        Right di -> holesMap (phase2' di) aux

-- |A 'PatchC' is a patch with potential conflicts inside
type PatchC prim at
  = Holes prim (Sum (Conflict prim) (Chg prim)) at

noConflicts :: PatchC prim ix -> Maybe (Patch prim ix)
noConflicts = holesMapM rmvInL
  where
    rmvInL (InL _) = Nothing
    rmvInL (InR x) = Just x

getConflicts :: PatchC prim ix -> [Exists (Conflict prim)]
getConflicts = foldr act [] . holesHolesList
  where
    act :: Exists (Sum (Conflict prim) (Chg prim))
        -> [Exists (Conflict prim)]
        -> [Exists (Conflict prim)]
    act (Exists (InR _)) = id
    act (Exists (InL c)) = (Exists c :)

diff3 :: forall prim ix
       . Patch prim ix
      -> Patch prim ix
      -> PatchC prim ix
diff3 oa ob = merge oa (ob `withFreshNamesFrom` oa)

type Subst2 prim = ( Subst prim MetaVar
                       , Subst prim MetaVar)

makeDelInsMaps :: forall prim
                . MergeState prim
               -> Either [Exists MetaVar]
                         (Subst2 prim)
makeDelInsMaps iota =
  let sd = M.toList $ M.map (exMap $ holesJoin . holesMap chgDel) iota
      si = M.toList $ M.map (exMap $ holesJoin . holesMap chgIns) iota
   in do
    d <- trace ("D:\n" ++ unlines (map show sd)) $ minimize (toSubst sd)
    i <- trace ("I:\n" ++ unlines (map show si)) $ minimize (toSubst si)
    
    return (d , i)
 where
   toSubst :: [(Int , Exists (Holes prim MetaVar))]
           -> Subst prim MetaVar
   toSubst = M.fromList
           . map (\(i , Exists h) -> (Exists (mkVar i h) , Exists h))

   mkVar :: Int -> Holes prim MetaVar at -> MetaVar at
   mkVar vx (Prim _) = Const vx
   mkVar vx (Hole v) = metavarSet vx v
   mkVar vx (Roll _) = Const vx
        
phase2' :: Subst2 prim
        -> Sum (Conflict prim) (Phase2 prim) at
        -> Sum (Conflict prim) (Chg prim) at
phase2' _  (InL c) = InL c
phase2' di (InR x) = phase2 di x


phase2 :: Subst2 prim
       -> Phase2 prim at
       -> Sum (Conflict prim) (Chg prim) at
phase2 di (P2Instantiate chg) = InR $ chgrefine di chg
phase2 di (P2TestEq ca cb)    = chgeq di ca cb

chgrefine :: Subst2 prim
          -> Chg prim at
          -> Chg prim at
chgrefine (d , i) (Chg del ins) =
  let del' = substApply d del
      ins' = substApply i ins
   in Chg del' ins'

chgeq :: Subst2 prim
      -> Chg prim at
      -> Chg prim at
      -> Sum (Conflict prim) (Chg prim) at
chgeq di ca cb = 
  let ca' = chgrefine di ca
      cb' = chgrefine di cb
  in if changeEq ca' cb'
     then InR ca'
     else InL (Conflict "not-eq" ca' cb')


phase1 :: Patch prim at
       -> Patch prim at
       -> MergeM prim (Sum (Conflict prim) (Phase2 prim) at)
phase1 ca cb = do
  r <- runExceptT $ discover ca cb
  return $ case r of
    Left err -> InL (Conflict err ca' cb')
    Right p2 -> InR p2
 where
   ca' = chgDistr ca
   cb' = chgDistr cb


discover :: Patch prim at
         -> Patch prim at
         -> ExceptT String (MergeM prim) (Phase2 prim at)
discover (Hole ca) (Hole cb) = recChgChg ca cb
discover ca        (Hole cb) = recApp    cb ca
discover (Hole ca) cb        = recApp    ca cb
discover _          _        = throwError "Not a span"
          
recChgChg :: Chg prim at
          -> Chg prim at
          -> ExceptT String (MergeM prim) (Phase2 prim at)
recChgChg ca cb
  | perm ca   = recApp ca (Hole cb)
  | perm cb   = recApp cb (Hole ca)
  | otherwise = return $ P2TestEq ca cb

recApp :: Chg prim at
       -> Patch prim at
       -> ExceptT String (MergeM prim) (Phase2 prim at)
recApp (Chg del ins) chg = do
  instM del chg
  return $ P2Instantiate (Chg del ins)
 
