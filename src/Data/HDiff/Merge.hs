{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE StandaloneDeriving    #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE PolyKinds             #-}
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
import           Generics.MRSOP.Util
import           Generics.MRSOP.Base hiding (match)
import           Generics.MRSOP.Holes
import           Generics.MRSOP.Holes.Unify
----------------------------------------
import           Data.HDiff.MetaVar
import           Data.HDiff.Base
import           Data.HDiff.Instantiate

-- |This is specific to merging; which is why we left it here.
-- When instantiatting a deletion context against a patch,
-- we do /not/ fail when the deletion context requires something
-- but the patch is a permutation.
instM :: forall ki codes at . (EqHO ki) 
      => Holes ki codes MetaVar at
      -> Patch ki codes at
      -> ExceptT String (MergeM ki codes) ()
instM p = void . holesMapM (\h -> uncurry' go h >> return h) . holesLCP p
  where
    go :: Holes ki codes MetaVar ix
       -> Patch ki codes ix
       -> ExceptT String (MergeM ki codes) ()
    go (Hole' v) x = do
      iota <- get
      case instAdd iota v x of
        Just iota' -> put iota'
        Nothing    -> throwError $ "Failed contraction: " ++ show (metavarGet v)
    go _ (Hole' (Chg (Hole' _) (Hole' _))) = return ()
    go _ (Hole' _)                         = throwError $ "Conflict"
    go _ _ = throwError $ "Symbol Clash"


type MergeState ki codes = Inst (Patch ki codes)

mergeState0 :: MergeState ki codes
mergeState0 = M.empty

type MergeM ki codes = State (MergeState ki codes)

data Conflict :: (kon -> *) -> [[[Atom kon]]] -> Atom kon -> * where
  FailedContr :: [Exists MetaVar]
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

type Subst2 ki codes = ( Subst ki codes MetaVar
                       , Subst ki codes MetaVar)

-- minimize :: forall ki codes phi
--           . (EqHO ki , Ord (Exists phi))
--          => Subst ki codes phi -- ^
--          -> Either [Exists phi] (Subst ki codes phi)


makeDelInsMaps :: forall ki codes
                . () -- (C ki fam codes at)
               => MergeState ki codes
               -> Either [Exists MetaVar]
                         (Subst2 ki codes)
makeDelInsMaps iota =
  let sd = M.toList $ M.map (exMap $ holesJoin . holesMap chgDel) iota
      si = M.toList $ M.map (exMap $ holesJoin . holesMap chgIns) iota
   in do
    d <- minimize (toSubst sd)
    i <- minimize (toSubst si)
    return (d , i)
 where
   toSubst :: [(Int , Exists (Holes ki codes MetaVar))]
           -> Subst ki codes MetaVar
   toSubst = M.fromList
           . map (\(i , Exists h) -> (Exists (Const i) , Exists h))

   mkVar :: Int -> Holes ki codes MetaVar at -> MetaVar at
   mkVar vx (HOpq _ k)    = Const vx
   mkVar vx (Hole _ v)    = metavarSet vx v
   mkVar vx (HPeel _ _ _) = Const vx
        
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
 
