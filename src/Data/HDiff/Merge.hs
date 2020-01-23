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
import           Generics.Simplistic.Zipper
----------------------------------------
import           Data.HDiff.MetaVar
import           Data.HDiff.Base
import           Data.HDiff.Instantiate
import           Data.HDiff.Merge.Align
import           Data.HDiff.Show

trace :: x -> a -> a
trace _ = id

data Conflict :: [*] -> [*] -> * -> * where
  FailedContr :: [Exists (MetaVar fam prim)]
              -> Conflict fam prim at
  
  Conflict :: String
           -> Aligned fam prim at
           -> Aligned fam prim at
           -> Conflict fam prim at

-- |A 'PatchC' is a patch with potential conflicts inside
type PatchC fam prim at
  = Holes fam prim (Sum (Conflict fam prim) (Chg fam prim)) at

diff3 :: forall fam prim ix
       . (HasDecEq fam)
      => Patch fam prim ix
      -> Patch fam prim ix
      -> PatchC fam prim ix
-- Since patches are well-scoped (again! yay! lol)
-- we can map over the anti-unif for efficiency purposes.
diff3 oa ob =
  let oa' = align oa
      ob' = align ob
   in holesMap (uncurry' mergeAl . delta alignDistr) $ lcp oa' ob'
 where
   delta f (x :*: y) = (f x :*: f y)

mergeAl :: Aligned fam prim x -> Aligned fam prim x
        -> Sum (Conflict fam prim) (Chg fam prim) x
mergeAl p q = case runExcept (evalStateT (mrg p q) mrgSt0) of
                Left err -> _
                Right r  -> _

-- Merging alignments might require merging changes; which
-- in turn requier a state.

type MergeState fam prim = Inst (Patch fam prim)
type MergeM     fam prim = StateT (MergeState fam prim) (Except String)

mrgSt0 :: MergeState fam prim
mrgSt0 = M.empty

mrg :: Aligned fam prim x -> Aligned fam prim x
    -> MergeM fam prim (Aligned fam prim x)
-- Insertions are preserved as long as they are not
-- simultaneous
mrg (Ins _) (Ins _)           = throwError "ins-ins"
mrg (Ins (Zipper zip p)) q    = Ins . Zipper zip <$> mrg p q
mrg p (Ins (Zipper zip q))    = Ins . Zipper zip <$> mrg p q

-- Deletions need to be checked for compatibility
mrg (Del p@(Zipper zip _)) q  = compat p q
                            >>= fmap (Del . Zipper zip) . uncurry mrg
mrg p (Del q@(Zipper zip _))  = compat q p
                            >>= fmap (Del . Zipper zip) . uncurry mrg . swap
  where swap (x , y) = (y , x)

-- Spines and Changes

-- |Checks that a deletion is compatible with an alignment; if so, returns
-- an adapted alignment;
compat :: Zipper (CompoundCnstr fam prim x) (SFix fam prim) (Aligned fam prim) x
       -> Aligned fam prim x
       -> MergeM fam prim (Aligned fam prim x , Aligned fam prim x)
compat (Zipper zip h) (Del (Zipper zip' h')) = _ 
compat (Zipper zip h) (Spn rep) = _ 




{-

-- |This is specific to merging; which is why we left it here.
-- When instantiatting a deletion context against a patch,
-- we do /not/ fail when the deletion context requires something
-- but the patch is a permutation.
instM :: forall fam prim at  
       . Holes fam prim (MetaVar fam prim) at
      -> Patch fam prim at
      -> ExceptT String (MergeM fam prim) ()
instM p = void . holesMapM (\h -> uncurry' go h >> return h) . lcp p
  where
    go :: Holes fam prim (MetaVar fam prim) ix
       -> Patch fam prim ix
       -> ExceptT String (MergeM fam prim) ()
    go (Hole v) x = do
      iota <- get
      case instAdd iota v x of
        Just iota' -> put iota'
        Nothing    -> throwError $ "Failed contraction: " ++ show (metavarGet v)
    go _ (Hole (Chg (Hole _) (Hole _))) = return ()
    go _ (Hole _)                       = throwError $ "Conflict"
    go _ _ = throwError $ "Symbol Clash"


type MergeState fam prim = Inst (Patch fam prim)

mergeState0 :: MergeState fam prim
mergeState0 = M.empty

type MergeM fam prim = State (MergeState fam prim)

data Conflict :: [*] -> [*] -> * -> * where
  FailedContr :: [Exists (MetaVar fam prim)]
              -> Conflict fam prim at
  
  Conflict :: String
           -> Chg fam prim at
           -> Chg fam prim at
           -> Conflict fam prim at

data Phase2 :: [*] -> [*] -> * -> * where
  -- |A instantiation needs to be done after we completed the information
  --  discovery phase.
  P2Instantiate :: Chg fam prim at
                -> Phase2 fam prim at
  
  -- |Sometimes we must decide whether we are looking into the same change or not.
  P2TestEq      :: Chg fam prim at
                -> Chg fam prim at
                -> Phase2 fam prim at

type C ki fam codes at = (EqHO ki , TestEquality ki)

merge :: Patch fam prim at
      -> Patch fam prim at
      -> Holes fam prim (Sum (Conflict fam prim) (Chg fam prim)) at
merge oa ob =
  let oab          = lcp oa ob
      (aux , inst) = runState (holesMapM (uncurry' phase1) oab) M.empty
   in case makeDelInsMaps inst of
        Left  vs -> Hole (InL $ FailedContr vs)
        Right di -> holesMap (phase2' di) aux

-- |A 'PatchC' is a patch with potential conflicts inside
type PatchC fam prim at
  = Holes fam prim (Sum (Conflict fam prim) (Chg fam prim)) at

noConflicts :: PatchC fam prim ix -> Maybe (Patch fam prim ix)
noConflicts = holesMapM rmvInL
  where
    rmvInL (InL _) = Nothing
    rmvInL (InR x) = Just x

getConflicts :: PatchC fam prim ix -> [Exists (Conflict fam prim)]
getConflicts = foldr act [] . holesHolesList
  where
    act :: Exists (Sum (Conflict fam prim) (Chg fam prim))
        -> [Exists (Conflict fam prim)]
        -> [Exists (Conflict fam prim)]
    act (Exists (InR _)) = id
    act (Exists (InL c)) = (Exists c :)

diff3 :: forall fam prim ix
       . Patch fam prim ix
      -> Patch fam prim ix
      -> PatchC fam prim ix
diff3 oa ob = merge oa (ob `withFreshNamesFrom` oa)

type Subst2 fam prim = ( Subst fam prim (MetaVar fam prim)
                       , Subst fam prim (MetaVar fam prim))

makeDelInsMaps :: forall fam prim
                . MergeState fam prim
               -> Either [Exists (MetaVar fam prim)]
                         (Subst2 fam prim)
makeDelInsMaps iota =
  let sd = M.toList $ M.map (exMap $ holesJoin . holesMap chgDel) iota
      si = M.toList $ M.map (exMap $ holesJoin . holesMap chgIns) iota
   in do
    d <- trace ("D:\n" ++ unlines (map show sd)) $ minimize (toSubst sd)
    i <- trace ("I:\n" ++ unlines (map show si)) $ minimize (toSubst si)
    
    return (d , i)
 where
   toSubst :: [(Int , Exists (Holes fam prim (MetaVar fam prim)))]
           -> Subst fam prim (MetaVar fam prim)
   toSubst = M.fromList
           . map (\(i , Exists h) -> (Exists (mkVar i h) , Exists h))

   mkVar :: Int -> Holes fam prim (MetaVar fam prim) at -> MetaVar fam prim at
   mkVar vx (Prim _) = MV_Prim vx
   mkVar vx (Hole v) = metavarSet vx v
   mkVar vx (Roll _) = MV_Comp vx
        
phase2' :: Subst2 fam prim
        -> Sum (Conflict fam prim) (Phase2 fam prim) at
        -> Sum (Conflict fam prim) (Chg fam prim) at
phase2' _  (InL c) = InL c
phase2' di (InR x) = phase2 di x


phase2 :: Subst2 fam prim
       -> Phase2 fam prim at
       -> Sum (Conflict fam prim) (Chg fam prim) at
phase2 di (P2Instantiate chg) = InR $ chgrefine di chg
phase2 di (P2TestEq ca cb)    = chgeq di ca cb

chgrefine :: Subst2 fam prim
          -> Chg fam prim at
          -> Chg fam prim at
chgrefine (d , i) (Chg del ins) =
  let del' = substApply d del
      ins' = substApply i ins
   in Chg del' ins'

chgeq :: Subst2 fam prim
      -> Chg fam prim at
      -> Chg fam prim at
      -> Sum (Conflict fam prim) (Chg fam prim) at
chgeq di ca cb = 
  let ca' = chgrefine di ca
      cb' = chgrefine di cb
  in if changeEq ca' cb'
     then InR ca'
     else InL (Conflict "not-eq" ca' cb')


phase1 :: Patch fam prim at
       -> Patch fam prim at
       -> MergeM fam prim (Sum (Conflict fam prim) (Phase2 fam prim) at)
phase1 ca cb = do
  r <- runExceptT $ trace ("phase1:\n" ++ show ca ++ "\n" ++ show cb) (discover ca cb)
  return $ case r of
    Left err -> InL (Conflict err ca' cb')
    Right p2 -> InR p2
 where
   ca' = chgDistr ca
   cb' = chgDistr cb


discover :: Patch fam prim at
         -> Patch fam prim at
         -> ExceptT String (MergeM fam prim) (Phase2 fam prim at)
discover (Hole ca) (Hole cb) = recChgChg ca cb
discover ca        (Hole cb) = recApp    cb ca
discover (Hole ca) cb        = recApp    ca cb
discover _          _        = throwError "Not a span"
          
recChgChg :: Chg fam prim at
          -> Chg fam prim at
          -> ExceptT String (MergeM fam prim) (Phase2 fam prim at)
recChgChg ca cb
  | perm ca   = recApp ca (Hole cb)
  | perm cb   = recApp cb (Hole ca)
  | otherwise = return $ P2TestEq ca cb

recApp :: Chg fam prim at
       -> Patch fam prim at
       -> ExceptT String (MergeM fam prim) (Phase2 fam prim at)
recApp (Chg del ins) chg = do
  instM del chg
  return $ P2Instantiate (Chg del ins)
 

-}
