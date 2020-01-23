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
import           Data.List (partition)
----------------------------------------
import           GHC.Generics
import           Generics.Simplistic
import           Generics.Simplistic.Util
import           Generics.Simplistic.Unify
import           Generics.Simplistic.Zipper
----------------------------------------
import           Data.HDiff.MetaVar
import           Data.HDiff.Base
import           Data.HDiff.Instantiate
import           Data.HDiff.Merge.Align

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
                Left err -> InL $ Conflict err p q
                Right r  -> InR (disalign r)

-- Merging alignments might require merging changes; which
-- in turn requier a state.

type MergeState fam prim = Inst (Patch fam prim)
type MergeM     fam prim = StateT (MergeState fam prim) (Except String)

mrgSt0 :: MergeState fam prim
mrgSt0 = M.empty

mrg :: Aligned fam prim x -> Aligned fam prim x
    -> MergeM fam prim (Aligned fam prim x)
mrg p q = do
  phase1 <- mrg0 p qFresh
  inst <- get
  case makeDelInsMaps inst of
    Left vs  -> throwError "failed-contr"
    Right di -> alignedMapM (phase2 di) phase1
 where
    qFresh = q `withFreshNamesFrom'` p

  
{-
  let oab          = lcp oa ob
      (aux , inst) = runState (holesMapM (uncurry' phase1) oab) M.empty
   in case makeDelInsMaps inst of
        Left  vs -> Hole (InL $ FailedContr vs)
        Right di -> holesMap (phase2' di) aux
-}


mrg0 :: Aligned fam prim x -> Aligned fam prim x
    -> MergeM fam prim (Aligned' fam prim (Phase2 fam prim) x)
-- Insertions are preserved as long as they are not
-- simultaneous
mrg0 (Ins _) (Ins _)           = throwError "ins-ins"

mrg0 (Ins (Zipper zip p)) q    = Ins . Zipper zip <$> mrg0 p q
mrg0 p (Ins (Zipper zip q))    = Ins . Zipper zip <$> mrg0 p q

-- Deletions need to be checked for compatibility
mrg0 (Del p@(Zipper zip _)) q  = compat p q
                            >>= fmap (Del . Zipper zip) . uncurry mrg0
mrg0 p (Del q@(Zipper zip _))  = compat q p
                            >>= fmap (Del . Zipper zip) . uncurry mrg0 . swap
  where swap (x , y) = (y , x)

-- Modifications sould be instantiated, if possible.
mrg0 (Mod p) q = Mod <$> mrgChg p (disalign q)
mrg0 p (Mod q) = Mod <$> mrgChg (disalign p) q

-- This is the last case.
mrg0 (Spn p) (Spn q) = case zipSRep p q of
                        Nothing -> throwError "spn-spn"
                        Just r  -> Spn <$> repMapM (uncurry' mrg0) r



-- Spines and Changes

isCpy :: Chg fam prim x -> Bool
isCpy (Chg (Hole v) (Hole u)) = metavarGet v == metavarGet u
isCpy _                       = False

-- |Checks that a deletion is compatible with an alignment; if so, returns
-- an adapted alignment;
compat :: Zipper (CompoundCnstr fam prim x) (SFix fam prim) (Aligned fam prim) x
       -> Aligned fam prim x
       -> MergeM fam prim (Aligned fam prim x , Aligned fam prim x)
compat (Zipper zip h) (Del (Zipper zip' h'))
  | zip == zip' = return (h , h')
  | otherwise   = throwError "del-del"
compat (Zipper zip h) (Mod chg)
  | isCpy chg = return (h , Mod chg) 
  | otherwise = throwError "del-mod"
compat (Zipper zip h) (Spn rep) =
  case zipperRepZip zip rep of
    Nothing -> throwError "del-spn-1"
    Just r  -> let hs = repLeavesList r
                in case partition (exElim isInR1) hs of
                     ([Exists (InL Refl :*: x)] , xs)
                       | all isCpyL1 xs -> return (h , x)
                       | otherwise      -> throwError "del-spn-2"
                     _                  -> throwError "del-spn-3"
 where
   isInR1 :: (Sum a b :*: f) i -> Bool
   isInR1 (InL _ :*: _) = True
   isInR1 _             = False

   isCpyL1 :: Exists (Sum a b :*: Aligned fam prim) -> Bool
   isCpyL1 (Exists (_ :*: a)) = isCpyA a

   isCpyA :: Aligned fam prim x -> Bool
   isCpyA (Mod c) = isCpy c -- TODO: what if c is a contraction or duplication?
   isCpyA (Spn r) = all (exElim isCpyA) (repLeavesList r)
   isCpyA _       = False


----------------------
-- Handling changes --
----------------------

data Phase2 :: [*] -> [*] -> * -> * where
  -- |A instantiation needs to be done after we completed the information
  --  discovery phase.
  P2Instantiate :: Chg fam prim at
                -> Phase2 fam prim at
  
  -- |Sometimes we must decide whether we are looking into the same change or not.
  P2TestEq      :: Chg fam prim at
                -> Chg fam prim at
                -> Phase2 fam prim at

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
    d <- minimize (toSubst sd)
    i <- minimize (toSubst si)
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

mrgChg :: Chg fam prim x -> Chg fam prim x
       -> MergeM fam prim (Phase2 fam prim x)
mrgChg (Chg dp ip) (Chg dq iq) = do
  -- TODO; this was the core issue before; what guarantees I don't have it
  -- now? I need to look into this.
  discover (holesMap (uncurry' Chg) $ lcp dp ip)
           (holesMap (uncurry' Chg) $ lcp dq iq)
  

phase2 :: Subst2 fam prim
       -> Phase2 fam prim at
       -> MergeM fam prim (Chg fam prim at)
phase2 di (P2Instantiate chg) = return $ chgrefine di chg
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
      -> MergeM fam prim (Chg fam prim at)
chgeq di ca cb = 
  let ca' = chgrefine di ca
      cb' = chgrefine di cb
  in if changeEq ca' cb'
     then return ca'
     else throwError "not-eq"



{-


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

diff3 :: forall fam prim ix
       . Patch fam prim ix
      -> Patch fam prim ix
      -> PatchC fam prim ix
diff3 oa ob = merge oa (ob `withFreshNamesFrom` oa)

        
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
-}

discover :: Patch fam prim at
         -> Patch fam prim at
         -> MergeM fam prim (Phase2 fam prim at)
discover (Hole ca) (Hole cb) = recChgChg ca cb
discover ca        (Hole cb) = recApp    cb ca
discover (Hole ca) cb        = recApp    ca cb
discover _          _        = throwError "Not a span"
          
recChgChg :: Chg fam prim at
          -> Chg fam prim at
          -> MergeM fam prim (Phase2 fam prim at)
recChgChg ca cb
  | perm ca   = recApp ca (Hole cb)
  | perm cb   = recApp cb (Hole ca)
  | otherwise = return $ P2TestEq ca cb

recApp :: Chg fam prim at
       -> Patch fam prim at
       -> MergeM fam prim (Phase2 fam prim at)
recApp (Chg del ins) chg = do
  instM del chg
  return $ P2Instantiate (Chg del ins)
 
-- |This is specific to merging; which is why we left it here.
-- When instantiatting a deletion context against a patch,
-- we do /not/ fail when the deletion context requires something
-- but the patch is a permutation.
instM :: forall fam prim at  
       . Holes fam prim (MetaVar fam prim) at
      -> Patch fam prim at
      -> MergeM fam prim ()
instM p = void . holesMapM (\h -> uncurry' go h >> return h) . lcp p
  where
    go :: Holes fam prim (MetaVar fam prim) ix
       -> Patch fam prim ix
       -> MergeM fam prim ()
    go (Hole v) x = do
      iota <- get
      case instAdd iota v x of
        Just iota' -> put iota'
        Nothing    -> throwError $ "Failed contraction: " ++ show (metavarGet v)
    go _ (Hole (Chg (Hole _) (Hole _))) = return ()
    go _ (Hole _)                       = throwError $ "Conflict"
    go _ _ = throwError $ "Symbol Clash"

