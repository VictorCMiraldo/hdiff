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
import           Control.Monad.Writer hiding (Sum)
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


import           Generics.Simplistic.Pretty
import           Data.HDiff.Show
import           Data.Text.Prettyprint.Doc hiding (align)
import           Data.Text.Prettyprint.Doc.Render.Terminal
import Debug.Trace
--trace :: x -> a -> a
--trace _ = id

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
      ob' = align (ob `withFreshNamesFrom` oa)
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

data MergeState fam prim = MergeState
  { iota :: Inst (Patch fam prim)
  , eqs  :: Subst fam prim (MetaVar fam prim)
  }
  
type MergeM     fam prim = StateT (MergeState fam prim) (Except String)

mrgSt0 :: MergeState fam prim
mrgSt0 = MergeState M.empty substEmpty

mrg :: Aligned fam prim x -> Aligned fam prim x
    -> MergeM fam prim (Aligned fam prim x)
mrg p q = do
  phase1 <- mrg0 p q
  inst <- get
  case makeDelInsMaps inst of
    Left vs  -> throwError ("failed-contr: " ++ show (map (exElim metavarGet) vs))
    Right di -> alignedMapM (phase2 di) phase1

  
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
mrg0 (Del p@(Zipper zip _)) q = compat p q
                            >>= fmap (Del . Zipper zip) . uncurry mrg0
mrg0 p (Del q@(Zipper zip _)) = compat q p
                            >>= fmap (Del . Zipper zip) . uncurry mrg0 . swap
  where swap (x , y) = (y , x)

-- Spines mean that on one hand a constructor was copied; but the mod
-- indicates this constructor changed. Hence, we hace to try applying
-- the change to the spine at hand.
mrg0 (Mod p) (Spn q) = Mod <$>  mrgChgSpn p q
mrg0 (Spn p) (Mod q) = Mod <$>  mrgChgSpn q p

-- When we have two spines it is easy, just pointwise merge their
-- recursive positions
mrg0 (Spn p) (Spn q) = case zipSRep p q of
                        Nothing -> throwError "spn-spn"
                        Just r  -> Spn <$> repMapM (uncurry' mrg0) r

-- Modifications sould be instantiated, if possible.
mrg0 (Mod p) (Mod q) = Mod <$> mrgChgChg p q



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
makeDelInsMaps (MergeState iot eqvs) =
  let sd = M.toList $ M.map (exMap $ holesJoin . holesMap chgDel) iot
      si = M.toList $ M.map (exMap $ holesJoin . holesMap chgIns) iot
   in do
    d <- minimize (toSubst $ sd)
    i <- minimize (toSubst $ si)
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

isPerm :: Chg fam prim x -> Bool
isPerm (Chg (Hole _) (Hole _)) = True
isPerm _ = False

instance ShowHO (MetaVar fam prim) where
  showHO = ('#':) . show . metavarGet

mrgChgChg :: Chg fam prim x -> Chg fam prim x
          -> MergeM fam prim (Phase2 fam prim x)
-- Changes must have unifiable domains
mrgChgChg p q =
  case runExcept (unify (chgDel p) (chgDel q)) of
    Left err -> throwError "chg-unif"
    Right r  -> trace ("r = " ++ show (M.toList r))
              $ modify (\s -> s { eqs = M.union (eqs s) r})
             >> mrgChgChg' p q
  


mrgChgChg' :: Chg fam prim x -> Chg fam prim x
           -> MergeM fam prim (Phase2 fam prim x)
mrgChgChg' p q 
 | isPerm p = mrgChgPrm p q
 | isPerm q = mrgChgPrm q p
 | otherwise =
   trace (unlines
         ["chg-chg"
         ,"chg = " ++ show p
         ,"chg = " ++ show q
         , ""
         ])
   $ do return (P2TestEq p q)


mrgChgPrm :: Chg fam prim x -> Chg fam prim x
          -> MergeM fam prim (Phase2 fam prim x)
mrgChgPrm perm@(Chg dp ip) q = 
 trace (unlines
       ["chg-perm"
       ,"perm = " ++ show perm
       ,"chg  = " ++ show q
       , ""
       ])
 $ do
  exs <- instM dp (Hole q)
  return $ P2Instantiate perm
   
mrgChgSpn :: (CompoundCnstr fam prim x)
          => Chg fam prim x -> SRep (Aligned fam prim) (Rep x)
          -> MergeM fam prim (Phase2 fam prim x)
mrgChgSpn p@(Chg dp ip) spn =
 trace (unlines
       ["chg-spn"
       ,"chg = " ++ show p
       ,"spn = " ++ show spn
       , ""
       ])
 $ do
  exs <- instM dp (chgPatch $ disalign $ Spn spn)
  -- Now, we look into exs; where we have places where dp required
  -- some structure, but spn had a change. In case this change's domain
  -- is compatible, we are happy.
  flip mapM_ exs $ \(Exists (v :*: chg)) -> do
    case chg of
      Chg (Hole vd) (Hole vi)
        | metavarGet vd == metavarGet vi -> return ()
        | otherwise                      -> trace "ip" $ throwError "inst-perm"
      _ -> trace "ic" $ throwError "inst-chg"
  return (P2Instantiate p)

instM :: forall fam prim at  
       . HolesMV fam prim at
      -> Patch fam prim at
      -> MergeM fam prim [Exists (HolesMV fam prim :*: Chg fam prim)]
instM p q = do
  (_ , exs) <- runWriterT (holesMapM (\h -> uncurry' go h >> return h) $ lcp p q)
  return exs
  where
    go :: HolesMV fam prim ix
       -> Patch fam prim ix
       -> WriterT [Exists (HolesMV fam prim :*: Chg fam prim)]
                  (MergeM fam prim) ()
    go (Hole v) x = do
      i <- gets iota
      case instAdd i v x of
        Just iota' -> modify (\st -> st { iota = iota' })
        Nothing    -> throwError "contr"
    go p (Hole d) = tell [Exists $ p :*: d]
    go _ _ = throwError "symb"


phase2 :: Subst2 fam prim
       -> Phase2 fam prim at
       -> MergeM fam prim (Chg fam prim at)
phase2 di (P2Instantiate chg) = eqvs (chgrefine di chg)
phase2 di (P2TestEq ca cb)    = chgeq di ca cb >>= eqvs

eqvs :: Chg fam prim at
     -> MergeM fam prim (Chg fam prim at)
eqvs (Chg d i) = do
  es <- gets eqs
  return (Chg (substApply es d) (substApply es i))

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

------------
-- Pretty -- 


instance Show (PatchC fam prim x) where
  show = myRender . holesPretty go
    where
      go x = case x of
               InL c -> confPretty c
               InR c -> chgPretty c

confPretty :: Conflict fam prim x
           -> Doc AnsiStyle
confPretty (FailedContr vars)
  = group (pretty "{!!" <+> sep (map (pretty . exElim metavarGet) vars) <+> pretty "!!}")
confPretty (Conflict lbl c d)
  = vcat [ pretty "{!! >>>>>>>" <+> pretty lbl <+> pretty "<<<<<<<"
         , alignedPretty c
         , pretty "==========="
         , alignedPretty d
         , pretty ">>>>>>>" <+> pretty lbl <+> pretty "<<<<<<< !!}"]

