{-# LANGUAGE KindSignatures        #-}
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
{-# LANGUAGE MultiWayIf            #-}
{-# LANGUAGE CPP                   #-}
{-# OPTIONS_GHC -Wno-orphans       #-}
module Data.HDiff.Merge where

import           Control.Monad.Cont
import           Control.Monad.State
import           Control.Monad.Except
import           Control.Monad.Writer hiding (Sum)
import           Data.Functor.Const
import qualified Data.Map as M
import           Data.Type.Equality
import           Data.List (partition, foldl')
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
import           Data.HDiff.Diff.Align


import           Generics.Simplistic.Pretty
import           Data.HDiff.Show
import           Data.Text.Prettyprint.Doc hiding (align)
import           Data.Text.Prettyprint.Doc.Render.Terminal

import Unsafe.Coerce 

#define DEBUG_MERGE
#ifdef DEBUG_MERGE
import Debug.Trace
#else
trace :: x -> a -> a
trace _ = id
#endif

mkDbgString :: String -> String -> String -> String -> String
mkDbgString ca cb stra strb =
  unlines [ca ++ "-" ++ cb
          ,"  " ++ ca ++ " = " ++ stra
          ,"  " ++ cb ++ " = " ++ strb
          , ""]

data Conflict :: [*] -> [*] -> * -> * where
  FailedContr :: [Exists (MetaVar kappa fam)]
              -> Conflict kappa fam at
  
  Conflict :: String
           -> Aligned kappa fam at
           -> Aligned kappa fam at
           -> Conflict kappa fam at

-- |A 'PatchC' is a patch with potential conflicts inside
type PatchC kappa fam at
  = Holes kappa fam (Sum (Conflict kappa fam) (Chg kappa fam)) at

noConflicts :: PatchC kappa fam ix -> Maybe (Patch kappa fam ix)
noConflicts = holesMapM rmvInL
  where
    rmvInL (InL _) = Nothing
    rmvInL (InR x) = Just x

getConflicts :: PatchC kappa fam ix -> [Exists (Conflict kappa fam)]
getConflicts = foldr act [] . holesHolesList
  where
    act :: Exists (Sum (Conflict kappa fam) (Chg kappa fam))
        -> [Exists (Conflict kappa fam)]
        -> [Exists (Conflict kappa fam)]
    act (Exists (InR _)) = id
    act (Exists (InL c)) = (Exists c :)

diff3 :: forall kappa fam ix
       . (HasDecEq fam)
      => Patch kappa fam ix
      -> Patch kappa fam ix
      -> PatchC kappa fam ix
-- Since patches are well-scoped (again! yay! lol)
-- we can map over the anti-unif for efficiency purposes.
diff3 oa ob =
  let oa' = align oa
      ob' = align (ob `withFreshNamesFrom` oa)
   in holesMap (uncurry' mergeAl . delta alignDistr) $ lcp oa' ob'
 where
   delta f (x :*: y) = (f x :*: f y)

mergeAl :: Aligned kappa fam x -> Aligned kappa fam x
        -> Sum (Conflict kappa fam) (Chg kappa fam) x
mergeAl p q = case runExcept (evalStateT (mrg p q) mrgSt0) of
                Left err -> InL $ Conflict err p q
                Right r  -> InR (disalign r)

-- Merging alignments might require merging changes; which
-- in turn requier a state.

-- |Well be keeping three maps in our state.
--
--  1. 'wasMap': tells us that some variable was equivalent to some term.
--     is carries information about the past.
--
--  2. 'becameMap': tells us some variable became a term; it
--     carries information about the future.
--
--  3. 'eqvsMap': is a map of variable equivalences; whenever
--  we discover a variable was equivalent to a term that
--  consists in a single variable, then they are the same term.
--
--
data MergeState kappa fam = MergeState
  { wasMap    :: Subst kappa fam (MetaVar kappa fam)
  , becameMap :: Subst kappa fam (MetaVar kappa fam)
  , varEqvs   :: [Exists (MetaVar kappa fam :*: MetaVar kappa fam)]
  }
type MergeM     kappa fam = StateT (MergeState kappa fam) (Except String)

mrgSt0 :: MergeState kappa fam
mrgSt0 = MergeState substEmpty substEmpty []

onBecame :: (Subst kappa fam (MetaVar kappa fam) -> Subst kappa fam (MetaVar kappa fam))
         -> MergeM kappa fam ()
onBecame f = modify (\st -> st { becameMap = f (becameMap st) })

-- |Whenever we unify two deletion contexts we gather
-- eqs and wasMap entries; this functions makes it esyo to manage that.
gatherWas :: HolesMV kappa fam at
          -> HolesMV kappa fam at
          -> MergeM kappa fam ()
gatherWas t u =
  case runExcept $ unify t u of
    Left err    -> throwError "not-a-span"
    Right sigma -> let (eqvs , was) = splitVarEqs sigma
                    in modify (\st -> st { wasMap  = M.union was (wasMap st)
                                         , varEqvs = eqvs ++ varEqvs st
                                         })


mrg :: Aligned kappa fam x -> Aligned kappa fam x
    -> MergeM kappa fam (Aligned kappa fam x)
mrg p q = do
  phase1 <- mrg0 p q
  st     <- get
  case makeDelInsMaps st of
    Left vs  -> throwError ("failed-contr: " ++ show (map (exElim metavarGet) vs))
    Right di -> alignedMapM (phase2 di) phase1
 where
   dbgMap :: String -> Subst kappa fam (MetaVar kappa fam) -> String
   dbgMap lbl m = unlines $
     [ lbl ++ ": " ++ show v ++ " => " ++ show c | (v , c) <- M.toList m ]


makeDelInsMaps :: forall kappa fam
                . MergeState kappa fam
               -> Either [Exists (MetaVar kappa fam)]
                         (Subst2 kappa fam)
makeDelInsMaps (MergeState was bec eqv) = do
  let eqvMap = substFromVarEqs eqv
  trace (unlines [ dbgMap "was" was
                 , dbgMap "eqv" eqvMap
                 , dbgMap "became" bec])
    $ do was' <- M.union eqvMap <$> minimize was
         bec' <- M.union eqvMap <$> minimize bec
         trace (unlines [ "%%%" , dbgMap "was'" was' , dbgMap "bec'" bec'])
           (return (was' , bec'))
 where
   dbgMap :: String -> Subst kappa fam (MetaVar kappa fam) -> String
   dbgMap lbl m = unlines $
     [ lbl ++ ": " ++ show v ++ " => " ++ show c | (v , c) <- M.toList m ]



{-
 do
  phase1 <- mrg0 p q
  insts  <- get
  case makeDelInsMaps insts of
    Left vs  -> throwError ("failed-contr: " ++ show (map (exElim metavarGet) vs))
    Right di -> alignedMapM (phase2 di) phase1
-}

mrg0 :: Aligned kappa fam x
     -> Aligned kappa fam x
     -> MergeM kappa fam (Aligned' kappa fam (Phase2 kappa fam) x)
-- Copies are the easiest case
mrg0 (Cpy x) q = Mod <$> mrgCpy x (disalign q)
mrg0 p (Cpy x) = Mod <$> mrgCpy x (disalign p)

-- Permutations are almost as simple as copies
-- mrg0 (Prm x y) (Prm x' y') = Mod <$> mrgPrmPrm x y x' y'
mrg0 (Prm x y) q = Mod <$> mrgPrm x y (disalign q)
mrg0 p (Prm x y) = Mod <$> mrgPrm x y (disalign p)

-- Insertions are preserved as long as they are not
-- simultaneous.
mrg0 (Ins (Zipper zip p)) (Ins (Zipper zip' q))
  | zip == zip' = Ins . Zipper zip <$> mrg0 p q
  | otherwise   = throwError "ins-ins"

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

-- |Checks that a deletion is compatible with an alignment; if so, returns
-- an adapted alignment;
compat :: Zipper (CompoundCnstr kappa fam x) (SFix kappa fam) (Aligned kappa fam) x
       -> Aligned kappa fam x
       -> MergeM kappa fam (Aligned kappa fam x , Aligned kappa fam x)
compat (Zipper zip h) (Del (Zipper zip' h'))
  | zip == zip' = return (h , h')
  | otherwise   = throwError "del-del"
-- Here we know chg is incompatibile; If it did not touch any
-- of the recursive places fixed by 'zip' it would have been
-- recognized as a deletion; if can't be a copy or a pemrutation
-- because it is not flagged as such (and we handled those above!)
compat (Zipper zip h) (Mod chg) = throwError "del-mod"
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

   isCpyL1 :: Exists (Sum a b :*: Aligned kappa fam) -> Bool
   isCpyL1 (Exists (_ :*: a)) = isCpyA a

   isCpyA :: Aligned kappa fam x -> Bool
   isCpyA (Cpy _) = True
   isCpyA (Spn r) = all (exElim isCpyA) (repLeavesList r)
   isCpyA _       = False

-----------------------
-- Preparing Phase 2 --
-----------------------

data Phase2 :: [*] -> [*] -> * -> * where
  -- |A instantiation needs to be done after we completed the information
  --  discovery phase.
  P2Instantiate :: Chg kappa fam at
                -> Phase2 kappa fam at

  P2Instantiate' :: Chg kappa fam at
                 -> HolesMV kappa fam at
                 -> Phase2 kappa fam at
  
  -- |Sometimes we must decide whether we are looking into the same change or not.
  P2TestEq      :: Chg kappa fam at
                -> Chg kappa fam at
                -> Phase2 kappa fam at

type Subst2 kappa fam = ( Subst kappa fam (MetaVar kappa fam)
                       , Subst kappa fam (MetaVar kappa fam))

-- |Subtree @x@ was copied but changd through @chg@;
-- we just instantiate @chg@
mrgCpy :: MetaVar kappa fam at -> Chg kappa fam at
       -> MergeM kappa fam (Phase2 kappa fam at)
mrgCpy _ chg = return $ P2Instantiate chg
{-
  trace (mkDbgString "cpy" "prm" (show x) (show chg))
   $ do i <- gets iota
        case instAdd i x (Hole chg) of
          Nothing -> error "inv-failure; cpy"
          Just i' -> modify (\s -> s { iota = i' })
                  >> return (P2Instantiate (Chg (Hole x) (Hole x)))
-}


{-
mrgPrmPrm :: MetaVar kappa fam x
          -> MetaVar kappa fam x
          -> MetaVar kappa fam x
          -> MetaVar kappa fam x
          -> MergeM kappa fam (Phase2 kappa fam x)
mrgPrmPrm x y x' y' =
  trace (mkDbgString "prm" "prm" (show x ++ " |-> " ++ show y) (show x' ++ " |-> " ++ show y'))
   $ do -- let ins oldEs = substInsert (substInsert oldEs x (Hole x')) y (Hole y')
        let ins oldEs = substInsert oldEs x (Hole x') 
        onEqvs ins
        return (P2TestEq (Chg (Hole x) (Hole y)) (Chg (Hole x') (Hole y')))
-}

-- |Subtree @x@ was swapped with subtree @y@ but at the same time
-- was changed by @c@; in this case, we will gather constraints
-- from unifying @x@ and @c@ and instantiate @Chg (chgDel c) y@
mrgPrm :: MetaVar kappa fam x
       -> MetaVar kappa fam x
       -> Chg kappa fam x
       -> MergeM kappa fam (Phase2 kappa fam x)
mrgPrm x y c = 
  trace (mkDbgString "prm" "chg" (show x ++ " |-> " ++ show y) (show c))
    $ do gatherWas (Hole x) (chgDel c)
         return $ P2Instantiate (Chg (chgDel c) (Hole y)) -- (chgIns c?)
{-
    $ do i <- gets iota
         case instAdd i x (Hole c) of
           Nothing -> error "inv-failure; inst"
           Just i' -> modify (\s -> s { iota = i' })
                   >> return (P2Instantiate' (Chg (Hole x) (Hole y)) (chgIns c))
-}

-- auxiliar predicate
isDup :: Chg kappa fam x -> Bool
isDup (Chg (Hole _) (Hole _)) = True
isDup _ = False

mrgChgChg :: Chg kappa fam x -> Chg kappa fam x
          -> MergeM kappa fam (Phase2 kappa fam x)
-- Changes must have unifiable domains
mrgChgChg p q = do
  gatherWas (chgDel p) (chgDel q)
  if | isDup p   -> mrgChgDup p q
     | isDup q   -> mrgChgDup q p
     | otherwise -> return (P2TestEq p q)
 where
   mrgChgDup :: Chg kappa fam x -> Chg kappa fam x
             -> MergeM kappa fam (Phase2 kappa fam x)
   mrgChgDup dup@(Chg (Hole v) (Hole u)) q = 
    trace (mkDbgString "chg" "dup" (show q) (show dup))
      $ do onBecame (\n -> substInsert n v (chgIns q))
           return $ P2Instantiate (Chg (chgDel q) (Hole u))
{-
 | isDup p = mrgChgDup p q
 | isDup q = mrgChgDup q p
 | otherwise =
   trace (mkDbgString "chg" "chg" (show p) (show q)) 
   $ case runExcept (unify (chgDel p) (chgDel q)) of
      Left err -> throwError "chg-unif"
      Right r  -> onEqvs (M.union r)
               >> return (P2TestEq p q)
-}

{-
  $ do i <- gets iota
       case instAdd i v (Hole q) of
         Nothing -> throwError "chg-dup"
         Just i' -> modify (\s -> s { iota = i' })
                 >> return (P2Instantiate dup)
-}

mrgChgSpn :: (CompoundCnstr kappa fam x)
          => Chg kappa fam x -> SRep (Aligned kappa fam) (Rep x)
          -> MergeM kappa fam (Phase2 kappa fam x)
mrgChgSpn p@(Chg dp ip) spn =
 trace (mkDbgString "chg" "spn" (show p) (show spn))
   $ instM dp (Spn spn) >> return (P2Instantiate' p (chgIns $ disalign $ Spn spn))


instM :: forall kappa fam at  
       . HolesMV kappa fam at
      -> Aligned kappa fam at
      -> MergeM kappa fam ()
-- instantiating over a copy is fine; 
instM _ (Cpy _)    = return ()

instM (Hole v) a =
  let da = disalign a
   in do gatherWas (Hole v) (chgDel da)
         onBecame (\n -> substInsert n v (chgIns da))
{-
  i <- gets iota
  case instAdd i v (Hole $ disalign a) of
    Nothing -> throwError "contr"
    Just i' -> modify (\st -> st { iota = i' })
-}

-- Instantiating over a modification might also be
-- possible in select cases; namelly, when the deletion
-- context has no variables, unifies with the deletion
-- context of the modification and both insert the
-- same thing. This is tricky to detect and I think
-- we overall need a better formalism to deal with
-- merging chgs over spines; I'm postponing this for now.
instM _ (Mod _) = throwError "inst-mod"

-- instantiating over a permutation if we are not immediatly
-- matching is tricky. I will be conservative and
-- raise a conflit. I suspect we can do better though.
-- For example; register that the deletion of x must be d
-- and return whatever we found about the insertion of y at this very
-- place; but this is difficult.
instM d (Prm _ _) = throwError "inst-perm"

instM x@(Prim _) d
  | x == chgDel (disalign d) = return ()
  | otherwise                = throwError "symbol-clash"

instM (Roll r) (Ins _) = throwError "chg-ins"
instM (Roll r) (Del _) = throwError "chg-del"
instM (Roll r) (Spn s) =
  case zipSRep r s of
    Nothing  -> throwError "constr-clash"
    Just res -> void $ repMapM (\x -> uncurry' instM x >> return x) res

{-


makeDelInsMaps :: forall kappa fam
                . MergeState kappa fam
               -> Either [Exists (MetaVar kappa fam)]
                         (Subst2 kappa fam)
makeDelInsMaps (MergeState iot eqvs) =
  let sd = M.toList $ M.map (exMap $ holesJoin . holesMap chgDel) iot
      si = M.toList $ M.map (exMap $ holesJoin . holesMap chgIns) iot
   in trace (oneStr "eqvs" eqvs) $ do
    d <- trace (oneStr "sd" $ toSubst sd) (minimize (addEqvs (toSubst sd)))
    i <- trace (oneStr "si" $ toSubst si) (minimize (addEqvs (toSubst si)))
    trace (diStr (d , i))
      return (d , i)
 where
   toSubst :: [(Int , Exists (Holes kappa fam (MetaVar kappa fam)))]
           -> Subst kappa fam (MetaVar kappa fam)
   toSubst = M.fromList
           . map (\(i , Exists h) -> (Exists (mkVar i h) , Exists h))

   mkVar :: Int -> Holes kappa fam (MetaVar kappa fam) at -> MetaVar kappa fam at
   mkVar vx (Prim _) = MV_Prim vx
   mkVar vx (Hole v) = metavarSet vx v
   mkVar vx (Roll _) = MV_Comp vx

   diStr :: Subst2 kappa fam -> String
   diStr (d , i) = unlines $
     [ "del-map: " ++ show v ++ ": " ++ show c | (v , c) <- M.toList d ] ++
     [ "ins-map: " ++ show v ++ ": " ++ show c | (v , c) <- M.toList i ]

   oneStr :: String -> Subst kappa fam (MetaVar kappa fam) -> String
   oneStr lbl d = unlines $
     [ "[" ++ lbl ++ "] " ++ show v ++ ": " ++ show c | (v , c) <- M.toList d ]

   -- TODO: moev this to unification; call it substToList.
   eqvsL = [ Exists (u :*: unsafeCoerce v) | (Exists u , Exists (Hole v)) <- M.toList eqvs]

   -- We only insert the equivalences when we don't yet have data about these
   -- variables in whatever map we are complementing
   addEqvs :: Subst kappa fam (MetaVar kappa fam)
           -> Subst kappa fam (MetaVar kappa fam)
   addEqvs s = let go k = foldl' k s eqvsL
                in go $ \s' (Exists (v :*: u)) 
                        -> if or (map (`M.member` s') [ Exists v , Exists u ])
                           then s'
                           else substInsert s' v (Hole u)

-}


phase2 :: Subst2 kappa fam
       -> Phase2 kappa fam at
       -> MergeM kappa fam (Chg kappa fam at)
phase2 di (P2TestEq ca cb) = chgeq di ca cb
phase2 di (P2Instantiate chg) =
  trace ("p2-inst:\n  " ++ show chg) $
    return (chgrefine di chg)
{-
phase2 di (P2Instantiate' chg i) =
  trace ("p2-inst-and-chk:\n  i = " ++ show i ++ "\n  c = " ++ show chg) $
    do es <- gets eqs
       case getCommonVars (substApply es (chgIns chg)) (substApply es i) of
           [] -> return $ chgrefine di chg
           xs -> throwError ("mov-mov " ++ show xs)
 where
   getCommonVars :: HolesMV kappa fam at -> HolesMV kappa fam at -> [Int]
   getCommonVars x y =
     let vx = holesVars x
         vy = holesVars y
      in M.keys (M.intersection vx vy)
-}

chgrefine :: Subst2 kappa fam
          -> Chg kappa fam at
          -> Chg kappa fam at
chgrefine (d , i) (Chg del ins) =
  let del' = substApply d del
      ins' = substApply i ins
   in Chg del' ins'

chgeq :: Subst2 kappa fam
      -> Chg kappa fam at
      -> Chg kappa fam at
      -> MergeM kappa fam (Chg kappa fam at)
chgeq di ca cb = 
  let ca' = chgrefine di ca
      cb' = chgrefine di cb
      r   = changeEq ca' cb'
  in trace ("p2-eq?:\n  ca = " ++ show ca' ++ "\n  cb = " ++ show cb' ++ "\n [" ++ show r ++ "]") $
     if r
     then return ca'
     else throwError "not-eq"

------------
-- Pretty -- 


instance Show (PatchC kappa fam x) where
  show = myRender . holesPretty go
    where
      go x = case x of
               InL c -> confPretty c
               InR c -> chgPretty c

confPretty :: Conflict kappa fam x
           -> Doc AnsiStyle
confPretty (FailedContr vars)
  = group (pretty "{!!" <+> sep (map (pretty . exElim metavarGet) vars) <+> pretty "!!}")
confPretty (Conflict lbl c d)
  = vcat [ pretty "{!! >>>>>>>" <+> pretty lbl <+> pretty "<<<<<<<"
         , alignedPretty c
         , pretty "==========="
         , alignedPretty d
         , pretty ">>>>>>>" <+> pretty lbl <+> pretty "<<<<<<< !!}"]


