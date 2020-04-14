{-# LANGUAGE UndecidableInstances #-}
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
{-# LANGUAGE CPP                   #-}
{-# OPTIONS_GHC -Wno-orphans       #-}
module Data.HDiff.Merge where

import           Control.Monad.Cont
import           Control.Monad.State
import           Control.Monad.Except
import qualified Data.Map as M
import           Data.Type.Equality
import           Data.List (partition)
----------------------------------------
import           GHC.Generics
import           Generics.Simplistic
import           Generics.Simplistic.Deep
import           Generics.Simplistic.Util
import           Generics.Simplistic.Unify
import           Generics.Simplistic.Zipper
----------------------------------------
import           Data.HDiff.MetaVar
import           Data.HDiff.Base
import           Data.HDiff.Diff.Align


import           Generics.Simplistic.Pretty
import           Data.HDiff.Show
import           Data.Text.Prettyprint.Doc hiding (align)
import           Data.Text.Prettyprint.Doc.Render.Terminal

import Unsafe.Coerce

-- #define DEBUG_MERGE
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

-- * Types and Auxiliary Definitions
--
-- $mergetypes

-- |A conflict signals a location in the source object
-- that was changed in two different ways.
-- There probably is a better way of identifying
-- conflicts in a more localized fashion, but this will work for now.
data Conflict :: [*] -> [*] -> * -> * where
  -- ^ A conflict carries a label about the issue
  --   and the the alignments that diverge in
  --   unreconcilable ways.
  Conflict :: String
           -> Al kappa fam at
           -> Al kappa fam at
           -> Conflict kappa fam at

-- |Extracts the label out of a conflict
conflictLbl :: Conflict kappa fam at -> String
conflictLbl (Conflict lbl _ _) = lbl

-- |A 'PatchC' is a patch with potential conflicts inside
type PatchC kappa fam at
  = Holes kappa fam (Sum (Conflict kappa fam) (Chg kappa fam)) at

-- |The core of the merge algorithm carries around
-- a map of decisions it made regarding how certain locations
-- have changed, in 'iota'; and also carries around a list
-- of equivalences it discovered, in 'eqs'.
data MergeState kappa fam = MergeState
  { iota :: Inst kappa fam
  , eqs  :: Subst kappa fam (MetaVar kappa fam)
  }

-- |Through the first phase of our merging algorithm we
-- collect information aout /how/ some subtrees have been changed.
-- This information is stored in this 'Inst' map.
type Inst kappa fam = M.Map (Exists (MetaVar kappa fam)) (Exists (Chg kappa fam))

-- |Empty merge state
mrgSt0 :: MergeState kappa fam
mrgSt0 = MergeState M.empty substEmpty

-- |Apply a function over the 'eqs' field of 'MergeState'
onEqvs :: (All Show kappa)
       => (Subst kappa fam (MetaVar kappa fam)
            -> Subst kappa fam (MetaVar kappa fam))
       -> MergeM kappa fam ()
onEqvs f = do
  e <- gets eqs
  let es' = f e
  trace ("eqvs = " ++ show es') (modify (\st -> st { eqs = es' }))

-- |The merge algorithm might fail with a conflict
-- or when the involved patches are not a span.
data MergeErr = NotASpan | Conf String

-- |Synonym for the merge monad.
type MergeM kappa fam = StateT (MergeState kappa fam)
                               (Except MergeErr)

-- |Makes it easier to throw conflicts
throwConf :: String -> MergeM kappa fam a
throwConf = throwError . Conf

-- |Records an invariant failure.
throwInvFailure :: MergeM kappa fam a
throwInvFailure = throwError NotASpan

-- |Attempts to insert a new point into an instantiation.
-- If @Patch kappa fam at@ is already associated to a value, ensure
-- it is the same as @x@. Note that we should really stick to
-- using 'instAdd' to manipulate instantiations as it forces
-- the metavariable and the element @Patch kappa fam@ to have the
-- same index.
instAdd :: (All Eq kappa)
        => Inst kappa fam -> MetaVar kappa fam at -> Chg kappa fam at
        -> Maybe (Inst kappa fam)
instAdd inst v x =
  case M.lookup (Exists v) inst of
     Just (Exists old)
       | eqHO x (unsafeCoerce old) -> return inst
       | otherwise                 -> Nothing
     Nothing
       -> Just $ M.insert (Exists v) (Exists x) inst

-- |Attempts to add a point to 'iota'; the string serves
-- as a label for throwing an error when this fails.
addToIota :: (All Eq kappa)
          => String -> MetaVar kappa fam at -> Chg kappa fam at
          -> MergeM kappa fam ()
addToIota errLbl v p = do
  i <- gets iota
  case instAdd i v p of
    Nothing -> throwConf errLbl
    Just i' -> modify (\st -> st { iota = i' })


-- |Casts a 'PatchC' into a 'Patch' in case no conflicts
-- have been found.
noConflicts :: PatchC kappa fam ix -> Maybe (Patch kappa fam ix)
noConflicts = holesMapM rmvInL
  where
    rmvInL (InL _) = Nothing
    rmvInL (InR x) = Just x

-- |Extracts the list of conflicts from a patch.
getConflicts :: PatchC kappa fam ix -> [Exists (Conflict kappa fam)]
getConflicts = foldr act [] . holesHolesList
  where
    act :: Exists (Sum (Conflict kappa fam) (Chg kappa fam))
        -> [Exists (Conflict kappa fam)]
        -> [Exists (Conflict kappa fam)]
    act (Exists (InR _)) = id
    act (Exists (InL c)) = (Exists c :)

-- * Diff3
--
-- $diff3

-- |@diff3 p q@ omputes a patch that attempts to reconcile
-- the differences from @p@ and @q@ into a single patch.
-- In the locations where this is not possible, we
-- place a conflict.
diff3 :: (All Show kappa , All Eq kappa)
      => Patch kappa fam ix -> Patch kappa fam ix
      -> Maybe (PatchC kappa fam ix)
diff3 oa ob =
  -- The first step is computing an alignment of
  -- oa; yet, we must care for the variables introduced
  -- by it; note how we align a /shifted/ version of ob
  -- to ensure no variable clashes.
  let (oa' , maxa) = align' oa
      ob'          = align (holesMap (chgShiftVarsBy maxa) ob)
   in holesMapM (uncurry' mergeAl . deltaMap alignDistr) $ lgg oa' ob'

-- |Attempts to merge two alignments. Assumes the alignments
-- have a disjoint set of variables.
mergeAl :: (All Show kappa , All Eq kappa)
        => Al kappa fam x -> Al kappa fam x
        -> Maybe (Sum (Conflict kappa fam) (Chg kappa fam) x)
mergeAl p q = case runExcept (evalStateT (mergeAlM p q) mrgSt0) of
                Left NotASpan   -> Nothing
                Left (Conf err) -> Just $ InL $ Conflict err p q
                Right r         -> Just $ InR (disalign r)

-- |Merging alignments is done in two phases.
-- A first phase is responsible for gathering equivalences,
-- making decisions about what to instantiate and issuing
-- commands that will be executed on a second phase; after
-- we process all of this gathered global information which
mergeAlM :: (All Show kappa , All Eq kappa)
         => Al kappa fam x -> Al kappa fam x -> MergeM kappa fam (Al kappa fam x)
mergeAlM p q = do
  phase1 <- mergePhase1 p q
  inst <- get
  case splitDelInsMaps inst of
    Left vs  -> throwConf ("failed-contr : " ++ show (map (exElim metavarGet) vs))
    Right di -> alMapM (phase2 di) phase1

-- |The second phase consists in going where 'mergePhase1' left
-- off and carrying one of three tasts.
data Phase2 :: [*] -> [*] -> * -> * where
  -- ^ Either we need to instantiate a given change with the
  --   updated information about how each subtree was individually altred.
  P2Instantiate :: Chg kappa fam at
                -> Maybe (HolesMV kappa fam at)
                -> Phase2 kappa fam at

  -- ^ Finally, when we cannot really reconcile we can at least try to
  --   check whether we are looking at the same change or not.
  P2TestEq      :: Chg kappa fam at
                -> Chg kappa fam at
                -> Phase2 kappa fam at


-- |Computes an alignment with leaves of type 'Phase2',
-- which enables us to map over and make decisions after
-- we have collected al the informatino.
mergePhase1 :: forall kappa fam x
             . (All Show kappa , All Eq kappa)
            => Al kappa fam x -> Al kappa fam x
            -> MergeM kappa fam (Al' kappa fam (Phase2 kappa fam) x)
mergePhase1 p q =
 case (p , q) of
   -- Copies are the easiest case; all we must do is
   -- instantiate the other change.
   (Cpy _ , _) -> return $ Mod $ P2Instantiate (disalign q) Nothing
   (_ , Cpy _) -> return $ Mod $ P2Instantiate (disalign p) Nothing

   -- Permutations are almost as simple as copies but
   -- do require some additional processing; we delegate to
   -- an auxiliary function
   (Prm x y, Prm x' y') -> Mod <$> mrgPrmPrm x y x' y'
   (Prm x y, _)         -> Mod <$> mrgPrm x y (disalign q)
   (_, Prm x y)         -> Mod <$> mrgPrm x y (disalign p)

   -- Insertions are preserved as long as they are not
   -- simultaneous.
   (Ins (Zipper z p'), Ins (Zipper z' q'))
     | z == z'   -> Ins . Zipper z <$> mergePhase1 p' q'
     | otherwise -> throwConf "ins-ins"
   (Ins (Zipper z p'), _) -> Ins . Zipper z <$> mergePhase1 p' q
   (_ ,Ins (Zipper z q')) -> Ins . Zipper z <$> mergePhase1 p q'

   -- Deletions need to be checked for compatibility: we try
   -- and "apply" the deletion to the other change, when we
   -- can safely delete the zipper from the other change
   -- we continue merge with the result and preserve the deletion.
   (Del zp@(Zipper z _), _) -> Del . Zipper z <$> (tryDel zp q >>= uncurry mergePhase1)
   (_, Del zq@(Zipper z _)) -> Del . Zipper z <$> (tryDel zq p >>= uncurry mergePhase1)

   -- Spines mean that on one hand a constructor was copied; but the mod
   -- indicates this constructor changed. Hence, we hace to try applying
   -- the change to the spine at hand.
   (Mod p', Spn q') -> Mod <$> mrgChgSpn p' q'
   (Spn p', Mod q') -> Mod <$> mrgChgSpn q' p'

   -- When we have two spines it is easy, just pointwise merge their
   -- recursive positions
   (Spn p', Spn q') -> case zipSRep p' q' of
       Nothing -> throwInvFailure
       Just r  -> Spn <$> repMapM (uncurry' mergePhase1) r

   -- Finally, modifications sould be instantiated, if possible.
   (Mod p', Mod q') -> Mod <$> mrgChgChg p' q'
 where
   mrgPrmPrm :: MetaVar kappa fam x
             -> MetaVar kappa fam x
             -> MetaVar kappa fam x
             -> MetaVar kappa fam x
             -> MergeM kappa fam (Phase2 kappa fam x)
   mrgPrmPrm x y x' y' =
     trace (mkDbgString "prm" "prm" (show x ++ " |-> " ++ show y)
                                    (show x' ++ " |-> " ++ show y'))
      $ do -- let ins oldEs = substInsert (substInsert oldEs x (Hole x')) y (Hole y')
           let ins oldEs = substInsert oldEs x (Hole x')
           onEqvs ins
           return (P2TestEq (Chg (Hole x) (Hole y)) (Chg (Hole x') (Hole y')))

   mrgPrm :: MetaVar kappa fam x
          -> MetaVar kappa fam x
          -> Chg kappa fam x
          -> MergeM kappa fam (Phase2 kappa fam x)
   mrgPrm x y c =
     trace (mkDbgString "prm" "chg" (show x ++ " |-> " ++ show y) (show c))
       $ addToIota "prm-chg" x c
       -- TODO: is this P2Instantiate' necessary? oesn't
       -- a P2Instantiate work?
       >> return (P2Instantiate (Chg (Hole x) (Hole y)) Nothing) -- (Just $ chgIns c))

   isDup :: Chg kappa fam x -> Bool
   isDup (Chg (Hole _) (Hole _)) = True
   isDup _ = False

   mrgChgChg :: Chg kappa fam x -> Chg kappa fam x
             -> MergeM kappa fam (Phase2 kappa fam x)
   -- Changes must have unifiable domains
   mrgChgChg p' q'
    | isDup p' = mrgChgDup p' q'
    | isDup q' = mrgChgDup q' p'
    | otherwise =
      trace (mkDbgString "chg" "chg" (show p') (show q'))
      $ case runExcept (unify (chgDel p') (chgDel q')) of
         Left _e  -> throwInvFailure
         Right r  -> onEqvs (M.union r)
                  >> return (P2TestEq p' q')

   mrgChgDup :: Chg kappa fam x -> Chg kappa fam x
             -> MergeM kappa fam (Phase2 kappa fam x)
   mrgChgDup dup@(Chg (Hole v) _) q' =
    trace (mkDbgString "chg" "dup" (show q') (show dup))
     $ addToIota "chg-dup" v q' >> return (P2Instantiate dup Nothing)
   mrgChgDup _ _ = error "imp: we did check with isDup' before calling"

   mrgChgSpn :: (CompoundCnstr kappa fam x)
             => Chg kappa fam x -> SRep (Al kappa fam) (Rep x)
             -> MergeM kappa fam (Phase2 kappa fam x)
   mrgChgSpn p'@(Chg dp _) spn =
    trace (mkDbgString "chg" "spn" (show p') (show spn))
      $ instM dp (Spn spn) >> return (P2Instantiate p' (Just $ chgIns $ disalign $ Spn spn))

-- |Checks whether we can /delete/ a zipper from an alignment.
-- For example, a zipper @Bin (Leaf 42) HOLE@ could be /deleted/
-- from a spine @Bin Cpy (Bin ...)@, and the result would be
-- overlaying whatever alignment is the continuation
-- of the deleton with the @Bin ...@ subtree.
tryDel :: (All Eq kappa)
       => Zipper (CompoundCnstr kappa fam x) (SFix kappa fam) (Al kappa fam) x
       -> Al kappa fam x
       -> MergeM kappa fam (Al kappa fam x , Al kappa fam x)
tryDel (Zipper z h) (Del (Zipper z' h'))
  | z == z'   = return (h , h')
  | otherwise = throwConf "del-del" -- never see this... why?
-- Here we know chg is incompatibile; If it did not touch any
-- of the recursive places fixed by 'zip' it would have been
-- recognized as a deletion; if can't be a copy or a pemrutation
-- because it is not flagged as such (and we handled those above!)
tryDel (Zipper _ _) (Mod _)   = throwConf "del-mod"
tryDel (Zipper z h) (Spn rep) =
  case zipperRepZip z rep of
    Nothing -> throwInvFailure
    Just r  -> let hs = repLeavesList r
                in case partition (exElim isInR1) hs of
                     ([Exists (InL Refl :*: x)] , xs)
                       | all isCpyL1 xs -> return (h , x)
                       | otherwise      -> throwConf "del-spn"
                     _                  -> error "unreachable: invariant of zipperRepZip"
 where
   isInR1 :: (Sum a b :*: f) i -> Bool
   isInR1 (InL _ :*: _) = True
   isInR1 _             = False

   isCpyL1 :: Exists (Sum a b :*: Al kappa fam) -> Bool
   isCpyL1 (Exists (_ :*: a)) = isCpyA a

   isCpyA :: Al kappa fam x -> Bool
   isCpyA (Cpy _) = True
   isCpyA (Spn r) = all (exElim isCpyA) (repLeavesList r)
   isCpyA _       = False
tryDel _ _ = error "imp: no other case should show up"


instM :: (All Eq kappa)
      => HolesMV kappa fam at -> Al kappa fam at -> MergeM kappa fam ()
-- instantiating over a copy is fine;
instM _ (Cpy     _) = return ()
instM (Hole v) a = addToIota "inst-contr" v (disalign a)
-- Instantiating over a modification might also be
-- possible in select cases; namelly, when the deletion
-- context has no variables, unifies with the deletion
-- context of the modification and both insert the
-- same thing. This is tricky to detect and I think
-- we overall need a better formalism to deal with
-- merging chgs over spines; I'm postponing this for now.
instM _ (Mod _) = throwConf "inst-mod"
-- instantiating over a permutation if we are not immediatly
-- matching is tricky. I will be conservative and
-- raise a conflit. I suspect we can do better though.
-- For example; register that the deletion of x must be d
-- and return whatever we found about the insertion of y at this very
-- place; but this is difficult.
instM _ (Prm _ _) = throwConf "inst-perm"
instM x@(Prim _) d
  | x == chgDel (disalign d) = return ()
  | otherwise                = throwInvFailure
instM (Roll _) (Ins _) = throwConf "inst-ins"
instM (Roll _) (Del _) = throwConf "inst-del"
instM (Roll r) (Spn s) =
  case zipSRep r s of
    Nothing  -> throwInvFailure
    Just res -> void $ repMapM (\x -> uncurry' instM x >> return x) res


----------------------
-- Handling changes --
----------------------

type Subst2 kappa fam = ( Subst kappa fam (MetaVar kappa fam)
                       , Subst kappa fam (MetaVar kappa fam))

-- * Processing 'iota' and 'eqs'

-- |Splits the gathered equivalences into those that
-- have no holes and the rest. For example,
--
-- > splitEqvs (M.fromList
-- >   [ (var 0 , Bin (var 1) (var 2))
-- >   , (var 1 , Bin (Leaf 42) (Leaf 84))
-- >   ]
-- > = (M.singleton (var 1) ... , M.singleton (var 0) ...)
--
splitEqvs :: Subst  kappa fam (MetaVar kappa fam)
          -> Subst2 kappa fam
splitEqvs = M.partition (exElim hasNoHoles)
  where
   hasNoHoles :: Holes kappa fam phi x -> Bool
   hasNoHoles (Hole _) = False
   hasNoHoles (Prim _) = True
   hasNoHoles (Roll r) = all (exElim hasNoHoles) $ repLeavesList r

-- |After we have split the equivalences into rigid and non-rigid,
-- with 'splitEqvs', we will add them to our deletion and
-- insertion maps.
addEqvsAndSimpl :: Subst kappa fam (MetaVar kappa fam)
                -> Subst2 kappa fam
                -> Either [Exists (MetaVar kappa fam)]
                          (Subst kappa fam (MetaVar kappa fam))
addEqvsAndSimpl m (rig, nrig) = minimize $ M.foldrWithKey go (M.union m rig) nrig
  where
    go :: Exists (MetaVar kappa fam)
       -> Exists (HolesMV kappa fam)
       -> Subst kappa fam (MetaVar kappa fam)
       -> Subst kappa fam (MetaVar kappa fam)
    go var u s
      -- we know 'var' and 'u' have the same index since they
      -- are comming from a subst, hence, we won't unsafe corce
      -- but just directly add in the map
      | canAdd var u s = M.insert var u s
      | otherwise      = s

    -- If we have a variable equivalence, and either of them are already members
    -- of the existing map we won't add the equivalence.
    -- The reason being that if we have an entry (var x , T) in the
    -- map, it means the merge algorithm has made a decision to
    -- instantiate x; if we insert an entry (var y , var x) or (var x , var y),
    -- then simplify, we will conflict with the merge's algorithm decision.
    -- Particularly when 'y' appears somewhere else. Recall that although
    -- we are using substitutions, these maps actually have the 'was' and
    -- 'became' semantics, not usual 'is-equivalent' semantics.
    canAdd :: Exists (MetaVar kappa fam)
           -> Exists (HolesMV kappa fam)
           -> Subst kappa fam (MetaVar kappa fam)
           -> Bool
    canAdd v (Exists (Hole u)) s = all (`M.notMember` s) [ v , Exists u ]
    canAdd v _                 s = v `M.notMember` s

-- |Here we split the a state into the deletion and insertion
-- maps that will be used to instantiate the result of the
-- first phase of the merge algorithm
splitDelInsMaps :: forall kappa fam
                 . (All Show kappa)
                => MergeState kappa fam
                -> Either [Exists (MetaVar kappa fam)]
                          (Subst2 kappa fam)
splitDelInsMaps (MergeState iot eqvs) =
  let sd = M.map (exMap chgDel) iot
      si = M.map (exMap chgIns) iot
      e' = splitEqvs eqvs
   in trace (oneStr "eqvs" eqvs) $ do
    d <- trace (oneStr "sd" $ sd) (addEqvsAndSimpl sd e')
    i <- trace (oneStr "si" $ si) (addEqvsAndSimpl si e')
    trace (diStr (d , i))
      return (d , i)
 where
   diStr :: Subst2 kappa fam -> String
   diStr (d , i) = unlines $
     [ "del-map: " ++ show v ++ ": " ++ show c | (v , c) <- M.toList d ] ++
     [ "ins-map: " ++ show v ++ ": " ++ show c | (v , c) <- M.toList i ]

   oneStr :: String -> Subst kappa fam (MetaVar kappa fam) -> String
   oneStr lbl d = unlines $
     [ "[" ++ lbl ++ "] " ++ show v ++ ": " ++ show c | (v , c) <- M.toList d ]

phase2 :: (All Show kappa , All Eq kappa)
       => Subst2 kappa fam
       -> Phase2 kappa fam at
       -> MergeM kappa fam (Chg kappa fam at)
phase2 di (P2TestEq ca cb) = chgeq di ca cb
phase2 di (P2Instantiate chg Nothing) =
  trace ("p2-inst:\n  " ++ show chg) $
    return (chgrefine di chg)
phase2 di (P2Instantiate chg (Just i)) =
  trace ("p2-inst-and-chk:\n  i = " ++ show i ++ "\n  c = " ++ show chg) $
    do es <- gets eqs
       case getCommonVars (substApply es (chgIns chg)) (substApply es i) of
           [] -> return $ chgrefine di chg
           xs -> throwConf ("mov-mov " ++ show xs)
 where
   getCommonVars :: HolesMV kappa fam at -> HolesMV kappa fam at -> [Int]
   getCommonVars x y =
     let vx = holesVars x
         vy = holesVars y
      in M.keys (M.intersection vx vy)

chgrefine :: Subst2 kappa fam
          -> Chg kappa fam at
          -> Chg kappa fam at
chgrefine (d , i) (Chg del ins) =
  let del' = substApply d del
      ins' = substApply i ins
   in Chg del' ins'

chgeq :: (All Show kappa , All Eq kappa)
      => Subst2 kappa fam
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
     else throwConf "not-eq"

------------
-- Pretty --


instance (All Show kappa) => Show (PatchC kappa fam x) where
  show = myRender . holesPretty go
    where
      go x = case x of
               InL c -> confPretty c
               InR c -> chgPretty c

confPretty :: (All Show kappa) => Conflict kappa fam x -> Doc AnsiStyle
-- confPretty (FailedContr vars)
--   = group (pretty "{!!" <+> sep (map (pretty . exElim metavarGet) vars) <+> pretty "!!}")
confPretty (Conflict lbl c d)
  = vcat [ pretty "{!! >>>>>>>" <+> pretty lbl <+> pretty "<<<<<<<"
         , alignedPretty c
         , pretty "==========="
         , alignedPretty d
         , pretty ">>>>>>>" <+> pretty lbl <+> pretty "<<<<<<< !!}"]
