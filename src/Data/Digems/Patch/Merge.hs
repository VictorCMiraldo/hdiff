{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes    #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds     #-}
{-# LANGUAGE PolyKinds     #-}
{-# LANGUAGE GADTs         #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Data.Digems.Patch.Merge where

import Data.Proxy
import Data.Type.Equality
import Data.Functor.Const
import Data.Functor.Sum
import qualified Data.Map as M
import qualified Data.Set as S
import Data.List (nub)

import Control.Monad
import Control.Monad.State
import Control.Monad.Writer hiding (Sum)
import Control.Monad.Identity
import Control.Monad.Except

import Generics.MRSOP.Util
import Generics.MRSOP.Base
import Generics.MRSOP.Digems.Treefix
import Generics.MRSOP.Digems.Digest

import Data.Exists
import qualified Data.WordTrie as T
import Data.Digems.Patch
import Data.Digems.Patch.Diff
import Data.Digems.Change
import Data.Digems.Change.Apply
import Data.Digems.MetaVar

import Debug.Trace


-- * Merging Treefixes
--
-- $mergingtreefixes
--
-- After merging two patches, we might end up with a conflict.
-- That is, two changes that can't be reconciled.

-- |Hence, a conflict is simply two changes together.
data Conflict :: (kon -> *) -> [[[Atom kon]]] -> Atom kon -> * where
  Conflict :: String
           -> RawPatch ki codes at
           -> RawPatch ki codes at
           -> Conflict ki codes at

-- |A 'PatchC' is a patch with potential conflicts inside
type PatchC ki codes ix
  = UTx ki codes (Sum (Conflict ki codes) (CChange ki codes)) (I ix)

-- |Tries to cast a 'PatchC' back to a 'Patch'. Naturally,
--  this is only possible if the patch has no conflicts.
noConflicts :: PatchC ki codes ix -> Maybe (Patch ki codes ix)
noConflicts = utxMapM rmvInL
  where
    rmvInL (InL _) = Nothing
    rmvInL (InR x) = Just x

-- |Returns the labels of the conflicts ina a patch.
getConflicts :: (Show1 ki) => PatchC ki codes ix -> [String]
getConflicts = snd . runWriter . utxMapM go
  where
    go x@(InL (Conflict str _ _)) = tell [show str] >> return x
    go x                          = return x
    

-- |A merge of @p@ over @q@, denoted @p // q@, is the adaptation
--  of @p@ so that it could be applied to an element in the
--  image of @q@.
(//) :: ( Applicable ki codes (UTx2 ki codes)
        , HasDatatypeInfo ki fam codes 
        )
     => Patch ki codes ix
     -> Patch ki codes ix
     -> PatchC ki codes ix
p // q = utxJoin . utxMap (uncurry' reconcile) $ utxLCP p q

-- |The 'reconcile' function will try to reconcile disagreeing
--  patches.
--
--  Precondition: before calling @reconcile p q@, make sure
--                @p@ and @q@ are different.
reconcile :: forall ki codes fam at
           . ( Applicable ki codes (UTx2 ki codes)
             , HasDatatypeInfo ki fam codes 
             ) 
          => RawPatch ki codes at
          -> RawPatch ki codes at
          -> UTx ki codes (Sum (Conflict ki codes) (CChange ki codes)) at
reconcile p q
  -- When one of the patches is a copy, this is easy. We borrow
  -- from residual theory and return the first one.
  | patchIsCpy p = utxMap InR p
  | patchIsCpy q = utxMap InR p
  -- If both patches are alpha-equivalent, we return a copy.
  | patchEq p q  = UTxHole $ InR $ makeCopyFrom (distrCChange p)
  -- Otherwise, this is slightly more involved, but it is intuitively simple.
  | otherwise    =
    -- First we translate both patches to a 'spined change' representation.
    let sp = utxJoin $ utxMap (uncurry' utxLCP . unCMatch) p
        sq = utxJoin $ utxMap (uncurry' utxLCP . unCMatch) q -- spinedChange q
     in case process sp sq of
          CantReconcile     -> UTxHole $ InL $ Conflict "conf" p q
          ReturnNominator   -> utxMap InR p
          InstDenominator v -> UTxHole $
            case runExcept $ transport (scIns sq) v of
              Left err -> InL $ Conflict (show err) p q
              Right r  -> InR $ utx2change r
          

type UTx2 ki codes
  = UTx ki codes (MetaVarIK ki) :*: UTx ki codes (MetaVarIK ki)
type UTxUTx2 ki codes
  = UTx ki codes (UTx2 ki codes)

utx2distr :: UTxUTx2 ki codes at -> UTx2 ki codes at
utx2distr x = (scDel x :*: scIns x)

instance (Eq1 f , Eq1 g) => Eq1 (f :*: g) where
  eq1 (fx :*: gx) (fy :*: gy) = eq1 fx fy && eq1 gx gy

instance (TestEquality f) => TestEquality (f :*: g) where
  testEquality x y = testEquality (fst' x) (fst' y)

instance HasIKProjInj ki (UTx2 ki codes) where
  konInj  ki = (konInj ki :*: konInj ki)
  varProj p (f :*: _) = varProj p f

utx2change :: UTxUTx2 ki codes at -> CChange ki codes at
utx2change x = cmatch (scDel x) (scIns x)

data ProcessOutcome ki codes
  = ReturnNominator
  | InstDenominator (Subst ki codes (UTx2 ki codes))
  | CantReconcile

fst' :: (f :*: g) x -> f x
fst' (a :*: _) = a

snd' :: (f :*: g) x -> g x
snd' (_ :*: b) = b

scDel :: SpinedChange ki codes at
      -> UTx ki codes (MetaVarIK ki) at
scDel = utxJoin . utxMap fst' 

scIns :: SpinedChange ki codes at
      -> UTx ki codes (MetaVarIK ki) at
scIns = utxJoin . utxMap snd'

-- |This will process two changes, represented as a spine and
-- inner changes, into a potential merged patch. The result of @process sp sq@
-- is supposed to be applicable to the codomain of @sq@
process :: (Applicable ki codes (UTx2 ki codes))
        => UTxUTx2 ki codes at -> UTxUTx2 ki codes at
        -> ProcessOutcome ki codes
process sp sq =
  let aux = utxGetHolesWithM' (uncurry' isSmaller) $ utxLCP sp sq
   in case runState (fmap mboolsum aux) M.empty of
        (Just True,  _) -> ReturnNominator
        (Just False, s) -> InstDenominator s
        (Nothing,    _) -> CantReconcile
 where
   mboolsum :: [Maybe Bool] -> Maybe Bool
   mboolsum = fmap and . sequence
    
   isSmaller :: (Applicable ki codes (UTx2 ki codes))
             => UTxUTx2 ki codes at -> UTxUTx2 ki codes at
             -> State (Subst ki codes (UTx2 ki codes)) (Maybe Bool)
   isSmaller (UTxHole pp) (UTxHole qq)
     | isLocalIns pp && isLocalIns qq = return Nothing
     | otherwise                      = instRight (UTxHole pp) qq
                                     >> return (Just True)
   isSmaller (UTxHole pp) qq = instRight (UTxHole pp) (utx2distr qq) 
                            >> return (Just True)
   isSmaller pp (UTxHole qq) = instRight pp qq
                            >> return (Just $ rawCpy qq)
   isSmaller _ _ = return $ Just False

   instRight :: (Applicable ki codes (UTx2 ki codes))
             => UTxUTx2 ki codes at -> UTx2 ki codes at
             -> State (Subst ki codes (UTx2 ki codes)) ()
   instRight l r = do
     s <- get
     case runExcept (pmatch' s (fst' r) l) of
       Left err -> trace "here" $ return () -- what to do here?
       Right r  -> put r
       
   isLocalIns :: (UTx ki codes phi :*: UTx ki codes phi) at -> Bool
   isLocalIns (UTxHole _ :*: UTxPeel _ _) = True
   isLocalIns _                           = False

{-

    domAccepts (UTxHole h) (UTxHole chgQ)
      = let r =not (isLocalIns h && isLocalIns chgQ)
         in trace ("$$$\n" ++ show1 h ++ "\n$$$\n" ++ show1 chgQ ++ "\n" ++ show r) r
    -- a hole accepts anything
    domAccepts (UTxHole h) s          = trace ("$$$\n" ++ show1 h ++ "\n$$$\n" ++ show1 s) True
    -- If we are going to apply over some unrestricted
    -- value, we can also consider our domain accepts it.
    domAccepts domP sQ@(UTxHole chgQ) = rawCpy chgQ
    -- Otherwise, we don't accept
    domAccepts domP sQ                = False

-}
      {- if sp `isShorterThan` sq
        then trace "ist" $ utxMap InR p -- utxMap InR $ close (utxMap (uncurry' change) sp)
        else let cq = CMatch S.empty (scDel sq) (scIns sq)
                 cp = CMatch S.empty (scDel sp) (scIns sp)
              in case metaApply cp cq of
                   Left  err -> UTxHole $ InL (Conflict (show err) cp cq)
                   Right res -> UTxHole $ InR res
      -}


refinedFor :: (Eq1 ki)
           => SpinedChange ki codes at
           -> UTx ki codes (MetaVarIK ki) at
           -> SpinedChange ki codes at
refinedFor s = utxJoin . utxMap (uncurry' go) . utxLCP s
  where
    go :: SpinedChange ki codes at
       -> UTx ki codes (MetaVarIK ki) at
       -> SpinedChange ki codes at
    go (UTxHole chgP) codQ
      | rawCpy chgP = let v = rawCpyVar chgP + 1
                       in utxMap (\i -> delta (UTxHole $ metavarAdd v i)) codQ
      | otherwise   = UTxHole chgP
    go sP             codQ = sP

    delta x = (x :*: x)

    rawCpyVar (UTxHole v :*: _) = metavarGet v
         
type SpinedChange ki codes
  = UTx ki codes (UTx ki codes (MetaVarIK ki) :*: UTx ki codes (MetaVarIK ki))

metaApply :: ( Show1 ki , Eq1 ki , HasDatatypeInfo ki fam codes
             , UTxTestEqualityCnstr ki (CChange ki codes))
          => CChange ki codes at -- ^ @cp@
          -> CChange ki codes at -- ^ @cq@
          -> Either (ApplicationErr ki codes (MetaVarIK ki)) (CChange ki codes at)
metaApply cp cq = do
    resD <- genericApply cq (cCtxDel cp)
    resI <- genericApply cq (cCtxIns cp)
    return $ cmatch resD resI


rawCpy :: (UTx ki codes (MetaVarIK ki) :*: UTx ki codes (MetaVarIK ki)) at -> Bool
rawCpy (UTxHole v1 :*: UTxHole v2) = metavarGet v1 == metavarGet v2
rawCpy _                           = False


isShorterThan :: (Eq1 ki, Show1 ki) => SpinedChange ki codes at -> SpinedChange ki codes at
              -> Bool
isShorterThan sp sq = and $ utxGetHolesWith' (uncurry' domAccepts) $ (utxLCP sp sq)
  where
    domAccepts (UTxHole h) (UTxHole chgQ)
      = let r =not (isLocalIns h && isLocalIns chgQ)
         in trace ("$$$\n" ++ show1 h ++ "\n$$$\n" ++ show1 chgQ ++ "\n" ++ show r) r
    -- a hole accepts anything
    domAccepts (UTxHole h) s          = trace ("$$$\n" ++ show1 h ++ "\n$$$\n" ++ show1 s) True
    -- If we are going to apply over some unrestricted
    -- value, we can also consider our domain accepts it.
    domAccepts domP sQ@(UTxHole chgQ) = rawCpy chgQ
    -- Otherwise, we don't accept
    domAccepts domP sQ                = False

    isLocalIns :: (UTx ki codes phi :*: UTx ki codes phi) at -> Bool
    isLocalIns (UTxHole _ :*: UTxPeel _ _) = True
    isLocalIns _                           = False

instance (Show1 f , Show1 g) => Show1 (f :*: g) where
  show1 (fx :*: gx) = "(" ++ show1 fx ++ " :*: " ++ show1 gx ++ ")"


{-

{-

     in go (sp `refinedFor` scDel sq) sq
  where
    go :: SpinedChange ki codes at -> SpinedChange ki codes at
       -> UTx ki codes (Sum (Conflict ki codes) (CChange ki codes)) at
    go sp sq 
      -- For us to be able to apply sp directly on top of sq,
      -- the spine of the change for sp has to be 'shorter' than
      -- sq.
      | sp `isShorterThan` sq = UTxHole $ InR (changeSpined sp)
      | otherwise             =
        let cq = cmatch (scDel sq) (scIns sq)
            cp = cmatch (scDel sp) (scIns sp)
         in UTxHole $ case metaApply cp cq of
                        Left  err -> InL (Conflict (show err) cp cq)
                        Right res -> InR res
-}
-- A spine 'sp' is shorter than a spine 'sq' when it has holes "sooner" and, moreover,
-- those holes' domain is compatible with the codomain of what 'sq' is doing.
{-

    go sP sQ = (scDel sP) `acceptsWhatIsProvidedBy` sQ
-}
{-
    go (UTxHole chgP) sQ = chgP `acceptsWhatIsProvidedBy` sQ
    -- this branch could be removed by specializing the 'spined changes'
    go sP (UTxHole chgQ) = rawCpy chgQ -- trace (show1 sP ++ "\n$$$\n" ++ show1 sQ) False
    go _  _ = False
-}

utxOnDisagreement :: (Eq1 ki)
                  => (forall at . UTx ki codes phi at -> UTx ki codes psi at -> r)
                  -> UTx ki codes phi at -> UTx ki codes psi at
                  -> [r]
utxOnDisagreement f x = utxGetHolesWith' (uncurry' f) . utxLCP x

-- checks that the domain of its first argument accepts what is provided
-- by its second argument.
acceptsWhatIsProvidedBy :: (Eq1 ki, Show1 ki)
                        => UTx ki codes (MetaVarIK ki) at
                        -> SpinedChange ki codes at
                        -> Bool
acceptsWhatIsProvidedBy domP = and . utxOnDisagreement domAccepts domP
  where
    -- a hole accepts anything
    domAccepts (UTxHole _) _          = True
    -- If we are going to apply over some unrestricted
    -- value, we can also consider our domain accepts it.
    domAccepts domP sQ@(UTxHole chgQ) = rawCpy chgQ
    -- Otherwise, we don't accept
    domAccepts domP sQ                = False

    -- domAccepts domP sQ@(UTxHole chgQ) = trace (show1 domP ++ "\n$$$\n" ++ show1 sQ) $ rawCpy chgQ
    -- domAccepts domP sQ = trace (show1 domP ++ "\n$$$\n" ++ show1 sQ) False

spinedChange :: (Eq1 ki)
             => RawPatch ki codes at
             -> SpinedChange ki codes at
spinedChange p = let cp = distrCChange p
                  in utxLCP (cCtxDel cp) (cCtxIns cp)

changeSpined :: SpinedChange ki codes at
             -> CChange ki codes at
changeSpined sp = let del = utxJoin (utxMap fst' sp)
                      ins = utxJoin (utxMap snd' sp)
                   in cmatch del ins
  where
                                                                   
{-


    UTxHole $ InL (Conflict "non-disjoint" (distrCChange p) (distrCChange q))
-}
{-
  | nonStrut q   = utxMap InR p
  -- | composes p q && nonStrut q = utxMap InR p
  | otherwise      =
    let cq = distrCChange q
        cp = distrCChange p
     in UTxHole
      $ case specializeAndApply cp cq of
          Left  err -> InL (Conflict (show err) cp cq)
          Right res -> InR res
-}
{-
  | otherwise      =
    let cp = distrCChange p
        cq = distrCChange q
     in UTxHole
      $ if changeEq cp cq
        then InR (makeCopyFrom cp)
        else case specializeAndApply cp cq of
                    Left  err -> InL (Conflict (show err) cp cq)
                    Right res -> InR res
-}

{-

specializeAndApply :: ( Show1 ki , Eq1 ki , HasDatatypeInfo ki fam codes
                      , UTxTestEqualityCnstr ki (CChange ki codes))
                   => CChange ki codes at -- ^ @cp@
                   -> CChange ki codes at -- ^ @cq@
                   -> Either (ApplicationErr ki codes (MetaVarIK ki)) (CChange ki codes at)
specializeAndApply cp cq = do
    cp'  <- CS.specialize cp (CS.domain cq) 
    resD <- genericApply cq (cCtxDel cp')
    resI <- genericApply cq (cCtxIns cp')
    return $ CMatch S.empty resD resI


nonStrut :: (TestEquality ki, Eq1 ki , Show1 ki) => RawPatch ki codes at -> Bool
nonStrut = nonstrut . utxGetHolesWith changeClassify
  where
    nonstrut s = or $ [ x `S.member` s | x <- [CPerm , CMod , CIns] ]
-}
{-
-- (i) both different patches consist in changes
reconcile (UTxHole cp) (UTxHole cq)
  | isCpy cp       = UTxHole (InR cp)
  | isCpy cq       = UTxHole (InR cp)
  | changeEq cp cq = UTxHole $ InR (makeCopyFrom cp)
  | otherwise      = UTxHole $ mergeCChange cp cq
 
-- (ii) We are transporting a spine over a change
reconcile cp           (UTxHole cq) 
  | isCpy cq  = utxMap InR cp
{-
  | otherwise = either (\err -> trace (show err) (UTxHole $ InL $ Conflict (CIns,CIns) cq cq))
                       (UTxHole . InR)
              $ utxTransport cq _ -- (closedChangeDistr (specialize cp (cchangeDomain cq)))
-}
{-
  | otherwise = UTxHole $ mergeCChange (distrCChange cp) cq
-}

-- (iii) We are transporting a change over a spine
reconcile (UTxHole cp) cq
  | isCpy cp  = UTxHole $ InR cp
  | otherwise = UTxHole $ mergeCChange cp (distrCChange cq)

-- (iv) Anything else is a conflict; this should be technically
--      unreachable since both patches were applicable to at least
--      one common element; hence the spines can't disagree other than
--      on the placement of the holes.
reconcile cp cq = error "unreachable"
-}
   
type ConflictClass = String

t :: Show a => a -> a
t a = trace (show a) a
{-
    go (UTxHole cp) (UTxHole cq)
      | isCpy cq      = Const True
      | otherwise     = applicableTo cp (cCtxIns cq)
    -- todo: specialize q's spine!
    go (UTxHole cp) q
      = let q' = specialize q (cCtxDel cp)
         in applicableTo cp (cCtxIns (distrCChange q'))
    go p (UTxHole cq)
      | isCpy cq  = Const True
      | otherwise = trace (show (distrCChange p) ++ ";;;" ++ show cq)
                  $ Const False
    go _ _ = trace "5" $ Const False
-}
{-

-- |If we are transporting @cp@ over @cq@, we need to adapt
--  both the pattern and expression of @cp@. Also known as the
--  deletion and insertion context, respectively.
--
--  We do so by /"applying"/ @cq@ on both of those. This application
--  is done by instantiating the variables of the pattern of @cq@
--  and substituting in the expression of @cq@.
mergeCChange :: ( Show1 ki , Eq1 ki , HasDatatypeInfo ki fam codes 
                 , UTxTestEqualityCnstr ki (CChange ki codes))
              => CChange ki codes at -- ^ @cp@
              -> CChange ki codes at -- ^ @cq@
              -> Sum (Conflict ki codes) (CChange ki codes) at
mergeCChange cp cq =
  let cclass = (changeClassify cp , changeClassify cq)
   in case cclass of
        (CIns , CIns) -> InL (Conflict cclass cp cq)
        (CDel , CDel) -> InL (Conflict cclass cp cq)

        (CDel , _)     -> InR cp
        (CPerm , CMod) -> InR cp

        (CIns , CDel)  -> inj cclass $ adapt cp cq
        (CIns , _)     -> InR cp

        _              -> inj cclass $ adapt cp cq
{-
        (CPerm , CPerm) -> inj cclass $ adapt cp cq
        (CMod   , CMod) -> inj cclass $ adapt cp cq

        (CMod  , CPerm) -> inj cclass $ adapt cp cq
        (CPerm , CMod)  -> inj cclass $ adapt cp cq -- InR cp

        (CPerm , CIns)  -> inj cclass $ adapt cp cq
        (CPerm , CDel)  -> inj cclass $ adapt cp cq
        (CMod  , CIns)  -> inj cclass $ adapt cp cq
        (CMod  , CDel)  -> inj cclass $ adapt cp cq
-}
{-
        (CIns , CIns) -> InL (Conflict cclass cp cq)
        (CDel , CDel) -> InL (Conflict cclass cp cq)

        (CIns , CDel) -> inj cclass $ adapt cp cq
        (CMod , CIns) -> inj cclass $ adapt cp cq

        (CPerm , CMod)  -> InR cp
        (CPerm , CIns)  -> inj cclass $ adapt cp cq
        (CPerm , CDel)  -> inj cclass $ adapt cp cq
        (CMod  , CPerm) -> inj cclass $ adapt cp cq
        (CIns  , CPerm) -> InR cp
        (CDel  , CPerm) -> InR cp
        (CPerm , CPerm) -> inj cclass $ adapt cp cq

        (CDel , CIns) -> InR cp
        (CIns , CMod) -> InR cp

        (CMod , CMod) -> inj cclass $ adapt cp cq

        (CDel  , CMod) -> InR cp
        (CMod  , CDel) -> inj cclass $ adapt cp cq
-}
  where
    inj confclass = either (const $ InL $ Conflict confclass cp cq) InR
    
    adapt1 :: ( Show1 ki , Eq1 ki , HasDatatypeInfo ki fam codes
              , UTxTestEqualityCnstr ki (CChange ki codes))
           => CChange ki codes at -- ^ @cp@
           -> CChange ki codes at -- ^ @cq@
           -> Either (ApplicationErr ki codes (MetaVarIK ki)) (CChange ki codes at)
    adapt1 cp cq = do
        resD <- genericApply cq (cCtxDel cp)
        resI <- genericApply cq (cCtxIns cp)
        return $ cmatch resD resI

    adapt :: ( Show1 ki , Eq1 ki , HasDatatypeInfo ki fam codes
             , UTxTestEqualityCnstr ki (CChange ki codes))
          => CChange ki codes at -- ^ @cp@
          -> CChange ki codes at -- ^ @cq@
          -> Either (ApplicationErr ki codes (MetaVarIK ki)) (CChange ki codes at)
    adapt cp cq = adapt1 cp cq
      `catchError` (\e -> case e of
        IncompatibleHole _ _ -> specialize cp (domain cq) >>= flip adapt1 cq
        _                    -> trace (show e) $ throwError e)

      {-
      let resD = genericApply cq (cCtxDel cp)
          resI = genericApply cq (cCtxIns cp)
       in either (\err -> trace (show err) (Left err))
                 (\(d, i) -> Right $ cmatch d i)
        $ codelta resD resI
      where
        codelta (Left e) _ = Left e
        codelta _ (Left e) = Left e
        codelta (Right a) (Right b) = Right (a , b)
-}

{-
-- |Applies a change to a term containing metavariables.
metaApply :: ( Show1 ki , Eq1 ki , HasDatatypeInfo ki fam codes
             , UTxTestEqualityCnstr ki (CChange ki codes))
          => CChange ki codes at -- ^ @cq@
          -> Term ki codes at    -- ^ @p@
          -> Either (UnificationErr ki codes) (Term ki codes at)
metaApply cq = utxUnify (cCtxDel cq) (cCtxIns cq) 
-}
-}
-}
