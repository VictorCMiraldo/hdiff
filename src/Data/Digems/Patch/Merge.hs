{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes    #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds     #-}
{-# LANGUAGE PolyKinds     #-}
{-# LANGUAGE GADTs         #-}
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

import Generics.MRSOP.Util
import Generics.MRSOP.Base
import Generics.MRSOP.Digems.Treefix
import Generics.MRSOP.Digems.Digest

import Data.Exists
import qualified Data.WordTrie as T
import Data.Digems.Patch.Preprocess
import Data.Digems.Patch
import Data.Digems.Change
import Data.Digems.Change.Apply
import Data.Digems.Change.Classify
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
  Conflict :: ConflictClass
           -> CChange        ki codes at
           -> CChange        ki codes at
           -> Conflict       ki codes at

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
(//) :: ( Show1 ki , Eq1 ki , HasDatatypeInfo ki fam codes , Ord1 ki
        , UTxTestEqualityCnstr ki (CChange ki codes))
     => Patch ki codes ix
     -> Patch ki codes ix
     -> PatchC ki codes ix
p // q = utxJoin . utxMap (uncurry' reconcile) $ utxLCP p q

-- |The 'reconcile' function will try to reconcile disagreeing
--  patches.
--
--  Precondition: before calling @reconcile p q@, make sure
--                @p@ and @q@ are different.
reconcile :: ( Show1 ki , Eq1 ki , HasDatatypeInfo ki fam codes , Ord1 ki
             , UTxTestEqualityCnstr ki (CChange ki codes))
          => RawPatch ki codes at
          -> RawPatch ki codes at
          -> UTx ki codes (Sum (Conflict ki codes) (CChange ki codes)) at
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
  | otherwise = UTxHole $ mergeCChange (distrCChange (specialize cp (cCtxDel cq))) cq

-- (iii) We are transporting a change over a spine
reconcile (UTxHole cp) cq
  | isCpy cp  = UTxHole $ InR cp
  | otherwise = UTxHole $ mergeCChange cp (distrCChange (specialize cq (cCtxDel cp)))

-- (iv) Anything else is a conflict; this should be technically
--      unreachable since both patches were applicable to at least
--      one common element; hence the spines can't disagree other than
--      on the placement of the holes.
reconcile cp cq = error "unreachable"
   
type ConflictClass = (ChangeClass , ChangeClass)

t :: Show a => a -> a
t a = trace (show a) a

-- |If we are transporting @cp@ over @cq@, we need to adapt
--  both the pattern and expression of @cp@. Also known as the
--  deletion and insertion context, respectively.
--
--  We do so by /"applying"/ @cq@ on both of those. This application
--  is done by instantiating the variables of the pattern of @cq@
--  and substituting in the expression of @cq@.
mergeCChange :: ( Show1 ki , Eq1 ki , HasDatatypeInfo ki fam codes , Ord1 ki
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
    
    adapt :: ( Show1 ki , Eq1 ki , HasDatatypeInfo ki fam codes
             , UTxTestEqualityCnstr ki (CChange ki codes))
          => CChange ki codes at -- ^ @cp@
          -> CChange ki codes at -- ^ @cq@
          -> Either (ApplicationErr ki codes (MetaVarIK ki)) (CChange ki codes at)
    adapt cp cq = 
      let resD = genericApply cq (cCtxDel cp)
          resI = genericApply cq (cCtxIns cp)
       in either (\err -> trace (show err) (Left err))
                 -- FIXME: compute variables!
                 (\(d, i) -> Right $ CMatch S.empty d i)
        $ codelta resD resI
      where
        codelta (Left e) _ = Left e
        codelta _ (Left e) = Left e
        codelta (Right a) (Right b) = Right (a , b)

{-
-- |Applies a change to a term containing metavariables.
metaApply :: ( Show1 ki , Eq1 ki , HasDatatypeInfo ki fam codes
             , UTxTestEqualityCnstr ki (CChange ki codes))
          => CChange ki codes at -- ^ @cq@
          -> Term ki codes at    -- ^ @p@
          -> Either (UnificationErr ki codes) (Term ki codes at)
metaApply cq = utxUnify (cCtxDel cq) (cCtxIns cq) 
-}
