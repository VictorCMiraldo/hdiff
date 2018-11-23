{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes    #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds     #-}
{-# LANGUAGE PolyKinds     #-}
{-# LANGUAGE GADTs         #-}
module Data.Digems.Diff.Merge where

import Data.Proxy
import Data.Type.Equality
import Data.Functor.Const
import Data.Functor.Sum
import qualified Data.Map as M
import qualified Data.Set as S

import Control.Monad
import Control.Monad.State
import Control.Monad.Writer hiding (Sum)
import Control.Monad.Identity

import Generics.MRSOP.Util
import Generics.MRSOP.Base
import Generics.MRSOP.Digems.Treefix
import Generics.MRSOP.Digems.Digest
import Generics.MRSOP.Digems.Unify

import qualified Data.WordTrie as T
import Data.Digems.Diff.Preprocess
import Data.Digems.Diff.Patch
import Data.Digems.Diff.MetaVar

-- * Merging Treefixes
--
-- $mergingtreefixes
--
-- After merging two patches, we might end up with a conflict.
-- That is, two changes that can't be reconciled.

-- |Hence, a conflict is simply two changes together.
data Conflict :: (kon -> *) -> [[[Atom kon]]] -> Atom kon -> * where
  Conflict :: UnificationErr ki codes
           -> Change         ki codes at
           -> Change         ki codes at
           -> Conflict       ki codes at

-- |A 'PatchC' is a patch with potential conflicts inside
type PatchC ki codes ix
  = UTx ki codes (Sum (Conflict ki codes) (Change ki codes)) (I ix)

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
(//) :: ( Show1 ki , Eq1 ki , HasDatatypeInfo ki fam codes
        , UTxTestEqualityCnstr ki (Change ki codes))
     => Patch ki codes ix
     -> Patch ki codes ix
     -> PatchC ki codes ix
p // q = let p' = changeDistr p
             q' = changeDistr q
          in case mergeChange p' q' of
               InL conf -> UTxHole (InL conf)
               InR ok   -> utxMap (InR . uncurry' CMatch)
                         $ utxLCP (cCtxDel ok) (cCtxIns ok)
mergeChange :: ( Show1 ki , Eq1 ki , HasDatatypeInfo ki fam codes
                , UTxTestEqualityCnstr ki (Change ki codes))
             => Change ki codes at
             -> Change ki codes at
             -> Sum (Conflict ki codes) (Change ki codes) at
mergeChange cb ca
  = let resD = utxUnify (cCtxDel ca) (cCtxDel cb) (cCtxIns ca)
        resI = utxUnify (cCtxDel ca) (cCtxIns cb) (cCtxIns ca)
     in either (\uerr   -> InL $ Conflict uerr ca cb)
               (\(d, i) -> InR $ CMatch d i)
      $ codelta resD resI
  where
    codelta (Left e) _ = Left e
    codelta _ (Left e) = Left e
    codelta (Right a) (Right b) = Right (a , b)

{-
  -- utxJoin . utxMap (uncurry' reconcile) $ utxLCP p q

-- |The 'reconcile' function will try to reconcile disagreeing
--  patches.
--
--  Precondition: before calling @reconcile p q@, make sure
--                @p@ and @q@ are different.
reconcile :: ( Show1 ki , Eq1 ki , HasDatatypeInfo ki fam codes
             , UTxTestEqualityCnstr ki (Change ki codes))
          => RawPatch ki codes at
          -> RawPatch ki codes at
          -> UTx ki codes (Sum (Conflict ki codes) (Change ki codes)) at
-- (i) both different patches consist in changes
reconcile (UTxHole cp) (UTxHole cq) =
 UTxHole $ mergeChange cp cq
-- (ii) We are transporting a spine over a change
reconcile cp           (UTxHole cq) =
  UTxHole $ mergeChange (closedChangeDistr cp) cq
-- (iii) We are transporting a change over a spine
reconcile (UTxHole cp) cq           =
  UTxHole $ mergeChange cp (closedChangeDistr cq)
-- (iv) Anything else is a conflict; this should be technically
--      unreachable since both patches were applicable to at least
--      one common element; hence the spines can't disagree other than
--      on the placement of the holes.
reconcile cp cq = error "unreachable"
-}



{-
-- * Reconciling Changes

isCpy :: Change ki codes at -> Bool
isCpy (CMatch _ (UTxHole v) (UTxHole u)) = v == u
isCpy _                                  = False

-- |Reconcile two changes. 
cc :: (Eq1 ki)
   => Change ki codes at
   -> Change ki codes at
   -> UTx ki codes (Sum (Conflict ki codes) (Change ki codes)) at
cc x y
  | isCpy y   = UTxHole (InR x)
  | isCpy x   = UTxHole (InR y)
  | otherwise = UTxHole $ InL $ Conflict "cc" x y
{-
  We need to be able to apply the deletion context of x after
  the insertion context of y took place, then adapt the insertion of x
  accordingly.
-}


-- |Transport a spine over a change. This returns a spine
--  by adapting the old spine to the image of the change,
--  if possible.
--
--  The operation is defined as:
--    i) Apply the change to the raw patch
--    
sc :: ( Show1 ki , Eq1 ki , HasDatatypeInfo ki fam codes
      , UTxTestEqualityCnstr ki (Change ki codes))
   => RawPatch ki codes at
   -> Change ki codes at
   -> UTx ki codes (Sum (Conflict ki codes) (Change ki codes)) at
sc x y = case metaChange y x of
           Left err -> let xD = utxJoin (utxMap cCtxDel x)
                           xI = utxJoin (utxMap cCtxIns x)
                           xV = utxGetHolesWith Exists xD
                        in UTxHole $ InL (Conflict err (CMatch xV xD xI) y)
           Right res -> utxMap InR res

-- |Transports a change over a spine.
--  This adapts the change over the new spine and
-- returns a new change (if possible)
cs :: (Eq1 ki)
   => Change ki codes at
   -> RawPatch ki codes at
   -> Sum (Conflict ki codes) (Change ki codes) at
cs x y 
  | isCpy x = InR x
  | True    = InR x
  | otherwise
  = let yD = utxJoin (utxMap cCtxDel y)
        yI = utxJoin (utxMap cCtxIns y)
        yV = utxGetHolesWith Exists yD
     in InL (Conflict "cs" x (CMatch yV yD yI))

-- ** TEMPORARY

data UTxE :: (kon -> *) -> [[[Atom kon]]] -> (Atom kon -> *) -> * where
  UTxE :: UTx ki codes f at -> UTxE ki codes f

type MetaValuation ki codes
  = M.Map Int (UTxE ki codes (Change ki codes))

-- TODO: we might need renamings

-- |Unifies a UTx with another, producing a substitution of
--  the variables of the first to transform it in the second
utxUnify :: (Show1 ki , Eq1 ki , HasDatatypeInfo ki fam codes)
         => UTx ki codes (MetaVarIK ki) at
         -> UTx ki codes (Change ki codes) at
         -> Either String (MetaValuation ki codes)
utxUnify (UTxHole var) uty
  = return $ M.singleton (metavarGet var) (UTxE uty)
utxUnify (UTxOpq kx) (UTxOpq ky)
  | eq1 kx ky = return M.empty
  | otherwise = Left . unwords $ ["utxUnify: " , "K" , show1 kx , " /= ", show1 ky ]
utxUnify (UTxPeel cx px) (UTxPeel cy py)
  = let pf = Proxy :: Proxy fam
     in case testEquality cx cy of
          Nothing   -> Left . unwords $ ["utxUnify: " , "Peel"] 
          Just Refl -> M.unions <$> elimNPM (uncurry' utxUnify) (zipNP px py)
-- Conflicting scenarios
utxUnify (UTxOpq ki) (UTxHole var)
  | isCpy var = return M.empty
  | otherwise = Left . unwords $ ["utxUnify:" , "opq hole"]
utxUnify (UTxPeel cx px) (UTxHole var)
  | isCpy var = return M.empty
  | otherwise = Left . unwords $ ["utxUnify:" , "peel hole"]


utxYfinu :: ( Show1 ki , Eq1 ki , HasDatatypeInfo ki cam codes 
            , UTxTestEqualityCnstr ki (Change ki codes))
         => UTx ki codes (MetaVarIK ki) at
         -> UTx ki codes (Change ki codes) at
         -> MetaValuation ki codes
         -> Either String (UTx ki codes (Change ki codes) at)
utxYfinu utx@(UTxHole var) uty val
  = case M.lookup (metavarGet var) val of
      Nothing  -> Left . unwords $ ["utxYfinu:" , "undefined var:" , show var ]
      -- hacking the typechecker!
      Just (UTxE res) -> case testEquality utx (utxJoin $ utxMap cCtxDel res) of
        Nothing -> Left . unwords $ ["utxYfinu: testEquality:" , show var ]
        Just Refl -> return res
utxYfinu (UTxOpq  kx ) (UTxHole var) val
  = return (UTxHole var)
utxYfinu (UTxPeel cx px) (UTxHole var) val
  = return (UTxHole var)
utxYfinu (UTxPeel cx px) (UTxPeel cy py) val
  = case testEquality cx cy of
      Nothing   -> Left "utxYfinu: testEquality peel peel"
      Just Refl -> UTxPeel cx <$> mapNPM (flip (uncurry' utxYfinu) val) (zipNP px py)

-- |applies a change to a UTx
metaChange :: (Show1 ki , Eq1 ki , HasDatatypeInfo ki fam codes
              , UTxTestEqualityCnstr ki (Change ki codes))
           => Change ki codes at
           -> UTx ki codes (Change ki codes) at
           -> Either String (UTx ki codes (Change ki codes) at)
metaChange (CMatch _ del ins) utx
  = utxUnify del utx >>= utxYfinu ins utx

isSimpleCopy :: Change ki codes at -> Bool
isSimpleCopy (CMatch _ (UTxHole h1) (UTxHole h2))
  = h1 == h2
isSimpleCopy _ = False

-- |A call to @merger pa pb@ will either fail or
--  return a patch that can be applied to the image of
--  @pb@ and should commute with @merger pb pa@ applied
--  to the image of @pa@.
merger :: (Show1 ki , Eq1 ki , HasDatatypeInfo ki fam codes
          ,UTxTestEqualityCnstr ki (Change ki codes))
       => UTx ki codes (Change ki codes) at
       -> UTx ki codes (Change ki codes) at
       -> Either String (UTx ki codes (Change ki codes) at)
-- Holes on the left are preserved
merger (UTxHole var) (UTxPeel cy py)
  = return $ UTxHole var
-- Holes on the right are applied
merger utx (UTxHole var)
  = metaChange var utx  
-- finding a copied constant is irrelevant
merger (UTxOpq kx)     (UTxOpq ky)
  = return (UTxOpq kx)
-- in case both constructors are copied, they better
-- be the same
merger (UTxPeel cx px) (UTxPeel cy py)
  = case testEquality cx cy of
      Nothing   -> Left . unwords $ [ "merger:" , "conflict:" , "Peel Peel"]
      Just Refl -> UTxPeel cx <$> mapNPM (uncurry' merger) (zipNP px py)
-}

{-

Now consider the patch from O to A, call it OA:

(Seq                 -|+ (Seq
 (:                  -|+  (:
  (Assign            -|+   (Assign
   [K| 3 |]          -|+    [K| 3 |]
   (ABinary          -|+    (ABinary
    Add              -|+     Add
    (Var             -|+     (Var
     someIdent)      -|+      change)
    (Var             -|+     (Var
     [K| 4 |])))     -|+      [K| 4 |])))
  (:                 -|+   (:
   [I| 1 |]          -|+    [I| 1 |]
   [])))             -|+    (:
                     -|+     (Assign
                     -|+      h
                     -|+      (IntConst
                     -|+       42))
                     -|+     []))))

And from O to B, call it OB:

(Seq                 -|+ (Seq
 (:                  -|+  (:
  [I| 5 |]           -|+   [I| 5 |]
  [I| 3 |]))         -|+   (:
                     -|+    (Assign
                     -|+     k
                     -|+     (IntConst
                     -|+      24))
                     -|+    [I| 3 |])))

The transport of OB over OA, meant to be applied to the
destination of OA should be:

(Seq                 -|+ (Seq
 (:                  -|+  (:
  [I| 6 |]           -|+   [I| 6 |]
  [I| 7 |]))         -|+   (:
                     -|+    (Assign
                     -|+     k
                     -|+     (IntConst
                     -|+      24))
                     -|+    [I| 7 |])))

Whereas the transport of OA over OB, meant to be applied to
the destination of OB should be:

(Seq                 -|+ (Seq
 (:                  -|+  (:
  (Assign            -|+   (Assign
   [K| 4 |]          -|+    [K| 4 |]
   (ABinary          -|+    (ABinary
    Add              -|+     Add
    (Var             -|+     (Var
     someIdent)      -|+      change)
    (Var             -|+     (Var
     [K| 5 |])))     -|+      [K| 5 |])))
  (:                 -|+   (:
   [I| 0 |]          -|+    [I| 0 |]
   (:                -|+    (:
    [I| 2 |]         -|+     [I| 2 |]
    []))))           -|+     (:
                     -|+      (Assign
                     -|+       h
                     -|+       (IntConst
                     -|+        42))
                     -|+      [])))))

The deletion context of (OA // OB) is obtained
by the means of applying (delCtx OB) to (delCtx OA),
yielding the following valuation:

OB.5 |-> (Assign [K| OA.3 |]
                (ABinary Add
                (Var someIdent)
                (Var [K| OA.4 |])))

OB.3 |-> (: [I| OA.1 |] [] )

If we apply this valuation to (insCtx OB), we get:

(Seq
 (:
  (Assign
   [K| OA.3 |]
   (ABinary
    Add
    (Var
     someIdent)
    (Var
     [K| OA.4 |])))
  (:
   (Assign k (IntConst 24))
   (: [I| OA.1 |]
      [] )
  )
 )
)

We now apply a generalization step: every tree that has no holes inside
becomes a hole:

(Seq
 (:
  (Assign
   [K| OA.3 |]
   (ABinary
    Add
    (Var
     someIdent)
    (Var
     [K| OA.4 |])))
  (:
   [I| NEWHOLE |]
   (: [I| OA.1 |]
      [])
  )
 )
)

This is essentially the deletion context of (OA / OB) !
The insertion context of (OA / OB), on the other hand, is obtained by
applying the patch OA to the deletion context we just obtained!

This will yield the valuation:

3 |-> [K| OA.3 |]
4 |-> [K| OA.4 |]
1 |-> 

-}
