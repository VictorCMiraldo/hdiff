{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes    #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds     #-}
{-# LANGUAGE PolyKinds     #-}
{-# LANGUAGE GADTs         #-}
{-# LANGUAGE TypeApplications #-}
module Languages.WhileMerge where

import Data.Proxy
import Data.Type.Equality hiding (apply)
import Data.Functor.Const
import Data.Functor.Sum
import qualified Data.Map as M
import qualified Data.Set as S

import Control.Monad
import Control.Monad.State
import Control.Monad.Identity

import           Data.Text.Prettyprint.Doc

import Generics.MRSOP.Util
import Generics.MRSOP.Base
import Generics.MRSOP.Digems.Treefix
import Generics.MRSOP.Digems.Digest
import Generics.MRSOP.Digems.Renderer

import qualified Data.WordTrie as T
import Data.Digems.Diff.Preprocess
import Data.Digems.Diff.Patch
import Data.Digems.Diff.Show

import Languages.While

{-
-- * Merging

-- TODO: flip Conflict and MetaVar; it is common to have the 'right'
--       result on the right side of the coproduct

data Conflict :: (kon -> *) -> [[[Atom kon]]] -> Atom kon -> * where
  Conflict :: GUTx ki codes (TxAtom ki codes MetaVar) v
           -> GUTx ki codes (TxAtom ki codes MetaVar) v
           -> Conflict ki codes v

type PatchC ki codes = RawPatch (Sum MetaVar (Conflict ki codes)) ki codes

-- |Merge two patches into a patch that may have conflicts.
--  TODO: prove @(q // p) . p == (p // q) . p@ in the absence of conflicts
--
(//) :: (Eq1 ki , IsNat v)
      => Patch ki codes v
      -> Patch ki codes v
      -> PatchC ki codes v
(Patch pd pi) // (Patch _ qi) = Patch (qi `transport` pd)
                                      (gtxMap (txatomMap InL) pi)

-- |Transports a deletion context (second arg) to work
--  on top of a insertion context.
--  We must produce a valuation in case the deletion context
--  copies some constants that need to be plugged into the
--  insertion context.
transport :: (Eq1 ki)
          => GUTx ki codes (TxAtom ki codes MetaVar) v -- holes0
          -> GUTx ki codes (TxAtom ki codes MetaVar) v -- holes1
          -> GUTx ki codes (TxAtom ki codes (Sum MetaVar (Conflict ki codes))) v -- holes1
-- transport preserves holes on the right
transport tx (GUTxHere (Meta v))
  = GUTxHere $ Meta (InL v)
-- ignores holes on the left
transport (GUTxHere (Meta _)) ty
  = gtxMap (txatomMap InL) ty
-- Checks constants for equality
transport tx@(GUTxHere (SolidK kx)) ty@(GUTxHere (SolidK ky))
  | eq1 kx ky = GUTxHere (SolidK kx)
  | otherwise = GUTxHere (Meta $ InR $ Conflict tx ty)
-- Checks trees for equality
transport tx@(GUTxHere (SolidI vx)) ty@(GUTxHere (SolidI vy))
  | eqFix eq1 vx vy = GUTxHere (SolidI vx)
  | otherwise       = GUTxHere (Meta $ InR $ Conflict tx ty)
-- Recurses over fixes trees
transport tx@(GUTxPeel cx dx)       ty@(GUTxHere (SolidI vy))
  | Tag cy dy <- sop (unFix vy)
  = case testEquality cx cy of
      Nothing   -> GUTxHere (Meta $ InR $ Conflict tx ty)
      Just Refl -> GUTxPeel cx (mapNP (uncurry' go) $ zipNP dx dy)
  where
    go :: (Eq1 ki)
       => GUTx ki codes (TxAtom ki codes MetaVar) at
       -> NA ki (Fix ki codes) at
       -> GUTx ki codes (TxAtom ki codes (Sum MetaVar (Conflict ki codes))) at
    go vx (NA_K k) = transport vx (GUTxHere (SolidK k))
    go vx (NA_I i) = transport vx (GUTxHere (SolidI i))
transport tx@(GUTxHere (SolidI vx)) ty@(GUTxPeel cy dy)
  | Tag cx dx <- sop (unFix vx)
  = case testEquality cx cy of
      Nothing   -> GUTxHere (Meta $ InR $ Conflict tx ty)
      Just Refl -> GUTxPeel cx (mapNP (uncurry' go) $ zipNP dx dy)
  where
    go :: (Eq1 ki)
       => NA ki (Fix ki codes) at
       -> GUTx ki codes (TxAtom ki codes MetaVar) at
       -> GUTx ki codes (TxAtom ki codes (Sum MetaVar (Conflict ki codes))) at
    go (NA_K k) = transport (GUTxHere (SolidK k))
    go (NA_I i) = transport (GUTxHere (SolidI i))
-- Goes over constructors, preserving data on the right
transport tx@(GUTxPeel cx dx) ty@(GUTxPeel cy dy)
  = case testEquality cx cy of
      Nothing   -> GUTxHere (Meta $ InR $ Conflict tx ty)
      Just Refl -> GUTxPeel cx (mapNP (uncurry' transport) $ zipNP dx dy)

-- |Tries to cast a patch with conflicts to one with
--  no conflicts. Only succeeeds if there are no conflicts,
--  of course.
hasNoConflict :: PatchC ki codes ix -> Maybe (Patch ki codes ix)
hasNoConflict (Patch del ins)
  = Patch <$> gtxMapM (txatomMapM unInL) del
          <*> gtxMapM (txatomMapM unInL) ins
  where
    unInL :: Sum a b x -> Maybe (a x)
    unInL (InL ax) = Just ax
    unInL _        = Nothing

-}
{-

A tell tale of some WHILE programs as a guiding
example to merging.

Let:

O.while  | f := a + b;
         | g := x + y + z;

A.while  | f := c + b;
         | g := x + y + z;
         | h := 42;

B.while  | f := a + b;
         | k := 24;
         | g := x + y + z;
-}

a , o , b :: Stmt
a = (Seq ((:) (Assign "f" (ABinary Add (Var "c") (Var "b"))) ((:)
      (Assign "g" (ABinary Multiply (ABinary Multiply (Var "x") (Var
      "y")) (Var "z"))) ((:) (Assign "h" (IntConst 42)) []))))

o = (Seq ((:) (Assign "f" (ABinary Add (Var "a") (Var "b"))) ((:)
      (Assign "g" (ABinary Multiply (ABinary Multiply (Var "x") (Var
      "y")) (Var "z"))) [])))

b = (Seq ((:) (Assign "f" (ABinary Add (Var "a") (Var "b"))) ((:)
      (Assign "k" (IntConst 24)) ((:) (Assign "g" (ABinary Multiply
      (ABinary Multiply (Var "x") (Var "y")) (Var "z"))) []))))



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

-}

tr :: Stmt -> Fix W CodesStmt Z
tr = dfrom . into @FamStmt

oa = digems 1 (dfrom $ into @FamStmt o) (dfrom $ into @FamStmt a)
ob = digems 1 (dfrom $ into @FamStmt o) (dfrom $ into @FamStmt b)

{-

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

-}

delPatch = utxJoin . utxMap ctxDel
insPatch = utxJoin . utxMap ctxIns

Right val = utxUnify (delPatch ob) oa

data UTxE :: (kon -> *) -> [[[Atom kon]]] -> (Atom kon -> *) -> * where
  UTxE :: UTx ki codes f at -> UTxE ki codes f

instance Show (UTxE W CodesStmt (Change W CodesStmt)) where
  show (UTxE utx) = show $ utxPretty Proxy id goChange utx
    where
      goChange :: Change W CodesStmt i -> Doc ()
      goChange (Match del ins)
        = vsep [ pretty ">>>"
               , utxPretty Proxy id goVar del
               , pretty "==="
               , utxPretty Proxy id goVar ins
               , pretty "<<<"
               ]

      goVar :: MetaVarIK ki at -> Doc ()
      goVar (NA_I (Const i))      = brackets $ pretty "I" <> pretty i
      goVar (NA_K (Annotate i _)) = brackets $ pretty "K" <> pretty i             


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

utxYfinu :: ( Show1 ki , Eq1 ki , HasDatatypeInfo ki cam codes 
            , UTxTestEqualityCnstr ki (Change ki codes))
         => UTx ki codes (MetaVarIK ki) at
         -> MetaValuation ki codes
         -> Either String (UTx ki codes (Change ki codes) at)
utxYfinu utx@(UTxHole var) val
  = case M.lookup (metavarGet var) val of
      Nothing  -> Left . unwords $ ["utxYfinu:" , "undefined var:" , show var ]
      -- hacking the typechecker!
      Just (UTxE res) -> case testEquality utx (utxJoin $ utxMap ctxDel res) of
        Nothing -> Left . unwords $ ["utxYfinu: testEquality:" , show var ]
        Just Refl -> return res
utxYfinu (UTxOpq  kx )   val = return (UTxOpq kx)
utxYfinu (UTxPeel cx px) val
  = UTxPeel cx <$> mapNPM (flip utxYfinu val) px

-- |applies a change to a UTx
metaChange :: (Show1 ki , Eq1 ki , HasDatatypeInfo ki fam codes
              , UTxTestEqualityCnstr ki (Change ki codes))
           => Change ki codes at
           -> UTx ki codes (Change ki codes) at
           -> Either String (UTx ki codes (Change ki codes) at)
metaChange (Match del ins) utx
  = utxUnify del utx >>= utxYfinu ins

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
{-
utxApply :: (Show1 ki , Eq1 ki , HasDatatypeInfo ki fam codes)
         => UTx ki codes MetaVarIK at
         -> MetaValuation ki codes
         -> UTx ki codes (Change ki codes) at
utxApply (UTxHole var) val
  | UTxE

-}

{-


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
