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
import Control.Monad.Identity

import Generics.MRSOP.Util
import Generics.MRSOP.Base
import Generics.MRSOP.Digems.Treefix
import Generics.MRSOP.Digems.Digest

import qualified Data.WordTrie as T
import Data.Digems.Diff.Preprocess
import Data.Digems.Diff.Patch

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
utxUnify _ (UTxHole var)
  = Left . unwords $ ["utxUnify:" , "hole"]
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
