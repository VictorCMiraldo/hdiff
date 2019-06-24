{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Data.Digems.Change.TreeEditDistance where

import           Data.Functor.Const
import qualified Data.Map as M
import           Data.STRef
import           Data.Type.Equality
import           Control.Monad.ST
import           Control.Monad.Except

import           Generics.MRSOP.Base
import qualified Generics.MRSOP.GDiff as GD

import           Generics.MRSOP.Digems.Treefix
import           Data.Exists
import           Data.Digems.MetaVar
import           Data.Digems.Change
import           Data.Digems.Change.Apply

import Debug.Trace

--------------------------------------------
-- * Regular Longest Common Subsequence * --
--------------------------------------------

data ListES a
  = LC Int a (ListES a)
  | LD Int a (ListES a)
  | LI Int a (ListES a)
  | LNil
  deriving (Eq , Show)

cost :: ListES a -> Int
cost LNil       = 0
cost (LC c _ _) = c
cost (LI c _ _) = c
cost (LD c _ _) = c

meet :: ListES a -> ListES a -> ListES a
meet a b
  | cost a <= cost b = a
  | otherwise        = b

type Table a = M.Map (Int , Int) (ListES a)

-- Memoized longest-common-subsequence with parametrizable weight
lcsW :: forall a . (Eq a) => (a -> Int) -> [a] -> [a] -> ListES a
lcsW weight xs ys = runST $ do
    tbl <- newSTRef M.empty
    lcs' tbl xs ys
  where
   lcs' :: STRef s (Table a) -> [a] -> [a] -> ST s (ListES a)
   lcs' tbl xs ys = do
     let ix = (length xs , length ys)
     m <- readSTRef tbl
     case M.lookup ix m of
       Just res -> return res
       Nothing  -> do res <- lcs'' tbl xs ys
                      modifySTRef tbl (M.insert ix res)
                      return $ res

   lcs'' :: STRef s (Table a) -> [a] -> [a] -> ST s (ListES a)
   lcs'' tbl []      []     = return LNil
   lcs'' tbl (x:xs)  []     = lcs' tbl xs [] >>= \d -> return (LD (weight x + cost d) x d)
   lcs'' tbl []      (y:ys) = lcs' tbl [] ys >>= \i -> return (LI (weight y + cost i) y i)
   lcs'' tbl  (x:xs) (y:ys) =
     do i <- lcs' tbl (x:xs) ys
        c <- lcs' tbl xs ys
        d <- lcs' tbl xs (y:ys)
        let di = meet (LD (weight x + cost d) x d) (LI (weight y + cost i) y i)
        return $ if x == y then meet (LC (cost c) x c) di else di

---------------------------------------------
-- * Translating Changes to Edit Scripts * --
---------------------------------------------

fromNA :: NA ki (Fix ki codes) at -> UTx ki codes (MetaVarIK ki) at
fromNA = utxStiff

utxSize :: UTx ki codes phi at -> Int
utxSize (UTxHole x)   = 0
utxSize (UTxOpq  k)   = 1
utxSize (UTxPeel c p) = 1 + sum (elimNP utxSize p)

ted :: (EqHO ki , ShowHO ki , TestEquality ki)
     => CChange ki codes at -> NA ki (Fix ki codes) at
     -> Either String Int
ted (CMatch _ del ins) elm =
  -- Since we can't have duplications or swaps in the edit-script
  -- world, we must decide which variables will be copied.
  -- To do that, we will run a least-common-subsequence weighting
  -- each variable by the size of the tree it was instantiated too.
  let vd   = reverse $ utxGetHolesWith' metavarGet del
      vi   = reverse $ utxGetHolesWith' metavarGet ins
   in case runExcept (pmatch del (fromNA elm)) of
        Left err -> Left ("Element not in domain. " ++ show err)
        Right s  ->
          let sizes_s = M.map (exElim utxSize) s
              ves     = lcsW (\v -> sizes_s M.! v) vd vi
           in trace (show ves ++ "\n") $ return $ computeTed s ves
                     + sum (utxGetHolesWith' getConst $ utxMap (Const . uncurry' di)
                                                      $ utxLCP del ins)
  where
    di x y = utxSize x + utxSize y

metavarSize :: (EqHO ki , TestEquality ki , ShowHO ki)
            => Subst ki codes (MetaVarIK ki) -> Int -> Int
metavarSize s v = case M.lookup v s of
                    Nothing   -> error (show v ++ " [!] not found ")
                    (Just vi) -> exElim utxSize vi

computeTed :: (EqHO ki , TestEquality ki , ShowHO ki)
           => Subst ki codes (MetaVarIK ki)
           -> ListES Int
           -> Int
computeTed sigma LNil = 0 
computeTed sigma (LC _ _ ves) = computeTed sigma ves
computeTed sigma (LD _ x ves) = metavarSize sigma x + computeTed sigma ves
computeTed sigma (LI _ x ves) = metavarSize sigma x + computeTed sigma ves
