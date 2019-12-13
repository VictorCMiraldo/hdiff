{-# LANGUAGE DeriveFunctor         #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE ScopedTypeVariables   #-}
module Data.HDiff.Base.TED where

import qualified Data.Map as M
import           Data.STRef
import           Data.Proxy
import           Data.Type.Equality
import           Control.Arrow (second)
import           Control.Monad.ST
import           Control.Monad.Except
import           Control.Monad.Reader

import           Generics.MRSOP.Holes
import           Generics.MRSOP.Base
import qualified Generics.MRSOP.GDiff as GD

import           Generics.MRSOP.HDiff.Holes.Unify
import           Data.Exists
import           Data.HDiff.MetaVar
import           Data.HDiff.Base

-- import Debug.Trace

--------------------------------------------
-- * Regular Longest Common Subsequence * --
--------------------------------------------

data ListES a
  = LC Int a (ListES a)
  | LD Int a (ListES a)
  | LI Int a (ListES a)
  | LLP_Nil
  deriving (Eq , Show , Functor)

cost :: ListES a -> Int
cost LLP_Nil       = 0
cost (LC c _ _) = c
cost (LI c _ _) = c
cost (LD c _ _) = c

-- Will make sure to copy just the last bit on a row of things.
-- For example, 
--
--   > λ> lcs [0,1,2] [0,1,1,1,2]
--   > LC 0 (LC 1 (LI 1 (LI 1 (LC 2 LLP_Nil))))
--
-- Note how the 1 is copied to the first position, then
-- the other ones are inserted.
--
--   > λ> pushCopiesIns $ lcsW (const 1) [0,1,2] [0,1,1,1,2]
--   > LC 0 (LI 1 (LI 1 (LC 1 (LC 2 LLP_Nil))))
--
-- Here instead, we insert two 1's then copy the last one.
-- This really helps with synchronization.
pushCopiesIns :: (Eq a) => ListES a -> ListES a
pushCopiesIns LLP_Nil = LLP_Nil
pushCopiesIns (LC _ c (LI _ c' es))
  | c == c'   = LI 0 c' (pushCopiesIns (LC 0 c es))
  | otherwise = LC 0 c  (pushCopiesIns (LI 0 c' es))
pushCopiesIns (LC _ c es) = LC 0 c (pushCopiesIns es)
pushCopiesIns (LI _ c es) = LI 0 c (pushCopiesIns es)
pushCopiesIns (LD _ c es) = LD 0 c (pushCopiesIns es)


meet :: ListES a -> ListES a -> ListES a
meet a b
  | cost a <= cost b = a
  | otherwise        = b

type Table a = M.Map (Int , Int) (ListES a)

-- Memoized longest-common-subsequence with parametrizable weight
lcsW :: forall a . (Eq a) => (a -> Int) -> [a] -> [a] -> ListES a
lcsW weight xs0 ys0 = runST $ do
    tbl <- newSTRef M.empty
    lcs' tbl xs0 ys0
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
   lcs'' _   []      []     = return LLP_Nil
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

fromNA :: NA ki (Fix ki codes) at -> Holes ki codes (MetaVarIK ki) at
fromNA = na2holes

toES :: (EqHO ki , ShowHO ki , TestEquality ki , HasDatatypeInfo ki fam codes)
     => Chg ki codes at -> NA ki (Fix ki codes) at
     -> Either String (GD.ES ki codes '[ at ] '[ at ])
toES (Chg del ins) elm =
  -- Since we can't have duplications or swaps in the edit-script
  -- world, we must decide which variables will be copied.
  -- To do that, we will run a least-common-subsequence weighting
  -- each variable by the size of the tree it was instantiated too.
  let vd   = reverse $ holesGetHolesAnnWith' Exists del
      vi   = reverse $ holesGetHolesAnnWith' Exists ins
   in case runExcept (unify del (fromNA elm)) of
        Left err -> Left ("Element not in domain. " ++ show err)
        Right s  ->
          let sizes_s = M.map (exElim holesSize) s
              ves     = fmap (exElim metavarGet)
                      $ pushCopiesIns $ lcsW (\v -> sizes_s M.! v) vd vi
           in runExcept (runReaderT (compress <$> delPhase (del :* Nil) (ins :* Nil)) (s , ves))

type ToES ki codes = ReaderT (Subst ki codes (MetaVarIK ki) , ListES Int)
                             (Except String)

askSubst :: ToES ki codes (Subst ki codes (MetaVarIK ki))
askSubst  = asks fst

askListES :: ToES ki codes (ListES Int)
askListES = asks snd

gcpy :: GD.Cof ki codes at l
     -> GD.ES ki codes (l :++: ds) (l :++: is)
     -> GD.ES ki codes (at : ds)   (at : is)
gcpy c e = GD.Cpy (GD.cost e) c e

gins :: GD.Cof ki codes at l
     -> GD.ES ki codes ds (l :++: is)
     -> GD.ES ki codes ds (at : is)
gins c e = GD.Ins (1 + GD.cost e) c e

gdel :: GD.Cof ki codes at l
     -> GD.ES ki codes (l :++: ds) is
     -> GD.ES ki codes (at : ds) is
gdel c e = GD.Del (1 + GD.cost e) c e

compress :: (EqHO ki , TestEquality ki) => GD.ES ki codes is ds -> GD.ES ki codes is ds
compress GD.ES0 = GD.ES0
compress (GD.Del _ v (GD.Ins c' v' e)) =
  case GD.cofHeq v v' of
    Just (Refl , Refl) -> gcpy v (compress e)
    Nothing            -> gdel v (compress $ GD.Ins c' v' e)
compress (GD.Del _ v e)
  = gdel v $ compress e
compress (GD.Ins _ v (GD.Del c' v' e)) =
  case GD.cofHeq v v' of
    Just (Refl , Refl) -> gcpy v (compress e)
    Nothing            -> gins v (compress $ GD.Del c' v' e)
compress (GD.Ins _ v e)
  = gins v $ compress e
compress (GD.Cpy _ v e)
  = gcpy v (compress e)

cpyOnly :: (EqHO ki , ShowHO ki , TestEquality ki)
        => NP (Holes ki codes (MetaVarIK ki)) xs
        -> ToES ki codes (GD.ES ki codes xs xs)
cpyOnly Nil = return GD.ES0
cpyOnly (Hole  _ var :* xs) = fetch var >>= cpyOnly . (:* xs) 
cpyOnly (HOpq  _ k   :* xs) = gcpy (GD.ConstrK k)               <$> cpyOnly xs
cpyOnly (HPeel _ c d :* xs) = gcpy (GD.ConstrI c (listPrfNP d)) <$> cpyOnly (appendNP d xs)

delOnly :: (EqHO ki , ShowHO ki , TestEquality ki)
        => NP (Holes ki codes (MetaVarIK ki)) ds
        -> ToES ki codes (GD.ES ki codes ds '[])
delOnly Nil = return GD.ES0
delOnly (Hole  _ var :* xs) = fetch var >>= delOnly . (:* xs) 
delOnly (HOpq  _ k   :* xs) = gdel (GD.ConstrK k)               <$> delOnly xs
delOnly (HPeel _ c d :* xs) = gdel (GD.ConstrI c (listPrfNP d)) <$> delOnly (appendNP d xs)

insOnly :: (EqHO ki , ShowHO ki , TestEquality ki)
        => NP (Holes ki codes (MetaVarIK ki)) is
        -> ToES ki codes (GD.ES ki codes '[] is)
insOnly Nil = return GD.ES0
insOnly (Hole  _ var :* xs) = fetch var >>= insOnly . (:* xs) 
insOnly (HOpq  _ k   :* xs) = gins (GD.ConstrK k)               <$> insOnly xs
insOnly (HPeel _ c d :* xs) = gins (GD.ConstrI c (listPrfNP d)) <$> insOnly (appendNP d xs)

listAssoc :: ListPrf a -> Proxy b -> Proxy c
          -> ListPrf ((a :++: b) :++: c) :~: ListPrf (a :++: (b :++: c))
listAssoc LP_Nil       _  _  = Refl
listAssoc (LP_Cons pa) pb pc = case listAssoc pa pb pc of
                              Refl -> Refl

listDrop :: ListPrf i -> ListPrf (i :++: t) -> ListPrf t
listDrop LP_Nil a             = a
listDrop (LP_Cons x) (LP_Cons a) = listDrop x a

esDelListPrf :: GD.ES ki codes ds is -> ListPrf ds
esDelListPrf GD.ES0 = LP_Nil
esDelListPrf (GD.Cpy _ v e) = LP_Cons $ listDrop (cofListPrf v) (esDelListPrf e)
esDelListPrf (GD.Del _ v e) = LP_Cons $ listDrop (cofListPrf v) (esDelListPrf e)
esDelListPrf (GD.Ins _ _ e) = esDelListPrf e

esInsListPrf :: GD.ES ki codes ds is -> ListPrf is
esInsListPrf GD.ES0 = LP_Nil
esInsListPrf (GD.Cpy _ v e) = LP_Cons $ listDrop (cofListPrf v) (esInsListPrf e)
esInsListPrf (GD.Ins _ v e) = LP_Cons $ listDrop (cofListPrf v) (esInsListPrf e)
esInsListPrf (GD.Del _ _ e) = esInsListPrf e

cofListPrf :: GD.Cof ki codes at l -> ListPrf l
cofListPrf (GD.ConstrK _)   = LP_Nil
cofListPrf (GD.ConstrI _ p) = p

esDelListProxy :: GD.ES ki codes ds is -> Proxy ds
esDelListProxy _ = Proxy

esDelListProxy' :: GD.ES ki codes (d : ds) is -> Proxy ds
esDelListProxy' _ = Proxy

esInsListProxy :: GD.ES ki codes ds is -> Proxy is
esInsListProxy _ = Proxy

esInsListProxy' :: GD.ES ki codes ds (i : is) -> Proxy is
esInsListProxy' _ = Proxy

esDelCong :: ListPrf ds :~: ListPrf ds' -> GD.ES ki codes ds is -> GD.ES ki codes ds' is
esDelCong Refl = id

esInsCong :: ListPrf is :~: ListPrf is' -> GD.ES ki codes ds is -> GD.ES ki codes ds is'
esInsCong Refl = id

appendES :: GD.ES ki codes ds  is
         -> GD.ES ki codes ds' is'
         -> GD.ES ki codes (ds :++: ds') (is :++: is')
appendES GD.ES0 b = b
appendES x@(GD.Del _ v a) b = 
  case appendES a b of
    res -> case listAssoc (cofListPrf v) (esDelListProxy' x) (esDelListProxy b) of
      prf -> gdel v $ esDelCong prf res
appendES x@(GD.Ins _ v a) b = 
  case appendES a b of
    res -> case listAssoc (cofListPrf v) (esInsListProxy' x) (esInsListProxy b) of
      prf -> gins v $ esInsCong prf res
appendES x@(GD.Cpy _ v a) b = 
  case appendES a b of
    res -> case listAssoc (cofListPrf v) (esInsListProxy' x) (esInsListProxy b) of
      prf -> case listAssoc (cofListPrf v) (esDelListProxy' x) (esDelListProxy b) of
        prf' -> gcpy v $ esDelCong prf' $ esInsCong prf res

fetch :: (EqHO ki , ShowHO ki , TestEquality ki)
      => MetaVarIK ki at
      -> ToES ki codes (Holes ki codes (MetaVarIK ki) at)
fetch var = do
  sigma <- askSubst
  case substLkup sigma var of
    Nothing  -> throwError $ "fetch: var not found"
    (Just t) -> return t

delSync :: (EqHO ki , ShowHO ki , TestEquality ki)
        => MetaVarIK ki at
        -> NP (Holes ki codes (MetaVarIK ki)) ds
        -> NP (Holes ki codes (MetaVarIK ki)) is
        -> ToES ki codes (GD.ES ki codes (at ': ds) is)
delSync var ds is = do
  ls <- askListES
  case ls of
    -- This variable is meant to be 'deleted'; so we put the right
    -- number of dels there.
    LD _ var' es' -> if var' /= metavarGet var
                     then throwError "delSync: var mismatch"
                     else do
                       t   <- fetch var
                       es0 <- delOnly (t :* Nil)
                       es1 <- local (second (const es'))
                            $ delPhase ds is
                       return (appendES es0 es1)
    -- Otherwise, we delegate the sharing to the insertion phase
    -- This is by convention.
    _             -> insPhase (Hole' var :* ds) is
  
insSync :: (EqHO ki , ShowHO ki , TestEquality ki)
        => MetaVarIK ki at
        -> NP (Holes ki codes (MetaVarIK ki)) ds
        -> NP (Holes ki codes (MetaVarIK ki)) is
        -> ToES ki codes (GD.ES ki codes ds (at ': is))
insSync var ds is = do
  ls <- askListES
  case ls of
    -- This variable is meant to be 'deleted'; so we put the right
    -- number of ins there.
    LI _ var' es' -> if var' /= metavarGet var
                     then throwError "insSync: var mismatch"
                     else do
                       t   <- fetch var
                       es0 <- insOnly (t :* Nil)
                       es1 <- local (second (const es'))
                            $ insPhase ds is
                       return (appendES es0 es1)
    -- Otherwise, if this is a deletion, we sent iy back to the delete phase
    LD _ _var' _es' -> delPhase ds (Hole' var :* is)

    -- Last case, it's an actual share; we gotta remove the var from the deletion
    -- list and proceed.
    LC _ var' es' -> case ds of
      -- If the copy is already there, we take it
      (Hole' var'' :* ds') ->
        if var' /= metavarGet var
        then throwError "insSync: var mismatch"
        else do
          t   <- fetch var
          es0 <- cpyOnly (t :* Nil)
          es1 <- local (second (const es'))
               $ delPhase ds' is
          case testEquality var var'' of
            Just Refl -> return $ appendES es0 es1
            Nothing   -> throwError "insSync: types mismatch"
      -- Otherwise, we must enter the deletion phase until
      -- we find it.
      _ -> delPhase ds (Hole' var :* is)
    LLP_Nil -> throwError "insSync: premature LLP_Nil"

delPhase , insPhase
  :: (EqHO ki , ShowHO ki , TestEquality ki)
  => NP (Holes ki codes (MetaVarIK ki)) ds
  -> NP (Holes ki codes (MetaVarIK ki)) is
  -> ToES ki codes (GD.ES ki codes ds is)
delPhase Nil is  = insOnly is
delPhase (d :* ds) is =
  case d of
    Hole  _ var -> delSync var ds is
    HOpq  _ k   -> gdel (GD.ConstrK k)               <$> insPhase ds is
    HPeel _ c p -> gdel (GD.ConstrI c (listPrfNP p)) <$> insPhase (appendNP p ds) is

insPhase ds Nil = delOnly ds
insPhase ds (i :* is) = 
  case i of
    Hole  _ var -> insSync var ds is
    HOpq  _ k   -> gins (GD.ConstrK k)               <$> delPhase ds is
    HPeel _ c p -> gins (GD.ConstrI c (listPrfNP p)) <$> delPhase ds (appendNP p is) 

