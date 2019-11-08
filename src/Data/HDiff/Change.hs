{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE GADTs                 #-}
{-# OPTIONS_GHC -Wno-orphans       #-}
module Data.HDiff.Change where

import           Control.Monad.Cont
import           Control.Monad.State
import           Data.Functor.Sum
import           Data.Functor.Const
import qualified Data.Map as M
import qualified Data.Set as S
import           Data.Type.Equality
----------------------------------------
import           Generics.MRSOP.Util
import           Generics.MRSOP.Base
----------------------------------------
import           Data.Exists
import           Data.HDiff.MetaVar
import           Generics.MRSOP.Holes
import           Generics.MRSOP.HDiff.Holes

-- this has the ShowHO (Const a) instance
import           Generics.MRSOP.AG ()


-- |A 'CChange', or, closed change, consists in a declaration of metavariables
--  and two contexts. The precondition is that every variable declared
--  occurs at least once in ctxDel and that every variable that occurs in ctxIns
--  is declared.
--  
data CChange ki codes at where
  CMatch :: { cCtxVars :: S.Set (Exists (MetaVarIK ki))
            , cCtxDel  :: Holes ki codes (MetaVarIK ki) at 
            , cCtxIns  :: Holes ki codes (MetaVarIK ki) at }
         -> CChange ki codes at

-- |smart constructor for 'CChange'. Enforces the invariant
cmatch :: Holes ki codes (MetaVarIK ki) at -> Holes ki codes (MetaVarIK ki) at
       -> CChange ki codes at
cmatch del ins = maybe (error "Data.HDiff.Change.cmatch: invariant failure") id
               $ cmatch' del ins

cmatch' :: Holes ki codes (MetaVarIK ki) at -> Holes ki codes (MetaVarIK ki) at
        -> Maybe (CChange ki codes at)
cmatch' del ins =
  let vi = holesGetHolesAnnWith'' Exists ins
      vd = holesGetHolesAnnWith'' Exists del
   in if vi == vd
      then Just $ CMatch vi del ins
      else Nothing

-- |A 'Domain' is just a deletion context. Type-synonym helps us
-- identify what's what on the algorithms below.
type Domain ki codes = Holes ki codes (MetaVarIK ki) 

domain :: CChange ki codes at -> Domain ki codes at
domain = cCtxDel


unCMatch :: CChange ki codes at -> (Holes ki codes (MetaVarIK ki) :*: Holes ki codes (MetaVarIK ki)) at
unCMatch (CMatch _ del ins) = del :*: ins

-- |Returns the maximum variable in a change
cMaxVar :: CChange ki codes at -> Int
cMaxVar = maybe 0 id . S.lookupMax . S.map (exElim metavarGet) . cCtxVars

instance HasIKProjInj ki (CChange ki codes) where
  konInj k = CMatch S.empty (HOpq' k) (HOpq' k)
  varProj pk (CMatch _ (Hole _ h) _)    = varProj pk h
  varProj _  (CMatch _ (HPeel _ _ _) _) = Just IsI
  varProj _  (CMatch _ _ _)             = Nothing

instance (TestEquality ki) => TestEquality (CChange ki codes) where
  testEquality (CMatch _ x _) (CMatch _ y _)
    = testEquality x y

-- |Alpha-equality for 'CChange'
changeEq :: (EqHO ki) => CChange ki codes at -> CChange ki codes at -> Bool
changeEq (CMatch v1 d1 i1) (CMatch v2 d2 i2)
  = S.size v1 == S.size v2 && holes2Eq (d1 :*: i1) (d2 :*: i2)

-- |Alpha-equality for 'Holes2'
holes2Eq :: (EqHO ki) => Holes2 ki codes at -> Holes2 ki codes at -> Bool
holes2Eq (d1 :*: i1) (d2 :*: i2) = aux
 where
   aux :: Bool
   aux = (`runCont` id) $
     callCC $ \exit -> flip evalStateT M.empty $ do
       _ <- holesMapM (uncurry' (reg (cast exit))) (holesLCP d1 d2)
       _ <- holesMapM (uncurry' (chk (cast exit))) (holesLCP i1 i2)
       return True
   
   cast :: (Bool -> Cont Bool b)
        -> Bool -> Cont Bool (Const () a)
   cast f b = (const (Const ())) <$> f b

   reg :: (Bool -> Cont Bool (Const () at))
       -> Holes ki codes (MetaVarIK ki) at
       -> Holes ki codes (MetaVarIK ki) at
       -> StateT (M.Map Int Int) (Cont Bool) (Const () at)
   reg _ (Hole' m1) (Hole' m2) 
     = modify (M.insert (metavarGet m1) (metavarGet m2))
     >> return (Const ())
   reg exit _ _ 
     = lift $ exit False

   chk :: (Bool -> Cont Bool (Const () at))
       -> Holes ki codes (MetaVarIK ki) at
       -> Holes ki codes (MetaVarIK ki) at
       -> StateT (M.Map Int Int) (Cont Bool) (Const () at)
   chk exit (Hole' m1) (Hole' m2) 
     = do st <- get
          case M.lookup (metavarGet m1) st of
            Nothing -> lift $ exit False
            Just r  -> if r == metavarGet m2
                       then return (Const ())
                       else lift $ exit False
   chk exit _ _ = lift (exit False)



-- |Issues a copy, this is a closed change analogous to
--  > \x -> x
changeCopy :: MetaVarIK ki at -> CChange ki codes at
changeCopy vik = CMatch (S.singleton (Exists vik)) (Hole' vik) (Hole' vik)

-- |Checks whetehr a change is a copy.
isCpy :: (EqHO ki) => CChange ki codes at -> Bool
isCpy (CMatch _ (Hole' v1) (Hole' v2))
  -- arguably, we don't even need that since changes are closed.
  = metavarGet v1 == metavarGet v2
isCpy _ = False

makeCopyFrom :: CChange ki codes at -> CChange ki codes at
makeCopyFrom chg = case cCtxDel chg of
  Hole  _ var -> changeCopy var
  HPeel _ _ _ -> changeCopy (NA_I (Const 0))
  HOpq  _ k   -> changeCopy (NA_K (Annotate 0 k))
  
-- |Renames all changes within a 'Holes' so that their
--  variable names will not clash.
cWithDisjNamesFrom :: CChange ki codes at
                   -> CChange ki codes at
                   -> CChange ki codes at
cWithDisjNamesFrom (CMatch vs del ins) q
  = let vmax = cMaxVar q + 1
     in CMatch (S.map (exMap $ metavarAdd vmax) vs)
               (holesMap (metavarAdd vmax) del)
               (holesMap (metavarAdd vmax) ins)

-- |A Utx with closed changes distributes over a closed change
--
distrCChange :: Holes ki codes (CChange ki codes) at -> CChange ki codes at
distrCChange = naiveDistr -- . alphaRenameChanges    
  where
    naiveDistr utx =
      let vars = S.foldl' S.union S.empty
               $ holesGetHolesAnnWith'' cCtxVars utx
          del  = holesJoin $ holesMap cCtxDel utx
          ins  = holesJoin $ holesMap cCtxIns utx
       in CMatch vars del ins

-- |A 'OChange', or, open change, is analogous to a 'CChange',
--  but has a list of free variables. These are the ones that appear
--  in 'oCtxIns' but not in 'oCtxDel'
data OChange ki codes at where
  OMatch :: { oCtxVDel :: S.Set (Exists (MetaVarIK ki))
            , oCtxVIns :: S.Set (Exists (MetaVarIK ki))
            , oCtxDel  :: Holes ki codes (MetaVarIK ki) at 
            , oCtxIns  :: Holes ki codes (MetaVarIK ki) at }
         -> OChange ki codes at

-- |Given two treefixes, constructs and classifies a change from
-- them.
change :: Holes ki codes (MetaVarIK ki) at
       -> Holes ki codes (MetaVarIK ki) at
       -> Sum (OChange ki codes) (CChange ki codes) at
change utx uty = let vx = holesGetHolesAnnWith'' Exists utx
                     vy = holesGetHolesAnnWith'' Exists uty
                  in if vx == vy
                     then InR $ CMatch vx utx uty
                     else InL $ OMatch vx vy utx uty

-----------------------------
-- Alternate representations

type Holes2 ki codes
  = Holes ki codes (MetaVarIK ki) :*: Holes ki codes (MetaVarIK ki)
type HolesHoles2 ki codes 
  = Holes ki codes (Holes2 ki codes)

fst' :: (f :*: g) x -> f x
fst' (Pair a _) = a

snd' :: (f :*: g) x -> g x
snd' (Pair _ b) = b

scDel :: HolesHoles2 ki codes at
      -> Holes ki codes (MetaVarIK ki) at
scDel = holesJoin . holesMap fst' 

scIns :: HolesHoles2 ki codes at
      -> Holes ki codes (MetaVarIK ki) at
scIns = holesJoin . holesMap snd'

utx2distr :: HolesHoles2 ki codes at -> Holes2 ki codes at
utx2distr x = (scDel x :*: scIns x)

utx22change :: HolesHoles2 ki codes at -> Maybe (CChange ki codes at)
utx22change x = cmatch' (scDel x) (scIns x)

change2holes2 :: (EqHO ki) => CChange ki codes at -> HolesHoles2 ki codes at 
change2holes2 (CMatch _ del ins) = holesLCP del ins

instance (TestEquality f) => TestEquality (f :*: g) where
  testEquality x y = testEquality (fst' x) (fst' y)

instance HasIKProjInj ki (Holes2 ki codes) where
  konInj  ki = (konInj ki :*: konInj ki)
  varProj p (Pair f _) = varProj p f

