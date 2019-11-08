{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE GADTs                 #-}
{-# OPTIONS_GHC -Wno-orphans       #-}
module Data.HDiff.Change.Merge where

import           Control.Monad.Cont
import           Control.Monad.State
import           Control.Monad.Except
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
import           Data.HDiff.Change
import           Data.HDiff.Change.Apply
import           Data.HDiff.Patch.Show
import           Generics.MRSOP.Holes
import           Generics.MRSOP.HDiff.Holes
import           Generics.MRSOP.HDiff.Renderer

import Debug.Trace

data Conflict :: (kon -> *) -> [[[Atom kon]]] -> Atom kon -> * where
  Conflict :: CChange ki codes at
           -> CChange ki codes at
           -> Conflict ki codes at

type C ki fam codes at = (ShowHO ki , HasDatatypeInfo ki fam codes
                         , RendererHO ki , EqHO ki , TestEquality ki)

isSimpleCpy (Hole' x :*: Hole' y) = metavarGet x == metavarGet y
isSimpleCpy _                     = False

go :: (C ki fam codes at)
      => CChange ki codes at
      -> CChange ki codes at
      -> Either Int {- (Conflict ki codes at) -} (HolesHoles2 ki codes at)
go    p q = let p0 = holesLCP (cCtxDel p) (cCtxIns p)
                q0 = holesLCP (cCtxDel q) (cCtxIns q)
             in case evalStateT (func p0 q0) mergeStateEmpty of
                  Left i  -> Left i
                  Right r -> Right $ r
  where
    func :: (C ki fam codes at)
         => HolesHoles2 ki codes at 
         -> HolesHoles2 ki codes at 
         -> MergeM ki codes (HolesHoles2 ki codes at)
    func p0 q0 = do
       let pq0 = holesLCP p0 q0
       mapM_ (exElim (uncurry' instantiate)) (holesGetHolesAnnWith' Exists pq0)
       sigma <- gets subst
       trace (unlines . map (\(x , Exists s) -> show x ++ " = " ++ show (scDel s) ++ "\n  ; " ++ show (scIns s) ) $ M.toList sigma) $ return p0
       holesMapM (uncurry' decide) pq0
       


mergeStateEmpty :: MergeState ki codes
mergeStateEmpty = MergeState M.empty

data MergeState ki codes = MergeState
  { subst :: Subst ki codes (Holes2 ki codes) 
  } 

setSubst s ms = ms { subst = s }

type MergeM ki codes = StateT (MergeState ki codes) (Either Int)
  
instantiate :: (C ki fam codes at)
            => HolesHoles2 ki codes at
            -> HolesHoles2 ki codes at
            -> MergeM ki codes ()
instantiate (Hole' p) (Hole' q) = register2 p q
instantiate (Hole' p)  cq       = register1 "L" p cq
instantiate cp        (Hole' q) = register1 "R" q cp
instantiate cp         cq       = lift (Left 1)

register2 :: (C ki fam codes at)
           => Holes2 ki codes at
           -> Holes2 ki codes at
           -> MergeM ki codes ()
register2 p q = do
  let scp = isSimpleCpy p
      scq = isSimpleCpy q
  when scp $ register1 "L'" p (Hole' q)
  when scq $ register1 "R'" q (Hole' p)
  -- needs an equality test
  when (not (scp || scq) && not (holes2Eq p q)) $ lift (Left 2)

register1 :: (C ki fam codes at)
          => String
          -> Holes2 ki codes at
          -> HolesHoles2 ki codes at
          -> MergeM ki codes ()
register1 side p q = do
  sigma <- gets subst
  -- Some thinning is necessary in here; case 9 displays the issue.
  -- It might even be that thinning removes the need for the fancy 'act'
  -- there.
  --
  -- Really need to check for:
  --  > actL
  --  >    v   = g
  --  >    phi = g
  --  >        ; e
  --  This must be flagged as a conflict! Maybe, actually, thinning takes good care
  --  refining things and we can use usual pmatch; whenever pmatch throws an
  --  IncompatibleHole; we know its a conflict...


  case runExcept (pmatch' sigma act (fst' p) q) of
    Left err     -> trace (dbg $ show err) (lift (Left 3))
    Right sigma' -> trace (dbg "") $ modify (setSubst sigma')
 where
    act :: (C ki fam codes at)
        => Holes ki codes (MetaVarIK ki) iy
        -> Holes2 ki codes iy
        -> Subst ki codes (Holes2 ki codes)
        -> Maybe (Subst ki codes (Holes2 ki codes))
    act v phi sigma = 
      -- here we must check that phi was a copy
                  flip trace (Just sigma) $ unlines [ "act" ++ side
                                                    , "  v   = " ++ show v
                                                    , "  phi = " ++ show (fst' phi)
                                                    , "      ; " ++ show (snd' phi)
                                                    ]
   
    dbg e = unlines ["register" ++ side ++ "[ " ++ e ++ "]"
                    ,"  p = " ++ show (fst' p)
                    ,"    ; " ++ show (snd' p)
                    ,"  q = " ++ show (scDel q)
                    ,"    ; " ++ show (scIns q)
                    ]


decide :: (C ki fam codes at)
        => HolesHoles2 ki codes at
        -> HolesHoles2 ki codes at
        -> MergeM ki codes (Holes2 ki codes at)
decide (Hole' p) (Hole' q) = inst2 p q
decide (Hole' p)  cq       = inst1 p cq
decide cp        (Hole' q) = inst1 q cp
decide cp         cq       = lift (Left 4)

inst1 :: (C ki fam codes at)
      => Holes2 ki codes at
      -> HolesHoles2 ki codes at
      -> MergeM ki codes (Holes2 ki codes at)
inst1 p q = do
  sigma <- gets subst
  case runExcept $ transport (snd' p) sigma of
    Left err -> trace dbg $ lift (Left 5)
    Right r  -> do
      p' <- holesRefineAnnM (\_ -> needRefine sigma) (\_ -> return . HOpq') (fst' p)
      return (p' :*: scIns r)
 where
   needRefine :: (C ki fam codes at)
              => Subst ki codes (Holes2 ki codes)
              -> MetaVarIK ki at
              -> MergeM ki codes (Holes ki codes (MetaVarIK ki) at)
   needRefine m v = case runExcept (lookupVar v m) of
     Left err -> trace "very bad!" (lift (Left 6))
     Right Nothing -> return (Hole' v)
     Right (Just r) 
       | isSimpleCpy (scDel r :*: scIns r) -> return $ Hole' v
       | otherwise                         -> return $ scDel r

   dbg = unlines ["inst"
                    ,"  p = " ++ show (fst' p)
                    ,"    ; " ++ show (snd' p)
                    ,"  q = " ++ show (scDel q)
                    ,"    ; " ++ show (scIns q)
                    ]


inst2 :: (C ki fam codes at)
      => Holes2 ki codes at
      -> Holes2 ki codes at
      -> MergeM ki codes (Holes2 ki codes at)
inst2 p q = do
  let scp = isSimpleCpy p
  if scp
  then return q
  else return p
 where








{- Examples from MergeSpec.hs

-- Apparently; registerLR is only ok
-- if either p or q is a copy.
-- 
registerLR
  p = `NA_K a[3]
    ; `NA_K a[3]
  q = `NA_K a[2]
    ; `NA_K a[2]

-- This really says: p old [1] is ((:>:) b [])
-- and p new [1] is ((:>:) b' []). This enables us to
-- store this information to maintain coherence.
registerL
  p = `NA_I (Const 1)
    ; `NA_I (Const 1)
  q = ((:>:)  b [] )
    ; ((:>:)  b' [] )

-- Again; a simple copy over some change.
registerLR
  p = `NA_I (Const 0)
    ; ((:)  ((:>:)  c [] ) `NA_I (Const 0))
  q = `NA_I (Const 0)
    ; `NA_I (Const 0)

-------------------
-------------------
-------------------

-- This is nastier; the left reached a change and the right
-- has changes inside of it. We want to apply p to q; why? how?
registerL
  p = ((:>:)  b ((:)  `NA_I (Const 3) ((:)  ((:>:)  . [] ) [] )))
    ; `NA_I (Const 3)
  q = ((:>:)  `NA_K b[4] ((:)  ((:>:)  `NA_K b[5] ((:)  ((:>:)  `NA_K u[6] ((:)  ((:>:)  3 [] ) [] )) `NA_I (Const 0))) `NA_I (Const 2)))
    ; ((:>:)  `NA_K b[4] ((:)  ((:>:)  `NA_K b[5] ((:)  ((:>:)  `NA_K u[6] ((:)  ((:>:)  4 [] ) [] )) ((:)  ((:>:)  u `NA_I (Const 0)) [] ))) `NA_I (Const 2)))

-----------------
-----------------
-----------------

-- This one is very simple; one LR with a copy
-- and one L with a simple copy too!
registerLR
  p = x
    ; x'
  q = `NA_K x[0]
    ; `NA_K x[0]

registerL
  p = `NA_I (Const 3)
    ; `NA_I (Const 3)
  q = ((:)  ((:>:)  y [] ) ((:)  ((:>:)  z [] ) [] ))
    ; ((:)  ((:>:)  y' [] ) [] )

----------------
---------------
----------------

-- There must be some equality checking on LR; it's naturally
-- ok for equal changes!
registerLR
  p = x
    ; y
  q = x
    ; y

----------------------
----------------------
----------------------

-- the usual here
registerLR
  p = `NA_K x[2]
    ; `NA_K x[2]
  q = `NA_K x[4]
    ; `NA_K x[4]

-- But now it gets interesting! Again, we want to apply q to p.
-- essentially duplicating p.
registerR
  p = ((:)  `NA_I (Const 0) ((:)  `NA_I (Const 1) [] ))
    ; ((:)  `NA_I (Const 1) ((:)  `NA_I (Const 0) [] ))
  q = `NA_I (Const 3)
    ; ((:)  ((:>:)  y `NA_I (Const 3)) `NA_I (Const 3))

-------------------
-------------------
-------------------

registerLR
  p = `NA_K x[5]
    ; `NA_K x[5]
  q = x
    ; y

registerLR
  p = ((:>:)  a [] )
    ; `NA_I (Const 4)
  q = `NA_I (Const 4)
    ; `NA_I (Const 4)

-- Looks like I want to apply p to (cCtxIns q); call it Q;
-- and return 'cmatch (cCtxDel p) Q'; looking back, this is also what
-- i want on the other cases
registerL
  p = ((:)  `NA_I (Const 4) ((:)  ((:>:)  k [] ) `NA_I (Const 2)))
    ; `NA_I (Const 2)
  q = ((:)  `NA_I (Const 6) ((:)  `NA_I (Const 5) `NA_I (Const 2)))
    ; ((:)  `NA_I (Const 6) ((:)  `NA_I (Const 5) ((:)  ((:>:)  new [] ) `NA_I (Const 2))))



-}

-- This won't work; should be a two phse process. First we go around
-- matching the deletion contexts against everything, then we come back around
-- and substitute on the insertion contexts!!!
{-

myapply :: (Applicable ki codes (MetaVarIK ki) , EqHO ki)
        => Holes2 ki codes at
        -> HolesHoles2 ki codes at
        -> Either (ApplicationErr ki codes (MetaVarIK ki)) (Holes ki codes (MetaVarIK ki) at)
myapply (d :*: i) x = runExcept (pmatch' M.empty _ d x >>= transport i)
-}

{-
   trace dbg (return p)
-}
