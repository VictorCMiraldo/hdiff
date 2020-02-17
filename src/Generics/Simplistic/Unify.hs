{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}
module Generics.Simplistic.Unify
  ( -- * Substitution
    Subst , substEmpty , substInsert , substLkup , substApply , substFromVarEqs
    -- * Unification
  , UnifyErr(..) , unify , unifyWith , minimize , splitVarEqs
  ) where

import           Data.List (sort, foldl')
import qualified Data.Map as M
import           Control.Monad.Except
import           Control.Monad.State
import           Control.Monad.Writer
import           Control.Arrow (first , second)
import           Unsafe.Coerce

import Generics.Simplistic
import Generics.Simplistic.Util

-- |Unification can return succesfully or find either
-- a 'OccursCheck' failure or a 'SymbolClash' failure.
data UnifyErr kappa fam phi :: * where
  -- |The occurs-check fails when the variable in question
  -- occurs within the term its supposed to be unified with.
  OccursCheck :: [Exists phi]
              -> UnifyErr kappa fam phi
  -- |A symbol-clash is thrown when the head of the
  -- two terms is different and neither is a variabe.
  SymbolClash :: Holes    kappa fam phi at
              -> Holes    kappa fam phi at
              -> UnifyErr kappa fam phi

-- |A substitution is but a map; the existential quantifiers are
-- necessary to ensure we can reuse from "Data.Map"
--
-- Note that we must be able to compare @Exists phi@. This
-- comparison needs to work heterogeneously and it must
-- return 'EQ' only when the contents are in fact equal.
-- Even though we only need this instance for "Data.Map"
--
-- A typical example for @phi@ is @Const Int at@, representing
-- a variable. The @Ord@ instance would then be:
--
-- > instance Ord (Exists (Const Int)) where
-- >   compare (Exists (Const x)) (Exists (Const y))
-- >     = compare x y
--
type Subst kappa fam phi 
  = M.Map (Exists phi) (Exists (Holes kappa fam phi))

-- |Empty substitution
substEmpty :: Subst kappa fam phi
substEmpty = M.empty

-- |Looks a value up in a substitution, see 'substInsert'
substLkup :: (Ord (Exists phi))
          => Subst kappa fam phi -- ^
          -> phi at
          -> Maybe (Holes kappa fam phi at)
substLkup sigma var =
  case M.lookup (Exists var) sigma of
    Nothing         -> Nothing
    -- In case we found something, it must be of the same
    -- type as what we got because we only insert
    -- well-typed things.
    -- TODO: Use our sameTy method to remove the unsafeCoerce
    Just (Exists t) -> Just $ unsafeCoerce t

-- |Applies a substitution to a term; Variables not in the
-- support of the substitution are left untouched.
substApply :: forall kappa fam phi at
            . (Ord (Exists phi))
           => Subst kappa fam phi -- ^
           -> Holes kappa fam phi at
           -> Holes kappa fam phi at
substApply sigma = holesJoin
                 . holesMap (\v -> ifProgress v $ substLkup sigma v)
  where
    bigger :: phi x -> Holes kappa fam phi y -> Bool
    bigger v (Hole u) = Exists v > Exists u
    bigger _ _        = True
    
    ifProgress :: phi x -> Maybe (Holes kappa fam phi x) -> Holes kappa fam phi x
    ifProgress v (Just t)
      | bigger v t = substApply sigma t
      | otherwise  = t
    ifProgress v Nothing = Hole v

-- |Inserts a point in a substitution. Note how the index of
-- @phi@ /must/ match the index of the term being inserted.
-- This is important when looking up terms because we must
-- 'unsafeCoerce' the existential type variables to return.
--
-- Please, always use this insertion function; or, if you insert
-- by hand, ensure thetype indices match.
substInsert :: (Ord (Exists phi))
            => Subst kappa fam phi -- ^
            -> phi at
            -> Holes kappa fam phi at
            -> Subst kappa fam phi
substInsert sigma v (Hole u)
  | Exists v  < Exists u = M.insert (Exists v) (Exists (Hole u)) sigma
  | Exists v == Exists u = sigma
  | otherwise            = M.insert (Exists u) (Exists (Hole v)) sigma
substInsert sigma v x    = M.insert (Exists v) (Exists x) sigma

substFromVarEqs :: (Ord (Exists phi))
                => [Exists (phi :*: phi)]
                -> Subst kappa fam phi
substFromVarEqs s =
  let s' = foldl' (\s (Exists (v :*: u)) -> substInsert s v (Hole u)) substEmpty s
   in case minimize s' of
        Left  _   -> error "invariant broke"
        Right res -> res

-- |Unification is done in a monad.
type UnifyM kappa fam phi
  = StateT (Subst kappa fam phi) (Except (UnifyErr kappa fam phi))

-- |Attempts to unify two 'Holes'
unify :: ( Ord (Exists phi) , EqHO phi)
      => Holes kappa fam phi at -- ^
      -> Holes kappa fam phi at
      -> Except (UnifyErr kappa fam phi)
                (Subst kappa fam phi)
unify = unifyWith substEmpty

-- |Attempts to unify two 'Holes' with an already existing
-- substitution
unifyWith :: ( Ord (Exists phi) , EqHO phi)
          => Subst kappa fam phi -- ^ Starting subst
          -> Holes kappa fam phi at
          -> Holes kappa fam phi at
          -> Except (UnifyErr kappa fam phi)
                    (Subst kappa fam phi)
unifyWith sigma x y = execStateT (unifyM x y) sigma

-- Actual unification algorithm; In order to improve efficiency,
-- we first register all equivalences we need to satisfy,
-- then on 'mininize' we do the occurs-check.
unifyM :: forall kappa fam phi at
        . (EqHO phi , Ord (Exists phi)) 
       => Holes kappa fam phi at
       -> Holes kappa fam phi at
       -> UnifyM kappa fam phi ()
unifyM x y = do
  _ <- getEquivs x y
  s <- get
  case minimize s of
    Left vs  -> throwError (OccursCheck vs)
    Right s' -> put s'
  where
    getEquivs :: Holes kappa fam phi b
              -> Holes kappa fam phi b
              -> UnifyM kappa fam phi ()
    getEquivs p q = void $ holesMapM (uncurry' getEq) (lcp p q)
    
    getEq :: Holes kappa fam phi b
          -> Holes kappa fam phi b
          -> UnifyM kappa fam phi (Holes kappa fam phi b)
    getEq p (Hole var)   = record_eq var p >> return p
    getEq p@(Hole var) q = record_eq var q >> return p
    getEq p q | eqHO p q   = return p
              | otherwise  = throwError (SymbolClash p q)
           
    -- Whenever we see a variable being matched against a term
    -- we record the equivalence. First we make sure we did not
    -- record such equivalence yet, otherwise, we recursively thin
    record_eq :: phi b -> Holes kappa fam phi b -> UnifyM kappa fam phi ()
    record_eq var q = do
      sigma <- get
      case substLkup sigma var of
        -- First time we see 'var', we instantiate it and get going.
        Nothing -> when (not $ eqHO q (Hole var))
                 $ modify (\s -> substInsert s var q)
        -- It's not the first time we thin 'var'; previously, we had
        -- that 'var' was supposed to be p'. We will check whether it
        -- is the same as q, if not, we will have to thin p' with q.
        Just q' -> unless (eqHO q' q)
                 $ void $ getEquivs q q'

-- |The minimization step performs the /occurs check/ and removes
--  unecessary steps. For example;
--
--  > sigma = fromList
--  >           [ (0 , bin 1 2)
--  >           , (1 , bin 4 4) ]
--
-- Then, @minimize sigma@ will return @fromList [(0 , bin (bin 4 4) 2) , (1 , bin 4 4)]@
-- This returns @Left vs@ if occurs-check fail for variables @vs@.
--
minimize :: forall kappa fam phi . (Ord (Exists phi))
         => Subst kappa fam phi -- ^
         -> Either [Exists phi] (Subst kappa fam phi)
minimize sigma =
  let sigma' = sortVarEqs inj proj sigma -- breakCycles inj proj $ removeIds proj sigma
   in whileM sigma' [] $ \_ _
    -> M.fromList <$> (mapM (secondF (exMapM (go sigma'))) (M.toList sigma'))
  where
    inj :: Exists phi -> Exists (Holes kappa fam phi)
    inj = exMap Hole

    proj :: Exists (Holes kappa fam phi) -> Maybe (Exists phi)
    proj (Exists (Hole phi)) = Just $ Exists phi
    proj _                   = Nothing
    
    secondF :: (Functor m) => (a -> m b) -> (x , a) -> m (x , b)
    secondF f (x , a) = (x,) <$> f a

    -- The actual engine of the 'minimize' function is thinning the
    -- variables that appear in the image of the substitution under production.
    -- We use the writer monad solely to let us know whether some variables have
    -- been substituted in this current term. After one iteration
    -- of the map where no variable is further refined, we are done.
    go :: Subst kappa fam phi
       -> Holes kappa fam phi at
       -> Writer [Exists phi] (Holes kappa fam phi at)
    go ss = holesRefineVarsM $ \var -> do
           case substLkup ss var of
             -- Didn't find anything for var
             Nothing          -> return (Hole var)

{-
             -- Found out @var == var'@;
             Just (Hole var') -> if (Exists var' < Exists var)
                                 then tell [Exists var] >> return (Hole var')
                                 else return (Hole var')
-}

             -- Found out @var == r && r is not variable@
             Just r  -> tell [Exists var] >> return r

    -- | Just like nub; but works on a sorted list
    mnub :: (Ord a) => [a] -> [a]
    mnub [] = []
    mnub [x] = [x]
    mnub (x:y:ys)
      | x == y    = mnub (y:ys)
      | otherwise = x : mnub (y:ys)

    -- We loop while there is work to be done or no progress
    -- was done.
    whileM :: (Ord (Exists phi))
           => a -> [Exists phi] -> (a -> [Exists phi] -> Writer [Exists phi] a)
           -> Either [Exists phi] a
    whileM a xs f = do
      let (x' , xs') = runWriter (f a xs)
      if null xs'
      then return x'
      else if (mnub (sort xs') == mnub (sort xs))
           then Left xs'
           else whileM x' xs' f

{-
data Whatever
  = Var Int
  | Else String
  deriving (Eq , Show)

proj :: Whatever -> Maybe Int
proj (Var x) = Just x
proj _       = Nothing

s :: M.Map Int Whatever
s = M.fromList
  [ (0 , Var 1)
  , (1 , Var 2)
  , (2 , Var 0)
  , (3 , Else "x")
  , (42 , Var 5)
  ]
-}

splitVarEqs :: forall kappa fam phi
             . (Ord (Exists phi))
            => Subst kappa fam phi
            -> ([Exists (phi :*: phi)] , Subst kappa fam phi)
splitVarEqs = first (map $ uncurry unsafePair) . splitVarEqs' proj
  where
    unsafePair :: Exists phi -> Exists phi -> Exists (phi :*: phi)
    unsafePair (Exists x) (Exists y) = Exists (x :*: unsafeCoerce y)
    
    proj :: Exists (Holes kappa fam phi) -> Maybe (Exists phi)
    proj (Exists (Hole phi)) = Just $ Exists phi
    proj _                   = Nothing

splitVarEqs' :: forall a b
              . (Ord a) => (b -> Maybe a) -> M.Map a b -> ([(a , a)], M.Map a b)
splitVarEqs' proj = first (map (second unsafeProj) . M.toList)
                  . M.partition isVarEqv
  where
    unsafeProj :: b -> a
    unsafeProj = maybe (error "impossible; we just checked!") id . proj
    
    isVarEqv :: b -> Bool
    isVarEqv v = maybe False (const True) $ proj v

sortVarEqs :: forall a b
            . (Ord a) => (a -> b) -> (b -> Maybe a) -> M.Map a b -> M.Map a b
sortVarEqs inj proj = uncurry joinVarEqvs . splitVarEqs' proj
  where
    sortVarEq1 v0 v1
      | v0 <  v1   = Just (v0 , v1)
      | v0 == v1   = Nothing
      | otherwise  = Just (v1 , v0)

    joinVarEqvs :: [(a , a)] -> M.Map a b -> M.Map a b
    joinVarEqvs varEqvs rest =
      foldl' (\m (k, v) ->
        case sortVarEq1 k v of
          Nothing        -> m
          Just (k' , v') -> M.insert k' (inj v') m
       ) rest $ varEqvs

{-

import           Control.Monad.Cont
  
-- |Removes the keys that project to themselves according to
-- the provided projection.
--
-- > removeIds id $ M.fromList [(0,0), (1,2) , (3,4)]
-- >   = M.fromList [(1,2),(3,4)]
--
removeIds :: forall a b
           . (Ord a) => (b -> Maybe a) -> M.Map a b -> M.Map a b
removeIds proj = M.filterWithKey (\a b -> not $ Just a == proj b)


-- |Will make sure there are no cycles in the map as per the
-- provided function. For example,
--
-- > breakCycles id Just $ M.fromList [(0,1) , (1,2) , (2,0)]
-- >  = M.fromList [(1,0),(2,0)]
--
-- Usefull when the maps represent some equivalence; the function essentially
-- collapses the equivalence class.
breakCycles :: forall a b
             . (Ord a) => (a -> b) -> (b -> Maybe a) -> M.Map a b -> M.Map a b
breakCycles inj proj m0
  = let (flattenedCycles , m') = runState (dropCycles m0) M.empty
     in M.union flattenedCycles m'
  where
    dropCycles :: M.Map a b -> State (M.Map a b) (M.Map a b)
    dropCycles m = case findCycle m of
                     Nothing        -> return m
                     Just (a , cyc) -> do
                       modify (M.union cyc)
                       dropCycles (M.delete a (m M.\\ cyc))

    cycleFor :: a -> M.Map a b -> Maybe (M.Map a b)
    cycleFor a0 m = M.lookup a0 m >>= proj >>= go M.empty
      where
        go :: M.Map a b -> a -> Maybe (M.Map a b)
        go aux a'
          | a' == a0 || a' `M.member` aux = return aux
          | otherwise = M.lookup a' m >>= proj >>= go (M.insert a' (inj a0) aux) 

    findCycle :: M.Map a b -> Maybe (a , M.Map a b)
    findCycle m = (`runCont` id) $ callCC $
      \exit -> (>> return Nothing) . flip mapM_ (M.keys m) $
        \a -> case cycleFor a m of
                Nothing -> return ()
                Just r  -> exit $ Just (a , r)

-}
