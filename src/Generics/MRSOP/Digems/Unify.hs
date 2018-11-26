{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}
module Generics.MRSOP.Digems.Unify where

import Data.Type.Equality
import qualified Data.Map as M
import qualified Data.Set as S
import Control.Monad
import Control.Monad.Writer
import Control.Monad.Except
import Control.Monad.State

import Data.Digems.Diff.MetaVar

import Generics.MRSOP.Util
import Generics.MRSOP.Base
import Generics.MRSOP.Digems.Treefix

data UnificationErr :: (kon -> *) -> [[[Atom kon]]] -> * where
  UndefinedVar      :: Int -> UnificationErr ki codes
  IncompatibleTerms :: String -> Term ki codes ix -> Term ki codes ix -> UnificationErr ki codes
  IncompatibleTypes :: UnificationErr ki codes

{-
instance (Show1 ki) => Show (UnificationErr ki codes) where
  showsPrec n (UndefinedVar v)
    = showParen (n > 0) $ shows "UndefinedVar "
                        . shows v
  showsPrec n (IncompatibleTerms t u)
    = showParen (n > 0) $ shows "IncompatibleTerms "
                        . shows (show1 t)
                        . shows " "
                        . shows (show1 u)
  showsPrec n IncompatibleTypes
    = shows "IncompatibleTypes"
-}
instance Show (UnificationErr ki codes) where
  show (UndefinedVar i) = "(UndefinedVar " ++ show i ++ ")"
  show (IncompatibleTerms n _ _) = "IncompatibleTerms " ++ n
  show (IncompatibleTypes)     = "IncompatibleTypes"

data UTxE :: (kon -> *) -> [[[Atom kon]]] -> (Atom kon -> *) -> * where
  UTxE :: UTx ki codes f at -> UTxE ki codes f

utxe :: (forall at . UTx ki codes f at -> UTx ki codes f at)
     -> UTxE ki codes f -> UTxE ki codes f
utxe f (UTxE x) = UTxE (f x)

type Subst ki codes = M.Map Int (UTxE ki codes (MetaVarIK ki))
type Term  ki codes = UTx ki codes (MetaVarIK ki)

type UnifyM ki codes = StateT (Subst ki codes)
                              (Except (UnificationErr ki codes))

type Unifiable ki codes = (Show1 ki , Eq1 ki , TestEquality ki)

-- |We try to unify @pa@ and @pq@ onto @ea@. The idea is that
--  we instantiate the variables of @pa@ with their corresponding expression
--  on @pb@, and substitute those in @ea@. Whereas if we reach a variable in @pb@
--  we ignore whatever was on @ea@ and give that variable instead.
--
utxUnify :: (Unifiable ki codes)
         => Term ki codes ix
         -> Term ki codes ix
         -> Term ki codes ix
         -> Either (UnificationErr ki codes) (Term ki codes ix)
utxUnify pa pb ea
  = let pb' = uniquenessNaming pa pb
     in runExcept $ evalStateT (unifyL pa pb' >> substR pb' ea) M.empty
  where
    uniquenessNaming :: Term ki codes iy -> Term ki codes ix -> Term ki codes ix
    uniquenessNaming x = let varsx  = utxGetHolesWith metavarGet x
                             varmax = maybe 0 id $ S.lookupMax varsx
                          in utxRefine (UTxHole . metavarAdd varmax) UTxOpq

-- |@unifyL pa pb@ traverses @pa@ and @pb@ instantiating the variables of @pa@.
unifyL :: (Unifiable ki codes)
       => Term ki codes ix
       -> Term ki codes ix
       -> UnifyM ki codes ()
unifyL (UTxHole var) y = modify (M.insert (metavarGet var) (UTxE y))
unifyL x (UTxHole var) = return ()
unifyL x@(UTxOpq ox) y@(UTxOpq oy)
  | eq1 ox oy = return ()
  | otherwise = throwError (IncompatibleTerms (show1 ox ++ ";" ++ show1 oy) x y)
unifyL x@(UTxPeel cx px) y@(UTxPeel cy py) =
  case testEquality cx cy of
    Nothing   -> throwError (IncompatibleTerms "2" x y)
    Just Refl -> void $ elimNPM (uncurry' unifyL) (zipNP px py)

-- |The second step is @substR pb ea@, where we substitue the variables
--  in @ea@ for the values they were instantiated for in @pa@,
--  but using the variables in @pb@ to take precedence.
substR :: (Unifiable ki codes)
       => Term ki codes ix
       -> Term ki codes ix
       -> UnifyM ki codes (Term ki codes ix)
substR (UTxHole var) _ = return (UTxHole var)
substR _ (UTxHole var) = get >>= lookupVar var
substR _ (UTxOpq oy)   = return $ UTxOpq oy
substR x@(UTxPeel cx px) y@(UTxPeel cy py) =
  case testEquality cx cy of
    Nothing   -> throwError (IncompatibleTerms "3" x y)
    Just Refl -> UTxPeel cy <$> mapNPM (uncurry' substR) (zipNP px py)

lookupVar :: forall ki codes ix
           . (Unifiable ki codes)
          => MetaVarIK ki ix
          -> Subst ki codes
          -> UnifyM ki codes (Term ki codes ix)
lookupVar var = maybe (throwError (UndefinedVar $ metavarGet var)) cast
              . M.lookup (metavarGet var)
  where
    cast :: UTxE ki codes (MetaVarIK ki)
         -> UnifyM ki codes (Term ki codes ix)
    cast (UTxE res) = case testEquality res (UTxHole var) of
      Nothing   -> throwError IncompatibleTypes
      Just Refl -> return res

{-
replace :: (Unifiable ki codes)
        => MetaVarIK ki ix
        -> Term ki codes ix
        -> Term ki codes iy
        -> Term ki codes iy
replace var x = utxRefine (go x var) UTxOpq
  where
    go :: (Unifiable ki codes)
       => Term ki codes ix
       -> MetaVarIK ki ix
       -> MetaVarIK ki iy
       -> UTx ki codes (MetaVarIK ki) iy
    go x var v = case testEquality var v of
      Nothing   -> UTxHole v
      Just Refl -> if metavarGet v == metavarGet var
                   then x
                   else UTxHole v
  
unifyVar :: forall ki codes ix
          . (Unifiable ki codes)
         => MetaVarIK ki ix
         -> Term ki codes ix
         -> UnifyM ki codes ()
unifyVar var x = get
             >>= maybe notThere (either throwError isThere)
               . lookupVar var
  where
    notThere :: UnifyM ki codes ()
    notThere = if occursCheck var x
               then throwError OccursCheck
               else modify ( M.insert (metavarGet var) (UTxE x)
                           . fmap (utxe $ replace var x))

    isThere :: UTx ki codes (MetaVarIK ki) ix -> UnifyM ki codes ()
    isThere utx = _ -- unify utx x


occursCheck :: MetaVarIK ki ix
            -> Term ki codes ix
            -> Bool
occursCheck var = maybe True (const False)
                . utxRefineM (\x -> guard (metavarGet x /= metavarGet var)
                                 >> return (UTxHole x))
                             (return . UTxOpq)
    
-}
