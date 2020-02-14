{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE UndecidableSuperClasses  #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DefaultSignatures     #-}
{-# LANGUAGE StandaloneDeriving    #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# OPTIONS_GHC -Wno-orphans #-}
-- |This is a inplace clone of @simplistic-generics@ with
-- added deep representations; I should move this stuff
-- to @simplistic-generics@ at one point.
module Generics.Simplistic where

import Data.Proxy
import Data.Type.Equality
import GHC.Generics
import Control.Monad.Identity
import Control.DeepSeq

import qualified Data.Set as S

import Generics.Simplistic.Util 

import Type.Reflection


---------------------
-- Representations --
---------------------

data SMeta i t where
  SM_D :: Datatype    d => SMeta D d
  SM_C :: Constructor c => SMeta C c
  SM_S :: Selector    s => SMeta S s
deriving instance Show (SMeta i t)
deriving instance Eq   (SMeta i t)

-- Dirty trick to access the dictionaries I need
data SMetaI d f x = SMetaI
smetaI :: SMeta i t -> SMetaI t Proxy ()
smetaI _ = SMetaI

getDatatypeName :: SMeta D d -> String
getDatatypeName x@SM_D = datatypeName (smetaI x)

getConstructorName :: SMeta C c -> String
getConstructorName x@SM_C = conName (smetaI x)

-- A Value of type @REP prim f rep@ represents one layer of
-- rep and, for the atoms of rep that are not elems of
-- the primitive types, some custom data dictated by a functor f.
-- You know where this is going.
infixr 5 :**:
data SRep w f where
  S_U1   ::                          SRep w U1
  S_L1   ::              SRep w f -> SRep w (f :+: g)
  S_R1   ::              SRep w g -> SRep w (f :+: g)
  (:**:) :: SRep w f  -> SRep w g -> SRep w (f :*: g)
  S_K1   ::              w a      -> SRep w (K1 i a)
  S_M1   :: SMeta i t -> SRep w f -> SRep w (M1 i t f)
deriving instance (forall a. Show (w a)) => Show (SRep w f)
deriving instance (forall a. Eq   (w a)) => Eq   (SRep w f)

repDatatypeName :: SRep w f -> String
repDatatypeName (S_M1 x@SM_D _)
  = getDatatypeName x
repDatatypeName (S_M1 _ x)
  = repDatatypeName x
repDatatypeName (S_L1 x)
  = repDatatypeName x
repDatatypeName (S_R1 x)
  = repDatatypeName x
repDatatypeName _
  = error "Please; use GHC's deriving mechanism. This keeps M1's at the top of the Rep"

repConstructorName :: SRep w f -> String
repConstructorName (S_M1 x@SM_C _)
  = getConstructorName x
repConstructorName (S_M1 _ x)
  = repConstructorName x
repConstructorName (S_L1 x)
  = repConstructorName x
repConstructorName (S_R1 x)
  = repConstructorName x
repConstructorName _
  = error "Please; use GHC's deriving mechanism. This keeps M1's at the top of the Rep"


zipSRep :: SRep w f -> SRep z f -> Maybe (SRep (w :*: z) f)
zipSRep S_U1         S_U1         = return S_U1
zipSRep (S_L1 x)     (S_L1 y)     = S_L1 <$> zipSRep x y
zipSRep (S_R1 x)     (S_R1 y)     = S_R1 <$> zipSRep x y
zipSRep (S_M1 m x)   (S_M1 _ y)   = S_M1 m <$> zipSRep x y
zipSRep (x1 :**: x2) (y1 :**: y2) = (:**:) <$> (zipSRep x1 y1)
                                           <*> (zipSRep x2 y2)
zipSRep (S_K1 x)     (S_K1 y)     = return $ S_K1 (x :*: y)
zipSRep _            _            = Nothing

repLeaves :: (forall x . w x -> r) -- ^ leaf extraction
          -> (r -> r -> r)         -- ^ join product
          -> r                     -- ^ empty
          -> SRep w rep -> r
repLeaves _ _ e S_U1       = e
repLeaves l j e (S_L1 x)   = repLeaves l j e x
repLeaves l j e (S_R1 x)   = repLeaves l j e x
repLeaves l j e (S_M1 _ x) = repLeaves l j e x
repLeaves l j e (x :**: y) = j (repLeaves l j e x) (repLeaves l j e y)
repLeaves l _ _ (S_K1 x)   = l x

repLeavesList :: SRep w rep -> [Exists w]
repLeavesList = repLeaves ((:[]) . Exists) (++) []

repMapM :: (Monad m)
        => (forall y . f y -> m (g y))
        -> SRep f rep -> m (SRep g rep)
repMapM _f (S_U1)    = return S_U1
repMapM f (S_K1 x)   = S_K1 <$> f x
repMapM f (S_M1 m x) = S_M1 m <$> repMapM f x
repMapM f (S_L1 x)   = S_L1 <$> repMapM f x
repMapM f (S_R1 x)   = S_R1 <$> repMapM f x
repMapM f (x :**: y)
  = (:**:) <$> repMapM f x <*> repMapM f y

repMap :: (forall y . f y -> g y)
       -> SRep f rep -> SRep g rep
repMap f = runIdentity . repMapM (return . f)

--------------------------------
-- Holes -- 


type PrimCnstr prim b
  = (Elem b prim , Show b , Eq b , Typeable b)

type CompoundCnstr prim a
  = (NotElem a prim , Generic a , Typeable a)

-- |The cofree comonad and free monad on the same type;
-- this allows us to use the same recursion operator
-- for everything.
data HolesAnn prim phi h a where
  Hole' :: (Typeable a)
        => phi a
        -> h a -> HolesAnn prim phi h a
  Prim' :: (PrimCnstr prim a)
        => phi a
        -> a -> HolesAnn prim phi h a
  Roll' :: (CompoundCnstr prim a)
        => phi a
        -> SRep (HolesAnn prim phi h) (Rep a)
        -> HolesAnn prim phi h a

-- |Deep representations are easily achieved by forbiding
-- the 'Hole'' constructor and providing unit annotations.
type SFix prim = HolesAnn prim U1 V1

pattern SFix :: () => (CompoundCnstr prim a)
             => SRep (SFix prim) (Rep a)
             -> SFix prim a
pattern SFix x = Roll x
{-# COMPLETE SFix , Prim #-}

-- |A tree with holes has unit annotations
type Holes prim = HolesAnn prim U1

pattern Hole :: () => (Typeable a) => h a -> Holes prim h a
pattern Hole x = Hole' U1 x

pattern Prim :: () => (PrimCnstr prim a)
             => a -> Holes prim h a
pattern Prim a = Prim' U1 a

pattern Roll :: () => (CompoundCnstr prim a)
             => SRep (Holes prim h) (Rep a)
             -> Holes prim h a
pattern Roll x = Roll' U1 x
{-# COMPLETE Hole , Prim , Roll #-}

-- |Annotated fixpoints are also easy; forbid the 'Hole''
-- constructor but add something to every 'Roll' of
-- the representation.
type SFixAnn prim phi = HolesAnn prim phi V1

pattern PrimAnn :: () => (PrimCnstr prim a)
                => phi a -> a -> SFixAnn prim phi a
pattern PrimAnn ann a = Prim' ann a


pattern SFixAnn :: () => (CompoundCnstr prim a)
                => phi a
                -> SRep (SFixAnn prim phi) (Rep a)
                -> SFixAnn prim phi a
pattern SFixAnn ann x = Roll' ann x
{-# COMPLETE SFixAnn , PrimAnn #-}

---------------------------------

instance (forall x . NFData (phi x) , forall x . NFData (h x))
    => NFData (HolesAnn prim phi h f) where
  rnf (Prim' ann _) = rnf ann
  rnf (Hole' ann h) = rnf ann `seq` rnf h
  rnf (Roll' ann x) = rnf ann `seq` rnf x

instance (forall x . NFData (w x)) => NFData (SRep w f) where
  rnf S_U1       = ()
  rnf (S_K1 w)   = rnf w
  rnf (S_M1 _ x) = rnf x
  rnf (S_L1 x)   = rnf x
  rnf (S_R1 x)   = rnf x
  rnf (x :**: y) = rnf x `seq` rnf y

instance NFData (V1 x) where
  rnf _ = ()

instance NFData (U1 x) where
  rnf U1 = ()
  
---------------------------------

getAnn :: HolesAnn prim phi h a
       -> phi a
getAnn (Hole' ann _) = ann
getAnn (Prim' ann _) = ann
getAnn (Roll' ann _) = ann

holesMapAnnM :: (Monad m)
             => (forall x . f x   -> m (g x))
             -> (forall x . phi x -> m (psi x))
             -> HolesAnn prim phi f a -> m (HolesAnn prim psi g a)
holesMapAnnM f g (Hole' a x)   = Hole' <$> g a <*> f x
holesMapAnnM _ g (Prim' a x)   = flip Prim' x <$> g a
holesMapAnnM f g (Roll' a x) = Roll' <$> g a <*> repMapM (holesMapAnnM f g) x

holesMapM :: (Monad m)
          => (forall x . f x -> m (g x))
          -> Holes prim f a -> m (Holes prim g a)
holesMapM f = holesMapAnnM f return

holesMap :: (forall x . f x -> g x)
         -> Holes prim f a -> Holes prim g a
holesMap f = runIdentity . holesMapM (return . f)

holesMapAnn :: (forall x . f x -> g x)
            -> (forall x . w x -> z x)
            -> HolesAnn prim w f a -> HolesAnn prim z g a
holesMapAnn f g = runIdentity . holesMapAnnM (return . f) (return . g)

holesJoin :: Holes prim (Holes prim f) a -> Holes prim f a
holesJoin (Hole x) = x
holesJoin (Prim x) = Prim x
holesJoin (Roll x) = Roll (repMap holesJoin x)

holesHolesList :: Holes prim f a -> [Exists f]
holesHolesList (Hole x) = [Exists x]
holesHolesList (Prim _) = []
holesHolesList (Roll x) = concatMap (exElim holesHolesList) $ repLeavesList x

holesHolesSet :: (Ord (Exists f)) => Holes prim f a -> S.Set (Exists f)
holesHolesSet = S.fromList . holesHolesList

holesRefineVarsM :: (Monad m)
                 => (forall b . f b -> m (Holes prim g b))
                 -> Holes prim f a
                 -> m (Holes prim g a)
holesRefineVarsM f = fmap holesJoin . holesMapM f
        

holesRefineVars :: (forall b . f b -> Holes prim g b)
                -> Holes prim f a
                -> Holes prim g a
holesRefineVars f = holesJoin . runIdentity . holesMapM (return . f)
      
holesRefineM :: (Monad m)
             => (forall b . f b -> m (Holes prim g b))
             -> (forall b . (PrimCnstr prim b)
                  => b -> m (Holes prim g b))
             -> Holes prim f a
             -> m (Holes prim g a)
holesRefineM f _ (Hole x) = f x
holesRefineM _ g (Prim x) = g x
holesRefineM f g (Roll x) = Roll <$> repMapM (holesRefineM f g) x
     
holesSize :: HolesAnn prim phi h a -> Int
holesSize (Hole' _ _) = 0
holesSize (Prim' _ _) = 1
holesSize (Roll' _ x) = 1 + sum (map (exElim holesSize) $ repLeavesList x)

-- Simpler cata; separate action injecting primitives
-- into the annotation type.
cataM :: (Monad m)
      => (forall b . (CompoundCnstr prim b)
            => ann b -> SRep phi (Rep b) -> m (phi b))
      -> (forall b . (PrimCnstr prim b)
            => ann b -> b -> m (phi b))
      -> (forall b . (Typeable b) => ann b -> h b -> m (phi b))
      -> HolesAnn prim ann h a
      -> m (phi a)
cataM f g h (Roll' ann x) = repMapM (cataM f g h) x >>= f ann
cataM _ g _ (Prim' ann x) = g ann x
cataM _ _ h (Hole' ann x) = h ann x

synthesizeM :: (Monad m)
            => (forall b . Generic b
                  => ann b -> SRep phi (Rep b) -> m (phi b))
            -> (forall b . (Elem b prim)
                  => ann b -> b -> m (phi b))
           -> (forall b . (Typeable b) => ann b -> h b -> m (phi b))
            -> HolesAnn prim ann h a
            -> m (HolesAnn prim phi h a)
synthesizeM f g h = cataM (\ann r -> flip Roll' r
                                <$> f ann (repMap getAnn r))
                          (\ann b -> flip Prim' b <$> g ann b)
                          (\ann r -> flip Hole' r <$> h ann r)

synthesize :: (forall b . Generic b
                 => ann b -> SRep phi (Rep b) -> phi b)
           -> (forall b . (Elem b prim)
                 => ann b -> b -> phi b)
           -> (forall b . ann b -> h b -> phi b)
           -> HolesAnn prim ann h a
           -> HolesAnn prim phi h a
synthesize f g h = runIdentity
                 . synthesizeM (\ann -> return . f ann)
                               (\ann -> return . g ann)
                               (\ann -> return . h ann)

botElim :: V1 x -> a
botElim _ = error "botElim"

----------------------------------
-- Anti unification is so simple it doesn't
-- deserve its own module

lcp :: (Typeable a)
    => Holes prim h a -> Holes prim i a
    -> Holes prim (Holes prim h :*: Holes prim i) a
lcp (Prim x) (Prim y)
 | x == y    = Prim x
 | otherwise = Hole (Prim x :*: Prim y)
lcp x@(Roll rx) y@(Roll ry) =
  case zipSRep rx ry of
    Nothing -> Hole (x :*: y)
    Just r  -> Roll (repMap (uncurry' lcp) r)
lcp x y = Hole (x :*: y)

----------------------------------

instance EqHO h => EqHO (Holes prim h) where
  eqHO x y = all (exElim $ uncurry' go) $ holesHolesList (lcp x y)
    where
      go :: Holes prim h a -> Holes prim h a -> Bool
      go (Hole h1) (Hole h2) = eqHO h1 h2
      go _         _         = False

instance EqHO V1 where
  eqHO _ _ = True

instance EqHO h => Eq (Holes prim h t) where
   (==) = eqHO

-- Converting values to deep representations is easy and follows
-- almost the usual convention; one top level class
-- and one generic version. This time though, we need
-- special treatment on atoms.
class (CompoundCnstr prim a) => Deep prim a where
  dfrom :: a -> SFix prim a
  default dfrom :: (GDeep prim (Rep a))
                => a -> SFix prim a
  dfrom = SFix . gdfrom . from
  
  dto :: SFix prim a -> a
  default dto :: (GDeep prim (Rep a)) => SFix prim a -> a
  dto (SFix x) = to . gdto $ x

-- Your usual suspect; the GDeep typeclass
class GDeep prim f where
  gdfrom :: f x -> SRep (SFix prim) f 
  gdto   :: SRep (SFix prim) f -> f x 

-- And the class that disambiguates primitive types
-- from types in the family. This is completely hidden from
-- the user though
class GDeepAtom prim (isPrim :: Bool) a where
  gdfromAtom  :: Proxy isPrim -> a -> SFix prim a
  gdtoAtom    :: Proxy isPrim -> SFix prim a -> a

instance (CompoundCnstr prim a , Deep prim a)
     => GDeepAtom prim 'False a where
  gdfromAtom _ a = dfrom $ a
  gdtoAtom _   x = dto x

instance (PrimCnstr prim a) => GDeepAtom prim 'True a where
  gdfromAtom _ a = Prim a
  gdtoAtom   _ (Prim a) = a

-- This ties the recursive knot
instance (GDeepAtom prim (IsElem a prim) a) => GDeep prim (K1 R a) where
  gdfrom (K1 a)   = S_K1 (gdfromAtom (Proxy :: Proxy (IsElem a prim)) a)
  gdto   (S_K1 a) = K1 (gdtoAtom (Proxy :: Proxy (IsElem a prim)) a)

-- The rest of the instances are trivial
instance GDeep prim U1 where
  gdfrom U1  = S_U1
  gdto S_U1 = U1

instance (GDeep prim f , GDeep prim g) => GDeep prim (f :*: g) where
  gdfrom (x :*: y) = (gdfrom x) :**: (gdfrom y)
  gdto (x :**: y) = (gdto x) :*: (gdto y)

instance (GDeep prim f , GDeep prim g) => GDeep prim (f :+: g) where
  gdfrom (L1 x) = S_L1 (gdfrom x)
  gdfrom (R1 x) = S_R1 (gdfrom x)

  gdto (S_L1 x) = L1 (gdto x)
  gdto (S_R1 x) = R1 (gdto x)

-- Metainformation is simple to handle

class GDeepMeta i c where
  smeta :: SMeta i c

instance Constructor c => GDeepMeta C c where
  smeta = SM_C

instance Datatype d => GDeepMeta D d where
  smeta = SM_D

instance Selector s => GDeepMeta S s where
  smeta = SM_S

instance (GDeepMeta i c , GDeep prim f)
    => GDeep prim (M1 i c f) where
  gdfrom (M1 x)   = S_M1 smeta (gdfrom x)
  gdto (S_M1 _ x) = M1 (gdto x)

-------------------------------

class HasDecEq fam where
  sameTy :: forall x y . (Elem x fam , Elem y fam) 
         => Proxy fam -> Proxy x -> Proxy y -> Maybe (x :~: y)
  sameTy _ _ _ = go (hasElem :: ElemPrf x fam) (hasElem :: ElemPrf y fam)
    where
      go :: ElemPrf x fam' -> ElemPrf b fam' -> Maybe (x :~: b)
      go Here       Here      = Just Refl
      go (There rr) (There y) = go rr y
      go _          _         = Nothing

--------------------------------

{- Example 

data RTree = String :>: [RTree]
  deriving (Eq , Show)

height :: RTree -> Int
height (_ :>: []) = 0
height (_ :>: ns) = 1 + maximum (map height ns)

-- Workflow: use
--   getTypesInvolved [ ''String ] [t| RTree |]
-- Then inspect the result,
--   :i TypesInvolved
-- get the list of types; then use emacs macros!

type RTreePrims = '[ String ]
type RTreeFam   = '[ RTree , [RTree] ]

deriving instance Generic RTree
instance Deep RTreeFam RTreePrims RTree 
instance Deep RTreeFam RTreePrims [ RTree ]
instance HasDecEq RTreeFam where

test = sameTy (Proxy :: Proxy RTreeFam)
              (Proxy :: Proxy RTree)
              (Proxy :: Proxy RTree)
              

dfromRTree :: RTree -> SFix RTreeFam RTreePrims RTree
dfromRTree = dfrom

dtoRTree :: SFix RTreeFam RTreePrims RTree -> RTree
dtoRTree = dto

-}
