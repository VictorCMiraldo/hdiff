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
-- |This is a inplace clone of @simplistic-generics@ with
-- added deep representations; I should move this stuff
-- to @simplistic-generics@ at one point.
module Generics.Simplistic where

import Data.Proxy
import Data.Functor.Const
import GHC.Generics
import Control.Monad.Identity

import Generics.Simplistic.Util


---------------------
-- Representations --
---------------------

data SMeta i t where
  SM_D :: Datatype    d => SMeta D d
  SM_C :: Constructor c => SMeta C c
  SM_S :: Selector    s => SMeta S s
deriving instance Show (SMeta i t)

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

-- |The cofree comonad and free monad on the same type;
-- this allows us to use the same recursion operator
-- for everything.
data HolesAnn prim phi h a where
  Hole' :: h a -> HolesAnn prim phi h a
  Prim' :: (Elem a prim , Show a , Eq a)
        => a -> HolesAnn prim phi h a
  Roll' :: (NotElem a prim , Generic a)
        => phi a
        -> SRep (HolesAnn prim phi h) (Rep a)
        -> HolesAnn prim phi h a
deriving instance (forall a . Show (h a) , forall a . Show (phi a))
  => Show (HolesAnn prim phi h x)

-- |Deep representations are easily achieved by forbiding
-- the 'Hole'' constructor and providing unit annotations.
type SFix prim = HolesAnn prim U1 V1

pattern SFix :: () => (NotElem a prim , Generic a)
             => SRep (SFix prim) (Rep a)
             -> SFix prim a
pattern SFix x = Roll x
{-# COMPLETE SFix , Prim #-}

-- |A tree with holes has unit annotations
type Holes prim = HolesAnn prim U1

pattern Hole :: h a -> Holes prim h a
pattern Hole x = Hole' x

pattern Prim :: () => (Elem a prim , Show a , Eq a)
             => a -> Holes prim h a
pattern Prim a = Prim' a

pattern Roll :: () => (NotElem a prim , Generic a)
             => SRep (Holes prim h) (Rep a)
             -> Holes prim h a
pattern Roll x = Roll' U1 x
{-# COMPLETE Hole , Prim , Roll #-}

-- |Annotated fixpoints are also easy; forbid the 'Hole''
-- constructor but add something to every 'Roll' of
-- the representation.
type SFixAnn prim phi = HolesAnn prim phi V1

pattern PrimAnn :: () => (Elem a prim , Show a , Eq a)
                => a -> SFixAnn prim phi a
pattern PrimAnn a = Prim' a


pattern SFixAnn :: () => (NotElem a prim , Generic a)
                => phi a
                -> SRep (SFixAnn prim phi) (Rep a)
                -> SFixAnn prim phi a
pattern SFixAnn ann x = Roll' ann x
{-# COMPLETE SFixAnn , PrimAnn #-}

---------------------------------

-- This is still uncertain; it does provide a nice way of writing
-- 'cataRecM' but feels messy.

-- |Enable us to apply @f@ to @a@ only
-- when @a@ is recursive; defined as @NotElem a prim@
-- for a given list of primitive types @prim@
data OnRec prim f a where
  NRec :: (Elem a prim , Show a , Eq a)
       => a -> OnRec prim f a
  Rec  :: (NotElem a prim)
       => f a -> OnRec prim f a

data WrapRep f a where
  WrapRep :: (Generic a) => {unwrapRep :: f (Rep a)} -> WrapRep f a

unfix :: SFixAnn prim phi a
      -> OnRec prim (phi :*: WrapRep (SRep (SFixAnn prim phi))) a
unfix (PrimAnn x)   = NRec x
unfix (SFixAnn a h) = Rec (a :*: WrapRep h)

refix :: OnRec prim (SFixAnn prim phi) a -> SFixAnn prim phi a
refix (NRec x) = Prim' x
refix (Rec x)  = x
      
mapOnRecM :: (Monad m)
          => (forall y . (NotElem y prim) => f y -> m (g y))
          -> OnRec prim f a -> m (OnRec prim g a)
mapOnRecM f  (Rec  x) = Rec <$> f x
mapOnRecM _f (NRec x) = return (NRec x)

mapOnRec :: (forall y . (NotElem y prim) => f y -> g y)
         -> OnRec prim f a -> OnRec prim g a
mapOnRec f = runIdentity . mapOnRecM (return . f)

----------------------------------
-- Maps, zips, catas and synths --
----------------------------------

zipSRep :: SRep w f -> SRep z f -> Maybe (SRep (w :*: z) f)
zipSRep S_U1         S_U1         = return S_U1
zipSRep (S_L1 x)     (S_L1 y)     = S_L1 <$> zipSRep x y
zipSRep (S_R1 x)     (S_R1 y)     = S_R1 <$> zipSRep x y
zipSRep (S_M1 m x)   (S_M1 _ y)   = S_M1 m <$> zipSRep x y
zipSRep (x1 :**: x2) (y1 :**: y2) = (:**:) <$> (zipSRep x1 y1)
                                           <*> (zipSRep x2 y2)
zipSRep (S_K1 x)     (S_K1 y)     = return $ S_K1 (x :*: y)
zipSRep _            _            = Nothing

repLeaves :: SRep w f -> [Exists w]
repLeaves S_U1 = []
repLeaves (S_L1 x) = repLeaves x
repLeaves (S_R1 x) = repLeaves x
repLeaves (S_M1 _ x) = repLeaves x
repLeaves (x :**: y) = repLeaves x ++ repLeaves y
repLeaves (S_K1 x) = [Exists x]

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

holesMapM :: (Monad m)
          => (forall x . f x -> m (g x))
          -> Holes prim f a -> m (Holes prim g a)
holesMapM f (Hole x) = Hole <$> f x
holesMapM _ (Prim x) = return $ Prim x
holesMapM f (Roll x) = Roll <$> repMapM (holesMapM f) x

holesMap :: (forall x . f x -> g x)
         -> Holes prim f a -> Holes prim g a
holesMap f = runIdentity . holesMapM (return . f)

holesJoin :: Holes prim (Holes prim f) a -> Holes prim f a
holesJoin (Hole x) = x
holesJoin (Prim x) = Prim x
holesJoin (Roll x) = Roll (repMap holesJoin x)

holesHoles :: Holes prim f a -> [Exists f]
holesHoles (Hole x) = [Exists x]
holesHoles (Prim _) = []
holesHoles (Roll x) = concatMap (exElim holesHoles) $ repLeaves x

holesRefineVarsM :: (Monad m)
                 => (forall b . f b -> m (Holes prim g b))
                 -> Holes prim f a
                 -> m (Holes prim g a)
holesRefineVarsM f = fmap holesJoin . holesMapM f
        
-- Cata for recursive positions only; a little bit
-- nastier in implementation but the type is nice
cataRecM :: forall m a prim ann phi
          . (Monad m , NotElem a prim)
         => (forall b . (NotElem b prim , Generic b)
               => ann b -> SRep (OnRec prim phi) (Rep b) -> m (phi b))
         -> SFixAnn prim ann a
         -> m (phi a)
cataRecM f (SFixAnn ann x) =
  repMapM (mapOnRecM (uncurry' relayer) . unfix) x >>= f ann
 where
   relayer :: (NotElem x prim)
           => ann x -> WrapRep (SRep (SFixAnn prim ann)) x -> m (phi x)
   relayer ann' (WrapRep x') = cataRecM f (SFixAnn ann' x')

synthesizeRecM :: forall m a ann phi prim
                . (Monad m , NotElem a prim)
               => (forall b . Generic b
                     => ann b -> SRep (OnRec prim phi) (Rep b) -> m (phi b))
               -> SFixAnn prim ann a
               -> m (SFixAnn prim phi a)
synthesizeRecM f = cataRecM (\ann r -> flip SFixAnn (repMap refix r)
                               <$> f ann (repMap (mapOnRec getRecAnn) r))
  where
    getRecAnn :: (NotElem y prim) => SFixAnn prim xsi y -> xsi y
    getRecAnn (SFixAnn x _) = x

-- Simpler cata; separate action injecting primitives
-- into the annotation type.
cataM :: (Monad m)
      => (forall b . (NotElem b prim , Generic b)
            => ann b -> SRep phi (Rep b) -> m (phi b))
      -> (forall b . (Elem b prim , Show b , Eq b)
            => b -> m (phi b))
      -> SFixAnn prim ann a
      -> m (phi a)
cataM f g (SFixAnn ann x) = repMapM (cataM f g) x >>= f ann
cataM _ g (PrimAnn x)     = g x

getAnn :: (forall b . (Elem b prim , Show b , Eq b)
            => b -> phi b)
       -> SFixAnn prim phi a
       -> phi a
getAnn _   (SFixAnn ann _) = ann
getAnn def (PrimAnn x)     = def x

synthesizeM :: (Monad m)
            => (forall b . Generic b
                  => ann b -> SRep phi (Rep b) -> m (phi b))
            -> (forall b . (Elem b prim , Show b , Eq b)
                  => b -> phi b)
            -> SFixAnn prim ann a
            -> m (SFixAnn prim phi a)
synthesizeM f def = cataM (\ann r -> flip SFixAnn r
                             <$> f ann (repMap (getAnn def) r))
                        (return . PrimAnn)

----------------------------------
-- Anti unification is so simple it doesn't
-- deserve its own module

lcp :: Holes prim h a -> Holes prim i a
    -> Holes prim (Holes prim h :*: Holes prim i) a
lcp (Hole x) (Hole y)
 = Hole (Hole x :*: Hole y)
lcp (Prim x) (Prim y)
 | x == y    = Prim x
 | otherwise = Hole (Prim x :*: Prim y)
lcp x@(Roll rx) y@(Roll ry) =
  case zipSRep rx ry of
    Nothing -> Hole (x :*: y)
    Just r  -> Roll (repMap (uncurry' lcp) r)

----------------------------------

instance EqHO h => EqHO (Holes prim h) where
  eqHO x y = all (exElim $ uncurry' go) $ holesHoles (lcp x y)
    where
      go :: Holes prim h a -> Holes prim h a -> Bool
      go (Hole h1) (Hole h2) = eqHO h1 h2
      go _         _         = False


-- Converting values to deep representations is easy and follows
-- almost the usual convention; one top level class
-- and one generic version. This time though, we need
-- special treatment on atoms.
class (NotElem a prim , Generic a) => Deep prim a where
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

instance (NotElem a prim , Deep prim a) => GDeepAtom prim 'False a where
  gdfromAtom _ a = dfrom $ a
  gdtoAtom _   x = dto x

instance (Elem a prim , Show a , Eq a) => GDeepAtom prim 'True a where
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


