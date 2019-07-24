{-# LANGUAGE PolyKinds        #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE GADTs            #-}
module Data.Digems.Patch.ThinningSpec (spec) where

import qualified Data.Set as S

import Generics.MRSOP.Base
import Generics.MRSOP.Util
import Generics.MRSOP.Holes

import Data.Functor.Const
import Data.Exists
import Data.Digems.Patch
import Data.Digems.Patch.Diff
import Data.Digems.Patch.Show
import Data.Digems.Patch.Thinning as PT
import qualified Data.Digems.Change.Thinning as CT
import Data.Digems.MetaVar
import Data.Digems.Change
import Languages.RTree
import Languages.RTree.Diff

import Test.QuickCheck
import Test.Hspec

import Control.Monad.State
import Control.Monad.Cont
import qualified Data.Map as M

context_alpha_eq :: (EqHO ki)
                 => Holes ki codes (MetaVarIK ki) at
                 -> Holes ki codes (MetaVarIK ki) at
                 -> Bool
context_alpha_eq x y = aux
  where
    aux :: Bool
    aux = (`runCont` id) $
        callCC $ \exit -> flip evalStateT M.empty $ do
          holesMapM (uncurry' (check (cast exit $ False))) (holesLCP x y)
          return True

    cast :: (Bool -> Cont Bool b)
         -> Bool -> Cont Bool (Const () a)
    cast f b = (const (Const ())) <$> f b

    check :: (Cont Bool (Const () at))
          -> Holes ki codes (MetaVarIK ki) at
          -> Holes ki codes (MetaVarIK ki) at
          -> StateT (M.Map Int Int) (Cont Bool) (Const () at)
    check exitF (Hole _ vx) (Hole _ vy) = do
      m <- get
      case M.lookup (metavarGet vx) m of
        Nothing -> modify (M.insert (metavarGet vx) (metavarGet vy))
                >> return (Const ())
        Just vz -> if metavarGet vy /= vz
                   then lift exitF 
                   else return (Const ())
    check exitF _ _ = lift exitF

thin_domain_eq :: Property
thin_domain_eq = forAll genSimilarTrees'' $ \(a , o , b)
  -> let oa = digemRTree o a
         ob = digemRTree o b
      in case (,) <$> PT.thin oa ob <*> PT.thin ob oa of
           Left err -> counterexample ("Thinning failed with: " ++ show err) False
           Right (oa' , ob') -> 
             property $ context_alpha_eq
                          (domain $ distrCChange oa')
                          (domain $ distrCChange ob')

-----------------------------
               
thin_respect_spans :: Property
thin_respect_spans = forAll genSimilarTrees'' $ \(a , o , b)
  -> let oa = digemRTree o a
         ob = digemRTree o b
      in case PT.thin oa ob of
           Left err -> counterexample ("Thinning failed with: " ++ show err) False
           Right oa' -> property $ applyRTree oa' o == Right a
               
---------------------------

thin_pp_is_p :: Property
thin_pp_is_p = forAll genSimilarTrees' $ \(a , b)
  -> let ab = digemRTree a b
      in case PT.thin ab ab of
           Left err -> counterexample ("Thinning failed with: " ++ show err) False
           Right ab' -> property $ patchEq ab ab'
               

-------------------------------

lf :: String -> RTree
lf x = x :>: []

bin :: RTree -> RTree -> RTree
bin l r = "bin" :>: [l , r]

a1 , o1 , b1 :: RTree
a1 = bin (bin (lf "w") (lf "z")) (bin (lf "x") (lf "y")) 
o1 = bin (bin (lf "x") (lf "y")) (bin (lf "w") (lf "z"))
b1 = bin (bin (lf "y") (lf "x")) (bin (lf "w") (lf "z"))

oa1 = digemRTree o1 a1
ob1 = digemRTree o1 b1 `withFreshNamesFrom` oa1

coa1 = distrCChange oa1
cob1 = distrCChange ob1 

---------------------

a2 , o2 , b2 :: RTree
a2 = "e" :>: ["j" :>: []]
o2 = "e" :>: ["a" :>: ["j" :>: []],"a" :>: ["j" :>: []]]
b2 = "a" :>: ["j" :>: [],"e" :>: []]

oa2 = digemRTree o2 a2
ob2 = digemRTree o2 b2 `withFreshNamesFrom` oa2

coa2 = distrCChange oa2
cob2 = distrCChange ob2 

-----------------------
--

a3 , o3 , b3 :: RTree
a3 = "e" :>: ["a" :>: [], "B" :>: [], "c" :>: []]
o3 = "e" :>: ["a" :>: [], "b" :>: [], "c" :>: []]
b3 = "e" :>: ["A" :>: [], "b" :>: [], "c" :>: []]

oa3 = digemRTree o3 a3
ob3 = digemRTree o3 b3

a4 = "k" :>: ["b" :>: [],"f" :>: []]
o4 = "k" :>: ["b" :>: [],"b" :>: []]
b4 = "k" :>: ["m" :>: [],"b" :>: []]

oa4 = digemRTree o4 a4
ob4 = digemRTree o4 b4

Right coa4 = PT.thin oa4 ob4
Right cob4 = PT.thin ob4 oa4

ca = domain $ distrCChange coa4
cb = domain $ distrCChange cob4

ok = context_alpha_eq ca cb

spec :: Spec
spec = do
  describe "thin" $ do
    it "is always possible for spans" $ property thin_respect_spans
    it "is symmetric w.r.t. domains"  $ property thin_domain_eq
    it "respects: thin p p == p"      $ property thin_pp_is_p


