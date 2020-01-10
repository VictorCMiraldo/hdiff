{-# LANGUAGE PolyKinds        #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE GADTs            #-}
module Data.HDiff.ThinningSpec (spec) where


import Control.Monad.Except

import Data.Functor.Const
import Data.HDiff.Base
import Data.HDiff.Thinning
import Data.HDiff.Diff
import Data.HDiff.MetaVar
import Languages.RTree
import Languages.RTree.Diff

import Test.QuickCheck
import Test.Hspec

import Generics.Simplistic
import Generics.Simplistic.Util


import Control.Monad.State
import Control.Monad.Cont
import qualified Data.Map as M

context_alpha_eq :: Holes prim MetaVar at
                 -> Holes prim MetaVar at
                 -> Bool
context_alpha_eq x y = aux
  where
    aux :: Bool
    aux = (`runCont` id) $
        callCC $ \exit -> flip evalStateT M.empty $ do
          _ <- holesMapM (uncurry' (check (cast exit $ False))) (lcp x y)
          return True

    cast :: (Bool -> Cont Bool b)
         -> Bool -> Cont Bool (Const () a)
    cast f b = (const (Const ())) <$> f b

    check :: (Cont Bool (Const () at))
          -> Holes prim MetaVar at
          -> Holes prim MetaVar at
          -> StateT (M.Map Int Int) (Cont Bool) (Const () at)
    check exitF (Hole vx) (Hole vy) = do
      m <- get
      case M.lookup (metavarGet vx) m of
        Nothing -> modify (M.insert (metavarGet vx) (metavarGet vy))
                >> return (Const ())
        Just vz -> if metavarGet vy /= vz
                   then lift exitF 
                   else return (Const ())
    check exitF _ _ = lift exitF

thin_domain_eq :: DiffMode -> Property
thin_domain_eq mode = forAll genSimilarTrees'' $ \(a , o , b)
  -> let oa = hdiffRTreeHM mode 1 o a
         ob = hdiffRTreeHM mode 1 o b `withFreshNamesFrom` oa
      in case runExcept $ (,) <$> thin oa (domain ob)
                              <*> thin ob (domain oa) of
           Left err -> counterexample ("Thinning failed") False
           Right (oa' , ob') -> 
             property $ context_alpha_eq
                          (domain oa')
                          (domain ob')

-----------------------------
               
thin_respect_spans :: DiffMode -> Property
thin_respect_spans mode = forAll genSimilarTrees'' $ \(a , o , b)
  -> let oa = hdiffRTreeHM mode 1 o a
         ob = hdiffRTreeHM mode 1 o b `withFreshNamesFrom` oa
      in case runExcept $ thin oa (domain ob) of
           Left err -> counterexample ("Thinning failed") False
           Right oa' -> property $ applyRTree oa' o == Right a
               
---------------------------

thin_pp_is_p :: DiffMode -> Property
thin_pp_is_p mode = forAll genSimilarTrees' $ \(a , b)
  -> let ab = hdiffRTreeHM mode 1 a b
      in case runExcept $ thin ab (domain ab) of
           Left err -> counterexample ("Thinning failed ") False
           Right ab' -> property $ patchEq ab ab'
               
-------------------------------

spec :: Spec
spec = do
  flip mapM_ (enumFrom (toEnum 0)) $ \m -> do
    describe ("thin (" ++ show m ++ ")") $ do
      it "is always possible for spans" $ property (thin_respect_spans m)
      it "is symmetric w.r.t. domains"  $ property (thin_domain_eq m)
      it "respects: thin p p == p"      $ property (thin_pp_is_p m)



{-

lf :: String -> RTree
lf x = x :>: []

bin :: RTree -> RTree -> RTree
bin l r = "bin" :>: [l , r]

a1 , o1 , b1 :: RTree
a1 = bin (bin (lf "w") (lf "z")) (bin (lf "x") (lf "y")) 
o1 = bin (bin (lf "x") (lf "y")) (bin (lf "w") (lf "z"))
b1 = bin (bin (lf "y") (lf "x")) (bin (lf "w") (lf "z"))

oa1 = hdiffRTree o1 a1
ob1 = hdiffRTree o1 b1 `withFreshNamesFrom` oa1

coa1 = distrCChange oa1
cob1 = distrCChange ob1 

---------------------

a2 , o2 , b2 :: RTree
a2 = "e" :>: ["j" :>: []]
o2 = "e" :>: ["a" :>: ["j" :>: []],"a" :>: ["j" :>: []]]
b2 = "a" :>: ["j" :>: [],"e" :>: []]

oa2 = hdiffRTree o2 a2
ob2 = hdiffRTree o2 b2 `withFreshNamesFrom` oa2

coa2 = distrCChange oa2
cob2 = distrCChange ob2 

-----------------------
--

a3 , o3 , b3 :: RTree
a3 = "e" :>: ["a" :>: [], "B" :>: [], "c" :>: []]
o3 = "e" :>: ["a" :>: [], "b" :>: [], "c" :>: []]
b3 = "e" :>: ["A" :>: [], "b" :>: [], "c" :>: []]

oa3 = hdiffRTree o3 a3
ob3 = hdiffRTree o3 b3

a4 = "k" :>: ["b" :>: [],"f" :>: []]
o4 = "k" :>: ["b" :>: [],"b" :>: []]
b4 = "k" :>: ["m" :>: [],"b" :>: []]

oa4 = hdiffRTree o4 a4
ob4 = hdiffRTree o4 b4

Right coa4 = PT.thin oa4 ob4
Right cob4 = PT.thin ob4 oa4

ca = domain $ distrCChange coa4
cb = domain $ distrCChange cob4

ok = context_alpha_eq ca cb

-}




