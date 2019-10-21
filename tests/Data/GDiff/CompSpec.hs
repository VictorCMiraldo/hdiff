{-# LANGUAGE PolyKinds        #-}
{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE TypeOperators    #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE TypeApplications #-}
module Data.GDiff.CompSpec (spec) where

import Data.Type.Equality hiding (apply)

import Generics.MRSOP.Base
import Generics.MRSOP.GDiff

import Languages.RTree

import Test.QuickCheck
import Test.Hspec hiding (after)

ins :: Cof ki codes a t -> ES ki codes i (t :++: j) -> ES ki codes i (a ': j)
ins c es = Ins (1 + cost es) c es

del :: Cof ki codes a t -> ES ki codes (t :++: i) j -> ES ki codes (a ': i) j
del c es = Del (1 + cost es) c es

cpy :: Cof ki codes a t -> ES ki codes (t :++: i) (t :++: j)
                        -> ES ki codes (a ': i)   (a ': j)
cpy c es = Cpy (cost es) c es

after :: (EqHO ki , TestEquality ki)
      => ES ki codes ys zs -> ES ki codes xs ys -> Maybe (ES ki codes xs zs)
after ES0          ES0           = Just ES0
after (Ins _ c ps) ES0           = ins c  <$> ps  `after` ES0
after ES0          (Del _ c' qs) = del c' <$> ES0 `after` qs
after ps           (Del _ c' qs) = del c' <$> ps  `after` qs
after (Ins _ c ps) qs            = ins c  <$> ps  `after` qs
after (Cpy _ c ps) (Cpy _ c' qs)
  = do (Refl , Refl) <- cofHeq c c'
       cpy c <$> ps `after` qs
after (Del _ c ps) (Ins _ c' qs)
  = do (Refl , Refl) <- cofHeq c c'
       ps `after` qs
after (Del _ c ps) (Cpy _ c' qs)
  = do (Refl , Refl) <- cofHeq c c'
       del c <$> ps `after` qs
after (Cpy _ c ps) (Ins _ c' qs)
  = do (Refl , Refl) <- cofHeq c c'
       ins c <$> ps `after` qs


instance (EqHO ki , TestEquality ki) => Eq (ES ki codes xs ys) where
  ES0          == ES0           = True
  (Cpy _ c ps) == (Cpy _ c' qs) = maybe False (\(Refl , Refl) -> ps == qs)
                                $ cofHeq c c'
  (Del _ c ps) == (Del _ c' qs) = maybe False (\(Refl , Refl) -> ps == qs)
                                $ cofHeq c c'
  (Ins _ c ps) == (Ins _ c' qs) = maybe False (\(Refl , Refl) -> ps == qs)
                                $ cofHeq c c'
  _            == _             = False
  

-----------------------
-----------------------
-----------------------

after_correct :: Property
after_correct = forAll genSimilarTrees'' $ \(x , y , z)
  -> let pXY = diff @FamRTree x y
         pYZ = diff @FamRTree y z
      in case pYZ `after` pXY of
           Nothing  -> counterexample "Doesn't compose!" False
           Just pXZ -> case apply @_ @FamRTree pXZ x of
                         Nothing -> counterexample "Doesn't apply!" False
                         Just z' -> z === z'

after_optimal :: Property
after_optimal = forAll genSimilarTrees'' $ \(x , y , z)
  -> let pXY = diff @FamRTree x y
         pYZ = diff @FamRTree y z
      in case pYZ `after` pXY of
           Nothing  -> counterexample "Doesn't compose!" False
           Just pXZ -> let pXZ' = diff @FamRTree x z
                        in cost pXZ === cost pXZ'

after_right_id :: Property
after_right_id = forAll genSimilarTrees' $ \(x , y)
  -> let pXY = diff @FamRTree x y
         pXX = diff @FamRTree x x
      in case pXY `after` pXX of
           Nothing  -> counterexample "Doesn't compose!" False
           Just res -> res === pXY

after_left_id :: Property
after_left_id = forAll genSimilarTrees' $ \(x , y)
  -> let pXY = diff @FamRTree x y
         pYY = diff @FamRTree y y
      in case pYY `after` pXY of
           Nothing  -> counterexample "Doesn't compose!" False
           Just res -> res === pXY

after_assoc :: Property
after_assoc = forAll (choose (0 , 3) >>= genSimilarTreesN 4) $ \[x,y,z,w]
  -> let pXY = diff @FamRTree x y
         pYZ = diff @FamRTree y z
         pZW = diff @FamRTree z w
      in case (,) <$> (pYZ `after` pXY >>= (pZW `after`))
                  <*> (pZW `after` pYZ >>= (`after` pXY))
                of
           Nothing  -> counterexample "Doesn't compose!" False
           Just (pXZ1 , pXZ2) -> cost pXZ1 === cost pXZ2

spec :: Spec
spec = do
  describe "gdiff composition" $ do
    it "is correct"     $ property after_correct
    it "is non-optimal" $ property $ expectFailure after_optimal
    it "has right-id"   $ property $ after_right_id
    it "has left-id"    $ property $ after_left_id
    it "is associative" $ property $ after_assoc
