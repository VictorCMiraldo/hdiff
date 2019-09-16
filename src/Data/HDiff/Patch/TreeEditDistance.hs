{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE ViewPatterns          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE ScopedTypeVariables   #-}
module Data.HDiff.Patch.TreeEditDistance where

import           Data.Type.Equality

import           Generics.MRSOP.Base
import           Generics.MRSOP.Holes
import qualified Generics.MRSOP.GDiff as GD

import           Data.HDiff.Patch 
import qualified Data.HDiff.Change.TreeEditDistance as TED

toES :: (EqHO ki , ShowHO ki , TestEquality ki)
     => RawPatch ki codes at -> NA ki (Fix ki codes) at
     -> Either String (GD.ES ki codes '[ at ] '[ at ])
toES (Hole  _ chg)    x         = TED.toES chg x
toES (HOpq  _ _)      (NA_K ox) = Right $ TED.gcpy (GD.ConstrK ox) GD.ES0
toES (HPeel _ ca ppa) (NA_I (Fix (sop -> Tag cx px))) =
  case testEquality ca cx of
    Nothing   -> Left "unapplicable"
    Just Refl -> (TED.gcpy (GD.ConstrI ca (listPrfNP ppa))
                 . TED.esDelCong (listId (listPrfNP ppa))
                 . TED.esInsCong (listId (listPrfNP ppa)))
               <$> toES' ppa px

listId :: ListPrf a -> ListPrf a :~: ListPrf (a :++: '[]) 
listId LP_Nil      = Refl
listId (LP_Cons a) = case listId a of
                      Refl -> Refl

toES' :: (EqHO ki , ShowHO ki , TestEquality ki)
      => NP (RawPatch ki codes) sum -> PoA ki (Fix ki codes) sum
      -> Either String (GD.ES ki codes sum sum)
toES' Nil Nil             = return GD.ES0
toES' (p :* ps) (x :* xs) = TED.appendES <$> toES p x <*> toES' ps xs

