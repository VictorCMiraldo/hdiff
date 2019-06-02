{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE TypeSynonymInstances  #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE DeriveDataTypeable    #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE ScopedTypeVariables   #-}
module Languages.Lambda where

import Data.Type.Equality

import Generics.MRSOP.Base
import Generics.MRSOP.AG
import Generics.MRSOP.TH
import Generics.MRSOP.Digems.Digest
import Generics.MRSOP.Digems.Renderer
import Generics.MRSOP.Digems.Scoped

import Data.Text.Prettyprint.Doc (pretty)

import Debug.Trace

import Control.Monad
import Test.QuickCheck

data WKon = WString

data W :: WKon -> * where
  W_String  :: String  -> W 'WString

instance EqHO W where
  eqHO (W_String s)  (W_String ss) = s == ss

instance DigestibleHO W where
  digestHO (W_String s)  = hashStr s

instance RendererHO W where
  renderHO (W_String s) = pretty s

instance ShowHO W where
  showHO (W_String s)  = s

instance TestEquality W where
  testEquality (W_String _)  (W_String _)  = Just Refl

data Lambda
  = Var String
  | Abs String Lambda
  | App Lambda Lambda
  deriving (Eq , Show)

deriveFamilyWith ''W [t| Lambda |]

-------------------------------
-- Veerle

varName :: W k -> String
varName (W_String s) = s

instance {-# OVERLAPPING #-} Scoped W CodesLambda where
  scope IdxLambda (Var_ var) = do
    sid <- lkupName (varName var)
    return (sid , Var_ var)
  scope IdxLambda (Abs_ var term) = do
    sids <- currScope
    t' <- onFresh (declName (varName var) >> scopeFix term)
    return (Nothing , Abs_ var t')
  scope ix tag = defaultScope ix tag

test :: Lambda
test = let x = Var "x"
           y = Var "y"
        in (App (Abs "y" y) (Abs "y" y))

instance (ShowHO ki , ShowHO phi) => ShowHO (AnnFix ki codes phi) where
  showHO (AnnFix phi rest) = case sop rest of
    Tag c p -> "(" ++ showHO phi ++ " , [" ++ show c ++ ":" ++ showHO p ++ "])"

go = runScope $ scopeFix $ deep @FamLambda test
