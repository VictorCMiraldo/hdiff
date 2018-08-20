
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}
-- |Defines a unified interface for writing
--  pretty printers. We force the definition of pretty
--  printers in this way to be able to use this very
--  pretty printer to render a 'Generics.MRSOP.Digems.Treefix.UTx'
--  in the same style as the rest of the ast.
--
module Generics.MRSOP.Digems.Renderer where

import Data.Proxy
import Data.Functor.Const

import Data.Text.Prettyprint.Doc

import Generics.MRSOP.Util
import Generics.MRSOP.Base

class (HasDatatypeInfo ki fam codes)
    => Renderer ki fam codes where
  renderK :: Proxy fam -> ki k -> Doc ann
  renderI :: Proxy fam
          -> SNat ix
          -> View ki (Const (Doc ann)) (Lkup ix codes)
          -> Doc ann

-- |Given a renderer instance, we can easily render
--  an element of the family
renderEl :: forall ki fam codes ix ann
          . (Family ki fam codes , Renderer ki fam codes , IsNat ix)
         => El fam ix -> Doc ann
renderEl = getConst . cata renderAlg . dfrom
  where
    renderAlg :: forall iy
               . (IsNat iy)
              => Rep ki (Const (Doc ann)) (Lkup iy codes)
              -> Const (Doc ann) iy
    renderAlg = Const . renderI (Proxy :: Proxy fam)
                                (getSNat (Proxy :: Proxy iy))
                      . sop
      
