{-# LANGUAGE TupleSections         #-}
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
import qualified Data.List as L
import Data.Functor.Const

import qualified Data.Text.Prettyprint.Doc as PP

import Generics.MRSOP.Util
import Generics.MRSOP.Base
import Generics.MRSOP.AG

-- * Domain Specific Pretty Printing
--

type Doc = PP.Doc ()

data Chunk = Chunk
  { unChunk :: [Doc]
  }

instance Semigroup Chunk where
  ds <> es = Chunk [compile ds <> compile es]

onChunk :: ([Doc] -> [Doc]) -> Chunk -> Chunk
onChunk f = Chunk . f . unChunk

emptyChunk :: Chunk
emptyChunk = Chunk []

singl :: Doc -> Chunk
singl d = Chunk [d]

pretty :: (PP.Pretty a) => a -> Chunk
pretty = singl . PP.pretty

semi :: Chunk
semi = pretty ";"

infixr 5 <+>
(<+>) :: Chunk -> Chunk -> Chunk
(Chunk ds) <+> (Chunk es) = Chunk (ds ++ es)

intercalate :: Doc -> Chunk -> Chunk
intercalate i = onChunk (L.intersperse i)

vcat :: Chunk -> Chunk
vcat (Chunk ds) = Chunk [PP.vcat ds]

hcat :: Chunk -> Chunk
hcat (Chunk ds) = Chunk [PP.hcat ds]

vsep :: Chunk -> Chunk
vsep (Chunk ds) = Chunk [PP.vsep ds]

vsep' :: [Chunk] -> Chunk
vsep' = Chunk . (:[]) . PP.vsep . map compile

hsep :: Chunk -> Chunk
hsep (Chunk ds) = Chunk [PP.hsep ds]

indent :: Int -> Chunk -> Chunk
indent i = onChunk (map (PP.indent i))

compile :: Chunk -> Doc
compile (Chunk [])  = PP.emptyDoc
compile (Chunk [p]) = p
compile (Chunk ps)  = PP.vcat ps

enclose :: Doc -> Doc -> Chunk -> Chunk
enclose l r (Chunk [])   = Chunk []
enclose l r (Chunk [ps]) = Chunk [PP.enclose l r ps]
enclose l r (Chunk ps)   = Chunk (l:ps ++ [r])

parens :: Chunk -> Chunk
parens = enclose PP.lparen PP.rparen

brackets :: Chunk -> Chunk
brackets = enclose PP.lbracket PP.rbracket

braces :: Chunk -> Chunk
braces = enclose PP.lbrace PP.rbrace

-- * The typeclass

type Rendered = Const (Int , Chunk)

renderDoc :: Rendered ix -> Doc
renderDoc = compile . snd . getConst

renderChunk :: Rendered ix -> Chunk
renderChunk = snd . getConst

-- |Returns the precedence of the topmost constructor in a
--  'rendered' instance.
precOf :: Rendered ix
       -> Int
precOf = fst . getConst

class (HasDatatypeInfo ki fam codes)
    => Renderer ki fam codes where
  -- |Renders opaque types
  renderK :: Proxy fam -> ki k -> Chunk

  -- |Renders a tree without precedence information
  render :: Proxy fam
         -> SNat ix
         -> View ki Rendered (Lkup ix codes)
         -> Chunk

  -- |Returns the precedence of the constructor
  precOfConstr :: Proxy fam
               -> SNat ix
               -> View ki (Const Int) (Lkup ix codes)
               -> Int
  precOfConstr _ _ _ = 0

-- |Applies a layout function iff the precedence @p@
--  is higher than the precedence of the underlying doc's
--  topmost operation.
layoutPrec :: (Renderer ki fam codes , IsNat ix)
           => Int
           -> (Chunk -> Chunk)
           -> Proxy fam
           -> Rendered ix
           -> Chunk 
layoutPrec p layout pf r
  = let f = if p > precOf r then layout else id
     in f (renderChunk r)

-- |Given a renderer instance, we can easily render
--  an element of the family
renderEl :: forall ki fam codes ix ann
          . (Family ki fam codes , Renderer ki fam codes , IsNat ix)
         => El fam ix -> Doc 
renderEl = renderDoc . cata renderAlg . dfrom 
  where
    renderAlg :: forall iy
               . (IsNat iy)
              => Rep ki Rendered (Lkup iy codes)
              -> Rendered iy
    renderAlg rep
      | s@(Tag c p) <- sop rep
      = let pf  = Proxy :: Proxy fam
            siy = getSNat (Proxy :: Proxy iy)
         in Const
          . (precOfConstr pf siy (Tag c (mapNP (mapNA id (Const . fst . getConst)) p)),)
          . render pf siy $ s 
