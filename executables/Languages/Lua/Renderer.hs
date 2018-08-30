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
module Languages.Lua.Renderer where

import Data.Text (Text)
import Data.Text.Encoding (encodeUtf8)
import Data.Type.Equality

import           Data.Proxy
import           Data.Functor.Const
import           Data.Functor.Sum
import qualified Data.Text.Prettyprint.Doc as PP
import           Data.Text.Prettyprint.Doc.Render.Text
import qualified Data.Text as T

import Generics.MRSOP.TH
import Generics.MRSOP.Base
import Generics.MRSOP.Util

import Generics.MRSOP.Digems.Renderer
import Generics.MRSOP.Digems.Digest

import Languages.Lua.Syntax

type TyExp = S (S (S (S (S (S (S (S Z)))))))

pattern MyNil :: View LuaSingl phi (Lkup TyExp CodesBlock)
pattern MyNil = Tag CZ NP0

pattern MyBool :: LuaSingl LuaBool -> View LuaSingl phi (Lkup TyExp CodesBlock)
pattern MyBool p_adQP = Tag (CS CZ) (NA_K p_adQP :* NP0)

instance Renderer W FamBlock CodesBlock where
  renderK _ (SLuaText text) = pretty $ T.unpack text
  renderK _ (SLuaBool b)    = pretty b

  render pf IdxExp Nil_              = pretty "nil"
  render pf IdxExp (Bool_ s)         = renderK pf s
  render pf IdxExp (Number_ _ n)     = renderK pf n
  render pf IdxExp (String_ s)       = renderK pf s
  render pf IdxExp Vararg_           = pretty "..."
  render pf IdxExp (EFunDef_ f)      = renderChunk f
  render pf IdxExp (PrefixExp_ pe)   = renderChunk pe
  render pf IdxExp (TableConst_ t)
    = braces (align (intercalate PP.comma (renderChunk t)))
  render pf IdxExp (Binop_ bop l r)  
    = let pbop = precOf bop
       in hsep' [layoutPrec pbop parens pf l
                ,renderChunk bop
                ,layoutPrec pbop parens pf r]
  render pf IdxExp (Unop_ uop e)
    = let puop = precOf uop
       in hsep' [renderChunk uop, layoutPrec puop parens pf e]

  render pf IdxVar (VarName_ n)   =  renderChunk n
  render pf IdxVar (Select_ pe e) =  renderChunk pe
                                  <> align (brackets (renderChunk e))
  render pf IdxVar (SelectName_ pe n)
    = renderChunk pe <> pretty "." <> renderChunk n 

  render pf IdxBinop Add_    = pretty "+"
  render pf IdxBinop Sub_    = pretty "-"
  render pf IdxBinop Mul_    = pretty "*"
  render pf IdxBinop Div_    = pretty "/"
  render pf IdxBinop IDiv_   = pretty "//"
  render pf IdxBinop Exp_    = pretty "^"
  render pf IdxBinop Mod_    = pretty "%"
  render pf IdxBinop Concat_ = pretty ".."
  render pf IdxBinop LT_     = pretty "<"
  render pf IdxBinop LTE_    = pretty "<="
  render pf IdxBinop GT_     = pretty ">"
  render pf IdxBinop GTE_    = pretty ">="
  render pf IdxBinop EQ_     = pretty "=="
  render pf IdxBinop NEQ_    = pretty "~="
  render pf IdxBinop And_    = pretty "and"
  render pf IdxBinop Or_     = pretty "or"
  render pf IdxBinop BAnd_   = pretty "&"
  render pf IdxBinop BOr_    = pretty "|"
  render pf IdxBinop BXor_   = pretty "~"
  render pf IdxBinop ShiftL_ = pretty "<<"
  render pf IdxBinop ShiftR_ = pretty ">>"

  render pf IdxUnop Neg_ = pretty "-"
  render pf IdxUnop Not_ = pretty "not "
  render pf IdxUnop Len_ = pretty "#"
  render pf IdxUnop Complement_ = pretty "~"

  render pf IdxPrefixExp (PEVar_ var)         = renderChunk var
  render pf IdxPrefixExp (PEFunCall_ funcall) = renderChunk funcall
  render pf IdxPrefixExp (Paren_ e)           = parens (renderChunk e)

  render pf IdxListTableField ListTableField_Ifx0
    = emptyChunk
  render pf IdxListTableField (ListTableField_Ifx1 f fs)
    = renderChunk f <+> renderChunk fs

  render pf IdxListVar (ListVar_Ifx0)
    = emptyChunk
  render pf IdxListVar (ListVar_Ifx1 f fs)
    = renderChunk f <+> renderChunk fs

  render pf IdxListStat (ListStat_Ifx0)
    = emptyChunk
  render pf IdxListStat (ListStat_Ifx1 f fs)
    = renderChunk f <+> renderChunk fs

  render pf IdxListTup1ExpBlock (ListTup1ExpBlock_Ifx0)
    = emptyChunk
  render pf IdxListTup1ExpBlock (ListTup1ExpBlock_Ifx1 f fs)
    = renderChunk f <+> renderChunk fs

  render pf IdxTup1ExpBlock (Tup1ExpBlock_Ifx0 x y)
    = renderChunk x <+> renderChunk y

  render pf IdxListName (ListName_Ifx0)
    = emptyChunk
  render pf IdxListName (ListName_Ifx1 f fs)
    = renderChunk f <+> renderChunk fs

  render pf IdxListExp (ListExp_Ifx0)
    = emptyChunk
  render pf IdxListExp (ListExp_Ifx1 f fs)
    = renderChunk f <+> renderChunk fs

  render pf IdxTableField (ExpField_ e1 e2)
    = brackets (renderChunk e1) <+> equals <+> renderChunk e2
  render pf IdxTableField (NamedField_ name e)
    = renderChunk name <+> equals <+> renderChunk e
  render pf IdxTableField (Field_ e)
    = renderChunk e

  render pf IdxBlock (Block_ stats ret)
    = vsep' [renderChunk stats , renderChunk ret]

  render pf IdxMaybeListExp MaybeListExpNothing_ = emptyChunk
  render pf IdxMaybeListExp (MaybeListExpJust_ ls)
    = hsep' [pretty "return", intercalate PP.comma (renderChunk ls)]

  render pf IdxFunName (FunName_ name s methods)
    = renderChunk name
      <> pretty "."
      <> intercalate PP.dot (renderChunk s)
      <> renderChunk methods

  render pf IdxMaybeName MaybeNameNothing_ = emptyChunk
  render pf IdxMaybeName (MaybeNameJust_ n)
    = pretty ":" <> renderChunk n

  render pf IdxFunBody (FunBody_ names vararg block)
    = group (vcat' [indent 2 $ vcat' [header , renderChunk block] , pretty "end"])
    where
      dv = case vararg of
              SLuaBool b -> if b then comma <+> pretty "..." else emptyChunk

      header = hsep' [pretty "function" ,parens (renderChunk names <> dv)]

  render pf IdxMaybeBlock (MaybeBlockJust_ x)
    = indent 2 $ hsep' [pretty "else" , renderChunk x]
  render pf IdxMaybeBlock MaybeBlockNothing_
    = emptyChunk

  render pf IdxFunCall (NormalFunCall_ pe arg)
    = renderChunk pe <> renderChunk arg
  render pf IdxFunCall (MethodCall_ pe method arg)
    = renderChunk pe <> colon <> renderChunk method <> renderChunk arg 

  render pf IdxFunArg (Args_ args)
    = parens (intercalate PP.comma (renderChunk args))
  render pf IdxFunArg (TableArg_ t)
    = braces (align (intercalate PP.comma (renderChunk t)))
  render pf IdxFunArg (StringArg_ s)
    = renderK pf s

  render pf IdxStat (Assign_ names vals)
    = hsep' [intercalate PP.comma (renderChunk names)
            , equals
            , intercalate PP.comma (renderChunk vals)]
  render pf IdxStat (FunCall_ f)
    = renderChunk f
  render pf IdxStat (Label_ name)
    = pretty "::" <> renderChunk name <> pretty "::"
  render pf IdxStat Break_ = pretty "break"
  render pf IdxStat (Goto_ name) = hsep' [pretty "goto", renderChunk name]
  render pf IdxStat (Do_ block)
    = group $ vcat' [indent 2 $ vcat' [pretty "do", renderChunk block] , pretty "end"]
  render pf IdxStat (While_ guard e)
    = vcat' [indent 2 $ vcat' [hsep' [pretty "while", renderChunk guard, pretty "do"]
                              , renderChunk e]
           , pretty "end"]
  render pf IdxStat (Repeat_ block guard)
    = vcat' [indent 2 $ vcat' [pretty "repeat" , renderChunk block]
           , indent 2 $ vcat' [pretty "until" , renderChunk guard]]
  render pf IdxStat (If_ cases elsePart)
    = case renderChunk cases of
        Chunk docs -> printIf docs elsePart
    where
      printIf [] e
        = error "If statement can't be empty"
      printIf (guard:block:rest) e
        = vcat' [indent 2 $ hsep' [pretty "if", singl guard, pretty "then", singl block]
                ,printIf' rest e]

      printIf' [] e = renderChunk e
      printIf' (guard:block:rest) e
        = vcat' [indent 2 $ hsep' [pretty "elseif", singl guard, pretty "then", singl block]
                ,printIf' rest e]
  render pf IdxStat (ForRange_ name e1 e2 e3 block)
    = vcat' [hsep' [ pretty "for"
                   , renderChunk name
                   , equals
                   , renderChunk e1
                   , comma
                   , renderChunk e2
                   , renderChunk e3
                   , pretty "do"
                   ]
            , indent 2 $ renderChunk block
            ]
  render pf IdxStat (ForIn_ name exps block)
    = vcat' [ hsep' [ pretty "for"
                    , intercalate PP.comma (renderChunk name)
                    , pretty "in"
                    , intercalate PP.comma (renderChunk exps)
                    , pretty "do"
                    ]
            , indent 2 $ renderChunk block
            ]
  render pf IdxStat (FunAssign_ name body)
    = hsep' [renderChunk name, renderChunk body]
  render pf IdxStat (LocalFunAssign_ name body)
    = hsep' [pretty "local" , renderChunk name , renderChunk body]
  render pf IdxStat (LocalAssign_ names exps)
    = hsep' [ pretty "local"
            , intercalate PP.comma (renderChunk names)
            , equals
            , intercalate PP.comma (renderChunk exps)
            ]
  render pf IdxStat EmptyStat_
    = semi

  render pf IdxMaybeExp (MaybeExpJust_ e)
    = comma <+> renderChunk e
  render pf IdxMaybeExp (MaybeExpNothing_)
    = emptyChunk

  render pf IdxName (Name_ n) = renderK pf n

  render pf idx _ = pretty "!!!!" <+> pretty (show $ go idx)
    where
      go :: SNat a -> Int
      go SZ = 0
      go (SS n) = 1 + go n
