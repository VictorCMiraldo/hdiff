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
import           Data.Text.Prettyprint.Doc hiding (braces,parens,semi)
import qualified Data.Text.Prettyprint.Doc as PP  (braces,parens,semi) 
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
  render pf IdxExp (EFunDef_ f)      = renderDoc f
  render pf IdxExp (PrefixExp_ pe)   = renderDoc pe
  render pf IdxExp (TableConst_ t)   = renderDoc t
  render pf IdxExp (Binop_ bop l r)  
    = let pbop = precOf bop
       in layoutPrec pbop PP.parens pf l
          <+> renderDoc bop
          <+> layoutPrec pbop PP.parens pf r
  render pf IdxExp (Unop_ uop e)
    = let puop = precOf uop
       in renderDoc uop <+> layoutPrec puop PP.parens pf e

  render pf IdxVar (VarName_ n)   =  renderDoc n
  render pf IdxVar (Select_ pe e) =  renderDoc pe
                                  <> align (brackets (renderDoc e))
  render pf IdxVar (SelectName_ pe n) = _

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

  render pf IdxPrefixExp (PEVar_ var)         = renderDoc var
  render pf IdxPrefixExp (PEFunCall_ funcall) = renderDoc funcall
  render pf IdxPrefixExp (Paren_ e)           = PP.parens (renderDoc e)

  render pf IdxListTableField ListTableField_Ifx0 = emptyDoc
  render pf IdxListTableField (ListTableField_Ifx1 f fs)
    -- TODO: hacky AF!! Maybe we could play with the precedence table?
    = let doComma = if length (show $ renderDoc fs) == 0
                    then id
                    else (<> comma)
       in doComma (renderDoc f) <+> renderDoc fs

  render pf IdxTableField (ExpField_ e1 e2)
    = brackets (renderDoc e1) <+> equals <+> renderDoc e2
  render pf IdxTableField (NamedField_ name e)
    = renderDoc name <+> equals <+> renderDoc e
  render pf IdxTableField (Field_ e)
    = renderDoc e

  render pf IdxBlock (Block_ stats ret)
    = vsep [renderDoc stats , renderDoc ret]

  render pf IdxMaybeListExp MaybeListExpNothing_ = emptyDoc
  render pf IdxMaybeListExp (MaybeListExpJust_ ls)
    = pretty "return" <+> renderDoc ls

  render pf IdxListExp (ListExp_Ifx0) = emptyDoc
  render pf IdxListExp (ListExp_Ifx1 f fs)
    -- TODO: hacky AF!! Maybe we could play with the precedence table?
    = let doComma = if length (show $ renderDoc fs) == 0
                    then id
                    else (<> comma)
       in doComma (renderDoc f) <+> renderDoc fs

  render pf IdxFunName (FunName_ name s methods)
    -- TODO: hacky AF^2
    = let doS = replace ',' '.' $ show s
       in renderDoc name <> dot <> pretty doS <> renderDoc methods
    where
      replace x y = map (\c -> if x == c then y else c)

  render pf IdxMaybeName MaybeNameNothing_ = emptyDoc
  render pf IdxMaybeName (MaybeNameJust_ n)
    = pretty ":" <> renderDoc n

  render pf IdxListName (ListName_Ifx0) = emptyDoc
  render pf IdxListName (ListName_Ifx1 f fs)
    -- TODO: hacky AF!! Maybe we could play with the precedence table?
    = let doComma = if length (show $ renderDoc fs) == 0
                    then id
                    else (<> comma)
       in doComma (renderDoc f) <+> renderDoc fs

  render pf IdxFunBody (FunBody_ names vararg block)
    = group (vcat [nest 2 $ vcat [header , renderDoc block] , pretty "end"])
    where
      dv = case vararg of
              SLuaBool b -> if b then comma <+> pretty "..." else emptyDoc

      header = pretty "function" <+> PP.parens (renderDoc names <> dv)

  render pf IdxFunCall (NormalFunCall_ pe arg)
    = renderDoc pe <> renderDoc arg
  render pf IdxFunCall (MethodCall_ pe method arg)
    = renderDoc pe <> colon <> renderDoc method <> renderDoc arg 

  render pf IdxFunArg (Args_ args)   = PP.parens (renderDoc args)
  render pf IdxFunArg (TableArg_ t)  = renderDoc t
  render pf IdxFunArg (StringArg_ s) = renderK pf s
  

  render pf IdxListVar (ListVar_Ifx0) = emptyDoc
  render pf IdxListVar (ListVar_Ifx1 f fs)
    -- TODO: hacky AF!! Maybe we could play with the precedence table?
    = let doComma = if length (show $ renderDoc fs) == 0
                    then id
                    else (<> comma)
       in doComma (renderDoc f) <+> renderDoc fs

  render pf IdxListStat (ListStat_Ifx0) = emptyDoc
  render pf IdxListStat (ListStat_Ifx1 f fs)
    -- TODO: hacky AF!! Maybe we could play with the precedence table?
    = vcat [renderDoc f , renderDoc fs]

  render pf IdxListTup1ExpBlock (ListTup1IdxBlock_Ifx0) = emptyDoc
  render pf IdxListTup1ExpBlock (ListTup1IdxBlock_Ifx1) = _

  render pf IdxStat (Assign_ names vals)
    = renderDoc names <+> pretty "=" <+> renderDoc vals
  render pf IdxStat (FunCall_ f)
    = renderDoc f
  render pf IdxStat (Label_ name)
    = pretty "::" <> renderDoc name <> pretty "::"
  render pf IdxStat Break_ = pretty "break"
  render pf IdxStat (Goto_ name) = pretty "goto" <+> renderDoc name
  render pf IdxStat (Do_ block)
    = group $ vcat [nest 2 $ vcat [pretty "do", renderDoc block] , pretty "end"]
  render pf IdxStat (While_ guard e)
    = vcat [nest 2 $ vcat [pretty "while" <+> renderDoc guard <+> pretty "do" , renderDoc e]
           ,pretty "end"]
  render pf IdxStat (Repeat_ block guard)
    = vcat [ nest 2 $ vcat [pretty "repeat" , renderDoc block]
           , nest 2 $ vcat [pretty "until" , renderDoc guard]]
  render pf IdxStat (If_ cases elsePart)
    = _
  


    
