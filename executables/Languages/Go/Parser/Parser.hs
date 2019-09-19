-- |
-- Module      : Language.Go.Parser.Parser
-- Copyright   : (c) 2011 Andrew Robbins
-- License     : GPLv3 (see COPYING)
--
-- y

{- LANGUAGE CPP -}
module Languages.Go.Parser.Parser where
import Languages.Go.Parser.Operators
import Languages.Go.Parser.Tokens
import Languages.Go.Parser.Tokens (GoTokenPos(..))
import Languages.Go.Parser.Lexer (alexScanTokens)
import Languages.Go.Syntax.AST

import Control.Monad
import Data.Maybe (isJust)
import Text.Parsec.Prim hiding (token)
import Text.Parsec.Error (ParseError)
import Text.Parsec.Combinator
import Data.Function


-- | Tokenize Go language source code
--
-- This is where semicolons are inserted into the token stream.
-- We also filter out comments here, so any comment processing
-- must occur before this stage.
--
-- TODO: Unicode identifiers
--
-- See also: 4.3. Semicolons
goTokenize :: String -> [GoTokenPos]
goTokenize = insertSemi . stripComments . alexScanTokens

-- | Parse Go Language source code into AST
goParse :: String -> String -> Either ParseError GoSource
goParse filename s = goParseTokens filename $ goTokenize s

-- | Parse Go Language token list into AST
goParseTokens :: String -> [GoTokenPos] -> Either ParseError GoSource
goParseTokens filename toks = parse goSource filename toks

goParseFileWith :: GoParser a -> String -> String -> Either ParseError a
goParseFileWith start filename s = parse start filename (goTokenize s)

goParseTestWith :: GoParser a -> String -> Either ParseError a
goParseTestWith start s = parse start "" (goTokenize s)

--
--  Begin specification grammar
--

-- | Standard @Type@
--
-- See also: SS. 6. Types
goType :: GoParser GoType
goType =  goTypeName
      <|> goTypeLit
      <|> goParen goType

-- | Standard @TypeName@
--
-- See also: SS. 6. Types
goTypeName :: GoParser GoType
goTypeName = do
  (GoQual q n) <- goQualifiedIdent
  return $ GoTypeName q n

-- | Standard @TypeLit@
--
-- See also: SS. 6. Types
goTypeLit :: GoParser GoType
goTypeLit =  (try goSliceType)
         <|> goArrayType
         <|> goStructType
         <|> goPointerType
         <|> goFunctionType
         <|> goInterfaceType
         <|> goMapType
         <|> goChannelType

-- See also: SS. 6.1. Boolean types
-- See also: SS. 6.2. Numeric types
-- See also: SS. 6.3. String types

-- | Standard @ArrayType@
--
-- See also: SS. 6.4. Array types
goArrayType :: GoParser GoType
goArrayType = do
  l <- goBracket goExpression -- Go @ArrayLength@
  t <- goType                 -- Go @ElementType@
  return $ GoArrayType l t

-- | Standard @SliceType@
--
-- See also: SS. 6.5. Slice types
goSliceType :: GoParser GoType
goSliceType = do
  goTokLBracket
  goTokRBracket
  liftM GoSliceType goType

-- | Standard @StructType@
--
-- See also: SS. 6.6. Struct types
goStructType :: GoParser GoType
goStructType = do
  goTokStruct
  liftM GoStructType $ goBlockish goFieldDecl

-- | Standard @FieldDecl@
--
-- See also: SS. 6.6. Struct types
goFieldDecl :: GoParser GoFieldType
goFieldDecl = field <|> anonymous where

    field = do -- Go @FieldDecl@
      ids <- goIdentifierList
      t <- goType
      tag <- option "" (try goString) -- Go @Tag@
      return $ GoFieldType tag ids t

    anonymous = do -- Go @AnonymousField@
      a <- optionMaybe goTokAsterisk -- "*"
      t <- goTypeName -- TypeName
      tag <- option "" (try goString) -- Go @Tag@
      return $ GoFieldAnon tag (isJust a) t

-- | Standard @PointerType@
--
-- See also: SS. 6.7. Pointer types
goPointerType :: GoParser GoType
goPointerType = do
  goTokAsterisk
  liftM GoPointerType goType -- Go @BaseType@

-- | Standard @FunctionType@
--
-- See also: SS. 6.8. Function types
goFunctionType :: GoParser GoType
goFunctionType = do
  goTokFunc
  liftM GoFunctionType goSignature

-- | Standard @Signature@
--
-- See also: SS. 6.8. Function types
goSignature :: GoParser GoSig
goSignature = do
  par <- goParameters
  res <- option [] goResult
  return $ GoSig par res

-- | Standard @Result@
--
-- See also: SS. 6.8. Function types
goResult :: GoParser [GoParam]
goResult =  goParameters 
        <|> do ty <- goType ; return [GoParam [] ty]

-- | Standard @Parameters@
--
-- See also: SS. 6.8. Function types
goParameters :: GoParser [GoParam]
goParameters = do
  goTokLParen
  params <- option [] $ do
    ps <- goParameterList
    optional goTokComma
    return ps
  goTokRParen
  return params

-- | Standard @ParameterList@
--
-- See also: SS. 6.8. Function types
goParameterList :: GoParser [GoParam]
goParameterList = sepBy goParameterDecl goTokComma

-- | Standard @ParameterDecl@
--
-- See also: SS. 6.8. Function types
goParameterDecl :: GoParser GoParam
goParameterDecl = (try goParameterDecl') <|> goParameterDecl'' where

    goParameterDecl' :: GoParser GoParam
    goParameterDecl' = do
      is <- option [] goIdentifierList
      optional goTokElipsis
      t <- goType
      return $ GoParam is t
    --  return $ flip map is (\i -> GoParam (Just i) t)
    
    goParameterDecl'' :: GoParser GoParam
    goParameterDecl'' = do
      t <- goType
      return $ GoParam [] t

-- | Standard @InterfaceType@
--
-- See also: SS. 6.9. Interface types
goInterfaceType :: GoParser GoType
goInterfaceType = do
  goTokInterface
  xs <- goBlockish goMethodSpec
  return $ GoInterfaceType xs

-- | Standard @MethodSpec@
--
-- See also: SS. 6.9. Interface types
goMethodSpec = goMethodSpec' <|> goMethodSpec'' where

    goMethodSpec'' = liftM GoInterface goIdentifier -- Go @InterfaceTypeName@

    goMethodSpec' = do
      n <- goIdentifier -- Go @MethodName@
      s <- goSignature
      return $ GoMethSpec n s

-- | Standard @MapType@
--
-- See also: SS. 6.10. Map types
goMapType :: GoParser GoType
goMapType = do
  goTokMap
  kt <- goBracket goType -- Go @KeyType@
  et <- goType -- Go @ElementType@
  return $ GoMapType kt et

-- | Standard @ChannelType@
--
-- See also: SS. 6.11. Channel types
goChannelType :: GoParser GoType
goChannelType = do
  qi <- goChannelQuip
  ty <- goType
  return $ GoChannelType qi ty

-- | Nonstandard
goChannelQuip :: GoParser GoChanKind
goChannelQuip =  do goTokArrow1 ; goTokChan ; return GoIChan         -- 1=RecvDir
             <|> (try $ do goTokChan ; goTokArrow1 ; return GoOChan) -- 2=SendDir
             <|> (try $ do goTokChan ; return GoIOChan)              -- 3=BothDir

-- See also: SS. 7.1. Type identity
-- See also: SS. 7.2. Assignability

-- | Standard @Block@
--
-- See also: SS. 8. Blocks
goBlock :: GoParser GoBlock
goBlock =  liftM GoBlock $ goBlockish goAnyStatement

-- | Nonstandard
goBlockish :: GoParser a -> GoParser [a]
goBlockish =  goBrace . many . goSemi

-- | Standard @Declaration@
--
-- See also: SS. 9. Declarations and scope
goDeclaration :: GoParser GoDecl
goDeclaration =  goConstDecl
             <|> goTypeDecl
             <|> goVarDecl
--             <?> "declaration"

-- | Standard @TopLevelDecl@
--
-- See also: SS. 9. Declarations and scope
goTopLevelDecl :: GoParser GoDecl
goTopLevelDecl =  goDeclaration
              <|> try goFunctionDecl
              <|> try goMethodDecl
--              <?> "top-level declaration"

-- | Nonstandard
--
-- This is not part of the standard, but is here to abstract away
-- some of the details of possible extensions to the language.
--
goTopLevelPrel :: GoParser GoPrel
goTopLevelPrel = goImportDecl

-- | Standard @ConstDecl@
--
-- See also: SS. 9.5. Constant declarations
goConstDecl :: GoParser GoDecl
goConstDecl = goTokConst >> liftM GoConst (goParenish goConstSpec)

-- | Standard @ConstSpec@
goConstSpec :: GoParser GoCVSpec
goConstSpec = do
  id <- goIdentifierList
  option (GoCVSpec id Nothing []) (try (goConstSpec' id) <|> goConstSpec'' id) where         

    goConstSpec' :: [GoId] -> GoParser GoCVSpec
    goConstSpec' ids = do
      goTokEqual
      exs <- goExpressionList
      return $ GoCVSpec ids Nothing exs

    goConstSpec'' :: [GoId] -> GoParser GoCVSpec
    goConstSpec'' ids = do
      typ <- goType
      goTokEqual
      exs <- goExpressionList
      return $ GoCVSpec ids (Just typ) exs

-- | Standard @IdentifierList@
--
-- See also: SS. 9.5. Constant declarations
goIdentifierList :: GoParser [GoId]
goIdentifierList = sepBy goIdentifier goTokComma

-- | Standard @ExpressionList@
--
-- See also: SS. 9.5. Constant declarations
goExpressionList :: GoParser [GoExpr]
goExpressionList = sepBy goExpression goTokComma

-- | Nonstandard, includes @ConstSpec@, @VarSpec@
--
-- See also: SS. 9.5. Constant declarations
--goCVSpecs :: GoParser [GoCVSpec]
--goCVSpecs = try goCVSpecs' <|> goCVSpecs'' where
--
--    goCVSpecs' = liftM (replicate 1) goCVSpec
--    goCVSpecs'' = goParen $ many $ goSemi goCVSpec
--
--    goCVSpec :: GoParser GoCVSpec
--    goCVSpec = do
--      ids <- goIdentifierList
--      try (goCVSpec' ids) <|> goCVSpec'' ids where

-- See also: SS. 9.6. Iota

-- | Standard @TypeDecl@
--
-- See also: SS. 9.7. Type declarations
goTypeDecl :: GoParser GoDecl
goTypeDecl = goTokType >> liftM GoType (goParenish goTypeSpec)

-- | Standard @TypeSpec@
--
-- See also: SS. 9.7. Type declarations
goTypeSpec :: GoParser GoTypeSpec
goTypeSpec = do
  id <- goIdentifier
  ty <- goType
  return $ GoTypeSpec id ty

-- | Standard @VarDecl@
--
-- See also: SS. 9.8. Variable declarations
goVarDecl :: GoParser GoDecl
goVarDecl = goTokVar >> liftM GoVar (goParenish goVarSpec)

goVarSpec :: GoParser GoCVSpec
goVarSpec = do
  id <- goIdentifierList
  (try (goVarSpec' id) <|> try (goVarSpec'' id) <|> goVarSpec''' id) where

    goVarSpec' :: [GoId] -> GoParser GoCVSpec
    goVarSpec' ids = do
      goTokEqual
      exs <- goExpressionList
      return $ GoCVSpec ids Nothing exs

    goVarSpec'' :: [GoId] -> GoParser GoCVSpec
    goVarSpec'' ids = do
      typ <- goType
      goTokEqual
      exs <- goExpressionList
      return $ GoCVSpec ids (Just typ) exs

    goVarSpec''' :: [GoId] -> GoParser GoCVSpec
    goVarSpec''' ids = do
      typ <- goType
      return $ GoCVSpec ids (Just typ) []

-- | Standard @ShortVarDecl@
--
-- See also: SS. 9.9. Short variable declarations
goShortVarDecl :: GoParser GoSimp
goShortVarDecl = do
  ids <- goIdentifierList
  goTokColonEq
  exs <- optionMaybe goExpressionList
  case exs of
    Just ex -> return (GoSimpVar ids ex)
    Nothing -> fail "short var"
--  return (GoSimpVar ids exs)
--             <?> "short variable declaration"

-- | Standard @FunctionDecl@
--
-- See also: SS. 9.10. Function declarations
goFunctionDecl :: GoParser GoDecl
goFunctionDecl = do
  goTokFunc
  id <- goIdentifier
  sg <- goSignature
  bk <- option GoNoBlock goBlock -- Go @Body@
  return $ GoFunc $ GoFuncDecl id sg bk

-- | Standard @MethodDecl@
--
-- See also: SS. 9.11. Method declarations
goMethodDecl :: GoParser GoDecl
goMethodDecl = do
  goTokFunc
  rc <- goReceiver
  id <- goIdentifier
  sg <- goSignature
  bk <- option GoNoBlock goBlock
  return $ GoMeth $ GoMethDecl rc id sg bk

-- | Standard @Receiver@
--
-- See also: SS. 9.11. Method declarations
goReceiver :: GoParser GoRec
goReceiver = between goTokLParen goTokRParen recspec
    where recspec = do
            id <- optionMaybe goIdentifier
            pt <- optionMaybe goTokAsterisk
            ty <- goTypeName -- Go @BaseTypeName@
            return $ GoRec (isJust pt) id ty

-- | Standard @Operand@
--
-- See also: SS. 10.1. Operands
goOperand :: GoParser GoPrim
goOperand =  (try $ liftM GoLiteral goLiteral)
         <|> try goQualifiedIdent
         <|> try goMethodExpr
         <|> liftM GoParen (goParen goExpression)

-- | Standard @Literal@
--
-- See also: SS. 10.1. Operands
goLiteral :: GoParser GoLit
goLiteral =  goBasicLit
         <|> goCompositeLit
         <|> goFunctionLit
         <?> "literal"

-- | Standard @BasicLit@
--
-- See also: SS. 10.1. Operands
goBasicLit :: GoParser GoLit
goBasicLit = try $ do
  (GoTokenPos _ tok) <- lookAhead anyToken
  case tok of
        (GoTokInt  (Just s) t) -> do anyToken; return $ GoLitInt  s t
        (GoTokReal (Just s) t) -> do anyToken; return $ GoLitReal s t
        (GoTokImag (Just s) t) -> do anyToken; return $ GoLitImag s t
        (GoTokChar (Just s) t) -> do anyToken; return $ GoLitChar s t
        (GoTokStr  (Just s) t) -> do anyToken; return $ GoLitStr  s t
        x -> fail (show x)

-- | Standard @QualifiedIdent@
--
-- See also: SS. 10.2. Qualified identifiers
goQualifiedIdent :: GoParser GoPrim
goQualifiedIdent = do
  ns <- sepBy1 goIdentifier goTokFullStop
  let qual = init ns
      name = last ns
  return $ GoQual qual name

-- | Standard @CompositeLit@
--
-- See also: SS. 10.3. Composite literals
goCompositeLit :: GoParser GoLit
goCompositeLit = do
  ty <- goLiteralType
  va <- goLiteralValue
  return $ GoLitComp ty va

-- | Nonstandard
--
-- This production represents the third part of the @LiteralType@ production.
--
-- See also: SS. 10.3. Composite literals
goArrayElipsisType :: GoParser GoType
goArrayElipsisType = do
  goBracket goTokElipsis
  goType

-- | Standard @LiteralType@
--
-- See also: SS. 10.3. Composite literals
goLiteralType :: GoParser GoType
goLiteralType =  (try goArrayType)
             <|> (try goArrayElipsisType)
             <|> goSliceType
             <|> goStructType
             <|> goMapType
             <|> goTypeName

-- | Standard @LiteralValue@
--
-- See also: SS. 10.3. Composite literals
goLiteralValue :: GoParser GoComp
goLiteralValue = liftM GoComp $ goBrace goElementList

-- | Standard @ElementList@
--
-- See also: SS. 10.3. Composite literals
goElementList :: GoParser [GoElement]
goElementList = try goElementList' <|> goElementList''
goElementList' = endBy1 goElement goTokComma
goElementList'' = sepBy1 goElement goTokComma

-- | Standard @Element@
--
-- See also: SS. 10.3. Composite literals
goElement :: GoParser GoElement
goElement = do
  key <- option GoKeyNone (try $ goAfter goTokColon goKey)
  val <- goValue
  return $ GoElement key val

-- | Standard @Key@
--
-- See also: SS. 10.3. Composite literals
goKey :: GoParser GoKey
goKey =  liftM GoKeyField goIdentifier -- Go @FieldName@
     <|> liftM GoKeyIndex goExpression -- Go @ElementIndex@
     <?> "literal key"

-- | Standard @Value@
--
-- See also: SS. 10.3. Composite literals
goValue :: GoParser GoValue
goValue =  liftM GoValueExpr goExpression
       <|> liftM GoValueComp goLiteralValue
       <?> "literal value"

-- | Standard @FunctionLit@
--
-- See also: SS. 10.4. Function literals
goFunctionLit :: GoParser GoLit
goFunctionLit = liftM GoLitFunc goFuncLambda

-- | Nonstandard function literals (self-contained)
goFuncLambda :: GoParser GoFuncExpr
goFuncLambda = do
  goTokFunc
  sg <- goSignature
  bk <- goBlock
  return $ GoFuncExpr sg bk

-- | Standard @PrimaryExpr@
--
-- @PrimaryExpr@ is occurs in many places:
--
-- * @Expression@,
--
-- * @TypeSwitchGuard@,
--
-- * and in its own definition.
--
-- Therefore, it is useful to have a separate datatype for it,
-- since otherwise we would have to repeat ourselves. This is
-- the responsibility @goPrimary@ below. The only thing we do
-- here is convert the AST one level, so it's an expression.
--
-- See also: SS. 10.5. Primary expressions
goPrimaryExpr :: GoParser GoExpr
goPrimaryExpr = liftM GoPrim goPrimary

-- | Nonstandard primary expressions (self-contained)
goPrimary :: GoParser GoPrim
goPrimary = goPrimary' >>= goPrimary''' where

    -- THANK YOU ski ...
    goPrimary''' :: GoPrim -> GoParser GoPrim
    goPrimary''' ex = (goPrimary'' ex >>= goPrimary''') <|> return ex
    
    -- this is the right-associative parts of 'PrimaryExpr'
    goPrimary'' :: GoPrim -> GoParser GoPrim
    goPrimary'' ex =  (try $ goIndex ex)
                  <|> (try $ goSlice ex)
                  <|> goTypeAssertion ex
                  <|> goCall ex
    --            <|> goSelector ex -- how to distinguish from qualified identifiers?
    --            <?> "primary expression component"
    
    -- this is the beginning parts of 'PrimaryExpr'
    goPrimary' :: GoParser GoPrim
    goPrimary' =  (try goOperand)
              <|> (try goBuiltinCall)
--              <|> (try goConversion)
    --        <?> "primary expression start"

-- | Standard @Selector@
--
-- See also: SS. 10.5. Primary expressions, 10.6. Selectors
goSelector :: GoPrim -> GoParser GoPrim
goSelector ex = do
  goTokFullStop
  id <- goIdentifier
  return $ GoSelect ex id

-- | Standard @Index@
--
-- See also: SS. 10.5. Primary expressions, 10.7. Indexes
goIndex :: GoPrim -> GoParser GoPrim
goIndex ex = do
  goTokLBracket
  ix <- goExpression
  goTokRBracket
  return $ GoIndex ex ix

-- | Standard @Slice@
--
-- See also: SS. 10.5. Primary expressions, 10.8. Slices
goSlice :: GoPrim -> GoParser GoPrim
goSlice ex = do
  goTokLBracket
  ix <- optionMaybe goExpression
  goTokColon
  iy <- optionMaybe goExpression
  goTokRBracket
  let zero = GoPrim (GoLiteral (GoLitInt "0" 0))
  return $ case (ix, iy) of
             (Just x, Just y)   -> GoSlice ex [x, y]
             (Just x, Nothing)  -> GoSlice ex [x]
             (Nothing, Just y)  -> GoSlice ex [zero, y]
             (Nothing, Nothing) -> GoSlice ex [zero]

-- | Standard @TypeAssertion@
--
-- See also: SS. 10.5. Primary expressions, 10.9. Type assertions
goTypeAssertion :: GoPrim -> GoParser GoPrim
goTypeAssertion ex = do
  goTokFullStop
  goTokLParen
  ty <- goType
  goTokRParen
  return $ GoTA ex ty

-- | Standard @Call@
--
-- See also: SS. 10.5. Primary expressions, 10.10. Calls
goCall :: GoPrim -> GoParser GoPrim
goCall ex = do
  goTokLParen
  ar <- goExpressionList
  rs <- optionMaybe goTokElipsis
  goTokRParen
  return $ GoCall ex ar (isJust rs)

-- | Standard @Expression@
--
-- Technically, the Go spec says
--
-- * @Expression@ = @UnaryExpr@ | @Expression@ @binary_op@ @UnaryExpr@ .
--
-- * @UnaryExpr@ = @PrimaryExpr@ | @unary_op@ @UnaryExpr@ .
--
-- but we combine these into one production here.
--
-- See also: SS. 10.12. Operators
goExpression :: GoParser GoExpr
goExpression = goOpExpr goPrimaryExpr
            <?> "expression"

--    goUnaryExpr
--    <|> goBinaryExpr

-- | Standard @UnaryExpr@
--
-- See also: SS. 10.12. Operators
--goUnaryExpr :: GoParser GoExpr
--goUnaryExpr =  goPrimaryExpr
--           <|> do f <- goTokPlus(Go1Op); x <- goPrimaryExpr; return f x
--           <|> do f <- goTokMinus(Go1Op); x <- goPrimaryExpr; return f x
--           <|> do f <- goTokAND(Go1Op); x <- goPrimaryExpr; return f x
--           <|> do f <- goTokAND(Go1Op); x <- goPrimaryExpr; return f x
--           <|> do f <- goTokAND(Go1Op); x <- goPrimaryExpr; return f x
--
---- | Nonstandard
----
---- We cheat here and make them right-associative
---- even though the standard indicates left-associative
---- this could be reversed later during processing
--goBinaryExpr :: GoParser GoExpr
--goBinaryExpr = goBinary goUnaryExpr

-- | Standard @MethodExpr@
--
-- See also: SS. 10.13. Method expressions
goMethodExpr :: GoParser GoPrim
goMethodExpr = do
  rc <- goReceiverType
  goTokFullStop
  id <- goMethodName
  return $ GoMethod rc id

-- | Nonstandard
goMethodName = goIdentifier

-- | Standard @ReceiverType@
--
-- See also: SS. 10.13. Method expressions
goReceiverType :: GoParser GoRec
goReceiverType =  try goReceiverType' <|> goReceiverType'' where

    goReceiverType'' = do
      ty <- goParen goPointerType
      return $ GoRec True Nothing ty

    goReceiverType' = do
      ty <- goTypeName
      return $ GoRec False Nothing ty

-- | Standard @Conversion@
--
-- See also: SS. 10.14. Conversions
goConversion :: GoParser GoPrim
goConversion = do
  ty <- goType
  ex <- goParen goExpression
  return $ GoCast ty ex

-- | Standard @Statement@
--
-- See also: SS. 11. Statements
goStatement :: GoParser GoStmt
goStatement =  (liftM GoStmtDecl goDeclaration)   -- 'Statement/Declaration'
           <|> (liftM GoStmtSimple goSimple)      -- 'Statement/SimpleStmt'
           <|> goLabeledStmt
           <|> goGoStmt
           <|> goReturnStmt
           <|> goBreakStmt
           <|> goContinueStmt
           <|> goGotoStmt
           <|> goFallthroughStmt
           <|> liftM GoStmtBlock goBlock
           <|> goIfStmt
           <|> goSwitchStmt
           <|> goSelectStmt
           <|> goForStmt
           <|> goDeferStmt
           <?> "statement"

-- | Nonstandard, TODO: remove this
goAnyStatement :: GoParser GoStmt
goAnyStatement =  goStatement
--            <|> goAnyStmt
              <?> "statement within a block"

-- | Nonstandard
--goAnyStmt :: GoParser GoStmt
--goAnyStmt = do
--  manyTill anyToken goTokSemicolon
----  fail "could not recognize statement"
--  goEmptyStmt

-- | Nonstandard simple statements (self-contained)
--
-- This is to wrap simple statements in a self-contained datatype.
goSimple :: GoParser GoSimp
goSimple =  (try goSendStmt)       -- 'SimpleStmt/SendStmt'
        <|> (try goIncDecStmt)     -- 'SimpleStmt/IncDecStmt'
        <|> (try goShortVarDecl)   -- 'SimpleStmt/ShortVarDecl'
        <|> (try goAssignment)     -- 'SimpleStmt/Assignment'
        <|> (liftM GoSimpExpr goExpression) -- 'SimpleStmt/ExpressionStmt'

-- | Standard @EmptyStmt@
--
-- See also: SS. 11.1. Empty statements
goEmptyStmt :: GoParser GoStmt
goEmptyStmt = return $ GoStmtSimple GoSimpEmpty

-- | Standard @LabeledStmt@
--
-- See also: SS. 11.2. Labeled statements
goLabeledStmt :: GoParser GoStmt
goLabeledStmt = do
  id <- goIdentifier -- Go @Label@
  goTokColon
  st <- goStatement
  return $ GoStmtLabeled id st

-- | Standard @SendStmt@
--
-- See also: SS. 11.4. Send statements
goSendStmt :: GoParser GoSimp
goSendStmt = do
  ch <- goExpression -- Go @Channel@
  goTokArrow2
  ex <- goExpression
  return $ GoSimpSend ch ex

-- | Standard @IncDecStmt@
--
-- See also: SS. 11.5. IncDec statements
goIncDecStmt :: GoParser GoSimp
goIncDecStmt = try $ do
  ex <- goPrimaryExpr -- goExpression
  (GoTokenPos _ op) <- anyToken
  case op of
    GoTokInc -> return $ GoSimpInc ex
    GoTokDec -> return $ GoSimpDec ex
--    GoOp"++" -> return $ GoSimpInc ex
--    GoOp"--" -> return $ GoSimpDec ex
    _ -> fail "IncDecStmt What?"

-- | Standard @Assignment@
--
-- See also: SS. 11.6. Assignments
goAssignment :: GoParser GoSimp
goAssignment = do
  lv <- goExpressionList
  op <- goAssignOp
  rv <- goExpressionList
  return $ GoSimpAsn lv op rv

-- | Standard @IfStmt@
--
-- See also: SS. 11.7. If statements
goIfStmt :: GoParser GoStmt
goIfStmt = do
  goTokIf
  s <- optionMaybe (goSemi goSimple)
  c <- optionMaybe goExpression
  b <- goBlock
  e <- optionMaybe (goTokElse >> goStatement)
  return $ GoStmtIf (GoCond s c) b e

-- | Standard @IfStmt@
--
-- See also: SS. 11.8. Switch statements
goSwitchStmt =  goExprSwitchStmt
            <|> goTypeSwitchStmt

-- | Standard @ExprSwitchStmt@
--
-- See also: SS. 11.8. Switch statements
goExprSwitchStmt :: GoParser GoStmt
goExprSwitchStmt = do
  goTokSwitch
  st <- optionMaybe (goSemi goSimple)
  ex <- optionMaybe goExpression
  cl <- goBrace $ many1 goExprCaseClause
  return $ GoStmtSwitch (GoCond st ex) cl

-- | Standard @ExprCaseClause@
--
-- See also: SS. 11.8. Switch statements
goExprCaseClause :: GoParser (GoCase GoExpr)
goExprCaseClause = do
  fn <- goAfter goTokColon goExprSwitchCase
  st <- many1 $ goSemi goStatement
  return $ fn st

-- | Standard @ExprSwitchCase@
--
-- See also: SS. 11.8. Switch statements
goExprSwitchCase :: GoParser ([GoStmt] -> GoCase GoExpr)
goExprSwitchCase = goExprSwitchCase' <|> goExprSwitchCase''
goExprSwitchCase' = do goTokCase; el <- goExpressionList; return $ GoCase el
goExprSwitchCase'' = do goTokDefault; return GoDefault

-- | Standard @TypeSwitchStmt@
goTypeSwitchStmt :: GoParser GoStmt
goTypeSwitchStmt = do
  goTokSwitch
  st <- optionMaybe $ goSemi goSimple
  id <- optionMaybe $ goAfter goTokColonEq goIdentifier
  ga <- goTypeSwitchGuard st
  cl <- goBrace $ many1 goTypeCaseClause
  return $ GoStmtTypeSwitch ga cl id

-- | Standard @TypeSwitchGuard@
goTypeSwitchGuard :: (Maybe GoSimp) -> GoParser GoCond
goTypeSwitchGuard st = do
  ex <- goExpression
  goTokFullStop
  goParen goTokType
  return $ GoCond st (Just ex)

-- | Standard @TypeSwitchCase@
goTypeCaseClause :: GoParser (GoCase GoType)
goTypeCaseClause = do
  fn <- goAfter goTokColon goTypeSwitchCase
  st <- many $ goSemi goStatement
  return $ fn st

-- | Standard @TypeSwitchCase@
goTypeSwitchCase :: GoParser ([GoStmt] -> GoCase GoType)
goTypeSwitchCase = goTypeSwitchCase' <|> goTypeSwitchCase''
goTypeSwitchCase' = do goTokCase; tl <- goTypeList; return $ GoCase tl
goTypeSwitchCase'' = do goTokDefault; return GoDefault

-- | Standard @TypeList@
goTypeList :: GoParser [GoType]
goTypeList = sepBy1 goType goTokComma

-- | Standard @ForStmt@
--
-- See also: SS. 11.9. For statements
goForStmt = do
  goTokFor
  h <- (try goForClause <|> try goRangeClause <|> goCondition)
  b <- goBlock
  return $ GoStmtFor h b

-- | Standard @Condition@
goCondition :: GoParser GoForClause
goCondition = liftM GoForWhile goExpression

-- | Standard @ForClause@
goForClause :: GoParser GoForClause
goForClause = do
  i <- option GoSimpEmpty goSimple -- Go @InitStmt@
  goTokSemicolon
  c <- optionMaybe goExpression
  goTokSemicolon
  p <- option GoSimpEmpty goSimple -- Go @PostStmt@
  return $ GoForThree i c p

-- | Standard @RangeClause@
goRangeClause :: GoParser GoForClause
goRangeClause = do
  k <- goExpression
  v <- option [] (goTokComma >> liftM (replicate 1) goPrimaryExpr)
  p <- goAnyEqual
  goTokRange
  e <- goExpression
  return $ GoForRange (k:v) e

-- Nonstandard
goAnyEqual :: GoParser GoOp
goAnyEqual =  do goTokEqual;   return $ GoOp "="
          <|> do goTokColonEq; return $ GoOp ":="
-- goEmpty = (GoStmtSimple GoSimpEmpty)

-- | Standard @GoStmt@
--
-- See also: SS. 11.10. Go statements
goGoStmt :: GoParser GoStmt
goGoStmt = do goTokGo; liftM GoStmtGo goExpression

-- | Standard @SelectStmt@
--
-- See also: SS. 11.11. Select statements
goSelectStmt :: GoParser GoStmt
goSelectStmt = do
  goTokSelect
  cl <- goBrace $ many1 goCommClause
  return $ GoStmtSelect cl

-- | Standard @CommClause@
--
-- See also: SS. 11.11. Select statements
goCommClause :: GoParser (GoCase GoChan)
goCommClause = do
  fn <- goAfter goTokColon goCommCase
  st <- many1 $ goSemi goStatement
  return $ fn st

-- | Standard @CommCase@
--
-- See also: SS. 11.11. Select statements
goCommCase :: GoParser ([GoStmt] -> GoCase GoChan)
goCommCase = goCommCase' <|> goCommCase''
goCommCase' = do goTokCase; ch <- goChanStmt; return $ GoCase [ch]
goCommCase'' = do goTokDefault; return GoDefault

-- | Nonstandard
goChanStmt :: GoParser GoChan
goChanStmt = try (goSendStmt >>= convert) <|> goRecvStmt
    where convert (GoSimpSend x y) = return (GoChanSend x y)

-- | Standard @RecvStmt@
--
-- See also: SS. 11.11. Select statements
goRecvStmt :: GoParser GoChan
goRecvStmt = do
  as <- optionMaybe $ do
               ex <- goExpression
               op <- goAnyEqual
               return (ex, op)
  re <- goRecvExpr
  return $ GoChanRecv as re

-- | Standard @RecvExpr@
--
-- See also: SS. 11.11. Select statements
goRecvExpr :: GoParser GoExpr
goRecvExpr =  goRecvExpr'
          <|> goParen goRecvExpr where

    goRecvExpr' = do
      goTokArrow1
      ex <- goExpression
      return $ Go1Op (GoOp "<-") ex

-- | Standard @ReturnStmt@
--
-- See also: SS. 11.12. Return statements
goReturnStmt = do goTokReturn; liftM GoStmtReturn $ option [] goExpressionList

-- | Standard @BreakStmt@
--
-- See also: SS. 11.13. Break statements
goBreakStmt = do goTokBreak; liftM GoStmtBreak $ optionMaybe goIdentifier

-- | Standard @ContinueStmt@
--
-- See also: SS. 11.14. Continue statementss
goContinueStmt = do goTokContinue; liftM GoStmtContinue $ optionMaybe goIdentifier

-- | Standard @GotoStmt@
--
-- See also: SS. 11.15. Goto statements
goGotoStmt = do goTokGoto; liftM GoStmtGoto $ goIdentifier

-- | Standard @FallthroughStmt@
--
-- See also: SS. 11.16. Fallthrough statements
goFallthroughStmt = goTokFallthrough >> return GoStmtFallthrough

-- | Standard @DeferStmt@
--
-- See also: SS. 11.17. Defer statements
goDeferStmt = goTokDefer >> liftM GoStmtDefer goExpression

-- | Standard @BuiltinCall@
--
-- See also: SS. 12. Built-in functions, 12.3. Allocation
goBuiltinCall :: GoParser GoPrim
goBuiltinCall = do
  id <- goIdentifier
  goTokLParen
  tj <- optionMaybe goType
  ar <- option [] goBuiltinArgs
  goTokRParen
  case (id, tj) of
    (GoId "new",  Just ty) -> return $ GoNew  ty
    (GoId "make", Just ty) -> return $ GoMake ty ar
    _ -> fail "BuiltinCall what?"

-- | Standard @BuiltinArgs@
--
-- See also: SS. 12. Built-in functions
goBuiltinArgs :: GoParser [GoExpr]
goBuiltinArgs = goTokComma >> goExpressionList

-- | Standard @SourceFile@
--
-- See also: SS. 13.1. Source file organization
goSource :: GoParser GoSource
goSource = do
  pkg <- goSemi goPackageClause
  imp <- many $ goSemi goTopLevelPrel
  top <- many $ goSemi goTopLevelDecl
  eof
--goSourceRest
--notFolloedBy anyToken
  return $ GoSource pkg [] top

-- | Nonstandard
goSourceRest :: GoParser ()
goSourceRest = do
  rest <- many anyToken
  case length rest of
    0 -> return ()
    _ -> fail "language-go: Source not consumed"

-- | Standard @PackageClase@
--
-- See also: SS. 13.2. Package clause
goPackageClause :: GoParser GoId
goPackageClause = do
  goTokPackage
  goIdentifier

-- | Standard @ImportDecl@
--
-- See also: SS. 13.3. Import declarations
goImportDecl :: GoParser GoPrel
goImportDecl = goTokImport >> liftM GoImportDecl goImportSpec

-- | Nonstandard
goParenish x = goParenish'' x <|> goParenish' x where
    goParenish' = liftM (replicate 1)
    goParenish'' = goParen . many . goSemi


-- | Standard @ImportSpec@
--
-- See also: SS. 13.3. Import declarations
goImportSpec :: GoParser [GoImpSpec]
goImportSpec = goImpSpecs'' <|> goImpSpecs' where

    goImpSpecs' = liftM (replicate 1) goImpSpec
    goImpSpecs'' = goParen $ many $ goSemi goImpSpec

    goImpSpec :: GoParser GoImpSpec
    goImpSpec = do
      ty <- try goImpType
      ip <- goString -- Go @ImportPath@
      return $ GoImpSpec ty ip

    goImpType :: GoParser GoImpType
    goImpType = lookAhead anyToken >>= \(GoTokenPos _ tok) ->
                case tok of
                  GoTokId _       -> liftM GoImpQual goIdentifier
                  GoTokFullStop   -> liftM GoImpDot goOperator
                  GoTokStr _ _ -> return GoImp
                  _ -> fail "language-go: bad import"

--
--  End specification grammar
--





-- combinators

goAfter :: GoParser b -> GoParser a -> GoParser a
goAfter y x = try (do z <- x ; y ; return z)

goSemi :: GoParser a -> GoParser a
goSemi = goAfter goTokSemicolon

-- literals

goString :: GoParser String
goString = do
  (GoTokenPos _ tok) <- anyToken
  case tok of
    (GoTokStr rep uni) -> return uni
    _ -> fail "String: what?"

goParen = between goTokLParen goTokRParen
goBrace = between goTokLBrace goTokRBrace
goBracket = between goTokLBracket goTokRBracket


-- parsers
-- only in TypeLit:
-- Pointer
-- InterfaceType
-- ChannelType
-- FunctionType (available as FunctionLit)
-- only in LiteralType:
-- goArrayElipsisType
