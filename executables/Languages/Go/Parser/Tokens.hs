-- |
-- Module      : Language.Go.Parser.Tokens
-- Copyright   : (c) 2011 Andrew Robbins
-- License     : GPLv3 (see COPYING)
--
-- x
module Languages.Go.Parser.Tokens where
import Languages.Go.Syntax.AST (GoSource)
import Languages.Go.Syntax.AST
import Text.Parsec.String
import Text.Parsec.Prim hiding (token)
import qualified Text.Parsec.Prim as Prim
import Text.Parsec.Pos (SourcePos(..))
import Text.Parsec.Combinator
import Control.Applicative

-- | GoTokener is the type used for all tokenizers
-- type GoTokener = GenParser Char () [GoToken]

-- | GoParser is the type used for all parsers
type GoParser a = GenParser GoTokenPos () a

-- | GoTokenPos encodes tokens and source positions
data GoTokenPos = GoTokenPos !SourcePos !GoToken
                  deriving (Eq, Show)

-- | GoToken encodes tokens
data GoToken = GoTokNone
             | GoTokComment Bool String
-- BEGIN literals
             | GoTokInt  (Maybe String) Integer
             | GoTokReal (Maybe String) Float
             | GoTokImag (Maybe String) Float
             | GoTokChar (Maybe String) Char
             | GoTokStr  (Maybe String) String
-- END literals
-- BEGIN wraps
             | GoTokLParen   -- '('
             | GoTokRParen   -- ')'
             | GoTokLBrace   -- '{'
             | GoTokRBrace   -- '}'
             | GoTokLBracket -- '['
             | GoTokRBracket -- ']'
-- END wraps
-- BEGIN keywords
             | GoTokBreak
             | GoTokCase
             | GoTokChan
             | GoTokConst
             | GoTokContinue
             | GoTokDefault
             | GoTokDefer
             | GoTokElse
             | GoTokFallthrough
             | GoTokFor
             | GoTokFunc
             | GoTokGo
             | GoTokGoto
             | GoTokIf
             | GoTokImport
             | GoTokInterface
             | GoTokMap
             | GoTokPackage
             | GoTokRange
             | GoTokReturn
             | GoTokSelect
             | GoTokStruct
             | GoTokSwitch
             | GoTokType
             | GoTokVar
-- END keywords
             | GoTokSemicolonAuto
             | GoTokSemicolon -- ';'
             | GoTokColon     -- ':'
             | GoTokColonEq   -- ':='
             | GoTokEqual     -- '='
             | GoTokComma     -- ','
             | GoTokFullStop  -- '.'
             | GoTokElipsis   -- '...'
-- BEGIN operators
             | GoTokLOR       -- '||'
             | GoTokLAND      -- '&&'
             | GoTokEQ        -- '=='
             | GoTokNE        -- '!='
             | GoTokLT        -- '<'
             | GoTokLE        -- '<='
             | GoTokGT        -- '>'
             | GoTokGE        -- '>='
             | GoTokPlus      -- '+'
             | GoTokMinus     -- '-'
             | GoTokIOR       -- '|'
             | GoTokXOR       -- '^'
             | GoTokAsterisk  -- '*'
             | GoTokSolidus   -- '/'
             | GoTokPercent   -- '%'
             | GoTokSHL       -- '<<'
             | GoTokSHR       -- '>>'
             | GoTokAND       -- '&'
             | GoTokBUT       -- '&^'
             | GoTokExclaim   -- '!'
             | GoTokArrow     -- '<-'
             | GoTokDec       -- '--'
             | GoTokInc       -- '++'
-- END operators
-- BEGIN names
             | GoTokId String
             | GoTokOp String -- future extensions
-- END names
               deriving (Eq, Read, Show)
-- Data, Typeable

tokenSimplify :: (Int, Int) -> String -> String
tokenSimplify (n, m) s = map (s!!) [n..(length s)-m-1]

tokenFromId :: String -> GoToken
tokenFromId s = GoTokId $ if s!!0 == '#' && s!!1 == '['
                          then tokenSimplify (2, 1) s
                          else s

tokenFromOp :: String -> GoToken
tokenFromOp s = GoTokOp $ if s!!0 == '#' && s!!1 == '{'
                          then tokenSimplify (2, 1) s
                          else s

-- False=singleline True=multiline
tokenFromComment :: Bool -> String -> GoToken
tokenFromComment False s = GoTokComment False $ tokenSimplify (2, 1) s
tokenFromComment True  s = GoTokComment True  $ tokenSimplify (2, 2) s

tokenFromInt :: String -> GoToken
tokenFromInt s = GoTokInt (Just s) $ ((read s) :: Integer)

tokenFromReal :: String -> GoToken
tokenFromReal s = GoTokReal (Just s) $ (read s)

tokenFromImag :: String -> GoToken
tokenFromImag s = GoTokImag (Just s) $ (read $ init s)

tokenFromRawStr :: String -> GoToken
tokenFromRawStr s = GoTokStr (Just s) $ tokenSimplify (1, 1) s

-- TODO: process \u#### and stuff
tokenFromString :: String -> GoToken
tokenFromString s = GoTokStr (Just s) $ tokenSimplify (1, 1) s

tokenFromChar :: String -> GoToken
tokenFromChar s = GoTokChar (Just s) (s!!1)


-- tokens

tokenEq :: GoToken -> GoToken -> Bool
tokenEq (GoTokComment _ _) (GoTokComment _ _) = True
tokenEq (GoTokInt _ _)     (GoTokInt _ _) = True
tokenEq (GoTokReal   _ _)  (GoTokReal   _ _) = True
tokenEq (GoTokImag  _ _)   (GoTokImag  _ _) = True
tokenEq (GoTokId _) (GoTokId _) = True
tokenEq (GoTokOp _) (GoTokOp _) = True
tokenEq a b = a == b

token :: GoToken -> GoParser GoToken
token tok = Prim.token showTok posnTok testTok
    where showTok (GoTokenPos pos t) = show t
          posnTok (GoTokenPos pos t) = pos
          testTok (GoTokenPos pos t) = if tokenEq tok t
                                       then Just t
                                       else Nothing

stripComments :: [GoTokenPos] -> [GoTokenPos]
stripComments tokens = map nocomm tokens where
    nocomm (xt@(GoTokenPos xp x)) = if (tokenEq x (GoTokComment False ""))
                                    then (GoTokenPos xp GoTokSemicolonAuto)
                                    else xt

stripNone :: [GoTokenPos] -> [GoTokenPos]
stripNone tokens = filter nonull tokens where
    nonull (GoTokenPos _ x) = (x /= GoTokNone)

stripAuto :: [GoTokenPos] -> [GoTokenPos]
stripAuto tokens = filter nonull tokens where
    nonull (GoTokenPos _ x) = (x /= GoTokSemicolonAuto)

needSemi :: GoToken -> Bool
needSemi token = case token of
                     GoTokId _        -> True
                     GoTokInt  _ _    -> True
                     GoTokReal _ _    -> True
                     GoTokImag _ _    -> True
                     GoTokChar _ _    -> True
                     GoTokStr  _ _    -> True
                     GoTokBreak       -> True
                     GoTokContinue    -> True
                     GoTokFallthrough -> True
                     GoTokReturn      -> True
                     GoTokDec         -> True
                     GoTokInc         -> True
                     GoTokRParen      -> True
                     GoTokRBrace      -> True
                     GoTokRBracket    -> True
                     _ -> False

appendSemi :: [GoTokenPos] -> [GoTokenPos]
appendSemi tokens = tokens ++ semi where
    semi = [GoTokenPos (lastpos $ last tokens) GoTokSemicolonAuto]
    lastpos (GoTokenPos pos _) = pos

insertSemi :: [GoTokenPos] -> [GoTokenPos]
insertSemi = stripAuto . stripNone . 
             insertAfter . stripNone . insertBefore . 
             insertAfter . stripNone . appendSemi 

--insertSemi = insertAfter . stripNone . insertBefore . appendSemi

insertAfter :: [GoTokenPos] -> [GoTokenPos]
insertAfter [] = []
insertAfter ((xt@(GoTokenPos xp x)):[]) = (xt:[])
insertAfter ((xt@(GoTokenPos _ x)):(yt@(GoTokenPos yp y)):zs) = xt:(insertAfter ((repl y):zs))
    where cond = if needSemi x then GoTokSemicolon else GoTokNone
          repl GoTokSemicolonAuto = GoTokenPos yp cond
          repl _ = yt

insertBefore :: [GoTokenPos] -> [GoTokenPos]
insertBefore [] = []
insertBefore ((xt@(GoTokenPos xp x)):[]) = xt:[]
insertBefore ((xt@(GoTokenPos xp x)):(yt@(GoTokenPos yp y)):zs) = out
    where repl (GoTokRBrace) (GoTokSemicolon) = GoTokenPos xp GoTokSemicolonAuto
          repl (GoTokRBrace) (GoTokElse) = GoTokenPos xp GoTokSemicolonAuto
--          repl (GoTokRParen) (GoTokSemicolon) = GoTokenPos xp GoTokSemicolonAuto
          repl _ _ = GoTokenPos xp GoTokNone
          out = ((repl x y):xt:(insertBefore (yt:zs)))



-- token parsers

goTokLParen   = token $ GoTokLParen
goTokRParen   = token $ GoTokRParen
goTokLBrace   = token $ GoTokLBrace
goTokRBrace   = token $ GoTokRBrace
goTokLBracket = token $ GoTokLBracket
goTokRBracket = token $ GoTokRBracket

goTokSemicolon= token $ GoTokSemicolon -- ';'
goTokColon    = token $ GoTokColon     -- ':'
goTokColonEq  = token $ GoTokColonEq   -- ':='
goTokEqual    = token $ GoTokEqual     -- '='
goTokComma    = token $ GoTokComma     -- ','
goTokFullStop = token $ GoTokFullStop  -- '.'
goTokElipsis  = token $ GoTokElipsis   -- '...'


-- BEGIN operators
goTokLOR      = do token GoTokLOR      ; return$Go2Op$GoOp "||" -- '||'
goTokLAND     = do token GoTokLAND     ; return$Go2Op$GoOp "&&" -- '&&'
goTokEQ       = do token GoTokEQ       ; return$Go2Op$GoOp "==" -- '=='
goTokNE       = do token GoTokNE       ; return$Go2Op$GoOp "!=" -- '!='
goTokLT       = do token GoTokLT       ; return$Go2Op$GoOp "<"  -- '<'
goTokLE       = do token GoTokLE       ; return$Go2Op$GoOp "<=" -- '<='
goTokGT       = do token GoTokGT       ; return$Go2Op$GoOp ">"  -- '>'
goTokGE       = do token GoTokGE       ; return$Go2Op$GoOp ">=" -- '>='
goTokPlus   f = do token GoTokPlus     ; return$  f  $GoOp "+"  -- '+'
goTokMinus  f = do token GoTokMinus    ; return$  f  $GoOp "-"  -- '-'
goTokIOR      = do token GoTokIOR      ; return$Go2Op$GoOp "|"  -- '|'
goTokXOR    f = do token GoTokXOR      ; return$  f  $GoOp "^"  -- '^'
goTokStar   f = do token GoTokAsterisk ; return$  f  $GoOp "*"  -- '*'
goTokSolidus  = do token GoTokSolidus  ; return$Go2Op$GoOp "/"  -- '/'
goTokPercent  = do token GoTokPercent  ; return$Go2Op$GoOp "%"  -- '%'
goTokSHL      = do token GoTokSHL      ; return$Go2Op$GoOp "<<" -- '<<'
goTokSHR      = do token GoTokSHR      ; return$Go2Op$GoOp ">>" -- '>>'
goTokAND    f = do token GoTokAND      ; return$  f  $GoOp "&"  -- '&'
goTokBUT      = do token GoTokBUT      ; return$Go2Op$GoOp "&^" -- '&^'
goTokExclaim  = do token GoTokExclaim  ; return$Go1Op$GoOp "!"  -- '!'
goTokArrow  f = do token GoTokArrow    ; return$  f  $GoOp "<-" -- '<-'
goTokDec      = do token GoTokDec      ; return$Go1Op$GoOp "--" -- '--'
goTokIng      = do token GoTokInc      ; return$Go1Op$GoOp "++" -- '++'
-- END operators

goTokAsterisk = goTokStar (\x -> ())
goTokArrow1 = do goTokArrow (Go1Op) ; return $GoOp "<-"
goTokArrow2 = do goTokArrow (Go2Op) ; return $GoOp "<-"

-- BEGIN keywords
goTokBreak    = token $ GoTokBreak
goTokCase     = token $ GoTokCase
goTokChan     = token $ GoTokChan
goTokConst    = token $ GoTokConst
goTokContinue = token $ GoTokContinue
goTokDefault  = token $ GoTokDefault
goTokDefer    = token $ GoTokDefer
goTokElse     = token $ GoTokElse
goTokFallthrough = token $ GoTokFallthrough
goTokFor      = token $ GoTokFor
goTokFunc     = token $ GoTokFunc
goTokGo       = token $ GoTokGo
goTokGoto     = token $ GoTokGoto
goTokIf       = token $ GoTokIf
goTokImport   = token $ GoTokImport
goTokInterface= token $ GoTokInterface
goTokMap      = token $ GoTokMap
goTokPackage  = token $ GoTokPackage
goTokRange    = token $ GoTokRange
goTokReturn   = token $ GoTokReturn
goTokSelect   = token $ GoTokSelect
goTokStruct   = token $ GoTokStruct
goTokSwitch   = token $ GoTokSwitch
goTokType     = token $ GoTokType
goTokVar      = token $ GoTokVar
-- END keywords




--

goIdentifier :: GoParser GoId
goIdentifier = do
  GoTokId name <- token $ GoTokId ""
  return $ GoId name

goOperator :: GoParser GoOp
goOperator = do
  GoTokOp name <- token $ GoTokOp ""
  return $ GoOp name

goUnaryOp :: GoParser GoOp
goUnaryOp = goOperator

goBinaryOp :: GoParser GoOp
goBinaryOp = do
  op <- goOperator
  case op of
    (GoOp "<-") -> fail "binary op"
    (GoOp ":=") -> fail "binary op"
    (GoOp "=")  -> fail "binary op"
    _ -> return op -- goOperator


-- | Standard @assign_op@
--
-- See also: SS. 11.6. Assignments
goAssignOp :: GoParser GoOp
goAssignOp = try $ do
  (GoTokenPos _ op) <- lookAhead anyToken
  case op of
    GoTokOp opname -> if last opname == '='
                      then goOperator
                      else fail "Assignment What?"
    GoTokEqual     -> do anyToken; return (GoOp "=")
    x -> unexpected (show x)
  
