module Languages.Go.Parser.Operators where
import Languages.Go.Parser.Tokens
import Languages.Go.Syntax.AST
import Text.Parsec.Expr

goOpExpr :: GoParser GoExpr -> GoParser GoExpr
goOpExpr p = buildExpressionParser goOpTable p
goOpTable =
  [ [ Prefix (goTokPlus  (Go1Op))
    , Prefix (goTokMinus (Go1Op))
    , Prefix (goTokExclaim      )
    , Prefix (goTokAND   (Go1Op))
    , Prefix (goTokXOR   (Go1Op))
    , Prefix (goTokStar  (Go1Op)) ]
  , [ Infix  (goTokStar  (Go2Op)) AssocLeft
    , Infix  (goTokSolidus      ) AssocLeft
    , Infix  (goTokPercent      ) AssocLeft
    , Infix  (goTokSHL          ) AssocLeft
    , Infix  (goTokSHR          ) AssocLeft
    , Infix  (goTokAND   (Go2Op)) AssocLeft
    , Infix  (goTokBUT          ) AssocLeft ]
  , [ Infix  (goTokPlus  (Go2Op)) AssocLeft
    , Infix  (goTokMinus (Go2Op)) AssocLeft
    , Infix  (goTokIOR          ) AssocLeft
    , Infix  (goTokXOR   (Go2Op)) AssocLeft ]
  , [ Infix  (goTokEQ           ) AssocLeft
    , Infix  (goTokNE           ) AssocLeft
    , Infix  (goTokLT           ) AssocLeft
    , Infix  (goTokLE           ) AssocLeft
    , Infix  (goTokGT           ) AssocLeft
    , Infix  (goTokGE           ) AssocLeft ]
--  , [ Infix  (goTokArrow (Go2Op)) AssocLeft ] -- Removed 2011-Feb
  , [ Infix  (goTokLAND         ) AssocLeft ]
  , [ Infix  (goTokLOR          ) AssocLeft ]
  ]


--goBinary :: GoParser GoExpr -> GoParser GoExpr
--goBinary p = buildExpressionParser goBinaryTable p
--goBinaryTable =
--goUnaryExpr =  goPrimaryExpr
--           <|> do op <- goUnaryOp
--                  ex <- goUnaryExpr
--                  return $ Go1Op op ex
--goBinaryExpr ex = try $ do
--  op <- goBinaryOp
--  e2 <- goExpression
--  return $ Go2Op op ex e2
--goBinaryExpr' :: GoExpr -> GoParser GoExpr
--goBinaryExpr' ex = (goBinaryExpr ex >>= goBinaryExpr') <|> return ex
{-
TODO:
 [X] operator precedence
 [X] operator associativity

-- See also: SS. 10.12.1. Operator precedence
etc.
-}
