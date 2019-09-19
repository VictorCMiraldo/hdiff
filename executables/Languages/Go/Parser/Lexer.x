{
-- |
-- Module: Language.Go.Parser.Lexer
module Languages.Go.Parser.Lexer where
import Languages.Go.Parser.Tokens
import Text.Parsec.Pos
}

%wrapper "posn"

-- SS. 3.1. Characters
@unicode_char   = [\x00-\x7F]|[\x80-\xFF]+
@unicode_nobr   = [\x00-\x5C\x5E-\x7F]|[\x80-\xFF]+
@unicode_nobq   = [\x00-\x5F\x61-\x7F]|[\x80-\xFF]+
@unicode_nodq   = [\x00-\x21\x23-\x7F]|[\x80-\xFF]+
@unicode_letter = [A-Za-z] -- should be [\p{L}]
@unicode_digit  = [0-9]    -- should be [\p{N}]

-- SS. 3.2 Letters and digits
@letter         = _|@unicode_letter
$decimal_digit  = [0-9]
$octal_digit    = [0-7]
$hex_digit      = [0-9A-Fa-f]
$sign           = [\+\-]
$punctuation    = [\!\@\#\$\%\^\&\*\-\+=\<\>\,\.\:\;\|\\\/\?\~]

-- SS. 4.1. Comments
@ol_char    = [^\n]
@ml_char    = [\x00-\x29\x2B-\xFF]|\*[\x00-\x2E\x30-\xFF]
@ol_comment = "//"(@ol_char)*\n
@ml_comment = "/*"(@ml_char)*"*/"

-- SS. 4.2. Tokens
$whitespace = [\ \t\f\v\r]
$whiteline  = [\n]

-- SS. 4.4. Identifiers
@ident7bit  = @letter(@letter|@unicode_digit)*
@identifier = (@ident7bit)|\#\[(@unicode_nobr)+\]

-- SS. 4.6. Operators and Delimiters
@operator   = ($punctuation)+|\#\{(@unicode_nobr)+\}

-- SS. 4.7. Integer literals
@decimallit = [1-9]($decimal_digit)*
@octal_lit  = 0($octal_digit)*
@hex_lit    = 0[xX]($hex_digit)+
@int_lit    = (@decimallit|@octal_lit|@hex_lit)

-- SS. 4.8. Floating-point literals
@decimals   = ($decimal_digit)+
@exponent   = [eE]($sign)?(@decimals)
@float1lit  = (@decimals)\.(@decimals)?(@exponent)?
@float2lit  = (@decimals)(@exponent)
@float3lit  = \.(@decimals)(@exponent)?
@float_lit  = (@float1lit|@float2lit|@float3lit)

-- SS. 4.9. Imaginary literals
@imaginary_lit  = (@decimals|@float_lit)i
@hex_byte_value = \\x($hex_digit){2}
@oct_byte_value = \\($octal_digit){3}
@little_u_value = \\u($hex_digit){4}
@big_u_value    = \\U($hex_digit){8}
@escaped_char   = \\[abfnrtv\`\'\"]
@unicode_value  = (@unicode_nodq|@little_u_value|@big_u_value|@escaped_char)
@byte_value     = (@oct_byte_value|@hex_byte_value)

-- SS. 4.10. Character literals
@char_lit   = \'(@unicode_value|@byte_value)\'

-- SS. 4.11. String literals
@raw_string_lit = \`(@unicode_nobq)*\`
@int_string_lit = \"(@unicode_value|@byte_value)*\"
@string_lit = (@raw_string_lit|@int_string_lit)

--
--
--

tokens :-

  $whitespace+    { \p s -> posify p $ GoTokNone }
  $whiteline      { \p s -> posify p $ GoTokSemicolonAuto }
  @ol_comment     { \p s -> posify p $ tokenFromComment False s }
  @ml_comment     { \p s -> posify p $ tokenFromComment True s }
  @int_lit        { \p s -> posify p $ tokenFromInt s }
  @float_lit      { \p s -> posify p $ tokenFromReal s }
  @imaginary_lit  { \p s -> posify p $ tokenFromImag s }
  @char_lit       { \p s -> posify p $ tokenFromChar s }
  @raw_string_lit { \p s -> posify p $ tokenFromRawStr s }
  @int_string_lit { \p s -> posify p $ tokenFromString s }
  "("             { \p s -> posify p $ GoTokLParen }
  ")"             { \p s -> posify p $ GoTokRParen }
  "{"             { \p s -> posify p $ GoTokLBrace }
  "}"             { \p s -> posify p $ GoTokRBrace }
  "["             { \p s -> posify p $ GoTokLBracket }
  "]"             { \p s -> posify p $ GoTokRBracket }

  ";"             { \p s -> posify p $ GoTokSemicolon }
  ":"             { \p s -> posify p $ GoTokColon }
  ":="            { \p s -> posify p $ GoTokColonEq }
  "="             { \p s -> posify p $ GoTokEqual }
  ","             { \p s -> posify p $ GoTokComma }
  "."             { \p s -> posify p $ GoTokFullStop }
  "..."           { \p s -> posify p $ GoTokElipsis }
  "_"             { \p s -> posify p $ tokenFromId "_" }

-- BEGIN operators
  "||"            { \p s -> posify p $ GoTokLOR }
  "&&"            { \p s -> posify p $ GoTokLAND }
  "=="            { \p s -> posify p $ GoTokEQ }
  "!="            { \p s -> posify p $ GoTokNE }
  "<"             { \p s -> posify p $ GoTokLT }
  "<="            { \p s -> posify p $ GoTokLE }
  ">"             { \p s -> posify p $ GoTokGT }
  ">="            { \p s -> posify p $ GoTokGE }
  "+"             { \p s -> posify p $ GoTokPlus }
  "-"             { \p s -> posify p $ GoTokMinus }
  "|"             { \p s -> posify p $ GoTokIOR }
  "^"             { \p s -> posify p $ GoTokXOR }
  "*"             { \p s -> posify p $ GoTokAsterisk }
  "/"             { \p s -> posify p $ GoTokSolidus }
  "%"             { \p s -> posify p $ GoTokPercent }
  "<<"            { \p s -> posify p $ GoTokSHL }
  ">>"            { \p s -> posify p $ GoTokSHR }
  "&"             { \p s -> posify p $ GoTokAND }
  "&^"            { \p s -> posify p $ GoTokBUT }
  "!"             { \p s -> posify p $ GoTokExclaim }
  "<-"            { \p s -> posify p $ GoTokArrow }
  "--"            { \p s -> posify p $ GoTokDec }
  "++"            { \p s -> posify p $ GoTokInc }
-- END operators
  @operator       { \p s -> posify p $ tokenFromOp s }

-- BEGIN keywords
  break           { \p s -> posify p $ GoTokBreak }
  case            { \p s -> posify p $ GoTokCase }
  chan            { \p s -> posify p $ GoTokChan }
  const           { \p s -> posify p $ GoTokConst }
  continue        { \p s -> posify p $ GoTokContinue }
  default         { \p s -> posify p $ GoTokDefault }
  defer           { \p s -> posify p $ GoTokDefer }
  else            { \p s -> posify p $ GoTokElse }
  fallthrough     { \p s -> posify p $ GoTokFallthrough }
  for             { \p s -> posify p $ GoTokFor }
  func            { \p s -> posify p $ GoTokFunc }
  go              { \p s -> posify p $ GoTokGo }
  goto            { \p s -> posify p $ GoTokGoto }
  if              { \p s -> posify p $ GoTokIf }
  import          { \p s -> posify p $ GoTokImport }
  interface       { \p s -> posify p $ GoTokInterface }
  map             { \p s -> posify p $ GoTokMap }
  package         { \p s -> posify p $ GoTokPackage }
  range           { \p s -> posify p $ GoTokRange }
  return          { \p s -> posify p $ GoTokReturn }
  select          { \p s -> posify p $ GoTokSelect }
  struct          { \p s -> posify p $ GoTokStruct }
  switch          { \p s -> posify p $ GoTokSwitch }
  type            { \p s -> posify p $ GoTokType }
  var             { \p s -> posify p $ GoTokVar }
-- END keywords
  @identifier     { \p s -> posify p $ tokenFromId s }

{
posAlex2Parsec :: String -> AlexPosn -> SourcePos
posAlex2Parsec filename (AlexPn o l c) = newPos filename l c

posify :: AlexPosn -> GoToken -> GoTokenPos
posify pos tok = GoTokenPos (posAlex2Parsec "" pos) tok
}
