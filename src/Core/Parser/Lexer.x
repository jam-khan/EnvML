{
module Core.Parser.Lexer (Token(..), lexer, alexScanTokens) where
}

%wrapper "basic"

$digit = 0-9
$alpha = [a-zA-Z]
$alphanum = [a-zA-Z0-9]

tokens :-
  $white+                       ;
  "--".*                        ;
  
  -- Keywords
  Int                           { \_ -> TokInt }
  Bool                          { \_ -> TokBoolKw }
  String                        { \_ -> TokStrKw }
  forall                        { \_ -> TokForall }
  Env                           { \_ -> TokEnv }
  eq                            { \_ -> TokEq }
  tdef                          { \_ -> TokTdef }
  lam                           { \_ -> TokLam }
  Lam                           { \_ -> TokBLam }
  fix                           { \_ -> TokFix }
  if                            { \_ -> TokIf }
  then                          { \_ -> TokThen }
  else                          { \_ -> TokElse }
  true                          { \_ -> TokBool True }
  false                         { \_ -> TokBool False }

  -- Literals
  x $digit+                     { \s -> TokVar (read (drop 1 s)) }
  $digit+                       { \s -> TokNum (read s) }
  \" [^\"]* \"                  { \s -> TokString (elemAt s) } -- Simple string handling
  $alpha $alphanum*             { \s -> TokIdent s }

  -- Operators
  "->"                          { \_ -> TokArrow }
  "|>"                          { \_ -> TokTriangle }
  "#["                          { \_ -> TokHashBracket }
  "("                           { \_ -> TokLParen }
  ")"                           { \_ -> TokRParen }
  "["                           { \_ -> TokLBracket }
  "]"                           { \_ -> TokRBracket }
  "{"                           { \_ -> TokLBrace }
  "}"                           { \_ -> TokRBrace }
  "<"                           { \_ -> TokLAngle }
  ">"                           { \_ -> TokRAngle }
  ":"                           { \_ -> TokColon }
  ","                           { \_ -> TokComma }
  "."                           { \_ -> TokDot }
  "*"                           { \_ -> TokStar }
  "@"                           { \_ -> TokAt }
  "="                           { \_ -> TokEquals }
  "=="                          { \_ -> TokEqOp }
  "|"                           { \_ -> TokBar }
  "-"                           { \_ -> TokSub }
  "**"                          { \_ -> TokMul }

{
-- Helper to strip quotes
elemAt :: String -> String
elemAt s = reverse $ drop 1 $ reverse $ drop 1 s

data Token
  = TokInt
  | TokBoolKw
  | TokStrKw
  | TokForall
  | TokEnv
  | TokEq
  | TokTdef
  | TokLam
  | TokBLam
  | TokFix
  | TokIf
  | TokThen
  | TokElse
  | TokBool Bool
  | TokString String
  | TokVar Int
  | TokIdent String
  | TokNum Int
  | TokArrow
  | TokTriangle
  | TokHashBracket
  | TokLParen
  | TokRParen
  | TokLBracket
  | TokRBracket
  | TokLBrace
  | TokRBrace
  | TokLAngle
  | TokRAngle
  | TokColon
  | TokComma
  | TokDot
  | TokStar
  | TokAt
  | TokEquals
  | TokEqOp
  | TokBar
  | TokSub
  | TokMul
  deriving (Eq, Show)

lexer :: String -> [Token]
lexer = alexScanTokens
}