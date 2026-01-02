{
module Lexer (Token(..), lexer, alexScanTokens) where
}

%wrapper "basic"

$digit = 0-9
$alpha = [a-zA-Z]
$alphanum = [a-zA-Z0-9]

tokens :-
  Int                           { \_ -> TokInt }

{
data Token
  = TokInt
  deriving (Eq, Show)

lexer :: String -> [Token]
lexer = alexScanTokens
}