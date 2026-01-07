{
module EnvML.Parser.HappyAlex.Lexer (Token(..), lexer) where
}

%wrapper "basic"

$digit = 0-9
$alpha = [a-zA-Z]
$alphanum = [a-zA-Z0-9]

tokens :-
  $white+     ;
  "--".*      ; -- Comments

  -- Keywords
  int         { \_ -> TokTInt  }
  let         { \_ -> TokLet  }
  val         { \_ -> TokVal  }
  type        { \_ -> TokType }
  fun         { \_ -> TokLam  }
  clos        { \_ -> TokClos }

  -- Symbols
  "="         { \_ -> TokEq       }
  ":"         { \_ -> TokColon    }
  "("         { \_ -> TokLParen   }
  ")"         { \_ -> TokRParen   }
  "["         { \_ -> TokLBracket }
  "]"         { \_ -> TokRBracket }
  "{"         { \_ -> TokLBrace   }
  "}"         { \_ -> TokRBrace   }
  ","         { \_ -> TokComma    }
  ";;"        { \_ -> TokSemiSemi }
  "->"        { \_ -> TokArrow    }

  -- Literals and Identifiers
  $digit+             { \s -> TokInt (read s) }
  $alpha $alphanum *  { \s -> TokVar s }
  \" [^\"]* \"        { \s -> TokStr (read s) }

{
data Token
  = TokInt Int
  | TokStr String
  | TokVar String
  -- Keywords
  | TokTInt
  | TokType
  | TokLet
  | TokVal
  | TokLam
  | TokClos
  -- Symbol Tokens
  | TokEq
  | TokColon    
  | TokLParen   
  | TokRParen   
  | TokLBracket 
  | TokRBracket 
  | TokLBrace   
  | TokRBrace   
  | TokComma    
  | TokSemiSemi
  | TokArrow
  deriving (Eq, Show)

lexer :: String -> [Token]
lexer = alexScanTokens
}
