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
  string      { \_ -> TokTStr  }
  bool        { \_ -> TokTBool  }
  true        { \_ -> TokTrue  }
  false       { \_ -> TokFalse  }
  let         { \_ -> TokLet  }
  val         { \_ -> TokVal  }
  type        { \_ -> TokType }
  Type        { \_ -> TokBType }
  fun         { \_ -> TokFun  }
  clos        { \_ -> TokClos }
  box         { \_ -> TokBox  }
  in          { \_ -> TokIn  }
  forall      { \_ -> TokForall }
  module      { \_ -> TokModule }
  sig         { \_ -> TokSig  }
  end         { \_ -> TokEnd  }
  functor     { \_ -> TokFunctor  }
  struct      { \_ -> TokStruct  }
  link        { \_ -> TokLink  }
  import      { \_ -> TokImport  }

  -- Symbols
  "="         { \_ -> TokEq       }
  ":"         { \_ -> TokColon    }
  ":="        { \_ -> TokColonEqual    }
  "("         { \_ -> TokLParen   }
  ")"         { \_ -> TokRParen   }
  "["         { \_ -> TokLBracket }
  "]"         { \_ -> TokRBracket }
  "{"         { \_ -> TokLBrace   }
  "}"         { \_ -> TokRBrace   }
  "<"         { \_ -> TokLAngle   }
  ">"         { \_ -> TokRAngle   }
  "."         { \_ -> TokDot      } 
  ","         { \_ -> TokComma    }
  ";"         { \_ -> TokSemi     }
  ";;"        { \_ -> TokSemiSemi }
  "::"        { \_ -> TokDoubleColon     }
  "->"        { \_ -> TokArrow    }
  "->m"       { \_ -> TokArrowM    }
  "===>"      { \_ -> TokTripleArrow    }

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
  | TokTBool
  | TokTStr
  | TokTrue
  | TokFalse
  | TokBType
  | TokLet
  | TokVal
  | TokFun
  | TokClos
  | TokBox
  | TokIn
  | TokForall
  | TokModule
  | TokSig
  | TokEnd
  | TokFunctor
  | TokStruct
  | TokImport
  -- Symbol Tokens
  | TokEq
  | TokColon    
  | TokLParen   
  | TokRParen   
  | TokLBracket 
  | TokRBracket 
  | TokLBrace   
  | TokRBrace   
  | TokLAngle
  | TokRAngle
  | TokComma    
  | TokDot
  | TokSemi
  | TokSemiSemi
  | TokArrow
  | TokArrowM
  | TokTripleArrow
  | TokDoubleColon
  | TokColonEqual
  | TokLink
  deriving (Eq, Show)

lexer :: String -> [Token]
lexer = alexScanTokens
}
