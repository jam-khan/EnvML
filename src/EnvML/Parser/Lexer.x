{
module EnvML.Parser.Lexer (Token(..), lexer) where
}

%wrapper "basic"

$digit = 0-9
$alpha = [a-zA-Z]
$alphanum = [a-zA-Z0-9_]

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
  fix         { \_ -> TokFix  }
  if          { \_ -> TokIf }
  case        { \_ -> TokCase }
  of          { \_ -> TokOf }
  as          { \_ -> TokAs }
  then        { \_ -> TokThen }
  else        { \_ -> TokElse }
  clos        { \_ -> TokClos }
  tclos       { \_ -> TokTClos}
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
  take        { \_ -> TokTake }
  nil         { \_ -> TokNil  }
  list        { \_ -> TokList }
  List        { \_ -> TokListE }

  -- Symbols
  "=="        { \_ -> TokEqEq     }
  "!="        { \_ -> TokNeq      }
  "<="        { \_ -> TokLe       }
  ">="        { \_ -> TokGe       }
  "="         { \_ -> TokEq       }
  ":"         { \_ -> TokColon    }
  ":="        { \_ -> TokColonEqual    }
  "=>"        { \_ -> TokFatArrow    }
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
  "::"        { \_ -> TokDoubleColon}
  "->"        { \_ -> TokArrow    }
  "->m"       { \_ -> TokArrowM   }
  "===>"      { \_ -> TokTripleArrow}
  "+"         { \_ -> TokPlus     }
  "-"         { \_ -> TokDash     }
  "*"         { \_ -> TokStar     }
  "@"         { \_ -> TokAt    }
  "|"         { \_ -> TokPipe   }
  "_"         { \_ -> TokWildcard }

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
  | TokFix
  | TokIf
  | TokCase
  | TokOf
  | TokThen
  | TokAs
  | TokElse
  | TokAt
  | TokClos
  | TokTClos
  | TokBox
  | TokIn
  | TokForall
  | TokModule
  | TokSig
  | TokEnd
  | TokFunctor
  | TokStruct
  | TokImport
  | TokTake
  | TokNil
  | TokList
  | TokListE
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
  | TokEqEq
  | TokNeq
  | TokLe
  | TokGe
  | TokComma    
  | TokDot
  | TokSemi
  | TokArrow
  | TokArrowM
  | TokTripleArrow
  | TokDoubleColon
  | TokColonEqual
  | TokFatArrow
  | TokLink
  | TokPlus
  | TokDash
  | TokStar
  | TokPipe
  | TokWildcard
  deriving (Eq, Show)

lexer :: String -> [Token]
lexer = alexScanTokens
}