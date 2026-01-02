{
module Parser (parseTyp, parseEnv, parseExp) where

import Lexer (Token(..))
import Syntax (Typ(..), Bind(..), Env, Exp(..), Cet(..), CEnv)
}

%name parseTyp Typ
%name parseEnv EnvBracketed
%name parseExp Exp
%tokentype { Token }
%error { parseError }

-- Expected shift/reduce conflicts
%expect 1

%token
  Int       { TokInt }

%right '->'
%left '.'

%%

AtomTyp :: { Typ }
  : Int                         { TInt }

{
parseError :: [Token] -> a
parseError tokens = error $ "Parse error: " ++ show tokens
}