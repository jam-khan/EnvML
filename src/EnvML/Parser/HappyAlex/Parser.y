{
module EnvML.Parser.HappyAlex.Parser where

import EnvML.Parser.HappyAlex.Lexer
import EnvML.Parser.AST
}

%name parseModule ModuleBody
%name parseModuleTyp InterfaceBody
%name parseTyp Typ
%name parseExp Exp

%tokentype  { Token }
%error      { parseError }

%token
  let       { TokLet }
  val       { TokVal }
  type      { TokType }
  int       { TokTInt }
  id        { TokVar $$ }
  num       { TokInt $$ }
  fun       { TokLam   }
  clos      { TokClos  }
  '='       { TokEq }
  ':'       { TokColon }
  ';;'      { TokSemiSemi }
  '->'      { TokArrow }
  ','       { TokComma }
  '('       { TokLParen }
  ')'       { TokRParen }
  '['       { TokLBracket }
  ']'       { TokRBracket }

%right '->'

%%

-------------------------------------------------------------------------
-- .eml Files (Structs)
-------------------------------------------------------------------------

-- A program file is implicitly a Struct containing a list of Env elements
ModuleBody :: { Module }
  : ModuleEnv { Struct $1 }

ModuleEnv :: { Env }
  : ModuleEnvElem ModuleEnv     { $1 : $2 }
  |                       { [] }

ModuleEnvElem :: { (Name, EnvE) }
  : let id '=' Exp ';;'   { ($2, ExpE $4) }
  | type id '=' Typ ';;'  { ($2, TypE $4) }

-------------------------------------------------------------------------
-- .emli Files (Signatures)
-------------------------------------------------------------------------

-- An interface file is implicitly a TySig containing a list of Intf elements
InterfaceBody :: { ModuleTyp }
  : Intf { TySig $1 }

Intf :: { Intf }
  : IntfE Intf          { $1 : $2 }
  |                     { [] }

IntfE :: { IntfE }
  : val id ':' Typ ';;'  { ValDecl $2 $4 }
  | type id '=' Typ ';;' { TyDef $2 $4 }

-------------------------------------------------------------------------
-- Core Expressions and Types
-------------------------------------------------------------------------

Exp :: { Exp }
  -- Lambdas & Type Lambdas (Lowest precedence, right associative)
  : fun '(' id ':' Typ ')' '->' Exp   { Lam $3 $5 $8 }
  | clos '[' Env ']' '(' id ':' Typ ')' '->' Exp  { Clos $3 $6 $8 $11 }
--  | fun type id '->' Exp              { TLam $3 $5 }
--  | box '[' Env ']' in Exp            { Box $3 $6 }
--  | Term '::' Typ                     { Anno $1 $3 }
  | Term                              { $1 }

Term :: { Exp }
  -- Application & Projection (Left associative)
  : Term Atom                         { App $1 $2 }
--  | Term '<' Typ '>'                  { TApp $1 $3 }
--  | Term '.' id                       { RProj $1 $3 }
  | Atom                              { $1 }

Atom :: { Exp }
  : num                               { Lit (LitInt $1) }
--  | str                               { Lit (LitStr $1) }
  | id                                { Var $1 }
--  | '{' id '=' Exp '}'                { Rec $2 $4 }
--  | '[' Env ']'                       { FEnv $2 }
  | '(' Exp ')'                       { $2 }


Env :: { Env }
  : EnvElem ',' Env  { $1 : $3 }
  | EnvElem                  { [$1] }
  |                                  { [] }

EnvElem :: { (Name, EnvE) }
  : id '=' Exp            { ($1, ExpE $3) }
  | type id '=' Typ       { ($2, TypE $4) }

Typ :: { Typ }
  : int                 { TyLit TyInt }
  | id                  { TyVar $1 }
  | Typ '->' Typ        { TyArr $1 $3 }
  | '(' Typ ')'         { $2 }

{
parseError :: [Token] -> a
parseError tokens = error $ "Parse error: " ++ show tokens
}
