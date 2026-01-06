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
  '='       { TokEq }
  ':'       { TokColon }
  ';;'      { TokSemiSemi }
  '->'      { TokArrow }
  '('       { TokLParen }
  ')'       { TokRParen }

%right '->'

%%

-------------------------------------------------------------------------
-- .eml Files (Structs)
-------------------------------------------------------------------------

-- A program file is implicitly a Struct containing a list of Env elements
ModuleBody :: { Module }
  : Env { Struct $1 }

Env :: { Env }
  : EnvE Env            { $1 : $2 }
  |                     { [] }

EnvE :: { (Name, EnvE) }
  : let id '=' Exp ';;'  { ($2, ExpE $4) }
  | type id '=' Typ ';;' { ($2, TypE $4) }

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
  : num                 { Lit (LitInt $1) }
  | id                  { Var $1 }
  | '(' Exp ')'         { $2 }

Typ :: { Typ }
  : int                 { TyLit TyInt }
  | id                  { TyVar $1 }
  | Typ '->' Typ        { TyArr $1 $3 }
  | '(' Typ ')'         { $2 }

{
parseError :: [Token] -> a
parseError tokens = error $ "Parse error: " ++ show tokens
}