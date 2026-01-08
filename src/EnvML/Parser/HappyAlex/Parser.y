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
  Type      { TokBType }
  int       { TokTInt }
  bool      { TokTBool }
  true      { TokTrue }
  false     { TokFalse }
  stringt   { TokTStr }
  str       { TokStr $$ }
  id        { TokVar $$ }
  num       { TokInt $$ }
  fun       { TokFun   }
  clos      { TokClos  }
  box       { TokBox   }
  in        { TokIn    }
  forall    { TokForall }
  module    { TokModule }
  sig       { TokSig }
  end       { TokEnd }
  functor   { TokFunctor }
  struct    { TokStruct }
  link      { TokLink }
  '='       { TokEq }
  ':'       { TokColon }
  ';'       { TokSemi }
  ';;'      { TokSemiSemi }
  '::'      { TokDoubleColon }
  ':='      { TokColonEqual }
  '->'      { TokArrow }
  '===>'    { TokTripleArrow }
  '->m'     { TokArrowM }
  ','       { TokComma }
  '.'       { TokDot }
  '('       { TokLParen }
  ')'       { TokRParen }
  '['       { TokLBracket }
  ']'       { TokRBracket }
  '{'       { TokLBrace }
  '}'       { TokRBrace }
  '<'       { TokLAngle }
  '>'       { TokRAngle }

%right '->'

%%

-------------------------------------------------------------------------
-- .eml Files (Structs)
-------------------------------------------------------------------------

-- A program file is implicitly a Struct containing a list of Env elements
ModuleBody :: { Module }
  : functor '(' id ':' Typ ')' '->' ModuleBody { Functor $3 $5 $8 }
  | ModuleEnv { Struct $1 }
  | struct ModuleEnv end { Struct $2 } -- allow explicit struct ... end
  | ModuleBody '(' ModuleBody ')' { MApp $1 $3 }
  | link '(' ModuleBody ',' ModuleBody ')' { MLink $3 $5 }
  | '(' ModuleBody ')'           { $2 }         

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
  | sig Intf end {TySig $2 } -- allow explicit sig ... end
  | Typ '->m' InterfaceBody { TyArrowM $1 $3 }

Intf :: { Intf }
  : IntfE Intf          { $1 : $2 }
  |                     { [] }

IntfE :: { IntfE }
  : val id ':' Typ ';;'  { ValDecl $2 $4 }
  | type id '=' Typ ';;' { TyDef $2 $4 }
  | module id ':' id ';;' { ModDecl $2 $4 }  
  | module type id '=' InterfaceBody ';;' { SigDecl $3 $5 }

-------------------------------------------------------------------------
-- Core Expressions and Types
-------------------------------------------------------------------------

Exp :: { Exp }
  : fun '(' id ':' Typ ')' '->' Exp   { Lam $3 $5 $8 }
  | clos '[' Env ']' '(' id ':' Typ ')' '->' Exp  { Clos $3 $6 $8 $11 }
  | fun type id '->' Exp              { TLam $3 $5 }
  | clos '[' Env ']' type id '->' Exp  { TClos $3 $6 $8 }
  | box '[' Env ']' in Exp            { Box $3 $6 }
  | Term '::' Typ                     { Anno $1 $3 }
  | ModuleBody                        { ModE $1 }
  | Term                              { $1 }

Term :: { Exp }
  : Term '(' Atom ')'                   { App $1 $3 }
  | Term '<' Typ '>'                  { TApp $1 $3 }
  | Term '.' id                       { RProj $1 $3 }
  | Atom                              { $1 }

Atom :: { Exp }
  : num                               { Lit (LitInt $1) }
  | str                               { Lit (LitStr $1) }
  | true                              { Lit (LitBool True) }
  | false                              { Lit (LitBool False) }
  | id                                { Var $1 }
  | '{' id '=' Exp '}'                { Rec $2 $4 }
  | '[' Env ']'                       { FEnv $2 }
  | '(' Exp ')'                       { $2 }


Env :: { Env }
  : EnvElem ',' Env  { $1 : $3 }
  | EnvElem                  { [$1] }
  |                                  { [] }

EnvElem :: { (Name, EnvE) }
  : id '=' Exp            { ($1, ExpE $3) }
  | type id '=' Typ       { ($2, TypE $4) }

Typ :: { Typ }
   : BaseTyp '->' Typ                  { TyArr $1 $3 }
   | forall id '.' Typ                 { TyAll $2 $4 }
   | '[' TyEnv ']' '===>' Typ          { TyBoxT $2 $5 }
   | '[' id ':=' Typ ']' Typ           { TySubstT $2 $4 $6 }
   | InterfaceBody                     { TyModule $1 }
   | BaseTyp                           { $1 }

BaseTyp :: { Typ }
  : int                               { TyLit TyInt }
  | bool                              { TyLit TyBool }
  | stringt                           { TyLit TyStr }
  | id                                { TyVar $1 }
  | '{' id ':' Typ '}'                { TyRcd $2 $4 }
  | '[' TyEnv ']'                     { TyEnvt $2 }
  | '(' Typ ')'                       { $2 }

TyEnv :: { TyEnv }
  : TyEnvElem ',' TyEnv               { $1 : $3 }
  | TyEnvElem                         { [$1] }
  |                                   { [] }

TyEnvElem :: { (Name, TyEnvE) }
  : id ':' Type                       { ($1, Kind) }
  | id ':' Typ                        { ($1, Type $3) }
  | id ':' '(' Typ ')' '='           { ($1, TypeEq $4) }

{
parseError :: [Token] -> a
parseError tokens = error $ "Parse error: " ++ show tokens
}
