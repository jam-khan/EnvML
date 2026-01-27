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
  typeApp   { TokTypeApp }
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
  import    { TokImport }
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
  '+'       { TokPlus   }
  '-'       { TokDash   }
  '*'       { TokStar   }

%right '->'

%%

-------------------------------------------------------------------------
-- .eml Files (Structs)
-------------------------------------------------------------------------

-- A program file is implicitly a Struct containing a list of Env elements
ModuleBody :: { Module }
  : ModuleImports ModuleEnv { Struct $1 $2 }

ModuleEnv :: { Env }
  : ModuleEnvElem ModuleEnv     { $1 : $2 }
  |                       { [] }

ModuleEnvElem :: { (Name, EnvE) }
  : let id '=' Exp ';;'   { ($2, ExpE $4) }
  | let id ':' Typ '=' Exp ';;' { ($2, ExpE (Anno $6 $4)) }
  | type id '=' Typ ';;'  { ($2, TypE $4) }
  | module let id '=' Exp ';;' { ($3, ModExpE $5) }
  | module let id ':' Typ '=' Exp ';;' { ($3, ModExpE (Anno $7 $5)) }
  | module type id '=' Typ ';;' { ($3, ModTypE $5) }

ModuleImports :: { Imports }
  : import ImportList ';;'    { $2 }  
  |                           { [] } 

ImportList :: { Imports }
  : ImportItem ',' ImportList { $1 : $3 } 
  | ImportItem                { [$1] }    

ImportItem :: { (Name, Typ) }
  : id ':' Typ                { ($1, $3) }

-------------------------------------------------------------------------
-- .emli Files (Signatures)
-------------------------------------------------------------------------

-- An interface file is implicitly a TySig containing a list of Intf elements
InterfaceBody :: { ModuleTyp }
  : Intf { TySig $1 }
  | Typ '->m' InterfaceBody { TyArrowM $1 $3 }

Intf :: { Intf }
  : IntfE Intf          { $1 : $2 }
  |                     { [] }

IntfE :: { IntfE }
  : val id ':' Typ ';;'  { ValDecl $2 $4 }
  | type id '=' Typ ';;' { TyDef $2 $4 }
  | module id ':' Typ ';;' { ModDecl $2 $4 }  
  | module type id '=' Typ ';;' { SigDecl $3 $5 }

-------------------------------------------------------------------------
-- Core Expressions and Types
-------------------------------------------------------------------------

Exp :: { Exp }
  : fun FunArgs '->' Exp   { Lam $2 $4 }
  | clos '[' Env ']' '(' id ')' '->' Exp  { Clos $3 $6 $9 }
  | clos '[' Env ']' type id '->' Exp  { TClos $3 $6 $8 }
  | box '[' Env ']' in Exp            { Box $3 $6 }
  | Term '::' Typ                     { Anno $1 $3 }
  | Exp '+' Exp                       { BinOp (Add $1 $3) }
  | Exp '-' Exp                       { BinOp (Sub $1 $3) }
  | ModuleExp                         { ModE $1 }
  | Term                              { $1 }

ModuleExp :: { Module }
  : id                                    { VarM $1 } -- Add this
  | struct ModuleImports ModuleEnv end    { Struct $2 $3  }
  | ModuleExp '(' ModuleExp ')'           { MApp $1 $3    }
  | ModuleExp '(' typeApp Type ')'        { MAppt $1 $4   }
  | link '(' ModuleExp ',' ModuleExp ')'  { MLink $3 $5   }
  | functor FunArgs '->' ModuleExp        { Functor $2 $4 }
  | '(' ModuleExp ')'                     { $2 }

Term :: { Exp }
  : Term '(' Atom ')'                   { App $1 $3 }
  | Term '<' Typ '>'                  { TApp $1 $3 }
  | Term '.' id                       { RProj $1 $3 }
  | Atom                              { $1 }

Atom :: { Exp }
  : num                               { Lit (LitInt $1) }
  | str                               { Lit (LitStr $1) }
  | true                              { Lit (LitBool True) }
  | false                             { Lit (LitBool False) }
  | id                                { Var $1 }
  | '{' id '=' Exp '}'                { Rec $2 $4 }
  | '[' Env ']'                       { FEnv $2 }
  | '(' Exp ')'                       { $2 }

FunArgs :: { FunArgs }
  : '(' FunArg ')' ',' FunArgs                 { $2 : $5 }
  | '(' FunArg ')'                             { [$2] }

FunArg :: { (Name, FunArg) }
  : id ':' Type                       { ($1, TyArg)    }
  | id                                { ($1, TmArg)    }

Env :: { Env }
  : EnvElem ',' Env  { $1 : $3 }
  | EnvElem                  { [$1] }
  |                                  { [] }

EnvElem :: { (Name, EnvE) }
  : id '=' Exp            { ($1, ExpE $3) }
  | type id '=' Typ       { ($2, TypE $4) }
  | module id '=' Exp     { ($2, ModExpE $4) }
  | module type id '=' Typ { ($3, ModTypE $5) }

Typ :: { Typ }
   : BaseTyp '->' Typ                  { TyArr $1 $3 }
   | forall id '.' Typ                 { TyAll $2 $4 }
   | '[' TyEnv ']' '===>' Typ          { TyBoxT $2 $5 }
   | ModuleTyp                         { TyModule $1 }
   | BaseTyp                           { $1 }

BaseTyp :: { Typ }
  : int                               { TyLit TyInt }
  | bool                              { TyLit TyBool }
  | stringt                           { TyLit TyStr }
  | id                                { TyVar $1 }
  | '{' id ':' Typ '}'                { TyRcd $2 $4 }
  | '[' TyEnv ']'                     { TyEnvt $2 }
  | '(' Typ ')'                       { $2 }

ModuleTyp :: { ModuleTyp }
  : sig Intf end                      { TySig $2 }
  | Typ '->m' ModuleTyp               { TyArrowM $1 $3 }
  | '(' ModuleTyp ')'                 { $2 }

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
