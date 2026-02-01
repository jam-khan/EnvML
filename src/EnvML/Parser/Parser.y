{
module EnvML.Parser.Parser where

import EnvML.Parser.Lexer
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
  tclos     { TokTClos }
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

ModuleBody :: { Module }
  : ModuleImports ModuleEnv { Struct $1 $2 }

ModuleEnv :: { Env }
  : ModuleEnvElem ModuleEnv     { $1 : $2 }
  |                              { [] }

ModuleEnvElem :: { EnvE }
  : let id '=' Exp ';;'                    { ExpEN $2 $4 }
  | let id ':' Typ '=' Exp ';;'            { ExpEN $2 (Anno $6 $4) }
  | type id '=' Typ ';;'                   { TypEN $2 $4 }
  | module id '=' ModuleExp ';;'           { ModE $2 $4 }
  | module id ':' ModuleTyp '=' ModuleExp ';;' { ModE $2 $6 }
  | module type id '=' ModuleTyp ';;'      { ModTypE $3 $5 }

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

InterfaceBody :: { ModuleTyp }
  : Intf                         { TySig $1 }
  | forall id '.' InterfaceBody  { ForallM $2 $4 }
  | Typ '->m' InterfaceBody      { TyArrowM $1 $3 }

Intf :: { Intf }
  : IntfE Intf          { $1 : $2 }
  |                     { [] }

IntfE :: { IntfE }
  : val id ':' Typ ';;'                      { ValDecl $2 $4 }
  | type id '=' Typ ';;'                     { TyDef $2 $4 }
  | module id ':' ModuleTyp ';;'             { ModDecl $2 $4 }
  | functor id FunArgs ':' ModuleTyp ';;'    { FunctorDecl $2 $3 $5 }
  | module type id '=' Intf ';;'             { SigDecl $3 $5 }

-------------------------------------------------------------------------
-- Core Expressions and Types
-------------------------------------------------------------------------

Exp :: { Exp }
  : fun FunArgs '->' Exp                  { Lam $2 $4 }
  | clos '[' Env ']' FunArgs '->' Exp     { Clos $3 $5 $7 }
  | tclos '[' Env ']' FunArgs '->' Exp    { TClos $3 $5 $7 }
  | box '[' Env ']' in Exp                { Box $3 $6 }
  | Term '::' Typ                         { Anno $1 $3 }
  | Exp '+' Exp                           { BinOp (Add $1 $3) }
  | Exp '-' Exp                           { BinOp (Sub $1 $3) }
  | Exp '*' Exp                           { BinOp (Mul $1 $3) }
  | Term                                  { $1 }

ModuleExp :: { Module }
  : struct ModuleImports ModuleEnv end      { Struct $2 $3 }
  | ModuleExp '(' ModuleExp ')'             { MApp $1 $3 }
  | ModuleExp '<' Typ '>'                   { MAppt $1 $3 }
  | link '(' ModuleExp ',' ModuleExp ')'    { MLink $3 $5 }
  | functor FunArgs '->' ModuleExp          { Functor $2 $4 }
  | id                                      { VarM $1 }
  | '(' ModuleExp ')'                       { $2 }

Term :: { Exp }
  : Term '(' Atom ')'    { App $1 $3 }
  | Term '<' Typ '>'     { TApp $1 $3 }
  | Term '.' id          { RProj $1 $3 }
  | Atom                 { $1 }

Atom :: { Exp }
  : num                  { Lit (LitInt $1) }
  | str                  { Lit (LitStr $1) }
  | true                 { Lit (LitBool True) }
  | false                { Lit (LitBool False) }
  | id                   { Var $1 }
  | '{' RecFields '}'    { Rec $2 }
  | '[' Env ']'          { FEnv $2 }
  | '(' Exp ')'          { $2 }
  | ModuleExp            { Mod $1 }

RecFields :: { [(Name, Exp)] }
  : id '=' Exp ',' RecFields  { ($1, $3) : $5 }
  | id '=' Exp                { [($1, $3)] }
  |                           { [] }

FunArgs :: { FunArgs }
  : '(' FunArg ')' FunArgs    { $2 : $4 }
  | '(' FunArg ')'            { [$2] }

FunArg :: { (Name, FunArg) }
  : type id             { ($2, TyArg) }
  | id ':' Typ          { ($1, TmArgType $3) }
  | id                  { ($1, TmArg) }

Env :: { Env }
  : EnvElem ',' Env  { $1 : $3 }
  | EnvElem          { [$1] }
  |                  { [] }

EnvElem :: { EnvE }
  : id '=' Exp                    { ExpEN $1 $3 }
  | Exp                           { ExpE $1 }
  | type id '=' Typ               { TypEN $2 $4 }
  | Typ                           { TypE $1 }
  | module id '=' ModuleExp       { ModE $2 $4 }
  | module type id '=' ModuleTyp  { ModTypE $3 $5 }

Typ :: { Typ }
  : BaseTyp '->' Typ                  { TyArr $1 $3 }
  | forall id '.' Typ                 { TyAll $2 $4 }
  | '[' TyCtx ']' '===>' Typ          { TyBoxT $2 $5 }
  | ModuleTyp                         { TyModule $1 }
  | BaseTyp                           { $1 }

BaseTyp :: { Typ }
  : int                    { TyLit TyInt }
  | bool                   { TyLit TyBool }
  | stringt                { TyLit TyStr }
  | id                     { TyVar $1 }
  | '{' TyRcdFields '}'    { TyRcd $2 }
  | '[' TyCtx ']'          { TyCtx $2 }
  | '(' Typ ')'            { $2 }

TyRcdFields :: { [(Name, Typ)] }
  : id ':' Typ ',' TyRcdFields  { ($1, $3) : $5 }
  | id ':' Typ                  { [($1, $3)] }
  |                             { [] }

ModuleTyp :: { ModuleTyp }
  : sig Intf end                { TySig $2 }
  | forall id '.' ModuleTyp     { ForallM $2 $4 }
  | Typ '->m' ModuleTyp         { TyArrowM $1 $3 }
  | '(' ModuleTyp ')'           { $2 }

TyCtx :: { TyCtx }
  : TyCtxElem ',' TyCtx  { $1 : $3 }
  | TyCtxElem            { [$1] }
  |                      { [] }

TyCtxElem :: { TyCtxE }
  : id ':' Type                         { KindN $1 }
  | Type                                { Kind }
  | id ':' Typ                          { TypeN $1 $3 }
  | Typ                                 { Type $1 }
  | type id '=' Typ                     { TypeEqN $2 $4 }
  | module id ':' ModuleTyp             { TyMod $2 $4 }
  | module type id '=' ModuleTyp        { TypeEqM $3 $5 }

{
parseError :: [Token] -> a
parseError tokens = error $ "Parse error: " ++ show tokens
}