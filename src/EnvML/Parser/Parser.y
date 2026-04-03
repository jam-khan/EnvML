{
module EnvML.Parser.Parser where

import EnvML.Parser.Lexer
import EnvML.Syntax
import qualified CoreFE.Syntax as CoreFE
import Data.Char (isUpper)
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
  fix       { TokFix   }
  if        { TokIf    }
  case      { TokCase  }
  of        { TokOf    }
  as        { TokAs    }
  then      { TokThen  }
  else      { TokElse  }
  clos      { TokClos  }
  tclos     { TokTClos }
  box       { TokBox   }
  in        { TokIn    }
  forall    { TokForall }
  forallm   { TokForallM }
  module    { TokModule }
  sig       { TokSig }
  end       { TokEnd }
  functor   { TokFunctor }
  struct    { TokStruct }
  link      { TokLink }
  take      { TokTake }
  nil       { TokNil }
  list      { TokList }
  List      { TokListE }
  unit      { TokUnit }
  '='       { TokEq }
  ':'       { TokColon }
  ';'       { TokSemi }
  '::'      { TokDoubleColon }
  '::m'     { TokDoubleColonM }
  ':='      { TokColonEqual }
  '=>'      { TokFatArrow }
  '->'      { TokArrow }
  '===>'    { TokTripleArrow }
  '->m'     { TokArrowM }
  '@'       { TokAt }
  '@m'      { TokAtM }
  '(|'      { TokLBanana }
  '|)'      { TokRBanana }
  '|'       { TokPipe }
  wildcard  { TokWildcard }
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
  '=='      { TokEqEq }
  '!='      { TokNeq }
  '<='      { TokLe }
  '>='      { TokGe }
  '+'       { TokPlus   }
  '-'       { TokDash   }
  '*'       { TokStar   }

%right '->'
%right '->m'
%nonassoc '==' '!=' '<' '<=' '>' '>='
%left '+' '-'
%left '*'

%%

-------------------------------------------------------------------------
-- .eml Files (Structs)
-------------------------------------------------------------------------

ModuleBody :: { Module }
  : ModuleStructs { Struct $1 }

ModuleStructs :: { Structures }
  : ModuleStruct ModuleStructs { $1 : $2 }
  |                            { [] }

ModuleStruct :: { Structure }
  : let    id          '=' Exp       ';' { Let $2 Nothing $4              }
  | let    id ':' Typ  '=' Exp       ';' { Let $2 (Just $4) $6            }
  | type   id          '=' Constructors ';' { TypDecl $2 (TySum $4)       }
  | type   id          '=' Typ       ';' { TypDecl $2 $4                  }
  | module id          '=' ModuleExp ';' { ModStruct $2 Nothing $4        }
  | module id ':' ModuleTyp 
                       '=' ModuleExp ';' { ModStruct $2 (Just $4) $6      }
  | module type id     '=' ModuleTyp ';' { ModTypDecl  $3 $5              }
  | functor id FunArgs '=' ModuleExp ';' { FunctStruct $2 $3 Nothing $5   }
  | functor id FunArgs ':' ModuleTyp 
                       '=' ModuleExp ';' { FunctStruct $2 $3 (Just $5) $7 }

Constructors :: { [(Name, Typ)] }
  : Constructor '|' Constructors { $1 : $3 }
  | Constructor                  { [$1] }

TypeVars :: { [Name] }
  : id ',' TypeVars { $1 : $3 }
  | id              { [$1] }

Constructor :: { (Name, Typ) }
  : id as Typ { ($1, $3) }

InterfaceBody :: { ModuleTyp }
  : Intf                          { TySig $1 }
  | forallm id '.'   InterfaceBody { ForallM $2 $4 }
  | Typ       '->m' InterfaceBody { TyArrowM $1 $3 }

Intf :: { Intf }
  : IntfE Intf { $1 : $2 }
  |            { [] }

IntfE :: { IntfE }
  : val     id ':' Typ  ';'              { ValDecl $2 $4 }
  | type    id '=' Typ  ';'              { TyDef $2 $4 }
  | module  id ':' id   ';'              { ModDecl $2 (TyVar $4) }
  | module  id ':' ModuleTyp ';'         { ModDecl $2 (TyModule $4) }
  | functor id FunArgs ':' id ';'        { FunctorDecl $2 $3 (TyVar $5) }
  | functor id FunArgs ':' ModuleTyp ';' { FunctorDecl $2 $3 (TyModule $5) }
  | module  type id '=' Intf ';'         { SigDecl $3 $5 }

Exp :: { Exp }
  : fun FunArgs '->' Exp                  { Lam $2 $4 }
  | fix id '.' Exp                        { Fix $2 $4 }
  | if Exp then Exp else Exp              { If $2 $4 $6 }
  | case Exp of '|' CaseBranches          { Case $2 $5 }
  | clos '[' Env ']' FunArgs '->' Exp     { Clos $3 $5 $7 }
  | tclos '[' Env ']' FunArgs '->' Exp    { TClos $3 $5 $7 }
  | box '[' Env ']' in Exp                { Box $3 $6 }
  | Term as Typ                           { mkDataConAs $1 $3 }
  | Term '::' Typ                         { Anno $1 $3 }
  | Exp '==' Exp                          { BinOp (EqEq $1 $3) }
  | Exp '!=' Exp                          { BinOp (Neq $1 $3) }
  | Exp '<' Exp                           { BinOp (Lt $1 $3) }
  | Exp '<=' Exp                          { BinOp (Le $1 $3) }
  | Exp '>' Exp                           { BinOp (Gt $1 $3) }
  | Exp '>=' Exp                          { BinOp (Ge $1 $3) }
  | Exp '+' Exp                           { BinOp (Add $1 $3) }
  | Exp '-' Exp                           { BinOp (Sub $1 $3) }
  | Exp '*' Exp                           { BinOp (Mul $1 $3) }
  | Term                                  { $1 }

ModuleExp :: { Module }
  : struct ModuleStructs end              { Struct  $2 }
  | ModuleExp '(|' ModuleExp '|)'         { MApp    $1 $3 }
  | ModuleExp '@m' Typ                     { MAppt   $1 $3 }
  | ModuleExp '::m' ModuleTyp             { MAnno   $1 $3 }
  | functor FunArgs '->' ModuleExp        { Functor $2 $4 }
  | id                                    { VarM    $1 }
  | '(' ModuleExp ')'                     { $2 }

Term :: { Exp }
  : Term '(' Exp ')'     { App $1 $3 }
  | Term '@' Typ         { TApp $1 $3 }
  | Term '.' id          { RProj $1 $3 }
  | Atom                 { $1 }

Atom :: { Exp }
  : num                       { Lit (CoreFE.LitInt $1) }
  | str                       { Lit (CoreFE.LitStr $1) }
  | true                      { Lit (CoreFE.LitBool True) }
  | false                     { Lit (CoreFE.LitBool False) }
  | '(' ')'                   { Lit CoreFE.LitUnit }
  | id                        { Var $1 }
  | '{' RecFields '}'         { Rec $2 }
  | '[' Env ']'               { FEnv $2 }
  | List '[' ListElems ']'    { EList $3 }
  | nil                       { EList [] }
  | take '(' num ',' Exp ')'  { ETake $3 $5 }
  | '(' Exp ')'               { $2 }
  | ModuleExp                 { Mod $1 }

CaseBranches :: { [CaseBranch] }
  : CaseBranch '|' CaseBranches { $1 : $3 }
  | CaseBranch                  { [$1] }

CaseBranch :: { CaseBranch }
  : '<' id '=' id '>' '=>' Exp  { CaseBranch $2 $4 $7 }
  | wildcard '=>' Exp           { CaseBranch "_" "" $3 }

ListElems :: { [Exp] }
  : Exp ',' ListElems    { $1 : $3 }
  | Exp                  { [$1] }
  |                      { [] }

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
  : id '=' Exp                     { ExpEN $1 $3 }
  | type id '=' Typ                { TypEN $2 $4 }
  | module      id  '=' ModuleExp  { ModE $2 $4 }
  | module type id  '=' ModuleTyp  { ModTypE $3 $5 }
  | Exp                            { ExpE $1 }


Typ :: { Typ }
  : BaseTyp '->' Typ                   { TyArr $1 $3 }
  | forall id '.' Typ                  { TyAll $2 $4 }
  | '[' TyCtx ']' '===>' Typ           { TyBoxT $2 $5 }
  | BaseTyp                            { $1 }

BaseTyp :: { Typ }
  : int                    { TyLit CoreFE.TyInt }
  | bool                   { TyLit CoreFE.TyBool }
  | stringt                { TyLit CoreFE.TyStr }
  | unit                   { TyLit CoreFE.TyUnit }
  | Constructors           { TySum $1 }
  | id                     { TyVar $1 }
  | '{' TyRcdFields '}'    { TyRcd $2 }
  | '[' TyCtx ']'          { TyCtx $2 }
  | list BaseTyp           { TyList $2 }
  | '(' Typ ')'            { $2 }
  | sig Intf end           { TyModule (TySig $2) }

TyRcdFields :: { [(Name, Typ)] }
  : id ':' Typ ',' TyRcdFields  { ($1, $3) : $5 }
  | id ':' Typ                  { [($1, $3)] }
  |                             { [] }

ModuleTyp :: { ModuleTyp }
  : sig Intf end                          { TySig $2 }
  | forallm id '.' ModuleTyp               { ForallM $2 $4 }
  | id '->m' ModuleTyp                    { TyArrowM (TyVar $1) $3 }
  | '(' Typ ')' '->m' ModuleTyp           { TyArrowM $2 $5 }
  | '(' ModuleTyp ')' '->m' ModuleTyp     { TyArrowM (TyModule $2) $5 }
  | '(' ModuleTyp ')'                     { $2 }
  | id                                    { TyVarM $1 }

TyCtx :: { TyCtx }
  : TyCtxElem ',' TyCtx  { $1 : $3 }
  | TyCtxElem            { [$1] }
  |                      { [] }

TyCtxElem :: { TyCtxE }
  : id ':' Type                         { KindN $1 }
  | id ':' Typ                          { TypeN $1 $3 }
  | type id '=' Typ                     { TypeEqN $2 $4 }
  | module id ':' ModuleTyp             { TyMod $2 $4 }
  | module type id '=' ModuleTyp        { TypeEqM $3 $5 }
  | Type                                { Kind }
  | id                                  { Type (TyVar $1) }
  | int                                 { Type (TyLit CoreFE.TyInt) }
  | bool                                { Type (TyLit CoreFE.TyBool) }
  | stringt                             { Type (TyLit CoreFE.TyStr) }
  | unit                                { Type (TyLit CoreFE.TyUnit) }

{
parseError :: [Token] -> a
parseError tokens = error $ "Parse error: " ++ show tokens

mkDataConAs :: Exp -> Typ -> Exp
mkDataConAs (App (Var n) e) t
  | not (null n) && isUpper (head n) = DataCon n e t
mkDataConAs e _ = error $ "`as` is only valid on data constructor applications, got: " ++ show e
}