{
module CoreFE.Parser.Parser (parseTyp, parseEnv, parseExp) where

import CoreFE.Parser.Lexer (Token(..))
import CoreFE.Syntax
}

%name parseTyp Typ
%name parseEnv EnvBracketed
%name parseExp Exp
%tokentype { Token }
%error { parseError }

%expect 1

%token
  int_kw    { TokInt }
  bool_kw   { TokBoolKw }
  str_kw    { TokStrKw }
  forall    { TokForall }
  EnvKw     { TokEnv }
  eq        { TokEq }           -- for TypeEq definition
  tdef      { TokTdef }
  lam       { TokLam }
  TLam      { TokBLam }         -- Usually capital 'Lam' in source
  var       { TokVar $$ }       -- De-bruijn index
  ident     { TokIdent $$ }
  num       { TokNum $$ }        -- Integer literal
  bool      { TokBool $$ }       -- Boolean literal
  string    { TokString $$ }     -- String literal
  fix       { TokFix }
  if        { TokIf }
  then      { TokThen }
  else      { TokElse }
  '->'      { TokArrow }
  '|>'      { TokTriangle }
  '#['      { TokHashBracket }
  '('       { TokLParen }
  ')'       { TokRParen }
  '['       { TokLBracket }
  ']'       { TokRBracket }
  '{'       { TokLBrace }
  '}'       { TokRBrace }
  '<'       { TokLAngle }
  '>'       { TokRAngle }
  ':'       { TokColon }
  ','       { TokComma }
  '.'       { TokDot }
  '*'       { TokStar }
  '@'       { TokAt }
  '='       { TokEquals }       -- record assignment
  '=='      { TokEqOp }         -- equality check
  '|'       { TokBar }
  '-'       { TokSub }
  '**'      { TokMul }          -- using ** to avoid confusion with * (Kind)

%right '->'
%nonassoc '=='
%left '-'
%left '**'
%left '.'

%%

-- Expressions
Exp :: { Exp }
  : lam '.' Exp                         { Lam $3 }
  | TLam '.' Exp                        { TLam $3 }
  | if Exp then Exp else Exp            { If $2 $4 $6 }
  | fix Exp                             { Fix $2 }
  | AppExp ':' Typ                      { Anno $1 $3 }
  | AppExp '==' AppExp                  { BinOp (EqEq $1 $3) }
  | AppExp '-' AppExp                   { BinOp (Sub $1 $3) }
  | AppExp '**' AppExp                  { BinOp (Mul $1 $3) }
  | AppExp                              { $1 }

-- Application expressions (left-associative)
AppExp :: { Exp }
  : AppExp ProjExp                      { App $1 $2 }
  | AppExp '@' Typ                      { TApp $1 $3 }
  | ProjExp                             { $1 }

ProjExp :: { Exp }
  : ProjExp '.' ident                   { RProj $1 $3 }
  | AtomExp                             { $1 }

AtomExp :: { Exp }
  : num                                 { Lit (LitInt $1) }
  | bool                                { Lit (LitBool $1) }
  | string                              { Lit (LitStr $1) }
  | var                                 { Var $1 }
  | '[' RuntimeEnvList ']' '|>' AtomExp { Box $2 $5 }
  | '[' RuntimeEnvList ']'              { FEnv $2 }
  | '<' '[' RuntimeEnvList ']' '|' lam '.' Exp '>'    { Clos $3 $8 }
  | '<' '[' RuntimeEnvList ']' '|' TLam '.' Exp '>'   { TClos $3 $8 }
  | '{' ident '=' Exp '}'               { Rec $2 $4 }
  | '(' Exp ')'                         { $2 }

-- Runtime environment entries (Env: [EnvE]) - reversed for right-to-left
RuntimeEnvList :: { Env }
  : {- empty -}                         { [] }
  | RuntimeEntries                      { reverse $1 }

RuntimeEntries :: { [EnvE] }
  : RuntimeEntry                        { [$1] }
  | RuntimeEntry ',' RuntimeEntries      { $1 : $3 }

RuntimeEntry :: { EnvE }
  : tdef Typ                            { TypE $2 }
  | Exp                                 { ExpE $1 }

-- Types
Typ :: { Typ }
  : AppTyp '->' Typ             { TyArr $1 $3 }
  | AppTyp                      { $1 }

AppTyp :: { Typ }
  : '#[' Typ ']' AppTyp         { TySubstT $2 $4 }
  | '[' TyEnvList ']' '|>' Typ  { TyBoxT $2 $5 }
  | AtomTyp                     { $1 }

AtomTyp :: { Typ }
  : int_kw                      { TyLit TyInt }
  | bool_kw                     { TyLit TyBool }
  | str_kw                      { TyLit TyStr }
  | num                         { TyVar $1 }
  | forall '.' Typ              { TyAll $3 }
  | EnvKw '[' TyEnvList ']'     { TyEnvt $3 }
  | '{' ident ':' Typ '}'       { TyRcd $2 $4 }
  | '(' Typ ')'                 { $2 }

-- Type Environments (TyEnv: [TyEnvE])
EnvBracketed :: { TyEnv }
  : '[' TyEnvList ']'             { $2 }

TyEnvList :: { TyEnv }
  : {- empty -}                 { [] }
  | TyEnvEntries                { reverse $1 }

TyEnvEntries :: { [TyEnvE] }
  : TyEnvEntry                        { [$1] }
  | TyEnvEntry ',' TyEnvEntries       { $1 : $3 }

TyEnvEntry :: { TyEnvE }
  : '*'                         { Kind }
  | eq Typ                      { TypeEq $2 }
  | Typ                         { Type $1 }

{
parseError :: [Token] -> a
parseError tokens = error $ "Parse error: " ++ show tokens
}
