{
{-# OPTIONS_GHC -Werror=non-exhaustive-patterns #-}
module ENVCAP.Parser.Implementation.ParseImp where
import Data.Char
import ENVCAP.Syntax 
}

%name implementationParser
%tokentype          { Token        }
%error              { parseError   }

%token
     int            { TokenInt $$       }
     var            { TokenVar $$       }
     '@pure'        { TokenPure         }
     '@resource'    { TokenResource     }
     'interface'    { TokenInterface    }
     'open'         { TokenOpen         }
     'import'       { TokenImport       }
     'require'      { TokenRequire      }
     'unit'         { TokenUnit         }
     'Sig'          { TokenSig          }  
     'Unit'         { TokenTyUnit       }        
     'Int'          { TokenTypeInt      }
     'Bool'         { TokenTypeBool     }
     'String'       { TokenTypeString   }
     '->'           { TokenTypeArrow    }
     'False'        { TokenFalse        }
     'True'         { TokenTrue         }
     'if'           { TokenIf           }
     'type'         { TokenTyAlias      }
     'then'         { TokenThen         }
     'else'         { TokenElse         }
     'val'          { TokenValDef       }
     'let'          { TokenLet          }
     'letrec'       { TokenLetrec       }
     'in'           { TokenIn           }
     'function'     { TokenFunc         }
     'struct'       { TokenStruct       }
     'module'       { TokenModule       }
     'functor'      { TokenFunctor      }
     'with'         { TokenBox          }
     'as'           { TokenAs           }
     'match'        { TokenMatch        }
     'case'         { TokenCase         }
     'of'           { TokenMatchOf      }
     '['            { TokenOpenSqBracket  }
     ']'            { TokenCloseSqBracket }
     '::'           { TokenCons         }
     ','            { TokenComma        }
     '+'            { TokenPlus         }
     '-'            { TokenMinus        }
     '*'            { TokenTimes        }
     '/'            { TokenDiv          }
     '%'            { TokenMod          }
     '('            { TokenOB           }
     ')'            { TokenCB           }
     'env'          { TokenQuery        }
     '.'            { TokenProjection   }
     '>='           { TokenGe           }
     '>'            { TokenGt           }
     '=='           { TokenEql          }
     '!='           { TokenNeq          }
     '<'            { TokenLt           }
     '<='           { TokenLe           }
     '&&'           { TokenAnd          }
     '||'           { TokenOr           }
     '|'            { TokenUnion        }
     ';'            { TokenSemicolon    }
     ':'            { TokenColon        }
     '='            { TokenEq           }
     '{'            { TokenOpenBracket  }
     '\''           { TokenSingleQuote  }
     '"'            { TokenDoubleQuote  }
     '}'            { TokenCloseBracket }
     '\\('          { TokenLambda       }
     '=>'           { TokenArrow        }
     ',,'           { TokenDepMerge }


%right '=' '=>'
%right 'if'
%left '.' proj
%left TokenElse
%left application_prec
%left '->'
%left '||'
%left '&&'
%left '>=' '>' '==' '!=' '<' '<='
%left '|'
%left '+' '-'
%left '*' '/' '%'
%left '++'
%nonassoc 'then'
%nonassoc 'else'

%%

Program             :    Fragment                                               { $1 }

Fragment            :    'module' var Statements                                { ($2, Pure,      [], [], $3) }
                    |    '@pure'     'module' var Import Required Statements    { ($3, Pure,      $4, $5, $6) }
                    |    '@resource' 'module' var Import Required Statements    { ($3, Resource,  $4, $5, $6) }

Import              :                                                 { [] }
                    |    'import' FileNames ';'                       { $2 }

FileNames           :    var FileNames                                { $1 : $2 }
                    |    var                                          { [$1] }

Required            :                                                 { [] }
                    |    'require' var                  ';'           { [Req $2 $2] }
                    |    'require' '(' Requirements ')' ';'           { $3 }

Requirements        :    Requirement                                  { [$1]  }
                    |    Requirement ',' Requirements                 { $1 : $3 }

Requirement         :    var                                          { Req      $1 $1 }

Statements          : Statements ';' Statement          { SMrg $1 $3 }
                    | Statement                         { $1 }

Statement           : Function                          { $1 }
                    | Module                            { $1 }
                    | Binding                           { $1 }
                    | TyAlias                           { $1 }
                    | Term                              { $1 }

Open                : 'open' Term                       { SOpen $2 }

Term                : BaseTerm                          { $1 }
                    | ConstructedTerm                   { $1 }
                    | List                              { $1 }
                    | Parens                            { $1 }
                    | error                             { parseError [$1] }

BaseTerm            : 'env'                             { SCtx }
                    | 'unit'                            { SUnit }
                    | FunctionApplication               { $1 }
                    | Bool                              { $1 }
                    | String                            { $1 } 
                    | int                               { SLit $1 }
                    | var                               { SVar $1 } -- Parsed into a general variable that will later get separated into

ConstructedTerm     : Projection            %prec proj  { $1 }
                    | ArithmeticOp                      { $1 }
                    | ComparisonOp                      { $1 }
                    | BooleanOp                         { $1 }
                    | IfThenElse                        { $1 }
                    | Lambda                            { $1 }
                    | Struct                            { $1 }
                    | Match                             { $1 }
                    | Tagging                           { $1 }
                    | Let                               { $1 }
                    | Letrec                            { $1 }
                    | Record                            { $1 }
                    | Tuple                             { $1 }
                    | DependentMerge                    { $1 }
                    | Box                               { $1 }

Tagging             : ADTInstance 'as' Type             { SADTInst $1 $3 }

ADTInstance         : var                               { ($1, [SUnit]) }
                    | '{' var Terms '}'                 { ($2, $3) }

Terms               : BaseTerm                Terms     { $1 : $2 }
                    | '(' ConstructedTerm ')' Terms     { $2 : $4 }
                    | BaseTerm                          { [$1] }
                    | '(' ConstructedTerm ')'           { [$2] }

Match               : 'match' Term 'of' Cases               { SCase $2 $4 }

Cases               :  Case    Cases                        { $1 : $2 }
                    |  Case                                 { [$1] }

Case                : 'case' Pattern '=>' '{' Term '}'      { ($2, $5) }

Pattern             :  '[' ']'                              { ("", []) }
                    |  '(' var ':' var ')'                  { ("", [$2, $4]) }                         
                    |  var                                  { ($1, []) }
                    |  '(' var Identifiers ')'              { ($2, $3) }

Identifiers         : var Identifiers                       { $1 : $2 }
                    | var                                   { [$1] }

Box                 : 'with' Term 'in' '{' Statements '}'    { SBox (SMrg SUnit $2) $5 }

Type                : BaseType                               { $1 }
                    | ADT                                    { $1 }
                    | Type '->' Type                         { STArrow $1 $3 }
                    | '[' Type ']'                           { STList $2 }
                    | '{' RecordType '}'                     { $2 }
                    | '(' IntersectionType ')'               { $2 }
                    | Signature                              { $1 }
                    | var                                    { STIden $1 }
                    | '(' Type ')'                           { $2 }

BaseType            : 'Unit'                                { STUnit } 
                    | 'Int'                                 { STInt }
                    | 'Bool'                                { STBool }
                    | 'String'                              { STString } 

ADT                 : Constructor '|' Constructor           { STUnion $1 $3 }
                    | ADT         '|' Constructor           { STUnion $1 $3 } 

Constructor         : var                                   { STRecord $1 STUnit }
                    | var BaseType                          { STRecord $1 $2 }
                    | var '(' Type ')'                      { STRecord $1 $3 }
                    | var ProductTypes                      { STRecord $1 $2 }

ProductTypes        : ProductTypes BaseType                 { STAnd $1 $2 }
                    | ProductTypes '(' Type ')'             { STAnd $1 $3 }
                    | '(' Type ')' BaseType                 { STAnd $2 $4 }
                    | BaseType '(' Type ')'                 { STAnd $1 $3 }
                    | '(' Type ')' '(' Type ')'             { STAnd $2 $5 }
                    | BaseType     BaseType                 { STAnd $1 $2 }

IntersectionType    : IntersectionType ',' Type             {  STAnd $1 $3  }
                    | Type ',' Type                         {  STAnd $1 $3  }

Projection               : Term '.' int                          {  SProj  $1 $3  }
                         | Term '.' var                          {  SRProj $1 $3  }

Module                   : 'functor' var '(' ParamList ')' ':' Type '{' Statements '}'   { (SModule $2 $4 $9) }    -- { SAnno  $7 }
                         | 'module' var ':' Type '{' Statements '}'                      { (SRec $2 $6) }          -- { SAnno  $4 }

Struct                   : 'module' 'struct' '{' Statements '}'                      { $4 }
                         | 'module' 'struct' '(' ParamList ')' '{' Statements '}'    { SStruct $4 $7 }
                         | 'struct' '{' Statements '}'                               { $3 }  
                         | 'struct' '(' ParamList ')' '{' Statements '}'             { SStruct $3 $6 }

Signature                : 'Sig' '[' Type ',' Type ']'                               { STSig $3 $5 }

Function                 : 'function' var '(' ParamList ')' ':' Type '=' Term        { SFunc $2 $4 $7 $9 }
                         | 'function' var '(' ParamList ')' ':' Type '{' Term '}'    { SFunc $2 $4 $7 $9 }

FunctionApplication      : var '(' Arguments ')'  %prec application_prec             { SApp (SVar $1) $3 }

Binding                  : 'let' var '=' Term                                        { SRec $2 $4 }
                         | 'val' var '=' Term                                        { SRec $2 $4 }

Lambda                   : '(' Lambda ')' '(' Arguments ')'  %prec application_prec              { SApp $2 $5 }
                         | '\\(' ParamList ')' '=>' '{' Statements '}'               { SLam $2 $6 }
                         | '\\(' ParamList ')' '=>' Term                             { SLam $2 $5 }

Bool                     : 'False'           { SBool False }
                         | 'True'            { SBool True }

String                   : '\'' var '\''                              { SString $2 }
                         | '"' var '"'                                { SString $2 }

List                     : '[' ']' '<' Type '>'                            { SList [] $4 }
                         | '[' Elements ']' '<' Type '>'                   { SList   $2 $5 }

Elements                 : Term ',' Elements                          { [$1] ++ $3 }
                         | Term                                       { [$1] }

TyAlias                  : 'type' var '=' Type                        { SAliasTyp $2 $4 }

DependentMerge           : '(' DependentMergeElements ')'             { $2 }

DependentMergeElements   : DependentMergeElements ';' Term       { SMrg $1 $3 }
                         | Term ';' Term                         { SMrg $1 $3 }

Tuple                    : '(' TupleElements ')'                 { STuple $2 }

TupleElements            : Term ',' TupleElements                     { $1 : $3 }
                         | Term ',' Term                              { $1 : [$3] }

RecordType               : Param ',' RecordType                       { STAnd $1 $3 }
                         | Param                                      { $1 }

Param                    : var ':' Type                               { STRecord $1 $3 }   

Record                   : '{' Records '}'                            { $2 }

Records                  : '"' var '"' '=' Term ',' Records           { SMrg (SRec $2 $5) $7 }
                         | '"' var '"' '=' Term                       { SRec $2 $5 }
                         | '\'' var '\'' '=' Term ',' Records         { SMrg (SRec $2 $5) $7 }
                         | '\'' var '\'' '=' Term                     { SRec $2 $5 }
                         | var '=' Term ',' Records                   { SMrg (SRec $1 $3) $5 }
                         | var '=' Term                               { SRec $1 $3 }

ParamList                : ParamL ',' ParamList                       { $1 : $3 }
                         | ParamL                                     { [$1] }

ParamL                   : var ':' Type                               { ($1, $3) } 

Let                      : 'let'    '{' bindings '}' 'in' '{' Term '}'   { SLet    $3 $7 }
Letrec                   : 'letrec' '{' bindings '}' 'in' '{' Term '}'   { SLetrec $3 $7 }

bindings                 : binding ';' bindings                       { $1 : $3 }
                         | binding                                    { [$1] }

binding                  : var ':' Type '=' Term                      { ($1, $3, $5) }

Arguments                : Term ',' Arguments                         { $1 : $3 }
                         | Term                                       { [$1] }

Parens                   : '(' Term ')'                               { $2 }

CurlyParens              : '{' Statements '}'                         { $2 }

IfThenElse               : 'if' Parens 'then' Term 'else' Term               { SIf $2 $4 $6 }
                         | 'if' Parens 'then' CurlyParens 'else' CurlyParens { SIf $2 $4 $6 }
                         
ComparisonOp             :  Term    '>='    Term                      { SBinOp (Comp  Ge)   $1 $3 }
                         |  Term    '>'     Term                      { SBinOp (Comp  Gt)   $1 $3 }
                         |  Term    '=='    Term                      { SBinOp (Comp  Eql)  $1 $3 }
                         |  Term    '!='    Term                      { SBinOp (Comp  Neq)  $1 $3 }
                         |  Term    '<'     Term                      { SBinOp (Comp  Lt)   $1 $3 }
                         |  Term    '<='    Term                      { SBinOp (Comp  Le)   $1 $3 }

BooleanOp                : Term    '&&'    Term                       { SBinOp (Logic And)  $1 $3 }
                         | Term    '||'    Term                       { SBinOp (Logic Or)   $1 $3 }
          
ArithmeticOp             :    Term    '+'     Term                    { SBinOp (Arith Add)  $1 $3 }
                         |    Term    '-'     Term                    { SBinOp (Arith Sub)  $1 $3 }
                         |    Term    '*'     Term                    { SBinOp (Arith Mul)  $1 $3 }
                         |    Term    '/'     Term                    { SBinOp (Arith Div)  $1 $3 }
                         |    Term    '%'     Term                    { SBinOp (Arith Mod)  $1 $3 }

{

parseError :: [Token] -> a
parseError (x:xs)   = error ("Parse Error: Token Failed" ++ show x)
parseError []       = error ("Parser Error: No Tokens")

data Token =   TokenInt Integer       -- Lit i
          |    TokenVar String        -- x
          |    TokenLambda            -- '\'
          |    TokenArrow             -- = >
          |    TokenPlus              -- '+'
          |    TokenMinus             -- '-'
          |    TokenTimes             -- '*'
          |    TokenDiv               -- '/'
          |    TokenMod               -- '%'
          |    TokenEql               -- '=='
          |    TokenNeq               -- '!='
          |    TokenGe                -- '>='
          |    TokenGt                -- '>'
          |    TokenLe                -- '<='
          |    TokenLt                -- '<'
          |    TokenAnd               -- '&&'
          |    TokenOr                -- '||'
          |    TokenOB                -- '('
          |    TokenCB                -- ')'
          |    TokenQuery             -- 'env()'
          |    TokenEq                -- '='
          |    TokenSemicolon         -- ';'
          |    TokenIf                -- 'if'
          |    TokenThen              -- 'then'
          |    TokenElse              -- 'else'
          |    TokenValDef            -- 'val'
          |    TokenTrue              -- 'True'
          |    TokenFalse             -- 'False'
          |    TokenFunc              -- 'function'
          |    TokenModule            -- 'module'
          |    TokenFunctor           -- 'functor'
          |    TokenStruct            -- 'struct'
          |    TokenOpenBracket       -- '{'
          |    TokenCloseBracket      -- '}'
          |    TokenColon             -- ':'
          |    TokenLet               -- 'let'
          |    TokenLetrec            -- 'letrec'
          |    TokenIn                -- 'in'
          |    TokenSig               -- 'Sig'
          |    TokenTypeInt           -- 'Int'
          |    TokenTypeBool          -- 'Bool'
          |    TokenTypeString        -- 'String'
          |    TokenTypeArrow         -- '->'
          |    TokenTyAlias           -- 'type'
          |    TokenComma             -- ','
          |    TokenCons              -- '::'
          |    TokenSingleQuote       -- '
          |    TokenDoubleQuote       -- "
          |    TokenDepMerge          -- ,,
          |    TokenProjection        -- 'term.x'
          |    TokenBox               -- "with"
          |    TokenUnit              -- 'unit'
          |    TokenTyUnit            -- 'Unit'
          |    TokenMatch             -- 'match'
          |    TokenCase              -- 'case'
          |    TokenMatchOf           -- 'of'
          |    TokenAs                -- 'as'
          |    TokenUnion             -- '|'
          |    TokenSpace             -- whitespace
          |    TokenPure              -- '@pure'
          |    TokenResource          -- '@resource'
          |    TokenImport            -- 'import'
          |    TokenRequire           -- 'require'
          |    TokenInterface         -- 'interface'
          |    TokenOpen              -- 'open'
          |    TokenOpenSqBracket     -- '['
          |    TokenCloseSqBracket      -- ']'
          deriving Show

lexer :: String -> [Token]
lexer [] = []
lexer (c:cs)
     | isSpace c = lexer cs
     | isAlpha c = lexVar (c:cs)
     | isDigit c = lexNum (c:cs)
lexer ('+':cs)      =    TokenPlus     : lexer cs
lexer ('-':cs)      = 
     case cs of
          ('>':cs')      -> TokenTypeArrow   : lexer cs'
          _              -> TokenMinus       : lexer cs
lexer ('*':cs)      = TokenTimes             : lexer cs
lexer ('/':cs)      = TokenDiv               : lexer cs
lexer ('%':cs)      = TokenMod               : lexer cs 
lexer ('\\':cs)     = case cs of 
                         ('(':cs') -> TokenLambda   : lexer cs' 
lexer ('=':cs)      = case cs of
                         ('>':cs') -> TokenArrow  : lexer cs'
                         ('=':cs') -> TokenEql    : lexer cs'
                         _         -> TokenEq     : lexer cs
lexer ('!':cs)      = case cs of
                         ('=':cs') -> TokenNeq : lexer cs'
lexer ('&':cs)      = case cs of
                         ('&':cs') -> TokenAnd         : lexer cs'
lexer ('|':cs)      = case cs of
                         ('|':cs') -> TokenOr     : lexer cs'
                         _         -> TokenUnion  : lexer cs
lexer ('>':cs)      = case cs of
                         ('=':cs') -> TokenGe  : lexer cs'
                         _         -> TokenGt  : lexer cs
lexer ('<':cs)      = case cs of
                         ('=':cs') -> TokenLe  : lexer cs'
                         _         -> TokenLt  : lexer cs
lexer (';':cs)      = TokenSemicolon : lexer cs
lexer (',':cs)      = case cs of
                         (',':cs')  -> TokenDepMerge : lexer cs'
                         _          -> TokenComma : lexer cs
lexer (':':cs)      = case cs of 
                         (':':cs')      ->   TokenCons      : lexer cs'
                         _              ->   TokenColon     : lexer cs 
lexer ('{':cs)      = TokenOpenBracket       : lexer cs
lexer ('}':cs)      = TokenCloseBracket      : lexer cs
lexer ('[':cs)      = TokenOpenSqBracket     : lexer cs
lexer (']':cs)      = TokenCloseSqBracket    : lexer cs
lexer ('(':cs)      = TokenOB                : lexer cs
lexer (')':cs)      = TokenCB                : lexer cs
lexer ('\'':cs)     = TokenSingleQuote       : lexer cs
lexer ('"':cs)      = TokenDoubleQuote       : lexer cs
lexer ('.':cs)      = TokenProjection        : lexer cs
lexer ('@':cs)      = case span isAlpha cs of
                         ("resource",   rest)     -> TokenResource : lexer rest
                         ("pure",       rest)     -> TokenPure     : lexer rest

lexNum cs = TokenInt (read num) : lexer rest
                    where (num, rest) = span isDigit cs
lexVar cs = case span isAlpha cs of
               ("import",     rest)     -> TokenImport      : lexer rest
               ("require",    rest)     -> TokenRequire     : lexer rest
               ("interface",  rest)     -> TokenInterface   : lexer rest
               ("open",       rest)     -> TokenOpen        : lexer rest
               ("Int",        rest)     -> TokenTypeInt     : lexer rest
               ("Bool",       rest)     -> TokenTypeBool    : lexer rest
               ("String",     rest)     -> TokenTypeString  : lexer rest
               ("unit",       rest)     -> TokenUnit        : lexer rest
               ("Sig",        rest)     -> TokenSig         : lexer rest
               ("Unit",       rest)     -> TokenTyUnit      : lexer rest
               ("with",       rest)     -> TokenBox         : lexer rest
               ("match",      rest)     -> TokenMatch       : lexer rest
               ("of",         rest)     -> TokenMatchOf     : lexer rest
               ("case",       rest)     -> TokenCase        : lexer rest         
               ("True",       rest)     -> TokenTrue        : lexer rest
               ("env",        rest)     -> TokenQuery       : lexer rest
               ("False",      rest)     -> TokenFalse       : lexer rest
               ("let",        rest)     -> TokenLet         : lexer rest
               ("letrec",     rest)     -> TokenLetrec      : lexer rest
               ("in",         rest)     -> TokenIn          : lexer rest
               ("type",       rest)     -> TokenTyAlias     : lexer rest
               ("function",   rest)     -> TokenFunc        : lexer rest
               ("module",     rest)     -> TokenModule      : lexer rest
               ("functor",    rest)     -> TokenFunctor     : lexer rest
               ("struct",     rest)     -> TokenStruct      : lexer rest
               ("val",        rest)     -> TokenValDef      : lexer rest
               ("if",         rest)     -> TokenIf          : lexer rest
               ("then",       rest)     -> TokenThen        : lexer rest
               ("else",       rest)     -> TokenElse        : lexer rest
               ("as",         rest)     -> TokenAs          : lexer rest
               (var,          rest)     -> TokenVar var     : lexer rest

parseImplementation :: String -> Maybe ParseImplData
parseImplementation input = case implementationParser (lexer input) of
                                   result -> Just result
                                   _      -> Nothing                    

test_cases :: [(String, SurfaceTm)]
test_cases = [  ("env", SCtx)
              , ("1 + 2", SBinOp (Arith Add) (SLit 1) (SLit 2))
              , ("1 - 2", SBinOp (Arith Sub) (SLit 1) (SLit 2))
              , ("3 * 4", SBinOp (Arith Mul) (SLit 3) (SLit 4))
              , ("10 / 2", SBinOp (Arith Div) (SLit 10) (SLit 2))
              , ("5 % 2", SBinOp (Arith Mod) (SLit 5) (SLit 2))
              , ("1 < 2", SBinOp (Comp Lt) (SLit 1) (SLit 2))
              , ("2 <= 3", SBinOp (Comp Le) (SLit 2) (SLit 3))
              , ("3 > 2", SBinOp (Comp Gt) (SLit 3) (SLit 2))
              , ("4 >= 1", SBinOp (Comp Ge) (SLit 4) (SLit 1))
              , ("1 == 1", SBinOp (Comp Eql) (SLit 1) (SLit 1))
              , ("2 != 3", SBinOp (Comp Neq) (SLit 2) (SLit 3))
              , ("a + b * c", SBinOp (Arith Add) (SVar "a") (SBinOp (Arith Mul) (SVar "b") (SVar "c")))
              , ("1 + 2 * c", SBinOp (Arith Add) (SLit 1) (SBinOp (Arith Mul) (SLit 2) (SVar "c")))
              , ("((3 + 4) * 2) - (5 / 2) >= (1 + x)", SBinOp   (Comp Ge)
                                                            (SBinOp (Arith Sub)
                                                                 (SBinOp (Arith Mul)
                                                                      (SBinOp (Arith Add) (SLit 3) (SLit 4))
                                                                      (SLit 2))
                                                                 (SBinOp (Arith Div) (SLit 5) (SLit 2)))
                                                            (SBinOp (Arith Add) (SLit 1) (SVar "x")))
              , ("(x * 2) + (y / 4) >= 3", SBinOp (Comp Ge)
                                             (SBinOp (Arith Add)
                                                  (SBinOp (Arith Mul) (SVar "x") (SLit 2))
                                                  (SBinOp (Arith Div) (SVar "y") (SLit 4)))
                                             (SLit 3))
              ,  ("1 ; (x * 2) + (y / 4) >= 3", SMrg (SLit 1) (SBinOp (Comp Ge)
                                                                 (SBinOp (Arith Add)
                                                                      (SBinOp (Arith Mul) (SVar "x") (SLit 2))
                                                                      (SBinOp (Arith Div) (SVar "y") (SLit 4)))
                                                                 (SLit 3)))
               , ("(1 , 2, 3)", STuple [SLit 1,SLit 2,SLit 3])
               , ("(1 ,, 2,, 4)", SMrg (SMrg (SLit 1) (SLit 2)) (SLit 4))
               , ("env.1", SProj SCtx 1)
               , ("env.hello", SRProj SCtx "hello")
               , ("({\"x\" = 10})", SRec "x" (SLit 10))
               , ("({\"x\" = 10} ,, env.x)", (SMrg (SRec "x" (SLit 10)) (SRProj SCtx "x")))]

runTest :: Int -> [(String, SurfaceTm)] -> IO()
runTest n []        = putStrLn $ (show (n + 1) ++ " Tests Completed.")
runTest n (x:xs)    = do
                         case parseImplementation (fst x) of
                              Just (_, _, _, _, tm)  -> 
                                   if tm == (snd x) 
                                        then putStrLn $ "Test " ++ (show (n + 1)) ++ ": Passed"
                                        else putStrLn $ "Test " ++ (show (n + 1)) ++ ": Failed: " ++ (show tm)
                              Nothing             -> putStrLn $ "Test " ++ (show (n + 1)) ++ ": Failed (Failed to Parse)"
                         runTest (n + 1) xs

test :: IO()
test = runTest 0 test_cases

}