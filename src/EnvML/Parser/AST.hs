{-# LANGUAGE InstanceSigs #-}

module EnvML.Parser.AST where

main :: IO ()
main = print "EnvML Parsed AST"

-- AST with names and direct source-level representation

type Name     = String            -- Alias for naming
type Imports  = [(Name, Typ)]     -- import x : A

type FunArgs = [(Name, FunArg)]
data FunArg
  = TyArg
  | TmArg
  | TmArgType Typ
  deriving (Show, Eq)

type TyCtx    = [TyCtxE]  -- [t : A, t1 : Type, type t2 = A]
data TyCtxE
  = TypeN    Name Typ       -- t : A
  | Type     Typ            -- nameless A
  | KindN    Name           -- t : *
  | Kind                    -- nameless *
  | TypeEqN  Name Typ       -- type x = A !Must be named
  | TyMod    Name ModuleTyp -- module n : A
  | TypeEqM  Name ModuleTyp -- module type m = .. 
  deriving (Show, Eq)

data ModuleTyp
  = TyArrowM  Typ ModuleTyp   -- (A ->m I)
  | ForallM   Name ModuleTyp  -- ∀t. I
  | TySig     Intf            -- (sig .. end)
  deriving (Show, Eq)

type Intf = [IntfE]           -- (sig ... end) .eli
data IntfE
  = TyDef       Name Typ               -- (type t = ...)
  | ValDecl     Name Typ               -- (val x : t)
  | ModDecl     Name ModuleTyp         -- (module M : S)
  | FunctorDecl Name FunArgs ModuleTyp -- (functor m (type t) (x: A) : S)
  | SigDecl     Name Intf              -- (module type S = ...)
  deriving (Show, Eq)

data Typ
  = TyLit     TyLit           -- int, bool, or string
  | TyVar     Name            -- x
  | TyArr     Typ   Typ       -- A -> B
  | TyAll     Name  Typ       -- forall a'. T
  | TyBoxT    TyCtx Typ       -- [t1 : int, t2 : int, t3: bool] ==> A
  | TyRcd     [(Name, Typ)]   -- {l1 : A1, l2 : A2, ln : An}
  | TyCtx     TyCtx           -- [t : A, t1 : Type, t2 : A=]
  | TyModule  ModuleTyp       -- Note: First-class modules
  deriving (Show, Eq)

data TyLit
  = TyInt     -- int
  | TyBool    -- bool
  | TyStr     -- string
  deriving (Show, Eq)

type Env = [EnvE]
data EnvE
  = ExpEN   Name Exp        -- [x = e]
  | ExpE    Exp             -- [e]
  | TypEN   Name Typ        -- [type x = A]
  | TypE    Typ             -- [A]
  | ModE    Name Module     -- [module m = ...]
  | ModTypE Name ModuleTyp  -- [module type A = sig .. end]
  deriving (Show, Eq)

data Module
  = VarM    Name            -- module variable
  | Functor FunArgs Module  -- functor (x : A) ->
  | Struct  Imports Env     -- struct type a = int; x = 1 end
  | MApp    Module Module   -- M1 ^ M2
  | MAppt   Module Typ      -- M1 ^ @A
  | MLink   Module Module   -- link(M1, M2)
  deriving (Show, Eq)

data Exp
  = Lit   Literal         -- Literals: int, double, bool, string
  | Var   Name            -- Var x, y, hello
  | Lam   FunArgs Exp     -- fun (x: A) (y : B) -> x + 1
  | TLam  FunArgs Exp     -- fun 
  | Clos  Env FunArgs Exp -- clos [type t = int, x = 1] (y: t) -> x + y
  | App   Exp Exp         -- f(x)
  | TClos Env FunArgs Exp -- clos [type t = int, x = 1] ->
  | TApp  Exp Typ         -- f<t>
  | Box   Env Exp         -- box [type t = int, x = 1] in e
  | Rec   [(Name, Exp)]   -- {l1 = e1, l2 = e2, l3 = e3}
  | RProj Exp Name        -- e.l
  | FEnv  Env             -- [type a = int, x = 1]
  | Anno  Exp Typ         -- (e::A)
  | Mod   Module          -- functor or struct
  -- Extensions
  | BinOp BinOp
  deriving (Show, Eq)

data BinOp
  = Add Exp Exp
  | Sub Exp Exp
  | Mul Exp Exp
  deriving (Show, Eq)

data Literal
  = LitInt  Int     -- 1, 2, etc.
  | LitBool Bool    -- false, true
  | LitStr  String  -- "hello"
  deriving (Show, Eq)

type Precedence = Int

typPrec :: Typ -> Precedence
typPrec t = case t of
  TyLit _     -> 4
  TyVar _     -> 4
  TyRcd {}    -> 4
  TyCtx _     -> 4
  TyModule _  -> 4
  TyArr _ _   -> 2
  TyBoxT _ _  -> 1
  TyAll _ _   -> 1

expPrec :: Exp -> Precedence
expPrec e = case e of
  Anno _ _  -> 0
  Box _ _   -> 1
  Clos {}   -> 1
  TClos {}  -> 1
  Lam {}    -> 2
  App _ _   -> 3
  TApp _ _  -> 3
  RProj _ _ -> 3
  Lit _     -> 5
  Var _     -> 5
  Rec {}    -> 5
  FEnv _    -> 5
  Mod _     -> 5
  _ -> 4 -- TODO: Extensions
