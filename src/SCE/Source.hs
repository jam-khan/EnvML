module SCE.Source where

-- Note: Context is a Type and Environment is an Expression
type Ctx      = Typ 
type Env      = Exp
type Name     = String
type Result a = Either String a

data Typ
  = Int
  | Unit
  | TyAnd Typ Typ
  | TyArr Typ Typ
  | TyRcd Name Typ
  | TyStruct SigTyp
  deriving (Eq, Show)

data SigTyp
  = TySig  Typ SigTyp
  | TyIntf [TyDecl]
  deriving (Eq, Show)

data TyDecl
  = TyVal   Name Typ
  | TyMod   Name SigTyp
  | TyFunct Name SigTyp SigTyp
  deriving (Eq, Show)
 
data Exp
  = Query
  | Proj Exp Int
  | Lit  Int
  | UnitE
  | Lam Typ Exp
  | Box Exp Exp
  | Clos Exp Typ Exp
  | App Exp Exp
  | Mrg Exp Exp
  | Rec Name Exp
  | RProj Exp Name
  -- To be elaborated
  | Mod Module
  deriving (Eq, Show)

-- To be elaborated
data Module
  = MVar     Name            -- M ~~> ?.M
  | MStruct  [Decl]          -- struct decl1; ...; declN end
  | MFunctor Name Typ Module -- functor (x : A) m end
  | MLink    Module Module   -- Link(M1, M2)
  deriving (Eq, Show)

data Sandbox = Sandboxed | Open
  deriving (Eq, Show)

data Decl
  = DLet   Sandbox Name (Maybe Typ) Exp
  | DMod   Sandbox Name (Maybe SigTyp) Module
  | DFunct Sandbox Name SigTyp (Maybe SigTyp) Module
  deriving (Eq, Show)

-- lookupv for runtime values (de Bruijn)
lookupV :: Env -> Int -> Result Exp
lookupV (Mrg _ v2) 0 = pure v2
lookupV (Mrg v1 _) n = lookupV v1 (n - 1)
lookupV _ _          = Left "lookupV: index out of bounds"

bigStep :: Env -> Exp -> Result Exp
bigStep env Query       = pure env
bigStep env (Proj e' i) = do
  v <- bigStep env e'
  lookupV v i
bigStep _ (Lit i)       = pure $ Lit i
bigStep _ UnitE         = pure $ UnitE
bigStep env (Lam ty e)  = pure $ Clos env ty e
bigStep _ _ = Left "TODO: Implement"    