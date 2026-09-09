{-# LANGUAGE InstanceSigs #-}
-- | The nameless core: a transcription of the FE calculus as mechanized in Rocq
--   (FirstForall/Rocq/exists: Teq.v @typ@, ExpSyntax.v @exp@).
--
--   * Contexts are lists with the newest entry at the head. @Type A@, @Kind@ and
--     @TypeEq A@ are Rocq's @T & A@, @T &s@ and @T &= A@; @TyEnvt@ is a context used
--     as a type, @TyBoxT@ is @boxt@, @TySubstT@ is the manifest type @mani@.
--   * Environment expressions are Rocq's @unit@ / @merge e1 e2@ / @tmerge e1 A@
--     chains, so a computed environment can be extended, boxed and closed over
--     exactly as in the calculus. 'envEntries' / 'mkEnv' view a @Unit@-rooted chain
--     as a list of entries (newest first) for printing and name resolution.
--
--   Implementation-only conveniences, orthogonal to first-class environments and not
--   part of the formal development: 'Anno' (bidirectional checking), 'BinOp', lists,
--   and the @Bool@ / @String@ literals.
module CoreFE.Syntax where

type TyEnv = [TyEnvE]

data TyEnvE
  = Type Typ
  | Kind
  | TypeEq Typ
  deriving (Eq, Show)

data Typ
  = TyLit TyLit
  | TyVar Int
  | TyArr Typ Typ
  | TyAll Typ
  | TyBoxT TyEnv Typ
  | TySubstT Typ Typ
  | TyRcd String Typ
  | TyEnvt TyEnv
  | TyList Typ          -- [A]
  deriving (Eq, Show)

data TyLit
  = TyInt
  | TyBool
  | TyStr
  deriving (Eq, Show)

data Exp
  = Lit    Literal
  | Var    Int
  | Lam    Exp
  | App    Exp Exp
  | Clos   Exp Exp       -- ⟨δ | λe⟩
  | TLam   Exp
  | TApp   Exp Typ
  | TClos  Exp Exp       -- ⟨δ | Λe⟩
  | Box    Exp Exp       -- e1 ▷ e2
  | Unit                 -- ·
  | Merge  Exp Exp       -- e1, e2
  | TMerge Exp Typ       -- e, [A]
  | Rec    String Exp
  | RProj  Exp String
  | Anno   Exp Typ
  | BinOp  BinOp
  -- List primitives
  | EList  [Exp]         -- [e1, e2, e3]
  | ETake  Int Exp       -- take(n, ls)
  | ELength Exp          -- length(ls)
  deriving (Eq, Show)

data BinOp
  = Add      Exp Exp
  | Sub      Exp Exp
  | Mul      Exp Exp
  | EqEq     Exp Exp
  | LessThan Exp Exp
  deriving (Eq, Show)

data Literal
  = LitInt  Int
  | LitBool Bool
  | LitStr  String
  deriving (Eq, Show)

--------------------------------------------------------------------------------
-- Environment chains viewed as entry lists
--------------------------------------------------------------------------------

-- | One entry of an environment chain.
data Entry = EntE Exp | EntT Typ
  deriving (Eq, Show)

-- | The entries of a @Unit@-rooted chain, newest first; 'Nothing' if the chain is
--   rooted in a computed environment.
envEntries :: Exp -> Maybe [Entry]
envEntries Unit         = Just []
envEntries (Merge d e)  = (EntE e :) <$> envEntries d
envEntries (TMerge d t) = (EntT t :) <$> envEntries d
envEntries _            = Nothing

-- | Build a @Unit@-rooted chain from entries given newest first.
mkEnv :: [Entry] -> Exp
mkEnv = foldr step Unit
  where
    step (EntE e) d = Merge d e
    step (EntT t) d = TMerge d t

--------------------------------------------------------------------------------
-- Pretty printing
--------------------------------------------------------------------------------

class Pretty a where
  pretty :: a -> String

instance Pretty Typ where
  pretty :: Typ -> String
  pretty = stringOfTyp

instance Pretty TyLit where
  pretty :: TyLit -> String
  pretty TyInt  = "Int"
  pretty TyBool = "Bool"
  pretty TyStr  = "String"

instance Pretty TyEnvE where
  pretty :: TyEnvE -> String
  pretty = stringOfTyEnvE

instance Pretty Exp where
  pretty :: Exp -> String
  pretty = prettyTop

instance Pretty Literal where
  pretty :: Literal -> String
  pretty = stringOfLiteral

instance Pretty BinOp where
  pretty :: BinOp -> String
  pretty = stringOfBinOp

instance Pretty Entry where
  pretty :: Entry -> String
  pretty = stringOfEntry

prettyTop :: Exp -> String
prettyTop e
  | Just entries <- envEntries e = prettyEnvVertical 0 (reverse entries)
  | otherwise                    = stringOfExpI 0 e

indent :: Int -> String
indent n = replicate (n * 2) ' '

-- | Entries are given oldest first here.
prettyEnvVertical :: Int -> [Entry] -> String
prettyEnvVertical _ [] = "[]"
prettyEnvVertical lvl entries =
  concatMap (\e -> indent lvl ++ stringOfEntryI lvl e ++ "\n\n") entries

parensIf :: Bool -> String -> String
parensIf True  s = "(" ++ s ++ ")"
parensIf False s = s

stringOfTyp :: Typ -> String
stringOfTyp (TyLit l) = pretty l
stringOfTyp (TyVar n) = "t" ++ show n
stringOfTyp (TyArr t1 t2) =
    let s1 = parensIf (typPrec t1 <= typPrec (TyArr t1 t2)) (stringOfTyp t1)
        s2 = stringOfTyp t2
     in s1 ++ " → " ++ s2
stringOfTyp (TyAll t) =
    "∀. " ++ stringOfTyp t
stringOfTyp (TyBoxT bs t) =
    let sBinds = showTyEnv bs
        sTyp = parensIf (typPrec t < typPrec (TyBoxT bs t)) (stringOfTyp t)
     in "[" ++ sBinds ++ "] ▷ " ++ sTyp
stringOfTyp (TySubstT t1 t2) =
    let s1 = stringOfTyp t1
        s2 = parensIf (typPrec t2 < typPrec (TySubstT t1 t2)) (stringOfTyp t2)
     in "#[" ++ s1 ++ "] " ++ s2
stringOfTyp (TyEnvt bs) = "Env[" ++ showTyEnv bs ++ "]"
stringOfTyp (TyRcd label t) = "{" ++ label ++ " : " ++ stringOfTyp t ++ "}"
stringOfTyp (TyList t) = "[" ++ stringOfTyp t ++ "]"

typPrec :: Typ -> Int
typPrec (TyLit _)      = 10
typPrec (TyVar _)      = 10
typPrec (TyRcd _ _)    = 10
typPrec (TyEnvt _)     = 10
typPrec (TyList _)     = 10
typPrec (TySubstT _ _) = 8
typPrec (TyBoxT _ _)   = 8
typPrec (TyArr _ _)    = 4
typPrec (TyAll _)      = 2

stringOfTyEnvE :: TyEnvE -> String
stringOfTyEnvE (Type t)   = stringOfTyp t
stringOfTyEnvE Kind       = "★"
stringOfTyEnvE (TypeEq t) = "≡ " ++ stringOfTyp t

showTyEnv :: TyEnv -> String
showTyEnv = stringOfList stringOfTyEnvE . reverse

stringOfEntry :: Entry -> String
stringOfEntry = stringOfEntryI 0

stringOfEntryI :: Int -> Entry -> String
stringOfEntryI lvl (EntE e) = stringOfEnvExpI lvl e
stringOfEntryI _   (EntT t) = "type " ++ stringOfTyp t

stringOfEnvExpI :: Int -> Exp -> String
stringOfEnvExpI lvl (Rec label e) =
    label ++ " = " ++ stringOfExpI lvl e
stringOfEnvExpI lvl (Anno (Rec label e) t) =
    label ++ " : " ++ stringOfTyp t ++ " =\n"
    ++ indent (lvl + 1) ++ stringOfExpI (lvl + 1) e
stringOfEnvExpI lvl (Anno e t) =
    stringOfExpI lvl e ++ "\n"
    ++ indent (lvl + 1) ++ ": " ++ stringOfTyp t
stringOfEnvExpI lvl e = stringOfExpI lvl e

stringOfExp :: Exp -> String
stringOfExp = stringOfExpI 0

stringOfExpI :: Int -> Exp -> String
stringOfExpI _ (Lit l) = stringOfLiteral l
stringOfExpI _ (Var n) = "x" ++ show n
stringOfExpI lvl (Lam e) =
    "λ. " ++ stringOfExpI lvl e
stringOfExpI lvl (TLam e) =
    "Λ. " ++ stringOfExpI lvl e

stringOfExpI lvl op@(Box d e) =
    let sE = parensIf (expPrec e < expPrec op) (stringOfExpI lvl e)
     in showEnvLike lvl d ++ " ▷ " ++ sE

stringOfExpI lvl op@(App e1 e2) =
    let s1 = parensIf (expPrec e1 < expPrec op) (stringOfExpI lvl e1)
        s2 = parensIf (expPrec e2 <= expPrec op) (stringOfExpI lvl e2)
     in s1 ++ " " ++ s2

stringOfExpI lvl (BinOp binOp) = stringOfBinOpI lvl binOp

stringOfExpI lvl (Clos d e) =
    "⟨" ++ showEnvLike lvl d ++ " | λ. " ++ stringOfExpI lvl e ++ "⟩"

stringOfExpI lvl (TClos d e) =
    "⟨" ++ showEnvLike lvl d ++ " | Λ. " ++ stringOfExpI lvl e ++ "⟩"

stringOfExpI lvl op@(TApp e t) =
    let sE = parensIf (expPrec e < expPrec op) (stringOfExpI lvl e)
     in sE ++ " @" ++ stringOfTyp t

stringOfExpI _ Unit = "[]"
stringOfExpI lvl e@(Merge _ _)  = stringOfEnvChain lvl e
stringOfExpI lvl e@(TMerge _ _) = stringOfEnvChain lvl e

stringOfExpI _ (Rec label e) =
    "{" ++ label ++ " = " ++ stringOfExp e ++ "}"

stringOfExpI lvl op@(RProj e label) =
    let sE = parensIf (expPrec e < expPrec op) (stringOfExpI lvl e)
     in sE ++ "." ++ label

stringOfExpI lvl op@(Anno e t) =
    let sE = parensIf (expPrec e < expPrec op) (stringOfExpI lvl e)
     in sE ++ " : " ++ stringOfTyp t

-- List expressions
stringOfExpI _lvl (EList [])  = "List[]"
stringOfExpI lvl (EList es)   = "List[" ++ stringOfList (stringOfExpI lvl) es ++ "]"
stringOfExpI lvl (ETake n ls) =
    "take(" ++ show n ++ ", " ++ stringOfExpI lvl ls ++ ")"
stringOfExpI lvl (ELength ls) =
    "length(" ++ stringOfExpI lvl ls ++ ")"

-- | A chain of environment entries. A @Unit@-rooted chain prints as a bracketed
--   list; a chain over a computed environment prints with the calculus' comma.
stringOfEnvChain :: Int -> Exp -> String
stringOfEnvChain lvl e =
  case envEntries e of
    Just entries
      | isSmallEnv entries -> "[" ++ stringOfList stringOfEntry (reverse entries) ++ "]"
      | otherwise ->
          "[\n" ++ prettyEnvVertical (lvl + 1) (reverse entries) ++ indent lvl ++ "]"
    Nothing ->
      case e of
        Merge d x  -> stringOfExpI lvl d ++ " ,, " ++ stringOfExpI lvl x
        TMerge d t -> stringOfExpI lvl d ++ " ,, type " ++ stringOfTyp t
        _          -> stringOfExpI lvl e

-- | The environment of a box or closure: inline brackets when literal.
showEnvLike :: Int -> Exp -> String
showEnvLike lvl d =
  case envEntries d of
    Just entries -> "[" ++ stringOfList stringOfEntry (reverse entries) ++ "]"
    Nothing      -> parensIf True (stringOfExpI lvl d)

-- Heuristic: an env is "small" if it has <= 2 entries and no nested environment
isSmallEnv :: [Entry] -> Bool
isSmallEnv entries =
    length entries <= 2 && all isSimpleEntry entries

isSimpleEntry :: Entry -> Bool
isSimpleEntry (EntE e) = isSimpleExp e
isSimpleEntry (EntT _) = True

isSimpleExp :: Exp -> Bool
isSimpleExp (Lit _)     = True
isSimpleExp (Var _)     = True
isSimpleExp Unit        = True
isSimpleExp (Rec _ e)   = isSimpleExp e
isSimpleExp (RProj e _) = isSimpleExp e
isSimpleExp (EList es)  = length es <= 3 && all isSimpleExp es
isSimpleExp _           = False

-- | Inline rendering of a literal environment's entries (newest first, as stored).
showEnvInline :: Exp -> String
showEnvInline = showEnvLike 0

stringOfBinOp :: BinOp -> String
stringOfBinOp = stringOfBinOpI 0

stringOfBinOpI :: Int -> BinOp -> String
stringOfBinOpI lvl op@(Add e1 e2) =
    let s1 = parensIf (expPrec e1 < binOpPrec op) (stringOfExpI lvl e1)
        s2 = parensIf (expPrec e2 <= binOpPrec op) (stringOfExpI lvl e2)
     in s1 ++ " + " ++ s2
stringOfBinOpI lvl op@(Sub e1 e2) =
    let s1 = parensIf (expPrec e1 < binOpPrec op) (stringOfExpI lvl e1)
        s2 = parensIf (expPrec e2 <= binOpPrec op) (stringOfExpI lvl e2)
     in s1 ++ " - " ++ s2
stringOfBinOpI lvl op@(Mul e1 e2) =
    let s1 = parensIf (expPrec e1 < binOpPrec op) (stringOfExpI lvl e1)
        s2 = parensIf (expPrec e2 <= binOpPrec op) (stringOfExpI lvl e2)
     in s1 ++ " * " ++ s2
stringOfBinOpI lvl op@(EqEq e1 e2) =
    let s1 = parensIf (expPrec e1 < binOpPrec op) (stringOfExpI lvl e1)
        s2 = parensIf (expPrec e2 <= binOpPrec op) (stringOfExpI lvl e2)
     in s1 ++ " == " ++ s2
stringOfBinOpI lvl op@(LessThan e1 e2) =
    let s1 = parensIf (expPrec e1 < binOpPrec op) (stringOfExpI lvl e1)
        s2 = parensIf (expPrec e2 <= binOpPrec op) (stringOfExpI lvl e2)
     in s1 ++ " < " ++ s2

stringOfLiteral :: Literal -> String
stringOfLiteral (LitInt n)  = show n
stringOfLiteral (LitBool b) = if b then "true" else "false"
stringOfLiteral (LitStr s)  = "\"" ++ s ++ "\""

expPrec :: Exp -> Int
expPrec (Lit _)      = 10
expPrec (Var _)      = 10
expPrec Unit         = 10
expPrec (Merge _ _)  = 10
expPrec (TMerge _ _) = 10
expPrec (Rec _ _)    = 10
expPrec (EList _)    = 10
expPrec (ETake _ _)  = 10
expPrec (ELength _)  = 10
expPrec (RProj _ _)  = 9
expPrec (App _ _)    = 8
expPrec (TApp _ _)   = 8
expPrec (BinOp _)    = 6
expPrec (Anno _ _)   = 4
expPrec (Box _ _)    = 3
expPrec (Clos _ _)   = 3
expPrec (TClos _ _)  = 3
expPrec (Lam _)      = 1
expPrec (TLam _)     = 1

binOpPrec :: BinOp -> Int
binOpPrec (Mul _ _)  = 7
binOpPrec (Add _ _)  = 6
binOpPrec (Sub _ _)  = 6
binOpPrec (EqEq _ _) = 5
binOpPrec (LessThan _ _) = 5

stringOfList :: (a -> String) -> [a] -> String
stringOfList _ [] = ""
stringOfList f [x] = f x
stringOfList f (x:xs) = f x ++ ", " ++ stringOfList f xs

stringOfMaybeTyp :: Maybe Typ -> String
stringOfMaybeTyp Nothing = "None"
stringOfMaybeTyp (Just t) = stringOfTyp t

stringOfMaybeExp :: Maybe Exp -> String
stringOfMaybeExp Nothing = "None"
stringOfMaybeExp (Just e) = stringOfExp e
