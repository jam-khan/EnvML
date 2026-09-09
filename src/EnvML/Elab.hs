{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

-- | Type-directed elaboration from EnvML to CoreFE: @Γ ⊢ M ⇝ e : τ@. Signatures
--   become core types and expressions core expressions, so only module forms do
--   work: a struct or functor is sandboxed as @[] ▷ e@, and @++@ / @+@ expand
--   into projections since the core has no concatenation primitive.
module EnvML.Elab where

import qualified CoreFE.Named  as CoreFE
import qualified EnvML.Syntax  as EnvML

type ElabError = String

-- | The core typing context, kept named.
data CtxE
  = CTm  EnvML.Name CoreFE.Typ  -- ^ @x : τ@
  | CTmU EnvML.Name             -- ^ @x@ bound, type undetermined
  | CTyD EnvML.Name CoreFE.Typ  -- ^ @type t = τ@ (transparent)
  | CTyA EnvML.Name             -- ^ @t : *@ (abstract)
  deriving (Show, Eq)

type Ctx = [CtxE]

lookupTm :: Ctx -> EnvML.Name -> Maybe CoreFE.Typ
lookupTm [] _ = Nothing
lookupTm (CTm n t : rest) x = if n == x then Just t else lookupTm rest x
lookupTm (CTmU n : rest) x = if n == x then Nothing else lookupTm rest x
lookupTm (_ : rest) x = lookupTm rest x

lookupTy :: Ctx -> EnvML.Name -> Maybe CoreFE.Typ
lookupTy [] _ = Nothing
lookupTy (CTyD n t : rest) x = if n == x then Just t else lookupTy rest x
lookupTy (CTyA n : rest) x = if n == x then Nothing else lookupTy rest x
lookupTy (_ : rest) x = lookupTy rest x

-- | A labelled term component, as it appears in an environment and a signature.
termEntry :: EnvML.Name -> CoreFE.Typ -> CoreFE.TyEnvE
termEntry n t = CoreFE.Type n (CoreFE.TyRcd n t)

-- | Wrap a core term in an empty-environment box (the sandbox wrapper).
box0 :: CoreFE.Exp -> CoreFE.Exp
box0 = CoreFE.Box []

-- | @[] ▷ A ≡ A@, mirroring 'CoreFE.Check.whnf'.
unboxT :: CoreFE.Typ -> CoreFE.Typ
unboxT (CoreFE.TyBoxT [] a) = unboxT a
unboxT a                    = a

-- | Unbox and expand transparent abbreviations, so a module type written as an
--   alias still exposes its signature.
whnfT :: Ctx -> CoreFE.Typ -> CoreFE.Typ
whnfT ctx = go (100 :: Int)
  where
    go 0 t = t
    go n t = case unboxT t of
      CoreFE.TyVar x | Just t' <- lookupTy ctx x -> go (n - 1) t'
      t' -> t'

renameTyVar :: EnvML.Name -> EnvML.Name -> CoreFE.Typ -> CoreFE.Typ
renameTyVar from to = substTyp from (CoreFE.TyVar to)

-- | Substitute a type for a named type variable. A box body is scoped by the
--   box's own entries alone, and an environment entry by the entries after it
--   (see 'CoreFE.DeBruijn'), so neither is substituted into when rebound.
substTyp :: EnvML.Name -> CoreFE.Typ -> CoreFE.Typ -> CoreFE.Typ
substTyp x s = go
  where
    go t = case t of
      CoreFE.TyLit l        -> CoreFE.TyLit l
      CoreFE.TyVar y        -> if y == x then s else CoreFE.TyVar y
      CoreFE.TyArr a b      -> CoreFE.TyArr (go a) (go b)
      CoreFE.TyAll y a      -> CoreFE.TyAll y (if y == x then a else go a)
      CoreFE.TyBoxT g a     -> CoreFE.TyBoxT (goEnv g) a
      CoreFE.TySubstT y a b -> CoreFE.TySubstT y (go a) (if y == x then b else go b)
      CoreFE.TyRcd l a      -> CoreFE.TyRcd l (go a)
      CoreFE.TyEnvt g       -> CoreFE.TyEnvt (goEnv g)
      CoreFE.TyList a       -> CoreFE.TyList (go a)

    goEnv [] = []
    goEnv (e : rest)
      | x `elem` tyEnvNames rest = e     : goEnv rest
      | otherwise                = goE e : goEnv rest

    goE (CoreFE.Type   n a) = CoreFE.Type   n (go a)
    goE (CoreFE.Kind   n)   = CoreFE.Kind   n
    goE (CoreFE.TypeEq n a) = CoreFE.TypeEq n (go a)

-- | The names bound by a type environment's type entries.
tyEnvNames :: CoreFE.TyEnv -> [EnvML.Name]
tyEnvNames = concatMap f
  where
    f (CoreFE.TypeEq n _) = [n]
    f (CoreFE.Kind n)     = [n]
    f (CoreFE.Type _ _)   = []

-- | Free type names, with the same scoping as 'substTyp'.
freeTyNames :: CoreFE.Typ -> [EnvML.Name]
freeTyNames t = case t of
  CoreFE.TyLit _        -> []
  CoreFE.TyVar x        -> [x]
  CoreFE.TyArr a b      -> freeTyNames a ++ freeTyNames b
  CoreFE.TyAll y a      -> filter (/= y) (freeTyNames a)
  CoreFE.TyBoxT g _     -> freeTyNamesEnv g
  CoreFE.TySubstT y a b -> freeTyNames a ++ filter (/= y) (freeTyNames b)
  CoreFE.TyRcd _ a      -> freeTyNames a
  CoreFE.TyEnvt g       -> freeTyNamesEnv g
  CoreFE.TyList a       -> freeTyNames a

freeTyNamesEnv :: CoreFE.TyEnv -> [EnvML.Name]
freeTyNamesEnv [] = []
freeTyNamesEnv (e : rest) =
  filter (`notElem` tyEnvNames rest) (entryNames e) ++ freeTyNamesEnv rest
  where
    entryNames (CoreFE.Type _ a)   = freeTyNames a
    entryNames (CoreFE.TypeEq _ a) = freeTyNames a
    entryNames (CoreFE.Kind _)     = []

-- | Expand a type's transparent abbreviations so it mentions no ambient name,
--   for an annotation placed inside a sandbox box. An abstract ambient type (a
--   functor's type parameter) cannot be expanded, so mentioning one is an error.
closeTyp :: Ctx -> CoreFE.Typ -> Either ElabError CoreFE.Typ
closeTyp ctx = go (100 :: Int) []
  where
    go 0 _ _ = Left "cyclic type abbreviation"
    go depth bound t = case t of
      CoreFE.TyLit l -> Right (CoreFE.TyLit l)
      CoreFE.TyVar x
        | x `elem` bound -> Right (CoreFE.TyVar x)
        | Just t' <- lookupTy ctx x -> go (depth - 1) bound t'
        | otherwise -> Left $
            "the annotation of a sandboxed module mentions the type '" ++ x
              ++ "', which is not visible inside the sandbox.\n"
              ++ "  A sandboxed module sees only its own components; only a\n"
              ++ "  transparent type abbreviation can be expanded into its annotation."
      CoreFE.TyArr a b      -> CoreFE.TyArr <$> go depth bound a <*> go depth bound b
      CoreFE.TyAll y a      -> CoreFE.TyAll y <$> go depth (y : bound) a
      CoreFE.TyBoxT g a     -> (\g' -> CoreFE.TyBoxT g' a) <$> goEnv depth bound g
      CoreFE.TySubstT y a b ->
        CoreFE.TySubstT y <$> go depth bound a <*> go depth (y : bound) b
      CoreFE.TyRcd l a      -> CoreFE.TyRcd l <$> go depth bound a
      CoreFE.TyEnvt g       -> CoreFE.TyEnvt <$> goEnv depth bound g
      CoreFE.TyList a       -> CoreFE.TyList <$> go depth bound a

    goEnv _ _ [] = Right []
    goEnv depth bound (e : rest) = do
      rest' <- goEnv depth bound rest
      let bound' = tyEnvNames rest ++ bound
      e' <- case e of
              CoreFE.Type n a   -> CoreFE.Type n <$> go depth bound' a
              CoreFE.Kind n     -> Right (CoreFE.Kind n)
              CoreFE.TypeEq n a -> CoreFE.TypeEq n <$> go depth bound' a
      return (e' : rest')

-- | The labelled (projectable) components of a signature.
sigLabels :: CoreFE.TyEnv -> [String]
sigLabels = concatMap f
  where
    f (CoreFE.Type _ (CoreFE.TyRcd l _)) = [l]
    f _                                  = []

-- | The type components of a signature.
sigTyNames :: CoreFE.TyEnv -> [String]
sigTyNames = tyEnvNames

duplicates :: [String] -> [String]
duplicates = go []
  where
    go _ [] = []
    go seen (x:xs) | x `elem` seen = x : go seen xs
                   | otherwise     = go (x:seen) xs

overlap :: [String] -> [String] -> [String]
overlap xs ys = [x | x <- xs, x `elem` ys]

-- | An operand of a merge: its term, its type, and the signature driving the
--   expansion.
data Operand = Operand
  { opExp :: CoreFE.Exp
  , opTyp :: CoreFE.Typ
  , opSig :: CoreFE.TyEnv
  }

-- | Package an elaborated module expression as a merge operand.
operandOf :: Ctx -> String -> CoreFE.Exp -> Maybe CoreFE.Typ -> Either ElabError Operand
operandOf _ what _ Nothing = Left (undetermined what)
operandOf ctx what e (Just t) =
  case whnfT ctx t of
    CoreFE.TyEnvt g -> Right (Operand e t g)
    other -> Left ("the " ++ what ++ " is not a structure; its type is " ++ CoreFE.pretty other)

undetermined :: String -> ElabError
undetermined what =
  "cannot determine the signature of the " ++ what ++ ".\n"
    ++ "  Composition is elaborated by projecting out each component, so the\n"
    ++ "  operand's signature must be known. Add a signature ascription."

-- | Rebuild one component: a labelled component by projection, a transparent
--   type component by writing it down.
projectEntry :: String -> CoreFE.Exp -> CoreFE.TyEnvE -> Either ElabError CoreFE.EnvE
projectEntry _ src (CoreFE.Type _ (CoreFE.TyRcd l _)) = Right (CoreFE.ModE l (CoreFE.RProj src l))
projectEntry _ _ (CoreFE.TypeEq n t) = Right (CoreFE.TypE n t)
projectEntry what _ (CoreFE.Kind n) =
  Left $ "cannot compose the " ++ what ++ ": it has an abstract type component '"
    ++ n ++ "'.\n"
    ++ "  Composition is expanded into projections, which requires every\n"
    ++ "  component to be manifest. An opaque component cannot be rebuilt."
projectEntry what _ (CoreFE.Type n t) =
  Left $ "cannot compose the " ++ what ++ ": component '" ++ n
    ++ "' is unlabelled (type " ++ CoreFE.pretty t ++ "),\n"
    ++ "  so there is no projection that recovers it."

-- | Expand a merge to @((λ#l. λ#r. [projections]) : τ1 → τ2 → τ) e1 e2@: both
--   operands sit outside every binder, evaluated once, left first. Splicing an
--   operand in would expose it to capture, since entries telescope.
expandMerge :: String -> Operand -> Operand -> Either ElabError (CoreFE.Exp, Maybe CoreFE.Typ)
expandMerge opName o1 o2 = do
  let g1 = opSig o1
      g2 = opSig o2
  checkComposable opName g1 g2
  env1 <- mapM (projectEntry ("left operand of " ++ opName) (CoreFE.Var "#l")) g1
  env2 <- mapM (projectEntry ("right operand of " ++ opName) (CoreFE.Var "#r")) g2
  let resT = CoreFE.TyEnvt (g2 ++ g1)
      fun  = CoreFE.Anno
               (CoreFE.Lam "#l" (CoreFE.Lam "#r" (CoreFE.FEnv (env2 ++ env1))))
               (CoreFE.TyArr (opTyp o1) (CoreFE.TyArr (opTyp o2) resT))
  return (CoreFE.App (CoreFE.App fun (opExp o1)) (opExp o2), Just resT)

-- | The side conditions that make a merge expandable, i.e. that make @++@
--   derivable rather than primitive.
checkComposable :: String -> CoreFE.TyEnv -> CoreFE.TyEnv -> Either ElabError ()
checkComposable opName g1 g2 = do
  let (l1, l2) = (sigLabels g1, sigLabels g2)
      (t1, t2) = (sigTyNames g1, sigTyNames g2)
  reportDup "left operand"  (duplicates l1 ++ duplicates t1)
  reportDup "right operand" (duplicates l2 ++ duplicates t2)
  case overlap l1 l2 ++ overlap t1 t2 of
    [] -> Right ()
    cs -> Left $
      "cannot compose with " ++ opName ++ ": both operands declare " ++ commaSep cs ++ ".\n"
        ++ "  Composition is expanded into projections, so the operands'\n"
        ++ "  components must be disjoint -- a repeated name would be\n"
        ++ "  unreachable in the result."
  -- The left operand's components come first, so a type name the right
  -- operand's signature refers to from outside would be captured.
  case overlap (freeTyNamesEnv g2) t1 of
    [] -> Right ()
    cs -> Left $
      "cannot compose with " ++ opName ++ ": the right operand's signature refers to "
        ++ commaSep cs ++ ", which the left operand also defines as a type component.\n"
        ++ "  The left operand's components come first in the result, so the\n"
        ++ "  name would be captured."
  where
    reportDup _    [] = Right ()
    reportDup side cs =
      Left ("the " ++ side ++ " of " ++ opName ++ " declares " ++ commaSep cs ++ " more than once.")

commaSep :: [String] -> String
commaSep []     = ""
commaSep [x]    = "'" ++ x ++ "'"
commaSep [x, y] = "'" ++ x ++ "' and '" ++ y ++ "'"
commaSep (x:xs) = "'" ++ x ++ "', " ++ commaSep xs

elabModule :: EnvML.Module -> Either ElabError CoreFE.Exp
elabModule m = fst <$> elabModuleExp [] m

-- | @Γ ⊢ M ⇝ e : τ@. The type is 'Nothing' when the source does not determine
--   it; that only matters if a merge later needs it.
elabModuleExp :: Ctx -> EnvML.Module -> Either ElabError (CoreFE.Exp, Maybe CoreFE.Typ)
elabModuleExp ctx modl =
  case modl of
    EnvML.VarM name -> Right (CoreFE.Var name, lookupTm ctx name)

    EnvML.Functor args m -> do
      (e, mt) <- elabFunctor ctx args m Nothing
      return (box0 e, CoreFE.TyBoxT [] <$> mt)

    EnvML.Struct structs -> do
      (env, msig) <- elabStructures ctx structs
      return (box0 (CoreFE.FEnv env), CoreFE.TyBoxT [] . CoreFE.TyEnvt <$> msig)

    EnvML.MApp m1 m2 -> do
      (e1, mt1) <- elabModuleExp ctx m1
      (e2, _)   <- elabModuleExp ctx m2
      let mres = case whnfT ctx <$> mt1 of
                   Just (CoreFE.TyArr _ b) -> Just b
                   _                       -> Nothing
      return (CoreFE.App e1 e2, mres)

    EnvML.MAppt m1 a -> do
      (e1, mt1) <- elabModuleExp ctx m1
      ta <- elabTyp a
      let mres = case whnfT ctx <$> mt1 of
                   Just (CoreFE.TyAll v b) -> Just (substTyp v ta b)
                   _                       -> Nothing
      return (CoreFE.TApp e1 ta, mres)

    EnvML.MAnno m mty -> do
      t <- elabModTyp mty
      e <- elabCheck ctx m t
      return (e, Just t)

    -- Independent merge: both operands are closed, so both are projected.
    EnvML.MConcat m1 m2 -> do
      (e1, mt1) <- elabModuleExp ctx m1
      (e2, mt2) <- elabModuleExp ctx m2
      o1 <- operandOf ctx "left operand of ++"  e1 mt1
      o2 <- operandOf ctx "right operand of ++" e2 mt2
      expandMerge "++" o1 o2

    -- Dependent merge of two literal structs: the declarations flatten into one
    -- environment, so the right struct's fields see the left struct's by name.
    EnvML.MDepConcat (EnvML.Struct s1) (EnvML.Struct s2) -> do
      (env, msig) <- elabStructures ctx (s1 ++ s2)
      return (CoreFE.FEnv env, CoreFE.TyEnvt <$> msig)

    -- Otherwise the left is opaque: project it, and elaborate the right fragment
    -- raw (unboxed) so it can still depend on the ambient context.
    EnvML.MDepConcat m1 m2 -> do
      (e1, mt1) <- elabModuleExp ctx m1
      (e2, mt2) <- elabBodyRaw ctx m2 Nothing
      o1 <- operandOf ctx "left operand of +"  e1 mt1
      o2 <- operandOf ctx "right operand of +" e2 mt2
      expandMerge "+" o1 o2

-- | Elaborate against a known type. A sandboxed form carries the annotation
--   inside its box, closed over the ambient abbreviations; for a functor the
--   annotation also supplies the parameter types the source leaves out.
elabCheck :: Ctx -> EnvML.Module -> CoreFE.Typ -> Either ElabError CoreFE.Exp
elabCheck ctx m t =
  case m of
    EnvML.Functor args body -> sandbox . fst =<< elabFunctor ctx args body (Just t)
    EnvML.Struct structs -> sandbox . CoreFE.FEnv . fst =<< elabStructures ctx structs
    _ -> do
      (e, _) <- elabModuleExp ctx m
      return (CoreFE.Anno e t)
  where
    sandbox e = (\tc -> box0 (CoreFE.Anno e tc)) <$> closeTyp ctx t

-- | Nested lambdas. The box is placed by the caller around the whole functor, so
--   the binders sit inside it. An expected type is peeled one parameter at a
--   time, which is what gives unannotated parameters their types.
elabFunctor ::
  Ctx -> EnvML.FunArgs -> EnvML.Module -> Maybe CoreFE.Typ
  -> Either ElabError (CoreFE.Exp, Maybe CoreFE.Typ)
elabFunctor ctx [] body mt = elabBodyRaw ctx body mt
elabFunctor ctx ((name, arg) : rest) body mt =
  case (arg, whnfT ctx <$> mt) of
    (EnvML.TyArg, Just (CoreFE.TyAll v t)) -> do
      (e, mt') <- elabFunctor (CTyA name : ctx) rest body (Just (renameTyVar v name t))
      return (CoreFE.TLam name e, CoreFE.TyAll name <$> mt')
    (EnvML.TyArg, _) -> do
      (e, _) <- elabFunctor (CTyA name : ctx) rest body Nothing
      return (CoreFE.TLam name e, Nothing)
    (_, Just (CoreFE.TyArr a t)) -> do
      (e, mt') <- elabFunctor (CTm name a : ctx) rest body (Just t)
      return (CoreFE.Lam name e, CoreFE.TyArr a <$> mt')
    (EnvML.TmArgType ty, _) -> do
      a <- elabTyp ty
      (e, mt') <- elabFunctor (CTm name a : ctx) rest body Nothing
      return (CoreFE.Lam name e, CoreFE.TyArr a <$> mt')
    (EnvML.TmArg, _) -> do
      (e, _) <- elabFunctor (CTmU name : ctx) rest body Nothing
      return (CoreFE.Lam name e, Nothing)

-- | A functor body, without an outer sandbox box: a struct body or nested
--   functor is already covered by the enclosing functor's box.
elabBodyRaw ::
  Ctx -> EnvML.Module -> Maybe CoreFE.Typ
  -> Either ElabError (CoreFE.Exp, Maybe CoreFE.Typ)
elabBodyRaw ctx (EnvML.Struct structs) _ = do
  (env, msig) <- elabStructures ctx structs
  return (CoreFE.FEnv env, CoreFE.TyEnvt <$> msig)
elabBodyRaw ctx (EnvML.Functor args m) mt = elabFunctor ctx args m mt
elabBodyRaw ctx other _ = elabModuleExp ctx other

-- | Declarations, threading the context so later ones see earlier ones. Returns
--   the environment (head = last declaration) and, when every component's type
--   is determined, the signature in the same order.
elabStructures :: Ctx -> EnvML.Structures -> Either ElabError (CoreFE.Env, Maybe CoreFE.TyEnv)
elabStructures ctx0 = go ctx0 [] []
  where
    go _ accE accT [] = Right (accE, sequence accT)
    go ctx accE accT (s : rest) = do
      (entry, mte) <- elabStructure ctx s
      go (extendCtx ctx entry mte) (entry : accE) (mte : accT) rest

extendCtx :: Ctx -> CoreFE.EnvE -> Maybe CoreFE.TyEnvE -> Ctx
extendCtx ctx entry mte =
  case (entry, mte) of
    (CoreFE.TypE n t, _)                         -> CTyD n t : ctx
    (_, Just (CoreFE.Type n (CoreFE.TyRcd _ t))) -> CTm n t : ctx
    (CoreFE.ModE n _, Nothing)                   -> CTmU n : ctx
    (CoreFE.ExpE n _, Nothing)                   -> CTmU n : ctx
    _                                            -> ctx

-- | One declaration, with its signature component when determined.
elabStructure :: Ctx -> EnvML.Structure -> Either ElabError (CoreFE.EnvE, Maybe CoreFE.TyEnvE)
elabStructure ctx struct =
  case struct of
    EnvML.Let name Nothing e -> do
      e' <- elabExp ctx e
      return (CoreFE.ModE name e', Nothing)
    EnvML.Let name (Just ty) e -> do
      t  <- elabTyp ty
      e' <- elabExp ctx e
      return (CoreFE.ModE name (CoreFE.Anno e' t), Just (termEntry name t))

    EnvML.TypDecl name ty -> typeDecl name =<< elabTyp ty
    EnvML.ModTypDecl name mty -> typeDecl name =<< elabModTyp mty

    EnvML.ModStruct name Nothing mod1 -> do
      (e, mt) <- elabModuleExp ctx mod1
      return (CoreFE.ModE name e, termEntry name <$> mt)
    EnvML.ModStruct name (Just mty) mod1 -> do
      t <- elabModTyp mty
      e <- elabCheck ctx mod1 t
      return (CoreFE.ModE name e, Just (termEntry name t))

    EnvML.FunctStruct name args Nothing mod1 -> do
      (e, mt) <- elabFunctor ctx args mod1 Nothing
      return (CoreFE.ModE name (box0 e), termEntry name . CoreFE.TyBoxT [] <$> mt)
    EnvML.FunctStruct name args (Just mty) mod1 -> do
      t <- elabModTyp mty
      (e, _) <- elabFunctor ctx args mod1 (Just t)
      tc <- closeTyp ctx t
      return (CoreFE.ModE name (box0 (CoreFE.Anno e tc)), Just (termEntry name t))
  where
    typeDecl name t = Right (CoreFE.TypE name t, Just (CoreFE.TypeEq name t))

elabExp :: Ctx -> EnvML.Exp -> Either ElabError CoreFE.Exp
elabExp ctx e =
  case e of
    EnvML.Lit i    -> return (CoreFE.Lit i)
    EnvML.Var n    -> return (CoreFE.Var n)
    EnvML.Lam args e1 -> elabLambda ctx args e1
    EnvML.TLam _ _ -> Left "Typed lambdas don't exist at source separately."
    EnvML.TClos {} -> Left "Typed closures don't exist at source separately."
    EnvML.Clos env args e1 ->
      CoreFE.Clos <$> elabEnv ctx env <*> elabLambda ctx args e1
    EnvML.App e1 e2 -> CoreFE.App <$> elabExp ctx e1 <*> elabExp ctx e2
    EnvML.TApp e1 t -> CoreFE.TApp <$> elabExp ctx e1 <*> elabTyp t
    EnvML.Box env e1 -> CoreFE.Box <$> elabEnv ctx env <*> elabExp ctx e1
    EnvML.Rec records -> CoreFE.FEnv . map (CoreFE.ExpE "_") <$> elabRecords ctx records
    EnvML.RProj e1 n -> (\x -> CoreFE.RProj x n) <$> elabExp ctx e1
    EnvML.FEnv env   -> CoreFE.FEnv <$> elabEnv ctx env
    EnvML.Anno e1 ty -> CoreFE.Anno <$> elabExp ctx e1 <*> elabTyp ty
    EnvML.Mod m      -> fst <$> elabModuleExp ctx m
    EnvML.BinOp op   -> elabBinOp ctx op
    EnvML.EList es   -> CoreFE.EList <$> mapM (elabExp ctx) es
    EnvML.ETake i e1 -> CoreFE.ETake i <$> elabExp ctx e1
    EnvML.ELength e1 -> CoreFE.ELength <$> elabExp ctx e1

elabBinOp :: Ctx -> EnvML.BinOp -> Either ElabError CoreFE.Exp
elabBinOp ctx op =
  let bin f a b = CoreFE.BinOp <$> (f <$> elabExp ctx a <*> elabExp ctx b)
  in case op of
       EnvML.Add      a b -> bin CoreFE.Add a b
       EnvML.Sub      a b -> bin CoreFE.Sub a b
       EnvML.Mul      a b -> bin CoreFE.Mul a b
       EnvML.EqEq     a b -> bin CoreFE.EqEq a b
       EnvML.LessThan a b -> bin CoreFE.LessThan a b
       EnvML.Concat _ _   -> Left "expression-level ++ is not supported; compose modules instead."

-- | Parameter annotations are not emitted: a lambda is checked against the
--   annotation of the declaration containing it.
elabLambda :: Ctx -> EnvML.FunArgs -> EnvML.Exp -> Either ElabError CoreFE.Exp
elabLambda ctx [] body = elabExp ctx body
elabLambda ctx ((name, arg) : rest) body = do
  ctx' <- case arg of
    EnvML.TyArg        -> Right (CTyA name : ctx)
    EnvML.TmArg        -> Right (CTmU name : ctx)
    EnvML.TmArgType ty -> (\a -> CTm name a : ctx) <$> elabTyp ty
  restExp <- elabLambda ctx' rest body
  return $ case arg of
    EnvML.TyArg -> CoreFE.TLam name restExp
    _           -> CoreFE.Lam name restExp

elabRecords :: Ctx -> [(EnvML.Name, EnvML.Exp)] -> Either ElabError [CoreFE.Exp]
elabRecords ctx = mapM (\(n, e) -> CoreFE.Rec n <$> elabExp ctx e)

elabEnv :: Ctx -> EnvML.Env -> Either ElabError CoreFE.Env
elabEnv ctx = fmap reverse . mapM (elabEnvE ctx)

elabEnvE :: Ctx -> EnvML.EnvE -> Either ElabError CoreFE.EnvE
elabEnvE ctx envE =
  case envE of
    EnvML.ExpEN name e     -> CoreFE.ExpE name <$> elabExp ctx e
    EnvML.ExpE e           -> CoreFE.ExpE "_"  <$> elabExp ctx e
    EnvML.TypEN name ty    -> CoreFE.TypE name <$> elabTyp ty
    EnvML.TypE ty          -> CoreFE.TypE "_" <$> elabTyp ty
    EnvML.ModE name m      -> CoreFE.ModE name . fst <$> elabModuleExp ctx m
    EnvML.ModTypE name mty -> CoreFE.TypE name <$> elabModTyp mty

elabTyp :: EnvML.Typ -> Either ElabError CoreFE.Typ
elabTyp ty =
  case ty of
    EnvML.TyLit lit      -> Right (CoreFE.TyLit lit)
    EnvML.TyVar n        -> Right (CoreFE.TyVar n)
    EnvML.TyArr ta tb    -> CoreFE.TyArr <$> elabTyp ta <*> elabTyp tb
    EnvML.TyAll n ty1    -> CoreFE.TyAll n <$> elabTyp ty1
    EnvML.TyBoxT ctx ty1 -> CoreFE.TyBoxT <$> elabTyCtx ctx <*> elabTyp ty1
    EnvML.TyCtx ctx      -> CoreFE.TyEnvt <$> elabTyCtx ctx
    EnvML.TyModule mty   -> elabModTyp mty
    EnvML.TyList ty1     -> CoreFE.TyList <$> elabTyp ty1
    EnvML.TyRcd fields   ->
      CoreFE.TyEnvt . map (CoreFE.Type "_") <$>
        mapM (\(n, t) -> CoreFE.TyRcd n <$> elabTyp t) fields

elabTyCtx :: EnvML.TyCtx -> Either ElabError CoreFE.TyEnv
elabTyCtx = fmap reverse . mapM elabTyCtxE

elabTyCtxE :: EnvML.TyCtxE -> Either ElabError CoreFE.TyEnvE
elabTyCtxE ctxE =
  case ctxE of
    EnvML.TypeN name ty    -> CoreFE.Type name <$> elabTyp ty
    EnvML.Type ty          -> CoreFE.Type "_" <$> elabTyp ty
    EnvML.KindN name       -> Right (CoreFE.Kind name)
    EnvML.Kind             -> Right (CoreFE.Kind "_")
    EnvML.TypeEqN name ty  -> CoreFE.TypeEq name <$> elabTyp ty
    EnvML.TypeEqM name mty -> CoreFE.TypeEq name <$> elabModTyp mty
    EnvML.TyMod name mty   -> termEntry name <$> elabModTyp mty

elabModTyp :: EnvML.ModuleTyp -> Either ElabError CoreFE.Typ
elabModTyp mty =
  case mty of
    EnvML.TyArrowM ty mty1 -> CoreFE.TyArr <$> elabTyp ty <*> elabModTyp mty1
    EnvML.ForallM n mty1   -> CoreFE.TyAll n <$> elabModTyp mty1
    EnvML.TySig intf       -> CoreFE.TyEnvt <$> elabIntf intf
    EnvML.TyVarM name      -> Right (CoreFE.TyVar name)
    -- Flat signature concatenation, with Y on the head side to match the merge.
    EnvML.MConcatT x y     -> do
      tx <- elabModTyp x
      ty <- elabModTyp y
      return (CoreFE.TyEnvt (tyEnvOf ty ++ tyEnvOf tx))

-- | A signature as a type environment; anything else is one anonymous entry.
tyEnvOf :: CoreFE.Typ -> CoreFE.TyEnv
tyEnvOf (CoreFE.TyEnvt g) = g
tyEnvOf t                 = [CoreFE.Type "_" t]

elabIntf :: EnvML.Intf -> Either ElabError CoreFE.TyEnv
elabIntf = fmap reverse . mapM elabIntfE

-- | A functor member is a term component, like a value or module member, so its
--   signature entry is labelled just as the providing struct's entry is.
elabIntfE :: EnvML.IntfE -> Either ElabError CoreFE.TyEnvE
elabIntfE intfE =
  case intfE of
    EnvML.TyDef name ty     -> CoreFE.TypeEq name <$> elabTyp ty
    EnvML.ValDecl name ty   -> termEntry name <$> elabTyp ty
    EnvML.ModDecl name ty   -> termEntry name <$> elabTyp ty
    EnvML.FunctorDecl name args retTyp -> termEntry name <$> elabFunctorDeclToType args retTyp
    EnvML.SigDecl name intf -> CoreFE.TypeEq name . CoreFE.TyEnvt <$> elabIntf intf

elabFunctorDeclToType :: EnvML.FunArgs -> EnvML.Typ -> Either ElabError CoreFE.Typ
elabFunctorDeclToType [] retTyp = elabTyp retTyp
elabFunctorDeclToType ((name, arg) : rest) retTyp = do
  restType <- elabFunctorDeclToType rest retTyp
  case arg of
    EnvML.TyArg        -> Right (CoreFE.TyAll name restType)
    EnvML.TmArgType ty -> (\a -> CoreFE.TyArr a restType) <$> elabTyp ty
    EnvML.TmArg        ->
      Left ("functor argument '" ++ name ++ "' in a signature must have a type annotation")
