{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

-- | Type-directed elaboration from EnvML (source) to CoreFE.
--
-- The judgment implemented here is
--
--     Γ ⊢ M ⇝ e : τ
--
-- Elaboration carries a typing context and, where the source provides enough
-- information, the core type of the elaborated term. The types are what make
-- module composition compilable: at a merge site @m1 ++ m2@ / @m1 + m2@ we know
-- both operands' signatures, so the merge is expanded into an environment
-- literal built from projections out of the operands. No concatenation
-- primitive is emitted, and CoreFE needs no @++@ term former.
--
-- The expansion is only possible when the operand signatures are *manifest*:
-- every component is either a labelled value/module component (projectable) or
-- a transparent type component (writable). An abstract component -- what
-- sealing would introduce -- cannot be reconstructed, and elaboration reports
-- that explicitly rather than falling back on a primitive.
module EnvML.Elab where

import qualified CoreFE.Named  as CoreFE
import qualified EnvML.Syntax  as EnvML

type ElabError = String

--------------------------------------------------------------------------------
-- Elaboration context
--------------------------------------------------------------------------------

-- | The elaboration context is the core typing context, kept named.
data CtxE
  = CTm  EnvML.Name CoreFE.Typ  -- ^ @x : τ@ with a known type
  | CTmU EnvML.Name             -- ^ @x@ bound, but its type is not determined
  | CTyD EnvML.Name CoreFE.Typ  -- ^ @type t = τ@ (transparent)
  | CTyA EnvML.Name             -- ^ @t : *@ (abstract; a functor type parameter)
  deriving (Show, Eq)

type Ctx = [CtxE]

-- | The type of a term-level name, if it has been determined.
lookupTm :: Ctx -> EnvML.Name -> Maybe CoreFE.Typ
lookupTm [] _ = Nothing
lookupTm (CTm n t : rest) x
  | n == x    = Just t
  | otherwise = lookupTm rest x
lookupTm (CTmU n : rest) x
  | n == x    = Nothing
  | otherwise = lookupTm rest x
lookupTm (_ : rest) x = lookupTm rest x

-- | The definition of a transparent type name, if any.
lookupTy :: Ctx -> EnvML.Name -> Maybe CoreFE.Typ
lookupTy [] _ = Nothing
lookupTy (CTyD n t : rest) x
  | n == x    = Just t
  | otherwise = lookupTy rest x
lookupTy (CTyA n : rest) x
  | n == x    = Nothing
  | otherwise = lookupTy rest x
lookupTy (_ : rest) x = lookupTy rest x

--------------------------------------------------------------------------------
-- Type utilities
--------------------------------------------------------------------------------

-- | @[] ▷ A ≡ A@: an empty-environment box is transparent, mirroring
--   'CoreFE.Check.unbox'.
unboxT :: CoreFE.Typ -> CoreFE.Typ
unboxT (CoreFE.TyBoxT [] a) = unboxT a
unboxT a                    = a

-- | Unbox and expand transparent type abbreviations, so that a module type
--   written as an alias (e.g. a @module type@ name) still exposes its
--   signature.
whnfT :: Ctx -> CoreFE.Typ -> CoreFE.Typ
whnfT ctx = go (0 :: Int)
  where
    go n t
      | n > 100 = t   -- guard against a cyclic abbreviation
      | otherwise =
          case unboxT t of
            CoreFE.TyVar x
              | Just t' <- lookupTy ctx x -> go (n + 1) t'
            t' -> t'

-- | Capture-avoiding enough for the uses here: rename a bound type variable.
renameTyVar :: EnvML.Name -> EnvML.Name -> CoreFE.Typ -> CoreFE.Typ
renameTyVar from to = substTyp from (CoreFE.TyVar to)

-- | Substitute a type for a named type variable.
substTyp :: EnvML.Name -> CoreFE.Typ -> CoreFE.Typ -> CoreFE.Typ
substTyp x s = go
  where
    go t = case t of
      CoreFE.TyLit l        -> CoreFE.TyLit l
      CoreFE.TyVar y        -> if y == x then s else CoreFE.TyVar y
      CoreFE.TyArr a b      -> CoreFE.TyArr (go a) (go b)
      CoreFE.TyAll y a      -> if y == x then CoreFE.TyAll y a else CoreFE.TyAll y (go a)
      -- The body of a box is scoped by the box's own type entries alone (see
      -- 'CoreFE.DeBruijn.toNamelessTyp'), so it never mentions an outer type
      -- variable and must not be substituted into. Its entries are outer-scoped.
      CoreFE.TyBoxT g a     -> CoreFE.TyBoxT (goEnv g) a
      CoreFE.TySubstT y a b ->
        CoreFE.TySubstT y (go a) (if y == x then b else go b)
      CoreFE.TyRcd l a      -> CoreFE.TyRcd l (go a)
      CoreFE.TyEnvt g       -> CoreFE.TyEnvt (goEnv g)
      CoreFE.TyList a       -> CoreFE.TyList (go a)

    -- Entries of a type environment are scoped by the entries AFTER them (see
    -- 'CoreFE.DeBruijn.toNamelessTyEnv'), so an entry whose tail rebinds x
    -- refers to that binding, not to the one being substituted.
    goEnv [] = []
    goEnv (e : rest)
      | any binds rest = e     : goEnv rest
      | otherwise      = goE e : goEnv rest

    goE e = case e of
      CoreFE.Type   n a -> CoreFE.Type   n (go a)
      CoreFE.Kind   n   -> CoreFE.Kind   n
      CoreFE.TypeEq n a -> CoreFE.TypeEq n (go a)

    binds (CoreFE.TypeEq n _) = n == x
    binds (CoreFE.Kind n)     = n == x
    binds _                   = False

--------------------------------------------------------------------------------
-- Signatures
--------------------------------------------------------------------------------

-- | The labelled (projectable) components of a signature.
sigLabels :: CoreFE.TyEnv -> [String]
sigLabels = concatMap f
  where
    f (CoreFE.Type _ (CoreFE.TyRcd l _)) = [l]
    f _                                  = []

-- | The type components of a signature.
sigTyNames :: CoreFE.TyEnv -> [String]
sigTyNames = concatMap f
  where
    f (CoreFE.TypeEq n _) = [n]
    f (CoreFE.Kind n)     = [n]
    f _                   = []

duplicates :: [String] -> [String]
duplicates = go []
  where
    go _ [] = []
    go seen (x:xs)
      | x `elem` seen = x : go seen xs
      | otherwise     = go (x:seen) xs

overlap :: [String] -> [String] -> [String]
overlap xs ys = [x | x <- xs, x `elem` ys]

-- | Demand a signature for a merge operand.
sigOf :: Ctx -> String -> Maybe CoreFE.Typ -> Either ElabError CoreFE.TyEnv
sigOf _ what Nothing =
  Left $
    "cannot determine the signature of the " ++ what ++ ".\n"
      ++ "  Composition is elaborated by projecting out each component, so the\n"
      ++ "  operand's signature must be known. Add a signature ascription."
sigOf ctx what (Just t) =
  case whnfT ctx t of
    CoreFE.TyEnvt g -> Right g
    other ->
      Left $
        "the " ++ what ++ " is not a structure; its type is "
          ++ CoreFE.pretty other

-- | Package an elaborated module expression as a merge operand.
operandOf ::
  Ctx
  -> String
  -> CoreFE.Exp
  -> Maybe CoreFE.Typ
  -> Either ElabError Operand
operandOf ctx what e mt = do
  g <- sigOf ctx what mt
  case mt of
    Just t  -> Right (Operand e t g)
    Nothing -> Left ("cannot determine the type of the " ++ what)

--------------------------------------------------------------------------------
-- Merge expansion
--------------------------------------------------------------------------------

-- | Reconstruct one component of an operand's signature as an environment
--   entry. Value and module components are projected by label; transparent
--   type components are written down directly.
projectEntry :: String -> CoreFE.Exp -> CoreFE.TyEnvE -> Either ElabError CoreFE.EnvE
projectEntry _ src (CoreFE.Type _ (CoreFE.TyRcd l _)) =
  Right (CoreFE.ModE l (CoreFE.RProj src l))
projectEntry _ _ (CoreFE.TypeEq n t) =
  Right (CoreFE.TypE n t)
projectEntry what _ (CoreFE.Kind n) =
  Left $
    "cannot compose the " ++ what ++ ": it has an abstract type component '"
      ++ n ++ "'.\n"
      ++ "  Composition is expanded into projections, which requires every\n"
      ++ "  component to be manifest. An opaque component cannot be rebuilt."
projectEntry what _ (CoreFE.Type n t) =
  Left $
    "cannot compose the " ++ what ++ ": component '" ++ n
      ++ "' is unlabelled (type " ++ CoreFE.pretty t ++ "),\n"
      ++ "  so there is no projection that recovers it."

-- | The entries realizing an operand: every component is rebuilt by
--   projection.
--
--   An operand is never spliced into the merged environment, even when it is a
--   literal. Environment entries telescope -- each entry sees the entries after
--   it -- so splicing would put the operand's body inside the merged
--   environment, where the other operand's component names could capture its
--   free variables. Projecting keeps every operand body outside.
realize :: String -> CoreFE.Exp -> CoreFE.TyEnv -> Either ElabError CoreFE.Env
realize what src g = mapM (projectEntry what src) g

-- | An operand of a merge: its term, its own type (needed to bind it), and the
--   signature driving the expansion.
data Operand = Operand
  { opExp :: CoreFE.Exp
  , opTyp :: CoreFE.Typ
  , opSig :: CoreFE.TyEnv
  }

-- | Expand a merge of two operands whose signatures are known.
--
--   The result matches the environment ordering used throughout: the right
--   operand's components sit at the head, so @m1 ++ m2@ has signature
--   @g2 ++ g1@ and the same evaluation behaviour as a primitive concatenation
--   would have had.
expandMerge :: String -> Operand -> Operand -> Either ElabError (CoreFE.Exp, Maybe CoreFE.Typ)
expandMerge opName o1 o2 = do
  let g1 = opSig o1
      g2 = opSig o2
  checkComposable opName g1 g2
  let resT       = CoreFE.TyEnvt (g2 ++ g1)
      introduced = sigLabels g1 ++ sigLabels g2
      (w1, s1)   = bindOperand "#l" introduced o1 resT
      (w2, s2)   = bindOperand "#r" introduced o2 resT
  env1 <- realize ("left operand of " ++ opName) s1 g1
  env2 <- realize ("right operand of " ++ opName) s2 g2
  let body = CoreFE.FEnv (env2 ++ env1)
  return (w1 (w2 body), Just resT)

-- | Bind an operand to a fresh variable so that its body is evaluated outside
--   the merged environment, and so that it is evaluated exactly once however
--   many components are projected from it. The binding is an annotated redex so
--   the result stays inferable.
--
--   A variable operand is already atomic and needs no binding -- unless the
--   merge introduces a component of the same name, which would shadow it.
--   The fresh names are not valid source identifiers, so they cannot clash.
bindOperand ::
  EnvML.Name
  -> [String]
  -> Operand
  -> CoreFE.Typ
  -> (CoreFE.Exp -> CoreFE.Exp, CoreFE.Exp)
bindOperand x introduced o resT =
  case opExp o of
    CoreFE.Var n | n `notElem` introduced -> (id, CoreFE.Var n)
    e ->
      ( \body ->
          CoreFE.App
            (CoreFE.Anno
               (CoreFE.Lam x body)
               (CoreFE.TyArr (opTyp o) resT))
            e
      , CoreFE.Var x
      )

-- | The side conditions that make a merge expandable. These are exactly the
--   conditions under which @++@ is derivable rather than primitive.
checkComposable :: String -> CoreFE.TyEnv -> CoreFE.TyEnv -> Either ElabError ()
checkComposable opName g1 g2 = do
  let l1 = sigLabels g1
      l2 = sigLabels g2
      t1 = sigTyNames g1
      t2 = sigTyNames g2
  reportDup "left operand"  (duplicates l1 ++ duplicates t1)
  reportDup "right operand" (duplicates l2 ++ duplicates t2)
  case overlap l1 l2 ++ overlap t1 t2 of
    [] -> Right ()
    cs ->
      Left $
        "cannot compose with " ++ opName ++ ": both operands declare "
          ++ commaSep cs ++ ".\n"
          ++ "  Composition is expanded into projections, so the operands'\n"
          ++ "  components must be disjoint -- a repeated name would be\n"
          ++ "  unreachable in the result."
  where
    reportDup _    [] = Right ()
    reportDup side cs =
      Left $
        "the " ++ side ++ " of " ++ opName ++ " declares "
          ++ commaSep cs ++ " more than once."

commaSep :: [String] -> String
commaSep []     = ""
commaSep [x]    = "'" ++ x ++ "'"
commaSep [x, y] = "'" ++ x ++ "' and '" ++ y ++ "'"
commaSep (x:xs) = "'" ++ x ++ "', " ++ commaSep xs

--------------------------------------------------------------------------------
-- Modules
--------------------------------------------------------------------------------

elabModule :: EnvML.Module -> Either ElabError CoreFE.Exp
elabModule m = fst <$> elabModuleExp [] m

-- | Γ ⊢ M ⇝ e : τ. The type is 'Nothing' when the source does not determine
--   it (an unannotated functor parameter, say); that is only an error if a
--   merge later needs it.
elabModuleExp :: Ctx -> EnvML.Module -> Either ElabError (CoreFE.Exp, Maybe CoreFE.Typ)
elabModuleExp ctx modl =
  case modl of
    EnvML.VarM name ->
      Right (CoreFE.Var name, lookupTm ctx name)

    -- Sandbox: a standalone struct / whole functor elaborates to an
    -- empty-environment box [] ▷ e, isolating it from the ambient context.
    EnvML.Functor args m -> do
      (e, mt) <- elabFunctor ctx args m Nothing
      return (box0 e, CoreFE.TyBoxT [] <$> mt)

    EnvML.Struct structs -> do
      (env, msig) <- elabStructures ctx structs
      return
        ( box0 (CoreFE.FEnv env)
        , CoreFE.TyBoxT [] . CoreFE.TyEnvt <$> msig
        )

    EnvML.MApp m1 m2 -> do
      (e1, mt1) <- elabModuleExp ctx m1
      (e2, _)   <- elabModuleExp ctx m2
      let mres = case whnfT ctx <$> mt1 of
                   Just (CoreFE.TyArr _ b) -> Just b
                   _                       -> Nothing
      return (CoreFE.App e1 e2, mres)

    EnvML.MAppt m1 a -> do
      (e1, mt1) <- elabModuleExp ctx m1
      let ta = elabTyp a
          mres = case whnfT ctx <$> mt1 of
                   Just (CoreFE.TyAll v b) -> Just (substTyp v ta b)
                   _                       -> Nothing
      return (CoreFE.TApp e1 ta, mres)

    EnvML.MAnno m mty -> do
      let t = elabModTyp mty
      e <- elabCheck ctx m t
      return (CoreFE.Anno e t, Just t)

    -- Independent merge: both operands are closed, so both are projected.
    EnvML.MConcat m1 m2 -> do
      (e1, mt1) <- elabModuleExp ctx m1
      (e2, mt2) <- elabModuleExp ctx m2
      o1 <- operandOf ctx "left operand of ++"  e1 mt1
      o2 <- operandOf ctx "right operand of ++" e2 mt2
      expandMerge "++" o1 o2

    -- Dependent merge `m1 + m2` (FE's ∆, e), vs `++` (closed δ-merge).
    -- When BOTH operands are literal structs, their declarations flatten into
    -- ONE environment: the right struct's fields then see the left struct's
    -- fields by name (later entries see earlier ones).
    EnvML.MDepConcat (EnvML.Struct s1) (EnvML.Struct s2) -> do
      (env, msig) <- elabStructures ctx (s1 ++ s2)
      return (CoreFE.FEnv env, CoreFE.TyEnvt <$> msig)

    -- Otherwise the left is opaque (a variable/application): its components are
    -- recovered by projection, and the right fragment is elaborated RAW
    -- (un-boxed) so it can still depend on the ambient context.
    EnvML.MDepConcat m1 m2 -> do
      (e1, mt1) <- elabModuleExp ctx m1
      (e2, mt2) <- elabBodyRaw ctx m2 Nothing
      o1 <- operandOf ctx "left operand of +"  e1 mt1
      o2 <- operandOf ctx "right operand of +" e2 mt2
      expandMerge "+" o1 o2

-- | Elaborate a module against a known type, pushing the type into functor
--   parameters (which the source leaves unannotated).
elabCheck :: Ctx -> EnvML.Module -> CoreFE.Typ -> Either ElabError CoreFE.Exp
elabCheck ctx m t =
  case m of
    EnvML.Functor args body -> box0 . fst <$> elabFunctor ctx args body (Just t)
    _                       -> fst <$> elabModuleExp ctx m

-- | Wrap a core term in an empty-environment box (the sandbox wrapper).
box0 :: CoreFE.Exp -> CoreFE.Exp
box0 = CoreFE.Box []

-- | Functor elaboration: nested lambdas. The box is placed by the caller AROUND
-- the whole functor (so the λ/Λ binders sit inside the box and rebind the
-- body's free vars). When an expected type is supplied it is peeled one
-- parameter at a time, which is what gives unannotated parameters their types.
elabFunctor ::
  Ctx
  -> EnvML.FunArgs
  -> EnvML.Module
  -> Maybe CoreFE.Typ
  -> Either ElabError (CoreFE.Exp, Maybe CoreFE.Typ)
elabFunctor ctx [] body mt = elabBodyRaw ctx body mt
elabFunctor ctx ((name, arg) : rest) body mt =
  case (arg, whnfT ctx <$> mt) of
    (EnvML.TyArg, Just (CoreFE.TyAll v t)) -> do
      (e, mt') <- elabFunctor (CTyA name : ctx) rest body
                    (Just (renameTyVar v name t))
      return (CoreFE.TLam name e, CoreFE.TyAll name <$> mt')

    (EnvML.TyArg, _) -> do
      (e, _) <- elabFunctor (CTyA name : ctx) rest body Nothing
      return (CoreFE.TLam name e, Nothing)

    (_, Just (CoreFE.TyArr a t)) -> do
      (e, mt') <- elabFunctor (CTm name a : ctx) rest body (Just t)
      return (CoreFE.Lam name e, CoreFE.TyArr a <$> mt')

    (EnvML.TmArgType ty, _) -> do
      let a = elabTyp ty
      (e, mt') <- elabFunctor (CTm name a : ctx) rest body Nothing
      return (CoreFE.Lam name e, CoreFE.TyArr a <$> mt')

    (EnvML.TmArg, _) -> do
      (e, _) <- elabFunctor (CTmU name : ctx) rest body Nothing
      return (CoreFE.Lam name e, Nothing)

-- | Elaborate a functor body WITHOUT adding an outer sandbox box: a struct body
-- and nested functor stay unboxed (covered by the enclosing functor's box);
-- everything else delegates to 'elabModuleExp'.
elabBodyRaw ::
  Ctx
  -> EnvML.Module
  -> Maybe CoreFE.Typ
  -> Either ElabError (CoreFE.Exp, Maybe CoreFE.Typ)
elabBodyRaw ctx (EnvML.Struct structs) _ = do
  (env, msig) <- elabStructures ctx structs
  return (CoreFE.FEnv env, CoreFE.TyEnvt <$> msig)
elabBodyRaw ctx (EnvML.Functor args m) mt = elabFunctor ctx args m mt
elabBodyRaw ctx other _ = elabModuleExp ctx other

--------------------------------------------------------------------------------
-- Structures
--------------------------------------------------------------------------------

-- | Elaborate a sequence of declarations, threading the context so that later
--   declarations see earlier ones. Returns the core environment (head = last
--   declaration) and, when every component's type is determined, the signature
--   in the same order.
elabStructures ::
  Ctx
  -> EnvML.Structures
  -> Either ElabError (CoreFE.Env, Maybe CoreFE.TyEnv)
elabStructures ctx0 = go ctx0 [] []
  where
    go _ accE accT [] = Right (accE, sequence accT)
    go ctx accE accT (s : rest) = do
      (entry, mte) <- elabStructure ctx s
      let ctx' = extendCtx ctx entry mte
      go ctx' (entry : accE) (mte : accT) rest

-- | Record a freshly elaborated declaration in the context.
extendCtx :: Ctx -> CoreFE.EnvE -> Maybe CoreFE.TyEnvE -> Ctx
extendCtx ctx entry mte =
  case (entry, mte) of
    (CoreFE.TypE n t, _)                    -> CTyD n t : ctx
    (_, Just (CoreFE.Type n (CoreFE.TyRcd _ t))) -> CTm n t : ctx
    (CoreFE.ModE n _, Nothing)              -> CTmU n : ctx
    (CoreFE.ExpE n _, Nothing)              -> CTmU n : ctx
    _                                       -> ctx

-- | A single declaration, with its signature component when determined.
elabStructure ::
  Ctx
  -> EnvML.Structure
  -> Either ElabError (CoreFE.EnvE, Maybe CoreFE.TyEnvE)
elabStructure ctx struct =
  case struct of
    EnvML.Let name maybeTyp e ->
      case maybeTyp of
        Nothing -> do
          e' <- elabExp ctx e
          return (CoreFE.ModE name e', Nothing)
        Just ty -> do
          let t = elabTyp ty
          e' <- elabExp ctx e
          return
            ( CoreFE.ModE name (CoreFE.Anno e' t)
            , Just (CoreFE.Type name (CoreFE.TyRcd name t))
            )

    EnvML.TypDecl name ty ->
      let t = elabTyp ty
      in return (CoreFE.TypE name t, Just (CoreFE.TypeEq name t))

    EnvML.ModTypDecl name mty ->
      let t = elabModTyp mty
      in return (CoreFE.TypE name t, Just (CoreFE.TypeEq name t))

    EnvML.ModStruct name maybeTyp mod1 ->
      case maybeTyp of
        Nothing -> do
          (e, mt) <- elabModuleExp ctx mod1
          return
            ( CoreFE.ModE name e
            , (\t -> CoreFE.Type name (CoreFE.TyRcd name t)) <$> mt
            )
        Just mty -> do
          let t = elabModTyp mty
          e <- elabCheck ctx mod1 t
          return
            ( CoreFE.ModE name (CoreFE.Anno e t)
            , Just (CoreFE.Type name (CoreFE.TyRcd name t))
            )

    EnvML.FunctStruct name args maybeTyp mod1 ->
      case maybeTyp of
        Nothing -> do
          (e, mt) <- elabFunctor ctx args mod1 Nothing
          return
            ( CoreFE.ModE name (box0 e)
            , (\t -> CoreFE.Type name (CoreFE.TyRcd name (CoreFE.TyBoxT [] t))) <$> mt
            )
        Just mty -> do
          let t = elabModTyp mty
          (e, _) <- elabFunctor ctx args mod1 (Just t)
          return
            ( CoreFE.ModE name (CoreFE.Anno (box0 e) t)
            , Just (CoreFE.Type name (CoreFE.TyRcd name t))
            )

--------------------------------------------------------------------------------
-- Expressions
--------------------------------------------------------------------------------

elabExp :: Ctx -> EnvML.Exp -> Either ElabError CoreFE.Exp
elabExp ctx e =
  case e of
    EnvML.Lit i    -> return (CoreFE.Lit i)
    EnvML.Var n    -> return (CoreFE.Var n)
    EnvML.Lam args e1  -> elabLambda ctx args e1
    EnvML.TLam _ _ -> Left "Typed lambdas don't exist at source separately."
    EnvML.Clos env args e1 -> do
      env'  <- elabEnv ctx env
      body' <- elabLambda ctx args e1
      return (CoreFE.Clos env' body')
    EnvML.App e1 e2 -> CoreFE.App <$> elabExp ctx e1 <*> elabExp ctx e2
    EnvML.TClos {}  -> Left "Typed closures don't exist at source separately."
    EnvML.TApp e1 t -> (\x -> CoreFE.TApp x (elabTyp t)) <$> elabExp ctx e1
    EnvML.Box env e1 -> do
      env' <- elabEnv ctx env
      CoreFE.Box env' <$> elabExp ctx e1
    EnvML.Rec records ->
      CoreFE.FEnv . map (CoreFE.ExpE "_") <$> elabRecords ctx records
    EnvML.RProj e1 n -> (\x -> CoreFE.RProj x n) <$> elabExp ctx e1
    EnvML.FEnv env   -> CoreFE.FEnv <$> elabEnv ctx env
    EnvML.Anno e1 ty -> (\x -> CoreFE.Anno x (elabTyp ty)) <$> elabExp ctx e1
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
       EnvML.Concat _ _   ->
         Left "expression-level ++ is not supported; compose modules instead."

elabLambda :: Ctx -> EnvML.FunArgs -> EnvML.Exp -> Either ElabError CoreFE.Exp
elabLambda ctx [] body = elabExp ctx body
elabLambda ctx ((name, arg) : rest) body = do
  restExp <- elabLambda (bindArg arg) rest body
  return $ case arg of
    EnvML.TyArg       -> CoreFE.TLam name restExp
    EnvML.TmArg       -> CoreFE.Lam  name restExp
    -- NOTE: We ignore type annotations on parameters for now
    EnvML.TmArgType _ -> CoreFE.Lam  name restExp
  where
    bindArg EnvML.TyArg           = CTyA name : ctx
    bindArg EnvML.TmArg           = CTmU name : ctx
    bindArg (EnvML.TmArgType ty)  = CTm name (elabTyp ty) : ctx

elabRecords :: Ctx -> [(EnvML.Name, EnvML.Exp)] -> Either ElabError [CoreFE.Exp]
elabRecords _ [] = return []
elabRecords ctx ((n, e) : rest) =
  (:) <$> (CoreFE.Rec n <$> elabExp ctx e) <*> elabRecords ctx rest

elabEnv :: Ctx -> EnvML.Env -> Either ElabError CoreFE.Env
elabEnv ctx = fmap reverse . mapM (elabEnvE ctx)

elabEnvE :: Ctx -> EnvML.EnvE -> Either ElabError CoreFE.EnvE
elabEnvE ctx envE =
  case envE of
    EnvML.ExpEN name e  -> CoreFE.ExpE name <$> elabExp ctx e
    EnvML.ExpE e        -> CoreFE.ExpE "_"  <$> elabExp ctx e
    EnvML.TypEN name ty -> return (CoreFE.TypE name (elabTyp ty))
    EnvML.TypE ty       -> return (CoreFE.TypE "_" (elabTyp ty))
    EnvML.ModE name m   -> CoreFE.ModE name . fst <$> elabModuleExp ctx m
    EnvML.ModTypE name mty -> return (CoreFE.TypE name (elabModTyp mty))

--------------------------------------------------------------------------------
-- Types (pure syntactic translation)
--------------------------------------------------------------------------------

elabTyp :: EnvML.Typ -> CoreFE.Typ
elabTyp ty =
  case ty of
    EnvML.TyLit lit      -> CoreFE.TyLit lit
    EnvML.TyVar n        -> CoreFE.TyVar n
    EnvML.TyArr ta tb    -> CoreFE.TyArr (elabTyp ta) (elabTyp tb)
    EnvML.TyAll n ty1    -> CoreFE.TyAll n (elabTyp ty1)
    EnvML.TyBoxT ctx ty1 -> CoreFE.TyBoxT (elabTyCtx ctx) (elabTyp ty1)
    EnvML.TyRcd fields   -> CoreFE.TyEnvt $ map (CoreFE.Type "_") $ elabRcdFieldsTy fields
    EnvML.TyCtx ctx      -> CoreFE.TyEnvt (elabTyCtx ctx)
    EnvML.TyModule mty   -> elabModTyp mty
    EnvML.TyList ty1     -> CoreFE.TyList (elabTyp ty1)

elabTyCtx :: EnvML.TyCtx -> CoreFE.TyEnv
elabTyCtx = reverse . map elabTyCtxE

elabTyCtxE :: EnvML.TyCtxE -> CoreFE.TyEnvE
elabTyCtxE ctxE =
  case ctxE of
    EnvML.TypeN name ty   -> CoreFE.Type name (elabTyp ty)
    EnvML.Type ty         -> CoreFE.Type "_" (elabTyp ty)
    EnvML.KindN name      -> CoreFE.Kind name
    EnvML.Kind            -> CoreFE.Kind "_"
    EnvML.TypeEqN name ty -> CoreFE.TypeEq name (elabTyp ty)
    EnvML.TyMod name mty  -> CoreFE.Type name (elabModTyp mty)
    EnvML.TypeEqM name mty -> CoreFE.TypeEq name (elabModTyp mty)

elabRcdFieldsTy :: [(EnvML.Name, EnvML.Typ)] -> [CoreFE.Typ]
elabRcdFieldsTy = map (\(n, ty) -> CoreFE.TyRcd n (elabTyp ty))

elabModTyp :: EnvML.ModuleTyp -> CoreFE.Typ
elabModTyp mty =
  case mty of
    EnvML.TyArrowM ty mty1 -> CoreFE.TyArr (elabTyp ty) (elabModTyp mty1)
    EnvML.ForallM n mty1   -> CoreFE.TyAll n (elabModTyp mty1)
    EnvML.TySig intf       -> CoreFE.TyEnvt (elabIntf intf)
    EnvML.TyVarM name      -> CoreFE.TyVar name
    -- Flat signature concatenation: append the two type environments, with Y on
    -- the head side to match the term-level merge ordering.
    EnvML.MConcatT x y     ->
      CoreFE.TyEnvt (tyEnvOf (elabModTyp y) ++ tyEnvOf (elabModTyp x))

-- | View a (module) type as a type environment. Signatures are TyEnvt;
--   anything else is treated as a single anonymous entry.
tyEnvOf :: CoreFE.Typ -> CoreFE.TyEnv
tyEnvOf (CoreFE.TyEnvt g) = g
tyEnvOf t                 = [CoreFE.Type "_" t]

elabIntf :: EnvML.Intf -> CoreFE.TyEnv
elabIntf = reverse . map elabIntfE

elabIntfE :: EnvML.IntfE -> CoreFE.TyEnvE
elabIntfE intfE =
  case intfE of
    EnvML.TyDef name ty    -> CoreFE.TypeEq name (elabTyp ty)
    EnvML.ValDecl name ty  -> CoreFE.Type name (CoreFE.TyRcd name (elabTyp ty))
    EnvML.ModDecl name ty  -> CoreFE.Type name (CoreFE.TyRcd name (elabTyp ty))
    EnvML.FunctorDecl name args retTyp ->
      CoreFE.TypeEq name (elabFunctorDeclToType args retTyp)
    EnvML.SigDecl name intf ->
      CoreFE.TypeEq name (CoreFE.TyEnvt (elabIntf intf))

elabFunctorDeclToType :: EnvML.FunArgs -> EnvML.Typ -> CoreFE.Typ
elabFunctorDeclToType [] retTyp = elabTyp retTyp
elabFunctorDeclToType ((name, arg) : rest) retTyp =
  let restType = elabFunctorDeclToType rest retTyp
  in case arg of
       EnvML.TyArg        -> CoreFE.TyAll name restType
       EnvML.TmArg        ->
         error $ "Functor argument '" ++ name ++ "' must have type annotation"
       EnvML.TmArgType ty -> CoreFE.TyArr (elabTyp ty) restType
