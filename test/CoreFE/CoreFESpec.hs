module CoreFE.CoreFESpec (spec) where

import CoreFE.Eval (eval)
import CoreFE.Check (infer, check, teq)
import CoreFE.Syntax
import CoreFE.Parser.Lexer (lexer)
import CoreFE.Parser.Parser (parseExp, parseTyp, parseEnv)
import Test.Hspec

-- Helpers: parse and evaluate
pExp :: String -> Exp
pExp = parseExp . lexer

pTyp :: String -> Typ
pTyp = parseTyp . lexer

pEnv :: String -> TyEnv
pEnv = parseEnv . lexer

eval0 :: Exp -> Maybe Exp
eval0 = eval []

evalP :: String -> Maybe Exp
evalP = eval0 . pExp

inferP :: String -> Maybe Typ
inferP s = infer [] (pExp s)

inferInCtx :: String -> String -> Maybe Typ
inferInCtx env expr = infer (pEnv env) (pExp expr)

checkP :: String -> String -> Bool
checkP expr typ = check [] (pExp expr) (pTyp typ)

checkInCtx :: String -> String -> String -> Bool
checkInCtx env expr typ = check (pEnv env) (pExp expr) (pTyp typ)

isTypEq :: String -> String -> String -> String -> Bool
isTypEq g1 a1 a2 g2 = teq (pEnv g1) (pTyp a1) (pTyp a2) (pEnv g2)

-- ═══════════════════════════════════════════════════════════════════
-- Eval tests
-- ═══════════════════════════════════════════════════════════════════
--
-- CoreFE parser syntax reference (from lexer):
--   Types:    Int, Bool, String  (capitalized keywords)
--   Vars:     x0, x1, x2, ...   (de Bruijn indices)
--   Lambda:   lam. body
--   TLambda:  Lam. body
--   App:      f arg              (juxtaposition, left-assoc)
--   TApp:     e @ T
--   Arith:    e1 - e2,  e1 ** e2  (** is multiply)
--   Eq:       e1 == e2
--   Record:   {l = e}
--   Proj:     e.l
--   Env:      [e1, e2, ...]  or  [tdef T, e1, ...]
--   Box:      [env] |> e
--   Closure:  <[env] | lam. body>
--   TClosure: <[env] | Lam. body>
--   Anno:     e : T
--   Fix:      fix e
--   If:       if e then e else e
--   TyEnv:    [*, Int, eq Int]  (Kind, Type, TypeEq)

evalTests :: [(String, String, Maybe Exp)]
evalTests =
  [ -- ── Literals ──────────────────────────────────────────────
    ( "int literal"
    , "42"
    , Just (Lit (LitInt 42))
    )
  , ( "bool literal true"
    , "true"
    , Just (Lit (LitBool True))
    )
  , ( "bool literal false"
    , "false"
    , Just (Lit (LitBool False))
    )
  , ( "string literal"
    , "\"hello\""
    , Just (Lit (LitStr "hello"))
    )

  -- ── Arithmetic ────────────────────────────────────────────
  , ( "subtraction"
    , "5 - 3"
    , Just (Lit (LitInt 2))
    )
  , ( "multiplication"
    , "4 ** 2"
    , Just (Lit (LitInt 8))
    )
  , ( "precedence: parens needed for grouping"
    , "(10 - 3) ** 2"
    , Just (Lit (LitInt 14))
    )

  -- ── Boolean / Conditionals ────────────────────────────────
  , ( "equality true"
    , "1 == 1"
    , Just (Lit (LitBool True))
    )
  , ( "equality false"
    , "1 == 2"
    , Just (Lit (LitBool False))
    )
  , ( "inequality true"
    , "1 != 2"
    , Just (Lit (LitBool True))
    )
  , ( "less than"
    , "1 < 2"
    , Just (Lit (LitBool True))
    )
  , ( "less than or equal"
    , "2 <= 2"
    , Just (Lit (LitBool True))
    )
  , ( "greater than"
    , "3 > 2"
    , Just (Lit (LitBool True))
    )
  , ( "greater than or equal"
    , "3 >= 3"
    , Just (Lit (LitBool True))
    )
  , ( "if-then-else true branch"
    , "if true then 1 else 0"
    , Just (Lit (LitInt 1))
    )
  , ( "if-then-else false branch"
    , "if false then 1 else 0"
    , Just (Lit (LitInt 0))
    )
  , ( "if with equality condition"
    , "if 3 == 3 then 42 else 0"
    , Just (Lit (LitInt 42))
    )

  -- ── Lambda and Application ────────────────────────────────
  , ( "identity function"
    , "(lam. x0) 5"
    , Just (Lit (LitInt 5))
    )
  , ( "lambda with subtraction"
    , "(lam. x0 - 1) 5"
    , Just (Lit (LitInt 4))
    )
  , ( "K combinator: returns first arg"
    , "((lam. lam. x1) 42) 99"
    , Just (Lit (LitInt 42))
    )
  , ( "lambda applied to itself squared"
    , "(lam. x0 ** x0) 3"
    , Just (Lit (LitInt 9))
    )

  -- ── Closures ──────────────────────────────────────────────
  , ( "empty closure application"
    , "<[] | lam. x0 - 1> 10"
    , Just (Lit (LitInt 9))
    )
  , ( "closure captures value from env"
    , "<[3] | lam. x0 ** x1> 10"
    , Just (Lit (LitInt 30))
    )

  -- ── Records ───────────────────────────────────────────────
  , ( "record creation"
    , "{x = 42}"
    , Just (Rec "x" (Lit (LitInt 42)))
    )
  -- Note: {x = 42}.x does NOT work because e.l requires e : Env.
  -- Must wrap in env: [{x = 42}].x
  , ( "record projection via env"
    , "[{x = 42}].x"
    , Just (Lit (LitInt 42))
    )
  , ( "nested record projection"
    , "[{a = [{b = 99}]}].a.b"
    , Just (Lit (LitInt 99))
    )

  -- ── Environments ──────────────────────────────────────────
  , ( "empty env"
    , "[]"
    , Just (FEnv [])
    )
  , ( "single-element env"
    , "[5]"
    , Just (FEnv [ExpE (Lit (LitInt 5))])
    )

  -- ── Box ───────────────────────────────────────────────────
  , ( "box projects from env"
    , "[{x = 10}] |> [x0].x"
    , Just (Lit (LitInt 10))
    )
  , ( "box with function application"
    , "[lam. x0 - 1, 10] |> (x1 x0)"
    , Just (Lit (LitInt 9))
    )

  -- ── Type Abstraction / Application ────────────────────────
  , ( "polymorphic identity at Int"
    , "((Lam. lam. x0) @ Int) 42"
    , Just (Lit (LitInt 42))
    )
  , ( "polymorphic identity at Bool"
    , "((Lam. lam. x0) @ Bool) true"
    , Just (Lit (LitBool True))
    )

  -- ── Annotation (erased at eval) ───────────────────────────
  , ( "annotation erased during eval"
    , "42 : Int"
    , Just (Lit (LitInt 42))
    )
  , ( "annotated lambda application"
    , "((lam. x0) : Int -> Int) 7"
    , Just (Lit (LitInt 7))
    )

  -- ── Higher-Order ──────────────────────────────────────────
  , ( "apply function twice"
    , "(lam. (x0) ((x0) 5)) (lam. x0 - 1)"
    , Just (Lit (LitInt 3))
    )
  ]

checkTests :: [(String, String, String, Bool)]
checkTests =
  [ ( "int literal checks as Int"
    , "42"
    , "Int"
    , True
    )
  , ( "bool literal checks as Bool"
    , "true"
    , "Bool"
    , True
    )
  , ( "string literal checks as String"
    , "\"hi\""
    , "String"
    , True
    )
  , ( "int does NOT check as Bool"
    , "42"
    , "Bool"
    , False
    )
  , ( "identity on Int"
    , "lam. x0"
    , "Int -> Int"
    , True
    )
  , ( "constant function"
    , "lam. 42"
    , "Bool -> Int"
    , True
    )
  , ( "wrong return type fails"
    , "lam. 42"
    , "Int -> Bool"
    , False
    )
  , ( "polymorphic identity"
    , "Lam. lam. x0"
    , "forall. 0 -> 0"
    , True
    )
  , ( "record checks"
    , "{x = 42}"
    , "{x : Int}"
    , True
    )
  , ( "record wrong field type fails"
    , "{x = true}"
    , "{x : Int}"
    , False
    )
  , ( "annotated expression"
    , "42 : Int"
    , "Int"
    , True
    )
  , ( "less-than returns Bool"
    , "1 < 2"
    , "Bool"
    , True
    )
  , ( "greater-than-or-equal returns Bool"
    , "3 >= 2"
    , "Bool"
    , True
    )
  , ( "empty closure checks as box arrow"
    , "<[] | lam. x0 - 1>"
    , "[] |> (Int -> Int)"
    , True
    )
  , ( "closure with captured value"
    , "<[5] | lam. x0 ** x1>"
    , "[Int] |> (Int -> Int)"
    , True
    )
  ]


inferTests :: [(String, String, Typ)]
inferTests =
  [ ( "infer int literal"
    , "42"
    , TyLit TyInt
    )
  , ( "infer bool literal"
    , "true"
    , TyLit TyBool
    )
  , ( "infer string literal"
    , "\"hi\""
    , TyLit TyStr
    )
  , ( "infer subtraction"
    , "5 - 3"
    , TyLit TyInt
    )
  , ( "infer multiplication"
    , "4 ** 2"
    , TyLit TyInt
    )
  , ( "infer equality"
    , "1 == 2"
    , TyLit TyBool
    )
  , ( "infer record"
    , "{x = 42}"
    , TyRcd "x" (TyLit TyInt)
    )
  , ( "infer nested record"
    , "{x = {y = 1}}"
    , TyRcd "x" (TyRcd "y" (TyLit TyInt))
    )
  ]

inferCtxTests :: [(String, String, String, Typ)]
inferCtxTests =
  [ ( "var in singleton context"
    , "[Int]"
    , "x0"
    , TyLit TyInt
    )
  , ( "var in two-element context"
    , "[Bool, Int]"
    , "x1"
    , TyLit TyBool
    )
  , ( "type equality is transparent to var lookup"
    , "[eq Int, Bool]"
    , "x0"
    , TyLit TyBool
    )
  , ( "application in context"
    , "[Int -> Bool, Int]"
    , "x1 x0"
    , TyLit TyBool
    )
  , ( "record projection in context"
    , "[Env[{x : Int}]]"
    , "x0.x"
    , TyLit TyInt
    )
  ]

checkCtxTests :: [(String, String, String, String, Bool)]
checkCtxTests =
  [ ( "lambda uses outer var"
    , "[Int]"
    , "lam. x0 - x1"
    , "Int -> Int"
    , True
    )
  , ( "polymorphic identity in empty context"
    , "[]"
    , "Lam. lam. x0"
    , "forall. 0 -> 0"
    , True
    )
  ]

typEqTests :: [(String, String, String, String, String, Bool)]
typEqTests =
  [ -- ═══════════════════════════════════════════════════════════
    -- BASIC LITERAL EQUALITY
    -- ═══════════════════════════════════════════════════════════
    ( "Int = Int"
    , "[]", "Int", "Int", "[]"
    , True
    )
  , ( "Bool = Bool"
    , "[]", "Bool", "Bool", "[]"
    , True
    )
  , ( "String = String"
    , "[]", "String", "String", "[]"
    , True
    )
  , ( "Int /= Bool"
    , "[]", "Int", "Bool", "[]"
    , False
    )
  , ( "Int /= String"
    , "[]", "Int", "String", "[]"
    , False
    )
  , ( "Int /= Arrow"
    , "[]", "Int", "Int -> Int", "[]"
    , False
    )

    -- ═══════════════════════════════════════════════════════════
    -- TYPE VARIABLES (de Bruijn indices)
    -- ═══════════════════════════════════════════════════════════
  , ( "type var same index, same context"
    , "[*]", "0", "0", "[*]"
    , True
    )
  , ( "type var in larger context"
    , "[*, *]", "0", "0", "[*, *]"
    , True
    )
  , ( "type var index 1 in two-element context"
    , "[*, *]", "1", "1", "[*, *]"
    , True
    )
  , ( "type vars with different indices"
    , "[*, *]", "0", "1", "[*, *]"
    , False
    )
  , ( "Evar (Type) is skipped for inner index"
    , "[*, Int]", "0", "0", "[*]"
    , True
    )
  , ( "multiple Evars skipped"
    , "[*, Int, Bool, Int]", "0", "0", "[*]"
    , True
    )

    -- ═══════════════════════════════════════════════════════════
    -- ARROW TYPES
    -- ═══════════════════════════════════════════════════════════
  , ( "Int -> Int = Int -> Int"
    , "[]", "Int -> Int", "Int -> Int", "[]"
    , True
    )
  , ( "arrow with type var"
    , "[*]", "0 -> Int", "0 -> Int", "[*]"
    , True
    )
  , ( "arrow domain mismatch"
    , "[]", "Int -> Int", "Bool -> Int", "[]"
    , False
    )
  , ( "arrow codomain mismatch"
    , "[]", "Int -> Int", "Int -> Bool", "[]"
    , False
    )
  , ( "arrow arity mismatch"
    , "[]", "Int -> Int", "Int -> Int -> Int", "[]"
    , False
    )
  , ( "nested arrows"
    , "[]", "(Int -> Int) -> Int", "(Int -> Int) -> Int", "[]"
    , True
    )
  , ( "curried function"
    , "[]", "Int -> Int -> Int", "Int -> Int -> Int", "[]"
    , True
    )

    -- ═══════════════════════════════════════════════════════════
    -- FORALL TYPES
    -- ═══════════════════════════════════════════════════════════
  , ( "forall identity"
    , "[]", "forall. 0", "forall. 0", "[]"
    , True
    )
  , ( "forall arrow"
    , "[]", "forall. 0 -> 0", "forall. 0 -> 0", "[]"
    , True
    )
  , ( "forall extends context"
    , "[*]", "forall. 1", "forall. 1", "[*]"
    , True
    )
  , ( "nested forall"
    , "[]", "forall. forall. 0 -> 1", "forall. forall. 0 -> 1", "[]"
    , True
    )
  , ( "forall with concrete return"
    , "[]", "forall. Int", "forall. Int", "[]"
    , True
    )
  , ( "forall body mismatch"
    , "[]", "forall. 0", "forall. Int", "[]"
    , False
    )

    -- ═══════════════════════════════════════════════════════════
    -- TYPE EQUALITY (TypeEq / Eteq)
    -- ═══════════════════════════════════════════════════════════
  , ( "Eteq unfolds: 0 in [eq Int] = Int"
    , "[eq Int]", "0", "Int", "[]"
    , True
    )
  , ( "Eteq unfolds arrow type"
    , "[eq Int -> Int]", "0", "Int -> Int", "[]"
    , True
    )
  , ( "Eteq on right side"
    , "[]", "Int", "0", "[eq Int]"
    , True
    )
  , ( "Eteq both sides"
    , "[eq Int]", "0", "0", "[eq Int]"
    , True
    )
  , ( "nested Eteq unfolding"
    , "[eq Int, eq 0]", "0", "Int", "[]"
    , True
    )
  , ( "Eteq chain: 0 -> 1 -> Int"
    , "[eq Int, eq 0]", "0", "1", "[eq Int, eq 0]"
    , True
    )

    -- ═══════════════════════════════════════════════════════════
    -- SUBSTITUTION TYPES (SubstT / #[A]B)
    -- ═══════════════════════════════════════════════════════════
  , ( "subst basic: #[Int]0 = Int"
    , "[]", "#[Int]0", "Int", "[]"
    , True
    )
  , ( "subst on right: Int = #[Int]0"
    , "[]", "Int", "#[Int]0", "[]"
    , True
    )
  , ( "subst arrow: #[Int](0 -> 0) = Int -> Int"
    , "[]", "#[Int](0 -> 0)", "Int -> Int", "[]"
    , True
    )
  , ( "subst in function domain"
    , "[]", "#[Int]0 -> Bool", "Int -> Bool", "[]"
    , True
    )
  , ( "subst preserves outer var"
    , "[]", "#[Int]0", "Int", "[]"
    , True
    )
  , ( "subst in Eteq binding"
    , "[eq #[Int]0]", "0", "Int", "[]"
    , True
    )

    -- ═══════════════════════════════════════════════════════════
    -- BOX TYPES (BoxT / [env] |> A)
    -- ═══════════════════════════════════════════════════════════
  , ( "empty box: [] |> Int = Int"
    , "[]", "[] |> Int", "Int", "[]"
    , True
    )
  , ( "box with Eteq: [eq Int] |> 0 = Int"
    , "[]", "[eq Int] |> 0", "Int", "[]"
    , True
    )
  , ( "box on right"
    , "[]", "Int", "[eq Int] |> 0", "[]"
    , True
    )
  , ( "box multi-entry: [eq Int, eq 0] |> 0 = Int"
    , "[]", "[eq Int, eq 0] |> 0", "Int", "[]"
    , True
    )
  , ( "box multi-entry index 1"
    , "[]", "[eq Int, eq 0] |> 1", "Int", "[]"
    , True
    )
  , ( "box with arrow in Eteq"
    , "[]", "[eq Int, eq (0 -> 0)] |> 0", "Int -> Int", "[]"
    , True
    )
  , ( "box complex: [eq Int, eq (Int -> Int)] |> 0 -> 1"
    , "[]", "[eq Int, eq (Int -> Int)] |> 0 -> 1", "(Int -> Int) -> Int", "[]"
    , True
    )
  , ( "box triple Eteq"
    , "[]", "[eq Int, eq 0, eq 1] |> 0", "Int", "[]"
    , True
    )

    -- ═══════════════════════════════════════════════════════════
    -- BOX WITH NON-CONCRETE ENV (should fail)
    -- ═══════════════════════════════════════════════════════════
  , ( "box with Kind fails"
    , "[]", "[*] |> 0", "0", "[*]"
    , False
    )
  , ( "box with Kind after Eteq fails"
    , "[]", "[*, eq Int] |> 0", "Int", "[]"
    , False
    )
  , ( "box with Kind before Eteq fails"
    , "[]", "[eq Int, *] |> 1", "Int", "[]"
    , False
    )

    -- ═══════════════════════════════════════════════════════════
    -- RECORD TYPES
    -- ═══════════════════════════════════════════════════════════
  , ( "record same label and type"
    , "[]", "{x : Int}", "{x : Int}", "[]"
    , True
    )
  , ( "record different label"
    , "[]", "{x : Int}", "{y : Int}", "[]"
    , False
    )
  , ( "record different type"
    , "[]", "{x : Int}", "{x : Bool}", "[]"
    , False
    )
  , ( "record with type var"
    , "[*]", "{val : 0}", "{val : 0}", "[*]"
    , True
    )
  , ( "record with arrow type"
    , "[]", "{f : Int -> Int}", "{f : Int -> Int}", "[]"
    , True
    )

    -- ═══════════════════════════════════════════════════════════
    -- ENVIRONMENT TYPES (TyEnvt / Env[...])
    -- ═══════════════════════════════════════════════════════════
  , ( "empty env type"
    , "[]", "Env[]", "Env[]", "[]"
    , True
    )
  , ( "env with Kind"
    , "[]", "Env[*]", "Env[*]", "[]"
    , True
    )
  , ( "env with Type"
    , "[]", "Env[Int]", "Env[Int]", "[]"
    , True
    )
  , ( "env with Kind and Type"
    , "[]", "Env[0, *]", "Env[0, *]", "[]"
    , True
    )
  , ( "env with multiple entries"
    , "[]", "Env[Int, Bool]", "Env[Int, Bool]", "[]"
    , True
    )
  , ( "env order matters"
    , "[]", "Env[Int, Bool]", "Env[Bool, Int]", "[]"
    , False
    )
  , ( "env with record"
    , "[]", "Env[{x : Int}]", "Env[{x : Int}]", "[]"
    , True
    )

    -- ═══════════════════════════════════════════════════════════
    -- COMPLEX / COMBINED CASES
    -- ═══════════════════════════════════════════════════════════
  , ( "complex module-like type"
    , "[]"
    , "Env[eq Int, {x : 0}]"
    , "Env[eq Int, {x : 0}]"
    , "[]"
    , True
    )
  , ( "functor-like type"
    , "[]"
    , "forall. Env[{x : 0}] -> Env[{y : 0}]"
    , "forall. Env[{x : 0}] -> Env[{y : 0}]"
    , "[]"
    , True
    )
  , ( "asymmetric contexts with same inner index"
    , "[*, eq Int]", "1", "1", "[*, *]"
    , False
    )
  , ( "box in subst"
    , "[]", "[eq ([] |> Int)] |> 0", "Int", "[]"
    , True
    )
  ]


spec :: Spec
spec = do
  describe "CoreFE.Eval" $
    describe "evaluation" $
      mapM_ mkEvalTest evalTests

  describe "CoreFE.Check" $ do
    describe "type checking" $
      mapM_ mkCheckTest checkTests
    describe "type inference" $
      mapM_ mkInferTest inferTests
    describe "inference in context" $
      mapM_ mkInferCtxTest inferCtxTests
    describe "checking in context" $
      mapM_ mkCheckCtxTest checkCtxTests
  
  describe "CoreFE Type Equality checking" $ do
    mapM_ mkTypEqTest typEqTests

  describe "CoreFE explicit isorecursive terms" $ do
    it "types fold into recursive type" $ do
      let natTy = TyMu (TySum [("Z", TyLit TyBool), ("S", TyVar 0)])
      let zVal = DataCon "Z" (Lit (LitBool True))
      infer [] (Fold natTy zVal) `shouldBe` Just natTy

    it "types and evaluates explicit unfold for case analysis" $ do
      let natTy = TyMu (TySum [("Z", TyLit TyBool), ("S", TyVar 0)])
      let scrutinee = Unfold (Fold natTy (DataCon "Z" (Lit (LitBool True))))
      let expr =
            Case
              scrutinee
              [ CaseBranch "Z" (Lit (LitInt 1))
              , CaseBranch "S" (Lit (LitInt 0))
              ]
      infer [] expr `shouldBe` Just (TyLit TyInt)

    it "uses wildcard case branch as fallback" $ do
      let natTy = TyMu (TySum [("Z", TyLit TyBool), ("S", TyVar 0)])
      let scrutinee = Unfold (Fold natTy (DataCon "S" (Fold natTy (DataCon "Z" (Lit (LitBool True))))))
      let expr =
            Case
              scrutinee
              [ CaseBranch "Z" (Lit (LitInt 1))
              , CaseBranch "_" (Lit (LitInt 0))
              ]
      infer [] expr `shouldBe` Just (TyLit TyInt)
      eval [] expr `shouldBe` Just (Lit (LitInt 0))

    it "types explicit unfold of recursive function type at application" $ do
      let muArrow = TyMu (TyArr (TyLit TyInt) (TyLit TyInt))
      let funVal = Fold muArrow (Lam (Var 0))
      let expr = App (Unfold funVal) (Lit (LitInt 1))
      check [] expr (TyLit TyInt) `shouldBe` True

  where
    mkEvalTest (name, src, expected) =
      it name $
        evalP src `shouldBe` expected

    mkCheckTest (name, expr, typ, expected) =
      it name $
        checkP expr typ `shouldBe` expected

    mkInferTest (name, src, expected) =
      it name $
        inferP src `shouldBe` Just expected

    mkInferCtxTest (name, env, src, expected) =
      it name $
        inferInCtx env src `shouldBe` Just expected

    mkCheckCtxTest (name, env, expr, typ, expected) =
      it name $
        checkInCtx env expr typ `shouldBe` expected
    
    mkTypEqTest (name, g1Str, aStr, bStr, g2Str, expected) =
      it name $
        isTypEq g1Str aStr bStr g2Str `shouldBe` expected