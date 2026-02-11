module CoreFE.CoreFESpec (spec) where

import CoreFE.Eval (eval)
import CoreFE.Check (infer, check)
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