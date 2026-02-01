module EnvML.Parser.DesugarSpec (spec) where

import EnvML.Parser.AST
import EnvML.Parser.Lexer (lexer)
import EnvML.Parser.Parser (parseExp, parseModule, parseModuleTyp, parseTyp)
import EnvML.Desugar
import Test.Hspec

spec :: Spec
spec = do
  describe "Desugar Expressions" $ do
    mapM_ mkExpDesugarTest expDesugarTests

  describe "Desugar Type Lambdas vs Term Lambdas" $ do
    mapM_ mkExpDesugarTest lamTlamTests

  describe "Desugar Types" $ do
    mapM_ mkTypDesugarTest typDesugarTests

  describe "Desugar Modules" $ do
    mapM_ mkModuleDesugarTest moduleDesugarTests

  describe "Desugar Functors" $ do
    mapM_ mkModuleDesugarTest functorTests

  describe "Desugar Interfaces" $ do
    mapM_ mkIntfDesugarTest intfDesugarTests

  describe "Full Pipeline Tests" $ do
    spec2

  describe "Idempotence Tests" $ do
    spec3

-- Test helpers
mkExpDesugarTest :: (String, Exp) -> SpecWith ()
mkExpDesugarTest (input, expected) =
  it ("desugars: " ++ input) $ do
    let parsed = parseExp (lexer input)
    let desugared = desugarExp parsed
    desugared `shouldBe` expected

mkTypDesugarTest :: (String, Typ) -> SpecWith ()
mkTypDesugarTest (input, expected) =
  it ("desugars type: " ++ input) $ do
    let parsed = parseTyp (lexer input)
    let desugared = desugarTyp parsed
    desugared `shouldBe` expected

mkModuleDesugarTest :: (String, Module) -> SpecWith ()
mkModuleDesugarTest (input, expected) =
  it ("desugars module: " ++ input) $ do
    let parsed = parseModule (lexer input)
    let desugared = desugarModule parsed
    desugared `shouldBe` expected

mkIntfDesugarTest :: (String, ModuleTyp) -> SpecWith ()
mkIntfDesugarTest (input, expected) =
  it ("desugars interface: " ++ input) $ do
    let parsed = parseModuleTyp (lexer input)
    let desugared = desugarModuleTyp parsed
    desugared `shouldBe` expected

-- Expression desugaring tests
expDesugarTests :: [(String, Exp)]
expDesugarTests =
  [ -- Multi-arg lambda desugaring
    ( "fun (x : int) (y : int) -> x"
    , Lam [("x", TmArgType (TyLit TyInt))]
          (Lam [("y", TmArgType (TyLit TyInt))]
               (Var "x"))
    )
  
  , -- Triple-arg lambda
    ( "fun (x : int) (y : int) (z : int) -> z"
    , Lam [("x", TmArgType (TyLit TyInt))]
          (Lam [("y", TmArgType (TyLit TyInt))]
               (Lam [("z", TmArgType (TyLit TyInt))]
                    (Var "z")))
    )
  
  , -- Simple record stays as is
    ( "{x = 1}"
    , Rec [("x", Lit (LitInt 1))]
    )
  
  , -- Multi-field record stays as is
    ( "{x = 1, y = 2}"
    , Rec [("x", Lit (LitInt 1)), ("y", Lit (LitInt 2))]
    )
  
  , -- Nested expressions get desugared
    ( "fun (f : int) -> f(1)"
    , Lam [("f", TmArgType (TyLit TyInt))]
          (App (Var "f") (Lit (LitInt 1)))
    )
  
  , -- Binary operations stay as is
    ( "1 + 2"
    , BinOp (Add (Lit (LitInt 1)) (Lit (LitInt 2)))
    )
  
  , -- Nested binary operations
    ( "(1 + 2) + 3"
    , BinOp (Add (BinOp (Add (Lit (LitInt 1)) (Lit (LitInt 2))))
                 (Lit (LitInt 3)))
    )
  ]

-- CRITICAL: TLam vs Lam distinction tests
lamTlamTests :: [(String, Exp)]
lamTlamTests =
  [ -- Single type argument -> TLam
    ( "fun (type a) -> x"
    , TLam [("a", TyArg)] (Var "x")
    )
  
  , -- Type arg followed by term arg -> TLam then Lam
    ( "fun (type a) (x : int) -> x"
    , TLam [("a", TyArg)]
           (Lam [("x", TmArgType (TyLit TyInt))]
                (Var "x"))
    )
  
  , -- Term arg followed by type arg -> Lam then TLam
    ( "fun (x : int) (type a) -> x"
    , Lam [("x", TmArgType (TyLit TyInt))]
          (TLam [("a", TyArg)]
                (Var "x"))
    )
  
  , -- Multiple type args
    ( "fun (type a) (type b) -> x"
    , TLam [("a", TyArg)]
           (TLam [("b", TyArg)]
                 (Var "x"))
    )
  
  , -- Type, term, type interleaved
    ( "fun (type a) (x : int) (type b) -> x"
    , TLam [("a", TyArg)]
           (Lam [("x", TmArgType (TyLit TyInt))]
                (TLam [("b", TyArg)]
                      (Var "x")))
    )
  
  , -- Type arg with dependent term arg
    ( "fun (type t) (x : t) -> x"
    , TLam [("t", TyArg)]
           (Lam [("x", TmArgType (TyVar "t"))]
                (Var "x"))
    )
  
  , -- Closure with type args in body
    ( "clos [x = 1] (type a) (y : int) -> y"
    , Clos [ExpEN "x" (Lit (LitInt 1))]
           []
           (TLam [("a", TyArg)]
                 (Lam [("y", TmArgType (TyLit TyInt))]
                      (Var "y")))
    )
  
  , -- TClos with type args in body
    ( "clos [type t = int] (type a) (y : t) -> y"
    , Clos [TypEN "t" (TyLit TyInt)]
            []
            (TLam [("a", TyArg)]
                  (Lam [("y", TmArgType (TyVar "t"))]
                       (Var "y")))
    )
  
  , -- Box with TLam inside
    ( "box [type t = int] in fun (type a) (x : t) -> x"
    , Box [TypEN "t" (TyLit TyInt)]
          (TLam [("a", TyArg)]
                (Lam [("x", TmArgType (TyVar "t"))]
                     (Var "x")))
    )
  
  , -- Nested TLam and Lam with annotation
    ( "fun (type a) (x : a) -> (x :: a)"
    , TLam [("a", TyArg)]
           (Lam [("x", TmArgType (TyVar "a"))]
                (Anno (Var "x") (TyVar "a")))
    )
  ]

-- Type desugaring tests
typDesugarTests :: [(String, Typ)]
typDesugarTests =
  [ -- Simple types stay as is
    ( "int"
    , TyLit TyInt
    )
  
  , -- Arrow types stay as is
    ( "int -> int"
    , TyArr (TyLit TyInt) (TyLit TyInt)
    )
  
  , -- Multi-field record type
    ( "{x : int, y : bool}"
    , TyRcd [("x", TyLit TyInt), ("y", TyLit TyBool)]
    )
  
  , -- Nested record types
    ( "{x : {y : int}}"
    , TyRcd [("x", TyRcd [("y", TyLit TyInt)])]
    )
  
  , -- Box type with context
    ( "[type t = int] ===> t"
    , TyBoxT [TypeEqN "t" (TyLit TyInt)] (TyVar "t")
    )
  
  , -- Box type with multiple bindings
    ( "[type t = int, type u = bool] ===> t"
    , TyBoxT [TypeEqN "t" (TyLit TyInt), TypeEqN "u" (TyLit TyBool)] (TyVar "t")
    )
  
  , -- Forall type
    ( "forall a. a -> a"
    , TyAll "a" (TyArr (TyVar "a") (TyVar "a"))
    )
  
  , -- Nested forall
    ( "forall a. forall b. a -> b"
    , TyAll "a" (TyAll "b" (TyArr (TyVar "a") (TyVar "b")))
    )
  
  , -- Module type with signature
    ( "sig val x : int;; end"
    , TyModule (TySig [ValDecl "x" (TyLit TyInt)])
    )
  
  , -- Module arrow type
    ( "int ->m sig end"
    , TyModule (TyArrowM (TyLit TyInt) (TySig []))
    )
  
  , -- Forall module type
    ( "forall t. sig end"
    , TyModule (ForallM "t" (TySig []))
    )
  
  , -- Nested module arrow types
    ( "int ->m int ->m sig end"
    , TyModule (TyArrowM (TyLit TyInt)
                         (TyArrowM (TyLit TyInt)
                                   (TySig [])))
    )
  ]

-- Module desugaring tests
moduleDesugarTests :: [(String, Module)]
moduleDesugarTests =
  [ -- Simple struct
    ( "let x = 1;;"
    , Struct [] [ExpEN "x" (Lit (LitInt 1))]
    )
  
  , -- Struct with multiple bindings
    ( "let x = 1;; type t = int;;"
    , Struct [] [ ExpEN "x" (Lit (LitInt 1))
                , TypEN "t" (TyLit TyInt)
                ]
    )
  
  , -- Struct with imports
    ( "import M : int;; let x = 1;;"
    , Struct [("M", TyLit TyInt)]
             [ExpEN "x" (Lit (LitInt 1))]
    )
  
  , -- Multiple imports
    ( "import M : int, N : bool;; let x = 1;;"
    , Struct [("M", TyLit TyInt), ("N", TyLit TyBool)]
             [ExpEN "x" (Lit (LitInt 1))]
    )
  ]

-- Functor-specific tests (CRITICAL for Functor vs Functort)
functorTests :: [(String, Module)]
functorTests =
  [ -- Term functor (single arg)
    ( "module F = functor (x : int) -> struct end;;"
    , Struct []
             [ModE "F" (Functor [("x", TmArgType (TyLit TyInt))]
                                (Struct [] []))]
    )
  
  , -- Type functor (single arg) - stays as Functor, NOT Functort in source!
    ( "module F = functor (type t) -> struct end;;"
    , Struct []
             [ModE "F" (Functor [("t", TyArg)]
                                (Struct [] []))]
    )
  
  , -- Multi-arg functor (term args)
    ( "module F = functor (x : int) (y : int) -> struct end;;"
    , Struct []
             [ModE "F" (Functor [("x", TmArgType (TyLit TyInt))]
                                (Functor [("y", TmArgType (TyLit TyInt))]
                                         (Struct [] [])))]
    )
  
  , -- Multi-arg functor (type then term)
    ( "module F = functor (type t) (x : int) -> struct end;;"
    , Struct []
             [ModE "F" (Functor [("t", TyArg)]
                                (Functor [("x", TmArgType (TyLit TyInt))]
                                         (Struct [] [])))]
    )
  
  , -- Multi-arg functor (term then type)
    ( "module F = functor (x : int) (type t) -> struct end;;"
    , Struct []
             [ModE "F" (Functor [("x", TmArgType (TyLit TyInt))]
                                (Functor [("t", TyArg)]
                                         (Struct [] [])))]
    )
  
  , -- Multi-arg functor (all type args)
    ( "module F = functor (type t) (type u) -> struct end;;"
    , Struct []
             [ModE "F" (Functor [("t", TyArg)]
                                (Functor [("u", TyArg)]
                                         (Struct [] [])))]
    )
  
  , -- Functor with dependent types
    ( "module F = functor (type t) (x : t) -> struct end;;"
    , Struct []
             [ModE "F" (Functor [("t", TyArg)]
                                (Functor [("x", TmArgType (TyVar "t"))]
                                         (Struct [] [])))]
    )
  
  , -- Complex nested functor
    ( "module F = functor (type t) (type u) (x : t) (y : u) -> struct end;;"
    , Struct []
             [ModE "F" (Functor [("t", TyArg)]
                                (Functor [("u", TyArg)]
                                         (Functor [("x", TmArgType (TyVar "t"))]
                                                  (Functor [("y", TmArgType (TyVar "u"))]
                                                           (Struct [] [])))))]
    )
  ]

-- Interface desugaring tests
intfDesugarTests :: [(String, ModuleTyp)]
intfDesugarTests =
  [ -- FunctorDecl with term arg -> ModDecl with TyArrowM
    ( "functor F (x : int) : sig end;;"
    , TySig [ModDecl "F" (TyArrowM (TyLit TyInt) (TySig []))]
    )
  
  , -- FunctorDecl with type arg -> ModDecl with ForallM
    ( "functor F (type t) : sig end;;"
    , TySig [ModDecl "F" (ForallM "t" (TySig []))]
    )
  
  , -- Multi-arg functor declaration (term args)
    ( "functor F (x : int) (y : int) : sig end;;"
    , TySig [ModDecl "F" (TyArrowM (TyLit TyInt)
                                   (TyArrowM (TyLit TyInt)
                                            (TySig [])))]
    )
  
  , -- Multi-arg functor declaration (type then term)
    ( "functor F (type t) (x : int) : sig end;;"
    , TySig [ModDecl "F" (ForallM "t"
                                  (TyArrowM (TyLit TyInt)
                                           (TySig [])))]
    )
  
  , -- Multi-arg functor declaration (term then type)
    ( "functor F (x : int) (type t) : sig end;;"
    , TySig [ModDecl "F" (TyArrowM (TyLit TyInt)
                                   (ForallM "t" (TySig [])))]
    )
  
  , -- Multi-arg functor declaration (all type args)
    ( "functor F (type t) (type u) : sig end;;"
    , TySig [ModDecl "F" (ForallM "t"
                                  (ForallM "u" (TySig [])))]
    )
  
  , -- Functor with dependent type
    ( "functor F (type t) (x : t) : sig end;;"
    , TySig [ModDecl "F" (ForallM "t"
                                  (TyArrowM (TyVar "t")
                                           (TySig [])))]
    )
  
  , -- Simple interface stays as is
    ( "val x : int;;"
    , TySig [ValDecl "x" (TyLit TyInt)]
    )
  
  , -- Multiple declarations
    ( "val x : int;; type t = int;;"
    , TySig [ ValDecl "x" (TyLit TyInt)
            , TyDef "t" (TyLit TyInt)
            ]
    )
  
  , -- Nested signatures
    ( "module M : sig val x : int;; end;;"
    , TySig [ModDecl "M" (TySig [ValDecl "x" (TyLit TyInt)])]
    )
  ]

-- Additional integration tests
spec2 :: Spec
spec2 = do
  it "desugars complex nested lambda with types" $ do
    let input = "fun (type a) (f : a -> a) (x : a) -> f(x)"
    let parsed = parseExp (lexer input)
    let desugared = desugarExp parsed
    let expected = TLam [("a", TyArg)]
                        (Lam [("f", TmArgType (TyArr (TyVar "a") (TyVar "a")))]
                             (Lam [("x", TmArgType (TyVar "a"))]
                                  (App (Var "f") (Var "x"))))
    desugared `shouldBe` expected

  it "desugars closure with type lambda body" $ do
    let input = "clos [x = 1] (type t) (y : t) -> y"
    let parsed = parseExp (lexer input)
    let desugared = desugarExp parsed
    let expected = Clos [ExpEN "x" (Lit (LitInt 1))]
                        []
                        (TLam [("t", TyArg)]
                              (Lam [("y", TmArgType (TyVar "t"))]
                                   (Var "y")))
    desugared `shouldBe` expected

  it "desugars functor with mixed args" $ do
    let input = "module Pair = functor (type t) (type u) (x : t) (y : u) -> struct end;;"
    let parsed = parseModule (lexer input)
    let desugared = desugarModule parsed
    let expected = Struct []
                          [ModE "Pair"
                                (Functor [("t", TyArg)]
                                         (Functor [("u", TyArg)]
                                                  (Functor [("x", TmArgType (TyVar "t"))]
                                                           (Functor [("y", TmArgType (TyVar "u"))]
                                                                    (Struct [] [])))))]
    desugared `shouldBe` expected

  it "pretty prints TLam correctly" $ do
    let input = "fun (type a) (x : a) -> x"
    let parsed = parseExp (lexer input)
    let desugared = desugarExp parsed
    let prettied = prettyExp desugared
    prettied `shouldBe` "fun (type a) -> (fun (x : a) -> x)"

-- Idempotence tests
spec3 :: Spec
spec3 = do
  it "desugaring twice gives same result for term lambdas" $ do
    let input = "fun (x : int) (y : int) -> x"
    let parsed = parseExp (lexer input)
    let desugared1 = desugarExp parsed
    let desugared2 = desugarExp desugared1
    desugared1 `shouldBe` desugared2

  it "desugaring twice gives same result for type lambdas" $ do
    let input = "fun (type a) (x : a) -> x"
    let parsed = parseExp (lexer input)
    let desugared1 = desugarExp parsed
    let desugared2 = desugarExp desugared1
    desugared1 `shouldBe` desugared2

  it "desugaring twice gives same result for mixed lambdas" $ do
    let input = "fun (type a) (x : int) (type b) (y : b) -> x"
    let parsed = parseExp (lexer input)
    let desugared1 = desugarExp parsed
    let desugared2 = desugarExp desugared1
    desugared1 `shouldBe` desugared2