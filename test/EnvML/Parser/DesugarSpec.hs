module EnvML.Parser.DesugarSpec (spec) where

import EnvML.Parser.AST
import EnvML.Parser.HappyAlex.Lexer (lexer)
import EnvML.Parser.HappyAlex.Parser (parseExp, parseModule, parseModuleTyp, parseTyp)
import EnvML.Desugar
import EnvML.Parser.Pretty
import Test.Hspec

spec :: Spec
spec = do
  describe "Desugar Expressions" $ do
    mapM_ mkExpDesugarTest expDesugarTests

  describe "Desugar Types" $ do
    mapM_ mkTypDesugarTest typDesugarTests

  describe "Desugar Modules" $ do
    mapM_ mkModuleDesugarTest moduleDesugarTests

  describe "Desugar Interfaces" $ do
    mapM_ mkIntfDesugarTest intfDesugarTests

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
  
  , -- Lambda with type and term args
    ( "fun (type a) (x : int) -> x"
    , Lam [("a", TyArg)]
          (Lam [("x", TmArgType (TyLit TyInt))]
               (Var "x"))
    )
  
  , -- Closure with multi-arg gets desugared
    ( "clos [x = 1] (y : int) (z : int) -> y"
    , Clos [ExpEN "x" (Lit (LitInt 1))]
           []
           (Lam [("y", TmArgType (TyLit TyInt))]
                (Lam [("z", TmArgType (TyLit TyInt))]
                     (Var "y")))
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
  
  , -- Box with nested lambda
    ( "box [type t = int] in fun (x : int) -> x"
    , Box [TypEN "t" (TyLit TyInt)]
          (Lam [("x", TmArgType (TyLit TyInt))]
               (Var "x"))
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
  
  , -- Forall type
    ( "forall a. a -> a"
    , TyAll "a" (TyArr (TyVar "a") (TyVar "a"))
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
  ]

-- Module desugaring tests
moduleDesugarTests :: [(String, Module)]
moduleDesugarTests =
  [ -- Multi-arg functor desugaring
    ( "import M : int;; \
      \module F = functor (x : int) (y : int) -> struct end;;"
    , Struct [("M", TyLit TyInt)]
             [ModE "F" (Functor [("x", TmArgType (TyLit TyInt))]
                                (Functor [("y", TmArgType (TyLit TyInt))]
                                         (Struct [] [])))]
    )
  
  , -- Functor with type arg
    ( "module F = functor (type t) (x : int) -> struct end;;"
    , Struct []
             [ModE "F" (Functor [("t", TyArg)]
                                (Functor [("x", TmArgType (TyLit TyInt))]
                                         (Struct [] [])))]
    )
  
  , -- Simple struct
    ( "let x = 1;;"
    , Struct [] [ExpEN "x" (Lit (LitInt 1))]
    )
  
  , -- Struct with multiple bindings
    ( "let x = 1;; type t = int;;"
    , Struct [] [ ExpEN "x" (Lit (LitInt 1))
                , TypEN "t" (TyLit TyInt)
                ]
    )
  ]

-- Interface desugaring tests
intfDesugarTests :: [(String, ModuleTyp)]
intfDesugarTests =
  [ -- FunctorDecl gets desugared to ModDecl with nested types
    ( "functor F (x : int) : sig end;;"
    , TySig [ModDecl "F" (TyArrowM (TyLit TyInt) (TySig []))]
    )
  
  , -- Multi-arg functor declaration
    ( "functor F (x : int) (y : int) : sig end;;"
    , TySig [ModDecl "F" (TyArrowM (TyLit TyInt)
                                   (TyArrowM (TyLit TyInt)
                                            (TySig [])))]
    )
  
  , -- Functor with type argument
    ( "functor F (type t) (x : int) : sig end;;"
    , TySig [ModDecl "F" (ForallM "t"
                                  (TyArrowM (TyLit TyInt)
                                           (TySig [])))]
    )
  
  , -- Mixed type and term arguments
    ( "functor F (type t) (type u) (x : int) : sig end;;"
    , TySig [ModDecl "F" (ForallM "t"
                                  (ForallM "u"
                                           (TyArrowM (TyLit TyInt)
                                                    (TySig []))))]
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
  describe "Full Pipeline Tests" $ do
    it "desugars complex nested lambda" $ do
      let input = "fun (f : int -> int) (x : int) (y : int) -> f(x)"
      let parsed = parseExp (lexer input)
      let desugared = desugarExp parsed
      let expected = Lam [("f", TmArgType (TyArr (TyLit TyInt) (TyLit TyInt)))]
                         (Lam [("x", TmArgType (TyLit TyInt))]
                              (Lam [("y", TmArgType (TyLit TyInt))]
                                   (App (Var "f") (Var "x"))))
      desugared `shouldBe` expected

    it "desugars closure with multi-arg lambda body" $ do
      let input = "clos [x = 1] (f : int) (g : int) -> f"
      let parsed = parseExp (lexer input)
      let desugared = desugarExp parsed
      let expected = Clos [ExpEN "x" (Lit (LitInt 1))]
                          []
                          (Lam [("f", TmArgType (TyLit TyInt))]
                               (Lam [("g", TmArgType (TyLit TyInt))]
                                    (Var "f")))
      desugared `shouldBe` expected

    it "desugars functor in module" $ do
      let input = "module MakePair = functor (type t) (x : t) -> struct end;;"
      let parsed = parseModule (lexer input)
      let desugared = desugarModule parsed
      let expected = Struct []
                            [ModE "MakePair"
                                  (Functor [("t", TyArg)]
                                           (Functor [("x", TmArgType (TyVar "t"))]
                                                    (Struct [] [])))]
      desugared `shouldBe` expected

    it "pretty prints desugared expression correctly" $ do
      let input = "fun (x : int) (y : int) -> x"
      let parsed = parseExp (lexer input)
      let desugared = desugarExp parsed
      let prettied = prettyExp desugared
      prettied `shouldBe` "fun (x : int) -> fun (y : int) -> x"

    it "round-trips parse -> desugar -> pretty" $ do
      let input = "fun (x : int) (y : int) -> x"
      let parsed = parseExp (lexer input)
      let desugared = desugarExp parsed
      let prettied = prettyExp desugared
      let reparsed = parseExp (lexer prettied)
      -- After desugaring, it should parse to nested lambdas
      reparsed `shouldBe` desugared

-- Add these to the spec
spec3 :: Spec
spec3 = do
  describe "Desugar Idempotence" $ do
    it "desugaring twice gives same result for lambdas" $ do
      let input = "fun (x : int) (y : int) -> x"
      let parsed = parseExp (lexer input)
      let desugared1 = desugarExp parsed
      let desugared2 = desugarExp desugared1
      desugared1 `shouldBe` desugared2

    it "desugaring twice gives same result for functors" $ do
      let input = "functor (x : int) (y : int) : sig end;;"
      let parsed = parseModuleTyp (lexer input)
      let desugared1 = desugarModuleTyp parsed
      let desugared2 = desugarModuleTyp desugared1
      desugared1 `shouldBe` desugared2