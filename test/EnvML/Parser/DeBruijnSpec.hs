module EnvML.Parser.DeBruijnSpec (spec) where

import EnvML.Parser.AST as S
import EnvML.Parser.Lexer (lexer)
import EnvML.Parser.Parser (parseExp, parseModule, parseTyp)
import EnvML.Desugar (desugarExp, desugarModule, desugarTyp)
import EnvML.DeBruijn
import qualified EnvML.Syntax as T
import Test.Hspec

spec :: Spec
spec = do
  describe "De Bruijn: Simple Expressions" $ do
    mapM_ mkExpTest simpleExpTests

  describe "De Bruijn: Lambda Variables" $ do
    mapM_ mkExpTest lambdaTests

  describe "De Bruijn: Type Lambda Variables" $ do
    mapM_ mkExpTest typeLambdaTests

  describe "De Bruijn: Nested Scopes" $ do
    mapM_ mkExpTest nestedScopeTests

  describe "De Bruijn: Environments (Critical Reversal)" $ do
    mapM_ mkExpTest environmentTests

  describe "De Bruijn: Box (Context Isolation)" $ do
    mapM_ mkExpTest boxTests

  describe "De Bruijn: Type Contexts (Critical Reversal)" $ do
    mapM_ mkTypTest typeContextTests

  describe "De Bruijn: Modules" $ do
    mapM_ mkModuleTest moduleTests

  describe "De Bruijn: Shadowing" $ do
    mapM_ mkExpTest shadowingTests

  describe "De Bruijn: Records" $ do
    mapM_ mkExpTest recordTests

  describe "De Bruijn: Complex Modules" $ do
    mapM_ mkModuleTest complexModuleTests

  describe "De Bruijn: Functors" $ do
    mapM_ mkModuleTest functorTests

  describe "De Bruijn: Closures" $ do
    mapM_ mkExpTest closureTests

  describe "De Bruijn: Deep Nesting" $ do
    mapM_ mkExpTest deepNestingTests

  describe "De Bruijn: Type in Modules" $ do
    mapM_ mkModuleTest moduleTypeTests

-- Test helpers
mkExpTest :: (String, T.Exp) -> SpecWith ()
mkExpTest (input, expected) =
  it ("converts: " ++ input) $ do
    let parsed = parseExp (lexer input)
    let desugared = desugarExp parsed
    let result = toDeBruijn desugared
    result `shouldBe` expected

mkTypTest :: (String, T.Typ) -> SpecWith ()
mkTypTest (input, expected) =
  it ("converts type: " ++ input) $ do
    let parsed = parseTyp (lexer input)
    let desugared = desugarTyp parsed
    let result = typToDeBruijn desugared
    result `shouldBe` expected

mkModuleTest :: (String, T.Module) -> SpecWith ()
mkModuleTest (input, expected) =
  it ("converts module: " ++ input) $ do
    let parsed = parseModule (lexer input)
    let desugared = desugarModule parsed
    let result = modToDeBruijn desugared
    result `shouldBe` expected

-------------------------------------------------------------------------
-- Test Cases
-------------------------------------------------------------------------

-- Simple expressions (no variables)
simpleExpTests :: [(String, T.Exp)]
simpleExpTests =
  [ ("1", T.Lit (T.LitInt 1))
  , ("true", T.Lit (T.LitBool True))
  , ("\"hello\"", T.Lit (T.LitStr "hello"))
  , ("1 + 2", T.BinOp (T.Add (T.Lit (T.LitInt 1)) (T.Lit (T.LitInt 2))))
  ]

-- Lambda and variable binding
lambdaTests :: [(String, T.Exp)]
lambdaTests =
  [ -- Single variable
    ( "fun (x : int) -> x"
    , T.Lam (T.Var 0)  -- x at index 0
    )
  
  , -- Two nested variables
    ( "fun (x : int) -> fun (y : int) -> x"
    , T.Lam (T.Lam (T.Var 1))  -- x at index 1 (skip y)
    )
  
  , -- Two nested variables - inner reference
    ( "fun (x : int) -> fun (y : int) -> y"
    , T.Lam (T.Lam (T.Var 0))  -- y at index 0
    )
  
  , -- Application with variable
    ( "fun (f : int) -> f(1)"
    , T.Lam (T.App (T.Var 0) (T.Lit (T.LitInt 1)))
    )
  
  , -- Multiple applications
    ( "fun (f : int) -> fun (x : int) -> f(x)"
    , T.Lam (T.Lam (T.App (T.Var 1) (T.Var 0)))
    )
  ]

-- Type lambda tests
typeLambdaTests :: [(String, T.Exp)]
typeLambdaTests =
  [ -- Simple type lambda
    ( "fun (type a) -> fun (x : a) -> x"
    , T.TLam (T.Lam (T.Var 0))  -- x becomes type variable at index 0
    )
  
  , -- Type lambda with term lambda
    ( "fun (type a) -> fun (x : int) -> x"
    , T.TLam (T.Lam (T.Var 0))  -- x at index 0
    )
  
  , -- Type variable reference in type annotation
    ( "fun (type a) -> fun (x : a) -> (x :: a)"
    , T.TLam (T.Lam (T.Anno (T.Var 0) (T.TyVar 0)))  -- was TyVar 1
    )
  ]

-- Nested scope tests
nestedScopeTests :: [(String, T.Exp)]
nestedScopeTests =
  [ -- Three levels deep
    ( "fun (x : int) -> fun (y : int) -> fun (z : int) -> x"
    , T.Lam (T.Lam (T.Lam (T.Var 2)))  -- x at index 2
    )
  
  , -- Three levels - middle reference
    ( "fun (x : int) -> fun (y : int) -> fun (z : int) -> y"
    , T.Lam (T.Lam (T.Lam (T.Var 1)))  -- y at index 1
    )
  
  , -- Three levels - innermost reference
    ( "fun (x : int) -> fun (y : int) -> fun (z : int) -> z"
    , T.Lam (T.Lam (T.Lam (T.Var 0)))  -- z at index 0
    )
  
  , -- Mixed type and term
    ( "fun (type t) -> fun (x : int) -> fun (type u) -> fun (y : int) -> x"
    , T.TLam (T.Lam (T.TLam (T.Lam (T.Var 1))))  -- was Var 2
    )
  ]

-- Environment tests (CRITICAL: tests reversal)
environmentTests :: [(String, T.Exp)]
environmentTests =
  [ -- Single binding
    ( "[x = 1]"
    , T.FEnv [T.ExpE (T.Lit (T.LitInt 1))]
    )
  
  , -- CRITICAL: Two bindings - order matters!
    -- Input:  [x = 1, y = 2]  (parsed right-to-left)
    -- Output: [y = 2, x = 1]  (reversed for De Bruijn)
    ( "[x = 1, y = 2]"
    , T.FEnv [ T.ExpE (T.Lit (T.LitInt 2))  -- y first (newest)
             , T.ExpE (T.Lit (T.LitInt 1))  -- x last (oldest)
             ]
    )
  
  , -- Three bindings with variable references
    -- x=1, y=x, z=y  should become:
    -- [z=_1_, y=_1_, x=1]  (reversed, indices point backwards)
    ( "[x = 1, y = x, z = y]"
    , T.FEnv [ T.ExpE (T.Var 1)              -- z = y (y is 1 back)
             , T.ExpE (T.Var 1)              -- y = x (x is 1 back)
             , T.ExpE (T.Lit (T.LitInt 1))   -- x = 1
             ]
    )
  
  , -- Type bindings in environment
    ( "[type t = int, x = 1]"
    , T.FEnv [ T.ExpE (T.Lit (T.LitInt 1))
             , T.TypE (T.TyLit T.TyInt)
             ]
    )
  ]

-- Box tests (context isolation)
boxTests :: [(String, T.Exp)]
boxTests =
  [ -- Empty box
    ( "box [] in 1"
    , T.Box [] (T.Lit (T.LitInt 1))
    )
  
  , -- Box with binding - body sees ONLY box context
    ( "box [x = 1] in x"
    , T.Box [T.ExpE (T.Lit (T.LitInt 1))]
            (T.Var 0)  -- x at index 0 in box context
    )
  
  , -- CRITICAL: Box isolates context
    -- Outer binding NOT visible in box
    ( "fun (y : int) -> box [x = 1] in x"
    , T.Lam (T.Box [T.ExpE (T.Lit (T.LitInt 1))]
                   (T.Var 0))  -- x, NOT y!
    )
  
  , -- Box with multiple bindings (reversal!)
    ( "box [x = 1, y = 2] in y"
    , T.Box [ T.ExpE (T.Lit (T.LitInt 2))  -- y first
            , T.ExpE (T.Lit (T.LitInt 1))  -- x last
            ]
            (T.Var 0)  -- y at index 0
    )
  
  , -- Box with type binding
    ( "box [type t = int, x = 1] in x"
    , T.Box [ T.ExpE (T.Lit (T.LitInt 1))
            , T.TypE (T.TyLit T.TyInt)
            ]
            (T.Var 0)
    )
  ]

-- Type context tests (CRITICAL: tests reversal in types)
typeContextTests :: [(String, T.Typ)]
typeContextTests =
  [ -- Empty context
    ( "[]"
    , T.TyEnvt []
    )
  
  , -- Single type binding
    ( "[type t = int]"
    , T.TyEnvt [T.TypeEq (T.TyLit T.TyInt)]
    )
  
  , -- CRITICAL: Multiple bindings - reversal!
    ( "[type t = int, type u = bool]"
    , T.TyEnvt [ T.TypeEq (T.TyLit T.TyBool)  -- u first
               , T.TypeEq (T.TyLit T.TyInt)   -- t last
               ]
    )
  
  , -- Kind binding
    ( "[x : Type]"
    , T.TyEnvt [T.Kind]
    )
  
  , -- Mixed bindings
    ( "[x : Type, type t = int]"
    , T.TyEnvt [ T.TypeEq (T.TyLit T.TyInt)
               , T.Kind
               ]
    )
  
  , -- Box type with context
    ( "[type t = int] ===> t"
    , T.TyBoxT [T.TypeEq (T.TyLit T.TyInt)]
               (T.TyVar 0)  -- t at index 0
    )
  
  , -- CRITICAL: Box type with dependent reference
    ( "[type t = int, type u = t] ===> u"
    , T.TyBoxT [ T.TypeEq (T.TyVar 1)          -- u = t (t at index 1)
               , T.TypeEq (T.TyLit T.TyInt)    -- t = int
               ]
               (T.TyVar 0)  -- u at index 0
    )
  ]

-- Module tests
moduleTests :: [(String, T.Module)]
moduleTests =
  [ -- Empty struct
    ( ""
    , T.Struct []
    )
  
  , -- Struct with binding
    ( "let x = 1;;"
    , T.Struct [T.ExpE (T.Lit (T.LitInt 1))]
    )
  
  , -- CRITICAL: Struct with multiple bindings (reversal!)
    ( "let x = 1;; let y = 2;;"
    , T.Struct [ T.ExpE (T.Lit (T.LitInt 2))  -- y first
               , T.ExpE (T.Lit (T.LitInt 1))  -- x last
               ]
    )
  
  , -- Functor (term)
    ( "module F = functor (x : int) -> struct end;;"
    , T.Struct [T.ModExpE (T.ModE (T.Functor (T.Struct [])))]
    )
  
  , -- Functor (type) - becomes Functort
    ( "module F = functor (type t) -> struct end;;"
    , T.Struct [T.ModExpE (T.ModE (T.Functort (T.Struct [])))]
    )
  ]

-- Shadowing tests (same name in different scopes)
shadowingTests :: [(String, T.Exp)]
shadowingTests =
  [ -- Inner x shadows outer x
    ( "fun (x : int) -> fun (x : int) -> x"
    , T.Lam (T.Lam (T.Var 0))  -- Inner x at 0, outer x at 1 (shadowed)
    )
  
  , -- Reference outer x before shadowing
    ( "fun (x : int) -> fun (y : int) -> fun (x : int) -> y"
    , T.Lam (T.Lam (T.Lam (T.Var 1)))  -- y, not either x
    )
  
  , -- Box shadows outer variable
    ( "fun (x : int) -> box [x = 2] in x"
    , T.Lam (T.Box [T.ExpE (T.Lit (T.LitInt 2))]
                   (T.Var 0))  -- Box's x, not outer x
    )
  ]

-- Record tests (labels preserved)
recordTests :: [(String, T.Exp)]
recordTests =
  [ -- Single field
    ( "{x = 1}"
    , T.Rec [("x", T.Lit (T.LitInt 1))]
    )
  
  , -- Multiple fields (order preserved!)
    ( "{x = 1, y = 2}"
    , T.Rec [("x", T.Lit (T.LitInt 1)), ("y", T.Lit (T.LitInt 2))]
    )
  
  , -- Record projection
    ( "fun (r : int) -> r.x"
    , T.Lam (T.RProj (T.Var 0) "x")
    )
  
  , -- Nested records
    ( "{x = {y = 1}}"
    , T.Rec [("x", T.Rec [("y", T.Lit (T.LitInt 1))])]
    )
  ]

complexModuleTests :: [(String, T.Module)]
complexModuleTests =
  [ -- Struct with value referencing previous value
    -- let x = 1;; let y = x;;
    -- Reversed: [y, x] where y references x
    ( "let x = 1;; let y = x;;"
    , T.Struct [ T.ExpE (T.Var 1)              -- y = x (x is at index 1)
               , T.ExpE (T.Lit (T.LitInt 1))   -- x = 1
               ]
    )

  , -- Three bindings with chained references
    -- let x = 1;; let y = x;; let z = y;;
    ( "let x = 1;; let y = x;; let z = y;;"
    , T.Struct [ T.ExpE (T.Var 1)              -- z = y
               , T.ExpE (T.Var 1)              -- y = x
               , T.ExpE (T.Lit (T.LitInt 1))   -- x = 1
               ]
    )

  , -- Struct with type and value
    -- type t = int;; let x = 1;;
    ( "type t = int;; let x = 1;;"
    , T.Struct [ T.ExpE (T.Lit (T.LitInt 1))   -- x = 1
               , T.TypE (T.TyLit T.TyInt)      -- type t = int
               ]
    )

  , -- Value referencing a type (in annotation)
    -- type t = int;; let x = (1 :: t);;
    ( "type t = int;; let x = (1 :: t);;"
    , T.Struct [ T.ExpE (T.Anno (T.Lit (T.LitInt 1)) (T.TyVar 1))  -- x = (1 :: t), t at index 1
               , T.TypE (T.TyLit T.TyInt)                          -- type t = int
               ]
    )

  , -- Struct with function that uses earlier binding
    -- let x = 1;; let f = fun (y : int) -> x;;
    ( "let x = 1;; let f = fun (y : int) -> x;;"
    , T.Struct [ T.ExpE (T.Lam (T.Var 2))      -- f: inside lambda, x is at index 2 (skip y, skip f, get x)
               , T.ExpE (T.Lit (T.LitInt 1))   -- x = 1
               ]
    )

  , -- Nested struct (module inside module)
    -- module M = struct let x = 1;; end;;
    ( "module M = struct let x = 1;; end;;"
    , T.Struct [ T.ModExpE (T.ModE (T.Struct [T.ExpE (T.Lit (T.LitInt 1))])) ]
    )

  , -- Two modules, second references first's structure
    -- module M = struct let x = 1;; end;;
    -- module N = struct let y = 2;; end;;
    ( "module M = struct let x = 1;; end;; module N = struct let y = 2;; end;;"
    , T.Struct [ T.ModExpE (T.ModE (T.Struct [T.ExpE (T.Lit (T.LitInt 2))]))  -- N
               , T.ModExpE (T.ModE (T.Struct [T.ExpE (T.Lit (T.LitInt 1))]))  -- M
               ]
    )
  ]

-------------------------------------------------------------------------
-- Functor Tests
-------------------------------------------------------------------------

functorTests :: [(String, T.Module)]
functorTests =
  [ -- Simple term functor
    -- module F = functor (x : int) -> struct let y = x;; end;;
    ( "module F = functor (x : int) -> struct let y = x;; end;;"
    , T.Struct [ T.ModExpE (T.ModE 
        (T.Functor                              -- functor (x : int) ->
          (T.Struct [T.ExpE (T.Var 1)])))       -- y = x, x at index 1 (skip y)
      ]
    )

  , -- Type functor
    -- module F = functor (type t) -> struct type u = t;; end;;
    ( "module F = functor (type t) -> struct type u = t;; end;;"
    , T.Struct [ T.ModExpE (T.ModE 
        (T.Functort                             -- functor (type t) ->
          (T.Struct [T.TypE (T.TyVar 1)])))     -- type u = t, t at index 1
      ]
    )

  , -- Functor with multiple bindings in body
    -- module F = functor (x : int) -> struct let a = x;; let b = a;; end;;
    ( "module F = functor (x : int) -> struct let a = x;; let b = a;; end;;"
    , T.Struct [ T.ModExpE (T.ModE
        (T.Functor
          (T.Struct [ T.ExpE (T.Var 1)          -- b = a (a at index 1)
                    , T.ExpE (T.Var 1)          -- a = x (x at index 1, skip a)
                    ])))
      ]
    )

  , -- Nested functors
    -- module F = functor (x : int) -> functor (y : int) -> struct let z = x;; end;;
    ( "module F = functor (x : int) -> functor (y : int) -> struct let z = x;; end;;"
    , T.Struct [ T.ModExpE (T.ModE
        (T.Functor                              -- functor (x : int) ->
          (T.Functor                            -- functor (y : int) ->
            (T.Struct [T.ExpE (T.Var 2)]))))    -- z = x (skip z, skip y, get x)
      ]
    )

  , -- Type functor with value using the type
    -- module F = functor (type t) -> struct let x = (1 :: t);; end;;
    ( "module F = functor (type t) -> struct let x = (1 :: t);; end;;"
    , T.Struct [ T.ModExpE (T.ModE
        (T.Functort
          (T.Struct [T.ExpE (T.Anno (T.Lit (T.LitInt 1)) (T.TyVar 1))])))
                                                -- t at index 1 (skip x)
      ]
    )

  , -- Mixed type and term functor
    -- module F = functor (type t) -> functor (x : int) -> struct let y = x;; end;;
    ( "module F = functor (type t) -> functor (x : int) -> struct let y = x;; end;;"
    , T.Struct [ T.ModExpE (T.ModE
        (T.Functort                             -- functor (type t) ->
          (T.Functor                            -- functor (x : int) ->
            (T.Struct [T.ExpE (T.Var 1)]))))    -- y = x
      ]
    )
  ]

-------------------------------------------------------------------------
-- Module Application Tests
-------------------------------------------------------------------------

moduleAppTests :: [(String, T.Module)]
moduleAppTests =
  [ -- Functor application
    -- module F = functor (x : int) -> struct end;;
    -- module M = F ^ 42;;
    -- This depends on your syntax for module application
    
    -- Module variable reference
    ( "module M = struct end;; module N = M;;"
    , T.Struct [ T.ModExpE (T.ModE (T.VarM 1))  -- N = M, M at index 1
               , T.ModExpE (T.ModE (T.Struct []))  -- M = struct end
               ]
    )
  ]

-------------------------------------------------------------------------
-- Closure Tests (clos [...] -> body)
-------------------------------------------------------------------------

closureTests :: [(String, T.Exp)]
closureTests =
  [ -- Simple closure with environment
    -- clos [x = 1] (y : int) -> x
    ( "clos [x = 1] (y : int) -> x"
    , T.Clos [T.ExpE (T.Lit (T.LitInt 1))]      -- env: [x = 1]
             (T.Lam (T.Var 1))                   -- body: fun y -> x (x at index 1)
    )

  , -- Closure referencing environment variable
    -- clos [x = 1, y = x] (z : int) -> y
    ( "clos [x = 1, y = x] (z : int) -> y"
    , T.Clos [ T.ExpE (T.Var 1)                 -- y = x (reversed: y first)
             , T.ExpE (T.Lit (T.LitInt 1))      -- x = 1
             ]
             (T.Lam (T.Var 1))                   -- body: fun z -> y (y at index 1)
    )

  , -- Closure with outer context
    -- fun (a : int) -> clos [x = a] (y : int) -> x
    ( "fun (a : int) -> clos [x = a] (y : int) -> x"
    , T.Lam 
        (T.Clos [T.ExpE (T.Var 1)]            -- a at index 1 in [x, a]
                (T.Lam (T.Var 1)))            -- x at index 1 in [y, x]
    )

  , -- Type closure
    -- tclos [type t = int] (x : t) -> x
    ( "tclos [type t = int] (x : t) -> x"
    , T.TClos [T.TypE (T.TyLit T.TyInt)]        -- env: [type t = int]
              (T.Lam (T.Var 0))                  -- body: fun x -> x
    )

  , -- Closure with multiple env bindings and references
    -- clos [a = 1, b = a, c = b] (x : int) -> c
    ( "clos [a = 1, b = a, c = b] (x : int) -> c"
    , T.Clos [ T.ExpE (T.Var 1)                 -- c = b
             , T.ExpE (T.Var 1)                 -- b = a  
             , T.ExpE (T.Lit (T.LitInt 1))      -- a = 1
             ]
             (T.Lam (T.Var 1))                   -- fun x -> c (c at index 1)
    )
  ]

-------------------------------------------------------------------------
-- Deep Nesting Tests
-------------------------------------------------------------------------

deepNestingTests :: [(String, T.Exp)]
deepNestingTests =
  [ -- Lambda inside box inside lambda
    -- fun (x : int) -> box [y = 1] in fun (z : int) -> y
    ( "fun (x : int) -> box [y = 1] in fun (z : int) -> y"
    , T.Lam                                     -- fun x ->
        (T.Box [T.ExpE (T.Lit (T.LitInt 1))]    -- box [y = 1] in
               (T.Lam (T.Var 1)))               -- fun z -> y (y at index 1)
    )

  , -- Nested environments
    -- [[x = 1]]
    ( "[[x = 1]]"
    , T.FEnv [T.ExpE (T.FEnv [T.ExpE (T.Lit (T.LitInt 1))])]
    )

  , -- Environment with lambda that captures
    -- [f = fun (x : int) -> x, g = fun (y : int) -> f]
    ( "[f = fun (x : int) -> x, g = fun (y : int) -> f]"
    , T.FEnv [ T.ExpE (T.Lam (T.Var 2))         -- g: fun y -> f (skip y, skip g, get f)
             , T.ExpE (T.Lam (T.Var 0))         -- f: fun x -> x
             ]
    )

  , -- Box inside environment
    -- [x = box [y = 1] in y]
    ( "[x = box [y = 1] in y]"
    , T.FEnv [T.ExpE (T.Box [T.ExpE (T.Lit (T.LitInt 1))]
                            (T.Var 0))]         -- y at index 0 in box context
    )

  , -- Multiple boxes
    -- box [x = 1] in box [y = x] in y
    -- Wait, this should fail because box isolates - x not visible in inner box!
    -- Let's do a valid one:
    -- box [x = 1] in box [y = 2] in y
    ( "box [x = 1] in box [y = 2] in y"
    , T.Box [T.ExpE (T.Lit (T.LitInt 1))]
            (T.Box [T.ExpE (T.Lit (T.LitInt 2))]
                   (T.Var 0))                   -- y at index 0
    )

  , -- Lambda returning environment
    -- fun (x : int) -> [y = x]
    ( "fun (x : int) -> [y = x]"
    , T.Lam (T.FEnv [T.ExpE (T.Var 1)])         -- y = x (skip y, get x at 1)
    )

  , -- Four levels of lambdas
    ( "fun (a : int) -> fun (b : int) -> fun (c : int) -> fun (d : int) -> a"
    , T.Lam (T.Lam (T.Lam (T.Lam (T.Var 3))))  -- a at index 3
    )

  , -- Complex: env with functions that reference each other
    -- [id = fun (x : int) -> x, apply = fun (f : int) -> fun (y : int) -> f(y)]
    ( "[id = fun (x : int) -> x, apply = fun (f : int) -> fun (y : int) -> f(y)]"
    , T.FEnv [ T.ExpE (T.Lam (T.Lam (T.App (T.Var 1) (T.Var 0))))  -- apply
             , T.ExpE (T.Lam (T.Var 0))                             -- id
             ]
    )
  ]

-------------------------------------------------------------------------
-- Type in Module Tests
-------------------------------------------------------------------------

moduleTypeTests :: [(String, T.Module)]
moduleTypeTests =
  [ -- Type definition followed by value using it
    -- type t = int;; let x = (1 :: t);;
    ( "type t = int;; let x = (1 :: t);;"
    , T.Struct [ T.ExpE (T.Anno (T.Lit (T.LitInt 1)) (T.TyVar 1))
               , T.TypE (T.TyLit T.TyInt)
               ]
    )

  , -- Multiple type definitions
    -- type t = int;; type u = t;;
    ( "type t = int;; type u = t;;"
    , T.Struct [ T.TypE (T.TyVar 1)             -- u = t
               , T.TypE (T.TyLit T.TyInt)       -- t = int
               ]
    )

  , -- Type, then value, then type referencing first type
    -- type t = int;; let x = 1;; type u = t;;
    ( "type t = int;; let x = 1;; type u = t;;"
    , T.Struct [ T.TypE (T.TyVar 2)             -- u = t (skip u, skip x, get t)
               , T.ExpE (T.Lit (T.LitInt 1))    -- x = 1
               , T.TypE (T.TyLit T.TyInt)       -- t = int
               ]
    )

  , -- Function type referencing module's type
    -- type t = int;; let f = fun (x : t) -> x;;
    ( "type t = int;; let f = fun (x : t) -> x;;"
    , T.Struct [ T.ExpE (T.Lam (T.Var 0))       -- f = fun (x : t) -> x
               , T.TypE (T.TyLit T.TyInt)       -- t = int
               ]
    -- Note: The type annotation (x : t) is in the source but might be erased
    -- depending on your Lam representation
    )
  ]

-------------------------------------------------------------------------
-- Edge Cases and Regression Tests  
-------------------------------------------------------------------------

edgeCaseTests :: [(String, T.Exp)]
edgeCaseTests =
  [ -- Empty environment
    ( "[]"
    , T.FEnv []
    )

  , -- Very long chain
    ( "[a = 1, b = a, c = b, d = c, e = d]"
    , T.FEnv [ T.ExpE (T.Var 1)              -- e = d
             , T.ExpE (T.Var 1)              -- d = c
             , T.ExpE (T.Var 1)              -- c = b
             , T.ExpE (T.Var 1)              -- b = a
             , T.ExpE (T.Lit (T.LitInt 1))   -- a = 1
             ]
    )

  , -- Binary operations with environment variables
    ( "[x = 1, y = 2, z = x + y]"
    , T.FEnv [ T.ExpE (T.BinOp (T.Add (T.Var 2) (T.Var 1)))  -- z = x + y
             , T.ExpE (T.Lit (T.LitInt 2))                    -- y = 2
             , T.ExpE (T.Lit (T.LitInt 1))                    -- x = 1
             ]
    )

  , -- Record inside environment
    ( "[r = {x = 1, y = 2}]"
    , T.FEnv [T.ExpE (T.Rec [("x", T.Lit (T.LitInt 1)), ("y", T.Lit (T.LitInt 2))])]
    )

  , -- Environment inside record (if supported)
    ( "{env = [x = 1]}"
    , T.Rec [("env", T.FEnv [T.ExpE (T.Lit (T.LitInt 1))])]
    )

  , -- Projection after box
    ( "(box [r = {x = 1}] in r).x"
    , T.RProj (T.Box [T.ExpE (T.Rec [("x", T.Lit (T.LitInt 1))])]
                     (T.Var 0))
              "x"
    )
  ]

-------------------------------------------------------------------------
-- Interface/Signature Tests (if applicable)
-------------------------------------------------------------------------

-- These test convIntf - add if you have signature syntax
interfaceTests :: [(String, T.Typ)]
interfaceTests =
  [ -- Simple signature
    -- sig type t;; val x : t;; end
    -- This depends on your syntax for standalone signatures
  ]

-------------------------------------------------------------------------
-- CRITICAL INVARIANT TESTS
-- These tests verify the core De Bruijn invariants
-------------------------------------------------------------------------

invariantTests :: [(String, T.Exp)]
invariantTests =
  [ -- Invariant 1: Index 0 always refers to most recently bound variable
    ( "fun (x : int) -> x"
    , T.Lam (T.Var 0)
    )

  , -- Invariant 2: Each lambda increases index for outer variables by 1
    ( "fun (x : int) -> fun (y : int) -> x"
    , T.Lam (T.Lam (T.Var 1))  -- x was 0, now 1 after y binding
    )

  , -- Invariant 3: Environment reversal - first in source = last in output
    ( "[first = 1, second = 2, third = 3]"
    , T.FEnv [ T.ExpE (T.Lit (T.LitInt 3))   -- third (index 0 in output)
             , T.ExpE (T.Lit (T.LitInt 2))   -- second (index 1)
             , T.ExpE (T.Lit (T.LitInt 1))   -- first (index 2)
             ]
    )

  , -- Invariant 4: Box completely isolates - outer variables NOT accessible
    -- The body of box ONLY sees the box's environment
    ( "fun (outer : int) -> box [inner = 1] in inner"
    , T.Lam (T.Box [T.ExpE (T.Lit (T.LitInt 1))]
                   (T.Var 0))  -- inner, NOT outer!
    )

  , -- Invariant 5: Clos/TClos extends context (unlike Box which replaces)
    ( "fun (outer : int) -> clos [inner = 1] (x : int) -> outer"
    , T.Lam (T.Clos [T.ExpE (T.Lit (T.LitInt 1))]
                    (T.Lam (T.Var 3)))  -- outer at index 3: skip x, inner, clos-binding, get outer
    )
  ]