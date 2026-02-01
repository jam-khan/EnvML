{-# LANGUAGE OverloadedStrings #-}

module WASM where

import qualified EnvML.Parser.Parser as Parser
import qualified EnvML.Parser.Lexer as Lexer
import qualified EnvML.Desugar as Desugar
import qualified EnvML.DeBruijn as DB
import qualified EnvML.Elab as Elab
import qualified Core.Check as Check
import qualified Core.Eval as Eval
import Foreign.C.String (CString, newCString, peekCString)

-- | Stage 1: Parse
-- Returns: S.Module
runParse :: String -> String
runParse input = 
    let res = Parser.parseModule (Lexer.lexer input) 
    in "Parsed AST:\n" ++ show res

-- | Stage 2: Parse + Desugar
-- Returns: S.Module
runDesugar :: String -> String
runDesugar input = 
    let parsed    = Parser.parseModule (Lexer.lexer input)
        desugared = Desugar.desugarModule parsed
    in "Desugared AST:\n" ++ show desugared

-- | Stage 3: De-Bruijn
-- Returns: T.Module
runDeBruijn :: String -> String
runDeBruijn input = 
    let parsed    = Parser.parseModule (Lexer.lexer input)
        desugared = Desugar.desugarModule parsed
        nameless  = DB.modToDeBruijn desugared
    in "De-Bruijn AST:\n" ++ show nameless

-- | Stage 4: Elaboration
-- Returns: Either ElabError Core.Exp
runElaborate :: String -> String
runElaborate input = 
    let parsed    = Parser.parseModule (Lexer.lexer input)
        desugared = Desugar.desugarModule parsed
        nameless  = DB.modToDeBruijn desugared
    in case Elab.elabM nameless of
        Left err   -> "Elab Error: " ++ err
        Right core -> "Core Syntax:\n" ++ show core

-- | Stage 5: Type Check
-- Returns: Maybe Core.Typ
runCheck :: String -> String
runCheck input = 
    let parsed    = Parser.parseModule (Lexer.lexer input)
        desugared = Desugar.desugarModule parsed
        nameless  = DB.modToDeBruijn desugared
    in case Elab.elabM nameless of
        Left err   -> "Elab Error: " ++ err
        Right core -> case Check.infer [] core of
            Nothing -> "Type Error: Term is ill-typed"
            Just ty -> "Type Check Success!\nType: " ++ show ty

-- | Stage 6: Eval
-- Returns: Maybe Core.Exp
runEval :: String -> String
runEval input = 
    let parsed    = Parser.parseModule (Lexer.lexer input)
        desugared = Desugar.desugarModule parsed
        nameless  = DB.modToDeBruijn desugared
    in case Elab.elabM nameless of
        Left err   -> "Elab Error: " ++ err
        Right core -> case Eval.eval [] core of
            Nothing -> "Runtime Error: Evaluation stuck"
            Just res -> "Execution Result:\n" ++ show res

-- FFI Helpers (Boilerplate for WASM/JS interface)
exportStr :: (String -> String) -> (CString -> IO CString)
exportStr f js_str = do
    input <- peekCString js_str
    newCString (f input)

-- foreign export javascript "runParse"     exportStr runParse
-- foreign export javascript "runDesugar"   exportStr runDesugar
-- foreign export javascript "runDeBruijn"  exportStr runDeBruijn
-- foreign export javascript "runElaborate" exportStr runElaborate
-- foreign export javascript "runCheck"     exportStr runCheck
-- foreign export javascript "runEval"      exportStr runEval