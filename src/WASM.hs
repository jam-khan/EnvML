{-# LANGUAGE OverloadedStrings #-}

module Main where

import qualified EnvML.Parser.Parser as Parser
import qualified EnvML.Parser.Lexer as Lexer
import qualified EnvML.Syntax as AST
import qualified EnvML.Desugar as Desugar
import qualified EnvML.Elab as Elab
import qualified Core.Check as Check
import qualified Core.Eval as Eval
import GHC.Wasm.Prim
import Control.Exception (catch, SomeException)

-------------------------------------------------------------------------------
-- Main (required but not used in reactor mode)
-------------------------------------------------------------------------------

main :: IO ()
main = error "This is a reactor module - call setup() from JavaScript"

-------------------------------------------------------------------------------
-- Setup function - exported to JavaScript
-------------------------------------------------------------------------------

foreign export javascript "setup" setup :: IO ()

-- | Initialize the WASM module. This should be called once from JavaScript
-- after the module is instantiated.
setup :: IO ()
setup = do
    return ()

-------------------------------------------------------------------------------
-- Pipeline Stage Functions - All exported to JavaScript
-------------------------------------------------------------------------------

-- | Stage 1: Parse
foreign export javascript "runParse" runParse :: JSString -> IO JSString

runParse :: JSString -> IO JSString
runParse input = safeRun runParseImpl input

runParseImpl :: String -> String
runParseImpl input = 
    let res = Parser.parseModule (Lexer.lexer input) 
    in "=== Parsed AST ===\n" ++ AST.pretty res

-- | Stage 2: Parse + Desugar
foreign export javascript "runDesugar" runDesugar :: JSString -> IO JSString

runDesugar :: JSString -> IO JSString
runDesugar input = safeRun runDesugarImpl input

runDesugarImpl :: String -> String
runDesugarImpl input = 
    let parsed    = Parser.parseModule (Lexer.lexer input)
        desugared = Desugar.desugarModule parsed
    in "=== Desugared AST ===\n" ++ AST.pretty desugared

-- | Stage 3: De-Bruijn
foreign export javascript "runDeBruijn" runDeBruijn :: JSString -> IO JSString

runDeBruijn :: JSString -> IO JSString
runDeBruijn input = safeRun runDeBruijnImpl input

runDeBruijnImpl :: String -> String
runDeBruijnImpl input =  error "De-bruijn to be FIXED."

-- | Stage 4: Elaboration
foreign export javascript "runElaborate" runElaborate :: JSString -> IO JSString

runElaborate :: JSString -> IO JSString
runElaborate input = safeRun runElaborateImpl input

runElaborateImpl :: String -> String
runElaborateImpl input = 
    let parsed    = Parser.parseModule (Lexer.lexer input)
        desugared = Desugar.desugarModule parsed
        nameless  = DB.modToDeBruijn desugared
    in case Elab.elabM nameless of
        Left err   -> "✗ Elaboration Error:\n" ++ err
        Right core -> "=== Elaborated Core ===\n" ++ show core

-- | Stage 5: Type Check
foreign export javascript "runCheck" runCheck :: JSString -> IO JSString

runCheck :: JSString -> IO JSString
runCheck input = safeRun runCheckImpl input

runCheckImpl :: String -> String
runCheckImpl input = 
    let parsed    = Parser.parseModule (Lexer.lexer input)
        desugared = Desugar.desugarModule parsed
        nameless  = DB.modToDeBruijn desugared
    in case Elab.elabM nameless of
        Left err   -> "✗ Elaboration Error:\n" ++ err
        Right core -> case Check.infer [] core of
            Nothing -> "✗ Type Error:\nTerm is ill-typed"
            Just ty -> "✓ Type Check Success!\n\nType: " ++ show ty

-- | Stage 6: Eval
foreign export javascript "runEval" runEval :: JSString -> IO JSString

runEval :: JSString -> IO JSString
runEval input = safeRun runEvalImpl input

runEvalImpl :: String -> String
runEvalImpl input = 
    let parsed    = Parser.parseModule (Lexer.lexer input)
        desugared = Desugar.desugarModule parsed
        nameless  = DB.modToDeBruijn desugared
    in case Elab.elabM nameless of
        Left err   -> "✗ Elaboration Error:\n" ++ err
        Right core -> case Eval.eval [] core of
            Nothing -> "✗ Runtime Error:\nEvaluation stuck"
            Just res -> "✓ Execution Result:\n" ++ show res

-------------------------------------------------------------------------------
-- Helper Functions
-------------------------------------------------------------------------------

-- | Safe wrapper that catches exceptions and converts to/from JSString
safeRun :: (String -> String) -> JSString -> IO JSString
safeRun f input = do
    let inputStr = fromJSString input
    result <- catch 
        (return $! f inputStr)
        (\(e :: SomeException) -> return $ "Error: " ++ show e)
    return $ toJSString result
