{-# LANGUAGE OverloadedStrings #-}

module Main where

import qualified EnvML.Parser.Parser as Parser
import qualified EnvML.Parser.Lexer as Lexer
import qualified EnvML.Syntax as AST
import qualified EnvML.Elab as Elab
import qualified Core.Named as CoreNamed
import qualified Core.DeBruijn as DeBruijn
import qualified Core.Syntax as Core
import qualified Core.Check as Check
import qualified Core.Eval as Eval
import qualified Core.Pretty as Pretty
import qualified Core.Parser.Lexer as CoreLexer
import qualified Core.Parser.Parser as CoreParser
import GHC.Wasm.Prim
import Control.Exception (catch, evaluate, SomeException)

-------------------------------------------------------------------------------
-- Main (required but not used in reactor mode)
-------------------------------------------------------------------------------

main :: IO ()
main = error "This is a reactor module - call setup() from JavaScript"

-------------------------------------------------------------------------------
-- Setup function - exported to JavaScript
-------------------------------------------------------------------------------

foreign export javascript "setup" setup :: IO ()

setup :: IO ()
setup = return ()

-------------------------------------------------------------------------------
-- EnvML Pipeline Helpers
-------------------------------------------------------------------------------

parseModule :: String -> AST.Module
parseModule input = Parser.parseModule (Lexer.lexer input)

elaborate :: AST.Module -> CoreNamed.Exp
elaborate = Elab.elabModule

toDeBruijn :: CoreNamed.Exp -> Core.Exp
toDeBruijn = DeBruijn.toDeBruijn

-------------------------------------------------------------------------------
-- EnvML Pipeline Stages
-------------------------------------------------------------------------------

-- | Stage 1: Parse
foreign export javascript "runParse" runParse :: JSString -> IO JSString

runParse :: JSString -> IO JSString
runParse = safeRun $ \input ->
    let ast = parseModule input
    in "=== Parsed AST ===\n" ++ AST.pretty ast

-- | Stage 2: Elaborate (Named Core)
foreign export javascript "runElaborate" runElaborate :: JSString -> IO JSString

runElaborate :: JSString -> IO JSString
runElaborate = safeRun $ \input ->
    let ast       = parseModule input
        coreNamed = elaborate ast
    in "=== Elaborated Core (Named) ===\n" ++ show coreNamed

-- | Stage 3: De Bruijn (Nameless Core)
foreign export javascript "runDeBruijn" runDeBruijn :: JSString -> IO JSString

runDeBruijn :: JSString -> IO JSString
runDeBruijn = safeRun $ \input ->
    let ast           = parseModule input
        coreNamed     = elaborate ast
        coreNameless  = toDeBruijn coreNamed
    in "=== De Bruijn Core ===\n" ++ Pretty.pretty coreNameless

-- | Stage 4: Type Check
foreign export javascript "runCheck" runCheck :: JSString -> IO JSString

runCheck :: JSString -> IO JSString
runCheck = safeRun $ \input ->
    let ast           = parseModule input
        coreNamed     = elaborate ast
        coreNameless  = toDeBruijn coreNamed
    in case Check.infer [] coreNameless of
        Nothing  -> "✗ Type check failed: Could not infer type"
        Just typ -> "✓ Type check succeeded!\n  Type: " ++ Pretty.pretty typ

-- | Stage 5: Eval
foreign export javascript "runEval" runEval :: JSString -> IO JSString

runEval :: JSString -> IO JSString
runEval = safeRun $ \input ->
    let ast           = parseModule input
        coreNamed     = elaborate ast
        coreNameless  = toDeBruijn coreNamed
    in case Eval.eval [] coreNameless of
        Nothing  -> "✗ Evaluation failed: stuck"
        Just res -> "✓ Result:\n" ++ Pretty.pretty res

-- | Full pipeline: check + eval
foreign export javascript "runFull" runFull :: JSString -> IO JSString

runFull :: JSString -> IO JSString
runFull = safeRun $ \input ->
    let ast           = parseModule input
        coreNamed     = elaborate ast
        coreNameless  = toDeBruijn coreNamed
        typeResult = case Check.infer [] coreNameless of
            Nothing  -> "✗ Type check failed"
            Just typ -> "✓ Type: " ++ Pretty.pretty typ
        evalResult = case Eval.eval [] coreNameless of
            Nothing  -> "✗ Evaluation stuck"
            Just res -> "✓ Result:\n" ++ Pretty.pretty res
    in typeResult ++ "\n\n" ++ evalResult

-------------------------------------------------------------------------------
-- Core Calculus Direct Functions
-------------------------------------------------------------------------------

-- | Parse a Core expression string
foreign export javascript "coreParseExp" coreParseExp :: JSString -> IO JSString

coreParseExp :: JSString -> IO JSString
coreParseExp = safeRun $ \input ->
    let expr = CoreParser.parseExp (CoreLexer.lexer input)
    in "=== Parsed Core ===\n" ++ Pretty.pretty expr

-- | Parse + Infer type of a Core expression
foreign export javascript "coreCheck" coreCheck :: JSString -> IO JSString

coreCheck :: JSString -> IO JSString
coreCheck = safeRun $ \input ->
    let expr = CoreParser.parseExp (CoreLexer.lexer input)
    in case Check.infer [] expr of
        Nothing  -> "✗ Type check failed: Could not infer type"
        Just typ -> "✓ Type: " ++ Pretty.pretty typ

-- | Parse + Eval a Core expression
foreign export javascript "coreEval" coreEval :: JSString -> IO JSString

coreEval :: JSString -> IO JSString
coreEval = safeRun $ \input ->
    let expr = CoreParser.parseExp (CoreLexer.lexer input)
    in case Eval.eval [] expr of
        Nothing  -> "✗ Evaluation stuck"
        Just res -> "✓ Result: " ++ Pretty.pretty res

-- | Parse + Check + Eval a Core expression (full pipeline)
foreign export javascript "coreRun" coreRun :: JSString -> IO JSString

coreRun :: JSString -> IO JSString
coreRun = safeRun $ \input ->
    let expr = CoreParser.parseExp (CoreLexer.lexer input)
        typeStr = case Check.infer [] expr of
            Nothing  -> "✗ Type error: Could not infer type"
            Just typ -> "Type   : " ++ Pretty.pretty typ
        evalStr = case Eval.eval [] expr of
            Nothing  -> "✗ Eval error: Evaluation stuck"
            Just res -> "Result : " ++ Pretty.pretty res
    in typeStr ++ "\n" ++ evalStr

-------------------------------------------------------------------------------
-- Helper Functions
-------------------------------------------------------------------------------

-- | Safe wrapper that catches exceptions and converts to/from JSString
safeRun :: (String -> String) -> JSString -> IO JSString
safeRun f input = do
    let inputStr = fromJSString input
    result <- catch
        (evaluate $! f inputStr)
        (\(e :: SomeException) -> return $ "Error: " ++ show e)
    return $ toJSString result