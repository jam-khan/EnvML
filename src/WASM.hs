{-# LANGUAGE OverloadedStrings #-}

module Main where

import qualified EnvML.Parser.Parser as Parser
import qualified EnvML.Parser.Lexer as Lexer
import qualified EnvML.Syntax as AST
import qualified EnvML.Elab as Elab
import qualified CoreFE.Named as CoreNamed
import qualified CoreFE.DeBruijn as DeBruijn
import qualified CoreFE.Syntax as CoreFE
import qualified CoreFE.Check as Check
import qualified CoreFE.Eval as Eval
import qualified PrettyWeb as PW
import qualified CoreFE.Parser.Lexer as CoreLexer
import qualified CoreFE.Parser.Parser as CoreParser
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

toDeBruijn :: CoreNamed.Exp -> CoreFE.Exp
toDeBruijn = DeBruijn.toDeBruijn

-------------------------------------------------------------------------------
-- EnvML Pipeline Stages
-------------------------------------------------------------------------------

-- | Stage 1: Parse
foreign export javascript "runParse" runParse :: JSString -> IO JSString

runParse :: JSString -> IO JSString
runParse = safeRun $ \input ->
    let ast = parseModule input
    in "=== Parsed AST ===\n\n" ++ PW.prettyEnvMLModule ast

-- | Stage 2: Elaborate (Named CoreFE)
foreign export javascript "runElaborate" runElaborate :: JSString -> IO JSString

runElaborate :: JSString -> IO JSString
runElaborate = safeRun $ \input ->
    let ast       = parseModule input
        coreNamed = elaborate ast
    in "=== Elaborated (Named CoreFE) ===\n\n" ++ PW.prettyNamedModule coreNamed

-- | Stage 3: De Bruijn (Nameless CoreFE)
foreign export javascript "runDeBruijn" runDeBruijn :: JSString -> IO JSString

runDeBruijn :: JSString -> IO JSString
runDeBruijn = safeRun $ \input ->
    let ast           = parseModule input
        coreNamed     = elaborate ast
        coreNameless  = toDeBruijn coreNamed
    in "=== De Bruijn (Nameless CoreFE) ===\n\n" ++ PW.prettyDeBruijnModule coreNameless

-- | Stage 4: Type Check
foreign export javascript "runCheck" runCheck :: JSString -> IO JSString

runCheck :: JSString -> IO JSString
runCheck = safeRun $ \input ->
    let ast           = parseModule input
        coreNamed     = elaborate ast
        coreNameless  = toDeBruijn coreNamed
    in case Check.infer [] coreNameless of
        Nothing  -> "✗ Type Error\n\nCould not infer type"
        Just typ -> "✓ Type Check Passed\n\n" ++ PW.prettyCheckResult typ

-- | Stage 5: Eval
foreign export javascript "runEval" runEval :: JSString -> IO JSString

runEval :: JSString -> IO JSString
runEval = safeRun $ \input ->
    let ast           = parseModule input
        coreNamed     = elaborate ast
        coreNameless  = toDeBruijn coreNamed
    in case Eval.eval [] coreNameless of
        Nothing  -> "✗ Evaluation Error\n\nEvaluation got stuck"
        Just res -> "✓ Evaluation Result\n\n" ++ PW.prettyEvalResult res

-- | Full pipeline: check + eval
foreign export javascript "runFull" runFull :: JSString -> IO JSString

runFull :: JSString -> IO JSString
runFull = safeRun $ \input ->
    let ast           = parseModule input
        coreNamed     = elaborate ast
        coreNameless  = toDeBruijn coreNamed
        typeResult = case Check.infer [] coreNameless of
            Nothing  -> "✗ Type Error: Could not infer type"
            Just typ -> "✓ Types:\n" ++ PW.prettyCheckResult typ
        evalResult = case Eval.eval [] coreNameless of
            Nothing  -> "✗ Evaluation Error: Got stuck"
            Just res -> "✓ Values:\n" ++ PW.prettyEvalResult res
    in typeResult ++ "\n" ++ evalResult

-------------------------------------------------------------------------------
-- CoreFE Calculus Direct Functions
-------------------------------------------------------------------------------

-- | Parse a CoreFE expression string
foreign export javascript "coreParseExp" coreParseExp :: JSString -> IO JSString

coreParseExp :: JSString -> IO JSString
coreParseExp = safeRun $ \input ->
    let expr = CoreParser.parseExp (CoreLexer.lexer input)
    in "=== Parsed CoreFE ===\n\n" ++ CoreFE.pretty expr

-- | Parse + Infer type of a CoreFE expression
foreign export javascript "coreCheck" coreCheck :: JSString -> IO JSString

coreCheck :: JSString -> IO JSString
coreCheck = safeRun $ \input ->
    let expr = CoreParser.parseExp (CoreLexer.lexer input)
    in case Check.infer [] expr of
        Nothing  -> "✗ Type Error\n\nCould not infer type"
        Just typ -> "✓ Type\n\n  " ++ PW.prettyDeBruijnTyp typ

-- | Parse + Eval a CoreFE expression
foreign export javascript "coreEval" coreEval :: JSString -> IO JSString

coreEval :: JSString -> IO JSString
coreEval = safeRun $ \input ->
    let expr = CoreParser.parseExp (CoreLexer.lexer input)
    in case Eval.eval [] expr of
        Nothing  -> "✗ Evaluation Error\n\nEvaluation got stuck"
        Just res -> "✓ Result\n\n  " ++ PW.prettyValueShort res

-- | Parse + Check + Eval a CoreFE expression (full pipeline)
foreign export javascript "coreRun" coreRun :: JSString -> IO JSString

coreRun :: JSString -> IO JSString
coreRun = safeRun $ \input ->
    let expr = CoreParser.parseExp (CoreLexer.lexer input)
        typeStr = case Check.infer [] expr of
            Nothing  -> "✗ Type Error: Could not infer type"
            Just typ -> "Type   : " ++ PW.prettyDeBruijnTyp typ
        evalStr = case Eval.eval [] expr of
            Nothing  -> "✗ Eval Error: Got stuck"
            Just res -> "Result : " ++ PW.prettyValueShort res
    in typeStr ++ "\n" ++ evalStr

safeRun :: (String -> String) -> JSString -> IO JSString
safeRun f input = do
    let inputStr = fromJSString input
    result <- catch
        (evaluate $! f inputStr)
        (\(e :: SomeException) -> return $ "Error: " ++ show e)
    return $ toJSString result