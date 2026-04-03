{-# LANGUAGE OverloadedStrings #-}

module Main where

import qualified EnvML.Parser.Parser as Parser
import qualified EnvML.Parser.Lexer as Lexer
import qualified EnvML.Syntax as AST
import qualified EnvML.Elab as Elab
import qualified EnvML.Desugar as Desugar
import qualified EnvML.Desugared as D
import qualified EnvML.Check as SCheck
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
elaborate = Elab.elabModule . Desugar.desugarModule

toDeBruijn :: CoreNamed.Exp -> CoreFE.Exp
toDeBruijn = DeBruijn.toDeBruijn

-------------------------------------------------------------------------------
-- EnvML Pipeline Stages - DETAILED (using Pretty instances)
-------------------------------------------------------------------------------

-- | Stage 1: Parse (Detailed)
foreign export javascript "runParseDetailed" runParseDetailed :: JSString -> IO JSString

runParseDetailed :: JSString -> IO JSString
runParseDetailed = safeRun $ \input ->
    let ast = parseModule input
    in "=== Parsed AST ===\n\n" ++ AST.pretty ast

-- | Stage 2: Desugar (Detailed)
foreign export javascript "runDesugarDetailed" runDesugarDetailed :: JSString -> IO JSString

runDesugarDetailed :: JSString -> IO JSString
runDesugarDetailed = safeRun $ \input ->
    let ast       = parseModule input
        desugared = Desugar.desugarModule ast
    in "=== Desugared AST ===\n\n" ++ D.prettyModule desugared

-- | Stage 2b: Source Type Check (Detailed)
foreign export javascript "runSourceCheckDetailed" runSourceCheckDetailed :: JSString -> IO JSString

runSourceCheckDetailed :: JSString -> IO JSString
runSourceCheckDetailed = safeRun $ \input ->
    let ast       = parseModule input
        desugared = Desugar.desugarModule ast
    in case desugared of
        D.Struct structs -> case SCheck.inferStructs [] structs of
            Nothing   -> "\10007 Source Type Error\n\nCould not infer types"
            Just intf -> "\10003 Source Type Check Passed\n\n" ++ AST.prettyIntf intf
        _ -> case SCheck.inferMod [] desugared of
            Nothing  -> "\10007 Source Type Error\n\nCould not infer module type"
            Just mty -> "\10003 Source Type Check Passed\n\n" ++ AST.prettyModuleTyp mty

-- | Stage 3: Elaborate (Detailed - Named CoreFE)
foreign export javascript "runElaborateDetailed" runElaborateDetailed :: JSString -> IO JSString

runElaborateDetailed :: JSString -> IO JSString
runElaborateDetailed = safeRun $ \input ->
    let ast       = parseModule input
        coreNamed = elaborate ast
    in "=== Elaborated (Named CoreFE) ===\n\n" ++ CoreNamed.pretty coreNamed

-- | Stage 4: De Bruijn (Detailed - Nameless CoreFE)
foreign export javascript "runDeBruijnDetailed" runDeBruijnDetailed :: JSString -> IO JSString

runDeBruijnDetailed :: JSString -> IO JSString
runDeBruijnDetailed = safeRun $ \input ->
    let ast           = parseModule input
        coreNamed     = elaborate ast
        coreNameless  = toDeBruijn coreNamed
    in "=== De Bruijn (Nameless CoreFE) ===\n\n" ++ CoreFE.pretty coreNameless

-- | Stage 5: Type Check (Detailed)
foreign export javascript "runCheckDetailed" runCheckDetailed :: JSString -> IO JSString

runCheckDetailed :: JSString -> IO JSString
runCheckDetailed = safeRun $ \input ->
    let ast           = parseModule input
        coreNamed     = elaborate ast
        coreNameless  = toDeBruijn coreNamed
    in case Check.infer [] coreNameless of
        Nothing  -> "✗ Type Error\n\nCould not infer type"
        Just typ -> "✓ Type Check Passed\n\n" ++ CoreFE.pretty typ

-- | Stage 6: Eval (Detailed)
foreign export javascript "runEvalDetailed" runEvalDetailed :: JSString -> IO JSString

runEvalDetailed :: JSString -> IO JSString
runEvalDetailed = safeRun $ \input ->
    let ast           = parseModule input
        coreNamed     = elaborate ast
        coreNameless  = toDeBruijn coreNamed
    in case Eval.eval [] coreNameless of
        Nothing  -> "✗ Evaluation Error\n\nEvaluation got stuck"
        Just res -> "✓ Evaluation Result\n\n" ++ CoreFE.pretty res

-- | Full pipeline: check + eval (Detailed)
foreign export javascript "runFullDetailed" runFullDetailed :: JSString -> IO JSString

runFullDetailed :: JSString -> IO JSString
runFullDetailed = safeRun $ \input ->
    let ast           = parseModule input
        coreNamed     = elaborate ast
        coreNameless  = toDeBruijn coreNamed
        typeResult = case Check.infer [] coreNameless of
            Nothing  -> "✗ Type Error: Could not infer type"
            Just typ -> "✓ Types:\n" ++ CoreFE.pretty typ
        evalResult = case Eval.eval [] coreNameless of
            Nothing  -> "✗ Evaluation Error: Got stuck"
            Just res -> "✓ Values:\n" ++ CoreFE.pretty res
    in typeResult ++ "\n\n" ++ evalResult

-------------------------------------------------------------------------------
-- EnvML Pipeline Stages - SIMPLIFIED (using PrettyWeb)
-------------------------------------------------------------------------------

-- | Stage 1: Parse (Simplified)
foreign export javascript "runParseSimplified" runParseSimplified :: JSString -> IO JSString

runParseSimplified :: JSString -> IO JSString
runParseSimplified = safeRun $ \input ->
    let ast = parseModule input
    in "=== Parsed AST ===\n\n" ++ PW.prettyEnvMLModule ast

-- | Stage 2: Desugar (Simplified)
foreign export javascript "runDesugarSimplified" runDesugarSimplified :: JSString -> IO JSString

runDesugarSimplified :: JSString -> IO JSString
runDesugarSimplified = safeRun $ \input ->
    let ast       = parseModule input
        desugared = Desugar.desugarModule ast
    in "=== Desugared AST ===\n\n" ++ D.prettyModule desugared

-- | Stage 2b: Source Type Check (Simplified)
foreign export javascript "runSourceCheckSimplified" runSourceCheckSimplified :: JSString -> IO JSString

runSourceCheckSimplified :: JSString -> IO JSString
runSourceCheckSimplified = safeRun $ \input ->
    let ast       = parseModule input
        desugared = Desugar.desugarModule ast
    in case desugared of
        D.Struct structs -> case SCheck.inferStructs [] structs of
            Nothing   -> "\10007 Source Type Error\n\nCould not infer types"
            Just intf -> "\10003 Source Type Check Passed\n\n" ++ AST.prettyIntf intf
        _ -> case SCheck.inferMod [] desugared of
            Nothing  -> "\10007 Source Type Error\n\nCould not infer module type"
            Just mty -> "\10003 Source Type Check Passed\n\n" ++ AST.prettyModuleTyp mty

-- | Stage 3: Elaborate (Simplified)
foreign export javascript "runElaborateSimplified" runElaborateSimplified :: JSString -> IO JSString

runElaborateSimplified :: JSString -> IO JSString
runElaborateSimplified = safeRun $ \input ->
    let ast       = parseModule input
        coreNamed = elaborate ast
    in "=== Elaborated (Named CoreFE) ===\n\n" ++ PW.prettyNamedModule coreNamed

-- | Stage 4: De Bruijn (Simplified)
foreign export javascript "runDeBruijnSimplified" runDeBruijnSimplified :: JSString -> IO JSString

runDeBruijnSimplified :: JSString -> IO JSString
runDeBruijnSimplified = safeRun $ \input ->
    let ast           = parseModule input
        coreNamed     = elaborate ast
        coreNameless  = toDeBruijn coreNamed
    in "=== De Bruijn (Nameless CoreFE) ===\n\n" ++ PW.prettyDeBruijnModule coreNameless

-- | Stage 5: Type Check (Simplified)
foreign export javascript "runCheckSimplified" runCheckSimplified :: JSString -> IO JSString

runCheckSimplified :: JSString -> IO JSString
runCheckSimplified = safeRun $ \input ->
    let ast           = parseModule input
        coreNamed     = elaborate ast
        coreNameless  = toDeBruijn coreNamed
    in case Check.infer [] coreNameless of
        Nothing  -> "✗ Type Error\n\nCould not infer type"
        Just typ -> "✓ Type Check Passed\n\n" ++ PW.prettyCheckResult typ

-- | Stage 6: Eval (Simplified)
foreign export javascript "runEvalSimplified" runEvalSimplified :: JSString -> IO JSString

runEvalSimplified :: JSString -> IO JSString
runEvalSimplified = safeRun $ \input ->
    let ast           = parseModule input
        coreNamed     = elaborate ast
        coreNameless  = toDeBruijn coreNamed
    in case Eval.eval [] coreNameless of
        Nothing  -> "✗ Evaluation Error\n\nEvaluation got stuck"
        Just res -> "✓ Evaluation Result\n\n" ++ PW.prettyEvalResult res

-- | Full pipeline: check + eval (Simplified)
foreign export javascript "runFullSimplified" runFullSimplified :: JSString -> IO JSString

runFullSimplified :: JSString -> IO JSString
runFullSimplified = safeRun $ \input ->
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
-- CoreFE Calculus Direct Functions - DETAILED
-------------------------------------------------------------------------------

-- | Parse a CoreFE expression string (Detailed)
foreign export javascript "coreParseExpDetailed" coreParseExpDetailed :: JSString -> IO JSString

coreParseExpDetailed :: JSString -> IO JSString
coreParseExpDetailed = safeRun $ \input ->
    let expr = CoreParser.parseExp (CoreLexer.lexer input)
    in "=== Parsed CoreFE ===\n\n" ++ CoreFE.pretty expr

-- | Parse + Infer type of a CoreFE expression (Detailed)
foreign export javascript "coreCheckDetailed" coreCheckDetailed :: JSString -> IO JSString

coreCheckDetailed :: JSString -> IO JSString
coreCheckDetailed = safeRun $ \input ->
    let expr = CoreParser.parseExp (CoreLexer.lexer input)
    in case Check.infer [] expr of
        Nothing  -> "✗ Type Error\n\nCould not infer type"
        Just typ -> "✓ Type\n\n  " ++ CoreFE.pretty typ

-- | Parse + Eval a CoreFE expression (Detailed)
foreign export javascript "coreEvalDetailed" coreEvalDetailed :: JSString -> IO JSString

coreEvalDetailed :: JSString -> IO JSString
coreEvalDetailed = safeRun $ \input ->
    let expr = CoreParser.parseExp (CoreLexer.lexer input)
    in case Eval.eval [] expr of
        Nothing  -> "✗ Evaluation Error\n\nEvaluation got stuck"
        Just res -> "✓ Result\n\n  " ++ CoreFE.pretty res

-- | Parse + Check + Eval a CoreFE expression (Detailed)
foreign export javascript "coreRunDetailed" coreRunDetailed :: JSString -> IO JSString

coreRunDetailed :: JSString -> IO JSString
coreRunDetailed = safeRun $ \input ->
    let expr = CoreParser.parseExp (CoreLexer.lexer input)
        typeStr = case Check.infer [] expr of
            Nothing  -> "✗ Type Error: Could not infer type"
            Just typ -> "Type   : " ++ CoreFE.pretty typ
        evalStr = case Eval.eval [] expr of
            Nothing  -> "✗ Eval Error: Got stuck"
            Just res -> "Result : " ++ CoreFE.pretty res
    in typeStr ++ "\n" ++ evalStr

-------------------------------------------------------------------------------
-- CoreFE Calculus Direct Functions - SIMPLIFIED
-------------------------------------------------------------------------------

-- | Parse a CoreFE expression string (Simplified)
foreign export javascript "coreParseExpSimplified" coreParseExpSimplified :: JSString -> IO JSString

coreParseExpSimplified :: JSString -> IO JSString
coreParseExpSimplified = safeRun $ \input ->
    let expr = CoreParser.parseExp (CoreLexer.lexer input)
    in "=== Parsed CoreFE ===\n\n" ++ CoreFE.pretty expr

-------------------------------------------------------------------------------
-- Legacy function names (for backward compatibility)
-------------------------------------------------------------------------------

-- EnvML stages (default to Simplified)
foreign export javascript "runParse" runParse :: JSString -> IO JSString
runParse = runParseSimplified

foreign export javascript "runElaborate" runElaborate :: JSString -> IO JSString
runElaborate = runElaborateSimplified

foreign export javascript "runSourceCheck" runSourceCheck :: JSString -> IO JSString
runSourceCheck = runSourceCheckSimplified

foreign export javascript "runDeBruijn" runDeBruijn :: JSString -> IO JSString
runDeBruijn = runDeBruijnSimplified

foreign export javascript "runCheck" runCheck :: JSString -> IO JSString
runCheck = runCheckSimplified

foreign export javascript "runEval" runEval :: JSString -> IO JSString
runEval = runEvalSimplified

foreign export javascript "runFull" runFull :: JSString -> IO JSString
runFull = runFullSimplified

-- CoreFE stages (default to Simplified)
foreign export javascript "coreParseExp" coreParseExp :: JSString -> IO JSString
coreParseExp = coreParseExpSimplified

foreign export javascript "coreCheck" coreCheck :: JSString -> IO JSString
coreCheck = coreCheckSimplified

foreign export javascript "coreEval" coreEval :: JSString -> IO JSString
coreEval = coreEvalSimplified

foreign export javascript "coreRun" coreRun :: JSString -> IO JSString
coreRun = coreRunSimplified

-- | Parse + Infer type of a CoreFE expression (Simplified)
foreign export javascript "coreCheckSimplified" coreCheckSimplified :: JSString -> IO JSString

coreCheckSimplified :: JSString -> IO JSString
coreCheckSimplified = safeRun $ \input ->
    let expr = CoreParser.parseExp (CoreLexer.lexer input)
    in case Check.infer [] expr of
        Nothing  -> "✗ Type Error\n\nCould not infer type"
        Just typ -> "✓ Type\n\n  " ++ PW.prettyDeBruijnTyp typ

-- | Parse + Eval a CoreFE expression (Simplified)
foreign export javascript "coreEvalSimplified" coreEvalSimplified :: JSString -> IO JSString

coreEvalSimplified :: JSString -> IO JSString
coreEvalSimplified = safeRun $ \input ->
    let expr = CoreParser.parseExp (CoreLexer.lexer input)
    in case Eval.eval [] expr of
        Nothing  -> "✗ Evaluation Error\n\nEvaluation got stuck"
        Just res -> "✓ Result\n\n  " ++ PW.prettyValueShort res

-- | Parse + Check + Eval a CoreFE expression (Simplified)
foreign export javascript "coreRunSimplified" coreRunSimplified :: JSString -> IO JSString

coreRunSimplified :: JSString -> IO JSString
coreRunSimplified = safeRun $ \input ->
    let expr = CoreParser.parseExp (CoreLexer.lexer input)
        typeStr = case Check.infer [] expr of
            Nothing  -> "✗ Type Error: Could not infer type"
            Just typ -> "Type   : " ++ PW.prettyDeBruijnTyp typ
        evalStr = case Eval.eval [] expr of
            Nothing  -> "✗ Eval Error: Got stuck"
            Just res -> "Result : " ++ PW.prettyValueShort res
    in typeStr ++ "\n" ++ evalStr

-------------------------------------------------------------------------------
-- Helper
-------------------------------------------------------------------------------

safeRun :: (String -> String) -> JSString -> IO JSString
safeRun f input = do
    let inputStr = fromJSString input
    result <- catch
        (evaluate $! f inputStr)
        (\(e :: SomeException) -> return $ "Error: " ++ show e)
    return $ toJSString result