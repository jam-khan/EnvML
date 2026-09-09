{-# LANGUAGE OverloadedStrings #-}

-- | The playground's entry points. Each pipeline stage is exported twice, once
--   rendered with the Pretty instances ("detailed") and once with PrettyWeb
--   ("simplified"); the unsuffixed names default to simplified.
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

main :: IO ()
main = error "This is a reactor module - call setup() from JavaScript"

foreign export javascript "setup" setup :: IO ()
setup :: IO ()
setup = return ()

parseModule :: String -> AST.Module
parseModule = Parser.parseModule . Lexer.lexer

-- | Elaboration can fail (an operand of a merge whose signature is undetermined,
--   say); 'safeRun' turns the message into playground output.
elaborate :: AST.Module -> CoreNamed.Exp
elaborate ast = either (error . ("Elaboration error: " ++)) id (Elab.elabModule ast)

-- | Source text through to the nameless core.
core :: String -> CoreFE.Exp
core = DeBruijn.toDeBruijn . elaborate . parseModule

parseCore :: String -> CoreFE.Exp
parseCore = CoreParser.parseExp . CoreLexer.lexer

-- | How one stage renders each intermediate form.
data Render = Render
  { rAst     :: AST.Module -> String
  , rNamed   :: CoreNamed.Exp -> String
  , rCore    :: CoreFE.Exp -> String
  , rTyp     :: CoreFE.Typ -> String
  , rVal     :: CoreFE.Exp -> String
  , rCoreTyp :: CoreFE.Typ -> String
  , rCoreVal :: CoreFE.Exp -> String
  , rSep     :: String
  }

detailed, simplified :: Render
detailed = Render AST.pretty CoreNamed.pretty CoreFE.pretty CoreFE.pretty CoreFE.pretty
                  CoreFE.pretty CoreFE.pretty "\n\n"
simplified = Render PW.prettyEnvMLModule PW.prettyNamedModule PW.prettyDeBruijnModule
                    PW.prettyCheckResult PW.prettyEvalResult PW.prettyDeBruijnTyp
                    PW.prettyValueShort "\n"

-- EnvML pipeline stages

envmlParse, envmlElab, envmlDeBruijn, envmlCheck, envmlEval, envmlFull
  :: Render -> JSString -> IO JSString
envmlParse r = safeRun $ \i -> "=== Parsed AST ===\n\n" ++ rAst r (parseModule i)
envmlElab r = safeRun $ \i ->
  "=== Elaborated (Named CoreFE) ===\n\n" ++ rNamed r (elaborate (parseModule i))
envmlDeBruijn r = safeRun $ \i ->
  "=== De Bruijn (Nameless CoreFE) ===\n\n" ++ rCore r (core i)
envmlCheck r = safeRun $ \i -> case Check.infer [] (core i) of
  Nothing  -> "✗ Type Error\n\nCould not infer type"
  Just typ -> "✓ Type Check Passed\n\n" ++ rTyp r typ
envmlEval r = safeRun $ \i -> case Eval.eval CoreFE.Unit (core i) of
  Nothing  -> "✗ Evaluation Error\n\nEvaluation got stuck"
  Just res -> "✓ Evaluation Result\n\n" ++ rVal r res
envmlFull r = safeRun $ \i ->
  let c = core i
      typeResult = maybe "✗ Type Error: Could not infer type"
                         (("✓ Types:\n" ++) . rTyp r) (Check.infer [] c)
      evalResult = maybe "✗ Evaluation Error: Got stuck"
                         (("✓ Values:\n" ++) . rVal r) (Eval.eval CoreFE.Unit c)
  in typeResult ++ rSep r ++ evalResult

-- CoreFE expressions, entered directly

coreParse, coreCheckIn, coreEvalIn, coreRunIn :: Render -> JSString -> IO JSString
coreParse _ = safeRun $ \i -> "=== Parsed CoreFE ===\n\n" ++ CoreFE.pretty (parseCore i)
coreCheckIn r = safeRun $ \i -> case Check.infer [] (parseCore i) of
  Nothing  -> "✗ Type Error\n\nCould not infer type"
  Just typ -> "✓ Type\n\n  " ++ rCoreTyp r typ
coreEvalIn r = safeRun $ \i -> case Eval.eval CoreFE.Unit (parseCore i) of
  Nothing  -> "✗ Evaluation Error\n\nEvaluation got stuck"
  Just res -> "✓ Result\n\n  " ++ rCoreVal r res
coreRunIn r = safeRun $ \i ->
  let e = parseCore i
      typeStr = maybe "✗ Type Error: Could not infer type"
                      (("Type   : " ++) . rCoreTyp r) (Check.infer [] e)
      evalStr = maybe "✗ Eval Error: Got stuck"
                      (("Result : " ++) . rCoreVal r) (Eval.eval CoreFE.Unit e)
  in typeStr ++ "\n" ++ evalStr

foreign export javascript "runParseDetailed" runParseDetailed :: JSString -> IO JSString
runParseDetailed = envmlParse detailed
foreign export javascript "runElaborateDetailed" runElaborateDetailed :: JSString -> IO JSString
runElaborateDetailed = envmlElab detailed
foreign export javascript "runDeBruijnDetailed" runDeBruijnDetailed :: JSString -> IO JSString
runDeBruijnDetailed = envmlDeBruijn detailed
foreign export javascript "runCheckDetailed" runCheckDetailed :: JSString -> IO JSString
runCheckDetailed = envmlCheck detailed
foreign export javascript "runEvalDetailed" runEvalDetailed :: JSString -> IO JSString
runEvalDetailed = envmlEval detailed
foreign export javascript "runFullDetailed" runFullDetailed :: JSString -> IO JSString
runFullDetailed = envmlFull detailed

foreign export javascript "runParseSimplified" runParseSimplified :: JSString -> IO JSString
runParseSimplified = envmlParse simplified
foreign export javascript "runElaborateSimplified" runElaborateSimplified :: JSString -> IO JSString
runElaborateSimplified = envmlElab simplified
foreign export javascript "runDeBruijnSimplified" runDeBruijnSimplified :: JSString -> IO JSString
runDeBruijnSimplified = envmlDeBruijn simplified
foreign export javascript "runCheckSimplified" runCheckSimplified :: JSString -> IO JSString
runCheckSimplified = envmlCheck simplified
foreign export javascript "runEvalSimplified" runEvalSimplified :: JSString -> IO JSString
runEvalSimplified = envmlEval simplified
foreign export javascript "runFullSimplified" runFullSimplified :: JSString -> IO JSString
runFullSimplified = envmlFull simplified

foreign export javascript "coreParseExpDetailed" coreParseExpDetailed :: JSString -> IO JSString
coreParseExpDetailed = coreParse detailed
foreign export javascript "coreCheckDetailed" coreCheckDetailed :: JSString -> IO JSString
coreCheckDetailed = coreCheckIn detailed
foreign export javascript "coreEvalDetailed" coreEvalDetailed :: JSString -> IO JSString
coreEvalDetailed = coreEvalIn detailed
foreign export javascript "coreRunDetailed" coreRunDetailed :: JSString -> IO JSString
coreRunDetailed = coreRunIn detailed

foreign export javascript "coreParseExpSimplified" coreParseExpSimplified :: JSString -> IO JSString
coreParseExpSimplified = coreParse simplified
foreign export javascript "coreCheckSimplified" coreCheckSimplified :: JSString -> IO JSString
coreCheckSimplified = coreCheckIn simplified
foreign export javascript "coreEvalSimplified" coreEvalSimplified :: JSString -> IO JSString
coreEvalSimplified = coreEvalIn simplified
foreign export javascript "coreRunSimplified" coreRunSimplified :: JSString -> IO JSString
coreRunSimplified = coreRunIn simplified

-- Unsuffixed names: the playground's defaults.
foreign export javascript "runParse" runParse :: JSString -> IO JSString
runParse = runParseSimplified
foreign export javascript "runElaborate" runElaborate :: JSString -> IO JSString
runElaborate = runElaborateSimplified
foreign export javascript "runDeBruijn" runDeBruijn :: JSString -> IO JSString
runDeBruijn = runDeBruijnSimplified
foreign export javascript "runCheck" runCheck :: JSString -> IO JSString
runCheck = runCheckSimplified
foreign export javascript "runEval" runEval :: JSString -> IO JSString
runEval = runEvalSimplified
foreign export javascript "runFull" runFull :: JSString -> IO JSString
runFull = runFullSimplified
foreign export javascript "coreParseExp" coreParseExp :: JSString -> IO JSString
coreParseExp = coreParseExpSimplified
foreign export javascript "coreCheck" coreCheck :: JSString -> IO JSString
coreCheck = coreCheckSimplified
foreign export javascript "coreEval" coreEval :: JSString -> IO JSString
coreEval = coreEvalSimplified
foreign export javascript "coreRun" coreRun :: JSString -> IO JSString
coreRun = coreRunSimplified

safeRun :: (String -> String) -> JSString -> IO JSString
safeRun f input = do
    result <- catch (evaluate $! f (fromJSString input))
                    (\(e :: SomeException) -> return ("Error: " ++ show e))
    return (toJSString result)
