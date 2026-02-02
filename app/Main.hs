{-# LANGUAGE ScopedTypeVariables #-}

module Main where

import System.Console.Haskeline
import Control.Monad.IO.Class (liftIO)
import Control.Exception (catch, evaluate, SomeException)
import Data.List (stripPrefix)
import Data.Char (isSpace)

-- Import your modules
import qualified EnvML.Parser.Parser as Parser
import qualified EnvML.Parser.Lexer as Lexer
import qualified EnvML.Parser.AST as AST
import qualified EnvML.Desugar as Desugar
import qualified EnvML.DeBruijn as DeBruijn
import qualified EnvML.Syntax as EnvML
import qualified EnvML.Elab as Elab
import qualified Core.Syntax as Core
import qualified Core.Check as Check
import qualified Core.Eval as Eval
import Core.Pretty (stringOfExp, stringOfTyp)

main :: IO ()
main = do
  putStrLn banner
  runInputT settings repl

banner :: String
banner = unlines
  [ "╔══════════════════════════════════════════════════════════════╗"
  , "║                    EnvML REPL v0.1                           ║"
  , "║  A Module System with First-Class Environments               ║"
  , "╠══════════════════════════════════════════════════════════════╣"
  , "║  Pipeline: Source → Desugar → DeBruijn → Elaborate → Core    ║"
  , "║  Type :help for available commands                           ║"
  , "╚══════════════════════════════════════════════════════════════╝"
  ]

settings :: Settings IO
settings = Settings
  { complete       = completeFilename
  , historyFile    = Just ".envml_history"
  , autoAddHistory = True
  }

repl :: InputT IO ()
repl = do
  minput <- getInputLine "envml> "
  case minput of
    Nothing      -> outputStrLn "Goodbye!"
    Just ":quit" -> outputStrLn "Goodbye!"
    Just ":q"    -> outputStrLn "Goodbye!"
    Just input   -> do
      liftIO $ processCommand (trim input)
      repl

trim :: String -> String
trim = dropWhile isSpace . reverse . dropWhile isSpace . reverse

processCommand :: String -> IO ()
processCommand "" = return ()
processCommand cmd
  | cmd == ":help" || cmd == ":h" = printHelp
  | Just path <- stripPrefix ":p " cmd     = cmdParse (trim path)
  | Just path <- stripPrefix ":d " cmd     = cmdDesugar (trim path)
  | Just path <- stripPrefix ":n " cmd     = cmdDeBruijn (trim path)
  | Just path <- stripPrefix ":e " cmd     = cmdElaborate (trim path)
  | Just path <- stripPrefix ":check " cmd = cmdCheck (trim path)
  | Just path <- stripPrefix ":eval " cmd  = cmdEval (trim path)
  | Just path <- stripPrefix ":c " cmd     = cmdCheck (trim path)
  | Just path <- stripPrefix ":v " cmd     = cmdEval (trim path)
  | otherwise = putStrLn $ "Unknown command: " ++ cmd ++ "\nType :help for available commands."

printHelp :: IO ()
printHelp = putStrLn $ unlines
  [ ""
  , "┌─────────────────────────────────────────────────────────────────┐"
  , "│                     EnvML REPL Commands                        │"
  , "├─────────────────────────────────────────────────────────────────┤"
  , "│  :p <file>     Parse and print AST                             │"
  , "│  :d <file>     Parse → Desugar → Print                         │"
  , "│  :n <file>     Parse → Desugar → De Bruijn → Print             │"
  , "│  :e <file>     Parse → Desugar → De Bruijn → Elaborate → Print │"
  , "│  :check <file> Full pipeline → Type check → Print result       │"
  , "│  :eval <file>  Full pipeline → Evaluate → Print result         │"
  , "│  :c <file>     (shorthand for :check)                          │"
  , "│  :v <file>     (shorthand for :eval)                           │"
  , "│  :help, :h     Show this help                                  │"
  , "│  :quit, :q     Exit the REPL                                   │"
  , "├─────────────────────────────────────────────────────────────────┤"
  , "│                     Pipeline Overview                          │"
  , "├─────────────────────────────────────────────────────────────────┤"
  , "│  1. Parse      Source text → EnvML.Parser.AST.Module           │"
  , "│  2. Desugar    Multi-arg → Single-arg, FunctorDecl → ModDecl   │"
  , "│  3. De Bruijn  Names → Indices (EnvML.Syntax.Module)           │"
  , "│  4. Elaborate  EnvML.Syntax → Core.Syntax (System F + Env)     │"
  , "│  5. Check      Type inference/checking at Core level           │"
  , "│  6. Eval       Evaluation at Core level                        │"
  , "└─────────────────────────────────────────────────────────────────┘"
  , ""
  ]

-------------------------------------------------------------------------------
-- File Reading and Parsing
-------------------------------------------------------------------------------

safeReadFile :: FilePath -> IO (Either String String)
safeReadFile path = do
  (Right <$> readFile path) `catch` handler
  where
    handler :: SomeException -> IO (Either String String)
    handler e = return $ Left $ "Error reading file '" ++ path ++ "': " ++ show e

-- | Parse with error handling for Happy-generated parser errors
safeParse :: String -> IO (Either String AST.Module)
safeParse content = do
  let tokens = Lexer.lexer content
  -- evaluate forces the parse result, catching any 'error' calls from Happy
  (Right <$> evaluate (Parser.parseModule tokens)) `catch` handler
  where
    handler :: SomeException -> IO (Either String AST.Module)
    handler e = return $ Left $ "Parse error: " ++ show e

readAndParse :: FilePath -> IO (Either String AST.Module)
readAndParse path = do
  result <- safeReadFile path
  case result of
    Left err -> return $ Left err
    Right content -> safeParse content

-------------------------------------------------------------------------------
-- Pipeline Helpers
-------------------------------------------------------------------------------

runPipeline :: FilePath 
            -> (AST.Module -> IO ()) 
            -> IO ()
runPipeline path action = do
  result <- readAndParse path
  case result of
    Left err  -> putStrLn $ "Error: " ++ err
    Right ast -> action ast

desugarModule :: AST.Module -> AST.Module
desugarModule = Desugar.desugarModule

toDeBruijn :: AST.Module -> EnvML.Module
toDeBruijn = DeBruijn.modToDeBruijn . desugarModule

elaborate :: AST.Module -> Either String Core.Exp
elaborate ast = Elab.elabM (toDeBruijn ast)

-------------------------------------------------------------------------------
-- Commands
-------------------------------------------------------------------------------

cmdParse :: FilePath -> IO ()
cmdParse path = runPipeline path $ \ast -> do
  putStrLn "=== Parsed AST ==="
  putStrLn $ AST.pretty ast

cmdDesugar :: FilePath -> IO ()
cmdDesugar path = runPipeline path $ \ast -> do
  let desugared = desugarModule ast
  putStrLn "=== Desugared AST ==="
  putStrLn $ AST.pretty desugared

cmdDeBruijn :: FilePath -> IO ()
cmdDeBruijn path = runPipeline path $ \ast -> do
  let nameless = toDeBruijn ast
  putStrLn "=== De Bruijn AST ==="
  print $ EnvML.pretty nameless

cmdElaborate :: FilePath -> IO ()
cmdElaborate path = runPipeline path $ \ast -> do
  case elaborate ast of
    Left err -> putStrLn $ "Elaboration error: " ++ err
    Right coreExp -> do
      putStrLn "=== Elaborated Core ==="
      print $ stringOfExp coreExp

cmdCheck :: FilePath -> IO ()
cmdCheck path = runPipeline path $ \ast -> do
  case elaborate ast of
    Left err -> putStrLn $ "Elaboration error: " ++ err
    Right coreExp -> do
      putStrLn "=== Type Checking ==="
      case Check.infer [] coreExp of
        Nothing -> putStrLn "✗ Type check failed: Could not infer type"
        Just typ -> do
          putStrLn "✓ Type check succeeded!"
          putStrLn $ "  Type: " ++ stringOfTyp typ

cmdEval :: FilePath -> IO ()
cmdEval path = runPipeline path $ \ast -> do
  case elaborate ast of
    Left err -> putStrLn $ "Elaboration error: " ++ err
    Right coreExp -> do
      -- Optionally type check first
      case Check.infer [] coreExp of
        Nothing -> putStrLn "Warning: Type check failed, attempting evaluation anyway..."
        Just typ -> putStrLn $ "Type: " ++ show typ
      putStrLn "=== Evaluation ==="
      case Eval.eval [] coreExp of
        Nothing -> putStrLn "✗ Evaluation failed"
        Just result -> do
          putStrLn "✓ Result:"
          putStrLn $ stringOfExp result