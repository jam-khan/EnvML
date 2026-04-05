{-# LANGUAGE ScopedTypeVariables #-}
module Repl where

import System.Console.Haskeline
    ( InputT,
      Settings(..),
      getInputLine,
      outputStrLn,
      completeFilename )
import Control.Monad.IO.Class (liftIO)
import Control.Exception (catch, evaluate, SomeException)
import Data.List (stripPrefix)
import Data.Char (isSpace)

import qualified EnvML.Parser.Parser as Parser
import qualified EnvML.Parser.Lexer as Lexer
import qualified EnvML.Syntax as AST
import qualified EnvML.Elab as Elab
import qualified EnvML.Desugar as Desugar
import qualified EnvML.Desugared as Desugared
import qualified EnvML.Parse as Parse
import qualified CoreFE.Named as CoreNamed
import qualified CoreFE.Syntax as CoreFE
import qualified CoreFE.Check as Check
import qualified CoreFE.Eval as Eval
import qualified CoreFE.DeBruijn as DeBruijn
import qualified EnvML.Check as SCheck

banner :: String
banner = unlines
  [ "╔══════════════════════════════════════════════════════════════╗"
  , "║                    EnvML REPL v0.1                           ║"
  , "║  A Module System with First-Class Environments               ║"
  , "╠══════════════════════════════════════════════════════════════╣"
  , "║  Pipeline: Source → Parse → Desugar → Elaborate → CoreFE          ║"
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
  | Just path <- stripPrefix ":sc " cmd    = cmdSourceCheck (trim path)
  | Just path <- stripPrefix ":e " cmd     = cmdElaborate (trim path)
  | Just path <- stripPrefix ":n " cmd     = cmdDeBruijn (trim path)
  | Just path <- stripPrefix ":check " cmd = cmdCheck (trim path)
  | Just path <- stripPrefix ":eval " cmd  = cmdEval (trim path)
  | Just path <- stripPrefix ":sep-sc " cmd = cmdSepSourceCheck (trim path)
  | Just path <- stripPrefix ":sep-e " cmd  = cmdSepElab (trim path)
  | Just path <- stripPrefix ":sep-c " cmd  = cmdSepCheck (trim path)
  | Just path <- stripPrefix ":sep-d " cmd  = cmdSep (trim path)
  | Just path <- stripPrefix ":c " cmd     = cmdCheck (trim path)
  | Just path <- stripPrefix ":v " cmd     = cmdEval (trim path)
  | otherwise = putStrLn $ "Unknown command: " ++ cmd ++ "\nType :help for available commands."

printHelp :: IO ()
printHelp = putStrLn $ unlines
  [ ""
  , "┌─────────────────────────────────────────────────────────────────┐"
  , "│                     EnvML REPL Commands                        │"
  , "├─────────────────────────────────────────────────────────────────┤"
  , "│  Single-file pipeline                                          │"
  , "├─────────────────────────────────────────────────────────────────┤"
  , "│  :p <file>     Parse and print AST                             │"
  , "│  :d <file>     Parse → Desugar → Print                         │"
  , "│  :sc <file>    Parse → Desugar → Source type check             │"
  , "│  :e <file>     Parse → Desugar → Elaborate (CoreFE.Named)      │"
  , "│  :n <file>     Parse → Desugar → Elaborate → De Bruijn         │"
  , "│  :check <file> Full pipeline → Core type check                 │"
  , "│  :eval <file>  Full pipeline → Evaluate                        │"
  , "│  :c <file>     (shorthand for :check)                          │"
  , "│  :v <file>     (shorthand for :eval)                           │"
  , "├─────────────────────────────────────────────────────────────────┤"
  , "│  Separate compilation (import-aware)                           │"
  , "├─────────────────────────────────────────────────────────────────┤"
  , "│  :sep-d    <file>  Resolve imports → Desugar → Print           │"
  , "│  :sep-sc <file>  → Source type check                           │"
  , "│  :sep-e  <file>  → Elaborate (CoreFE.Named)                    │"
  , "│  :sep-c  <file>  → Core type check                             │"
  , "├─────────────────────────────────────────────────────────────────┤"
  , "│  :help, :h     Show this help                                  │"
  , "│  :quit, :q     Exit the REPL                                   │"
  , "└─────────────────────────────────────────────────────────────────┘"
  , ""
  ]

safeReadFile :: FilePath -> IO (Either String String)
safeReadFile path = do
  (Right <$> readFile path) `catch` handler
  where
    handler :: SomeException -> IO (Either String String)
    handler e = return $ Left $ "Error reading file '" ++ path ++ "': " ++ show e

safeParse :: String -> IO (Either String AST.Module)
safeParse content = do
  let tokens = Lexer.lexer content
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

runPipeline :: FilePath 
            -> (AST.Module -> IO ()) 
            -> IO ()
runPipeline path action = do
  result <- readAndParse path
  case result of
    Left err  -> putStrLn $ "Error: " ++ err
    Right ast -> action ast

elaborate :: AST.Module -> CoreNamed.Exp
elaborate = Elab.elabModule . Desugar.desugarModule

toDeBruijn :: CoreNamed.Exp -> CoreFE.Exp
toDeBruijn = DeBruijn.toDeBruijn

cmdParse :: FilePath -> IO ()
cmdParse path = runPipeline path $ \ast -> do
  putStrLn "=== Parsed AST ==="
  putStrLn $ AST.pretty ast

cmdDesugar :: FilePath -> IO ()
cmdDesugar path = runPipeline path $ \ast -> do
  let desugared = Desugar.desugarModule ast
  putStrLn "=== Desugared AST ==="
  putStrLn $ Desugared.prettyModule desugared

cmdSourceCheck :: FilePath -> IO ()
cmdSourceCheck path = runPipeline path $ \ast -> do
  putStrLn "=== Source Type Checking ==="
  let desugared = Desugar.desugarModule ast
  case desugared of
    Desugared.Struct structs -> case SCheck.inferStructs [] structs of
      Nothing -> putStrLn "✗ Source type check failed: Could not infer types"
      Just intf -> do
        putStrLn "✓ Source type check succeeded!"
        putStrLn $ AST.prettyIntf intf
    _ -> case SCheck.inferMod [] desugared of
      Nothing -> putStrLn "✗ Source type check failed: Could not infer module type"
      Just mty -> do
        putStrLn "✓ Source type check succeeded!"
        putStrLn $ AST.prettyModuleTyp mty

cmdElaborate :: FilePath -> IO ()
cmdElaborate path = runPipeline path $ \ast -> do
  let coreNamed = elaborate ast
  putStrLn "=== Elaborated CoreFE (Named) ==="
  print coreNamed

cmdDeBruijn :: FilePath -> IO ()
cmdDeBruijn path = runPipeline path $ \ast -> do
  let coreNamed = elaborate ast
  let coreNameless = toDeBruijn coreNamed
  putStrLn "=== De Bruijn Core (Nameless) ==="
  putStrLn $ show coreNameless
  putStrLn $ CoreFE.pretty coreNameless

cmdCheck :: FilePath -> IO ()
cmdCheck path = runPipeline path $ \ast -> do
  let coreNamed = elaborate ast
  let coreNameless = toDeBruijn coreNamed
  putStrLn "=== Type Checking ==="
  case Check.infer [] coreNameless of
    Nothing -> putStrLn "✗ Type check failed: Could not infer type"
    Just typ -> do
      putStrLn "✓ Type check succeeded!"

cmdEval :: FilePath -> IO ()
cmdEval path = runPipeline path $ \ast -> do
  let coreNamed = elaborate ast
  let coreNameless = toDeBruijn coreNamed
  
  -- Optionally type check first
  case Check.infer [] coreNameless of
    Nothing -> putStrLn "Warning: Type check failed, attempting evaluation anyway..."
    Just typ -> putStrLn $ "Type: " ++ CoreFE.pretty typ
  
  putStrLn "=== Evaluation ==="
  case Eval.eval [] coreNameless of
    Nothing -> putStrLn "✗ Evaluation failed"
    Just result -> do
      putStrLn "✓ Result:"
      putStrLn $ "  " ++ CoreFE.pretty result

-- | Parse an .eml file, resolve imports from neighbouring .emli files, desugar.
cmdSep :: FilePath -> IO ()
cmdSep path = do
  result <- (Right <$> Parse.compileEmlFile path) `Control.Exception.catch` handler
  case result of
    Left err      -> putStrLn $ "Error: " ++ err
    Right desugared -> do
      putStrLn "=== Sep: Imports resolved, desugared ==="
      putStrLn $ Desugared.prettyModule desugared
  where
    handler :: SomeException -> IO (Either String Desugared.Module)
    handler e = return $ Left $ show e

cmdSepSourceCheck :: FilePath -> IO ()
cmdSepSourceCheck path = do
  result <- (Right <$> Parse.compileEmlFile path) `Control.Exception.catch` handler
  case result of
    Left err -> putStrLn $ "Error: " ++ err
    Right desugared -> do
      putStrLn "=== Sep: Source type checking ==="
      case desugared of
        Desugared.Struct structs -> case SCheck.inferStructs [] structs of
          Nothing   -> putStrLn "✗ Source type check failed"
          Just intf -> putStrLn "✓ Source type check succeeded!" >> putStrLn (AST.prettyIntf intf)
        _ -> case SCheck.inferMod [] desugared of
          Nothing  -> putStrLn "✗ Source type check failed"
          Just mty -> putStrLn "✓ Source type check succeeded!" >> putStrLn (AST.prettyModuleTyp mty)
  where
    handler :: SomeException -> IO (Either String Desugared.Module)
    handler e = return $ Left $ show e

cmdSepElab :: FilePath -> IO ()
cmdSepElab path = do
  result <- (Right <$> Parse.compileEmlFile path) `Control.Exception.catch` handler
  case result of
    Left err -> putStrLn $ "Error: " ++ err
    Right desugared -> do
      let coreNamed = Elab.elabModule desugared
      putStrLn "=== Sep: Elaborated CoreFE (Named) ==="
      print coreNamed
  where
    handler :: SomeException -> IO (Either String Desugared.Module)
    handler e = return $ Left $ show e

cmdSepCheck :: FilePath -> IO ()
cmdSepCheck path = do
  result <- (Right <$> Parse.compileEmlFile path) `Control.Exception.catch` handler
  case result of
    Left err -> putStrLn $ "Error: " ++ err
    Right desugared -> do
      let coreNamed     = Elab.elabModule desugared
          coreNameless  = DeBruijn.toDeBruijn coreNamed
      putStrLn "=== Sep: Core type checking ==="
      case Check.infer [] coreNameless of
        Nothing  -> putStrLn "✗ Core type check failed"
        Just typ -> putStrLn "✓ Core type check succeeded!" >> putStrLn ("  Type: " ++ CoreFE.pretty typ)
  where
    handler :: SomeException -> IO (Either String Desugared.Module)
    handler e = return $ Left $ show e