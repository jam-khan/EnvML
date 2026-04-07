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
import Data.List (stripPrefix, isPrefixOf, isSuffixOf)
import Data.Char (isSpace)
import System.FilePath (replaceExtension, takeDirectory, (</>))
import System.Directory (listDirectory, removeFile)

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
import Debug.Trace

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
  | Just path <- stripPrefix ":sep-sc " cmd    = cmdSepSourceCheck (trim path)
  | Just path <- stripPrefix ":sep-eval " cmd  = cmdSepEval (trim path)
  | Just path <- stripPrefix ":sep-e " cmd     = cmdSepElab (trim path)
  | Just path <- stripPrefix ":sep-n " cmd     = cmdSepDeBruijn (trim path)
  | Just path <- stripPrefix ":sep-c " cmd     = cmdSepCheck (trim path)
  | Just path <- stripPrefix ":sep-d " cmd     = cmdSep (trim path)
  | Just path <- stripPrefix ":sep-obj " cmd   = cmdSepObj (trim path)
  | Just args <- stripPrefix ":sep-link " cmd  = cmdSepLink (trim args)
  | Just path <- stripPrefix ":sep-info " cmd  = cmdSepInfo (trim path)
  | Just path <- stripPrefix ":l " cmd        = cmdLoad (trim path)
  | Just dir  <- stripPrefix ":clean " cmd    = cmdClean (trim dir)
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
  , "│  :sep-sc   <file> → Source type check                          │"
  , "│  :sep-e    <file> → Elaborate (CoreFE.Named)                   │"
  , "│  :sep-n    <file> → De Bruijn (nameless)                        │"
  , "│  :sep-c    <file> → Core type check                            │"
  , "│  :sep-obj  <file>          → Compile → write .emlo              │"
  , "│  :sep-link <f.emlo> [deps.emle] → App-fold + type check → .emle │"
  , "│  :sep-eval <f.emle>        → Evaluate linked file               │"
  , "│  :sep-info <f.emlo>        → Display .emlo contents             │"
  , "├─────────────────────────────────────────────────────────────────┤"
  , "│  Utilities                                                     │"
  , "├─────────────────────────────────────────────────────────────────┤"
  , "│  :l <file>     Load and execute a .repl script                 │"
  , "│  :clean <dir>  Remove .emlo and .emle files in directory       │"
  , "├─────────────────────────────────────────────────────────────────┤"
  , "│  :help, :h     Show this help                                  │"
  , "│  :quit, :q     Exit the REPL                                   │"
  , "└─────────────────────────────────────────────────────────────────┘"
  , ""
  ]

cmdLoad :: FilePath -> IO ()
cmdLoad path = do
  result <- (Right <$> readFile path) `catch` handler
  case result of
    Left err -> putStrLn $ "Error loading script '" ++ path ++ "': " ++ err
    Right contents -> do
      let cmds = filter (not . isComment) $ map trim $ lines contents
      mapM_ (\c -> putStrLn ("envml> " ++ c) >> processCommand c) cmds
  where
    handler :: SomeException -> IO (Either String String)
    handler e = return $ Left $ show e
    isComment s = null s || "--" `isPrefixOf` s

cmdClean :: FilePath -> IO ()
cmdClean dir = do
  result <- (Right <$> listDirectory dir) `catch` handler
  case result of
    Left err -> putStrLn $ "Error: " ++ err
    Right entries -> do
      let targets = filter (\f -> ".emlo" `isSuffixOf` f || ".emle" `isSuffixOf` f) entries
      mapM_ (\f -> let fp = dir </> f in removeFile fp >> putStrLn ("  removed: " ++ fp)) targets
      putStrLn $ "✓ Cleaned " ++ show (length targets) ++ " file(s) in " ++ dir
  where
    handler :: SomeException -> IO (Either String [FilePath])
    handler e = return $ Left $ show e

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
  case SCheck.inferMod [] desugared of
    Nothing  -> putStrLn "✗ Source type check failed"
    Just mty -> putStrLn "✓ Source type check succeeded!" >> putStrLn (AST.prettyModuleTyp mty)

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
  result <- (Right <$> Desugar.resolveImports path) `Control.Exception.catch` handler
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
  result <- (Right <$> Desugar.resolveImports path) `Control.Exception.catch` handler
  case result of
    Left err -> putStrLn $ "Error: " ++ err
    Right desugared -> do
      putStrLn "=== Sep: Source type checking ==="
      case SCheck.inferMod [] desugared of
        Nothing  -> trace (show (desugared)) $ putStrLn "✗ Source type check failed"
        Just mty -> putStrLn "✓ Source type check succeeded!" >> putStrLn (AST.prettyModuleTyp mty)
  where
    handler :: SomeException -> IO (Either String Desugared.Module)
    handler e = return $ Left $ show e


cmdSepElab :: FilePath -> IO ()
cmdSepElab path = do
  result <- (Right <$> Desugar.resolveImports path) `Control.Exception.catch` handler
  case result of
    Left err -> putStrLn $ "Error: " ++ err
    Right desugared -> do
      let coreNamed = Elab.elabModule desugared
      putStrLn "=== Sep: Elaborated CoreFE (Named) ==="
      print coreNamed
  where
    handler :: SomeException -> IO (Either String Desugared.Module)
    handler e = return $ Left $ show e

cmdSepDeBruijn :: FilePath -> IO ()
cmdSepDeBruijn path = do
  result <- (Right <$> Desugar.resolveImports path) `Control.Exception.catch` handler
  case result of
    Left err -> putStrLn $ "Error: " ++ err
    Right desugared -> do
      let coreNamed    = Elab.elabModule desugared
          coreNameless = DeBruijn.toDeBruijn coreNamed
      putStrLn "=== Sep: De Bruijn (Nameless) ==="
      putStrLn $ CoreFE.pretty coreNameless
  where
    handler :: SomeException -> IO (Either String Desugared.Module)
    handler e = return $ Left $ show e

-- | Object file format: bundles the serialized expression with the
data ObjFile = ObjFile
  { objDeps :: [String]   -- names of imported modules (not actually used in linking, just for info)
  , objExp  :: CoreFE.Exp -- nameless De Bruijn expression
  } deriving (Show, Read)

-- | Compile .eml file (resolving imports) and write .emlo object file.
-- The .emlo contains the serialized ObjFile (deps + De Bruijn expression).
cmdSepObj :: FilePath -> IO ()
cmdSepObj path = do
  result <- (Right <$> Desugar.resolveImports path) `Control.Exception.catch` handler
  case result of
    Left err -> putStrLn $ "Error: " ++ err
    Right desugared -> do
      -- Source type check
      putStrLn "=== Sep: Source type checking ==="
      case SCheck.inferMod [] desugared of
        Nothing -> putStrLn "✗ Source type check failed" >> return ()
        Just _  -> do
          putStrLn "✓ Source type check succeeded!"
          -- Core type check
          let coreNamed    = Elab.elabModule desugared
              coreNameless = DeBruijn.toDeBruijn coreNamed
          putStrLn "=== Sep: Core type checking ==="
          case Check.infer [] coreNameless of
            Nothing  -> putStrLn "✗ Core type check failed" >> return ()
            Just typ -> do
              putStrLn "✓ Core type check succeeded!"
              putStrLn $ "  Type: " ++ CoreFE.pretty typ
              srcMod <- Parse.parseEmlFile path
              let deps     = Parse.collectImports srcMod
                  obj      = ObjFile { objDeps = deps, objExp = coreNameless }
                  emloPath = replaceExtension path ".emlo"
              writeFile emloPath (show obj)
              putStrLn $ "✓ Object file written: " ++ emloPath
  where
    handler :: SomeException -> IO (Either String Desugared.Module)
    handler e = return $ Left $ show e

-- | Link: fold App over dep .emle files onto a .emlo object, core type check,
-- write the linked (unevaluated) expression to .emle.
-- Usage: :sep-link <main.emlo> [dep1.emle dep2.emle ...]
cmdSepLink :: String -> IO ()
cmdSepLink args = do
  result <- doLink `Control.Exception.catch` handler
  case result of
    Left err -> putStrLn $ "Error: " ++ err
    Right _  -> return ()
  where
    handler :: SomeException -> IO (Either String ())
    handler e = return $ Left $ show e
    doLink = case words args of
      [] -> return $ Left "Usage: :sep-link <main.emlo> [dep1.emle ...]"
      (mainPath:depPaths) -> do
        let emlePath = replaceExtension mainPath ".emle"
        mainContents <- readFile mainPath
        let mainExp = objExp (read mainContents :: ObjFile)
        depExps <- mapM (\p -> (read :: String -> CoreFE.Exp) <$> readFile p) depPaths
        let linked = foldl CoreFE.App mainExp depExps
        putStrLn "=== Sep: Linking ==="
        case Check.infer [] linked of
          Nothing -> do
            putStrLn "\x2717 Core type check failed after linking"
            return $ Left "type check failed"
          Just typ -> do
            putStrLn "\x2713 Core type check succeeded!"
            putStrLn $ "  Type: " ++ CoreFE.pretty typ
            writeFile emlePath (show linked)
            putStrLn $ "\x2713 Linked expression written to: " ++ emlePath
            return $ Right ()

-- | Evaluate .emle file + print
cmdSepEval :: FilePath -> IO ()
cmdSepEval path = do
  result <- (Right <$> readFile path) `catch` handler
  case result of
    Left err -> putStrLn $ "Error: " ++ err
    Right contents -> do
      let expr = read contents :: CoreFE.Exp
      putStrLn "=== Sep: Evaluation ==="
      case Eval.eval [] expr of
        Nothing  -> putStrLn "\x2717 Evaluation failed"
        Just val -> putStrLn "\x2713 Result:" >> putStrLn ("  " ++ CoreFE.pretty val)
  where
    handler :: SomeException -> IO (Either String String)
    handler e = return $ Left $ show e

-- | Display the contents of a .emlo object file.
cmdSepInfo :: FilePath -> IO ()
cmdSepInfo path = do
  result <- (Right <$> readFile path) `catch` handler
  case result of
    Left err -> putStrLn $ "Error: " ++ err
    Right contents -> do
      let obj = read contents :: ObjFile
      putStrLn $ "=== Object file: " ++ path ++ " ==="
      putStrLn $ "  Dependencies: " ++ show (objDeps obj)
      putStrLn   "  Expression:"
      putStrLn $ "    " ++ CoreFE.pretty (objExp obj)
  where
    handler :: SomeException -> IO (Either String String)
    handler e = return $ Left $ show e

cmdSepCheck :: FilePath -> IO ()
cmdSepCheck path = do
  result <- (Right <$> Desugar.resolveImports path) `Control.Exception.catch` handler
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