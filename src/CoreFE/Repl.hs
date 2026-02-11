module CoreFE.Repl where

import Control.Exception (try, SomeException)
import Control.Monad.IO.Class (liftIO) -- Necessary to run IO inside Haskeline

-- Your Project Modules
import CoreFE.Syntax ( Exp, stringOfTyp, stringOfExp )
import CoreFE.Parser.Lexer (lexer)
import CoreFE.Parser.Parser (parseExp)
import CoreFE.Eval (eval)
import CoreFE.Check (infer)
import System.Console.Haskeline
    ( InputT, defaultSettings, getInputLine, outputStrLn, runInputT )

main :: IO ()
main = do
  putStrLn "Welcome to the Calculus REPL"
  putStrLn "Commands: :t (test suite), :q (quit)"
  -- You must wrap the Haskeline monad with runInputT
  runInputT defaultSettings repl

repl :: InputT IO ()
repl = do
  minput <- getInputLine "λ.∀> "
  case minput of
    Nothing      -> outputStrLn "Goodbye!" -- Handles Ctrl-D
    Just input -> 
      case input of
        ":q"    -> outputStrLn "Goodbye!"
        ":quit" -> outputStrLn "Goodbye!"
        ""      -> repl -- Handle empty input (just loop again)
        _       -> do
          -- handleInput is IO, so we must lift it to InputT IO
          liftIO $ handleInput input
          repl

handleInput :: String -> IO ()
handleInput str = do
  -- 1. Parse
  -- We use ($!) to force evaluation to catch pure exceptions from the parser
  exprRes <- try (return $! parseExp (lexer str)) :: IO (Either SomeException Exp)
  case exprRes of
    Left err -> putStrLn $ "Parse Error: " ++ show err
    Right e  -> do
      -- 2. Type Check (Inference)
      case infer [] e of
        Nothing -> putStrLn "Type Error: Could not infer type"
        Just t  -> do
          putStrLn $ "Type   : " ++ stringOfTyp t
          -- 3. Evaluate
          case eval [] e of
            Nothing -> putStrLn "Eval Error: Evaluation failed"
            Just v  -> putStrLn $ "Result : " ++ stringOfExp v