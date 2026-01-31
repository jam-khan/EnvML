module Core.Repl where

import System.IO (hFlush, stdout)
import Control.Exception (try, SomeException)

-- Your Project Modules
import Core.Syntax
import Core.Parser.Lexer (lexer)
import Core.Parser.Parser (parseExp)
import Core.Pretty
import Core.Eval (eval)
import Core.Check (infer)

main :: IO ()
main = do
  putStrLn "Welcome to the Calculus REPL"
  putStrLn "Commands: :t (test suite), :q (quit)"
  repl

repl :: IO ()
repl = do
  putStr "λ> "
  hFlush stdout
  input <- getLine
  case input of
    ":q" -> putStrLn "Goodbye!"
    _ | null input -> repl
    _ -> do
      handleInput input
      repl

handleInput :: String -> IO ()
handleInput str = do
  -- 1. Parse
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
