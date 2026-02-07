{-# LANGUAGE ScopedTypeVariables #-}

module Main where

import System.Console.Haskeline (runInputT)
import Control.Monad.IO.Class (liftIO)
import Control.Exception (catch, evaluate, SomeException)
import Data.List (stripPrefix)
import Data.Char (isSpace)
import Repl ( banner, settings, repl )

main :: IO ()
main = do
  putStrLn banner
  runInputT settings repl
