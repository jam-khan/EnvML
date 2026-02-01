
module EnvML.Parse
  ( parseEmlFile
  , parseEmliFile
  , module EnvML.Parser.AST
  ) where

import EnvML.Parser.AST
import EnvML.Parser.Lexer (lexer)
import EnvML.Parser.Parser (parseModule, parseModuleTyp)

parseEmlFile :: FilePath -> IO Module
parseEmlFile path = parseModule . lexer <$> readFile path

parseEmliFile :: FilePath -> IO ModuleTyp
parseEmliFile path = parseModuleTyp . lexer <$> readFile path
