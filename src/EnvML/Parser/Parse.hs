
module EnvML.Parser.Parse
  ( parseEmlFile
  , parseEmliFile
  , module EnvML.Parser.AST
  ) where

import EnvML.Parser.AST
import EnvML.Parser.HappyAlex.Lexer (lexer)
import EnvML.Parser.HappyAlex.Parser (parseModule, parseModuleTyp)

parseEmlFile :: FilePath -> IO Module
parseEmlFile path = parseModule . lexer <$> readFile path

parseEmliFile :: FilePath -> IO ModuleTyp
parseEmliFile path = parseModuleTyp . lexer <$> readFile path
