
module EnvML.Parse
  ( parseEmlFile
  , parseEmliFile
  , collectImports
  , module EnvML.Syntax
  ) where

import EnvML.Syntax
import EnvML.Parser.Lexer (lexer)
import EnvML.Parser.Parser (parseModule, parseModuleTyp)

parseEmlFile :: FilePath -> IO Module
parseEmlFile path = parseModule . lexer <$> readFile path

parseEmliFile :: FilePath -> IO ModuleTyp
parseEmliFile path = parseModuleTyp . lexer <$> readFile path

-- | Collect top-level import names from a parsed module.
collectImports :: Module -> [Name]
collectImports (Struct structs) = [n | Import n <- structs]
collectImports _                = []