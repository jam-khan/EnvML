
module EnvML.Parse
  ( parseEmlFile
  , parseEmliFile
  , compileEmlFile
  , module EnvML.Syntax
  ) where

import EnvML.Syntax
import EnvML.Parser.Lexer (lexer)
import EnvML.Parser.Parser (parseModule, parseModuleTyp)
import qualified EnvML.Desugar as Desugar
import qualified EnvML.Desugared as D
import System.FilePath (takeDirectory, (</>) , replaceExtension)

parseEmlFile :: FilePath -> IO Module
parseEmlFile path = parseModule . lexer <$> readFile path

parseEmliFile :: FilePath -> IO ModuleTyp
parseEmliFile path = parseModuleTyp . lexer <$> readFile path

-- | Collect top-level import names from a parsed module.
collectImports :: Module -> [Name]
collectImports (Struct structs) = [n | Import n <- structs]
collectImports _                = []

-- | Parse an .eml file, resolve each import by reading the corresponding
-- .emli file in the same directory, and desugar with import types.
-- Also reads <file>.emli as the main module's own signature and wraps the
-- result in an annotation so the core type checker can check parameterised
-- modules (which elaborate to unannotated lambdas in CoreFE).
compileEmlFile :: FilePath -> IO D.Module
compileEmlFile path = do
  m <- parseEmlFile path
  let baseDir     = takeDirectory path
      importNames = collectImports m
  importTypes <- mapM (\n -> fmap (\mty -> (n, mty)) (parseEmliFile (baseDir </> n ++ ".emli"))) importNames
  mainSig     <- parseEmliFile (replaceExtension path ".emli")
  let desugared      = Desugar.desugarModuleWithImports importTypes m
      annotationType = foldr (\(_, impSig) acc -> TyArrowM (TyModule impSig) acc) mainSig importTypes
  return $ D.MAnno desugared annotationType
