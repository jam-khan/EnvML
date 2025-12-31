{- |
Module      : EnvML.Manager.Implementation
Description : Module is responsible for parsing and loading of multiple implementation files.
Copyright   : (c) Jam Kabeer Ali Khan, 2025
License     : MIT
Maintainer  : jamkhan@connect.hku.hk
Stability   : experimental

Key functionalities:
- Functionality 1: Parse multiple implementation files.
- Functionality 2: Structure these implementation files.

For more details, see the individual function documentation.
-}
module EnvML.Manager.Implementation where

import Control.Exception (IOException, try)
import Data.Either (rights)
import Data.List
import EnvML.Interpreter (desugarSource, locallyNameless, parseCode, typeAliasExpansion)
import EnvML.Errors (InterpreterError (..))
import Syntax (SourceTm)
import EnvML.Utils (readFileSafe)
import System.FilePath (takeBaseName, takeFileName)

-- `readInterfaceFiles` basically takes filepaths of multiple interface files
-- and reads each with some basic checks on files.
--
-- returns the content of the files.
readImplementationFiles ::
    [FilePath] ->
    IO [String]
readImplementationFiles files = do
    -- Check all files have .ep extension first
    case partition (".ep" `Data.List.isSuffixOf`) files of
        (_, []) -> do
            -- All files are valid
            contents <- mapM readFileSafe files
            return (rights contents)
        (_, invalidFiles) ->
            fail $ "These files must have .ep extension: " ++ show invalidFiles

type Path = String
type FileName = String
type Code = String
type Fragment = (FileName, SourceTm)

-- A function to extract the file name from the file path.
--
-- === Example:
-- >>> getNameFromPath "examples/Source/Anonymous.ep"
-- Right "Anonymous"
getNameFromPath ::
    Path ->
    FileName
getNameFromPath path = takeBaseName $ takeFileName path

-- `getImplementationAST` is a function that parses, expands type aliases, transforms AST
-- into a locally nameless representation and desugars the AST into source level AST.
--
-- === Example:
-- >>> getImplementationAST "val x = 1"
-- Right (TmRec "x" (TmLit 1))
getImplementationAST ::
    -- | Implementation code
    Code ->
    -- | SourceAST or Interpreter Error with message
    Either InterpreterError SourceTm
getImplementationAST code =
    do
        surfaceAST <- parseCode code
        surfaceASTExpanded <- typeAliasExpansion surfaceAST
        surfacelocallyNameLessAST <- locallyNameless surfaceASTExpanded
        desugarSource surfacelocallyNameLessAST

-- A function to load an implementation file.
--
-- It simply reads the implementation file and returns the AST with its name extracted from path.
--
-- === Example:
-- >>> readImplementation "examples/Source/Anonymous.ep"
readImplementation ::
    -- | Path for implementation file
    Path ->
    -- | Either Interpreter Failed Error or Fragment
    IO (Either InterpreterError Fragment)
readImplementation filePath = do
    result <- try (readFile filePath) :: IO (Either IOException String)
    case result of
        Right code ->
            case getImplementationAST code of
                Right ast -> return $ Right (getNameFromPath filePath, ast)
                Left err -> return $ Left err
        Left ioException -> return $ Left $ InterpreterFailed ("I/O error (" ++ filePath ++ "):\n" ++ show ioException)

test :: IO ()
test = do
    putStrLn $ "examples/Source/Anonymous.ep  -> " ++ getNameFromPath "examples/Source/Anonymous.ep"
    putStrLn $ "examples/Source/Anonymous     -> " ++ getNameFromPath "examples/Source/Anonymous"
    putStrLn $ "Anonymous                     -> " ++ getNameFromPath "Anonymous"
