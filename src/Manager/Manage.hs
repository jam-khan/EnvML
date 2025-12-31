{-# LANGUAGE DeriveGeneric #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use lefts" #-}

{- |
Module      : EnvML.Manager.Manage
Description : Module is responsible for the management of project, files, and separate compilation etc.
Copyright   : (c) Jam Kabeer Ali Khan, 2025
License     : MIT
Maintainer  : jamkhan@connect.hku.hk
Stability   : experimental

For more details, see the individual function documentation.
-}
module EnvML.Manager.Manage where

import Control.Monad (filterM, forM, forM_)
import Data.Binary (decodeOrFail, encode)
import qualified Data.ByteString.Lazy as BL
import Data.Configurator (Worth (Required), load, require)
import Data.List (isSuffixOf)
import Data.Text (isSuffixOf, pack)
import EnvML.Interpreter (evaluate)
import EnvML.Manager.Implementation (Fragment, readImplementation)
import EnvML.Elaboration (elaborateInfer)
import EnvML.Errors
import Syntax
import System.Directory (createDirectoryIfMissing, doesDirectoryExist, doesFileExist, listDirectory)
import System.Directory.Internal.Prelude
import System.FilePath (takeBaseName, takeFileName, (</>))
import System.IO.Error

type ProjectName = String

{- | `getBaseDir` loads the path from environment variable `EnvML_CODE` in `config.cfg`
and returns the project path.
-}
getBaseDir :: IO String
getBaseDir =
    load [Required "config.cfg"] >>= \config ->
        require config (pack "EnvML_CODE") :: IO String

-- | `createCompiledDir` creates the compiled directory in the project directory.
createCompiledDir ::
    -- | Project Name
    String ->
    IO ()
createCompiledDir projectName =
    do
        baseDir <- getBaseDir
        let compiledDir = baseDir </> projectName </> "compiled"
        exists <- doesDirectoryExist compiledDir
        unless exists $ createDirectoryIfMissing True compiledDir

-- Extracts "Variants" from "/path/to/Variants.epi"
getFileBaseName :: FilePath -> String
getFileBaseName = takeBaseName . takeFileName

{- | `getFileNames` is a utility function that returns the file names
present in a specific directory.
-}
getFileNames ::
    -- | Path of a file/directory
    FilePath ->
    -- | List of file names located in the path
    IO [FilePath]
getFileNames dirPath =
    listDirectory dirPath >>= \contents ->
        filterM (doesFileExist . (dirPath </>)) contents

{- | `getProjectFiles` is a utility function that returns the Files present in
the specified project.

It utilizes the path specified in environment variable `EnvML_CODE`.
-}
getProjectFiles ::
    -- | Name of the project
    ProjectName ->
    -- | List of file names in the project
    IO [FilePath]
getProjectFiles projectName =
    do
        baseDir <- getBaseDir
        filesNames <- getFileNames (baseDir ++ projectName) `catchIOError` handleDirectoryError
        return $ map (\x -> baseDir </> projectName </> x) filesNames

{- | `getInterfaceAndImplFiles` is a utility function that returns the path of
all implementation and interface Files present in the specified project.

It utilizes the path specified in environment variable `EnvML_CODE`.
Reads all the files present and returns list of interface paths and list of impl paths.
-}
getInterfaceAndImplFiles ::
    -- | Name of the project
    ProjectName ->
    -- | (interface files, implementation files)
    IO ([FilePath], [FilePath])
getInterfaceAndImplFiles projName =
    do
        allFiles <- getProjectFiles projName `catchIOError` handleDirectoryError
        return $ foldr categorize ([], []) allFiles
  where
    categorize :: FilePath -> ([FilePath], [FilePath]) -> ([FilePath], [FilePath])
    categorize file (epis, eps)
        | ".epi" `Data.List.isSuffixOf` file = (file : epis, eps)
        | ".ep" `Data.List.isSuffixOf` file = (epis, file : eps)
        | otherwise = (epis, eps)

{- | `loadProjectFiles` loads and parses the implementation files of a project.
It returns a list of successfully parsed fragments and a list of errors.
-}
loadProjectFiles ::
    -- | Files to be loaded
    [FilePath] ->
    IO ([Fragment], [EnvML.Errors.InterpreterError])
loadProjectFiles projectFiles = do
    results <- mapM readImplementation projectFiles
    return $ foldr categorize ([], []) results
  where
    categorize ::
        Either EnvML.Errors.InterpreterError Fragment ->
        ([Fragment], [EnvML.Errors.InterpreterError]) ->
        ([Fragment], [EnvML.Errors.InterpreterError])
    categorize (Left err) (fragments, errors) = (fragments, err : errors)
    categorize (Right fragment) (fragments, errors) = (fragment : fragments, errors)

{- | `elaborateFragments` is a utility function that elaborates fragments to core expressions.
Each fragment becomes a record at the source level ~~~~> core level

=== Example:
>>> elaborateFragments [("X", (TmLit 1))]
Right (Rec "X" (Lit 1))
-}
elaborateFragments ::
    [Fragment] ->
    Either EnvML.Errors.SourceTypeError [(String, CoreTm)]
elaborateFragments [] = Right []
elaborateFragments fragments = elaborateMultiple fragments
  where
    elaborateMultiple :: [Fragment] -> Either EnvML.Errors.SourceTypeError [(String, CoreTm)]
    elaborateMultiple [] = Right []
    elaborateMultiple ((file, term) : xs) =
        case elaborateInfer TySUnit term of
            Right (_, term') ->
                elaborateMultiple xs
                    >>= \xs' -> Right ((file, term') : xs')
            Left err -> Left err

{- | `saveCoreTmToFile` saves a core expression to a .epc file.
core expression is converted into binary file and saved in a `.epc` file.
-}
saveCoreTmFile ::
    ProjectName ->
    (String, CoreTm) ->
    IO (Either String ())
saveCoreTmFile projectName (fileName, coreTm) =
    do
        baseDir <- getBaseDir
        let filePath = baseDir </> projectName </> "compiled" </> (fileName ++ ".epc")
        result <- try (BL.writeFile filePath (encode coreTm)) :: IO (Either SomeException ())
        case result of
            Left exception -> return $ Left (show exception)
            Right _ -> return $ Right ()

-- | `loadCoreTmFile` loads a CoreTm expression from a .epc file.
loadCoreTmFile ::
    ProjectName ->
    String ->
    IO (Either String CoreTm)
loadCoreTmFile projectName fileName =
    do
        baseDir <- getBaseDir
        let filePath = baseDir </> projectName </> "compiled" </> (fileName ++ ".epc")
        fileExists <- doesFileExist filePath
        if not fileExists
            then return $ Left ("File not found: " ++ filePath)
            else do
                result <- try (BL.readFile filePath) :: IO (Either SomeException BL.ByteString)
                case result of
                    Left exception -> return $ Left (show exception)
                    Right byteString ->
                        case decodeOrFail byteString of
                            Left (_, _, errMsg) -> return $ Left ("Decoding error: " ++ errMsg)
                            Right (_, _, coreTm) -> return $ Right coreTm

{- | `compiledProject` creates a compiled directory in the project
if it doesn't exists and then, loads the project files, elaborates to
core expression and generates `.epc` files in the `compiled` directory.
-}
compileProject ::
    ProjectName ->
    IO (Either [String] ())
compileProject projectName = do
    createCompiledDir projectName
    projectFiles <- getProjectFiles projectName
    (fragments, _) <- loadProjectFiles projectFiles

    case elaborateFragments fragments of
        Left typeError -> return $ Left [show typeError]
        Right coreTms -> do
            results <- mapM (saveCoreTmFile projectName) coreTms
            let saveErrors = [errMsg | Left errMsg <- results]
            if null saveErrors
                then return $ Right ()
                else return $ Left saveErrors

{- | `executeProject` loads the `.epc` files from the compiled directory in the
project if `/compiled` dir exists, and then, executes.
-}
executeProject ::
    ProjectName ->
    IO ()
executeProject projectName = do
    baseDir <- getBaseDir
    let projectDir = baseDir </> projectName
    let compiledDir = projectDir </> "compiled"

    fileNames <- getFileNames projectDir

    let epcFileNames = map (\fn -> takeBaseName fn ++ ".epc") fileNames
    epcFileExists <- forM epcFileNames $ \epcFileName ->
        doesFileExist (compiledDir </> epcFileName)

    unless (and epcFileExists) $ do
        hPutStrLn stderr "Not all .epc files found in the compiled directory."
        return ()

    forM_ epcFileNames $ \epcFileName -> do
        let baseFileName = takeBaseName epcFileName
        putStrLn $ "-----running " ++ baseFileName ++ ".epc------"
        coreTmResult <- loadCoreTmFile projectName baseFileName
        case coreTmResult of
            Left loadError -> hPutStrLn stderr $ "Error loading " ++ epcFileName ++ ": " ++ loadError
            Right coreTm -> do
                case EnvML.Interpreter.evaluate coreTm of
                    Left evalError -> hPutStrLn stderr $ "Error evaluating " ++ epcFileName ++ ": " ++ show evalError
                    Right value -> print value

{- | `handleDirectoryError` is an error handling function
for handling the case when the project directory is not found
in the `getProjectFiles` function.
-}
handleDirectoryError ::
    -- | IOError raised
    IOError ->
    -- | List of file names (returns [])
    IO [FilePath]
handleDirectoryError e
    | isDoesNotExistError e = return []
    | otherwise = return []
