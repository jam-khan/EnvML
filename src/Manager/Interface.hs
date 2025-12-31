{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module EnvML.Manager.Interface where

import Control.Exception ()
import Control.Monad ()
import Data.Either (rights)
import Data.List
import qualified Data.Map.Strict as M
import Data.Maybe (mapMaybe)
import EnvML.Manager.Manage
import EnvML.Manager.Sort (Graph, getDependencyOrder, getNodes)
import EnvML.Parser.Interface.ParseInterface (parseInterface)
import EnvML.Desugar ()
import EnvML.Errors
import EnvML.TypeExpansion ()
import Syntax
import EnvML.Utils (readFileSafe)
import System.Directory ()
import System.FilePath ()
import System.IO ()

-- `parseInterfaceFile` takes one file content and parses
--
-- Returns either separate compilation error or the result
parseIntfFile ::
    (FilePath, String) ->
    Either SeparateCompilationError (FilePath, ParseIntfData)
parseIntfFile (path, contents) =
    case parseInterface contents of
        Just res -> Right (path, res) -- Preserve path in success case
        Nothing -> Left $ SepCompError ("Parse failed: " ++ path)

-- `parseInterfaceFiles` takes file contents and parses
-- each files and returns a list of parsed data.
--
-- returns the parsed data
parseInterfaceFiles ::
    [(FilePath, String)] ->
    Either SeparateCompilationError [(FilePath, ParseIntfData)]
parseInterfaceFiles = traverse parseIntfFile

-- `readInterfaceFiles` basically takes filepaths of multiple interface files
-- and reads each with some basic checks on files.
--
-- returns the content of the files.
readInterfaceFiles ::
    [FilePath] ->
    IO [(FilePath, String)]
readInterfaceFiles files = do
    case partition (".epi" `isSuffixOf`) files of
        (validFiles, []) -> do
            contents <- mapM readFileSafe validFiles
            return $ zip validFiles (rights contents)
        (_, invalidFiles) ->
            fail $ "Invalid extensions in: " ++ show invalidFiles

-- `verifyFileNames` is a utility function that ensures that
-- top-level interface name matches the file name
--
-- Returns Error or Nothing
verifyFileNames :: [(FilePath, ParseIntfData)] -> Maybe SeparateCompilationError
verifyFileNames parsedFiles =
    let check (path, (name, _, _, _)) =
            if name == getFileBaseName path
                then Nothing
                else
                    Just $
                        SepCompError $
                            "Interface name '" ++ name ++ "' doesn't match filename '" ++ getFileBaseName path ++ "'"
     in case mapMaybe check parsedFiles of
            [] -> Nothing
            (err : _) -> Just err -- Return first error found

{- | `buildDependencyGraph` converts the parsed interface data
into a dependencyGraph

Convert parsed interfaces into a dependency graph
-}
buildDependencyGraph :: [ParseIntfData] -> Graph
buildDependencyGraph interfaces =
    M.fromList $
        map
            ( \(name, _, requirements, _) ->
                (name, extractDependencies requirements)
            )
            interfaces
  where
    -- Extract all dependencies from requirements
    extractDependencies :: Requirements -> [Name]
    extractDependencies reqs =
        [dep | Req _ dep <- reqs] -- Only take Req constructs, ignore Params

{- | `sortByDependencyOrder` simply returns the topological
 sort of the parsed interfaces.

Returns list of topologically sorted interface lists
-}
sortByDependencyOrder :: [ParseIntfData] -> [Name] -> [ParseIntfData]
sortByDependencyOrder interfaces order =
    let
        interfaceMap = M.fromList [(name, intf) | intf@(name, _, _, _) <- interfaces]
     in
        mapMaybe (`M.lookup` interfaceMap) order

{- | `sortInterfacesTopologically` creates a dependency graph
performs topological sorting and detects cycles, if any.

Returns the ParsedIntfData in the topological sort order
-}
sortInterfacesTopologically :: [ParseIntfData] -> Either SeparateCompilationError [ParseIntfData]
sortInterfacesTopologically interfaces =
    let
        graph = buildDependencyGraph interfaces
        interfaceNames = map (\(name, _, _, _) -> name) interfaces
        allNodes = getNodes graph
        missingDeps = filter (`notElem` interfaceNames) allNodes
     in
        if not (null missingDeps)
            then Left $ SepCompError $ "Missing interface dependencies: " ++ show missingDeps
            else case getDependencyOrder graph of
                Right order ->
                    Right (sortByDependencyOrder interfaces order)
                Left _ ->
                    Left $ SepCompError "Cyclic dependencies detected between interfaces"

{- | `interfaceStmtToSurfaceTyp` converts an interface statement
 into surface type
-}
interfaceStmtToSurfaceTyp ::
    InterfaceStmt ->
    Either SeparateCompilationError SurfaceTyp
interfaceStmtToSurfaceTyp _ = Left $ SepCompError "Not implemented"

{- | `substTyAliasInTyp` is an utility function that
takes the alias (string + typ) as input along with surface typ
and then, substitutes any type alias that matches the string label.

=== Example:
>>> substTyAliasInTyp "X" STInt (STAnd STUnit (STIden "X"))
Right (STAnd STUnit STInt)
-}
substTyAliasInTyp ::
    String ->
    SurfaceTyp ->
    SurfaceTyp ->
    Either SeparateCompilationError SurfaceTyp
substTyAliasInTyp _ _ STUnit = Right STUnit
substTyAliasInTyp _ _ STInt = Right STInt
substTyAliasInTyp _ _ STBool = Right STBool
substTyAliasInTyp _ _ STString = Right STString
substTyAliasInTyp l ty (STAnd ty1 ty2) =
    STAnd <$> substTyAliasInTyp l ty ty1 <*> substTyAliasInTyp l ty ty2
substTyAliasInTyp l ty (STArrow tyA tyB) =
    STArrow <$> substTyAliasInTyp l ty tyA <*> substTyAliasInTyp l ty tyB
substTyAliasInTyp l ty (STRecord l' ty') =
    STRecord l' <$> substTyAliasInTyp l ty ty'
substTyAliasInTyp l ty (STUnion ty1 ty2) =
    STUnion <$> substTyAliasInTyp l ty ty1 <*> substTyAliasInTyp l ty ty2
substTyAliasInTyp l ty (STList ty') =
    STList <$> substTyAliasInTyp l ty ty'
substTyAliasInTyp l ty (STSig tyA tyB) =
    STSig <$> substTyAliasInTyp l ty tyA <*> substTyAliasInTyp l ty tyB
substTyAliasInTyp l ty (STIden l') =
    if l == l'
        then Right ty
        else Right $ STIden l'

substTyAliasIntf ::
    String ->
    SurfaceTyp ->
    Interface ->
    Either SeparateCompilationError Interface
substTyAliasIntf _ _ _ = Left $ SepCompError "Not implemented yet."

{- | `interfaceToSourceTy` takes the Interface Type and proceses
the type aliases, and then, converts the Interface to SourceTyp
-}
interfaceToSurfaceTyp ::
    Interface ->
    Either SeparateCompilationError SourceTyp
interfaceToSurfaceTyp _ = Left $ SepCompError "Not implemented yet."

expandRequirements ::
    [SourceHeader] ->
    Requirements ->
    Either SeparateCompilationError SourceRequirements
expandRequirements _ [] = Right []
expandRequirements _ _ = Left $ SepCompError "Not Implemented yet."

{- | `intfToHeader` is a utility function that takes
an expanded parsed interface and converts into source level header.

=== Example:
-}
parseIntfToHeader ::
    [SourceHeader] ->
    ParseIntfData ->
    Either SeparateCompilationError SourceHeader
parseIntfToHeader headers (name, auth, reqs, intf) =
    TmInterface name auth <$> expandRequirements headers reqs <*> interfaceToSurfaceTyp intf

{- | `processInterfaceFiles` loads the interface files from
the project, parses and returns in topologically sorted
order based on the requirements of the interfaces

=== Example:
>>> processInterfaceFiles "ADT"
Right [("TyAliases",Pure,[],[IAliasTyp "newInt" STInt,Binding "hello" (STArrow (STIden "newInt") (STIden "newInt")),IType (STIden "newInt")]),("Variants",Resource,[],[Binding "res" STString])]
-}
processInterfaceFiles ::
    ProjectName ->
    IO (Either SeparateCompilationError [ParseIntfData])
processInterfaceFiles projname = do
    -- Step 1: Read interface files
    (interfaceFiles, _) <- getInterfaceAndImplFiles projname
    if null interfaceFiles
        then return $ Right []
        else do
            contentsWithPaths <- readInterfaceFiles interfaceFiles
            let processingResult = do
                    parseWithPaths <- parseInterfaceFiles contentsWithPaths
                    case verifyFileNames parseWithPaths of
                        Nothing -> return () -- check this!! maybe
                        Just err -> Left err
                    let intfDataOnly = map snd parseWithPaths
                    sortInterfacesTopologically intfDataOnly
            return processingResult

-- Need to do:
-- Convert and expand the headers from left to right
-- translating to the source level
-- Clean up and test
-- Repeat the same for implementation files
-- Once completed, then work on source to core translation
-- Test imports and required (A lot)
-- Then, add lists and test and finish
-- Document the project and write thesis/report
