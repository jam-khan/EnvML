module ENVCAP.Utils where

import Control.Exception (IOException, try)
import ENVCAP.Syntax
import System.Directory (doesFileExist)


readFileSafe :: FilePath -> IO (Either String String)
readFileSafe path = do
    exists <- doesFileExist path
    if exists
        then do
            content <- try (readFile path) :: IO (Either IOException String)
            case content of
                Left err -> return $ Left ("Error reading " ++ path ++ ": " ++ show err)
                Right c -> return $ Right c
        else return $ Left ("File not found: " ++ path)
