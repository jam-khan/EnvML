module Utils where

import Control.Exception (IOException, try)
import Syntax
import System.Directory (doesFileExist)

arithOp :: ArithOp -> Integer -> Integer -> Maybe Integer
arithOp Add v1 v2 = Just (v1 + v2)
arithOp Sub v1 v2 = Just (v1 - v2)
arithOp Mul v1 v2 = Just (v1 * v2)
arithOp Div v1 v2 =
    if v2 == 0
        then Nothing
        else Just (v1 `Prelude.div` v2)
arithOp Mod v1 v2 =
    if v2 == 0
        then Nothing
        else Just (v1 `Prelude.mod` v2)

compareOp :: CompOp -> Value -> Value -> Bool
compareOp op (VInt v1) (VInt v2) =
    compareWith op v1 v2
compareOp op (VBool b1) (VBool b2) =
    compareWith op b1 b2
compareOp op (VString s1) (VString s2) =
    compareWith op s1 s2
compareOp _ _ _ = False

compareWith :: (Ord a) => CompOp -> a -> a -> Bool
compareWith Eql x y = x == y
compareWith Neq x y = x /= y
compareWith Lt x y = x < y
compareWith Le x y = x <= y
compareWith Gt x y = x > y
compareWith Ge x y = x >= y

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
