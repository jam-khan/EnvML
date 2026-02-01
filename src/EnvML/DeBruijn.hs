{-# LANGUAGE LambdaCase #-}
module EnvML.DeBruijn where

import Data.List (elemIndex)
import qualified EnvML.Parser.AST as S  -- Source (Named, Desugared)
import qualified EnvML.Syntax as T      -- Target (Nameless)

type Ctx = [S.Name] -- Names in scope

-- lookupVar :: S.Name -> Ctx -> Int
-- lookupVar x ctx =
--   case elemIndex x ctx of
--     Just i -> i
--     Nothing -> error $ "Unbound variable: " ++ x

-- toDeBruijn :: S.Exp -> T.Exp
-- toDeBruijn = convExp []

-- typToDeBruijn :: S.Typ -> T.Typ
-- typToDeBruijn = convTyp []

-- modToDeBruijn :: S.Module -> T.Module
-- modToDeBruijn = convModule []

-- -- Convert expressionns from named to nameless
-- convExp :: Ctx -> S.Exp -> T.Exp
-- convExp ctx = \case
--   S.Lit l -> T.Lit (convLit l)
--   S.Var x -> T.Var (lookupVar x ctx)

--   -- Single-arg lambda
--   S.Lam [("x", S.TmArg)] body ->
--     T.Lam (convExp ("x" : ctx) body)

--   S.Lam [("x", S.TmArgType _)] body ->
--     T.Lam (convExp ("x" : ctx) body)

--   S.Lam [(s, S.TyArg)] body ->
--     T.TLam (convExp (x : ctx) body)

--   S.Lam _ _ ->
--     error "Multi-arg lambda should be desugared already!"
  
-- --   S.TLam _ _ ->

-- -- Expression conversion to De-Bruijn
-- -- convExp :: Ctx -> S.Exp -> T.Exp
-- -- convExp ctx e = case e of
-- --   S.Lit l -> T.Lit (convLit l)