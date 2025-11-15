module ENVCAP.Core.Evaluator where
import ENVCAP.Syntax
import Control.Monad (guard)

eval :: Value -> CoreTm -> Maybe Value
eval env Ctx            = pure env
eval _ Unit             = pure VUnit
eval _ (Lit n)          = pure $ VInt n
eval _ (EBool b)        = pure $ VBool b
eval _ (EString s)      = pure $ VString s
eval env (Lam t e)      = pure $ VClos env (Lam t e)
eval env (Proj e n)     = do  
    v <- eval env e
    lookupv v n
eval env (Clos e1 e2)   = do
    v1 <- eval env e1
    return $ VClos v1 e2
eval env (Rec s e)      = do
    v <- eval env e
    return $ VRcd s v
eval env (RProj e s)    = do
    v1 <- eval env e
    rlookupv v1 s
eval env (App e1 e2)    = do
    (VClos v lambda) <- eval env e1
    v2               <- eval env e2
    apply v lambda v2
    where
        apply :: Value -> CoreTm -> Value -> Maybe Value
        apply env' (Lam _ e) arg =
            eval (VMrg env' arg) e
        apply env' fix@(Fix _ (Lam _ e')) arg =
            eval (VMrg (VMrg env' (VClos env' fix)) arg) e'
        apply _ _ _ = Nothing
eval env (Mrg e1 e2)    = do
    v1 <- eval env e1 
    v2 <- eval (VMrg env v1) e2
    return $ VMrg v1 v2
eval env (Box e1 e2)    = do
    v1 <- eval env e1
    eval v1 e2
eval env (Fix ty e)     = pure $ VClos env (Fix ty e)
eval env (Tag tm ty)    = do
    v <- eval env tm
    return $ VTag v ty
eval env (Case tm cases) = do
    (VTag (VRcd l v) _) <- eval env tm
    tm' <- getCase l cases
    eval (mergeEnvTuple env v) tm'
    where
        mergeEnvTuple env' (VMrg v1 v2) = VMrg (mergeEnvTuple env' v1) v2
        mergeEnvTuple env' v' = VMrg env' v'
eval env (If cond e1 e2) = do
    VBool b <- eval env cond
    eval env (if b then e1 else e2)
eval env (BinOp (Arith op) e1 e2) = do
    (VInt v1) <- eval env e1
    (VInt v2) <- eval env e2
    VInt <$> arithOp op v1 v2   
eval env (BinOp (Comp op) e1 e2)    = do
    v1 <- eval env e1
    v2 <- eval env e2
    pure $ VBool (compareOp op v1 v2)
eval env (BinOp (Logic op) e1 e2)   = do
    (VBool b1) <- eval env e1
    (VBool b2) <- eval env e2
    pure $ VBool (solve op b1 b2)
    where
        solve And v1 v2 = v1 && v2
        solve Or v1 v2  = v1 || v2 
eval env (UnOp Not e1)  = do
    (VBool b ) <- eval env e1
    return $ VBool (not b)
eval env (Cons e1 e2)   = do
    v1 <- eval env e1
    v2 <- eval env e2
    return $ VCons v1 v2
eval env (LCase e1 e2 e3) = do
    v1 <- eval env e1
    solveLCase v1
    where
        solveLCase (VNil _ty)    = eval env e2
        solveLCase (VCons v1 v2) = eval (VMrg (VMrg env v1) v2) e3
        solveLCase _             = Nothing
eval _ (Nil ty)      = pure $ VNil ty
eval _ (CLam _ _)    = error "NOT SUPPORTED CLam"
eval env (Anno tm _) = eval env tm

lookupv :: Value -> Integer -> Maybe Value
lookupv (VMrg _ v2) 0 = Just v2
lookupv (VMrg v1 _) n = lookupv v1 (n - 1)
lookupv _ _ = Nothing

rlookupv :: Value -> String -> Maybe Value
rlookupv (VRcd l v) label
    | l == label = Just v
rlookupv (VMrg v1 v2) label =
    case (rlookupv v1 label, rlookupv v2 label) of
        (Just vL, Nothing) -> Just vL
        (Nothing, Just vR) -> Just vR
        (_, _) -> Nothing
rlookupv _ _ = Nothing

getCase :: String -> [(Pattern, CoreTm)] -> Maybe CoreTm
getCase _ [] = Nothing
getCase l (((l', _), tm) : xs) =
    if l == l' then Just tm else getCase l xs

arithOp :: ArithOp -> Integer -> Integer -> Maybe Integer
arithOp Add v1 v2 = pure $ v1 + v2
arithOp Sub v1 v2 = pure $ v1 - v2
arithOp Mul v1 v2 = pure $ v1 * v2
arithOp Div v1 v2 = do
    guard (v2 /= 0) 
    return $ v1 `div` v2
arithOp Mod v1 v2 = do
    guard (v2 /= 0) 
    return $ v1 `mod` v2

compareOp :: CompOp -> Value -> Value -> Bool
compareOp Eql v1 v2     = v1 == v2
    -- compareWith op v1 v2
compareOp op (VBool b1) (VBool b2) =
    compareWith op b1 b2
compareOp op (VString s1) (VString s2) =
    compareWith op s1 s2
compareOp _ _ _ = False

compareWith :: (Ord a) => CompOp -> a -> a -> Bool
compareWith Eql x y     = x == y
compareWith Neq x y     = x /= y
compareWith Lt x y      = x < y
compareWith Le x y      = x <= y
compareWith Gt x y      = x > y
compareWith Ge x y      = x >= y
