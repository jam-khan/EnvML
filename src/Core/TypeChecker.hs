{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use >=>" #-}

module Core.TypeChecker where
import Syntax
    ( BinaryOp(Logic, Arith, Comp),
      CoreTm(..),
      CoreTyp(..),
      UnaryOp(Not) )

newtype TypeError = TypeError String 
    deriving (Eq, Show)

lookupt :: CoreTyp -> Integer -> Maybe CoreTyp
lookupt (TyCAnd _ tB) 0 = Just tB
lookupt (TyCAnd tA _) n = lookupt tA (n - 1)
lookupt _ _ = Nothing

isLabel :: String -> CoreTyp -> Bool
isLabel l (TyCRecord label _) = l == label
isLabel l (TyCAnd tA tB) = isLabel l tA || isLabel l tB
isLabel _ _ = False

containment :: CoreTyp -> CoreTyp -> Bool
containment (TyCRecord l tA) (TyCRecord label typ) =
    l == label && tA == typ
containment (TyCRecord l tA) (TyCAnd tB tC) =
    (containment (TyCRecord l tA) tB && not (isLabel l tC))
        || (containment (TyCRecord l tA) tC && not (isLabel l tB))
containment _ _ = False

rlookupt :: CoreTyp -> String -> Maybe CoreTyp
rlookupt (TyCRecord l t) label
    | l == label = Just t
rlookupt (TyCAnd tA tB) label =
    case rlookupt tB label of
        Just t -> Just t
        Nothing -> rlookupt tA label
rlookupt _ _ = Nothing

infer :: CoreTyp 
    -> CoreTm 
    -> Either TypeError CoreTyp
infer ctx Ctx           = pure ctx
infer _ Unit            = pure TyCUnit
infer _ (Lit _)         = pure TyCInt
infer _ (EBool _)       = pure TyCBool
infer _ (EString _)     = pure TyCString
infer ctx (Lam tA e)    = do
    tB <- infer (TyCAnd ctx tA) e
    return (TyCArrow tA tB)
infer ctx (Proj e n)    = do
    tB <- infer ctx e
    case lookupt tB n of
        Just t -> Right t
        Nothing ->
            Left $ TypeError $
            "Projection " ++ show n++ " failed on type " ++ show tB ++ " ctx: " ++ show ctx
infer ctx (Clos e1 (Lam tA e2)) = do
    ctx1    <- infer ctx e1
    tB      <- infer (TyCAnd ctx1 tA) e2
    return $ TyCArrow tA tB
infer ctx (Rec l e)             = 
    infer ctx e >>= \tA -> Right (TyCRecord l tA)
infer ctx (RProj e l) = do
    tB <- infer ctx e
    case rlookupt tB l of
        Just tA ->
            if containment (TyCRecord l tA) tB
                then Right tA
                else Left $ TypeError "Record projection failed due to containment"
        Nothing -> Left $ TypeError $ "Field " ++ show l ++ " not found in type " ++ show tB
infer ctx (Box e1 e2) = infer ctx e1 >>= \ctx1 -> infer ctx1 e2
infer ctx (Mrg e1 e2) = infer ctx e1 >>= \tA -> infer (TyCAnd ctx tA) e2 >>= \tB -> Right (TyCAnd tA tB)
infer ctx (App e1 e2) = do
    ty1 <- infer ctx e1
    case ty1 of
        TyCArrow tA tB ->
            if check ctx e2 tA
                then Right tB
                else Left $ TypeError ("Type mismatch in application: Context:" ++ show ctx)
        _ ->    
            Left $ TypeError ("Expected a function type in application Function Type: " ++ show ty1 ++ " Function: " ++ show e1)
infer ctx (If cond e1 e2) =
    if check ctx cond TyCBool
        then do
            t1 <- infer ctx e1
            t2 <- infer ctx e2
            if t1 == t2
                then Right t1
                else Left $ TypeError "Branches of if must have the same type"
        else Left $ TypeError "Condition must be of type Bool"
infer ctx (BinOp (Arith _) e1 e2)   = do
    t1 <- infer ctx e1
    t2 <- infer ctx e2
    if t1 == TyCInt && check ctx e2 TyCInt
        then Right TyCInt
        else Left $ TypeError ("Type mismatch in arithmetic operation " ++ show t1 ++ " " ++ show t2)
infer ctx (BinOp (Comp _) e1 e2)    = do
    t1 <- infer ctx e1
    if check ctx e2 t1
    then Right TyCBool
    else Left $ TypeError "Type mismatch in comparison operation. Expected an integer, boolean, or string for comparison"
infer ctx (BinOp (Logic _) e1 e2)   = do
    t1 <- infer ctx e1
    if t1 == TyCBool && check ctx e2 TyCBool
        then Right TyCBool
        else Left $ TypeError "Type mismatch in logical operation"
infer ctx (UnOp Not e) =
    if check ctx e TyCBool
        then Right TyCBool
        else Left $ TypeError "Expected boolean for negation"
infer _ _ = Left $ TypeError "Unknown expression"

check :: CoreTyp -> CoreTm -> CoreTyp -> Bool
check ctx e tA = case infer ctx e of
    Right tB -> tA == tB
    _ -> False
