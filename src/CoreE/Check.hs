{-# HLINT ignore "Use newtype instead of data" #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use >=>" #-}
module CoreE.Check where
import Syntax

data TypeError = TypeError String deriving (Eq, Show)

-- `lookupt` performs an index lookup on the typing context.
--
-- === Example:
-- >>> lookupt (TyCAnd TyCInt TyCInt) 0
-- Just TyCInt
lookupt :: CoreTyp -> Integer -> Maybe CoreTyp
lookupt (TyCAnd _ tB) 0 = Just tB
lookupt (TyCAnd tA _) n = lookupt tA (n - 1)
lookupt _ _ = Nothing

-- `isLabel` checks if the label exists in a record type.
--
-- === Example:
-- >>> isLabel "X" (TyCRecord "A" TyCInt)
-- False
isLabel :: String -> CoreTyp -> Bool
isLabel l (TyCRecord label _) = l == label
isLabel l (TyCAnd tA tB) = isLabel l tA || isLabel l tB
isLabel _ _ = False

-- `containment` checks if the record type is contained in the context.
-- Essentially, no duplicates.
--
-- === Example:
-- >>> containment (TyCRecord "x" TyCInt) (TyCAnd (TyCRecord "x" TyCInt) TyCUnit)
-- True
containment :: CoreTyp -> CoreTyp -> Bool
containment (TyCRecord l tA) (TyCRecord label typ) =
    l == label && tA == typ
containment (TyCRecord l tA) (TyCAnd tB tC) =
    (containment (TyCRecord l tA) tB && not (isLabel l tC))
        || (containment (TyCRecord l tA) tC && not (isLabel l tB))
containment _ _ = False

-- `containmentUnion` checks if the record type is contained in the union type.
-- Essentially, no duplicate constructors in a variant.
--
-- === Example:
-- >>> containmentUnion (TyCRecord "x" TyCInt) (TyCUnion (TyCRecord "x" TyCInt) TyCUnit)
-- True
containmentUnion :: CoreTyp -> CoreTyp -> Bool
containmentUnion (TyCRecord l tA) (TyCRecord label typ) =
    l == label && tA == typ
containmentUnion (TyCRecord l tA) (TyCUnion tB tC) =
    (containmentUnion (TyCRecord l tA) tB && not (isLabel l tC))
        || (containmentUnion (TyCRecord l tA) tC && not (isLabel l tB))
containmentUnion _ _ = False

-- `rlookupt` performs a look on the typing context by record
--
-- === Example:
-- >>> rlookupt (TyCRecord "X" TyCInt) "X"
-- Just TyCInt
rlookupt :: CoreTyp -> String -> Maybe CoreTyp
rlookupt (TyCRecord l t) label
    | l == label = Just t
rlookupt (TyCAnd tA tB) label =
    case rlookupt tB label of
        Just t -> Just t
        Nothing -> rlookupt tA label
rlookupt _ _ = Nothing

{- | `countLabels` is a utility function that ensures well-formedness of the variant type
  and returns the count of labels present in the variant type.

=== Example:
>>> countLabels (TyCRecord "x" TyInt)
Right 1
-}
countLabels :: CoreTyp -> Either TypeError Int
countLabels (TyCRecord _ _) = Right 1
countLabels (TyCUnion tA tB) =
    do
        left <- countLabels tA
        right <- countLabels tB
        return $ left + right
countLabels _ =
    Left $ TypeError "Variant Type must be restricted to only records with unions"

{- | `countTypesInConstructor` is a utility function that returns the count of types
inside an intersection type.

=== Example:
>>> countTypesInConstructor (TyCAnd TyCInt TyCInt)
Right 2
-}
countTypesInConstructor :: CoreTyp -> Either TypeError Int
countTypesInConstructor (TyCAnd tA _) =
    countTypesInConstructor tA >>= \left -> return $ left + 1
countTypesInConstructor _ =
    Right 1

{- | `isPatternPresentInVariantTy` is a utility function that ensures each case in a match statement
  is well typed and returns the corresponding type of constructor from the variant type
  via a type label lookup.

=== Example:
>>> isPatternPresentInVariantTy (TyCUnion (TyCRecord "Num" TyCInt) (TyCRecord "Var" TyCString)) ("Var", ["x"])
Right TyCString

>>> isPatternPresentInVariantTy (TyCUnion (TyCRecord "Num" TyCInt) (TyCRecord "Var" TyCString)) ("Var", ["x", "y"])
Left (TypeError "The number of bindings in the case Var do not match the data type constructor")

>>> isPatternPresentInVariantTy (TyCUnion (TyCRecord "Num" TyCUnit) (TyCRecord "Var" TyCString)) ("Num", [])
Right TyCUnit
-}
isPatternPresentInVariantTy :: CoreTyp -> Pattern -> Either TypeError CoreTyp
isPatternPresentInVariantTy variantTy (label, bindings) =
    -- Firstly, a label lookup is performed on the variantTy
    case rlookupVariant variantTy of
        Just ty ->
            -- This gives the type, but we need to ensure containment for uniqueness
            if containmentUnion (TyCRecord label ty) variantTy
                then
                    if (ty == TyCUnit && countBindings == 0)
                        || (countTypesInConstructor ty == Right countBindings)
                        then Right ty
                        else Left $ TypeError ("The number of bindings in the case " ++ label ++ " do not match the data type constructor")
                else Left $ TypeError ("Duplicate constructor found in the variant type: " ++ show variantTy)
        Nothing ->
            Left $ TypeError ("Constructor " ++ label ++ " not present in the variant type: " ++ show variantTy)
  where
    countBindings = length bindings
    rlookupVariant :: CoreTyp -> Maybe CoreTyp
    rlookupVariant (TyCRecord l t)
        | l == label = Just t
    rlookupVariant (TyCUnion tA tB) =
        case rlookupVariant tB of
            Just t -> Just t
            Nothing -> rlookupVariant tA
    rlookupVariant _ = Nothing

{- | `insertIntersectionContext` is a utility function that inserts an intersection type in the context
correct.

=== Example:
>>> insertIntersectionContext (TyCAnd TyCUnit TyCInt) (TyCAnd (TyCAnd TyCString TyCInt) TyCBool)
Right (TyCAnd (TyCAnd (TyCAnd (TyCAnd TyCUnit TyCInt) TyCString) TyCInt) TyCBool)
-}
insertIntersectionContext :: CoreTyp -> CoreTyp -> Either TypeError CoreTyp
insertIntersectionContext ctx (TyCAnd tA tB) =
    insertIntersectionContext ctx tA >>= \left -> return $ TyCAnd left tB
insertIntersectionContext ctx ty =
    Right $ TyCAnd ctx ty

inferCase :: CoreTyp -> CoreTyp -> (Pattern, CoreTm) -> Either TypeError CoreTyp
inferCase ctx variantTy ((label, bindings), tm) =
    isPatternPresentInVariantTy variantTy (label, bindings) >>= \ty' ->
        insertIntersectionContext ctx ty' >>= \ctx' ->
            case infer ctx' tm of
                Right caseTy ->
                    Right caseTy
                Left err -> Left err

checkCases :: CoreTyp -> CoreTyp -> CoreTyp -> [(Pattern, CoreTm)] -> Either TypeError CoreTyp
checkCases _ ty _ [] = Right ty
checkCases ctx ty1 variantTy (x : xs) =
    if checkEach (x : xs)
        then Right ty1
        else
            Left $ TypeError "Types of each case don't match. Elaboration not sound."
  where
    checkEach [] = True
    checkEach (fstcase : rest) =
        case inferCase ctx variantTy fstcase of
            Right ty' -> ty1 == ty' && checkEach rest
            Left _ -> False

inferMatch :: CoreTyp -> CoreTm -> Either TypeError CoreTyp
inferMatch _ (Case _ []) =
    Left $ TypeError "Match statement must have atleast one case. Elaboration is not sound."
inferMatch ctx (Case tm (fstcase : cases)) =
    case infer ctx tm of
        Right variantTy@(TyCUnion _ _) ->
            if countLabels variantTy == Right (length cases + 1) && isUnique (fstcase : cases)
                then
                    inferCase ctx variantTy fstcase >>= \ty1 ->
                        checkCases ctx ty1 variantTy cases
                else Left $ TypeError "Fewer cases present in the match than the constructors in the ADT."
        Right _ -> Left $ TypeError "match can only be called on variant"
        Left err -> Left err
  where
    isUnique ls = case ls of
        ((constructor, _), _) : xs ->
            notFound constructor xs && isUnique xs
        [] -> True
      where
        notFound l ls' = case ls' of
            ((constructor', _), _) : xs ->
                l /= constructor' && notFound l xs
            [] -> True
inferMatch _ _ =
    Left $ TypeError ""

-- `infer` infers the type of the expression.
--
-- === Example:
-- >>> infer TyCUnit (Lit 1)
-- Right TyCInt
infer :: CoreTyp -> CoreTm -> Either TypeError CoreTyp
infer ctx Ctx = Right ctx
infer _ Unit = Right TyCUnit
infer _ (Lit _) = Right TyCInt
infer _ (EBool _) = Right TyCBool
infer _ (EString _) = Right TyCString
infer ctx (Lam tA e) = infer (TyCAnd ctx tA) e >>= \tB -> Right (TyCArrow tA tB)
infer ctx (Proj e n) =
    infer ctx e >>= \tB ->
        case lookupt tB n of
            Just t -> Right t
            Nothing ->
                Left $
                    TypeError $
                        "Projection "
                            ++ show n
                            ++ " failed on type "
                            ++ show tB
                            ++ " ctx: "
                            ++ show ctx
infer ctx (Clos e1 (Lam tA e2)) =
    infer ctx e1 >>= \ctx1 ->
        infer (TyCAnd ctx1 tA) e2 >>= \tB ->
            Right (TyCArrow tA tB)
infer ctx (Rec l e) = infer ctx e >>= \tA -> Right (TyCRecord l tA)
infer ctx (RProj e l) =
    infer ctx e >>= \tB ->
        case rlookupt tB l of
            Just tA ->
                if containment (TyCRecord l tA) tB
                    then Right tA
                    else Left $ TypeError "Record projection failed due to containment"
            Nothing -> Left $ TypeError $ "Field " ++ show l ++ " not found in type " ++ show tB
infer ctx (Box e1 e2) = infer ctx e1 >>= \ctx1 -> infer ctx1 e2
infer ctx (Mrg e1 e2) = infer ctx e1 >>= \tA -> infer (TyCAnd ctx tA) e2 >>= \tB -> Right (TyCAnd tA tB)
infer ctx (App e1 e2) =
    infer ctx e1 >>= \ty1 ->
        case ty1 of
            TyCArrow tA tB ->
                if check ctx e2 tA
                    then Right tB
                    else Left $ TypeError ("Type mismatch in application: Context:" ++ show ctx)
            _ ->
                Left $
                    TypeError
                        ( "Expected a function type in application Function Type: "
                            ++ show ty1
                            ++ " Function: "
                            ++ show e1
                        )
infer ctx (If cond e1 e2) =
    if check ctx cond TyCBool
        then
            infer ctx e1 >>= \t1 ->
                infer ctx e2 >>= \t2 ->
                    if t1 == t2
                        then Right t1
                        else Left $ TypeError "Branches of if must have the same type"
        else Left $ TypeError "Condition must be of type Bool"
infer ctx (Fix tA e) =
    if check (TyCAnd ctx tA) e tA 
        then Right tA
        else Left $ TypeError "Fixpoint type check failed"
infer ctx (Tag tm ty) = case infer ctx tm of
    Right tm'@(TyCRecord _ _) ->
        if containmentUnion tm' ty
            then Right ty
            else Left $ TypeError ("Ambiguous label on ADT. Elaboration FAILED. " ++ show (Tag tm ty))
    Right _ -> Left $ TypeError "Value can't be tagged with ADT"
    Left _ -> Left $ TypeError "Elaboration Failed"
infer ctx (Case tm cases) = inferMatch ctx (Case tm cases)
infer ctx (BinOp (Arith _) e1 e2) =
    infer ctx e1 >>= \t1 ->
        infer ctx e2 >>= \t2 ->
            if t1 == TyCInt && check ctx e2 TyCInt
                then Right TyCInt
                else Left $ TypeError ("Type mismatch in arithmetic operation " ++ show t1 ++ " " ++ show t2)
infer ctx (BinOp (Comp _) e1 e2) =
    infer ctx e1 >>= \t1 ->
        if check ctx e2 t1
            then Right TyCBool
            else
                Left $
                    TypeError "Type mismatch in comparison operation. Expected an integer, boolean, or string for comparison"
infer ctx (BinOp (Logic _) e1 e2) =
    infer ctx e1 >>= \t1 ->
        if t1 == TyCBool && check ctx e2 TyCBool
            then Right TyCBool
            else Left $ TypeError "Type mismatch in logical operation"
infer ctx (UnOp Not e) =
    if check ctx e TyCBool
        then Right TyCBool
        else Left $ TypeError "Expected boolean for negation"
infer ctx (Nil ty) = Right ty
infer ctx (Cons e1 e2) =
    infer ctx e1 >>= \t1 ->
        infer ctx e2 >>= \t2 ->
            if TyCList t1 == t2
                then Right $ TyCList t1
                else Left $ TypeError ("List type check failed: " ++ "Expected type of list " ++ show t1 ++ ", but got " ++ show t2)
infer ctx (LCase e1 e2 e3) = case infer ctx e1 of
    Right (TyCList ty1) ->
        infer ctx e2 >>= \ty2 ->
            infer (TyCAnd (TyCAnd ctx ty1) (TyCList ty1)) e3 >>= \ty3 ->
                if ty2 == ty3
                    then Right $ TyCList ty1
                    else Left $ TypeError "Case branches list pattern match don't have same types."
infer ctx (CLam ty tm) = Left $ TypeError "Linking not resolved properly"
infer ctx (Anno tm ty) =
    if check ctx tm ty
        then Right ty
        else Left $ TypeError "Types and Annotation don't match."
infer _ _ = Left $ TypeError "Unknown expression"

check :: CoreTyp -> CoreTm -> CoreTyp -> Bool
check ctx e tA = case infer ctx e of
    Right tB -> tA == tB
    _ -> False
