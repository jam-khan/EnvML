{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use >=>" #-}
module Source.Elaboration where

import Source.Errors
import Syntax

elaborateTyp :: SourceTyp -> CoreTyp
elaborateTyp TySUnit = TyCUnit
elaborateTyp TySInt = TyCInt
elaborateTyp TySBool = TyCBool
elaborateTyp TySString = TyCString
elaborateTyp (TySRecord label ty) = TyCRecord label (elaborateTyp ty)
elaborateTyp (TySAnd ty1 ty2) = TyCAnd (elaborateTyp ty1) (elaborateTyp ty2)
elaborateTyp (TySUnion ty1 ty2) = TyCUnion (elaborateTyp ty1) (elaborateTyp ty2)
elaborateTyp (TySArrow ty1 ty2) = TyCArrow (elaborateTyp ty1) (elaborateTyp ty2)
elaborateTyp (TySSig tA tB) = TyCArrow (elaborateTyp tA) (elaborateTyp tB)

type Elab = (SourceTyp, CoreTm)
type Context = SourceTyp
type Message = String
type Suggestion = String

{- | `generateError` is a utility function used to construct error message for
type checking error at source level during elaboration.
-}
generateError :: Context -> SourceTm -> Message -> Suggestion -> SourceTypeError
generateError ctx tm msg sugg =
    STypeError
        ( "Typechecking failed at Source level\n\n"
            ++ "Context: "
            ++ show ctx
            ++ "\n"
            ++ "Expression: "
            ++ show tm
            ++ "\n"
            ++ msg
            ++ "\n"
            ++ sugg
            ++ "\n"
        )

-- Lookup based on indexing
lookupt :: SourceTyp -> Integer -> Maybe SourceTyp
lookupt (TySAnd _ tB) 0 = Just tB
lookupt (TySAnd tA _) n = lookupt tA (n - 1)
lookupt _ _ = Nothing

-- checks if l is a label in the typing context
isLabel :: String -> SourceTyp -> Bool
isLabel l (TySRecord label _) = l == label
isLabel l (TySAnd tA tB) = isLabel l tA || isLabel l tB
isLabel _ _ = False

-- containment
containment :: SourceTyp -> SourceTyp -> Bool
containment (TySRecord l tA) (TySRecord label typ) =
    l == label && tA == typ
containment (TySRecord l tA) (TySAnd tB tC) =
    (containment (TySRecord l tA) tB && not (isLabel l tC))
        || (containment (TySRecord l tA) tC && not (isLabel l tB))
containment _ _ = False

containmentUnion :: SourceTyp -> SourceTyp -> Bool
containmentUnion (TySRecord l tA) (TySRecord label typ) =
    l == label && tA == typ
containmentUnion (TySRecord l tA) (TySUnion tB tC) =
    (containmentUnion (TySRecord l tA) tB && not (isLabel l tC))
        || (containmentUnion (TySRecord l tA) tC && not (isLabel l tB))
containmentUnion _ _ = False

{- | `rlookupt` is the record lookup function in the type-directed elaboration rules.
It is used to perform label projection on the context.

=== Example:
>>> rlookupt (TySAnd (TySRecord "Num" TySInt) (TySRecord "Var" TySString)) "Num"
Just TySInt

>>> rlookupt (TySAnd (TySRecord "Val" TySBool) TySInt) "Val"
Just TySBool
-}
rlookupt :: SourceTyp -> String -> Maybe SourceTyp
rlookupt (TySRecord l t) label
    | l == label = Just t
rlookupt (TySAnd tA tB) label =
    case rlookupt tB label of
        Just t -> Just t
        Nothing -> rlookupt tA label
rlookupt _ _ = Nothing

{- | `countLabels` is a utility function that ensures well-formedness of the variant type
  and returns the count of labels present in the variant type.

=== Example:
>>> countLabels (TySRecord "x" TyInt)
Right 1
-}
countLabels :: SourceTyp -> Either SourceTypeError Int
countLabels (TySRecord _ _) = Right 1
countLabels (TySUnion tA tB) =
    do
        left <- countLabels tA
        right <- countLabels tB
        return $ left + right
countLabels _ =
    Left $ STypeError "Variant Type must be restricted to only records with unions"

{- | `countTypesInConstructor` is a utility function that returns the count of types
inside an intersection type.

=== Example:
>>> countTypesInConstructor (TySAnd TySInt TySInt)
Right 2

>>> countTypesInConstructor (TySAnd (TySAnd TySInt TySTring) TySInt))
Right 3
-}
countTypesInConstructor :: SourceTyp -> Either SourceTypeError Int
countTypesInConstructor (TySAnd tA _) =
    countTypesInConstructor tA >>= \left -> return $ left + 1
countTypesInConstructor _ =
    Right 1

{- | `isPatternPresentInVariantTy` is a utility function that ensures each case in a match statement
  is well typed and returns the corresponding type of constructor from the variant type
  via a type label lookup.

=== Example:
>>> isPatternPresentInVariantTy (TySUnion (TySRecord "Num" TySInt) (TySRecord "Var" TySString)) ("Var", ["x"])
Right TySString

>>> isPatternPresentInVariantTy (TySUnion (TySRecord "Num" TySInt) (TySRecord "Var" TySString)) ("Var", ["x", "y"])
Left (STypeError "The number of bindings in the case Var do not match the data type constructor")

>>> isPatternPresentInVariantTy (TySUnion (TySRecord "Num" TySUnit) (TySRecord "Var" TySString)) ("Num", [])
Right TySUnit
-}
isPatternPresentInVariantTy :: SourceTyp -> Pattern -> Either SourceTypeError SourceTyp
isPatternPresentInVariantTy variantTy (label, bindings) =
    -- Firstly, a label lookup is performed on the variantTy
    case rlookupVariant variantTy of
        Just ty ->
            -- This gives the type, but we need to ensure containment for uniqueness
            if containmentUnion (TySRecord label ty) variantTy
                then
                    if (ty == TySUnit && countBindings == 0)
                        || (countTypesInConstructor ty == Right countBindings)
                        then Right ty
                        else Left $ STypeError ("The number of bindings in the case " ++ label ++ " do not match the data type constructor")
                else Left $ STypeError ("Duplicate constructor found in the variant type: " ++ show variantTy)
        Nothing ->
            Left $ STypeError ("Constructor " ++ label ++ " not present in the variant type: " ++ show variantTy)
  where
    countBindings = length bindings
    rlookupVariant :: SourceTyp -> Maybe SourceTyp
    rlookupVariant (TySRecord l t)
        | l == label = Just t
    rlookupVariant (TySUnion tA tB) =
        case rlookupVariant tB of
            Just t -> Just t
            Nothing -> rlookupVariant tA
    rlookupVariant _ = Nothing

{- | `insertIntersectionContext` is a utility function that inserts an intersection type in the context
correct.

=== Example:
>>> insertIntersectionContext (TySAnd TySUnit TySInt) (TySAnd (TySAnd TySString TySInt) TySBool)
Right (TySAnd (TySAnd (TySAnd (TySAnd TySUnit TySInt) TySString) TySInt) TySBool)
-}
insertIntersectionContext :: SourceTyp -> SourceTyp -> Either SourceTypeError SourceTyp
insertIntersectionContext ctx (TySAnd tA tB) =
    insertIntersectionContext ctx tA >>= \left -> return $ TySAnd left tB
insertIntersectionContext ctx ty =
    Right $ TySAnd ctx ty

{- | `elaborateCase` is a utility function that elaborates single case/pattern in the match statement.

=== Example:
>>> elaborateCase TySUnit (TySAnd (TySRecord "Num" TySInt) (TySRecord "Var" TySString)) (("Num", ["x"]), (TmLit 1))
Right (("Num",["x"]),TySInt,Lit 1)

>>> elaborateCase TySUnit (TySAnd (TySRecord "Num" TySInt) (TySRecord "Var" TySString)) (("Var", ["x"]), (TmLit 1))
Right (("Var",["x"]),TySInt,Lit 1)
-}
elaborateCase :: SourceTyp -> SourceTyp -> (Pattern, SourceTm) -> Either SourceTypeError (Pattern, SourceTyp, CoreTm)
elaborateCase ctx variantTy ((label, bindings), tm) =
    isPatternPresentInVariantTy variantTy (label, bindings) >>= \ty' ->
        insertIntersectionContext ctx ty' >>= \ctx' ->
            case elaborateInfer ctx' tm of
                Right (caseTy, caseTm') ->
                    Right ((label, bindings), caseTy, caseTm')
                Left err -> Left err

{- | `elaborateCases` is a utility function that elaborates all the cases in the match statement.

=== Example:
>>> elaborateCasesCheck TySUnit TySInt (TySAnd (TySRecord "Num" TySInt) (TySRecord "Var" TySString)) [(("Var", ["x"]), (TmLit 1)), (("Num", ["x"]), (TmLit 1))]
Right [(("Var",["x"]),Lit 1),(("Num",["x"]),Lit 1)]

>>> elaborateCasesCheck TySUnit TySInt (TySUnion (TySRecord "Num" TySInt) (TySRecord "Var" TySString)) [(("Var", ["x"]), (TmProj TmCtx 0)), (("Var", ["x"]), (TmProj TmCtx 0))]
Data constructor not in scope:
  TySUnion :: SourceTyp -> SourceTyp -> SourceTyp
-}
elaborateCasesCheck :: SourceTyp -> SourceTyp -> SourceTyp -> [(Pattern, SourceTm)] -> Either SourceTypeError [(Pattern, CoreTm)]
elaborateCasesCheck _ _ _ [] = Right []
elaborateCasesCheck ctx ty1 variantTy (x : xs) =
    case elaborateCase ctx variantTy x of
        Right (pattern, ty', ctm1) ->
            if ty1 == ty'
                then
                    elaborateCasesCheck ctx ty1 variantTy xs
                        >>= \xs' -> return ((pattern, ctm1) : xs')
                else Left $ STypeError "Types don't match for all the case branches"
        Left err -> Left err

-- `elaborateMatch` is a function that elaborates the match statement.
--
-- === Example:
-- >>> elaborateMatch TySUnit (TmCase (Lit 1) [(("Var", ["x"]), (TmProj TmCtx 0)), (("Var", ["x"]), (TmProj TmCtx 0))])
elaborateMatch :: SourceTyp -> SourceTm -> Either SourceTypeError Elab
elaborateMatch _ (TmCase _ []) = Left $ STypeError "Match statement must have atleast one case"
elaborateMatch ctx (TmCase tm (fstcase : cases)) =
    case elaborateInfer ctx tm of
        Right (variantTy@(TySUnion _ _), tm') ->
            if countLabels variantTy == Right (length cases + 1) && isUnique (fstcase : cases)
                then case elaborateCase ctx variantTy fstcase of
                    Right (pattern, ty1, tm1) ->
                        elaborateCasesCheck ctx ty1 variantTy cases
                            >>= \cases' -> return (ty1, Case tm' ((pattern, tm1) : cases'))
                    Left err -> Left err
                else Left $ STypeError "Fewer cases present in the match than the constructors in the ADT"
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

elaborateInfer :: SourceTyp -> SourceTm -> Either SourceTypeError Elab
elaborateInfer ctx TmCtx = Right (ctx, Ctx)
elaborateInfer _ TmUnit = Right (TySUnit, Unit)
elaborateInfer _ (TmLit i) = Right (TySInt, Lit i)
elaborateInfer _ (TmBool b) = Right (TySBool, EBool b)
elaborateInfer _ (TmString s) = Right (TySString, EString s)
elaborateInfer ctx (TmLam tA tm) =
    case elaborateInfer (TySAnd ctx tA) tm of
        Right (tB, tm') -> Right (TySArrow tA tB, Lam (elaborateTyp tA) tm')
        Left (STypeError err) ->
            Left $
                generateError
                    ctx
                    tm
                    "Couldn't infer the type of the term inside abstraction."
                    ("Check the term inside abstraction. \n \n-----Further info-----\n \n" ++ err)
elaborateInfer ctx (TmClos e1 tA e2) =
    case elaborateInfer TySUnit e1 of
        Right (gamma', e1') ->
            case elaborateInfer (TySAnd gamma' tA) e2 of
                Right (tB, e2') ->
                    Right
                        (TySArrow tA tB, Box e1' (Lam (elaborateTyp tA) e2'))
                Left err -> Left err
        Left (STypeError err) ->
            Left $
                generateError
                    ctx
                    (TmClos e1 tA e2)
                    "Couldn't infer the type of closure environment."
                    ("Check the environment passed into the closure. \n \n \n-----Further info-----\n \n \n" ++ err)
elaborateInfer ctx (TmRec l tm) =
    case elaborateInfer ctx tm of
        Right (tA, tm') ->
            Right (TySRecord l tA, Rec l tm')
        Left (STypeError err) ->
            Left $ generateError ctx (TmRec l tm) "Typecheck failed at a record/assignment." err
elaborateInfer ctx (TmRProj tm l) =
    case elaborateInfer ctx tm of
        Right (tB, tm') ->
            case rlookupt tB l of
                Just tA ->
                    if containment (TySRecord l tA) tB
                        then Right (tA, RProj tm' l)
                        else
                            Left $
                                generateError
                                    ctx
                                    tm
                                    "Containment failed for labeled lookup."
                                    "Make sure that are no ambiguous lookups."
                Nothing ->
                    Left $
                        generateError
                            ctx
                            tm
                            "Lookup failed. Label doesn't exists!"
                            ("Check whether label " ++ show l ++ " exists in the record.")
        Left err -> Left err
elaborateInfer ctx (TmProj tm n) =
    case elaborateInfer ctx tm of
        Right (tB, tm') -> case lookupt tB n of
            Just tA -> Right (tA, Proj tm' n)
            Nothing ->
                Left $
                    generateError
                        tB
                        tm
                        "Type error on index lookup failed."
                        "Make sure the term is present in context."
        Left (STypeError err) ->
            Left $
                generateError
                    ctx
                    tm
                    "Type error on term for projection."
                    ("Make sure that term is correct before projecting\n \n-----Further info-----\n \n" ++ err)
elaborateInfer ctx (TmApp tm1 tm2) =
    case elaborateInfer ctx tm1 of
        Right (typ, tm1') ->
            case typ of
                (TySArrow tA tB) ->
                    case elaborateCheck ctx tm2 tA of
                        Right tm2' -> Right (tB, App tm1' tm2')
                        Left (STypeError err) ->
                            Left $
                                generateError
                                    ctx
                                    tm2
                                    ("Type error on application: expected type " ++ show tA)
                                    err
                (TySSig tA tB) ->
                    case elaborateCheck ctx tm2 tA of
                        Right tm2' -> Right (tB, App tm1' tm2')
                        Left (STypeError err) ->
                            Left $
                                generateError
                                    ctx
                                    tm2
                                    ("Type error on module application: expected type " ++ show tA)
                                    err
                _ ->
                    Left $
                        generateError
                            ctx
                            tm1
                            ("Type error on application: function type expected, but got" ++ show typ)
                            "Make sure that function is well-defined."
        Left (STypeError err) ->
            Left $
                generateError
                    ctx
                    tm1
                    "Type error on application"
                    ("Check the function \n \n-----Further info-----\n \n" ++ err)
elaborateInfer ctx (TmMrg tm1 tm2) =
    case elaborateInfer ctx tm1 of
        Right (ty1, tm1') ->
            case elaborateInfer (TySAnd ctx ty1) tm2 of
                Right (ty2, tm2') -> Right (TySAnd ty1 ty2, Mrg tm1' tm2')
                Left (STypeError err) ->
                    Left $
                        generateError
                            (TySAnd ctx ty1)
                            tm2
                            "Type error on second term in merge."
                            ("Check if second part of merge is well-defined. \n \n-----Further info-----\n \n" ++ err)
        Left (STypeError err) ->
            Left $
                generateError
                    ctx
                    (TmMrg tm1 tm2)
                    "Type error on first-part of merge."
                    ("Check if first part of merge is well-defined. \n \n-----Further info-----\n \n" ++ err)
elaborateInfer ctx (TmBox tm1 tm2) =
    case elaborateInfer ctx tm1 of
        Right (ctx', tm1') ->
            case elaborateInfer ctx' tm2 of
                Right (ty, tm2') ->
                    Right (ty, Box tm1' tm2')
                Left (STypeError err) ->
                    Left $
                        generateError
                            ctx'
                            tm2
                            "Type error on the term inside the box."
                            ("Check if the term inside the box is well-defined.\n \n-----Further info-----\n \n" ++ err)
        Left (STypeError err) ->
            Left $
                generateError
                    ctx
                    tm1
                    "Type error on box construct"
                    ("Make sure that the environment for box construct is correct.\n \n-----Further info-----\n \n" ++ err)
elaborateInfer ctx (TmIf tm1 tm2 tm3) =
    case elaborateCheck ctx tm1 TySBool of
        Right tm1' ->
            case elaborateInfer ctx tm2 of
                Right (ty2, tm2') ->
                    case elaborateCheck ctx tm3 ty2 of
                        Right tm3' ->
                            Right (ty2, If tm1' tm2' tm3')
                        Left (STypeError _err) ->
                            Left $
                                generateError
                                    ctx
                                    tm3
                                    "Type error on the if statement: types don't match of then and else branch."
                                    "Make sure that the types of both branches are same"
                Left (STypeError err) ->
                    Left $
                        generateError
                            ctx
                            tm2
                            "Type error on the then branch of if statement"
                            ("Make sure that the term inside `then` is well-defined and sound.\n----Further info-----\n" ++ err)
        Left (STypeError err) ->
            Left $
                generateError
                    ctx
                    tm1
                    "Type error on condition: condition must be of type Bool"
                    ("Fix the condition and make sure it is of type Bool.\n \n-----Further info-----\n \n" ++ err)
elaborateInfer ctx (TmFix ty tm) =
    case elaborateCheck (TySAnd ctx ty) tm ty of
        Right tm' -> Right (ty, Fix (elaborateTyp ty) tm')
        Left (STypeError err) ->
            Left $
                generateError
                    ctx
                    (TmFix ty tm)
                    "Type error on fixpoint"
                    err
elaborateInfer ctx (TmStruct tyA tm) =
    case elaborateInfer (TySAnd TySUnit tyA) tm of
        Right (tyB, tm') -> Right (TySSig tyA tyB, Box Unit (Lam (elaborateTyp tyA) tm'))
        Left (STypeError err) ->
            Left $
                generateError
                    ctx
                    (TmStruct tyA tm)
                    "Type error on module."
                    ("Fix the module.\n \n-----Further info-----\n \n" ++ err)
elaborateInfer ctx (TmTag tm ty) =
    case elaborateInfer ctx tm of
        Right (TySRecord _ ty', Rec l tm') ->
            if containmentUnion (TySRecord l ty') ty
                then Right (ty, Tag (Rec l tm') (elaborateTyp ty))
                else
                    Left $
                        generateError
                            ctx
                            tm
                            "Type error on ADT"
                            "Ambiguous label in ADT"
        _ ->
            Left $
                generateError
                    ctx
                    tm
                    "Type error on algebraic data type instance."
                    "Only an ADT constructor can be tagged."
elaborateInfer ctx (TmCase tm cases) = elaborateMatch ctx (TmCase tm cases)
elaborateInfer ctx (TmBinOp (Arith op) tm1 tm2) =
    case elaborateCheck ctx tm1 TySInt of
        Right tm1' ->
            case elaborateCheck ctx tm2 TySInt of
                Right tm2' ->
                    Right (TySInt, BinOp (Arith op) tm1' tm2')
                Left (STypeError err) ->
                    Left $
                        generateError
                            ctx
                            (TmBinOp (Arith op) tm1 tm2)
                            ("Type error on arithmetic operation `" ++ show op ++ "`. Types on both sides must be Int.")
                            ("Make sure that types of both operands are Int.\n \n-----Further info-----\n \n" ++ err)
        Left err ->
            Left $
                generateError
                    ctx
                    tm1
                    ("Type error on first operand of the operator" ++ show op)
                    ("First operand has type error.\n \n-----Further info-----\n \n" ++ show err)
elaborateInfer ctx (TmBinOp (Comp op) tm1 tm2) =
    case elaborateInfer ctx tm1 of
        Right (TySInt, tm1') ->
            case elaborateCheck ctx tm2 TySInt of
                Right tm2' ->
                    Right (TySBool, BinOp (Comp op) tm1' tm2')
                Left (STypeError err) ->
                    Left $
                        generateError
                            ctx
                            (TmBinOp (Comp op) tm1 tm2)
                            ("Type error on comparsion operation `" ++ show op ++ "`. Types on both sides must be Int.")
                            ("Make sure that types of both operands are Int.\n \n-----Further info-----\n \n" ++ err ++ "\n")
        Right (TySBool, tm1') ->
            case elaborateCheck ctx tm2 TySBool of
                Right tm2' ->
                    Right (TySBool, BinOp (Comp op) tm1' tm2')
                Left (STypeError err) ->
                    Left $
                        generateError
                            ctx
                            (TmBinOp (Comp op) tm1 tm2)
                            ("Type error on comparsion operation `" ++ show op ++ "`. Types on both sides must be Bool.")
                            ("Make sure that types of both operands are Bool.\n \n-----Further info-----\n \n" ++ err)
        Right (TySString, tm1') ->
            case elaborateCheck ctx tm2 TySString of
                Right tm2' ->
                    Right (TySBool, BinOp (Comp op) tm1' tm2')
                Left (STypeError err) ->
                    Left $
                        generateError
                            ctx
                            (TmBinOp (Comp op) tm1 tm2)
                            ("Type error on comparsion operation `" ++ show op ++ "`. Types on both sides must be String.")
                            ("Make sure that types of both operands are String.\n \n-----Further info-----\n \n" ++ err)
        Right (_, _) ->
            Left $
                generateError
                    ctx
                    (TmBinOp (Comp op) tm1 tm2)
                    ("Type error on comparsion operation `" ++ show op ++ "`. Types on both sides must be String.")
                    "Make sure that types of both operands are of same type.\n \n-----Further info-----\n \n"
        Left (STypeError err) ->
            Left $
                generateError
                    ctx
                    tm1
                    ("Type error on first operand of the comparison operator" ++ show op)
                    ("First operand has type error.\n \n-----Further info-----\n \n" ++ err)
elaborateInfer ctx (TmBinOp (Logic op) tm1 tm2) =
    case elaborateCheck ctx tm1 TySBool of
        Right tm1' ->
            case elaborateCheck ctx tm2 TySBool of
                Right tm2' ->
                    Right (TySBool, BinOp (Logic op) tm1' tm2')
                Left (STypeError err) ->
                    Left $
                        generateError
                            ctx
                            (TmBinOp (Logic op) tm1 tm2)
                            ("Type error on logic operation `" ++ show op ++ "`. Types on both sides must be Bool.")
                            ("Make sure that types of both operands are Bool.\n \n-----Further info-----\n \n" ++ err)
        Left (STypeError err) ->
            Left $
                generateError
                    ctx
                    tm1
                    ("Type error on first operand of the logic operator" ++ show op)
                    ("First operand has type error.\n \n-----Further info-----\n \n" ++ err)
elaborateInfer ctx (TmUnOp Not tm) =
    case elaborateInfer ctx tm of
        Right (ty, tm') -> Right (ty, UnOp Not tm')
        Left err -> Left err
elaborateInfer ctx (TmAnno tm typ) =
    case elaborateCheck ctx tm typ of
        Right tm' -> Right (typ, tm')
        Left err ->
            Left $
                generateError
                    ctx
                    (TmAnno tm typ)
                    "Type error on the annotation."
                    ("Type inferred from term does not checks with the type on the annotation. \n \n----Further info-----\n \n" ++ show err)

elaborateCheck :: SourceTyp -> SourceTm -> SourceTyp -> Either SourceTypeError CoreTm
elaborateCheck ctx tm typ =
    case elaborateInfer ctx tm of
        Right (typ', e') ->
            if typ == typ'
                then Right e'
                else
                    Left $
                        generateError
                            ctx
                            tm
                            ("Couldn't match expected type \'" ++ show typ ++ "\' with actual type \'" ++ show typ' ++ "\'")
                            "Please check your code."
        Left err -> Left err
