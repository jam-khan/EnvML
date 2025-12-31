module EnvML.PrettyPrint where

import EnvML.Errors (SurfacePrettyPrintError (PrettyPrintFailed))
import Syntax

import Data.List (intercalate)
import Text.Printf (printf)

-- ANSI escape codes for colored output (optional)
colorRed, colorGreen, colorBlue, colorReset :: String
colorRed = "\x1b[31m"
colorGreen = "\x1b[32m"
colorBlue = "\x1b[34m"
colorReset = "\x1b[0m"

-- Pretty print SurfaceTm
prettySurfaceTm :: SurfaceTm -> String
prettySurfaceTm (SCtx) = "ctx"
prettySurfaceTm (SUnit) = "()"
prettySurfaceTm (SLit n) = show n
prettySurfaceTm (SBool b) = show b
prettySurfaceTm (SString s) = show s
prettySurfaceTm (SLam params body) =
    let paramStr = intercalate ", " (map (\(name, typ) -> name ++ " : " ++ prettySurfaceTyp typ) params)
     in printf "\\(%s) => { %s }" paramStr (prettySurfaceTm body)
prettySurfaceTm (SClos tm params body) =
    printf "closure(%s, %s, %s)" (prettySurfaceTm tm) (show params) (prettySurfaceTm body)
prettySurfaceTm (SRec label body) =
    printf "{%s = %s}" label (prettySurfaceTm body)
prettySurfaceTm (SRProj tm label) =
    printf "%s.%s" (prettySurfaceTm tm) label
prettySurfaceTm (SProj tm idx) =
    printf "%s.%d" (prettySurfaceTm tm) idx
prettySurfaceTm (SApp func args) =
    let funcStr = prettySurfaceTm func
        argsStr = intercalate ", " (map prettySurfaceTm args)
     in printf "%s(%s)" funcStr argsStr
prettySurfaceTm (SMrg tm1 tm2) =
    printf "merge(%s, %s)" (prettySurfaceTm tm1) (prettySurfaceTm tm2)
prettySurfaceTm (SBox tm1 tm2) =
    printf "box(%s, %s)" (prettySurfaceTm tm1) (prettySurfaceTm tm2)
prettySurfaceTm (SVar name) = name
prettySurfaceTm (SStruct params body) =
    let paramStr = intercalate ", " (map (\(name, typ) -> name ++ " : " ++ prettySurfaceTyp typ) params)
     in printf "struct(%s) { %s }" paramStr (prettySurfaceTm body)
prettySurfaceTm (SFunc name params typ body) =
    let paramStr = intercalate ", " (map (\(name, typ) -> name ++ " : " ++ prettySurfaceTyp typ) params)
     in printf "func %s(%s) : %s { %s }" name paramStr (prettySurfaceTyp typ) (prettySurfaceTm body)
prettySurfaceTm (SModule name params body) =
    let paramStr = intercalate ", " (map (\(name, typ) -> name ++ " : " ++ prettySurfaceTyp typ) params)
     in printf "module %s(%s) { %s }" name paramStr (prettySurfaceTm body)
prettySurfaceTm (SAliasTyp name typ) =
    printf "type %s = %s" name (prettySurfaceTyp typ)
prettySurfaceTm (SLet bindings body) =
    let bindingStr = intercalate "; " (map (\(name, typ, tm) -> name ++ " : " ++ prettySurfaceTyp typ ++ " = " ++ prettySurfaceTm tm) bindings)
     in printf "let %s in %s" bindingStr (prettySurfaceTm body)
prettySurfaceTm (SLetrec bindings body) =
    let bindingStr = intercalate "; " (map (\(name, typ, tm) -> name ++ " : " ++ prettySurfaceTyp typ ++ " = " ++ prettySurfaceTm tm) bindings)
     in printf "letrec %s in %s" bindingStr (prettySurfaceTm body)
prettySurfaceTm (SBinOp op tm1 tm2) =
    let opStr = prettyBinaryOp op
     in printf "(%s %s %s)" (prettySurfaceTm tm1) opStr (prettySurfaceTm tm2)
prettySurfaceTm (SUnOp op tm) =
    let opStr = prettyUnaryOp op
     in printf "(%s %s)" opStr (prettySurfaceTm tm)
prettySurfaceTm (SAnno tm typ) =
    printf "(%s : %s)" (prettySurfaceTm tm) (prettySurfaceTyp typ)
prettySurfaceTm (SIf cond thenTm elseTm) =
    printf "if %s then %s else %s" (prettySurfaceTm cond) (prettySurfaceTm thenTm) (prettySurfaceTm elseTm)
prettySurfaceTm (SPair tm1 tm2) =
    printf "(%s, %s)" (prettySurfaceTm tm1) (prettySurfaceTm tm2)
prettySurfaceTm (SFst tm) =
    printf "fst(%s)" (prettySurfaceTm tm)
prettySurfaceTm (SSnd tm) =
    printf "snd(%s)" (prettySurfaceTm tm)
prettySurfaceTm (SNil typ) =
    printf "nil[%s]" (prettySurfaceTyp typ)
prettySurfaceTm (SCons tm1 tm2) =
    printf "cons(%s, %s)" (prettySurfaceTm tm1) (prettySurfaceTm tm2)
prettySurfaceTm (STuple tms) =
    printf "(%s)" (intercalate ", " (map prettySurfaceTm tms))
-- prettySurfaceTm (SSwitch tm cases) =
--     let caseStr = intercalate "; " (map (\(pat, tm) -> prettyPattern pat ++ " => " ++ prettySurfaceTm tm) cases)
-- in printf "switch %s { %s }" (prettySurfaceTm tm) caseStr
prettySurfaceTm (SADTInst (name, args) typ) =
    printf "%s[%s](%s)" name (prettySurfaceTyp typ) (intercalate ", " (map prettySurfaceTm args))
prettySurfaceTm (SCase tm cases) =
    let caseStr = intercalate "; " (map (\(pat, tm) -> prettyPattern pat ++ " => " ++ prettySurfaceTm tm) cases)
     in printf "case %s of { %s }" (prettySurfaceTm tm) caseStr
prettySurfaceTm _ = ""

-- Pretty print SurfaceTyp
prettySurfaceTyp :: SurfaceTyp -> String
prettySurfaceTyp STUnit = "Unit"
prettySurfaceTyp STInt = "Int"
prettySurfaceTyp (STAnd typ1 typ2) =
    printf "%s & %s" (prettySurfaceTyp typ1) (prettySurfaceTyp typ2)
prettySurfaceTyp (STArrow typ1 typ2) =
    printf "%s -> %s" (prettySurfaceTyp typ1) (prettySurfaceTyp typ2)
prettySurfaceTyp (STRecord label typ) =
    printf "{%s : %s}" label (prettySurfaceTyp typ)
prettySurfaceTyp STBool = "Bool"
prettySurfaceTyp STString = "String"
prettySurfaceTyp (STList typ) =
    printf "List[%s]" (prettySurfaceTyp typ)
prettySurfaceTyp (STUnion typ1 typ2) =
    printf "%s | %s" (prettySurfaceTyp typ1) (prettySurfaceTyp typ2)
prettySurfaceTyp (STSig typ1 typ2) =
    printf "Sig(%s, %s)" (prettySurfaceTyp typ1) (prettySurfaceTyp typ2)
prettySurfaceTyp (STIden name) = name

-- Pretty print BinaryOp
prettyBinaryOp :: BinaryOp -> String
prettyBinaryOp (Arith Add) = "+"
prettyBinaryOp (Arith Sub) = "-"
prettyBinaryOp (Arith Mul) = "*"
prettyBinaryOp (Arith Div) = "/"
prettyBinaryOp (Arith Mod) = "%"
prettyBinaryOp (Comp Eql) = "=="
prettyBinaryOp (Comp Neq) = "!="
prettyBinaryOp (Comp Lt) = "<"
prettyBinaryOp (Comp Le) = "<="
prettyBinaryOp (Comp Gt) = ">"
prettyBinaryOp (Comp Ge) = ">="
prettyBinaryOp (Logic And) = "&&"
prettyBinaryOp (Logic Or) = "||"

-- Pretty print UnaryOp
prettyUnaryOp :: UnaryOp -> String
prettyUnaryOp Not = "!"

-- Pretty print Pattern
prettyPattern :: Pattern -> String
prettyPattern (name, args) =
    if null args
        then name
        else printf "%s(%s)" name (intercalate ", " args)

-- Example usage
main :: IO ()
main = do
    let exampleTm = SLam [("x", STInt), ("y", STInt)] (SBinOp (Arith Add) (SVar "x") (SVar "y"))
    putStrLn $ prettySurfaceTm exampleTm
