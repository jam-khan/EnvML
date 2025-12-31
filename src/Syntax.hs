{-# HLINT ignore "Use camelCase" #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module Syntax where

import Data.Binary
import GHC.Generics (Generic)

type Params = [(String, SurfaceTyp)]
type Letargs = [(String, SurfaceTyp, SurfaceTm)]
type Name = String
type Pattern = (String, [String])
type Cases = [(Pattern, SurfaceTm)]
type Imports = [String]

-- data Requirement        = Req String String | Param String SurfaceTyp
--                         deriving (Eq, Show)
-- For sake of simplicity, parameter requirements are not allowed yet.
data Requirement = Req String String
    deriving (Eq, Show)

type Requirements = [Requirement]
type ParseImplData = (Name, Authority, Imports, Requirements, SurfaceTm)
type ParseIntfData = (Name, Authority, Requirements, Interface)

type Interface = [InterfaceStmt]

data InterfaceStmt
    = IAliasTyp String SurfaceTyp
    | IAliasIntf String Interface
    | IType SurfaceTyp
    | IIden String
    | FunctionTyp Name Params SurfaceTyp
    | ModuleTyp Name Params Interface
    | Binding Name SurfaceTyp
    deriving (Eq, Show)

type Statements = [SurfaceTm]

data SurfaceTm
    = SCtx -- Query
    | SUnit -- Unit
    | SLit Integer -- Integer Literal
    | SBool Bool -- Boolean Literal
    | SString String -- String  Literal
    | SLam Params SurfaceTm -- Abstraction with binding
    | SClos SurfaceTm Params SurfaceTm
    | SRec String SurfaceTm
    | SRProj SurfaceTm String
    | SProj SurfaceTm Integer -- Projection on Expression
    | SApp SurfaceTm [SurfaceTm]
    | SMrg SurfaceTm SurfaceTm
    | SBox SurfaceTm SurfaceTm
    | SVar String
    | SStruct Params SurfaceTm
    | SFunc Name Params SurfaceTyp SurfaceTm
    | SModule Name Params SurfaceTm
    | {-- CAREFUL: Type Expansion --}
      SAliasTyp String SurfaceTyp
    | SAliasIntf String Interface
    | {-- CAREFUL: Type Expansion --}
      SLet Letargs SurfaceTm
    | SLetrec Letargs SurfaceTm
    | SBinOp BinaryOp SurfaceTm SurfaceTm
    | SUnOp UnaryOp SurfaceTm
    | SAnno SurfaceTm SurfaceTyp
    | SIf SurfaceTm SurfaceTm SurfaceTm
    | SPair SurfaceTm SurfaceTm
    | STuple [SurfaceTm]
    | SSwitch SurfaceTm [(SurfaceTm, SurfaceTm)]
    | SADTInst (String, [SurfaceTm]) SurfaceTyp
    | SCase SurfaceTm Cases
    | SOpen SurfaceTm SurfaceTm
    | -- List matching
      SNil SurfaceTyp
    | SCons SurfaceTm SurfaceTm
    | SList [SurfaceTm] SurfaceTyp
    deriving (Eq, Show)

data SurfaceTyp
    = -- | Unit type for empty environment
      STUnit
    | -- | Integer type
      STInt
    | -- | Boolean type
      STBool
    | -- | String type
      STString
    | -- | Intersection type
      STAnd SurfaceTyp SurfaceTyp
    | -- | Arrow type, e.g. A -> B
      STArrow SurfaceTyp SurfaceTyp
    | -- | Single-Field Record Type
      STRecord String SurfaceTyp
    | {- | Union
      Extensions
      -}
      STUnion SurfaceTyp SurfaceTyp
    | -- | Type for built-in list
      STList SurfaceTyp
    | -- | Sig Type End
      STSig SurfaceTyp SurfaceTyp
    | -- | Simply an alias
      STIden String
    deriving (Eq, Show)

data SourceFragment = TmFragment Name Authority SourceImport SourceRequirements SourceTyp
data Authority = Pure | Resource
    deriving (Eq, Show)

data SourceHeader = TmInterface Name Authority SourceRequirements SourceTyp
type SourceImport = [(String, SourceHeader)]
type SourceRequirements = [(String, SourceHeader)]

data SourceTm
    = TmCtx -- Query
    | TmUnit -- Unit
    | TmLit Integer -- Integer Literal
    | TmBool Bool -- Boolean Literal
    | TmString String -- String  Literal
    | TmLam SourceTyp SourceTm -- Abstraction with binding
    | TmClos SourceTm SourceTyp SourceTm
    | TmRec String SourceTm
    | TmRProj SourceTm String
    | TmProj SourceTm Integer -- Projection on Expression
    | TmApp SourceTm SourceTm
    | TmMrg SourceTm SourceTm
    | TmBox SourceTm SourceTm
    | -- Extension that require elaboration
      TmIf SourceTm SourceTm SourceTm
    | TmFix SourceTyp SourceTm
    | TmNil SourceTyp
    | TmCons SourceTm SourceTm
    | -- [SourceTm] should become merges
      TmTag SourceTm SourceTyp
    | TmCase SourceTm [(Pattern, SourceTm)]
    | TmBinOp BinaryOp SourceTm SourceTm
    | TmUnOp UnaryOp SourceTm
    | -- Not sure if tagging is needed at source level -- can be simply added during elaboration to core
      TmAnno SourceTm SourceTyp
    | TmTuple [SourceTm]
    | TmStruct SourceTyp SourceTm
    | TmModule String SourceTyp SourceTm
    deriving (Eq, Show)

data SourceTyp
    = TySUnit -- Unit type for empty environment
    | TySInt -- Integer type
    | TySAnd SourceTyp SourceTyp -- Intersection type
    | TySArrow SourceTyp SourceTyp -- Arrow type, e.g. A -> B
    | TySRecord String SourceTyp -- Single-Field Record Type
    | TySBool -- Boolean type
    | TySString -- String type
    | TySList SourceTyp -- Type for built-in list
    | TySUnion SourceTyp SourceTyp -- Type for sums
    | TySPair SourceTyp SourceTyp -- Type for pairs
    | TySSig SourceTyp SourceTyp -- Sig Type End
    | TySIden String -- Simply an alias
    deriving (Eq, Show)

data CoreTm
    = Ctx -- Context
    | Unit -- Unit
    | Lit Integer -- Integer literal
    | Lam CoreTyp CoreTm -- Lambda Abstraction
    | Proj CoreTm Integer -- Projection
    | Clos CoreTm CoreTm -- Closure
    | Rec String CoreTm -- Single-Field Record
    | RProj CoreTm String -- Record Projection by Label
    | App CoreTm CoreTm -- Application
    | Mrg CoreTm CoreTm -- Merge
    | Box CoreTm CoreTm -- Box
    -- Extensions
    | EBool Bool -- Boolean Term
    | EString String -- String Term
    | If CoreTm CoreTm CoreTm -- Conditionals
    | Fix CoreTyp CoreTm -- Recursion
    | Tag CoreTm CoreTyp
    | Case CoreTm [(Pattern, CoreTm)]
    | Nil CoreTyp -- Nil List with Type
    | Cons CoreTm CoreTm -- List expression
    | LCase CoreTm CoreTm CoreTm
    | BinOp BinaryOp CoreTm CoreTm -- Binary operations
    | UnOp UnaryOp CoreTm -- Unary operations
    -- Lambda for linking
    | CLam CoreTyp CoreTm
    | Anno CoreTm CoreTyp
    deriving (Eq, Show, Generic)

data CoreTyp
    = TyCUnit -- Unit type for empty environment
    | TyCInt -- Integer type
    | TyCAnd CoreTyp CoreTyp -- Intersection type
    | TyCArrow CoreTyp CoreTyp -- Arrow type, e.g. A -> B
    | TyCRecord String CoreTyp -- Single-Field Record Type
    -- Extensions
    | TyCUnion CoreTyp CoreTyp -- Union type
    | TyCList CoreTyp -- List Type
    | TyCBool -- Boolean type
    | TyCString -- String type
    deriving (Eq, Show, Generic)

data Value
    = VUnit -- Unit value
    | VInt Integer -- Integer value
    | VClos Value CoreTm -- Closure
    | VRcd String Value -- Single-field record value
    | VMrg Value Value -- Merge of two values
    -- Extensions
    | VNil CoreTyp
    | VCons Value Value
    | VTag Value CoreTyp
    | VBool Bool -- Boolean Value
    | VString String -- String Value
    deriving (Show, Eq, Generic)

instance Binary CoreTm
instance Binary CoreTyp
instance Binary Value
instance Binary BinaryOp
instance Binary UnaryOp
instance Binary ArithOp
instance Binary CompOp
instance Binary LogicOp

data UnaryOp = Not
    deriving (Eq, Show, Generic)

data BinaryOp
    = Arith ArithOp -- Arithmetic
    | Comp CompOp -- CompOp
    | Logic LogicOp -- Boolean Logic
    deriving (Eq, Show, Generic)

data ArithOp = Add | Sub | Mul | Div | Mod
    deriving (Eq, Show, Generic)

data CompOp = Eql | Neq | Lt | Le | Gt | Ge
    deriving (Eq, Show, Generic)

data LogicOp = And | Or
    deriving (Eq, Show, Generic)
