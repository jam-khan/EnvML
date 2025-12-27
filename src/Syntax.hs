{-# HLINT ignore "Use camelCase" #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module Syntax where

import Data.Binary
import GHC.Generics (Generic)

data SourceTm
    = TmCtx 
    | TmUnit 
    | TmLit     Integer
    | TmBool    Bool 
    | TmString  String 
    | TmLam     SourceTyp SourceTm
    | TmClos    SourceTm SourceTyp SourceTm
    | TmRec     String SourceTm
    | TmRProj   SourceTm String
    | TmProj    SourceTm Integer
    | TmApp     SourceTm SourceTm
    | TmMrg     SourceTm SourceTm
    | TmBox     SourceTm SourceTm
    | TmIf      SourceTm SourceTm SourceTm
    | TmBinOp   BinaryOp SourceTm SourceTm
    | TmUnOp    UnaryOp SourceTm
    deriving (Eq, Show)

data SourceTyp
    = TySUnit
    | TySBool
    | TySString
    | TySInt
    | TySAnd    SourceTyp SourceTyp
    | TySArrow  SourceTyp SourceTyp
    | TySRecord String SourceTyp
    | TySIden   String
    deriving (Eq, Show)

data CoreTm
    = Ctx 
    | Unit
    | Lit     Integer
    | EBool   Bool
    | EString String 
    | Lam     CoreTyp CoreTm
    | Proj    CoreTm Integer
    | Clos    CoreTm CoreTm
    | Rec     String CoreTm
    | RProj   CoreTm String
    | App     CoreTm CoreTm
    | Mrg     CoreTm CoreTm
    | Box     CoreTm CoreTm
    | If      CoreTm CoreTm CoreTm
    | BinOp   BinaryOp CoreTm CoreTm
    | UnOp    UnaryOp CoreTm
    deriving (Eq, Show, Generic)

data CoreTyp
    = TyCUnit
    | TyCInt
    | TyCAnd    CoreTyp CoreTyp
    | TyCArrow  CoreTyp CoreTyp
    | TyCRecord String CoreTyp
    | TyCBool
    | TyCString
    deriving (Eq, Show, Generic)

data Value
    = VUnit
    | VInt    Integer
    | VClos   Value CoreTm
    | VRcd    String Value
    | VMrg    Value Value
    | VBool   Bool
    | VString String
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
