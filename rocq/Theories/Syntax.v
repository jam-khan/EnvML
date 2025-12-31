Require Import Arith.
From Coq Require Import Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.EquivDec.


Module Syntax.

Inductive styp :=
  | Sint : styp
  | Stop : styp
  | Sarr : styp -> styp -> styp
  | Sand : styp -> styp -> styp
  | Srcd : string -> styp -> styp
  | Ssig : styp -> styp -> styp.

Inductive sop := Sapp | Swith | SDmrg | SNmrg | SMapp.

Inductive sexp :=
  | Sctx        : sexp  
  | Sunit       : sexp
  | Slit        : nat   -> sexp
  | Sbinop      : sop   -> sexp -> sexp -> sexp
  | Slam        : styp  -> sexp -> sexp
  | Sproj       : sexp  -> nat  -> sexp
  | SClos       : sexp  -> styp -> sexp -> sexp
  | SStruct     : styp  -> sexp -> sexp
  | Srec        : string -> sexp -> sexp
  | Srproj      : sexp -> string -> sexp
  | Slet        : sexp -> styp -> sexp -> sexp
  | Sopen       : sexp -> sexp -> sexp.

Inductive typ :=
  | int : typ
  | top : typ
  | arr : typ -> typ -> typ
  | and : typ -> typ -> typ
  | rcd : string -> typ -> typ.

Inductive op := app | box | mrg.

Inductive exp :=
  | ctx         : exp
  | lit         : nat -> exp
  | unit        : exp
  | binop       : op -> exp -> exp -> exp
  | lam         : typ -> exp -> exp
  | proj        : exp -> nat -> exp
  | clos        : exp -> typ -> exp -> exp
  | rec         : string -> exp -> exp
  | rproj       : exp -> string -> exp.

End Syntax.