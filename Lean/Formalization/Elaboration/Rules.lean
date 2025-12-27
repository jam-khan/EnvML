import Formalization.ENVCAP.Syntax
import Formalization.LambdaE.Syntax

namespace ENVCAP

/-
  Type Elaboration from ENVCAP Types to λE Types

  This module defines the type translation |·| from ENVCAP types
  (used in the source language) to λE types (used in the elaborated/core language).

  The elaboration rules are as follows:

    |i|          = i
    |ε|          = ε
    |A → B|      = |A| → |B|
    |{l : A}|    = {l : |A|}
    |Sig[A, B]|  = |A| → |B|

-/

def ElaborateType : Typ → LambdaE.Typ
  | Typ.int        => LambdaE.Typ.int
  | Typ.top        => LambdaE.Typ.top
  | Typ.arr t1 t2  => LambdaE.Typ.arr (ElaborateType t1) (ElaborateType t2)
  | Typ.and t1 t2  => LambdaE.Typ.and (ElaborateType t1) (ElaborateType t2)
  | Typ.rcd str t  => LambdaE.Typ.rcd str (ElaborateType t)
  | Typ.sig t1 t2  => LambdaE.Typ.arr (ElaborateType t1) (ElaborateType t2)

inductive ElaborateExp : Typ -> Exp -> Typ -> LambdaE.Exp -> Prop
| ctx (EnvT : Typ) : ElaborateExp EnvT Exp.ctx EnvT LambdaE.Exp.ctx
| int (EnvT : Typ) (i : Nat) : ElaborateExp EnvT (Exp.lit i) Typ.int (LambdaE.Exp.lit i)
| unit (EnvT : Typ) : ElaborateExp EnvT Exp.unit Typ.top LambdaE.Exp.unit
| proj (EnvT A B : Typ) (n : Nat) (e : Exp) (ce : LambdaE.Exp) :
    ElaborateExp EnvT e A ce →
    IndexLookup A n B →
    ElaborateExp EnvT (Exp.proj e n) B (LambdaE.Exp.proj ce n)
| lam (EnvT A B : Typ) (e : Exp) (ce : LambdaE.Exp) :
    ElaborateExp (Typ.and EnvT A) e B ce →
    ElaborateExp EnvT (Exp.lam A e) (Typ.arr A B) (LambdaE.Exp.lam (ElaborateType A) ce)
| box (EnvT EnvT₁ A: Typ) (e₁ e₂ : Exp) (ce₁ ce₂ : LambdaE.Exp) :
    ElaborateExp EnvT e₁ EnvT₁ ce₁ →
    ElaborateExp EnvT₁ e₂ A ce₂ →
    ElaborateExp EnvT (Exp.binop Op.withE e₁ e₂) A
    (LambdaE.Exp.binop LambdaE.Op.box ce₁ ce₂)
| clos (EnvT EnvT₁ A B : Typ) (e env : Exp) (ce cenv : LambdaE.Exp) :
    ElaborateExp EnvT env EnvT₁ cenv →
    ElaborateExp (Typ.and EnvT₁ A) e B ce →
    ElaborateExp EnvT (Exp.clos env A e) (Typ.arr A B)
    (LambdaE.Exp.binop LambdaE.Op.box cenv (LambdaE.Exp.lam (ElaborateType A) ce))
| app (EnvT A B : Typ) (e₁ e₂ : Exp) (ce₁ ce₂ : LambdaE.Exp) :
    ElaborateExp EnvT e₁ (Typ.arr A B) ce₁ →
    ElaborateExp EnvT e₂ A ce₂ →
    ElaborateExp EnvT (Exp.binop Op.app e₁ e₂) B
    (LambdaE.Exp.binop LambdaE.Op.app ce₁ ce₂)
| dmrg (EnvT A B : Typ) (e₁ e₂ : Exp) (ce₁ ce₂ : LambdaE.Exp) :
    ElaborateExp EnvT e₁ A ce₁ →
    ElaborateExp (Typ.and EnvT A) e₂ B ce₂ →
    ElaborateExp EnvT (Exp.binop Op.dmrg e₁ e₂) (Typ.and A B)
    (LambdaE.Exp.binop LambdaE.Op.mrg ce₁ ce₂)
| ndmrg (EnvT A B : Typ) (e₁ e₂ : Exp) (ce₁ ce₂ : LambdaE.Exp) :
    ElaborateExp EnvT e₁ A ce₁ →
    ElaborateExp EnvT e₂ B ce₂ →
    ElaborateExp EnvT (Exp.binop Op.ndmrg e₁ e₂) (Typ.and A B)
    (LambdaE.Exp.binop LambdaE.Op.app
      (LambdaE.Exp.lam (ElaborateType EnvT)
        (LambdaE.Exp.binop LambdaE.Op.mrg
          (LambdaE.Exp.binop LambdaE.Op.box (LambdaE.Exp.proj LambdaE.Exp.ctx 0) ce₁)
          (LambdaE.Exp.binop LambdaE.Op.box (LambdaE.Exp.proj LambdaE.Exp.ctx 1) ce₂)))
      LambdaE.Exp.ctx)
| struct (EnvT A B : Typ) (e : Exp) (ce : LambdaE.Exp) :
    ElaborateExp (Typ.and Typ.top A) e B ce →
    ElaborateExp EnvT (Exp.struct A e) (Typ.sig A B) (LambdaE.Exp.binop LambdaE.Op.box LambdaE.Exp.unit (LambdaE.Exp.lam (ElaborateType A) ce))
| modapp (EnvT A B : Typ) (e₁ e₂ : Exp) (ce₁ ce₂ : LambdaE.Exp) :
    ElaborateExp EnvT e₁ (Typ.sig A B) ce₁ →
    ElaborateExp EnvT e₂ A ce₂ →
    ElaborateExp EnvT (Exp.binop Op.mapp e₁ e₂) B
    (LambdaE.Exp.binop LambdaE.Op.app ce₁ ce₂)
| lrec (EnvT A : Typ) (e : Exp) (ce : LambdaE.Exp) (label : String) :
    ElaborateExp EnvT e A ce →
    ElaborateExp EnvT (Exp.lrec label e) (Typ.rcd label A)
    (LambdaE.Exp.lrec label ce)
| rproj (EnvT A B : Typ) (e : Exp) (ce : LambdaE.Exp) (label : String) :
    ElaborateExp EnvT e B ce →
    RecordLookup B label A →
    ElaborateExp EnvT (Exp.rproj e label) A (LambdaE.Exp.rproj ce label)
| slet (EnvT A B : Typ) (e₁ e₂ : Exp) (ce₁ ce₂ : LambdaE.Exp) :
    ElaborateExp EnvT e₁ A ce₁ →
    ElaborateExp (Typ.and EnvT A) e₂ B ce₂ →
    ElaborateExp EnvT (Exp.slet e₁ A e₂) B
    (LambdaE.Exp.binop LambdaE.Op.app
      (LambdaE.Exp.lam (ElaborateType A) ce₂)
      ce₁)
| sopen (EnvT A B : Typ) (e₁ e₂ : Exp) (ce₁ ce₂ : LambdaE.Exp) (label : String) :
    RecordLookup (Typ.rcd label A) label B →
    ElaborateExp EnvT e₁ (Typ.rcd label A) ce₁ →
    ElaborateExp EnvT (Exp.rproj e₁ label) A (LambdaE.Exp.rproj ce₁ label) →
    ElaborateExp (Typ.and EnvT A) e₂ B ce₂ →
    ElaborateExp EnvT (Exp.sopen e₁ e₂) B
    (LambdaE.Exp.binop LambdaE.Op.app
      (LambdaE.Exp.lam (ElaborateType A) ce₂)
      (LambdaE.Exp.rproj ce₁ label))

end ENVCAP
