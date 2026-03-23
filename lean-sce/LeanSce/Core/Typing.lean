import LeanSce.Core.Syntax

open Core

inductive HasType : Typ → Exp → Typ → Prop where
  | tquery {Γ : Typ}
    : HasType Γ .query Γ
  | tint {Γ : Typ} {i : Nat}
    : HasType Γ (.lit i) .int
  | tunit {Γ : Typ}
    : HasType Γ .unit .top
  | tapp {Γ A B : Typ} {e₁ e₂ : Exp}
    : HasType Γ e₁ (.arr A B)
    → HasType Γ e₂ A
    → HasType Γ (.app e₁ e₂) B
  | tbox {Γ Γ₁ A B : Typ} {e₁ e₂ : Exp}
    : HasType Γ e₁ Γ₁
    → HasType Γ₁ e₂ A
    → HasType Γ (.box e₁ e₂) A
  | tmrg {Γ A B : Typ} {e₁ e₂ : Exp}
    : HasType Γ e₁ A
    → HasType (.and Γ A) e₂ B
    → HasType Γ (.mrg e₁ e₂) (.and A B)
  | tlam {Γ A B : Typ} {e : Exp}
    : HasType (.and Γ A) e B
    → HasType Γ (.lam A e) (.arr A B)
  | tproj {Γ A B : Typ} {e : Exp} {n : Nat}
    : HasType Γ e A
    → Lookup A n B
    → HasType Γ (.proj e n) B
  | tclos {Γ Γ₁ A B : Typ} {v e : Exp}
    : Value v
    → HasType .top v Γ₁
    → HasType (.and Γ₁ A) e B
    → HasType Γ (.clos v A e) (.arr A B)
  | trcd {Γ A : Typ} {l : String} {e : Exp}
    : HasType Γ e A
    → HasType Γ (.lrec l e) (.rcd l A)
  | trproj {Γ A B : Typ} {l : String} {e : Exp}
    : HasType Γ e B
    → RLookup B l A
    → HasType Γ (.rproj e l) A
