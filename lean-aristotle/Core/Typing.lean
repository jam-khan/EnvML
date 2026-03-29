import Core.Syntax

open Core

/--
  `HasType E e A` means: under environment type `E`, expression `e` has type `A`.

  Note: the environment is a *type* (not a context list). The `ctx` expression
  returns the current environment, `box` switches environments, and `mrg`
  extends the environment.
-/
inductive HasType : Typ → Exp → Typ → Prop where
  /-
    Γ ⊢ ? : Γ
  -/
  | tquery {Γ : Typ}
    : HasType Γ .query Γ
  /-
    Γ ⊢ i : Int
  -/
  | tint {Γ : Typ} {i : Nat}
    : HasType Γ (.lit i) .int
  /-
    Γ ⊢ () : ()
  -/
  | tunit {Γ : Typ}
    : HasType Γ .unit .top
  /-
    Γ ⊢ e₁ : A → B
    Γ ⊢ e₂ : A
    ───────────────
    Γ ⊢ e₁ e₂ : B
  -/
  -- Fixed: second premise uses A (argument type), not B (return type)
  | tapp {Γ A B : Typ} {e₁ e₂ : Exp}
    : HasType Γ e₁ (.arr A B)
    → HasType Γ e₂ A
    → HasType Γ (.app e₁ e₂) B
  /-
    Γ ⊢ e₁ : Γ₁
    Γ₁ ⊢ e₂ : A
    ────────────────
    Γ ⊢ e₁ ▷ e₂ : A
  -/
  | tbox {Γ Γ₁ A B : Typ} {e₁ e₂ : Exp}
    : HasType Γ e₁ Γ₁
    → HasType Γ₁ e₂ A
    → HasType Γ (.box e₁ e₂) A
  /-
    Γ ⊢ e₁ : A
    Γ & A ⊢ e₂ : B
    ────────────────────
    Γ ⊢ e₁ ,, e₂ : A & B
  -/
  | tmrg {Γ A B : Typ} {e₁ e₂ : Exp}
    : HasType Γ e₁ A
    → HasType (.and Γ A) e₂ B
    → HasType Γ (.mrg e₁ e₂) (.and A B)
  /-
    Γ & A ⊢ e : B
    ────────────────────
    Γ ⊢ λA. e : A → B
  -/
  | tlam {Γ A B : Typ} {e : Exp}
    : HasType (.and Γ A) e B
    → HasType Γ (.lam A e) (.arr A B)
  /-
    Γ ⊢ e : A
    lookup(A, n) = B
    ─────────────────
    Γ ⊢ e.n : B
  -/
  | tproj {Γ A B : Typ} {e : Exp} {n : Nat}
    : HasType Γ e A
    → Lookup A n B
    → HasType Γ (.proj e n) B
  /-
    value v
    () ⊢ v : Γ₁
    Γ₁ & A ⊢ e : B
    ─────────────────
    Γ ⊢ ⟨v, λA. e⟩ : A → B
  -/
  | tclos {Γ Γ₁ A B : Typ} {v e : Exp} {n : Nat}
    : Value v
    → HasType .top v Γ₁
    → HasType (.and Γ₁ A) e B
    → HasType Γ (.clos v A e) (.arr A B)
  /-
    Γ ⊢ e : A
    ─────────────────────
    Γ ⊢ {l = e} : {l : A}
  -/
  | trcd {Γ A : Typ} {l : String} {e : Exp}
    : HasType Γ e A
    → HasType Γ (.lrec l e) (.rcd l A)
  /-
    Γ ⊢ e : B
    rlookup(B, l) = A
    ───────────────
    Γ ⊢ e.l : A
  -/
  | trproj {Γ A B : Typ} {l : String} {e : Exp}
    : HasType Γ e B
    → RLookup B l A
    → HasType Γ (.rproj e l) A
