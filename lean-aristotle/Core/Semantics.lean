import Core.Syntax

open Core

namespace C_Sem
/--
  Positional lookup in merged values.
  `LookupV v n v'` means: in the merged value `v`,
  the component at index `n` is `v'`.

  Index 0 is the rightmost (most recently merged) component.
-/
inductive LookupV : Exp → Nat → Exp → Prop where
  /-
    ─────────────────────────
    lookupv(v₁ ,, v₂, 0) = v₂
  -/
  | lvzero {v₁ v₂ : Exp}
    : LookupV (.mrg v₁ v₂) 0 v₂
  /-
    lookupv(v₁, n) = v₃
    ──────────────────────────────────
    lookupv(v₁ ,, v₂, n + 1) = v₃
  -/
  | lvsucc {v₁ v₂ v₃ : Exp} {n : Nat}
    : LookupV v₁ n v₃
    → LookupV (.mrg v₁ v₂) (n + 1) v₃


/--
  Record-label lookup in merged values.
  `RLookupV v l v'` means: in the value `v`,
  the component with label `l` is `v'`.
-/
inductive RLookupV : Exp → String → Exp → Prop where
  /-
    ────────────────────────────
    rlookupv({l = e}, l) = e
  -/
  | rvlzero {l : String} {e : Exp}
    : RLookupV (.lrec l e) l e
  /-
    rlookupv(e₁, l) = e
    ─────────────────────────────
    rlookupv(e₁ ,, e₂, l) = e
  -/
  | vlandl {e₁ e₂ e : Exp} {l : String}
    : RLookupV e₁ l e
    → RLookupV (.mrg e₁ e₂) l e
  /-
    rlookupv(e₂, l) = e
    ─────────────────────────────
    rlookupv(e₁ ,, e₂, l) = e
  -/
  | vlandr {e₁ e₂ e : Exp} {l : String}
    : RLookupV e₂ l e
    → RLookupV (.mrg e₁ e₂) l e


/--
  `EBig env e v` means: under runtime environment `env`,
  expression `e` evaluates to value `v`.

  The environment is a *value* (not a list). It gets extended
  via merge and switched via box.
-/
inductive EBig : Exp → Exp → Exp → Prop where
  /-
    value v
    ─────────────
    v ⊢ i ⇓ i
  -/
  | eblit {v : Exp} {i : Nat}
    : Value v
    → EBig v (.lit i) (.lit i)
  /-
    value v
    ─────────────
    v ⊢ () ⇓ ()
  -/
  | ebunit {v : Exp}
    : Value v
    → EBig v .unit .unit
  /-
    v ⊢ e₁ ⇓ v₁
    (v ,, v₁) ⊢ e₂ ⇓ v₂
    ──────────────────────────────
    v ⊢ e₁ ,, e₂ ⇓ v₁ ,, v₂
  -/
  | ebmrg {v e₁ e₂ v₁ v₂ : Exp}
    : EBig v e₁ v₁
    → EBig (.mrg v v₁) e₂ v₂
    → EBig v (.mrg e₁ e₂) (.mrg v₁ v₂)
  /-
    value v
    ────────────────────
    v ⊢ λA. e ⇓ ⟨v, A, e⟩
  -/
  | ebclos {v : Exp} {A : Typ} {e : Exp}
    : Value v
    → EBig v (.lam A e) (.clos v A e)
  /-
    v ⊢ e₁ ⇓ ⟨v₂, A, e⟩
    v ⊢ e₂ ⇓ v₁
    (v₂ ,, v₁) ⊢ e ⇓ vr
    ──────────────────────────
    v ⊢ e₁ e₂ ⇓ vr
  -/
  | ebapp {v e₁ e₂ v₁ v₂ vr e : Exp} {A : Typ}
    : EBig v e₁ (.clos v₂ A e)
    → EBig v e₂ v₁
    → EBig (.mrg v₂ v₁) e vr
    → EBig v (.app e₁ e₂) vr
  /-
    v ⊢ e₁ ⇓ v₁
    v₁ ⊢ e₂ ⇓ vr
    ─────────────────────
    v ⊢ e₁ ▷ e₂ ⇓ vr
  -/
  | ebbox {v e₁ e₂ v₁ vr : Exp}
    : EBig v e₁ v₁
    → EBig v₁ e₂ vr
    → EBig v (.box e₁ e₂) vr
  /-
    value v
    value v₁
    ──────────────────────────
    v ⊢ ⟨v₁, A, e⟩ ⇓ ⟨v₁, A, e⟩
  -/
  | eclos {v v₁ : Exp} {A : Typ} {e : Exp}
    : Value v
    → Value v₁
    → EBig v (.clos v₁ A e) (.clos v₁ A e)
  /-
    value e
    ─────────────
    e ⊢ ? ⇓ e
  -/
  | equery {e : Exp}
    : Value e
    → EBig e .query e
  /-
    e ⊢ a ⇓ v
    lookupv(v, n) = v'
    ────────────────────
    e ⊢ a.n ⇓ v'
  -/
  | ebproj {e a v v' : Exp} {n : Nat}
    : EBig e a v
    → LookupV v n v'
    → EBig e (.proj a n) v'
  /-
    e ⊢ a ⇓ v
    ──────────────────────
    e ⊢ {l = a} ⇓ {l = v}
  -/
  | ebrec {e a v : Exp} {l : String}
    : EBig e a v
    → EBig e (.lrec l a) (.lrec l v)
  /-
    e ⊢ a ⇓ v₁
    rlookupv(v₁, l) = v₂
    ───────────────────────
    e ⊢ a.l ⇓ v₂
  -/
  | ebsel {e a v₁ v₂ : Exp} {l : String}
    : EBig e a v₁
    → RLookupV v₁ l v₂
    → EBig e (.rproj a l) v₂

end C_Sem
