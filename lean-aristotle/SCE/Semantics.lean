import SCE.Syntax

open SCE

namespace S_Sem

/-!
  ## Value Index Lookup

  `LookupV v n v'` holds when projecting index `n` from
  a merge value `v` yields sub-value `v'`.

  This is the runtime counterpart of `IndexLookup` on types.
  Merge values form a right-biased cons-list:
  `v₁ ,, v₂` stores `v₂` at index 0 and recurses into `v₁`.

  Works uniformly over both dependent merges (`mrg`)
  and non-dependent merges (`nmrg`), since at runtime
  both are just pairs of values.
```
  lookupV (v₁ ,, v₂) 0     =  v₂
  lookupV (v₁ ,, v₂) (n+1) =  lookupV v₁ n
```
-/
inductive LookupV : Exp → Nat → Exp → Prop where
  | dmrg_zero {v₁ v₂ : Exp}
    : LookupV (.mrg v₁ v₂) 0 v₂
  | dmrg_succ {v₁ v₂ v' : Exp} {n : Nat}
    : LookupV v₁ n v'
    → LookupV (.mrg v₁ v₂) (n + 1) v'
  | nmrg_zero {v₁ v₂ : Exp}
    : LookupV (.nmrg v₁ v₂) 0 v₂
  | nmrg_succ {v₁ v₂ v' : Exp} {n : Nat}
    : LookupV v₁ n v'
    → LookupV (.nmrg v₁ v₂) (n + 1) v'

/-!
  ## Record Selection

  `Sel v l v'` holds when selecting label `l` from value `v`
  yields sub-value `v'`.

  This is the runtime counterpart of `RecordLookup` on types.
  Selection searches through records and merges for the label.

  Unlike `RecordLookup` which carries explicit `LabelIn` / `¬LabelIn`
  witnesses for disjointness, `Sel` does **not** enforce uniqueness
  by construction. Instead, determinism is a **theorem** proved
  using the typing derivation:
```
  sel_unique :
    HasType Γ v B → RecordLookup B l A →
    Sel v l v₁ → Sel v l v₂ → v₁ = v₂
```
  The typing guarantees that labels are unambiguous, so both
  `dmrg_left` and `dmrg_right` cannot both fire for a well-typed
  value. This keeps the operational semantics simple — it finds
  the label without re-checking disjointness.
```
  sel {l = v}      l  =  v
  sel (v₁ ,, v₂)  l  =  sel v₁ l  ∨  sel v₂ l
```
-/
inductive Sel : Exp → String → Exp → Prop where
  /-  Direct record match: `sel {l = v} l = v` -/
  | rcd {l : String} {v : Exp}
    : Sel (.lrec l v) l v
  /-  Found on the left side of a dependent merge. -/
  | dmrg_left {v₁ v₂ v' : Exp} {l : String}
    : Sel v₁ l v'
    → Sel (.mrg v₁ v₂) l v'
  /-  Found on the right side of a dependent merge. -/
  | dmrg_right {v₁ v₂ v' : Exp} {l : String}
    : Sel v₂ l v'
    → Sel (.mrg v₁ v₂) l v'
  /-  Found on the left side of a non-dependent merge. -/
  | nmrg_left {v₁ v₂ v' : Exp} {l : String}
    : Sel v₁ l v'
    → Sel (.nmrg v₁ v₂) l v'
  /-  Found on the right side of a non-dependent merge. -/
  | nmrg_right {v₁ v₂ v' : Exp} {l : String}
    : Sel v₂ l v'
    → Sel (.nmrg v₁ v₂) l v'

/-!
  ## Big-Step Semantics

  `BigStep ρ e v` holds when expression `e` evaluates to
  value `v` under environment `ρ`.

  Written `ρ ⊢ e ⇓ v` on paper.

  ### Environment model

  Environments are values — specifically, nested merge values
  that mirror the typing context structure. The environment `ρ`
  is passed explicitly and accessed via `query` (reification).
  Closures capture the environment at their creation point.

  ### Key invariants

  - Every rule produces a `Value` (proved separately as
    a theorem, not enforced by the inductive definition)
  - `mrg` is **dependent**: `e₂` evaluates under `ρ ,, v₁`
  - `nmrg` is **non-dependent**: `e₂` evaluates under `ρ`
  - Module constructs (`mstruct`, `mfunctor`, `mlink`)
    reduce to the same value-level constructs (`box`, `clos`, `app`)
    mirroring how they elaborate to core

  ### Correspondence with elaboration

  Each big-step rule corresponds to an elaboration rule.
  Semantics preservation states that if
  `Γ ⊢ eˢ : A ⤳ eᶜ` and `ρ ⊢ˢ eˢ ⇓ vˢ`,
  then `⟦ρ⟧ ⊢ᶜ eᶜ ⇓ ⟦vˢ⟧`.
-/
inductive BigStep : Exp → Exp → Exp → Prop where
  /-
    ─────────────
    ρ ⊢ ? ⇓ ρ
  -/
  | query {ρ : Exp}
    : Value ρ
    → BigStep ρ .query ρ

  /-
    ─────────────────
    ρ ⊢ n ⇓ n
  -/
  | lit {ρ : Exp} {n : Nat}
    : Value ρ
    → BigStep ρ (.lit n) (.lit n)
  /-
    ─────────────────
    ρ ⊢ () ⇓ ()
  -/
  | unit {ρ : Exp}
    : Value ρ
    → BigStep ρ .unit .unit
  /-
    Value v
    ──────────────────────────────
    ρ ⊢ ⟨v, A, body⟩ ⇓ ⟨v, A, body⟩
  -/
  | clos_val {ρ v : Exp} {A : Typ} {body : Exp}
    : Value ρ
    → Value v
    → BigStep ρ (.clos v A body) (.clos v A body)
  /-
    Value v
    ──────────────────────────────────
    ρ ⊢ mclos(v, A, body) ⇓ mclos(v, A, body)
  -/
  | mclos_val {ρ v : Exp} {A : Typ} {body : Exp}
    : Value ρ
    → Value v
    → BigStep ρ (.mclos v A body) (.mclos v A body)
  /-
    ρ ⊢ e ⇓ v       lookupV(v, n) = v'
    ────────────────────────────────────
    ρ ⊢ e.n ⇓ v'
  -/
  | proj {ρ e v v' : Exp} {n : Nat}
    : Value ρ
    → BigStep ρ e v
    → LookupV v n v'
    → BigStep ρ (.proj e n) v'
  /-
    ──────────────────────────────
    ρ ⊢ λ A. body ⇓ ⟨ρ, A, body⟩
  -/
  | lam {ρ : Exp} {A : Typ} {body : Exp}
    : Value ρ
    → BigStep ρ (.lam A body) (.clos ρ A body)
  /-
    ρ ⊢ e₁ ⇓ v₁       v₁ ⊢ e₂ ⇓ v
    ──────────────────────────────────
    ρ ⊢ e₁ |> e₂ ⇓ v
  -/
  | box {ρ e₁ e₂ v₁ v : Exp}
    : Value ρ
    → BigStep ρ e₁ v₁
    → BigStep v₁ e₂ v
    → BigStep ρ (.box e₁ e₂) v
  /-
    ρ ⊢ e₁ ⇓ ⟨v₁, _, body⟩       ρ ⊢ e₂ ⇓ v₂
    v₁ ,, v₂ ⊢ body ⇓ v
    ──────────────────────────────────────────────
    ρ ⊢ e₁ e₂ ⇓ v
  -/
  | app_clos {ρ e₁ e₂ v₁ v₂ v : Exp} {A : Typ} {body : Exp}
    : Value ρ
    → BigStep ρ e₁ (.clos v₁ A body)
    → BigStep ρ e₂ v₂
    → BigStep (.mrg v₁ v₂) body v
    → BigStep ρ (.app e₁ e₂) v
  /-
    ρ ⊢ e₁ ⇓ mclos(v₁, _, body)       ρ ⊢ e₂ ⇓ v₂
    v₁ ,, v₂ ⊢ body ⇓ v
    ──────────────────────────────────────────────────
    ρ ⊢ e₁ e₂ ⇓ v
  -/
  | app_mclos {ρ e₁ e₂ v₁ v₂ v : Exp} {A : Typ} {body : Exp}
    : Value ρ
    → BigStep ρ e₁ (.mclos v₁ A body)
    → BigStep ρ e₂ v₂
    → BigStep (.mrg v₁ v₂) body v
    → BigStep ρ (.app e₁ e₂) v
  /-
    ρ ⊢ e₁ ⇓ v₁       ρ ,, v₁ ⊢ e₂ ⇓ v₂
    ────────────────────────────────────────
    ρ ⊢ e₁ #d e₂ ⇓ v₁ ,, v₂
  -/
  | dmrg {ρ e₁ e₂ v₁ v₂ : Exp}
    : Value ρ
    → BigStep ρ e₁ v₁
    → BigStep (.mrg ρ v₁) e₂ v₂
    → BigStep ρ (.mrg e₁ e₂) (.mrg v₁ v₂)
  /-
    ρ ⊢ e₁ ⇓ v₁       ρ ⊢ e₂ ⇓ v₂
    ──────────────────────────────────
    ρ ⊢ e₁ #n e₂ ⇓ v₁ ,,ₙ v₂
  -/
  | nmrg {ρ e₁ e₂ v₁ v₂ : Exp}
    : Value ρ
    → BigStep ρ e₁ v₁
    → BigStep ρ e₂ v₂
    → BigStep ρ (.nmrg e₁ e₂) (.nmrg v₁ v₂)
  /-
    ρ ⊢ e ⇓ v
    ──────────────────────────
    ρ ⊢ {l = e} ⇓ {l = v}
  -/
  | lrec {ρ e v : Exp} {l : String}
    : Value ρ
    → BigStep ρ e v
    → BigStep ρ (.lrec l e) (.lrec l v)
  /-
    ρ ⊢ e ⇓ v       sel(v, l) = v'
    ────────────────────────────────
    ρ ⊢ e.l ⇓ v'
  -/
  | rproj {ρ e v v' : Exp} {l : String}
    : Value ρ
    → BigStep ρ e v
    → Sel v l v'
    → BigStep ρ (.rproj e l) v'
  /-
    ρ ⊢ e₁ ⇓ v₁       ρ ,, v₁ ⊢ e₂ ⇓ v
    ──────────────────────────────────────
    ρ ⊢ let e₁ : A in e₂ ⇓ v
  -/
  | letb {ρ e₁ e₂ v₁ v : Exp} {A : Typ}
    : Value ρ
    → BigStep ρ e₁ v₁
    → BigStep (.mrg ρ v₁) e₂ v
    → BigStep ρ (.letb e₁ A e₂) v
  /-
    ρ ⊢ e₁ ⇓ {l = v'}       ρ ,, v' ⊢ e₂ ⇓ v
    ─────────────────────────────────────────────
    ρ ⊢ open e₁ in e₂ ⇓ v
  -/
  | openm {ρ e₁ e₂ v' v : Exp} {l : String}
    : Value ρ
    → BigStep ρ e₁ (.lrec l v')
    → BigStep (.mrg ρ v') e₂ v
    → BigStep ρ (.openm e₁ e₂) v
  /-
    () ⊢ body ⇓ v
    ──────────────────────────────────────────
    ρ ⊢ struct[sandboxed] body ⇓ v
  -/
  | mstruct_sandboxed {ρ body v : Exp}
    : Value ρ
    → BigStep .unit body v
    → BigStep ρ (.mstruct .sandboxed body) v
  /-
    ρ ⊢ body ⇓ v
    ──────────────────────────────────────
    ρ ⊢ struct[open] body ⇓ v
  -/
  | mstruct_open {ρ body v : Exp}
    : Value ρ
    → BigStep ρ body v
    → BigStep ρ (.mstruct .open_ body) v
  /-
    ──────────────────────────────────────────────────────
    ρ ⊢ functor[sandboxed](A) body ⇓ mclos((), A, body)
  -/
  | mfunctor_sandboxed {ρ : Exp} {A : Typ} {body : Exp}
    : Value ρ
    → BigStep ρ (.mfunctor .sandboxed A body) (.mclos .unit A body)
  /-
    ──────────────────────────────────────────────────
    ρ ⊢ functor[open](A) body ⇓ mclos(ρ, A, body)
  -/
  | mfunctor_open {ρ : Exp} {A : Typ} {body : Exp}
    : Value ρ
    → BigStep ρ (.mfunctor .open_ A body) (.mclos ρ A body)
  /-
    ρ ⊢ e₁ ⇓ mclos(v₁, _, body)       ρ ⊢ e₂ ⇓ v₂
    v₁ ,, v₂ ⊢ body ⇓ v
    ──────────────────────────────────────────────────
    ρ ⊢ mapp(e₁, e₂) ⇓ v
  -/
  | mapp {ρ e₁ e₂ v₁ v₂ v : Exp} {A : Typ} {body : Exp}
    : Value ρ
    → BigStep ρ e₁ (.mclos v₁ A body)
    → BigStep ρ e₂ v₂
    → BigStep (.mrg v₁ v₂) body v
    → BigStep ρ (.mlink e₁ e₂) v
  /-
    ρ ⊢ e₁ ⇓ mclos(v₁, _, body)       ρ ⊢ e₂ ⇓ v₂
    v₁ ,, v₂ ⊢ body ⇓ v
    ──────────────────────────────────────────────────
    ρ ⊢ link(e₁, e₂) ⇓ v₂ ,, v
  -/
  | mlink {ρ e₁ e₂ v₁ v₂ v : Exp} {A : Typ} {body : Exp}
    : Value ρ
    → BigStep ρ e₁ (.mclos v₁ A body)
    → BigStep ρ e₂ v₂
    → BigStep (.mrg v₁ v₂) body v
    → BigStep ρ (.mlink e₁ e₂) (.mrg v₂ v)

end S_Sem
