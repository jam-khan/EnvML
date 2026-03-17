import LeanSce.Core.Syntax
import LeanSce.Core.Semantics
import LeanSce.Core.Typing
import LeanSce.SCE.Syntax
import LeanSce.SCE.Semantics
import LeanSce.Elaboration

open SCE

/-
  Environment-value typing: relates an SCE value to
  an SCE type and a Core value simultaneously.

  `ValTrans v A cv` means: SCE value `v` of type `A`
  translates to Core value `cv`.
-/
inductive ValTrans : SCE.Exp → SCE.Typ → Core.Exp → Prop where
  | vint {n}
    : ValTrans (.lit n) .int (.lit n)
  | vunit
    : ValTrans .unit .top .unit
  | vlrec {v A cv l}
    : ValTrans v A cv
    → ValTrans (.lrec l v) (.rcd l A) (.lrec l cv)
  | vmrg {v₁ v₂ A B cv₁ cv₂}
    : ValTrans v₁ A cv₁
    → ValTrans v₂ B cv₂
    → ValTrans (.mrg v₁ v₂) (.and A B) (.mrg cv₁ cv₂)
  | vnmrg {v₁ v₂ A B cv₁ cv₂}
    : ValTrans v₁ A cv₁
    → ValTrans v₂ B cv₂
    → ValTrans (.nmrg v₁ v₂) (.and A B) (.mrg cv₁ cv₂)
  | vclos {v A B body Γ' cv ce}
    : ValTrans v Γ' cv
    → elabExp (.and Γ' A) body B ce
    → ValTrans (.clos v A body) (.arr A B) (.clos cv (elabTyp A) ce)
  | vmclos {v A B body Γ' mt cv ce}
    : ValTrans v Γ' cv
    → elabExp (.and Γ' A) body B ce
    → ValTrans (.mclos v A body) (.sig mt) (.clos cv (elabTyp A) ce)

theorem type_elaboration_uniqueness
    {ST : SCE.Typ} {CT₁ CT₂ : Core.Typ}
    (h₁ : elabTyp ST = CT₁)
    (h₂ : elabTyp ST = CT₂)
    : CT₁ = CT₂ := by
  sorry

theorem type_safe_index_lookup
    {ST₁ ST₂ : SCE.Typ} {n : Nat}
    (h : SCE.IndexLookup ST₁ n ST₂)
    : Core.Lookup (elabTyp ST₁) n (elabTyp ST₂) := by
  sorry

theorem type_safe_label_existence
    {l : String} {ST : SCE.Typ}
    : SCE.LabelIn l ST ↔ Core.Lin l (elabTyp ST) := by
  sorry

theorem type_safe_label_nonexistence
    {l : String} {ST : SCE.Typ}
    : ¬ SCE.LabelIn l ST ↔ ¬ Core.Lin l (elabTyp ST) := by
  sorry

theorem type_safe_record_lookup
    {ST₁ ST₂ : SCE.Typ} {l : String}
    (h : SCE.RecordLookup ST₁ l ST₂)
    : Core.RLookup (elabTyp ST₁) l (elabTyp ST₂) := by
  sorry

theorem type_preservation
    {Γ A : SCE.Typ} {es : SCE.Exp} {ec : Core.Exp}
    (h : elabExp Γ es A ec)
    : HasType (elabTyp Γ) ec (elabTyp A) := by
  sorry

theorem index_lookup_uniqueness
    {T T₁ T₂ : SCE.Typ} {n : Nat}
    (h₁ : SCE.IndexLookup T n T₁)
    (h₂ : SCE.IndexLookup T n T₂)
    : T₁ = T₂ := by
  sorry

theorem record_lookup_uniqueness
    {T T₁ T₂ : SCE.Typ} {l : String}
    (h₁ : SCE.RecordLookup T l T₁)
    (h₂ : SCE.RecordLookup T l T₂)
    : T₁ = T₂ := by
  sorry

theorem inference_uniqueness
    {Γ T₁ T₂ : SCE.Typ} {e : SCE.Exp} {ce₁ ce₂ : Core.Exp}
    (h₁ : elabExp Γ e T₁ ce₁)
    (h₂ : elabExp Γ e T₂ ce₂)
    : T₁ = T₂ := by
  sorry

theorem elaboration_uniqueness
    {Γ T₁ T₂ : SCE.Typ} {e : SCE.Exp} {ce₁ ce₂ : Core.Exp}
    (h₁ : elabExp Γ e T₁ ce₁)
    (h₂ : elabExp Γ e T₂ ce₂)
    : ce₁ = ce₂ := by
  sorry

/--
  **Semantics Preservation.**
  ```
          SCE.BigStep ρˢ eˢ vˢ
    eˢ ──────────────────────────→ vˢ
     │                               │
     │ elab                          │ ⟦·⟧
     ↓                               ↓
    eᶜ ──────────────────────────→ ⟦vˢ⟧
          Core.EBig ⟦ρˢ⟧ eᶜ ⟦vˢ⟧
  ```

  If  Γ ⊢ es : A ⤳ ec
    ∧ ρs ⊢s es ⇓ vs
    ∧ ρs : Γ ↝ cρ
  then
    ∃ cv, vs : A ↝ cv  ∧  cρ ⊢c ec ⇓ cv

  where ⟦·⟧ is the value translation from SCE to Core.

  If `eˢ` elaborates to `eᶜ` under `Γ` and evaluates to `vˢ`
  under `ρˢ`, then `eᶜ` evaluates to `⟦vˢ⟧` under `⟦ρˢ⟧` in Core.
-/
theorem semantics_preservation
    {Γ A : SCE.Typ}
    {es : SCE.Exp} {ec : Core.Exp}
    {rs vs : SCE.Exp}
    {cr : Core.Exp}
    (helab : elabExp Γ es A ec)
    (heval : S_Sem.BigStep rs es vs)
    (henv  : ValTrans rs Γ cr)
    : ∃ cv, ValTrans vs A cv ∧ C_Sem.EBig cr ec cv := by
  sorry
