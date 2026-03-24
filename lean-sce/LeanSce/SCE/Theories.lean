import LeanSce.Core.Syntax
import LeanSce.Core.BigStep
import LeanSce.Core.Typing
import LeanSce.SCE.Syntax
import LeanSce.SCE.Semantics
import LeanSce.SCE.Elaboration

open SCE Core

theorem index_lookup_uniqueness
    {T T₁ T₂ : SCE.Typ} {n : Nat}
    (h₁ : SLookup T n T₁)
    (h₂ : SLookup T n T₂)
    : T₁ = T₂ := by
  induction h₁ with
  | zero A B => cases h₂; rfl
  | succ A B n C _ ih => cases h₂ with | succ _ _ _ _ h₂ => exact ih h₂

theorem record_lookup_uniqueness
    {T T₁ T₂ : SCE.Typ} {l : String}
    (h₁ : SCE.SRLookup T l T₁)
    (h₂ : SCE.SRLookup T l T₂)
    : T₁ = T₂ := by sorry

theorem type_safe_index_lookup
    {ST₁ ST₂ : SCE.Typ} {n : Nat}
    (h : SLookup ST₁ n ST₂)
    : Core.Lookup (elabTyp ST₁) n (elabTyp ST₂) := by
  induction h with
  | zero A B => exact Core.Lookup.zero
  | succ A B n C _ ih => exact Core.Lookup.succ ih

theorem type_safe_label_existence
    {l : String} {ST : SCE.Typ}
    : SCE.LabelIn l ST ↔ Core.Lin l (elabTyp ST) := by sorry

theorem type_safe_label_nonexistence
    {l : String} {ST : SCE.Typ}
    : ¬ SCE.LabelIn l ST ↔ ¬ Core.Lin l (elabTyp ST) := by
  constructor
  · intro hns hc; exact hns (type_safe_label_existence.mpr hc)
  · intro hnc hs; exact hnc (type_safe_label_existence.mp hs)

theorem type_safe_record_lookup
    {ST₁ ST₂ : SCE.Typ} {l : String}
    (h : SCE.SRLookup ST₁ l ST₂)
    : Core.RLookup (elabTyp ST₁) l (elabTyp ST₂) := by sorry

/-- Same source expression in same context yields same type -/
theorem inference_uniqueness
    {Γ T₁ T₂ : SCE.Typ} {e : SCE.Exp} {ce₁ ce₂ : Core.Exp}
    (h₁ : elabExp Γ e T₁ ce₁)
    (h₂ : elabExp Γ e T₂ ce₂)
    : T₁ = T₂ := by sorry

/-- Same source expression in same context yields same core expression -/
theorem elaboration_uniqueness
    {Γ T₁ T₂ : SCE.Typ} {e : SCE.Exp} {ce₁ ce₂ : Core.Exp}
    (h₁ : elabExp Γ e T₁ ce₁)
    (h₂ : elabExp Γ e T₂ ce₂)
    : ce₁ = ce₂ := by sorry

/-- Elaborated core expression is well-typed in core -/
theorem type_preservation
    {Γ A : SCE.Typ} {es : SCE.Exp} {ec : Core.Exp}
    (h : elabExp Γ es A ec)
    : HasType (elabTyp Γ) ec (elabTyp A) := by sorry

-- ============================================
-- Values elaborate to values
-- ============================================

/-- If a source value elaborates, the core result is a core value -/
theorem elab_value
    {Γ A : SCE.Typ} {v : SCE.Exp} {cv : Core.Exp}
    (helab : elabExp Γ v A cv)
    (hval : SCE.Value v)
    : Core.Value cv := by sorry

/--
  If es elaborates to ec, and es evaluates to vs under ρs,
  and ρs elaborates to ρc, then ec evaluates to some vc
  under ρc, and vs elaborates to vc.
-/
theorem semantic_preservation
    {Γ A : SCE.Typ} {es : SCE.Exp} {ec : Core.Exp}
    {ρs vs : SCE.Exp} {ρc : Core.Exp}
    (helab : elabExp Γ es A ec)
    (heval : S_Sem.BStep ρs es vs)
    (henv : elabExp SCE.Typ.top ρs Γ ρc)
    (henv_val : SCE.Value ρs)
    : ∃ vc, EBig ρc ec vc ∧ elabExp SCE.Typ.top vs A vc := by sorry

/--
  A closed well-elaborated program evaluates
  consistently across source and core.
-/
theorem whole_program_correctness
    {A : SCE.Typ} {es : SCE.Exp} {ec : Core.Exp} {vs : SCE.Exp}
    (helab : elabExp SCE.Typ.top es A ec)
    (heval : S_Sem.BStep .unit es vs)
    : ∃ vc, EBig .unit ec vc ∧ elabExp SCE.Typ.top vs A vc := by
  exact semantic_preservation helab heval (elabExp.eunit SCE.Typ.top) SCE.Value.vunit

-- Linking and separate compilation

def linkSCE (e₁ e₂ : SCE.Exp) : SCE.Exp :=
  .mlink e₁ e₂

def linkCore (e₁ e₂ : Core.Exp) : Core.Exp :=
  .mrg e₁ (.app e₂ e₁)

/--
  Separate compilation: compiling components separately
  then linking in core preserves the behavior of
  linking in source then evaluating.
-/
theorem separate_compilation
    {Γ A : SCE.Typ} {mt : SCE.ModTyp}
    {es₁ es₂ : SCE.Exp} {ec₁ ec₂ : Core.Exp}
    {ρs vs : SCE.Exp} {ρc : Core.Exp}
    (helab₁ : elabExp Γ es₁ A ec₁)
    (helab₂ : elabExp Γ es₂ (SCE.Typ.sig (SCE.ModTyp.TyArrM A mt)) ec₂)
    (heval : S_Sem.BStep ρs (linkSCE es₁ es₂) vs)
    (henv : elabExp SCE.Typ.top ρs Γ ρc)
    (henv_val : SCE.Value ρs)
    : ∃ vc, EBig ρc (linkCore ec₁ ec₂) vc
           ∧ elabExp SCE.Typ.top vs (.and A (.sig mt)) vc := by
  have hmlink : elabExp Γ (linkSCE es₁ es₂) (.and A (.sig mt))
      (linkCore ec₁ ec₂) :=
    elabExp.mlink Γ A mt es₁ es₂ ec₁ ec₂ helab₁ helab₂
  exact semantic_preservation hmlink heval henv henv_val
