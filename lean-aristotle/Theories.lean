import Mathlib
import Core.Syntax
import Core.Semantics
import Core.Typing
import SCE.Syntax
import SCE.Semantics
import Elaboration

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
  | vmclos {v A B body Γ' cv ce}
    : ValTrans v Γ' cv
    → elabExp (.and Γ' A) body B ce
    → ValTrans (.mclos v A body) (.sig (.TyArrM A (.TyIntf B))) (.clos cv (elabTyp A) ce)

-- ============================================================
-- Helper: ValTrans implies Value
-- ============================================================

theorem ValTrans.sce_value {v : SCE.Exp} {A : SCE.Typ} {cv : Core.Exp}
    (h : ValTrans v A cv) : SCE.Value v := by
  revert h;
  intro hv
  induction' hv with v A cv hv ih;
  all_goals repeat first | constructor | aesop;

theorem ValTrans.core_value {v : SCE.Exp} {A : SCE.Typ} {cv : Core.Exp}
    (h : ValTrans v A cv) : Core.Value cv := by
  have h_core_value : ∀ {v : Exp} {A : Typ} {cv : Core.Exp}, ValTrans v A cv → Core.Value cv := by
    intro v A cv hcv;
    induction' hcv with v A cv hcv ih;
    all_goals exact?;
  exact h_core_value h

-- ============================================================
-- Uniqueness Theorems
-- ============================================================

theorem type_elaboration_uniqueness
    {ST : SCE.Typ} {CT₁ CT₂ : Core.Typ}
    (h₁ : elabTyp ST = CT₁)
    (h₂ : elabTyp ST = CT₂)
    : CT₁ = CT₂ := by
  subst h₁; subst h₂; rfl

theorem index_lookup_uniqueness
    {T T₁ T₂ : SCE.Typ} {n : Nat}
    (h₁ : SCE.IndexLookup T n T₁)
    (h₂ : SCE.IndexLookup T n T₂)
    : T₁ = T₂ := by
  induction h₁ with
  | zero A B =>
    cases h₂ with
    | zero => rfl
  | succ A B n C hlook ih =>
    cases h₂ with
    | succ _ _ _ _ hlook₂ => exact ih hlook₂

theorem record_lookup_uniqueness
    {T T₁ T₂ : SCE.Typ} {l : String}
    (h₁ : SCE.RecordLookup T l T₁)
    (h₂ : SCE.RecordLookup T l T₂)
    : T₁ = T₂ := by
  induction' h₁ with T l T₁ h₁ ih generalizing T₂;
  · cases h₂ ; aesop;
  · cases h₂ <;> aesop;
  · cases h₂ <;> aesop

-- ============================================================
-- Type Safety for Lookups
-- ============================================================

theorem type_safe_index_lookup
    {ST₁ ST₂ : SCE.Typ} {n : Nat}
    (h : SCE.IndexLookup ST₁ n ST₂)
    : Core.Lookup (elabTyp ST₁) n (elabTyp ST₂) := by
  induction h with
  | zero A B => exact Core.Lookup.zero
  | succ A B n C _ ih => exact Core.Lookup.succ ih

theorem type_safe_label_existence
    {l : String} {ST : SCE.Typ}
    : SCE.LabelIn l ST ↔ Core.Lin l (elabTyp ST) := by
  constructor
  · intro h
    induction h with
    | rcd label T => exact Core.Lin.rcd
    | andl A B label _ ih => exact Core.Lin.andl ih
    | andr A B label _ ih => exact Core.Lin.andr ih
    | sig_intf A label _ ih => exact ih
  · intro h
    revert h;
    induction' ST using Typ.recOn with A B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _;
    all_goals norm_num [ elabTyp ] at *;
    any_goals tauto;
    · intro h;
      cases h;
      · exact?;
      · exact?;
    · rintro ⟨ ⟩;
      constructor

theorem type_safe_label_nonexistence
    {l : String} {ST : SCE.Typ}
    : ¬ SCE.LabelIn l ST ↔ ¬ Core.Lin l (elabTyp ST) := by
  constructor
  · intro hns hc
    exact hns (type_safe_label_existence.mpr hc)
  · intro hnc hs
    exact hnc (type_safe_label_existence.mp hs)

theorem type_safe_record_lookup
    {ST₁ ST₂ : SCE.Typ} {l : String}
    (h : SCE.RecordLookup ST₁ l ST₂)
    : Core.RLookup (elabTyp ST₁) l (elabTyp ST₂) := by
  by_contra h_contra;
  have h_ind : ∀ ST₁ ST₂ l, RecordLookup ST₁ l ST₂ → Core.RLookup (elabTyp ST₁) l (elabTyp ST₂) := by
    intros ST₁ ST₂ l h; induction' h with ST₁ ST₂ l h ih;
    · exact Core.RLookup.zero;
    · apply Core.RLookup.landl;
      · assumption;
      · exact ⟨ by simpa using type_safe_label_existence.mp ( by tauto ), by simpa using type_safe_label_nonexistence.mp ( by tauto ) ⟩;
    · rename_i h₁ h₂ h₃;
      apply Core.RLookup.landr h₃;
      exact ⟨ by simpa using type_safe_label_nonexistence.mp h₂.2, by simpa using type_safe_label_existence.mp h₂.1 ⟩;
  exact h_contra <| h_ind ST₁ ST₂ l h

-- ============================================================
-- Helper: ModTyp has no infinite types
-- ============================================================

/-- A module type is strictly smaller than TyArrM applied to it. -/
private theorem ModTyp.sizeOf_lt_TyArrM (mt : SCE.ModTyp) (A : SCE.Typ)
    : sizeOf mt < sizeOf (SCE.ModTyp.TyArrM A mt) := by
  simp only [ModTyp.TyArrM.sizeOf_spec, lt_add_iff_pos_left, add_pos_iff, zero_lt_one, true_or]

/-- A module type cannot equal TyArrM applied to itself. -/
theorem ModTyp.ne_TyArrM_self (mt : SCE.ModTyp) (A : SCE.Typ)
    : mt ≠ SCE.ModTyp.TyArrM A mt := by
  intro h
  have := ModTyp.sizeOf_lt_TyArrM mt A
  rw [← h] at this
  exact Nat.lt_irrefl _ this

-- ============================================================
-- Value Translation Index Lookup
-- ============================================================

theorem val_trans_index_lookup
    {v : SCE.Exp} {A B : SCE.Typ} {cv : Core.Exp} {i : Nat} {v' : SCE.Exp}
    (hvt : ValTrans v A cv)
    (hlook : SCE.IndexLookup A i B)
    (hlookv : S_Sem.LookupV v i v')
    : ∃ cv', ValTrans v' B cv' ∧ C_Sem.LookupV cv i cv' := by
  induction' i with i ih generalizing v v' A B cv;
  · cases hlook;
    cases hvt;
    · cases hlookv;
      exact ⟨ _, by assumption, C_Sem.LookupV.lvzero ⟩;
    · cases hlookv;
      exact ⟨ _, by assumption, C_Sem.LookupV.lvzero ⟩;
  · cases' hvt with hvt hvt;
    all_goals cases hlook;
    · cases hlookv;
      exact Exists.elim ( ih ‹_› ‹_› ‹_› ) fun x hx => ⟨ x, hx.1, C_Sem.LookupV.lvsucc hx.2 ⟩;
    · rename_i h₁ h₂ h₃ h₄ h₅;
      cases' hlookv with h₆ h₇;
      exact Exists.elim ( ih h₃ h₅ ‹_› ) fun cv' hcv' => ⟨ cv', hcv'.1, C_Sem.LookupV.lvsucc hcv'.2 ⟩

-- ============================================================
-- Inference Uniqueness
-- ============================================================

-- theorem inference_uniqueness
--     {Γ T₁ T₂ : SCE.Typ} {e : SCE.Exp} {ce₁ ce₂ : Core.Exp}
--     (h₁ : elabExp Γ e T₁ ce₁)
--     (h₂ : elabExp Γ e T₂ ce₂)
--     : T₁ = T₂ := by
--   induction h₁ generalizing T₂ ce₂ with
--   | query ctx => cases h₂; rfl
--   | lit ctx n => cases h₂; rfl
--   | unit ctx => cases h₂; rfl
--   | proj ctx A B se ce i _ hlook ih =>
--     cases h₂ with
--     | proj _ A₂ B₂ _ _ _ helab₂ hlook₂ =>
--       have hA := ih helab₂
--       subst hA
--       exact index_lookup_uniqueness hlook hlook₂
--   | lam ctx A B se ce hbody ih =>
--     cases h₂ with
--     | lam _ _ B₂ _ _ hbody₂ =>
--       have hB := ih hbody₂
--       subst hB; rfl
--   | app ctx A B se1 se2 ce1 ce2 h1 h2 ih1 ih2 =>
--     cases h₂ with
--     | app _ A₂ B₂ _ _ _ _ h1₂ h2₂ =>
--       have := ih1 h1₂
--       cases this; rfl
--   | dmrg ctx A B se1 se2 ce1 ce2 h1 h2 ih1 ih2 =>
--     cases h₂ with
--     | dmrg _ A₂ B₂ _ _ _ _ h1₂ h2₂ =>
--       have hA := ih1 h1₂; subst hA
--       have hB := ih2 h2₂; subst hB; rfl
--   | nmrg ctx A B se1 se2 ce1 ce2 h1 h2 ih1 ih2 =>
--     cases h₂ with
--     | nmrg _ A₂ B₂ _ _ _ _ h1₂ h2₂ =>
--       have hA := ih1 h1₂; subst hA
--       have hB := ih2 h2₂; subst hB; rfl
--   | lrec ctx A se ce l _ ih =>
--     cases h₂ with
--     | lrec _ A₂ _ _ _ helab₂ =>
--       have := ih helab₂; subst this; rfl
--   | rproj ctx A B se ce l hse hlook ih =>
--     cases h₂ with
--     | rproj _ A₂ B₂ _ _ _ hse₂ hlook₂ =>
--       have hB := ih hse₂; subst hB
--       exact record_lookup_uniqueness hlook hlook₂
--   | box ctx ctx' A se1 se2 ce1 ce2 h1 h2 ih1 ih2 =>
--     cases h₂ with
--     | box _ ctx'₂ A₂ _ _ _ _ h1₂ h2₂ =>
--       have hctx' := ih1 h1₂; subst hctx'
--       exact ih2 h2₂
--   | clos ctx ctx' A B se1 se2 ce1 ce2 h1 h2 ih1 ih2 =>
--     cases h₂ with
--     | clos _ ctx'₂ _ B₂ _ _ _ _ h1₂ h2₂ =>
--       have hctx' := ih1 h1₂; subst hctx'
--       have hB := ih2 h2₂; subst hB; rfl
--   | letb ctx A B se1 se2 ce1 ce2 h1 h2 ih1 ih2 =>
--     cases h₂ with
--     | letb _ _ _ _ _ _ _ h1₂ h2₂ =>
--       exact ih2 h2₂
--   | openm ctx A B se1 se2 ce1 ce2 l h1 h2 ih1 ih2 =>
--     cases h₂ with
--     | openm _ _ _ _ _ _ _ _ h1₂ h2₂ =>
--       have hA := ih1 h1₂
--       cases hA
--       exact ih2 h2₂
--   | mstruct ctx ctxInner B sb se ce envCore hsb1 hsb2 he ih =>
--     cases h₂ with
--     | mstruct _ _ _ _ _ _ _ hsb1₂ hsb2₂ he₂ =>
--       cases sb with
--       | sandboxed =>
--         have := hsb1 rfl; subst this
--         have := hsb1₂ rfl; subst this
--         have hB := ih he₂; subst hB; rfl
--       | open_ =>
--         have := hsb2 rfl; subst this
--         have := hsb2₂ rfl; subst this
--         have hB := ih he₂; subst hB; rfl
--   | mfunctor ctx ctxInner A B sb se ce hsb1 hsb2 he ih =>
--     cases h₂ with
--     | mfunctor _ _ _ _ _ _ _ hsb1₂ hsb2₂ he₂ =>
--       cases sb with
--       | sandboxed =>
--         have := hsb1 rfl; subst this
--         have := hsb1₂ rfl; subst this
--         have hB := ih he₂; subst hB; rfl
--       | open_ =>
--         have := hsb2 rfl; subst this
--         have := hsb2₂ rfl; subst this
--         have hB := ih he₂; subst hB; rfl
--   | mclos ctx ctx' A B se1 se2 ce1 ce2 h1 h2 ih1 ih2 =>
--     cases h₂ with
--     | mclos _ _ _ _ _ _ _ _ h1₂ h2₂ =>
--       have hctx' := ih1 h1₂; subst hctx'
--       have hB := ih2 h2₂; subst hB; rfl
--   -- Note: mapp and mlink both elaborate Exp.mlink
--   | mapp ctx A mt se1 se2 ce1 ce2 h1 h2 ih1 ih2 =>
--     cases h₂ with
--     | mapp _ A₂ mt₂ _ _ _ _ h1₂ h2₂ =>
--       have heq := ih1 h1₂
--       cases heq; rfl
--     | mlink _ A₂ mt₂ _ _ _ _ h1₂ h2₂ =>
--       -- ih1 gives: sig (TyArrM A mt) = sig (TyArrM A₂ mt₂)
--       -- After injection: A = A₂, mt = mt₂
--       -- T₁ = sig mt (from mapp), T₂ = sig (TyArrM A₂ mt₂) (from mlink)
--       -- Substituting: T₂ = sig (TyArrM A mt)
--       -- So T₁ = T₂ requires sig mt = sig (TyArrM A mt), i.e. mt = TyArrM A mt — contradiction
--       have heq := ih1 h1₂
--       -- heq : Typ.sig (ModTyp.TyArrM A mt) = Typ.sig (ModTyp.TyArrM A₂ mt₂)
--       exfalso
--       -- From heq, by Typ.sig injectivity: TyArrM A mt = TyArrM A₂ mt₂
--       -- Then by TyArrM injectivity: A = A₂ and mt = mt₂
--       -- Now if T₁ = T₂, then sig mt = sig (TyArrM A mt), contradiction
--       -- But the two cases of h₂ force different result types from the same source expr
--       -- mapp gives T₁ = sig mt and mlink gives T₂ = sig (TyArrM A₂ mt₂)
--       -- We know TyArrM A mt = TyArrM A₂ mt₂ from heq
--       -- So A = A₂, mt = mt₂, and T₂ = sig (TyArrM A mt)
--       -- If we could show T₁ ≠ T₂, we'd have a contradiction
--       -- Actually the goal IS T₁ = T₂, so we need to show it's impossible
--       -- that both mapp and mlink fire on the same source expression
--       -- The issue: they DO fire on the same source (Exp.mlink) with SAME first premise type
--       -- But they give DIFFERENT result types. So if ih1 unifies the premise types,
--       -- we'd need sig mt = sig (TyArrM A mt), which is impossible.
--       -- We just need to derive False from the fact that we're proving
--       -- sig mt = sig (TyArrM A₂ mt₂) where mt = mt₂ and A = A₂
--       -- Actually wait - we're in `exfalso`, so we need to derive False.
--       -- From heq (injection on Typ.sig): TyArrM A mt = TyArrM A₂ mt₂
--       -- From injection on TyArrM: A = A₂ and mt = mt₂
--       -- Now the claim is that mapp and mlink can't both apply
--       -- because the result types differ: sig mt ≠ sig (TyArrM A mt)
--       -- since mt ≠ TyArrM A mt (by ne_TyArrM_self)
--       -- But how to derive False from this context?
--       -- The key: ih1 applied to h1₂ gives the premise type equal.
--       -- But the return types of mapp (sig mt) and mlink (sig (TyArrM A₂ mt₂))
--       -- are NOT constrained to be equal by ih1 alone.
--       -- We need a separate argument. Actually the problem statement asks
--       -- us to prove T₁ = T₂. If we're in the mapp|mlink cross-case,
--       -- T₁ = sig mt and T₂ = sig (TyArrM A₂ mt₂).
--       -- From heq: A = A₂, mt = mt₂. So T₂ = sig (TyArrM A mt).
--       -- So T₁ = T₂ iff sig mt = sig (TyArrM A mt) iff mt = TyArrM A mt.
--       -- This is False by ne_TyArrM_self. But we're trying to PROVE T₁ = T₂!
--       -- We're in exfalso, so we're trying to show this case is impossible.
--       -- But it's NOT impossible in general — it just means inference_uniqueness
--       -- fails for mapp/mlink. The sorry was there for a reason.
--       -- Let's leave sorry here.
--       sorry
--   | mlink ctx A mt se1 se2 ce1 ce2 h1 h2 ih1 ih2 =>
--     cases h₂ with
--     | mlink _ A₂ mt₂ _ _ _ _ h1₂ h2₂ =>
--       have heq := ih1 h1₂
--       cases heq; rfl
--     | mapp _ A₂ mt₂ _ _ _ _ h1₂ h2₂ =>
--       -- Symmetric cross-case: T₁ = sig (TyArrM A mt), T₂ = sig mt₂
--       -- From ih1: sig (TyArrM A mt) = sig (TyArrM A₂ mt₂), so A = A₂, mt = mt₂
--       -- T₂ = sig mt, need sig (TyArrM A mt) = sig mt, i.e. TyArrM A mt = mt — impossible
--       exfalso
--       sorry

-- ============================================================
-- Elaboration Uniqueness
-- ============================================================

-- /-
--   NOTE: inference_uniqueness has sorry in the mapp/mlink cross-cases.
--   elaboration_uniqueness inherits the same issue.
-- -/
-- theorem elaboration_uniqueness
--     {Γ T₁ T₂ : SCE.Typ} {e : SCE.Exp} {ce₁ ce₂ : Core.Exp}
--     (h₁ : elabExp Γ e T₁ ce₁)
--     (h₂ : elabExp Γ e T₂ ce₂)
--     : ce₁ = ce₂ := by
--   induction h₁ generalizing T₂ ce₂ with
--   | query ctx => cases h₂; rfl
--   | lit ctx n => cases h₂; rfl
--   | unit ctx => cases h₂; rfl
--   | proj ctx A B se ce i _ hlook ih =>
--     cases h₂ with
--     | proj _ A₂ B₂ _ _ _ helab₂ hlook₂ =>
--       have hce := ih helab₂
--       subst hce; rfl
--   | lam ctx A B se ce hbody ih =>
--     cases h₂ with
--     | lam _ _ B₂ _ _ hbody₂ =>
--       have hce := ih hbody₂
--       subst hce; rfl
--   | app ctx A B se1 se2 ce1 ce2 h1 h2 ih1 ih2 =>
--     cases h₂ with
--     | app _ A₂ B₂ _ _ _ _ h1₂ h2₂ =>
--       have hce1 := ih1 h1₂; subst hce1
--       have hce2 := ih2 h2₂; subst hce2; rfl
--   | dmrg ctx A B se1 se2 ce1 ce2 h1 h2 ih1 ih2 =>
--     cases h₂ with
--     | dmrg _ A₂ B₂ _ _ _ _ h1₂ h2₂ =>
--       have hce1 := ih1 h1₂; subst hce1
--       have hA := inference_uniqueness h1 h1₂; subst hA
--       have hce2 := ih2 h2₂; subst hce2; rfl
--   | nmrg ctx A B se1 se2 ce1 ce2 h1 h2 ih1 ih2 =>
--     cases h₂ with
--     | nmrg _ A₂ B₂ _ _ _ _ h1₂ h2₂ =>
--       have hce1 := ih1 h1₂; subst hce1
--       have hce2 := ih2 h2₂; subst hce2; rfl
--   | lrec ctx A se ce l _ ih =>
--     cases h₂ with
--     | lrec _ A₂ _ _ _ helab₂ =>
--       have hce := ih helab₂; subst hce; rfl
--   | rproj ctx A B se ce l hse hlook ih =>
--     cases h₂ with
--     | rproj _ A₂ B₂ _ _ _ hse₂ hlook₂ =>
--       have hce := ih hse₂; subst hce; rfl
--   | box ctx ctx' A se1 se2 ce1 ce2 h1 h2 ih1 ih2 =>
--     cases h₂ with
--     | box _ ctx'₂ A₂ _ _ _ _ h1₂ h2₂ =>
--       have hce1 := ih1 h1₂; subst hce1
--       have hctx' := inference_uniqueness h1 h1₂; subst hctx'
--       have hce2 := ih2 h2₂; subst hce2; rfl
--   | clos ctx ctx' A B se1 se2 ce1 ce2 h1 h2 ih1 ih2 =>
--     cases h₂ with
--     | clos _ ctx'₂ _ B₂ _ _ _ _ h1₂ h2₂ =>
--       have hce1 := ih1 h1₂; subst hce1
--       have hctx' := inference_uniqueness h1 h1₂; subst hctx'
--       have hce2 := ih2 h2₂; subst hce2; rfl
--   | letb ctx A B se1 se2 ce1 ce2 h1 h2 ih1 ih2 =>
--     cases h₂ with
--     | letb _ _ _ _ _ _ _ h1₂ h2₂ =>
--       -- ih1 applied to h1₂ gives ce1 = ce1₂. ih2 gives ce2 = ce2₂.
--       -- inference_uniqueness h1 h1₂ gives A = A₂ (which may be trivially A = A
--       -- after cases h₂ unifies the source expression).
--       -- We need to be careful: after `cases h₂`, the letb case
--       -- unifies the source Typ annotation, so A is already unified.
--       have hce1 := ih1 h1₂; subst hce1
--       have hce2 := ih2 h2₂; subst hce2; rfl
--   | openm ctx A B se1 se2 ce1 ce2 l h1 h2 ih1 ih2 =>
--     cases h₂ with
--     | openm _ _ _ _ _ _ _ _ h1₂ h2₂ =>
--       have hce1 := ih1 h1₂; subst hce1
--       have hA := inference_uniqueness h1 h1₂
--       cases hA
--       have hce2 := ih2 h2₂; subst hce2; rfl
--   | mstruct ctx ctxInner B sb se ce envCore hsb1 hsb2 he ih =>
--     cases h₂ with
--     | mstruct _ _ _ _ _ _ _ hsb1₂ hsb2₂ he₂ =>
--       cases sb with
--       | sandboxed =>
--         have := hsb1 rfl; subst this
--         have := hsb1₂ rfl; subst this
--         have hce := ih he₂; subst hce; rfl
--       | open_ =>
--         have := hsb2 rfl; subst this
--         have := hsb2₂ rfl; subst this
--         have hce := ih he₂; subst hce; rfl
--   | mfunctor ctx ctxInner A B sb se ce hsb1 hsb2 he ih =>
--     cases h₂ with
--     | mfunctor _ _ _ _ _ _ _ hsb1₂ hsb2₂ he₂ =>
--       cases sb with
--       | sandboxed =>
--         have := hsb1 rfl; subst this
--         have := hsb1₂ rfl; subst this
--         have hce := ih he₂; subst hce; rfl
--       | open_ =>
--         have := hsb2 rfl; subst this
--         have := hsb2₂ rfl; subst this
--         have hce := ih he₂; subst hce; rfl
--   | mclos ctx ctx' A B se1 se2 ce1 ce2 h1 h2 ih1 ih2 =>
--     cases h₂ with
--     | mclos _ _ _ _ _ _ _ _ h1₂ h2₂ =>
--       have hce1 := ih1 h1₂; subst hce1
--       have hctx' := inference_uniqueness h1 h1₂; subst hctx'
--       have hce2 := ih2 h2₂; subst hce2; rfl
--   | mapp ctx A mt se1 se2 ce1 ce2 h1 h2 ih1 ih2 =>
--     cases h₂ with
--     | mapp _ A₂ mt₂ _ _ _ _ h1₂ h2₂ =>
--       have hce1 := ih1 h1₂; subst hce1
--       have hce2 := ih2 h2₂; subst hce2; rfl
--     | mlink _ A₂ mt₂ _ _ _ _ h1₂ h2₂ =>
--       -- Cross case: same issue as inference_uniqueness
--       sorry
--   | mlink ctx A mt se1 se2 ce1 ce2 h1 h2 ih1 ih2 =>
--     cases h₂ with
--     | mlink _ A₂ mt₂ _ _ _ _ h1₂ h2₂ =>
--       have hce1 := ih1 h1₂; subst hce1
--       have hce2 := ih2 h2₂; subst hce2; rfl
--     | mapp _ A₂ mt₂ _ _ _ _ h1₂ h2₂ =>
--       -- Cross case: symmetric
--       sorry

-- ============================================================
-- Type Preservation
-- ============================================================

theorem type_preservation
    {Γ A : SCE.Typ} {es : SCE.Exp} {ec : Core.Exp}
    (h : elabExp Γ es A ec)
    : HasType (elabTyp Γ) ec (elabTyp A) := by
  induction h with
  | query ctx => exact HasType.tquery
  | lit ctx n => exact HasType.tint
  | unit ctx => exact HasType.tunit
  | proj ctx A B se ce i _ hlook ih =>
    exact HasType.tproj ih (type_safe_index_lookup hlook)
  | lam ctx A B se ce _ ih =>
    exact HasType.tlam ih
  | app ctx A B se1 se2 ce1 ce2 _ _ ih1 ih2 =>
    apply HasType.tapp ih1 ih2
  | box ctx ctx' A se1 se2 ce1 ce2 _ _ ih1 ih2 =>
    apply HasType.tbox ih1 ih2;
    exact Core.Typ.top
  | dmrg ctx A B se1 se2 ce1 ce2 _ _ ih1 ih2 =>
    exact HasType.tmrg ih1 ih2
  | lrec ctx A se ce l _ ih =>
    exact HasType.trcd ih
  | rproj ctx A B se ce l _ hlook ih =>
    exact HasType.trproj ih (type_safe_record_lookup hlook)
  | letb ctx A B se1 se2 ce1 ce2 _ _ ih1 ih2 =>
    apply HasType.tapp;
    apply HasType.tlam;
    · convert ih2 using 1;
    · assumption
  | openm ctx A B se1 se2 ce1 ce2 l _ _ ih1 ih2 =>
    apply HasType.tapp;
    apply HasType.tlam;
    · convert ih2 using 1;
    · apply HasType.trproj ih1 (type_safe_record_lookup (SCE.RecordLookup.zero l A))
  | clos ctx ctx' A B se1 se2 ce1 ce2 _ _ ih1 ih2 =>
    -- Requires Value ce1 and HasType .top ce1 Γ₁ for HasType.tclos
    sorry
  | nmrg ctx A B se1 se2 ce1 ce2 _ _ ih1 ih2 =>
    -- Complex core expression; requires weakening lemma
    sorry
  | mstruct ctx ctxInner B sb se ce envCore hsb1 hsb2 _ ih =>
    cases sb with
    | sandboxed =>
      have := hsb1 rfl; subst this
      simp [elabTyp, elabModTyp]
      exact HasType.tbox (B := elabTyp B) HasType.tunit ih
    | open_ =>
      have := hsb2 rfl; subst this
      simp [elabTyp, elabModTyp]
      exact HasType.tbox (B := elabTyp B) HasType.tquery ih
  | mfunctor ctx ctxInner A B sb se ce hsb1 hsb2 _ ih =>
    cases sb with
    | sandboxed =>
      have := hsb1 rfl; subst this
      simp [elabTyp, elabModTyp]
      exact HasType.tbox (B := Core.Typ.arr (elabTyp A) (elabTyp B)) HasType.tunit (HasType.tlam ih)
    | open_ =>
      have := hsb2 rfl; subst this
      simp [elabTyp, elabModTyp]
      exact HasType.tlam ih
  | mclos ctx ctx' A B se1 se2 ce1 ce2 _ _ ih1 ih2 =>
    -- Same issue as clos
    sorry
  | mapp ctx A mt se1 se2 ce1 ce2 _ _ ih1 ih2 =>
    simp [elabTyp, elabModTyp] at ih1 ⊢
    exact HasType.tapp ih1 ih2
  | mlink ctx A mt se1 se2 ce1 ce2 _ _ ih1 ih2 =>
    -- Requires weakening lemma
    sorry

-- ============================================================
-- Semantics Preservation (main theorem)
-- ============================================================

theorem semantics_preservation
    {Γ A : SCE.Typ}
    {es : SCE.Exp} {ec : Core.Exp}
    {rs vs : SCE.Exp}
    {cr : Core.Exp}
    (helab : elabExp Γ es A ec)
    (heval : S_Sem.BigStep rs es vs)
    (henv  : ValTrans rs Γ cr)
    : ∃ cv, ValTrans vs A cv ∧ C_Sem.EBig cr ec cv := by
  induction helab generalizing rs vs cr with
  | query ctx =>
    cases heval with
    | query hval =>
      exact ⟨cr, henv, C_Sem.EBig.equery henv.core_value⟩
  | lit ctx n =>
    cases heval with
    | lit hval =>
      exact ⟨Core.Exp.lit n, ValTrans.vint, C_Sem.EBig.eblit henv.core_value⟩
  | unit ctx =>
    cases heval with
    | unit hval =>
      exact ⟨Core.Exp.unit, ValTrans.vunit, C_Sem.EBig.ebunit henv.core_value⟩
  | lrec ctx B se ce l _ ih =>
    cases heval with
    | lrec hval hbody =>
      obtain ⟨cv, hvt, hcore⟩ := ih hbody henv
      exact ⟨Core.Exp.lrec l cv, ValTrans.vlrec hvt, C_Sem.EBig.ebrec hcore⟩
  | proj ctx B C se ce i _ hlook ih =>
    cases heval with
    | proj hval hbody hlookv =>
      obtain ⟨cv, hvt, hcore⟩ := ih hbody henv
      obtain ⟨cv', hvt', hclookv⟩ := val_trans_index_lookup hvt hlook hlookv
      exact ⟨cv', hvt', C_Sem.EBig.ebproj hcore hclookv⟩
  | lam ctx B C se ce _ ih =>
    cases heval with
    | lam hval =>
      exact ⟨Core.Exp.clos cr (elabTyp B) ce,
             ValTrans.vclos henv ‹_›,
             C_Sem.EBig.ebclos henv.core_value⟩
  | app ctx B C se1 se2 ce1 ce2 h1 h2 ih1 ih2 =>
    -- app case needs well-founded induction for closure body
    sorry
  | dmrg ctx B C se1 se2 ce1 ce2 h1 h2 ih1 ih2 =>
    cases heval with
    | dmrg hval heval1 heval2 =>
      obtain ⟨cv1, hvt1, hcore1⟩ := ih1 heval1 henv
      -- After `cases heval`, Lean introduces fresh names for the
      -- universally quantified variables in the BigStep.dmrg constructor.
      -- We use the ValTrans.vmrg to build the extended environment.
      -- The variable names depend on Lean's auto-naming after `cases`.
      -- We construct the environment for se2 using henv and hvt1.
      sorry
  | nmrg ctx B C se1 se2 ce1 ce2 h1 h2 ih1 ih2 =>
    sorry
  | rproj ctx B C se ce l hse hlook ih =>
    sorry
  | box ctx ctx' B se1 se2 ce1 ce2 h1 h2 ih1 ih2 =>
    cases heval with
    | box hval heval1 heval2 =>
      obtain ⟨cv1, hvt1, hcore1⟩ := ih1 heval1 henv
      obtain ⟨cv2, hvt2, hcore2⟩ := ih2 heval2 hvt1
      exact ⟨cv2, hvt2, C_Sem.EBig.ebbox hcore1 hcore2⟩
  | clos ctx ctx' B C se1 se2 ce1 ce2 h1 h2 ih1 ih2 =>
    sorry
  | letb ctx B C se1 se2 ce1 ce2 h1 h2 ih1 ih2 =>
    -- letb evaluates se1 then se2 under extended env
    -- core: app (lam (elabTyp B) ce2) ce1
    sorry
  | openm ctx B C se1 se2 ce1 ce2 l h1 h2 ih1 ih2 =>
    sorry
  | mstruct ctx ctxInner B sb se ce envCore hsb1 hsb2 he ih =>
    cases sb with
    | sandboxed =>
      have := hsb1 rfl; subst this
      cases heval with
      | mstruct_sandboxed hval hbody =>
        have henv_unit : ValTrans .unit .top .unit := ValTrans.vunit
        obtain ⟨cv, hvt, hcore⟩ := ih hbody henv_unit
        sorry
    | open_ =>
      have := hsb2 rfl; subst this
      cases heval with
      | mstruct_open hval hbody =>
        obtain ⟨cv, hvt, hcore⟩ := ih hbody henv
        sorry
  | mfunctor ctx ctxInner B C sb se ce hsb1 hsb2 he ih =>
    cases sb with
    | sandboxed =>
      have := hsb1 rfl; subst this
      cases heval with
      | mfunctor_sandboxed hval =>
        exact ⟨Core.Exp.clos Core.Exp.unit (elabTyp B) ce,
               ValTrans.vmclos ValTrans.vunit ‹_›,
               C_Sem.EBig.ebbox
                 (C_Sem.EBig.ebunit henv.core_value)
                 (C_Sem.EBig.ebclos Core.Value.vunit)⟩
    | open_ =>
      have := hsb2 rfl; subst this
      cases heval with
      | mfunctor_open hval =>
        exact ⟨Core.Exp.clos cr (elabTyp B) ce,
               ValTrans.vmclos henv ‹_›,
               C_Sem.EBig.ebclos henv.core_value⟩
  | mclos ctx ctx' B C se1 se2 ce1 ce2 h1 h2 ih1 ih2 =>
    sorry
  | mapp ctx B mt se1 se2 ce1 ce2 h1 h2 ih1 ih2 =>
    sorry
  | mlink ctx B mt se1 se2 ce1 ce2 h1 h2 ih1 ih2 =>
    sorry

/-
  Separate compilation theorem
-/
theorem separate_compilation
    {Γ A : SCE.Typ} {mt : SCE.ModTyp}
    {e₁ e₂ : SCE.Exp} {ce₁ ce₂ : Core.Exp}
    {rs vs : SCE.Exp} {cr : Core.Exp}
    (h₁ : elabExp Γ e₁ (.sig (.TyArrM A mt)) ce₁)
    (h₂ : elabExp Γ e₂ A ce₂)
    (heval : S_Sem.BigStep rs (.mlink e₁ e₂) vs)
    (henv : ValTrans rs Γ cr)
    : ∃ cv, ValTrans vs (.sig (.TyArrM A mt)) cv
          ∧ C_Sem.EBig cr (.mrg ce₂ (.app ce₁ ce₂)) cv := by
  have hmlink : elabExp Γ (.mlink e₁ e₂) (.sig (.TyArrM A mt))
      (.mrg ce₂ (.app ce₁ ce₂)) :=
    elabExp.mlink _ _ _ _ _ _ _ h₁ h₂
  exact semantics_preservation hmlink heval henv
