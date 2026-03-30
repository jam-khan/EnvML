import LeanSce.Core.Syntax
import LeanSce.Core.BigStep
import LeanSce.Core.Typing
import LeanSce.SCE.Syntax
import LeanSce.SCE.Semantics
import LeanSce.SCE.Elaboration

open SCE Core

inductive CoreLink
    : Core.Typ → String → Core.Typ → Core.Typ → Core.Typ
    → Core.Exp → Core.Exp → Core.Exp → Prop where
  | link (Γ A₁ A B : Core.Typ) (l : String) (ec₁ ec₂ : Core.Exp)
    : Core.RLookup A₁ l A
    → CoreLink Γ l A₁ A B ec₁ ec₂ (linkedCore Γ l ec₁ ec₂)

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
    : T₁ = T₂ := by
  induction h₁ with
  | zero l T => cases h₂; rfl
  | andl A B l T _ h_cond ih =>
    cases h₂ with
    | andl _ _ _ _ h₂' _ => exact ih h₂'
    | andr _ _ _ _ h₂' h_cond₂ =>
      exact absurd (h_cond.1) h_cond₂.2
  | andr A B l T _ h_cond ih =>
    cases h₂ with
    | andr _ _ _ _ h₂' _ => exact ih h₂'
    | andl _ _ _ _ h₂' h_cond₂ =>
      exact absurd (h_cond.1) h_cond₂.2

theorem type_safe_index_lookup
    {ST₁ ST₂ : SCE.Typ} {n : Nat}
    (h : SLookup ST₁ n ST₂)
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
    | rcd l T =>
      simp [elabTyp]
      exact Core.Lin.rcd
    | andl A B l _ ih =>
      simp [elabTyp]
      exact Core.Lin.andl ih
    | andr A B l _ ih =>
      simp [elabTyp]
      exact Core.Lin.andr ih
    | sig l T _ ih =>
      simp [elabTyp, elabModTyp]
      exact ih
  · intro h
    cases ST with
    | rcd lA T =>
      simp [elabTyp] at h
      cases h
      exact SCE.LabelIn.rcd l T
    | and A B =>
      simp [elabTyp] at h
      cases h with
      | andl h =>
        exact SCE.LabelIn.andl A B l (type_safe_label_existence.mpr h)
      | andr h =>
        exact SCE.LabelIn.andr A B l (type_safe_label_existence.mpr h)
    | int => simp [elabTyp] at h; cases h
    | top => simp [elabTyp] at h; cases h
    | arr _ _ => simp [elabTyp] at h; cases h
    | sig mt =>
      cases mt with
      | TyIntf T =>
        simp [elabTyp, elabModTyp] at h
        exact SCE.LabelIn.sig l T (type_safe_label_existence.mpr h)
      | TyArrM T mt' =>
        simp [elabTyp, elabModTyp] at h; cases h


theorem type_safe_label_nonexistence
    {l : String} {ST : SCE.Typ}
    : ¬ SCE.LabelIn l ST ↔ ¬ Core.Lin l (elabTyp ST) := by
  constructor
  · intro hns hc; exact hns (type_safe_label_existence.mpr hc)
  · intro hnc hs; exact hnc (type_safe_label_existence.mp hs)

theorem type_safe_record_lookup
    {ST₁ ST₂ : SCE.Typ} {l : String}
    (h : SCE.SRLookup ST₁ l ST₂)
    : Core.RLookup (elabTyp ST₁) l (elabTyp ST₂) := by
  induction h with
  | zero l T =>
    simp [elabTyp]
    exact Core.RLookup.zero
  | andl A B l T _ h_cond ih =>
    simp [elabTyp]
    exact Core.RLookup.landl ih
      (type_safe_label_nonexistence.mp h_cond.2)
  | andr A B l T _ h_cond ih =>
    simp [elabTyp]
    exact Core.RLookup.landr ih
      ⟨type_safe_label_nonexistence.mp h_cond.2,
       type_safe_label_existence.mp h_cond.1⟩

theorem inference_uniqueness
    {Γ T₁ T₂ : SCE.Typ} {e : SCE.Exp} {ce₁ ce₂ : Core.Exp}
    (h₁ : elabExp Γ e T₁ ce₁)
    (h₂ : elabExp Γ e T₂ ce₂)
    : T₁ = T₂ := by
  revert T₂ ce₂
  induction h₁ with
  | equery =>
    intro ce₂ T₂ h₂; cases h₂; rfl
  | elit _ n =>
    intro ce₂ T₂ h₂; cases h₂; rfl
  | eunit _ =>
    intro ce₂ T₂ h₂; cases h₂; rfl
  | eapp ctx A B se1 se2 ce1 ce2 _ _ ih1 ih2 =>
    intro ce₂ T₂ h₂
    cases h₂ with
    | eapp _ a' _ _ _ ce1' ce2' h1' h2' =>
      have := ih1 h1'
      cases this; rfl
  | eproj ctx A B se ce i _ hlook ih =>
    intro ce₂ T₂ h₂
    cases h₂ with
    | eproj _ a' _ _ ce' _ h' hlook' =>
      have hA := ih h'
      rw [hA] at hlook
      exact index_lookup_uniqueness hlook hlook'
  | ebox ctx ctx' A se1 se2 ce1 ce2 _ _ ih1 ih2 =>
    intro ce₂ T₂ h₂
    cases h₂ with
    | ebox _ en _ _ _ ce1' ce2' h1' h2' =>
      have hA := ih1 h1'
      rw [hA] at ih2
      exact ih2 h2'
  | edmrg ctx A B se1 se2 ce1 ce2 _ _ ih1 ih2 =>
    intro ce₂ T₂ h₂
    cases h₂ with
    | edmrg _ a' b' _ _ ce1' ce2' h1' h2' =>
      have hA := ih1 h1'
      have hB := ih2 (hA ▸ h2')
      rw [hA, hB]
  | enmrg ctx A B se1 se2 ce1 ce2 _ _ ih1 ih2 =>
    intro ce₂ T₂ h₂
    cases h₂ with
    | enmrg _ a' b' _ _ ce1' ce2' h1' h2' =>
      have hA := ih1 h1'
      have hB := ih2 h2'
      rw [hA, hB]
  | elam ctx A B se ce _ ih =>
    intro ce₂ T₂ h₂
    cases h₂ with
    | elam _ _ b' _ ce' h' =>
      have hB := ih h'
      rw [hB]
  | erproj ctx A B se ce l _ hlook ih =>
    intro ce₂ T₂ h₂
    cases h₂ with
    | erproj _ a' b' _ ce' _ h' hlook' =>
      have hB := ih h'
      rw [hB] at hlook
      exact record_lookup_uniqueness hlook hlook'
  | eclos ctx ctx' A B se1 se2 ce1 ce2 _ _ _ ih1 ih2 =>
    intro ce₂ T₂ h₂
    cases h₂ with
    | eclos _ et _ bT _ _ ce1' ce2' _ h1' h2' =>
      have hA := ih1 h1'
      have hB := ih2 (hA ▸ h2')
      rw [hB]
  | elrec ctx A se ce l _ ih =>
    intro ce₂ T₂ h₂
    cases h₂ with
    | elrec _ a' _ ce' _ h' =>
      have hA := ih h'
      rw [hA]
  | letb ctx A B se1 se2 ce1 ce2 _ _ ih1 ih2 =>
    intro ce₂ T₂ h₂
    cases h₂ with
    | letb _ _ b' _ _ ce1' ce2' h1' h2' =>
      exact ih2 h2'
  | openm ctx A B se1 se2 ce1 ce2 l _ _ ih1 ih2 =>
    intro ce₂ T₂ h₂
    cases h₂ with
    | openm _ a' b' _ _ ce1' ce2' _ h1' h2' =>
      have hA : SCE.Typ.rcd l A = SCE.Typ.rcd _ a' := ih1 h1'
      cases hA
      exact ih2 h2'
  | mstruct ctx ctxInner B sb se ce envCore _ _ _ ih =>
    intros T₂ ce₂ h₂
    rename_i hs1 hs2 el1
    cases h₂ with
    | mstruct _ ci' b' _ _ ce' _ hs1' hs2' h' =>
      have hCtx : ctxInner = ci' := by
        cases sb with
        | sandboxed =>
          rw [hs1 rfl, hs1' rfl]
        | open_ =>
          rw [hs2 rfl, hs2' rfl]
      rw [←hCtx] at h'
      have hB := ih h'
      rw [hB]
  | mfunctor ctx ctxInner A B sb se ce _ _ _ ih =>
    intro ce₂ T₂ h₂
    rename_i hs1 hs2 el1
    cases h₂ with
    | mfunctor _ ci' _ b' _ _ ce' hs1' hs2' h' =>
      have hCtx : ctxInner = ci' := by
        cases sb with
        | sandboxed => rw [hs1 rfl, hs1' rfl]
        | open_ => rw [hs2 rfl, hs2' rfl]
      rw [← hCtx] at h'
      have hB := ih h'
      rw [hB]
  | mclos ctx ctx' A B se1 se2 ce1 ce2 _ _ _ ih1 ih2 =>
    intro ce₂ T₂ h₂
    cases h₂ with
    | mclos _ et _ bT _ _ ce1' ce2' _ h1' h2' =>
      have hA := ih1 h1'
      rw [← hA] at h2'
      have hB := ih2 h2'
      rw [hB]
  | mapp ctx A mt se1 se2 ce1 ce2 _ _ ih1 ih2 =>
    intro ce₂ T₂ h₂
    cases h₂ with
    | mapp _ a' mt' _ _ ce1' ce2' h1' h2' =>
      have hA := ih2 h2'
      have := ih1 h1'
      rw [hA] at this
      cases this; rfl
  | mlink ctx Γ₁ A mt l se1 se2 ce1 ce2 _ _ _ ih1 ih2 =>
    intro ce₂ T₂ h₂
    cases h₂ with
    | mlink _ Γ₁' A' mt' l' _ _ ce1' ce2' h1' h2' _ =>
      have hΓ := ih1 h1'
      have := ih2 h2'
      cases this
      rw [hΓ]

theorem elaboration_uniqueness
    {Γ T₁ T₂ : SCE.Typ} {e : SCE.Exp} {ce₁ ce₂ : Core.Exp}
    (h₁ : elabExp Γ e T₁ ce₁)
    (h₂ : elabExp Γ e T₂ ce₂)
    : ce₁ = ce₂ := by
  revert T₂ ce₂
  induction h₁ with
  | equery =>
    intro ce₂ T₂ h₂; cases h₂; rfl
  | elit _ n =>
    intro ce₂ T₂ h₂; cases h₂; rfl
  | eunit _ =>
    intro ce₂ T₂ h₂; cases h₂; rfl
  | eapp ctx A B se1 se2 ce1 ce2 _ _ ih1 ih2 =>
    intro ce₂ T₂ h₂
    cases h₂ with
    | eapp _ a' _ _ _ ce1' ce2' h1' h2' =>
      have hA := ih1 h1'
      have hB := ih2 h2'
      rw [hA, hB]
  | eproj ctx A B se ce i _ hlook ih =>
    intro ce₂ T₂ h₂
    cases h₂ with
    | eproj _ a' _ _ ce' _ h' hlook' =>
      have hA := ih h'
      rw [hA]
  | ebox ctx ctx' A se1 se2 ce1 ce2 h1_orig h2_orig ih1 ih2 =>
    intro ce₂ T₂ h₂
    cases h₂ with
    | ebox _ en _ _ _ ce1' ce2' h1' h2' =>
      have hce1 := ih1 h1'
      have hctx := inference_uniqueness h1_orig h1'
      rw [← hctx] at h2'
      have hce2 := ih2 h2'
      rw [hce1, hce2]
  | edmrg ctx A B se1 se2 ce1 ce2 h1_orig h2_orig ih1 ih2 =>
    intro ce₂ T₂ h₂
    cases h₂ with
    | edmrg _ a' b' _ _ ce1' ce2' h1' h2' =>
      have hce1 := ih1 h1'
      have hA := inference_uniqueness h1_orig h1'
      rw [← hA] at h2'
      have hce2 := ih2 h2'
      rw [hce1, hce2]
  | enmrg ctx A B se1 se2 ce1 ce2 _ _ ih1 ih2 =>
    intro ce₂ T₂ h₂
    cases h₂ with
    | enmrg _ a' b' _ _ ce1' ce2' h1' h2' =>
      have hce1 := ih1 h1'
      have hce2 := ih2 h2'
      rw [hce1, hce2]
  | elam ctx A B se ce _ ih =>
    intro ce₂ T₂ h₂
    cases h₂ with
    | elam _ _ b' _ ce' h' =>
      have hce := ih h'
      rw [hce]
  | erproj ctx A B se ce l _ hlook ih =>
    intro ce₂ T₂ h₂
    cases h₂ with
    | erproj _ a' b' _ ce' _ h' hlook' =>
      have hce := ih h'
      rw [hce]
  | eclos ctx ctx' A B se1 se2 ce1 ce2 hval h1_orig h2_orig ih1 ih2 =>
    intro ce₂ T₂ h₂
    cases h₂ with
    | eclos _ et _ bT _ _ ce1' ce2' _ h1' h2' =>
      have hce1 := ih1 h1'
      have hctx := inference_uniqueness h1_orig h1'
      rw [← hctx] at h2'
      have hce2 := ih2 h2'
      rw [hce1, hce2]
  | elrec ctx A se ce l _ ih =>
    intro ce₂ T₂ h₂
    cases h₂ with
    | elrec _ a' _ ce' _ h' =>
      have hce := ih h'
      rw [hce]
  | letb ctx A B se1 se2 ce1 ce2 _ _ ih1 ih2 =>
    intro ce₂ T₂ h₂
    cases h₂ with
    | letb _ _ b' _ _ ce1' ce2' h1' h2' =>
      have hce1 := ih1 h1'
      have hce2 := ih2 h2'
      rw [hce1, hce2]
  | openm ctx A B se1 se2 ce1 ce2 l h1_orig h2_orig ih1 ih2 =>
    intro ce₂ T₂ h₂
    cases h₂ with
    | openm _ a' b' _ _ ce1' ce2' _ h1' h2' =>
      have htyp : SCE.Typ.rcd l A = SCE.Typ.rcd _ a' := inference_uniqueness h1_orig h1'
      cases htyp
      have hce1 := ih1 h1'
      have hce2 := ih2 h2'
      rw [hce1, hce2]
  | mstruct ctx ctxInner B sb se ce envCore _ _ _ ih =>
    intro ce₂ T₂ h₂
    rename_i hs1 hs2 el1
    cases h₂ with
    | mstruct _ ci' b' _ _ ce' _ hs1' hs2' h' =>
      have hCtx : ctxInner = ci' := by
        cases sb with
        | sandboxed => rw [hs1 rfl, hs1' rfl]
        | open_ => rw [hs2 rfl, hs2' rfl]
      rw [← hCtx] at h'
      have hce := ih h'
      rw [hce]
  | mfunctor ctx ctxInner A B sb se ce _ _ _ ih =>
    intro ce₂ T₂ h₂
    rename_i hs1 hs2 el1
    cases h₂ with
    | mfunctor _ ci' _ b' _ _ ce' hs1' hs2' h' =>
      have hCtx : ctxInner = ci' := by
        cases sb with
        | sandboxed => rw [hs1 rfl, hs1' rfl]
        | open_ => rw [hs2 rfl, hs2' rfl]
      rw [← hCtx] at h'
      have hce := ih h'
      rw [hce]
  | mclos ctx ctx' A B se1 se2 ce1 ce2 hval h1_orig h2_orig ih1 ih2 =>
    intro ce₂ T₂ h₂
    cases h₂ with
    | mclos _ et _ bT _ _ ce1' ce2' _ h1' h2' =>
      have hce1 := ih1 h1'
      have hctx := inference_uniqueness h1_orig h1'
      rw [← hctx] at h2'
      have hce2 := ih2 h2'
      rw [hce1, hce2]
  | mapp ctx A mt se1 se2 ce1 ce2 _ _ ih1 ih2 =>
    intro ce₂ T₂ h₂
    cases h₂ with
    | mapp _ a' mt' _ _ ce1' ce2' h1' h2' =>
      have hce1 := ih1 h1'
      have hce2 := ih2 h2'
      rw [hce1, hce2]
  | mlink ctx Γ₁ A mt l se1 se2 ce1 ce2 h1_orig h2_orig _ ih1 ih2 =>
    intro ce₂ T₂ h₂
    cases h₂ with
    | mlink _ Γ₁' A' mt' l' _ _ ce1' ce2' h1' h2' _ =>
      have hce1 := ih1 h1'
      have hce2 := ih2 h2'
      have htyp := inference_uniqueness h2_orig h2'
      cases htyp
      rw [hce1, hce2]

theorem elab_value
    {Γ A : SCE.Typ} {v : SCE.Exp} {cv : Core.Exp}
    (helab : elabExp Γ v A cv)
    (hval : SCE.Value v)
    : Core.Value cv := by
  induction hval generalizing Γ A cv with
  | vint =>
    cases helab
    exact Core.Value.vint
  | vunit =>
    cases helab
    exact Core.Value.vunit
  | vclos hv ih =>
    cases helab with
    | eclos _ _ _ _ _ _ ce1 ce2 _ h1 h2 =>
      exact Core.Value.vclos (ih h1)
  | vmclos hv ih =>
    cases helab with
    | mclos _ _ _ _ _ _ ce1 ce2 _ h1 h2 =>
      exact Core.Value.vclos (ih h1)
  | vmrg hv1 hv2 ih1 ih2 =>
    cases helab with
    | edmrg _ _ _ _ _ ce1 ce2 h1 h2 =>
      exact Core.Value.vmrg (ih1 h1) (ih2 h2)
  | vlrec hv ih =>
    cases helab with
    | elrec _ _ _ ce _ h =>
      exact Core.Value.vrcd (ih h)

theorem type_preservation
    {Γ A : SCE.Typ} {es : SCE.Exp} {ec : Core.Exp}
    (h : elabExp Γ es A ec)
    : HasType (elabTyp Γ) ec (elabTyp A) := by
    induction h with
    | equery =>
      exact HasType.tquery
    | elit ctx n =>
      simp [elabTyp]
      exact HasType.tint
    | eunit ctx =>
      simp [elabTyp]
      exact HasType.tunit
    | eapp ctx A B se1 se2 ce1 ce2 _ _ ih1 ih2 =>
      exact HasType.tapp ih1 ih2
    | eproj ctx A B se ce i _ hlook ih =>
      exact HasType.tproj ih (type_safe_index_lookup hlook)
    | ebox ctx ctx' A se1 se2 ce1 ce2 _ _ ih1 ih2 =>
      exact HasType.tbox ih1 ih2
    | edmrg ctx A B se1 se2 ce1 ce2 _ _ ih1 ih2 =>
      simp [elabTyp]
      exact HasType.tmrg ih1 ih2
    | enmrg ctx A B se1 se2 ce1 ce2 _ _ ih1 ih2 =>
      simp [elabTyp]
      apply HasType.tapp
      · apply HasType.tlam
        apply HasType.tmrg
        · apply HasType.tbox
          · exact HasType.tproj HasType.tquery Lookup.zero
          · exact ih1
        · apply HasType.tbox
          · exact HasType.tproj HasType.tquery (Lookup.succ Lookup.zero)
          · exact ih2
      · exact HasType.tquery
    | elam ctx A B se ce _ ih =>
      simp [elabTyp]
      exact HasType.tlam ih
    | erproj ctx A B se ce l _ hlook ih =>
      exact HasType.trproj ih (type_safe_record_lookup hlook)
    | eclos ctx ctx' A B se1 se2 ce1 ce2 hval h1 h2 ih1 ih2 =>
      simp [elabTyp]
      exact HasType.tclos (elab_value h1 hval) ih1 ih2
    | elrec ctx A se ce l _ ih =>
      simp [elabTyp]
      exact HasType.trcd ih
    | letb ctx A B se1 se2 ce1 ce2 _ _ ih1 ih2 =>
      exact HasType.tapp (HasType.tlam ih2) ih1
    | openm ctx A B se1 se2 ce1 ce2 l _ _ ih1 ih2 =>
      exact HasType.tapp (HasType.tlam ih2) (HasType.trproj ih1 Core.RLookup.zero)
    | mstruct ctx ctxInner B sb se ce envCore hs1 hs2 _ ih =>
      cases sb with
      | sandboxed =>
        have := hs1 rfl
        rw [this] at ih
        simp [elabTyp] at ih
        exact HasType.tbox HasType.tunit ih
      | open_ =>
        have := hs2 rfl
        rw [this] at ih
        exact HasType.tbox HasType.tquery ih
    | mfunctor ctx ctxInner A B sb se ce hs1 hs2 _ ih =>
      simp [elabTyp, elabModTyp]
      cases sb with
      | sandboxed =>
        have := hs1 rfl
        rw [this] at ih
        simp [elabTyp] at ih
        exact HasType.tbox HasType.tunit (HasType.tlam ih)
      | open_ =>
        have := hs2 rfl
        rw [this] at ih
        simp [elabTyp] at ih
        exact HasType.tlam ih
    | mclos ctx ctx' A B se1 se2 ce1 ce2 hval h1 h2 ih1 ih2 =>
      simp [elabTyp, elabModTyp]
      exact HasType.tclos (elab_value h1 hval) ih1 ih2
    | mapp ctx A B se1 se2 ce1 ce2 _ _ ih1 ih2 =>
      exact HasType.tapp ih1 ih2
    | mlink ctx Γ₁ A mt l se1 se2 ce1 ce2 _ _ hlookup ih1 ih2 =>
      simp [elabTyp, linkedCore]
      apply HasType.tapp
      · apply HasType.tlam
        apply HasType.tmrg
        · apply HasType.tbox
          · exact HasType.tproj HasType.tquery Lookup.zero
          · exact ih1
        · apply HasType.tbox
          · exact HasType.tproj HasType.tquery (Lookup.succ Lookup.zero)
          · exact HasType.tapp ih2
              (HasType.trcd (HasType.trproj ih1 (type_safe_record_lookup hlookup)))
      · exact HasType.tquery

theorem value_typing_weakening
    {v : SCE.Exp} {cv : Core.Exp} {A Γ₁ Γ₂ : SCE.Typ}
    (hval : SCE.Value v)
    (helab : elabExp Γ₁ v A cv)
    : elabExp Γ₂ v A cv := by
  induction hval generalizing Γ₁ Γ₂ A cv with
  | vint =>
    cases helab
    exact elabExp.elit Γ₂ _
  | vunit =>
    cases helab
    exact elabExp.eunit Γ₂
  | vclos hv ih =>
    cases helab with
    | eclos _ _ _ _ _ _ _ _ hval' h1 h2 =>
      exact elabExp.eclos Γ₂ _ _ _ _ _ _ _ hval' h1 h2
  | vmclos hv ih =>
    cases helab with
    | mclos _ _ _ _ _ _ _ _ hval' h1 h2 =>
      exact elabExp.mclos Γ₂ _ _ _ _ _ _ _ hval' h1 h2
  | vmrg hv1 hv2 ih1 ih2 =>
    cases helab with
    | edmrg _ _ _ _ _ _ _ h1 h2 =>
      exact elabExp.edmrg Γ₂ _ _ _ _ _ _ (ih1 h1) (ih2 h2)
  | vlrec hv ih =>
    cases helab with
    | elrec _ _ _ _ _ h =>
      exact elabExp.elrec Γ₂ _ _ _ _ (ih h)

theorem source_lookupv_value
    {v v' : SCE.Exp} {n : Nat}
    (hval : SCE.Value v)
    (hlook : S_Sem.LookupV v n v')
    : SCE.Value v' := by
  induction hlook with
  | dmrg_zero => cases hval with | vmrg h1 h2 => exact h2
  | dmrg_succ _ ih => cases hval with | vmrg h1 h2 => exact ih h1
  | nmrg_zero => cases hval
  | nmrg_succ => cases hval

theorem source_sel_value
    {v v' : SCE.Exp} {l : String}
    (hval : SCE.Value v)
    (hsel : S_Sem.Sel v l v')
    : SCE.Value v' := by
  induction hsel with
  | rcd => cases hval with | vlrec h => exact h
  | dmrg_left _ ih => cases hval with | vmrg h1 h2 => exact ih h1
  | dmrg_right _ ih => cases hval with | vmrg h1 h2 => exact ih h2
  | nmrg_left _ ih => cases hval
  | nmrg_right _ ih => cases hval

theorem eval_produces_value
    {ρ e v : SCE.Exp}
    (hval : SCE.Value ρ)
    (heval : S_Sem.BStep ρ e v)
    : SCE.Value v := by
  induction heval with
  | query _ => exact hval
  | lit _ => exact SCE.Value.vint
  | unit _ => exact SCE.Value.vunit
  | clos_val _ hv => exact SCE.Value.vclos hv
  | mclos_val _ hv => exact SCE.Value.vmclos hv
  | proj _ _ hlook ih1 =>
    exact source_lookupv_value (ih1 hval) hlook
  | lam _ => exact SCE.Value.vclos hval
  | box _ _ _ ih1 ih2 => exact ih2 (ih1 hval)
  | app_clos _ _ _ _ ih1 ih2 ih3 =>
    have hvclos := ih1 hval
    cases hvclos with | vclos hv => exact ih3 (SCE.Value.vmrg hv (ih2 hval))
  | app_mclos _ _ _ _ ih1 ih2 ih3 =>
    have hvclos := ih1 hval
    cases hvclos with | vmclos hv => exact ih3 (SCE.Value.vmrg hv (ih2 hval))
  | dmrg _ _ _ ih1 ih2 =>
    exact SCE.Value.vmrg (ih1 hval) (ih2 (SCE.Value.vmrg hval (ih1 hval)))
  | nmrg _ _ _ ih1 ih2 =>
    exact SCE.Value.vmrg (ih1 hval) (ih2 hval)
  | lrec _ _ ih => exact SCE.Value.vlrec (ih hval)
  | rproj _ _ hsel ih =>
    exact source_sel_value (ih hval) hsel
  | letb _ _ _ ih1 ih2 =>
    exact ih2 (SCE.Value.vmrg hval (ih1 hval))
  | openm _ _ _ ih1 ih2 =>
    have := ih1 hval
    cases this with | vlrec hv => exact ih2 (SCE.Value.vmrg hval hv)
  | mstruct_sandboxed _ _ ih => exact ih SCE.Value.vunit
  | mstruct_open _ _ ih => exact ih hval
  | mfunctor_sandboxed _ => exact SCE.Value.vmclos SCE.Value.vunit
  | mfunctor_open hv => exact SCE.Value.vmclos hv
  | mlink hv hstep1 hstep2 hsel hstep3 ih1 ih2 ih3 =>
    have hv1 := ih1 hv
    have hv2 := ih2 hv
    cases hv2 with
    | vmclos hvv2 =>
      have hvl := source_sel_value hv1 hsel
      exact SCE.Value.vmrg hv1 (ih3 (SCE.Value.vmrg hvv2 (SCE.Value.vlrec hvl)))

theorem lookup_preservation
    {v_e v' : SCE.Exp} {vc_e : Core.Exp} {A B : SCE.Typ} {i : Nat}
    (hval : SCE.Value v_e)
    (helab : elabExp SCE.Typ.top v_e A vc_e)
    (hlook : S_Sem.LookupV v_e i v')
    (htyp_look : SCE.SLookup A i B)
    : ∃ vc', Core.LookupV vc_e i vc' ∧ elabExp SCE.Typ.top v' B vc' := by
  sorry

theorem sel_preservation
    {v_e v' : SCE.Exp} {vc_e : Core.Exp} {A B : SCE.Typ} {l : String}
    (hval : SCE.Value v_e)
    (helab : elabExp SCE.Typ.top v_e A vc_e)
    (hlook : S_Sem.Sel v_e l v')
    (htyp_look : SCE.SRLookup A l B)
    : ∃ vc', Core.RLookupV vc_e l vc' ∧ elabExp SCE.Typ.top v' B vc' := by
  sorry

theorem linkedCore_eval
    {ρc vc1 vc2 vc_l vc3 : Core.Exp} {ctx : Core.Typ} {l : String}
    {ce1 ce2 body : Core.Exp} {A : Core.Typ}
    (hval_ρ : Core.Value ρc)
    (hbig1 : EBig ρc ce1 vc1)
    (hbig2 : EBig ρc ce2 (Core.Exp.clos vc2 (.rcd l A) body))
    (hsel : Core.RLookupV vc1 l vc_l)
    (hbig3 : EBig (.mrg vc2 (.lrec l vc_l)) body vc3)
    : EBig ρc (linkedCore ctx l ce1 ce2) (.mrg vc1 vc3) := by
  have hval_vc1 := ebig_produces_value hval_ρ hbig1
  simp [linkedCore]
  apply EBig.ebapp
  · exact EBig.ebclos hval_ρ
  · exact EBig.equery hval_ρ
  · apply EBig.ebmrg
    · apply EBig.ebbox
      · exact EBig.ebproj (EBig.equery (Value.vmrg hval_ρ hval_ρ)) LookupV.lvzero
      · exact hbig1
    · apply EBig.ebbox
      · exact EBig.ebproj
          (EBig.equery (Value.vmrg (Value.vmrg hval_ρ hval_ρ) hval_vc1))
          (LookupV.lvsucc LookupV.lvzero)
      · exact EBig.ebapp
          hbig2
          (EBig.ebrec (EBig.ebsel hbig1 hsel))
          hbig3

theorem nmrg_core_eval
    {ρc vc1 vc2 : Core.Exp} {ctx : Core.Typ}
    {ce1 ce2 : Core.Exp}
    (hval_ρ : Core.Value ρc)
    (hbig1 : EBig ρc ce1 vc1)
    (hbig2 : EBig ρc ce2 vc2)
    : EBig ρc
        (Core.Exp.app
          (Core.Exp.lam ctx
            (Core.Exp.mrg
              (Core.Exp.box (Core.Exp.proj Core.Exp.query 0) ce1)
              (Core.Exp.box (Core.Exp.proj Core.Exp.query 1) ce2)))
          Core.Exp.query)
        (.mrg vc1 vc2) := by
  have hval_vc1 := ebig_produces_value hval_ρ hbig1
  apply EBig.ebapp
  · exact EBig.ebclos hval_ρ
  · exact EBig.equery hval_ρ
  · apply EBig.ebmrg
    · apply EBig.ebbox
      · exact EBig.ebproj (EBig.equery (Value.vmrg hval_ρ hval_ρ)) LookupV.lvzero
      · exact hbig1
    · apply EBig.ebbox
      · exact EBig.ebproj
          (EBig.equery (Value.vmrg (Value.vmrg hval_ρ hval_ρ) hval_vc1))
          (LookupV.lvsucc LookupV.lvzero)
      · exact hbig2

theorem semantic_preservation
    {Γ A : SCE.Typ} {es : SCE.Exp} {ec : Core.Exp}
    {ρs vs : SCE.Exp} {ρc : Core.Exp}
    (helab : elabExp Γ es A ec)
    (heval : S_Sem.BStep ρs es vs)
    (henv : elabExp SCE.Typ.top ρs Γ ρc)
    (henv_val : SCE.Value ρs)
    : ∃ vc, EBig ρc ec vc ∧ elabExp SCE.Typ.top vs A vc := by
  induction heval generalizing Γ A ec ρc with
  | query hval=>
    rename_i v
    exists ρc
    constructor
    · cases helab
      refine EBig.equery ?_
      exact elab_value henv hval
    · cases helab
      assumption
  | lit hval =>
    cases helab
    exact ⟨Core.Exp.lit _, EBig.eblit (elab_value henv henv_val), elabExp.elit .top _⟩
  | unit =>
    cases helab
    exists Core.Exp.unit
    constructor
    · apply EBig.ebunit
      (expose_names; exact elab_value henv h)
    · exact elabExp.eunit SCE.Typ.top
  | clos_val henv_src hval =>
    cases helab with
    | eclos _ _ _ _ _ _ _ _ hval' h1 h2 =>
      exact ⟨_, EBig.eclos (elab_value henv henv_val) (elab_value h1 hval),
               elabExp.eclos .top _ _ _ _ _ _ _ hval h1 h2⟩
  | mclos_val henv_src hval =>
    cases helab with
    | mclos _ _ _ _ _ _ _ _ hval' h1 h2 =>
      exact ⟨_, EBig.eclos (elab_value henv henv_val) (elab_value h1 hval),
               elabExp.mclos .top _ _ _ _ _ _ _ hval h1 h2⟩
  | proj ρ1 hstep hlookv ih1 =>
    cases helab with
    | eproj _ A' _ _ ce _ h_elab h_slook =>
      obtain ⟨vc, hbig, helab_v⟩ := ih1 h_elab henv henv_val
      obtain ⟨vc', hlookvc, helab_v'⟩ := lookup_preservation
        (eval_produces_value henv_val hstep)
        helab_v hlookv h_slook
      exact ⟨vc', EBig.ebproj hbig hlookvc, helab_v'⟩
  | lam hval =>
    cases helab with
    | elam _ _ _ _ ce h_body =>
      exact ⟨Core.Exp.clos ρc _ ce,
             EBig.ebclos (elab_value henv henv_val),
             elabExp.eclos .top _ _ _ _ _ _ _ henv_val henv h_body⟩
  | box hval_ρ hstep1 hstep2 ih1 ih2 =>
    cases helab with
    | ebox _ ctx' _ _ _ ce1 ce2 h_elab1 h_elab2 =>
      obtain ⟨vc1, hbig1, helab_v1⟩ := ih1 h_elab1 henv henv_val
      have hv1_val := eval_produces_value henv_val hstep1
      obtain ⟨vc, hbig2, helab_v⟩ := ih2 h_elab2 helab_v1 hv1_val
      exact ⟨vc, EBig.ebbox hbig1 hbig2, helab_v⟩
  | app_clos hval_ρ hstep1 hstep2 hstep_body ih1 ih2 ih3 =>
    cases helab with
    | eapp _ A_param B _ _ ce1 ce2 h_elab1 h_elab2 =>
      obtain ⟨vc_clos, hbig1, helab_clos⟩ := ih1 h_elab1 henv henv_val
      obtain ⟨vc2, hbig2, helab_v2⟩ := ih2 h_elab2 henv henv_val
      cases helab_clos with
      | eclos _ _ _ _ _ _ _ _ hval_v1 h_env_v1 h_body_elab =>
        rename_i ctx_clos ce_env ce_body
        have hv1_val := eval_produces_value henv_val hstep1
        cases hv1_val with
        | vclos hval_inner =>
          have hv2_val := eval_produces_value henv_val hstep2
          have hval_body_env := SCE.Value.vmrg hval_inner hv2_val
          have helab_body_env := elabExp.edmrg .top _ _ _ _ _ _
            h_env_v1 (value_typing_weakening (Γ₂ := SCE.Typ.and .top ctx_clos) hv2_val helab_v2)
          obtain ⟨vc_result, hbig3, helab_result⟩ := ih3 h_body_elab helab_body_env hval_body_env
          exact ⟨vc_result,
                 EBig.ebapp hbig1 hbig2 hbig3,
                 helab_result⟩
  | app_mclos hval_ρ hstep1 hstep2 hstep_body ih1 ih2 ih3 =>
    cases helab with
    | mapp _ A_param mt _ _ ce1 ce2 h_elab1 h_elab2 =>
      obtain ⟨vc_clos, hbig1, helab_clos⟩ := ih1 h_elab1 henv henv_val
      obtain ⟨vc2, hbig2, helab_v2⟩ := ih2 h_elab2 henv henv_val
      cases helab_clos with
      | mclos _ _ _ _ _ _ _ _ hval_v1 h_env_v1 h_body_elab =>
        have hv1_val := eval_produces_value henv_val hstep1
        cases hv1_val with
        | vmclos hval_inner =>
          have hv2_val := eval_produces_value henv_val hstep2
          have hval_body_env := SCE.Value.vmrg hval_inner hv2_val
          have helab_body_env := elabExp.edmrg .top _ _ _ _ _ _
            h_env_v1 (value_typing_weakening hv2_val helab_v2)
          obtain ⟨vc_result, hbig3, helab_result⟩ := ih3 h_body_elab helab_body_env hval_body_env
          exact ⟨vc_result,
                 EBig.ebapp hbig1 hbig2 hbig3,
                 helab_result⟩
  | dmrg hval_ρ hstep1 hstep2 ih1 ih2 =>
    cases helab with
    | edmrg _ A_inner B_inner _ _ ce1 ce2 h_elab1 h_elab2 =>
      obtain ⟨vc1, hbig1, helab_v1⟩ := ih1 h_elab1 henv henv_val
      have hv1_val := eval_produces_value henv_val hstep1
      have hval_mrg := SCE.Value.vmrg henv_val hv1_val
      have helab_mrg_env := elabExp.edmrg .top _ _ _ _ _ _
        henv (value_typing_weakening hv1_val helab_v1)
      obtain ⟨vc2, hbig2, helab_v2⟩ := ih2 h_elab2 helab_mrg_env hval_mrg
      have hv2_val := eval_produces_value hval_mrg hstep2
      have helab_result := elabExp.edmrg .top _ _ _ _ _ _
        helab_v1 (value_typing_weakening hv2_val helab_v2)
      exact ⟨.mrg vc1 vc2, EBig.ebmrg hbig1 hbig2, helab_result⟩
  | nmrg hval_ρ hstep1 hstep2 ih1 ih2 =>
    cases helab with
    | enmrg _ A_inner B_inner _ _ ce1 ce2 h_elab1 h_elab2 =>
      obtain ⟨vc1, hbig1, helab_v1⟩ := ih1 h_elab1 henv henv_val
      obtain ⟨vc2, hbig2, helab_v2⟩ := ih2 h_elab2 henv henv_val
      have hv1_val := eval_produces_value henv_val hstep1
      have hv2_val := eval_produces_value henv_val hstep2
      have helab_result := elabExp.edmrg .top _ _ _ _ _ _
        helab_v1 (value_typing_weakening hv2_val helab_v2)
      exact ⟨.mrg vc1 vc2,
             nmrg_core_eval (elab_value henv henv_val) hbig1 hbig2,
             helab_result⟩
  | openm hval_ρ hstep1 hstep2 ih1 ih2 =>
    cases helab with
    | openm _ A_inner B_inner _ _ ce1 ce2 l_inner h_elab1 h_elab2 =>
      -- IH on e₁: produces lrec l v'
      obtain ⟨vc_rcd, hbig1, helab_rcd⟩ := ih1 h_elab1 henv henv_val
      -- extract inner value from lrec elaboration
      cases helab_rcd with
      | elrec _ _ _ vc_inner _ helab_inner =>
        -- build env for body: ρ ,, v'
        have hv'_val := eval_produces_value henv_val hstep1
        cases hv'_val with
        | vlrec hval_inner =>
          have hval_mrg := SCE.Value.vmrg henv_val hval_inner
          have helab_mrg_env := elabExp.edmrg .top _ _ _ _ _ _
            henv (value_typing_weakening hval_inner helab_inner)
          -- IH on e₂
          obtain ⟨vc_result, hbig2, helab_result⟩ := ih2 h_elab2 helab_mrg_env hval_mrg
          -- core big-step: app (lam ce2) (rproj ce1 l)
          exact ⟨vc_result,
                 EBig.ebapp
                   (EBig.ebclos (elab_value henv henv_val))
                   (EBig.ebsel hbig1 Core.RLookupV.rvlzero)
                   hbig2,
                 helab_result⟩
  | letb hval_ρ hstep1 hstep2 ih1 ih2 =>
    cases helab with
    | letb _ A_inner B_inner _ _ ce1 ce2 h_elab1 h_elab2 =>
      obtain ⟨vc1, hbig1, helab_v1⟩ := ih1 h_elab1 henv henv_val
      have hv1_val := eval_produces_value henv_val hstep1
      have hval_mrg := SCE.Value.vmrg henv_val hv1_val
      have helab_mrg_env := elabExp.edmrg .top _ _ _ _ _ _
        henv (value_typing_weakening hv1_val helab_v1)
      obtain ⟨vc_result, hbig2, helab_result⟩ := ih2 h_elab2 helab_mrg_env hval_mrg
      exact ⟨vc_result,
             EBig.ebapp (EBig.ebclos (elab_value henv henv_val)) hbig1 hbig2,
             helab_result⟩
  | mstruct_sandboxed hval_ρ hstep_body ih =>
    cases helab with
    | mstruct _ _ _ _ _ ce _ hs1 hs2 h_elab_body =>
      have hctx := hs1 rfl
      rw [hctx] at h_elab_body
      obtain ⟨vc, hbig, helab_v⟩ := ih h_elab_body (elabExp.eunit .top) SCE.Value.vunit
      exact ⟨vc, EBig.ebbox (EBig.ebunit (elab_value henv henv_val)) hbig, helab_v⟩
  | mstruct_open hval_ρ hstep_body ih =>
    cases helab with
    | mstruct _ _ _ _ _ ce _ hs1 hs2 h_elab_body =>
      have hctx := hs2 rfl
      rw [hctx] at h_elab_body
      obtain ⟨vc, hbig, helab_v⟩ := ih h_elab_body henv henv_val
      exact ⟨vc, EBig.ebbox (EBig.equery (elab_value henv henv_val)) hbig, helab_v⟩
  | mfunctor_sandboxed hval_ρ =>
    cases helab with
    | mfunctor _ ctxInner _ _ sb _ ce hs1 hs2 h_body =>
      have hctx := hs1 rfl
      rw [hctx] at h_body
      exact ⟨Core.Exp.clos .unit _ ce,
             EBig.ebbox (EBig.ebunit (elab_value henv henv_val))
                        (EBig.ebclos Value.vunit),
             elabExp.mclos .top _ _ _ _ _ _ _ Value.vunit (elabExp.eunit .top) h_body⟩
  | mfunctor_open hval_ρ =>
    cases helab with
    | mfunctor _ ctxInner _ _ sb _ ce hs1 hs2 h_body =>
      have hctx := hs2 rfl
      rw [hctx] at h_body
      exact ⟨Core.Exp.clos ρc _ ce,
             EBig.ebclos (elab_value henv henv_val),
             elabExp.mclos .top _ _ _ _ _ _ _ henv_val henv h_body⟩
  | lrec hval_ρ hstep ih =>
    cases helab with
    | elrec _ A_inner _ ce l h_elab =>
      obtain ⟨vc, hbig, helab_v⟩ := ih h_elab henv henv_val
      exact ⟨Core.Exp.lrec _ vc,
             EBig.ebrec hbig,
             elabExp.elrec .top _ _ _ _ helab_v⟩
  | rproj hval_ρ hstep hsel ih =>
    cases helab with
    | erproj _ A_inner B_inner _ ce l_inner h_elab h_slook =>
      obtain ⟨vc, hbig, helab_v⟩ := ih h_elab henv henv_val
      have hv_val := eval_produces_value henv_val hstep
      obtain ⟨vc', hrlookup_v, helab_v'⟩ :=
        sel_preservation hv_val helab_v hsel h_slook
      exact ⟨vc', EBig.ebsel hbig hrlookup_v, helab_v'⟩
  | mlink h1 bstep1 bstep2 sel1 step2 step3 ih1 ih2 =>
    rename_i _ e1 e2 v1 v2 vl v3 A_src body_src l_name
    cases helab with
    | mlink _ Γ₁ A_inner mt l_inner _ _ ce1 ce2 h_elab1 h_elab2 h_lookup =>
      obtain ⟨vc1, hbig1, helab_v1⟩ := step3 h_elab1 henv henv_val
      obtain ⟨vc2, hbig2, helab_v2⟩ := ih1 h_elab2 henv henv_val
      cases helab_v2 with
      | mclos _ _ _ _ _ _ _ _ hval_v2 h_env2 h_body =>
        rename_i ctx_inner ce1_inner ce2_inner
        have hv1_val := eval_produces_value henv_val bstep1
        obtain ⟨vc_l, hrlookup_v, helab_vl⟩ :=
          sel_preservation hv1_val helab_v1 sel1 h_lookup
        have hvl_val := source_sel_value hv1_val sel1
        have hval_lrec := SCE.Value.vlrec (l := l_name) hvl_val
        have hval_env := SCE.Value.vmrg hval_v2 hval_lrec
        have helab_lrec := elabExp.elrec .top _ _ _ l_name helab_vl
        have helab_lrec_weak :=
          value_typing_weakening (Γ₂ := SCE.Typ.and .top ctx_inner) hval_lrec helab_lrec
        have helab_env := elabExp.edmrg .top _ _ _ _ _ _ h_env2 helab_lrec_weak
        obtain ⟨vc3, hbig3, helab_v3⟩ := ih2 h_body helab_env hval_env
        have hv3_val := eval_produces_value hval_env step2
        have helab_v3_weak :=
          value_typing_weakening (Γ₂ := SCE.Typ.and .top Γ₁) hv3_val helab_v3
        have helab_result := elabExp.edmrg .top _ _ _ _ _ _
          helab_v1 helab_v3_weak
        exact ⟨.mrg vc1 vc3,
               linkedCore_eval (elab_value henv henv_val) hbig1 hbig2 hrlookup_v hbig3,
               helab_result⟩

theorem whole_program_correctness
    {A : SCE.Typ} {es : SCE.Exp} {ec : Core.Exp} {vs : SCE.Exp}
    (helab : elabExp SCE.Typ.top es A ec)
    (heval : S_Sem.BStep .unit es vs)
    : ∃ vc, EBig .unit ec vc ∧ elabExp SCE.Typ.top vs A vc := by
  exact semantic_preservation helab heval (elabExp.eunit SCE.Typ.top) SCE.Value.vunit

-- Linking and separate compilation

def linkSCE (e₁ e₂ : SCE.Exp) : SCE.Exp :=
  .mlink e₁ e₂

theorem core_link_typed
    {Γ A₁ A B : Core.Typ} {l : String} {ec₁ ec₂ ec : Core.Exp}
    (hlink : CoreLink Γ l A₁ A B ec₁ ec₂ ec)
    (h₁ : HasType Γ ec₁ A₁)
    (h₂ : HasType Γ ec₂ (.arr (.rcd l A) B))
    : HasType Γ ec (.and A₁ B) := by
  cases hlink with
  | link _ _ _ _ _ _ hrlookup =>
    simp [linkedCore]
    apply HasType.tapp
    · apply HasType.tlam
      apply HasType.tmrg
      · apply HasType.tbox
        · exact HasType.tproj HasType.tquery Lookup.zero
        · exact h₁
      · apply HasType.tbox
        · exact HasType.tproj HasType.tquery (Lookup.succ Lookup.zero)
        · exact HasType.tapp h₂ (HasType.trcd (HasType.trproj h₁ hrlookup))
    · exact HasType.tquery

theorem separate_compilation
    {Γ Γ₁ A B : SCE.Typ} {l : String}
    {es₁ es₂ : SCE.Exp} {ec₁ ec₂ ec : Core.Exp}
    {ρs vs : SCE.Exp} {ρc : Core.Exp}
    (helab₁ : elabExp Γ es₁ Γ₁ ec₁)
    (helab₂ : elabExp Γ es₂ (.sig (.TyArrM (.rcd l A) (.TyIntf B))) ec₂)
    (hlookup : SRLookup Γ₁ l A)
    (hlink : CoreLink (elabTyp Γ) l (elabTyp Γ₁) (elabTyp A) (elabTyp B) ec₁ ec₂ ec)
    (heval : S_Sem.BStep ρs (.mlink es₁ es₂) vs)
    (henv : elabExp SCE.Typ.top ρs Γ ρc)
    (henv_val : SCE.Value ρs)
    : ∃ vc, EBig ρc ec vc
           ∧ elabExp SCE.Typ.top vs (.and Γ₁ B) vc := by
  cases hlink with
  | link _ _ _ _ _ _ _ =>
    have hmlink := elabExp.mlink Γ Γ₁ A B l es₁ es₂ ec₁ ec₂ helab₁ helab₂ hlookup
    exact semantic_preservation hmlink heval henv henv_val
/-
Dynamic and Static linking at Source with first-class modules

Elaboration rules
  Γ ⊢ e1 : Γ₁ ⤳ e1'
  Γ ⊢ e2 : {l : A} →m B ⤳ e2'
  {l : A} ∈ Γ₁
  ----------------------------------------------
  Γ ⊢ linkₛ(e1, e2) : Γ₁ & B → linkc(e1, e2)

Semantics
  v ⊢ e1              => v1
  v ⊢ e2              => ⟨v', functor {l : A}, e3⟩m
  v1 ⊢ ?.l            => vₗ
  v' ,, {l = vₗ} ⊢ e3 => v3
  ----------------------------------------------
  v ⊢ linkₛ(e1, e2) => v1 ,, v3
-/
