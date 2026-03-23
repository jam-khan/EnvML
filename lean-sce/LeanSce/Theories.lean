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
    sorry

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
  · intro h
    sorry

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
    sorry
  -- induction h with
  -- | zero label T => exact Core.RLookup.zero
  -- | andl A B label T _ ⟨hlinA, hnotB⟩ ih =>
  --   exact Core.RLookup.landl ih
  --     ⟨type_safe_label_existence.mp hlinA,
  --      type_safe_label_nonexistence.mp hnotB⟩
  -- | andr A B label T _ ⟨hlinB, hnotA⟩ ih =>
  --   exact Core.RLookup.landr ih
  --     ⟨type_safe_label_nonexistence.mp hnotA,
  --      type_safe_label_existence.mp hlinB⟩
theorem val_trans_index_lookup
    {v : SCE.Exp} {A B : SCE.Typ} {cv : Core.Exp} {i : Nat} {v' : SCE.Exp}
    (hvt : ValTrans v A cv)
    (hlook : SCE.IndexLookup A i B)
    (hlookv : S_Sem.LookupV v i v')
    : ∃ cv', ValTrans v' B cv' ∧ C_Sem.LookupV cv i cv' := by
    sorry

theorem inference_uniqueness
    {Γ T₁ T₂ : SCE.Typ} {e : SCE.Exp} {ce₁ ce₂ : Core.Exp}
    (h₁ : elabExp Γ e T₁ ce₁)
    (h₂ : elabExp Γ e T₂ ce₂)
    : T₁ = T₂ := by
  induction h₁ generalizing T₂ ce₂ with
  | query ctx => cases h₂; rfl
  | lit ctx n => cases h₂; rfl
  | unit ctx => cases h₂; rfl
  | proj ctx A B se ce i _ hlook ih =>
    cases h₂ with
    | proj _ A₂ B₂ _ _ _ helab₂ hlook₂ =>
      have hA := ih helab₂
      subst hA
      exact index_lookup_uniqueness hlook hlook₂
  | lam ctx A B se ce hbody ih =>
    cases h₂ with
    | lam _ _ B₂ _ _ hbody₂ =>
      have hB := ih hbody₂
      subst hB; rfl
  | app ctx A B se1 se2 ce1 ce2 h1 h2 ih1 ih2 =>
    cases h₂ with
    | app _ A₂ B₂ _ _ _ _ h1₂ h2₂ =>
      have := ih1 h1₂
      -- arr A B = arr A₂ B₂ implies B = B₂
      cases this; rfl
  | dmrg ctx A B se1 se2 ce1 ce2 h1 h2 ih1 ih2 =>
    cases h₂ with
    | dmrg _ A₂ B₂ _ _ _ _ h1₂ h2₂ =>
      have hA := ih1 h1₂; subst hA
      have hB := ih2 h2₂; subst hB; rfl
  | nmrg ctx A B se1 se2 ce1 ce2 h1 h2 ih1 ih2 =>
    cases h₂ with
    | nmrg _ A₂ B₂ _ _ _ _ h1₂ h2₂ =>
      have hA := ih1 h1₂; subst hA
      have hB := ih2 h2₂; subst hB; rfl
  | lrec ctx A se ce l _ ih =>
    cases h₂ with
    | lrec _ A₂ _ _ _ helab₂ =>
      have := ih helab₂; subst this; rfl
  | rproj ctx A B se ce l hse hlook ih =>
    cases h₂ with
    | rproj _ A₂ B₂ _ _ _ hse₂ hlook₂ =>
      have hB := ih hse₂; subst hB
      exact record_lookup_uniqueness hlook hlook₂
  | box ctx ctx' A se1 se2 ce1 ce2 h1 h2 ih1 ih2 =>
    cases h₂ with
    | box _ ctx'₂ A₂ _ _ _ _ h1₂ h2₂ =>
      have hctx' := ih1 h1₂; subst hctx'
      exact ih2 h2₂
  | clos ctx ctx' A B se1 se2 ce1 ce2 h1 h2 ih1 ih2 =>
    cases h₂ with
    | clos _ ctx'₂ _ B₂ _ _ _ _ h1₂ h2₂ =>
      have hctx' := ih1 h1₂; subst hctx'
      have hB := ih2 h2₂; subst hB; rfl
  | _ => sorry

theorem elaboration_uniqueness
    {Γ T₁ T₂ : SCE.Typ} {e : SCE.Exp} {ce₁ ce₂ : Core.Exp}
    (h₁ : elabExp Γ e T₁ ce₁)
    (h₂ : elabExp Γ e T₂ ce₂)
    : ce₁ = ce₂ := by
  sorry -- follows same structure as inference_uniqueness

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
    sorry
  | box ctx ctx' A se1 se2 ce1 ce2 _ _ ih1 ih2 =>
    -- exact HasType.tbox ih1 ih2
    sorry
  | dmrg ctx A B se1 se2 ce1 ce2 _ _ ih1 ih2 =>
    exact HasType.tmrg ih1 ih2
  | lrec ctx A se ce l _ ih =>
    exact HasType.trcd ih
  | rproj ctx A B se ce l _ hlook ih =>
    exact HasType.trproj ih (type_safe_record_lookup hlook)
  | letb ctx A B se1 se2 ce1 ce2 _ _ ih1 ih2 =>
    sorry
    -- exact HasType.tapp (HasType.tlam ih2) ih1
  | openm ctx A B se1 se2 ce1 ce2 l _ _ ih1 ih2 =>
    sorry
    -- exact HasType.tapp (HasType.tlam ih2) (HasType.trproj ih1 (type_safe_record_lookup (SCE.RecordLookup.zero l A)))
  | clos ctx ctx' A B se1 se2 ce1 ce2 _ _ ih1 ih2 =>
    sorry -- need to show HasType for clos construct
  | nmrg ctx A B se1 se2 ce1 ce2 _ _ ih1 ih2 =>
    sorry
  | mstruct ctx ctxInner B sb se ce envCore _ _ _ ih =>
    sorry
  | mfunctor ctx ctxInner A B mt sb se ce _ _ _ ih =>
    sorry
  | mclos ctx ctx' A B mt se1 se2 ce1 ce2 _ _ ih1 ih2 =>
    sorry
  | mapp ctx A mt se1 se2 ce1 ce2 _ _ ih1 ih2 =>
    -- exact HasType.tapp ih1 ih2
    sorry
  | mlink ctx A mt se1 se2 ce1 ce2 _ _ ih1 ih2 =>
    sorry -- need to show mrg typing

-- ============================================================
-- Semantics Preservation (main theorem)
-- ============================================================

theorem semantics_preservation
    {Γ A : SCE.Typ}
    {es : SCE.Exp} {ec : Core.Exp}
    {rs vs : SCE.Exp}
    {cr : Core.Exp}
    {hv1 : Core.Value cr}
    {hv2 : SCE.Value vs}
    {hv3 : SCE.Value rs}
    {hv4 : Core.Value cv}
    (helab : elabExp Γ es A ec)
    (heval : S_Sem.BStep rs es vs)
    (henv  : ValTrans rs Γ cr)
    : ∃ cv, ValTrans vs A cv ∧ C_Sem.EBig cr ec cv := by
  induction helab generalizing rs vs cr with
  | query ctx =>
    cases heval with
    | query hv =>
      exists cr
      constructor
      · assumption
      · refine C_Sem.EBig.equery ?_
        assumption
  | lit ctx n =>
    cases heval with
    | lit hv =>
      exists (Core.Exp.lit n)
      constructor
      · exact ValTrans.vint
      · exact C_Sem.EBig.eblit hv1
  | unit ctx =>
    cases heval with
    | unit hv =>
      exists Core.Exp.unit
      constructor
      · exact ValTrans.vunit
      · exact C_Sem.EBig.ebunit hv1
  | clos ctx v A body hp hv hce1 hce2 ihel1 ihel2 ih1 ih2 =>
      sorry
  | mclos ctx A A' B mty se1 se2 ce1 ce2 ihel1 ihel2 ih1 ih2 =>
      sorry
  | proj ctx A B se ce i he hlook ih =>
    cases heval with
    | proj hv heval_inner hlookv =>
        rename_i vi
        have hv_vi : SCE.Value vi := by
          · sorry
        obtain ⟨cv_mid, hvt_mid, hceval_mid⟩ :=
          ih (hv1 := hv1) (hv2 := hv_vi) (hv3 := hv3) heval_inner henv
        obtain ⟨cv', hvt', hlookv_core⟩ :=
          val_trans_index_lookup hvt_mid hlook hlookv
        exact ⟨cv', hvt', C_Sem.EBig.ebproj hceval_mid hlookv_core⟩
  | lam ctx A B se ce elh ih =>
    cases heval with
    | lam hv =>
      sorry
  | box ctx e1 e2 v1 v ce1 ce2 ihel1 ihel2 ih1 ih2 =>
    sorry
  | lrec ctx A se ce l he ih =>
      cases heval with
      | lrec hv heval_inner =>
          rename_i vi
          have hv_inner : SCE.Value vi := by cases hv2; assumption
          obtain ⟨cv', hvt, hceval⟩ := ih (hv1 := hv1) (hv2 := hv_inner) (hv3 := hv3) heval_inner henv
          exact ⟨Core.Exp.lrec l cv', ValTrans.vlrec hvt, C_Sem.EBig.ebrec hceval⟩
  | app ctx A B se1 se2 ce1 ce2 elh1 elh2 ih1 ih2 =>
    cases heval with
    | app_clos hv heval1 heval2 heval_body =>
        sorry
  | mapp ctx A mty se1 se2 ce1 ce2 ihe1 ihe2 ih1 ih2 =>
    sorry
  | dmrg ctx A B se1 se2 ce1 ce2 _ _ ih1 ih2 =>
    cases heval with
    | dmrg hv heval1 heval2 =>
      sorry
  | _ => sorry -- remaining cases

/-
  Γ ⊢ e₁ : Sig(A →ₘ mt) ⤳ ce₁        (compile functor separately)
  Γ ⊢ e₂ : A ⤳ ce₂                   (compile argument separately)
  ρˢ ⊢ˢ link(e₁, e₂) ⇓ vˢ            (source-level linking)
  ρˢ : Γ ↝ cρ
  ⟹  ∃ cv,  vˢ : Sig(A →ₘ mt) ↝ cv  ∧  cρ ⊢ᶜ ce₂ ,, (ce₁ ce₂) ⇓ cv
-/
theorem separate_compilation
    {Γ A : SCE.Typ} {mt : SCE.ModTyp}
    {e₁ e₂ : SCE.Exp} {ce₁ ce₂ : Core.Exp}
    {rs vs : SCE.Exp} {cr : Core.Exp}
    (h₁ : elabExp Γ e₁ (.sig (.TyArrM A mt)) ce₁)
    (h₂ : elabExp Γ e₂ A ce₂)
    (heval : S_Sem.BStep rs (.mlink e₁ e₂) vs)
    (henv : ValTrans rs Γ cr)
    : ∃ cv, ValTrans vs (.sig (.TyArrM A mt)) cv
          ∧ C_Sem.EBig cr (.mrg ce₂ (.app ce₁ ce₂)) cv := by
  have hmlink : elabExp Γ (.mlink e₁ e₂) (.sig (.TyArrM A mt))
      (.mrg ce₂ (.app ce₁ ce₂)) :=
    elabExp.mlink _ _ _ _ _ _ _ h₁ h₂
  exact semantics_preservation hmlink heval henv
