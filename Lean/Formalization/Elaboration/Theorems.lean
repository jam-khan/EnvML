import Formalization.Elaboration.Rules

theorem TypeElaborationUniqueness : ∀ (ST : ENVCAP.Typ) (CT₁ CT₂ : LambdaE.Typ),
    ENVCAP.ElaborateType ST = CT₁ →
    ENVCAP.ElaborateType ST = CT₂ →
    CT₁ = CT₂ := by 
  intro ST CT₁ CT₂ h1 h2;
  rw [← h1];
  rw [← h2];

theorem TypeSafeIndexLookup : ∀ (ST₁ ST₂ : ENVCAP.Typ) (n : Nat), 
    ENVCAP.IndexLookup ST₁ n ST₂ → 
    LambdaE.IndexLookup (ENVCAP.ElaborateType ST₁) n (ENVCAP.ElaborateType ST₂) := by
      intro ST₁ n ST₂ H;
      induction H with
      | zero A B =>
          apply LambdaE.IndexLookup.zero;
      | succ A B n C _ IH =>
          rw [ENVCAP.ElaborateType];
          apply LambdaE.IndexLookup.succ;  
          apply IH;
        
theorem TypeSafeLabelExistence: ∀ (label : String) (ST : ENVCAP.Typ),
    ENVCAP.LabelIn label ST ↔ 
    LambdaE.LabelIn label (ENVCAP.ElaborateType ST) := by
      intro label ST;
      apply Iff.intro;
      · intro H;
        induction H with
        | rcd label T =>
            rw [ENVCAP.ElaborateType];
            apply LambdaE.LabelIn.rcd;
        | andl A B label _ IH =>
            rw [ENVCAP.ElaborateType];
            apply LambdaE.LabelIn.andl;
            apply IH;
        | andr A B label _ IH =>
            rw [ENVCAP.ElaborateType];
            apply LambdaE.LabelIn.andr;
            apply IH;
      · intro H;
        induction ST with
        | rcd labelA T IH => 
            rw [ENVCAP.ElaborateType] at H;
            cases H
            apply ENVCAP.LabelIn.rcd
        | and A B IH1 IH2 => 
            rw [ENVCAP.ElaborateType] at H;
            cases H with
            | andl _ _ _ H1 =>
                apply ENVCAP.LabelIn.andl;
                apply IH1;
                apply H1;
            | andr _ _ _ H2 =>
                apply ENVCAP.LabelIn.andr;
                apply IH2;
                apply H2;
        | _ => cases H

theorem TypeSafeLabelNonExistence : ∀ (label : String) (ST : ENVCAP.Typ),
    ¬ ENVCAP.LabelIn label ST ↔ 
    ¬ LambdaE.LabelIn label (ENVCAP.ElaborateType ST) := by
      intro label ST;
      apply Iff.intro;
      · intro H1 H2;
        have H3 := TypeSafeLabelExistence label ST;
        apply H1;
        apply H3.mpr;
        apply H2;
      · intro H1 H2;
        have H3 := TypeSafeLabelExistence label ST;
        apply H1;
        apply H3.mp;
        apply H2;

theorem TypeSafeRecordLookup : ∀ (ST₁ ST₂: ENVCAP.Typ) (label : String),  
    ENVCAP.RecordLookup ST₁ label ST₂ → 
    LambdaE.RecordLookup (ENVCAP.ElaborateType ST₁) label (ENVCAP.ElaborateType ST₂) := by
      intro ST₁ label ST₂ H;
      induction H with
      | zero label T =>
          apply LambdaE.RecordLookup.zero;
      | andl A B label T H1 H2 IH =>
          rw [ENVCAP.ElaborateType];
          apply LambdaE.RecordLookup.andl;
          · apply IH;
          · apply And.intro
            · rw [← TypeSafeLabelExistence label A];
              apply H2.left;
            · rw [← TypeSafeLabelNonExistence label B];
              apply H2.right;
      | andr A B label T H1 H2 IH =>
          rw [ENVCAP.ElaborateType];
          apply LambdaE.RecordLookup.andr;
          · apply IH;
          · apply And.intro
            · rw [← TypeSafeLabelExistence label B];
              apply H2.left;
            · rw [← TypeSafeLabelNonExistence label A];
              apply H2.right;

theorem TypePreservation : ∀ (EnvT ST : ENVCAP.Typ) (e : ENVCAP.Exp) (_ : LambdaE.Typ) (ce : LambdaE.Exp),
    ENVCAP.ElaborateExp EnvT e ST ce →
    LambdaE.HasType (ENVCAP.ElaborateType EnvT) ce (ENVCAP.ElaborateType ST) := by
      intro EnvT ST e CT ce H;
      induction H with
      | ctx EnvT => apply LambdaE.HasType.ctx;
      | int EnvT n => apply LambdaE.HasType.int;
      | unit EnvT => apply LambdaE.HasType.unit;
      | proj EnvT A B n e ce H1 H2 IH =>
          apply LambdaE.HasType.proj; 
          · apply IH;
          · apply TypeSafeIndexLookup;
            apply H2;
      | lam EnvT A B e ce H IH => 
          apply LambdaE.HasType.lam;
          apply IH;
      | box EnvT EnvT₁ A e₁ e₂ ce₁ ce₂ H1 H2 IH1 IH2 => 
          apply LambdaE.HasType.box;
          · apply IH1;
          · apply IH2;
      | clos EnvT EnvT₁ A B e env ce cenv H1 H2 IH1 IH2 => 
          rw [ENVCAP.ElaborateType];
          apply LambdaE.HasType.box;
          · apply IH1;
          · apply LambdaE.HasType.lam;
            apply IH2;
      | app EnvT A B e₁ e₂ ce₁ ce₂ H1 H2 IH1 IH2 =>
          apply LambdaE.HasType.app;
          · apply IH1;
          · apply IH2;
      | dmrg EnvT A B e₁ e₂ ce₁ ce₂ H1 H2 IH1 IH2 =>
          apply LambdaE.HasType.mrg;
          · apply IH1;
          · apply IH2;
      | ndmrg EnvT A B e₁ e₂ ce₁ ce₂ H1 H2 IH1 IH2 =>
          apply LambdaE.HasType.app;
          · apply LambdaE.HasType.lam;
            apply LambdaE.HasType.mrg;
            · apply LambdaE.HasType.box;
              · apply LambdaE.HasType.proj;
                · apply LambdaE.HasType.ctx;
                · apply LambdaE.IndexLookup.zero;
              · apply IH1;
            · apply LambdaE.HasType.box;
              · apply LambdaE.HasType.proj;
                · apply LambdaE.HasType.ctx;
                · apply LambdaE.IndexLookup.succ;
                  · apply LambdaE.IndexLookup.zero;
              · apply IH2;
          · apply LambdaE.HasType.ctx;
      | struct EnvT A B e ce H IH =>
          apply LambdaE.HasType.box;
          · apply LambdaE.HasType.unit;
          · rw [ENVCAP.ElaborateType];
            apply LambdaE.HasType.lam;
            apply IH;
      | modapp EnvT A B e₁ e₂ ce₁ ce₂ H1 H2 IH1 IH2 =>
          apply LambdaE.HasType.app;
          · apply IH1;
          · apply IH2;
      | lrec EnvT A e ce label H IH =>            
          apply LambdaE.HasType.rcd;
          apply IH;
      | rproj EnvT A B e ce label H1 H2 IH =>
          apply LambdaE.HasType.rproj;
          · apply IH;
          · apply TypeSafeRecordLookup;
            apply H2;
      | slet EnvT A B e₁ e₂ ce₁ ce₂ H1 H2 IH1 IH2 =>
          apply LambdaE.HasType.app; 
          · apply LambdaE.HasType.lam;
            apply IH2;
          · apply IH1;
      | sopen EnvT A B e₁ e₂ ce₁ ce₂ label H1 H2 H3 IH1 IH2 IH3 IH4 =>
          apply LambdaE.HasType.app; 
          · apply LambdaE.HasType.lam;
            apply IH4;
          · apply LambdaE.HasType.rproj;
            · apply IH2;
            · apply TypeSafeRecordLookup;
              apply ENVCAP.RecordLookup.zero

theorem SlookupUniqueness : ∀ (EnvT T₁ T₂: ENVCAP.Typ) (n : Nat),
    ENVCAP.IndexLookup EnvT n T₁ →
    ENVCAP.IndexLookup EnvT n T₂ →
    T₁ = T₂ := by
      intro EnvT T₁ T₂ n H1 H2;
      induction H1 with
      | zero A B =>
          cases H2;
          rfl;
      | succ A B n C H IH =>
        apply IH;
        cases H2 with
        | succ _ _ _ _ h => exact h  

theorem RLookupUniqueness : ∀ (RT T₁ T₂: ENVCAP.Typ) (label : String),
    ENVCAP.RecordLookup RT label T₁ →
    ENVCAP.RecordLookup RT label T₂ →
    T₁ = T₂ := by
      intro RT T₁ T₂ label H1 H2;
      induction H1 with
      | zero label T =>
          cases H2;
          rfl;
      | andl A B label T H3 H4 IH =>
        apply IH;
        cases H2 with
        | andl _ _ _ _ h1 h2 => apply h1
        | andr _ _ _ _ h1 h2 => 
          cases H4 with | intro ha hb =>
          cases h2 with | intro hc hd =>
          exfalso; apply hb; apply hc
      | andr A B label T H3 H4 IH => 
        apply IH;
        cases H2 with
        | andr _ _ _ _ h1 h2 => apply h1
        | andl _ _ _ _ h1 h2 => 
          cases H4 with | intro ha hb =>
          cases h2 with | intro hc hd =>
          exfalso; apply hb; apply hc

theorem InferenceUniqueness : ∀ (EnvT T₁ T₂ : ENVCAP.Typ) (e : ENVCAP.Exp) (ce₁ ce₂ : LambdaE.Exp),
    ENVCAP.ElaborateExp EnvT e T₁ ce₁ →
    ENVCAP.ElaborateExp EnvT e T₂ ce₂ →
    T₁ = T₂ := by
      intro EnvT T₁ T₂ e ce₁ ce₂ H1 H2;
      revert T₂;
      revert ce₂;
      induction H1 with
      | ctx EnvT =>
          intro ce₂ T₂ H2;
          cases H2;
          rfl;
      | int EnvT n =>
          intro ce₂ T₂ H2;
          cases H2;
          rfl;
      | unit EnvT =>
          intro ce₂ T₂ H2;
          cases H2;
          rfl;
      | proj EnvT A B n e ce H1 H2 IH =>
          intro ce₂ T₂ H3;
          cases H3 with
          | proj _ a' _ _ _ ce' H4 H5 =>
              have hA : A = a' := by apply IH; apply H4;
              rw [hA] at H2;
              apply SlookupUniqueness a' B T₂ n;
              · apply H2;
              · apply H5;
      | lam EnvT A B e ce H IH => 
          intro ce₂ T₂ H2;
          cases H2 with
          | lam _ _ b' _ ce' h =>
              have hA : B = b' := by apply IH; apply h;
              rw [hA];
      | box EnvT EnvT₁ A e₁ e₂ ce₁ ce₂ H1 H2 IH1 IH2 => 
          intro ce' T' H3;
          cases H3 with
          | box _ en _ _ _ ce1' ce2' h1 h2 =>
            have hA : EnvT₁ = en :=  by apply IH1; apply h1;
            rw [hA] at IH2;
            apply IH2;
            apply h2;
      | clos EnvT EnvT₁ A B e env ce cenv H1 H2 IH1 IH2 =>
          intro ce' T' H3;
          cases H3 with
          | clos _ et _ bT _ _ ce1' cenv' h1 h2 =>
            have hA : EnvT₁ = et := by apply IH1; apply h1;
            have hB : B = bT := by apply IH2;  rw [hA]; apply h2;
            rw [hB];
      | app EnvT A B e₁ e₂ ce₁ ce₂ H1 H2 IH1 IH2 =>
          intro ce' T' H3;
          cases H3 with
          | app _ a' _ _ _ ce1' ce2' h1 h2 =>
            have hA : ENVCAP.Typ.arr A B = ENVCAP.Typ.arr a' T' := by apply IH1; apply h1;
            cases hA;
            rfl;
      | dmrg EnvT A B e₁ e₂ ce₁ ce₂ H1 H2 IH1 IH2 =>
          intro ce' T' H3;
          cases H3 with
          | dmrg _ a' b' _ _ ce1' ce2' h1 h2 =>
            have hA : A = a' := by apply IH1; apply h1;
            have hB : B = b' := by rw [hA] at IH2; apply IH2; apply h2;
            rw [hA, hB];
      | ndmrg EnvT A B e₁ e₂ ce₁ ce₂ H1 H2 IH1 IH2 =>
          intro ce' T' H3;
          cases H3 with
          | ndmrg _ a' b' _ _ ce1' ce2' h1 h2 =>
            have hA : A = a' := by apply IH1; apply h1;
            have hB : B = b' := by apply IH2; apply h2;
            rw [hA, hB];
      | struct EnvT A B e ce H IH => 
          intro ce' T' H2;
          cases H2 with
          | struct _ a' b' _ ce1' h =>
              have hA : B = b' := by apply IH; apply h;
              rw [hA];
      | modapp EnvT A B e₁ e₂ ce₁ ce₂ H1 H2 IH1 IH2 =>
          intro ce' T' H3;
          cases H3 with
          | modapp _ a' _ _ _ ce1' ce2' h1 h2 =>
            have hA : A = a' := by apply IH2; apply h2;
            have hB : ENVCAP.Typ.sig A B = ENVCAP.Typ.sig a' T' := by apply IH1; apply h1;
            cases hB;
            rfl;
      | lrec EnvT A e ce label H IH => 
          intro ce' T' H2;
          cases H2 with
          | lrec _ a' _ ce1' label h =>
              have hA : A = a' := by apply IH; apply h;
              rw [hA];
      | rproj EnvT A B e ce label H1 H2 IH => 
          intro ce' T' H3;
          cases H3 with
          | rproj _ a' b' _ ce1' _ h1 h2 =>
            have hA : B = b' := by apply IH; apply h1;
            apply RLookupUniqueness; 
            · apply H2;
            · rw [hA];
              apply h2;
      | slet EnvT A B e₁ e₂ ce₁ ce₂ H1 H2 IH1 IH2 =>
          intro ce' T' H3;
          cases H3 with
          | slet _ _ b' _ _ ce1' ce2' h1 h2 =>
            apply IH2;
            apply h2;
      | sopen EnvT A B e₁ e₂ ce₁ ce₂ label H1 H2 H3 IH1 IH2 IH3 IH4 =>
          intro ce' T' H5;
          cases H5 with
          | sopen _ a' b' _ _ ce1' ce2' label' h1 h2 h3 h4 =>
            have hA : ENVCAP.Typ.rcd label A = ENVCAP.Typ.rcd label' a' := by apply IH2; apply h2;
            cases hA;
            apply IH4;
            apply h4;

theorem ElaborationUniqueness : ∀ (EnvT T₁ T₂ : ENVCAP.Typ) (e : ENVCAP.Exp) (ce₁ ce₂ : LambdaE.Exp),
    ENVCAP.ElaborateExp EnvT e T₁ ce₁ →
    ENVCAP.ElaborateExp EnvT e T₂ ce₂ →
    ce₁ = ce₂ := by
      intro EnvT T₁ T₂ e ce₁ ce₂ H1 H2;
      revert T₂;
      revert ce₂;
      induction H1 with
      | ctx EnvT =>
          intro ce₂ T₂ H2;
          cases H2;
          rfl;
      | int EnvT n =>
          intro ce₂ T₂ H2;
          cases H2;
          rfl;
      | unit EnvT =>
          intro ce₂ T₂ H2;
          cases H2;
          rfl;
      | proj EnvT A B n e ce H1 H2 IH =>
          intro ce₂ T₂ H3;
          cases H3 with
          | proj _ a' _ _ _ ce' H4 H5 =>
              have hA : ce = ce' := by apply IH; apply H4;
              rw [hA];
      | lam EnvT A B e ce H IH => 
          intro ce₂ T₂ H2;
          cases H2 with
          | lam _ _ b' _ ce' h =>
              have hA : ce = ce' := by apply IH; apply h;
              rw [hA];
      | box EnvT EnvT₁ A e₁ e₂ ce₁ ce₂ H1 H2 IH1 IH2 => 
          intro ce' T' H3;
          cases H3 with
          | box _ en _ _ _ ce1' ce2' h1 h2 =>
            have hA : ce₁ = ce1' := by apply IH1; apply h1;
            have hB : EnvT₁ = en := by apply InferenceUniqueness EnvT EnvT₁ en e₁ ce₁ ce1'; apply H1; apply h1; 
            have hC : ce₂ = ce2' :=  by apply IH2; rw [hB]; apply h2;
            rw [hA, hC];
      | clos EnvT EnvT₁ A B e env ce cenv H1 H2 IH1 IH2 =>
          intro ce' T' H3;
          cases H3 with
          | clos _ et _ bT _ _ ce1' cenv' h1 h2 =>
            have hA : cenv = cenv' := by apply IH1; apply h1;
            have hB : EnvT₁ = et := by apply InferenceUniqueness EnvT EnvT₁ et env cenv cenv'; apply H1; apply h1;
            have hC : ce = ce1' := by apply IH2;  rw [hB]; apply h2; 
            rw [hA, hC];
      | app EnvT A B e₁ e₂ ce₁ ce₂ H1 H2 IH1 IH2 =>
          intro ce' T' H3;
          cases H3 with
          | app _ a' _ _ _ ce1' ce2' h1 h2 =>
            have hA : ce₁ = ce1' := by apply IH1; apply h1;
            have hB : ce₂ = ce2' := by apply IH2; apply h2;
            rw [hA, hB];
      | dmrg EnvT A B e₁ e₂ ce₁ ce₂ H1 H2 IH1 IH2 =>
          intro ce' T' H3;
          cases H3 with
          | dmrg _ a' b' _ _ ce1' ce2' h1 h2 =>
            have hA : ce₁ = ce1' := by apply IH1; apply h1;
            have hB : A = a' := by apply InferenceUniqueness EnvT A a' e₁ ce₁ ce1'; apply H1; apply h1;
            have hC : ce₂ = ce2' := by apply IH2; rw [hB]; apply h2;
            rw [hA, hC];
      | ndmrg EnvT A B e₁ e₂ ce₁ ce₂ H1 H2 IH1 IH2 =>
          intro ce' T' H3;
          cases H3 with
          | ndmrg _ a' b' _ _ ce1' ce2' h1 h2 =>
            have hA : ce₁ = ce1' := by apply IH1; apply h1;
            have hB : ce₂ = ce2' := by apply IH2; apply h2;
            rw [hA, hB];
      | struct EnvT A B e ce H IH => 
          intro ce' T' H2;
          cases H2 with
          | struct _ a' b' _ ce1' h =>
              have hA : ce = ce1' := by apply IH; apply h;
              rw [hA];
      | modapp EnvT A B e₁ e₂ ce₁ ce₂ H1 H2 IH1 IH2 =>
          intro ce' T' H3;
          cases H3 with
          | modapp _ a' _ _ _ ce1' ce2' h1 h2 =>
            have hA : ce₂ = ce2' := by apply IH2; apply h2;
            have hB : ce₁ = ce1' := by apply IH1; apply h1;
            rw [hA, hB];
      | lrec EnvT A e ce label H IH => 
          intro ce' T' H2;
          cases H2 with
          | lrec _ a' _ ce1' label h =>
              have hA : ce = ce1' := by apply IH; apply h;
              rw [hA];
      | rproj EnvT A B e ce label H1 H2 IH => 
          intro ce' T' H3;
          cases H3 with
          | rproj _ a' b' _ ce1' _ h1 h2 =>
            have hA : ce = ce1' := by apply IH; apply h1;
            rw [hA];
      | slet EnvT A B e₁ e₂ ce₁ ce₂ H1 H2 IH1 IH2 =>
          intro ce' T' H3;
          cases H3 with
          | slet _ _ b' _ _ ce1' ce2' h1 h2 =>
            have hA : ce₂ = ce2' := by apply IH2; apply h2;
            have hB : ce₁ = ce1' := by apply IH1; apply h1;
            rw [hA, hB];
      | sopen EnvT A B e₁ e₂ ce₁ ce₂ label H1 H2 H3 IH1 IH2 IH3 IH4 =>
          intro ce' T' H5;
          cases H5 with
          | sopen _ a' b' _ _ ce1' ce2' label' h1 h2 h3 h4 =>
            have hA : ENVCAP.Typ.rcd label A = ENVCAP.Typ.rcd label' a' := by apply InferenceUniqueness EnvT (ENVCAP.Typ.rcd label A) (ENVCAP.Typ.rcd label' a') e₁ ce₁ ce1'; apply H2; apply h2;
            cases hA;
            have hB : ce₁ = ce1' := by apply IH2; apply h2;
            have hC : ce₂ = ce2' := by apply IH4; apply h4;
            rw [hB, hC];
