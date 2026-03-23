
import LeanSce.Core.Syntax
import LeanSce.Core.Semantics
import LeanSce.Core.Typing

open Core C_Sem

@[simp]
theorem value_weaken
  {E A : Typ} { v : Exp} :
  HasType E v A →
  ∀ {E' : Typ},
    Value v
    → HasType E' v A := by
  intro htype
  induction htype with
  | tint          => intro _ _; exact .tint
  | tunit         => intro _ _; exact .tunit
  | trcd ht ih    => intro _ hv; cases hv; exact .trcd (ih ‹_›)
  | tlam _        => intro _ hv; cases hv
  | tquery        => intro _ hv; cases hv
  | tapp _ _      => intro _ hv; cases hv
  | tbox _ _      => intro _ hv; cases hv
  | tproj _ _     => intro _ hv; cases hv
  | trproj _ _    => intro _ hv; cases hv
  | tmrg h1 h2 ih1 ih2 =>
    intro _ hv
    cases hv with
    | vmrg hv1 hv2 => exact .tmrg (ih1 hv1) (ih2 hv2)
  | tclos hv' ht' hb ih1 ih2 =>
    rename_i Γ₁ Γ₂ A' B' v₀ e₀
    intro E' hv
    apply HasType.tclos <;> assumption

@[simp]
theorem lookupv_value:
  ∀ {v v' : Exp} {n : Nat},
    LookupV v n v'
    → Value v
    → Value v' := by
  intro v v' n hlook hval
  induction hlook with
  | lvzero =>
    cases hval <;> try assumption
  | lvsucc =>
    cases hval with
    | vmrg hv1 _ =>
      rename_i v1 v2 v3 n ih11 ih12 hv2
      apply ih12
      assumption

@[simp]
theorem lookup_pres_ctx {E n A}:
  Lookup E n A
  → ∀ v v',
    LookupV v n v'
    → Value v
    → HasType .top v E
    → HasType E v' A := by
  intro hl
  induction hl with
  | zero =>
    intro v v' hlv hv ht
    cases hlv
    cases ht with
    | tmrg h1 h2 =>
      cases hv with
      | vmrg hv1 hv2 =>
        exact value_weaken h2 hv2
  | succ hl' ih =>
    intro v v' hlv hv ht
    cases hlv with
    | lvsucc hlv' =>
      cases ht with
      | tmrg h1 h2 =>
        cases hv with
        | vmrg hv1 hv2 =>
          rename_i v1 v2
          have h := ih v1 _ hlv' hv1 (value_weaken h1 hv1)
          exact value_weaken h (lookupv_value hlv' hv1)

@[simp]
theorem lookup_pres {E n A} :
  Lookup E n A
  → ∀ v v',
    LookupV v n v'
    → Value v
    → HasType .top v E
    → HasType .top v' A := by
  intro hl v v' hlv hv ht
  have h := lookup_pres_ctx hl v v' hlv hv ht
  exact value_weaken h (lookupv_value hlv hv)

@[simp]
theorem rlookupv_value {v l v'} :
  RLookupV v l v'
  → Value v
  → Value v' := by
  intro hl hv
  induction hl with
  | rvlzero => cases hv; assumption
  | vlandl _ ih => cases hv with
    | vmrg hv1 hv2 => exact ih hv1
  | vlandr _ ih => cases hv with
    | vmrg hv1 hv2 => exact ih hv2

@[simp]
theorem rcd_shape {E v l B} :
  HasType E v (.rcd l B)
  → Value v
  → ∃ v', v = .lrec l v' := by
  intro ht hv
  cases ht with
  | trcd => exact ⟨_, rfl⟩
  | tquery => cases hv
  | tapp _ _ => cases hv
  | tbox _ _ => cases hv
  | tproj _ _ => cases hv
  | trproj _ _ => cases hv


@[simp]
theorem notin_false {E v A} :
  HasType E v A
  → ∀ l v',
      RLookupV v l v'
      → ¬ Lin l A
      → False := by
  intro ht
  induction ht with
  | tint => intro l v' hr; cases hr
  | tunit => intro l v' hr; cases hr
  | tquery => intro l v' hr; cases hr
  | tlam _ => intro l v' hr; cases hr
  | tapp _ _ => intro l v' hr; cases hr
  | tbox _ _ => intro l v' hr; cases hr
  | tproj _ _ => intro l v' hr; cases hr
  | trproj _ _ => intro l v' hr; cases hr
  | trcd ht ih =>
    intro l v' hr hnl
    cases hr with
    | rvlzero => exact hnl .rcd
  | tmrg h1 h2 ih1 ih2 =>
    intro l v' hr hnl
    cases hr with
    | vlandl hr' =>
      exact ih1 l _ hr' (fun hlin => hnl (.andl hlin))
    | vlandr hr' =>
      exact ih2 l _ hr' (fun hlin => hnl (.andr hlin))
  | tclos _ _ _ => intro l v' hr; cases hr

@[simp]
theorem rlookup_pres_aux {E l A} :
    RLookup E l A
    → ∀ {v v'},
      RLookupV v l v'
      → Value v
      → HasType .top v E
      → HasType E v' A := by
  intro hl
  induction hl with
  | zero =>
    intro v v' hlv hv ht
    cases ht with
    | tapp _ _ => cases hv
    | tbox _ _ => cases hv
    | tproj _ _ => cases hv
    | trproj _ _ => cases hv
    | trcd ht' =>
      cases hlv with
      | rvlzero =>
        cases hv with
        | vrcd hv' =>
          exact value_weaken ht' hv'
  | landl hrl hnl ih =>
    intro v v' hlv hv ht
    cases hlv with
    | vlandl hlv' =>
      cases ht with
      | tmrg h1 h2 =>
        cases hv with
        | vmrg hv1 hv2 =>
          have h := ih hlv' hv1 (value_weaken h1 hv1)
          exact value_weaken h (rlookupv_value hlv' hv1)
    | vlandr hlv' =>
      cases ht with
      | tmrg h1 h2 =>
        cases hv with
        | vmrg hv1 hv2 =>
          have : False := notin_false h2 _ _ hlv' hnl
          contradiction
    | rvlzero =>
      cases ht
  | landr hrl hnla ih =>
    intro v v' hlv hv ht
    cases hlv with
    | vlandl hlv' =>
      cases ht with
      | tmrg h1 h2 =>
        cases hv with
        | vmrg hv1 hv2 =>
          have : False := notin_false h1 _ _ hlv' hnla.1
          contradiction
    | vlandr hlv' =>
      cases ht with
      | tmrg h1 h2 =>
        cases hv with
        | vmrg hv1 hv2 =>
          have h := ih hlv' hv2 (value_weaken h2 hv2)
          exact value_weaken h (rlookupv_value hlv' hv2)
    | rvlzero =>
      cases ht

@[simp]
theorem rlookup_pres {E l A} :
  RLookup E l A
  → ∀ {v v'},
      RLookupV v l v'
      → Value v
      → HasType .top v E
      → HasType .top v' A := by
  intro hl v v' hlv hv ht
  have h := rlookup_pres_aux hl hlv hv ht
  exact value_weaken h (rlookupv_value hlv hv)

@[simp]
theorem gpreservation
  {e e' v : Exp}
  (hstep : Step v e e') :
  ∀ {E A : Typ},
  HasType E e A
  → HasType .top v E
  → HasType E e' A
  := by
  induction hstep with
  | squery heval =>
    rename_i v
    intro E A htype henv
    cases htype
    apply value_weaken; try assumption
    assumption
  | sappl hv hstep ih1 =>
    rename_i v v' e1 e2
    intro E A htype henv
    cases htype with
    | tapp ht1 ht2 =>
      apply HasType.tapp
      · exact ih1 ht1 henv
      · assumption
  | sboxl hv hstep ih1 =>
    rename_i v1 v2 v3 v4
    intro E A htype henv
    cases htype with
    | tbox ih2 ih3 =>
      rename_i Γ Γ₁
      apply HasType.tbox <;> try assumption
      apply ih1
      repeat assumption
  | smrgl hv hstep ih1 =>
    rename_i v1 v2 v3 v4
    intro E A htype henv
    cases htype with
    | tmrg ih2 ih3 =>
        rename_i A B
        apply HasType.tmrg <;> try apply ih1
        repeat assumption
  | sappr hv hv1 hstep ih1 =>
    rename_i v1 v2 v3 v4
    intro E A htype henv
    cases htype with
    | tapp ht1 ht2 =>
      apply HasType.tapp
      · assumption
      · apply ih1<;> assumption
  | sboxr hv hstep ih1 ih2 =>
    rename_i v1 v2 v3 v4
    intro E A htype henv
    cases htype with
    | tbox ih3 ih4 =>
      rename_i Γ₁ B
      apply HasType.tbox <;> try assumption
      apply ih2
      repeat assumption
      apply value_weaken <;> try assumption
  | smrgr hv1 hv2 hstep ih1 =>
    rename_i v1 v2 v3 v4
    intro E A htype henv
    cases htype with
    | tmrg ih2 ih3 =>
        rename_i A B
        apply HasType.tmrg
        · assumption
        · apply ih1
          · assumption
          · apply HasType.tmrg
            · assumption
            · exact value_weaken ih2 hv2
  | sclos hv =>
    rename_i v1 v2 A
    intro E A htype henv
    rename_i e2
    cases htype with
    | tlam ih =>
      rename_i B
      apply HasType.tclos <;> try assumption
  | sbeta hv hv1 hv2 =>
    intro E A htype henv
    rename_i v1 v2 v3 B e1
    cases htype with
    | tapp ih1 ih2 =>
      cases ih1 with
      | tclos hv' ht' hb =>
        rename_i Γ₁
        apply HasType.tbox <;> try assumption
        apply HasType.tmrg
        · exact value_weaken ht' hv2
        · exact value_weaken ih2 hv1
  | sboxv hv1 hv2 hv3 =>
    intro E A htype henv
    rename_i v1 v2 v3
    cases htype with
    | tbox ih1 ih2 =>
      rename_i Γ₁ B
      apply value_weaken ih2 hv3
  | sproj hv hstep ih =>
    rename_i v1 e1 e2 n
    intro E A htype henv
    cases htype with
    | tproj ht hl =>
      exact HasType.tproj (ih ht henv) hl
  | sprojv hv1 hv2 hlook =>
    rename_i v1 v2 v3 v4
    intro E A htype henv
    cases htype with
    | tproj ht hl =>
      rename_i A'
      obtain h1 := lookupv_value hlook
      obtain h2 := h1 hv2
      exact value_weaken (lookup_pres hl v2 v4 hlook hv2 (value_weaken ht hv2)) h2
  | slrec hv hstep ih1 =>
    rename_i v e1 e2 l
    intro E A htype henv
    cases htype
    rename_i A ih2
    apply HasType.trcd
    apply ih1
    repeat assumption
  | srproj hv hstep ih =>
    rename_i v1 e1 e2 l
    intro E A htype henv
    cases htype
    rename_i B ih2 hlook
    apply HasType.trproj <;> try assumption
    apply ih
    repeat assumption
  | srprojv hv hv1 hlook =>
    rename_i v' v1 l v2
    intro E A htype henv
    cases htype
    rename_i B ih2 hlook'
    exact value_weaken (rlookup_pres hlook' hlook hv1 (value_weaken ih2 hv1)) (rlookupv_value hlook hv1)

theorem gprogress
  {E A : Typ} {e : Exp}
  {htype : HasType E e A} :
  ∀ {v : Exp},
  Value v
  → HasType .top v E
  → (Value e) ∨ (∃ e' : Exp, Step v e e') := by
  sorry
