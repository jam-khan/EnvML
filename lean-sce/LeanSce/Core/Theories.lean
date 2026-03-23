
import LeanSce.Core.Syntax
import LeanSce.Core.Semantics
import LeanSce.Core.Typing

open Core C_Sem

@[simp]
theorem value_weaken
  {E A : Typ} { v : Exp}
  {htype : HasType E v A} :
  ∀ {E' : Typ},
    Value v
    → HasType E' v A := by
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
    rename_i Γ₁ Γ₂ A' B' v₀ e₀ n
    intro E' hv
    apply HasType.tclos
    · assumption
    · assumption
    · exact (ih1 ∘ fun a => hv') E
    · assumption

theorem Gpreservation
  {E A : Typ} {e e' v' : Exp} {hv : Value v'}
  (hstep : Step v' e e')
  (htype : HasType E e A)
  (henv  : HasType .top v' E) :
  HasType E e' A := by
  induction hstep with
  | squery heval =>
    rename_i v
    cases htype
    apply value_weaken; try assumption
    apply hv
  | _ =>
    sorry
