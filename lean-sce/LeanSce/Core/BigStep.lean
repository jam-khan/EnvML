import LeanSce.Core.Syntax
import LeanSce.Core.Typing
import LeanSce.Core.SmallStep

open Core

inductive EBig : Exp → Exp → Exp → Prop where
  | eblit {v : Exp} {i : Nat}
    : Value v
    → EBig v (.lit i) (.lit i)
  | ebunit {v : Exp}
    : Value v
    → EBig v .unit .unit
  | ebmrg {v e₁ e₂ v₁ v₂ : Exp}
    : EBig v e₁ v₁
    → EBig (.mrg v v₁) e₂ v₂
    → EBig v (.mrg e₁ e₂) (.mrg v₁ v₂)
  | ebclos {v : Exp} {A : Typ} {e : Exp}
    : Value v
    → EBig v (.lam A e) (.clos v A e)
  | ebapp {v e₁ e₂ v₁ v₂ vr e : Exp} {A : Typ}
    : EBig v e₁ (.clos v₂ A e)
    → EBig v e₂ v₁
    → EBig (.mrg v₂ v₁) e vr
    → EBig v (.app e₁ e₂) vr
  | ebbox {v e₁ e₂ v₁ vr : Exp}
    : EBig v e₁ v₁
    → EBig v₁ e₂ vr
    → EBig v (.box e₁ e₂) vr
  | eclos {v v₁ : Exp} {A : Typ} {e : Exp}
    : Value v
    → Value v₁
    → EBig v (.clos v₁ A e) (.clos v₁ A e)
  | equery {e : Exp}
    : Value e
    → EBig e .query e
  | ebproj {e a v v' : Exp} {n : Nat}
    : EBig e a v
    → LookupV v n v'
    → EBig e (.proj a n) v'
  | ebrec {e a v : Exp} {l : String}
    : EBig e a v
    → EBig e (.lrec l a) (.lrec l v)
  | ebsel {e a v₁ v₂ : Exp} {l : String}
    : EBig e a v₁
    → RLookupV v₁ l v₂
    → EBig e (.rproj a l) v₂

theorem ebig_produces_value
    {v e v' : Core.Exp}
    (hval : Core.Value v)
    (hbig : EBig v e v')
    : Core.Value v' := by
  induction hbig with
  | eblit _ => exact Value.vint
  | ebunit _ => exact Value.vunit
  | ebmrg _ _ ih1 ih2 => exact Value.vmrg (ih1 hval) (ih2 (Value.vmrg hval (ih1 hval)))
  | ebclos hv => exact Value.vclos hv
  | ebapp _ _ _ ih1 ih2 ih3 =>
    have hclos := ih1 hval
    cases hclos with | vclos hv => exact ih3 (Value.vmrg hv (ih2 hval))
  | ebbox _ _ ih1 ih2 => exact ih2 (ih1 hval)
  | eclos _ hv1 => exact Value.vclos hv1
  | equery hv => exact hv
  | ebproj _ hlook ih =>
    exact lookupv_value hlook (ih hval)
  | ebrec _ ih => exact Value.vrcd (ih hval)
  | ebsel _ hsel ih =>
    exact rlookupv_value hsel (ih hval)
