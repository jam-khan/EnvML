import LeanSce.Core.Syntax

open Core

namespace C_Sem
/--
  Positional lookup in merged values.
  `LookupV v n v'` means: in the merged value `v`,
  the component at index `n` is `v'`.

  Index 0 is the rightmost (most recently merged) component.
-/
inductive LookupV : Exp → Nat → Exp → Prop where
  | lvzero {v₁ v₂ : Exp}
    : LookupV (.mrg v₁ v₂) 0 v₂
  | lvsucc {v₁ v₂ v₃ : Exp} {n : Nat}
    : LookupV v₁ n v₃
    → LookupV (.mrg v₁ v₂) (n + 1) v₃

inductive RLookupV : Exp → String → Exp → Prop where
  | rvlzero {l : String} {e : Exp}
    : RLookupV (.lrec l e) l e
  | vlandl {e₁ e₂ e : Exp} {l : String}
    : RLookupV e₁ l e
    → RLookupV (.mrg e₁ e₂) l e
  | vlandr {e₁ e₂ e : Exp} {l : String}
    : RLookupV e₂ l e
    → RLookupV (.mrg e₁ e₂) l e

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

inductive Step : Exp → Exp → Exp → Prop :=
  | squery {v}
    : Value v
    -> Step v .query v
  | sappl {v e1 e1' e2}
    : Value v
    → Step v e1 e1'
    → Step v (.app e1 e2) (.app e1' e2)
  | sboxl {v e1 e1' e2}
    : Value v
    → Step v e1 e1'
    → Step v (.box e1 e2) (.box e1' e2)
  | smrgl {v e1 e1' e2}
    : Value v
    → Step v e1 e1'
    → Step v (.mrg e1 e2) (.mrg e1' e2)
  | sappr {v v1 e2 e2'}
    : Value v
    → Value v1
    → Step v e2 e2'
    → Step v (.app v1 e2) (.app v1 e2')
  | sboxr
    : Value v
    → Value v1
    → Step v1 e2 e2'
    → Step v (.box v1 e2) (.box v1 e2')
  | smrgr {v v1 e2 e2'}
    : Value v
    → Value v1
    → Step (.mrg v v1) e2 e2'
    → Step v (.mrg v1 e2) (.mrg v1 e2')
  | sclos {v A e}
    : Value v
    → Step v (.lam A e) (.clos v A e)
  | sbeta {v v1 v2 A e}
    : Value v
    → Value v1
    → Value v2
    → Step v (.app (.clos v2 A e) v1) (.box (.mrg v2 v1) e)
  | sboxv {v v1 v2}
    : Value v
    → Value v1
    → Value v2
    → Step v (.box v1 v2) v2
  | sproj {v e1 e2 n}
    : Value v
    → Step v e1 e2
    → Step v (.proj e1 n) (.proj e2 n)
  | sprojv {v v1 n v2}
    : Value v
    → Value v1
    → LookupV v1 n v2
    → Step v (.proj v1 n) v2
  | slrec {v e1 e2 l}
    : Value v
    → Step v e1 e2
    → Step v (.lrec l e1) (.lrec l e2)
  | srproj
    : Value v
    → Step v e1 e2
    → Step v (.rproj e1 l) (.rproj e2 l)
  | srprojv {v v1 l v2}
    : Value v
    → Value v1
    → RLookupV v1 l v2
    → Step v (.rproj v1 l) v2

end C_Sem
