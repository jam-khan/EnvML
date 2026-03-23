import LeanSce.SCE.Syntax

open SCE

namespace S_Sem

inductive LookupV : Exp → Nat → Exp → Prop where
  | dmrg_zero {v₁ v₂ : Exp}
    : LookupV (.mrg v₁ v₂) 0 v₂
  | dmrg_succ {v₁ v₂ v' : Exp} {n : Nat}
    : LookupV v₁ n v'
    → LookupV (.mrg v₁ v₂) (n + 1) v'
  | nmrg_zero {v₁ v₂ : Exp}
    : LookupV (.nmrg v₁ v₂) 0 v₂
  | nmrg_succ {v₁ v₂ v' : Exp} {n : Nat}
    : LookupV v₁ n v'
    → LookupV (.nmrg v₁ v₂) (n + 1) v'

inductive Sel : Exp → String → Exp → Prop where
  | rcd {l : String} {v : Exp}
    : Sel (.lrec l v) l v
  | dmrg_left {v₁ v₂ v' : Exp} {l : String}
    : Sel v₁ l v'
    → Sel (.mrg v₁ v₂) l v'
  | dmrg_right {v₁ v₂ v' : Exp} {l : String}
    : Sel v₂ l v'
    → Sel (.mrg v₁ v₂) l v'
  | nmrg_left {v₁ v₂ v' : Exp} {l : String}
    : Sel v₁ l v'
    → Sel (.nmrg v₁ v₂) l v'
  | nmrg_right {v₁ v₂ v' : Exp} {l : String}
    : Sel v₂ l v'
    → Sel (.nmrg v₁ v₂) l v'

inductive BStep : Exp → Exp → Exp → Prop where
  | query {ρ : Exp}
    : Value ρ
    → BStep ρ .query ρ
  | lit {ρ : Exp} {n : Nat}
    : Value ρ
    → BStep ρ (.lit n) (.lit n)
  | unit {ρ : Exp}
    : Value ρ
    → BStep ρ .unit .unit
  | clos_val {ρ v : Exp} {A : Typ} {body : Exp}
    : Value ρ
    → Value v
    → BStep ρ (.clos v A body) (.clos v A body)
  | mclos_val {ρ v : Exp} {A : Typ} {body : Exp}
    : Value ρ
    → Value v
    → BStep ρ (.mclos v A body) (.mclos v A body)
  | proj {ρ e v v' : Exp} {n : Nat}
    : Value ρ
    → BStep ρ e v
    → LookupV v n v'
    → BStep ρ (.proj e n) v'
  | lam {ρ : Exp} {A : Typ} {body : Exp}
    : Value ρ
    → BStep ρ (.lam A body) (.clos ρ A body)
  | box {ρ e₁ e₂ v₁ v : Exp}
    : Value ρ
    → BStep ρ e₁ v₁
    → BStep v₁ e₂ v
    → BStep ρ (.box e₁ e₂) v
  | app_clos {ρ e₁ e₂ v₁ v₂ v : Exp} {A : Typ} {body : Exp}
    : Value ρ
    → BStep ρ e₁ (.clos v₁ A body)
    → BStep ρ e₂ v₂
    → BStep (.mrg v₁ v₂) body v
    → BStep ρ (.app e₁ e₂) v
  | app_mclos {ρ e₁ e₂ v₁ v₂ v : Exp} {A : Typ} {body : Exp}
    : Value ρ
    → BStep ρ e₁ (.mclos v₁ A body)
    → BStep ρ e₂ v₂
    → BStep (.mrg v₁ v₂) body v
    → BStep ρ (.mapp e₁ e₂) v
  | dmrg {ρ e₁ e₂ v₁ v₂ : Exp}
    : Value ρ
    → BStep ρ e₁ v₁
    → BStep (.mrg ρ v₁) e₂ v₂
    → BStep ρ (.mrg e₁ e₂) (.mrg v₁ v₂)
  | nmrg {ρ e₁ e₂ v₁ v₂ : Exp}
    : Value ρ
    → BStep ρ e₁ v₁
    → BStep ρ e₂ v₂
    → BStep ρ (.nmrg e₁ e₂) (.nmrg v₁ v₂)
  | lrec {ρ e v : Exp} {l : String}
    : Value ρ
    → BStep ρ e v
    → BStep ρ (.lrec l e) (.lrec l v)
  | rproj {ρ e v v' : Exp} {l : String}
    : Value ρ
    → BStep ρ e v
    → Sel v l v'
    → BStep ρ (.rproj e l) v'
  | letb {ρ e₁ e₂ v₁ v : Exp} {A : Typ}
    : Value ρ
    → BStep ρ e₁ v₁
    → BStep (.mrg ρ v₁) e₂ v
    → BStep ρ (.letb e₁ A e₂) v
  | openm {ρ e₁ e₂ v' v : Exp} {l : String}
    : Value ρ
    → BStep ρ e₁ (.lrec l v')
    → BStep (.mrg ρ v') e₂ v
    → BStep ρ (.openm e₁ e₂) v
  | mstruct_sandboxed {ρ body v : Exp}
    : Value ρ
    → BStep .unit body v
    → BStep ρ (.mstruct .sandboxed body) v
  | mstruct_open {ρ body v : Exp}
    : Value ρ
    → BStep ρ body v
    → BStep ρ (.mstruct .open_ body) v
  | mfunctor_sandboxed {ρ : Exp} {A : Typ} {body : Exp}
    : Value ρ
    → BStep ρ (.mfunctor .sandboxed A body) (.mclos .unit A body)
  | mfunctor_open {ρ : Exp} {A : Typ} {body : Exp}
    : Value ρ
    → BStep ρ (.mfunctor .open_ A body) (.mclos ρ A body)
  -- Below is completely wrong!!!!
  | mlink {ρ e₁ e₂ v₁ v₂ v : Exp} {A : Typ} {body : Exp}
    : Value ρ
    → BStep ρ e₂ (.mclos v A body)
    → BStep ρ e₁ v₁
    → BStep (.mrg v₁ v₂) body v
    → BStep ρ (.mlink e₁ e₂) (.mrg v₁ (.app v₂ v₁))

end S_Sem
