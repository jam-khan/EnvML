namespace ENVCAP

inductive Typ where
  | int  : Typ
  | top  : Typ
  | arr  : Typ → Typ → Typ
  | and  : Typ → Typ → Typ
  | rcd  : String → Typ → Typ
  | sig  : Typ → Typ → Typ
  deriving Repr

inductive Op where
  | app
  | withE
  | dmrg
  | ndmrg
  | mapp
  deriving Repr

inductive Exp where
  | ctx    : Exp
  | unit   : Exp
  | lit    : Nat → Exp
  | binop  : Op → Exp → Exp → Exp
  | lam    : Typ → Exp → Exp
  | proj   : Exp → Nat → Exp
  | clos   : Exp → Typ → Exp → Exp
  | struct : Typ → Exp → Exp
  | lrec   : String → Exp → Exp
  | rproj  : Exp → String → Exp
  | slet   : Exp → Typ → Exp → Exp
  | sopen  : Exp → Exp → Exp
  deriving Repr

inductive IndexLookup : Typ → Nat → Typ → Prop
| zero (A B : Typ) : IndexLookup (Typ.and A B) 0 B
| succ (A B : Typ) (n : Nat) (C : Typ) : IndexLookup A n C → IndexLookup (Typ.and A B) (Nat.succ n) C

inductive LabelIn : String -> Typ -> Prop
| rcd (label : String) (T : Typ) : LabelIn label (Typ.rcd label T)
| andl (A B : Typ) (label : String) : LabelIn label A → LabelIn label (Typ.and A B)
| andr (A B : Typ) (label : String) : LabelIn label B → LabelIn label (Typ.and A B)

inductive RecordLookup : Typ → String → Typ → Prop
| zero (label : String) (T : Typ) :
    RecordLookup (Typ.rcd label T) label T
| andl (A B : Typ) (label : String) (T : Typ) :
    RecordLookup A label T →
    LabelIn label A ∧ ¬ LabelIn label B →
    RecordLookup (Typ.and A B) label T
| andr (A B : Typ) (label : String) (T : Typ) :
    RecordLookup B label T →
    LabelIn label B ∧ ¬ LabelIn label A →
    RecordLookup (Typ.and A B) label T

end ENVCAP
