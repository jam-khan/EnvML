
namespace SCE

mutual

inductive Typ where
  | int  : Typ
  | top  : Typ
  | arr  : Typ → Typ → Typ
  | and  : Typ → Typ → Typ
  | rcd  : String → Typ → Typ
  | sig  : ModTyp → Typ

inductive ModTyp where
  | TyIntf : Typ → ModTyp
  | TyArrM : Typ → ModTyp → ModTyp

end

deriving instance Repr for Typ
deriving instance Repr for ModTyp

inductive Sandbox where
  | sandboxed : Sandbox
  | open_ : Sandbox
  deriving Repr

inductive Exp where
  | query  : Exp
  | proj   : Exp → Nat → Exp
  | lit    : Nat → Exp
  | unit   : Exp
  | lam    : Typ → Exp → Exp
  | box    : Exp → Exp → Exp
  | clos   : Exp → Typ → Exp → Exp
  | app    : Exp → Exp → Exp
  | mrg    : Exp → Exp → Exp
  | lrec   : String → Exp → Exp
  | rproj  : Exp → String → Exp
  -- to be elaborated
  | mstruct : Sandbox → Exp → Exp
  | mfunctor : Sandbox → Typ → Exp → Exp
  | mclos : Exp → Typ → Exp → Exp
  | mlink : Exp → Exp → Exp
  | mapp : Exp → Exp → Exp
  -- more terms
  | nmrg  : Exp → Exp → Exp
  | letb  : Exp → Typ → Exp → Exp
  | openm : Exp → Exp → Exp
  deriving Repr

inductive Value : Exp → Prop where
  | vint   {n}     : Value (.lit n)
  | vunit          : Value .unit
  | vclos  {v A e} : Value v  → Value (.clos v A e)
  | vmclos {v A e} : Value v  → Value (.mclos v A e)
  | vmrg   {v₁ v₂} : Value v₁ → Value v₂ → Value (.mrg v₁ v₂)
  | vnmrg  {v₁ v₂} : Value v₁ → Value v₂ → Value (.nmrg v₁ v₂)
  | vlrec  {v l}   : Value v  → Value (.lrec l v)

inductive IndexLookup : Typ → Nat → Typ → Prop
| zero (A B : Typ) : IndexLookup (Typ.and A B) 0 B
| succ (A B : Typ) (n : Nat) (C : Typ)
    : IndexLookup A n C → IndexLookup (Typ.and A B) (Nat.succ n) C

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

end SCE
