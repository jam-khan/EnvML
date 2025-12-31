namespace LambdaE

inductive Typ where
  | int  : Typ
  | top  : Typ
  | arr  : Typ → Typ → Typ
  | and  : Typ → Typ → Typ
  | rcd  : String → Typ → Typ
  deriving Repr

inductive Op where
  | app
  | box
  | mrg
  deriving Repr

inductive Exp where
  | ctx    : Exp
  | lit    : Nat → Exp
  | unit   : Exp
  | binop  : Op → Exp → Exp → Exp
  | lam    : Typ → Exp → Exp
  | proj   : Exp → Nat → Exp
  | clos   : Exp → Typ → Exp → Exp
  | lrec   : String → Exp → Exp
  | rproj  : Exp → String → Exp
  deriving Repr

inductive Value : Exp → Prop
| vint  : ∀ n, Value (Exp.lit n)
| vunit : Value unit
| vclos : ∀ v A e, Value v → Value (Exp.clos v A e)
| vrcd  : ∀ l v, Value v → Value (Exp.lrec l v)
| vmrg  : ∀ v₁ v₂, Value v₁ → Value v₂ → Value (Exp.binop Op.mrg v₁ v₂) 

inductive IndexLookup : Typ -> Nat-> Typ -> Prop 
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

inductive HasType : Typ -> Exp -> Typ -> Prop
| ctx (EnvT : Typ) : HasType EnvT Exp.ctx EnvT
| int (EnvT : Typ) (i : Nat) : HasType EnvT (Exp.lit i) Typ.int
| unit (EnvT : Typ) : HasType EnvT Exp.unit Typ.top
| app (EnvT A B : Typ) (e1 e2 : Exp) :
    HasType EnvT e1 (Typ.arr A B) →
    HasType EnvT e2 A →
    HasType EnvT (Exp.binop Op.app e1 e2) B
| box (EnvT EnvT₁ A: Typ) (e1 e2 : Exp) :
    HasType EnvT e1 EnvT₁ →
    HasType EnvT₁ e2 A →
    HasType EnvT (Exp.binop Op.box e1 e2) A
| mrg (EnvT A B: Typ) (e1 e2 : Exp) :
    HasType EnvT e1 A →
    HasType (Typ.and EnvT A) e2 B →
    HasType EnvT (Exp.binop Op.mrg e1 e2) (Typ.and A B)
| lam (EnvT A B : Typ) (e : Exp) :
    HasType (Typ.and EnvT A) e B →
    HasType EnvT (Exp.lam A e) (Typ.arr A B)
| proj (EnvT A B : Typ) (e : Exp) (n : Nat) :
    HasType EnvT e A →
    IndexLookup A n B →
    HasType EnvT (Exp.proj e n) B
| clos (EnvT EnvT₁ A B : Typ) (e env : Exp) : 
    Value env →
    HasType Typ.top env EnvT₁ →
    HasType (Typ.and EnvT₁ A) e B →
    HasType EnvT (Exp.clos env A e) (Typ.arr A B)
| rcd (EnvT A : Typ) (e : Exp) (label : String) :
    HasType EnvT e A →
    HasType EnvT (Exp.lrec label e) (Typ.rcd label A)
| rproj (EnvT A B : Typ) (e : Exp) (label : String) :
    HasType EnvT e B →
    RecordLookup B label A →
    HasType EnvT (Exp.rproj e label) A 

end LambdaE

