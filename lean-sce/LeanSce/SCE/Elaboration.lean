import LeanSce.SCE.Syntax
import LeanSce.Core.Syntax


open SCE

def linkedCore (ctx : Core.Typ) (l : String) (ce₁ ce₂ : Core.Exp) : Core.Exp :=
  Core.Exp.app
    (Core.Exp.lam ctx
      (Core.Exp.mrg
        (Core.Exp.box (Core.Exp.proj Core.Exp.query 0) ce₁)
        (Core.Exp.box (Core.Exp.proj Core.Exp.query 1)
          (Core.Exp.app ce₂
            (Core.Exp.lrec l (Core.Exp.rproj ce₁ l))))))
    Core.Exp.query

mutual
@[simp]
def elabTyp : Typ → Core.Typ
  | Typ.int        => Core.Typ.int
  | Typ.top        => Core.Typ.top
  | Typ.arr t1 t2  => Core.Typ.arr (elabTyp t1) (elabTyp t2)
  | Typ.and t1 t2  => Core.Typ.and (elabTyp t1) (elabTyp t2)
  | Typ.rcd str t  => Core.Typ.rcd str (elabTyp t)
  | Typ.sig mty    => elabModTyp mty

@[simp]
def elabModTyp : ModTyp → Core.Typ
  | ModTyp.TyIntf t1      => elabTyp t1
  | ModTyp.TyArrM t1 mty  => Core.Typ.arr (elabTyp t1) (elabModTyp mty)
end

abbrev TyCtx := Typ

inductive elabExp : TyCtx → Exp → Typ → Core.Exp → Prop
  | equery {ctx}
    : elabExp ctx Exp.query ctx Core.Exp.query
  | elit (ctx : Typ) (n : Nat)
    : elabExp ctx (Exp.lit n) Typ.int (Core.Exp.lit n)
  | eunit (ctx : Typ)
    : elabExp ctx Exp.unit Typ.top Core.Exp.unit
  | eapp (ctx A B : Typ) (se1 se2 : Exp) (ce1 ce2 : Core.Exp)
    : elabExp ctx se1 (Typ.arr A B) ce1
    → elabExp ctx se2 A ce2
    → elabExp ctx (Exp.app se1 se2) B (Core.Exp.app ce1 ce2)
  | eproj (ctx A B : Typ) (se : Exp) (ce : Core.Exp) (i : Nat)
    : elabExp ctx se A ce
    → SLookup A i B
    → elabExp ctx (Exp.proj se i) B (Core.Exp.proj ce i)
  | ebox (ctx ctx' A : Typ) (se1 se2 : Exp) (ce1 ce2 : Core.Exp)
    : elabExp ctx se1 ctx' ce1
    → elabExp ctx' se2 A ce2
    → elabExp ctx (Exp.box se1 se2) A (Core.Exp.box ce1 ce2)
  | edmrg (ctx A B : Typ) (se1 se2 : Exp) (ce1 ce2 : Core.Exp)
    : elabExp ctx se1 A ce1
    → elabExp (Typ.and ctx A) se2 B ce2
    → elabExp ctx (Exp.mrg se1 se2) (Typ.and A B) (Core.Exp.mrg ce1 ce2)
  /-
    Γ ⊢ eˢ₁ : A ⤳ eᶜ₁
    Γ ⊢ eˢ₂ : B ⤳ eᶜ₂
    ──────────────────────────────────────────────────────────
    Γ ⊢ eˢ₁ #n eˢ₂ : A & B ⤳ (λ⟦Γ⟧. mrg (box ?.0 eᶜ₁) (box ?.1 eᶜ₂)) ?
  -/
  | enmrg (ctx A B : Typ) (se1 se2 : Exp) (ce1 ce2 : Core.Exp)
    : elabExp ctx se1 A ce1
    → elabExp ctx se2 B ce2
    → elabExp ctx (Exp.nmrg se1 se2) (Typ.and A B)
        (Core.Exp.app
          (Core.Exp.lam (elabTyp ctx)
            (Core.Exp.mrg
              (Core.Exp.box (Core.Exp.proj Core.Exp.query 0) ce1)
              (Core.Exp.box (Core.Exp.proj Core.Exp.query 1) ce2)))
          Core.Exp.query)
  | elam (ctx A B : Typ) (se : Exp) (ce : Core.Exp)
    : elabExp (Typ.and ctx A) se B ce
    → elabExp ctx (Exp.lam A se) (Typ.arr A B) (Core.Exp.lam (elabTyp A) ce)
  | erproj (ctx A B : Typ) (se : Exp) (ce : Core.Exp) (l : String) :
      elabExp ctx se B ce
      → SRLookup B l A
      → elabExp ctx (Exp.rproj se l) A (Core.Exp.rproj ce l)
  | eclos (ctx ctx' A B : Typ) (se1 se2 : Exp) (ce1 ce2 : Core.Exp)
    : SCE.Value se1
    → elabExp Typ.top se1 ctx' ce1
    → elabExp (Typ.and ctx' A) se2 B ce2
    → elabExp ctx (Exp.clos se1 A se2) (Typ.arr A B) (Core.Exp.clos ce1 (elabTyp A) ce2)
  | elrec (ctx A : Typ) (se : Exp) (ce : Core.Exp) (l : String)
    : elabExp ctx se A ce
    → elabExp ctx (Exp.lrec l se) (Typ.rcd l A) (Core.Exp.lrec l ce)
  | letb (ctx A B : Typ) (se1 se2 : Exp) (ce1 ce2 : Core.Exp)
    : elabExp ctx se1 A ce1
    → elabExp (Typ.and ctx A) se2 B ce2
    → elabExp ctx (Exp.letb se1 A se2) B
        (Core.Exp.app (Core.Exp.lam (elabTyp A) ce2) ce1)
  | openm (ctx A B : Typ) (se1 se2 : Exp) (ce1 ce2 : Core.Exp) (l : String)
    : elabExp ctx se1 (Typ.rcd l A) ce1
    → elabExp (Typ.and ctx A) se2 B ce2
    → elabExp ctx (Exp.openm se1 se2) B
        (Core.Exp.app (Core.Exp.lam (elabTyp A) ce2) (Core.Exp.rproj ce1 l))
  | mstruct (ctx ctxInner B : Typ) (sb : Sandbox) (se : Exp) (ce envCore : Core.Exp)
    : (sb = Sandbox.sandboxed → ctxInner = Typ.top)
    → (sb = Sandbox.open_     → ctxInner = ctx)
    → elabExp ctxInner se B ce
    → elabExp ctx (Exp.mstruct sb se) B
        (Core.Exp.box
          (match sb with
            | Sandbox.sandboxed => Core.Exp.unit
            | Sandbox.open_     => Core.Exp.query)
          ce)
  | mfunctor (ctx ctxInner A B : Typ) (sb : Sandbox) (se : Exp) (ce : Core.Exp)
    : (sb = Sandbox.sandboxed → ctxInner = Typ.and Typ.top A)
    → (sb = Sandbox.open_     → ctxInner = Typ.and ctx A)
    → elabExp ctxInner se B ce
    → elabExp ctx (Exp.mfunctor sb A se) (Typ.sig (ModTyp.TyArrM A (ModTyp.TyIntf B)))
        (match sb with
          | Sandbox.sandboxed => Core.Exp.box Core.Exp.unit (Core.Exp.lam (elabTyp A) ce)
          | Sandbox.open_     => Core.Exp.lam (elabTyp A) ce)
  | mclos (ctx ctx' A B : Typ) (se1 se2 : Exp) (ce1 ce2 : Core.Exp)
    : SCE.Value se1
    → elabExp Typ.top se1 ctx' ce1
    → elabExp (Typ.and ctx' A) se2 B ce2
    → elabExp ctx (Exp.mclos se1 A se2) (Typ.sig (ModTyp.TyArrM A (ModTyp.TyIntf B)))
        (Core.Exp.clos ce1 (elabTyp A) ce2)
  | mapp (ctx A B : Typ) (se1 se2 : Exp) (ce1 ce2 : Core.Exp)
    : elabExp ctx se1 (Typ.sig (ModTyp.TyArrM A (ModTyp.TyIntf B))) ce1
    → elabExp ctx se2 A ce2
    → elabExp ctx (Exp.mapp se1 se2) B (Core.Exp.app ce1 ce2)
  | mlink (ctx Γ₁ A B : Typ) (l : String)
      (se1 se2 : Exp) (ce1 ce2 : Core.Exp)
    : elabExp ctx se1 Γ₁ ce1
    → elabExp ctx se2 (Typ.sig (ModTyp.TyArrM (Typ.rcd l A) (ModTyp.TyIntf B))) ce2
    → SRLookup Γ₁ l A
    → elabExp ctx (Exp.mlink se1 se2) (Typ.and Γ₁ B)
        (linkedCore (elabTyp ctx) l ce1 ce2)
  -- | mlink (ctx A : Typ) (mt : ModTyp) (se1 se2 : Exp) (ce1 ce2 : Core.Exp)
  --   : elabExp ctx se1 A ce1
  --   → elabExp ctx se2 (Typ.sig (ModTyp.TyArrM A mt)) ce2
  --   → elabExp ctx (Exp.mlink se1 se2) (Typ.and A (Typ.sig mt))
  --       (Core.Exp.mrg ce1 (Core.Exp.app ce2 ce1))
