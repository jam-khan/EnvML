import LeanSce.SCE.Syntax
import LeanSce.Core.Syntax

open SCE

/-!
  ## Type Elaboration

  Translates source-level types `SCE.Typ` into core `LambdaE.Typ`.

  The key insight is that module types `Sig(−)` are **erased** —
  they elaborate into ordinary arrow/product types in the core,
  since the core calculus has no notion of modules.
```
  ⟦ Int ⟧        =  Int
  ⟦ Unit ⟧       =  Unit
  ⟦ A → B ⟧      =  ⟦A⟧ → ⟦B⟧
  ⟦ A & B ⟧      =  ⟦A⟧ & ⟦B⟧
  ⟦ {l : A} ⟧    =  {l : ⟦A⟧}
  ⟦ Sig(mt) ⟧    =  ⟦mt⟧ᴹ
```

  ## Module Type Elaboration

  Translates source-level module types `SCE.ModTyp` into core `LambdaE.Typ`.

  Module types are stratified in the source but collapse into
  ordinary types in the core:
```
  ⟦ Intf A ⟧      =  ⟦A⟧          (interface is just its type)
  ⟦ A →ₘ mt ⟧    =  ⟦A⟧ → ⟦mt⟧ᴹ  (functor becomes arrow)
```

  Note that `elabTyp` and `ElabModTyp` are **mutually recursive**
  via the `Sig` case of `elabTyp`.
-/
mutual
def elabTyp : Typ → Core.Typ
  | Typ.int        => Core.Typ.int
  | Typ.top        => Core.Typ.top
  | Typ.arr t1 t2  => Core.Typ.arr (elabTyp t1) (elabTyp t2)
  | Typ.and t1 t2  => Core.Typ.and (elabTyp t1) (elabTyp t2)
  | Typ.rcd str t  => Core.Typ.rcd str (elabTyp t)
  | Typ.sig mty    => elabModTyp mty

def elabModTyp : ModTyp → Core.Typ
  | ModTyp.TyIntf t1      => elabTyp t1
  | ModTyp.TyArrM t1 mty  => Core.Typ.arr (elabTyp t1) (elabModTyp mty)
end

-- Abbreviation for typing context
-- note: Types and Typing context are same
abbrev TyCtx := Typ

/-!
  ## Expression Elaboration

  Given typing context Γ, the source level
  expression eˢ of type A elaborates into
  core expression eᶜ.
```
  Γ ⊢ eˢ : A ⤳ eᶜ

  where
    Γ is typing context for source SCE
    eˢ is source expression
    A is type of eˢ
    eᶜ is core expression
```
-/
inductive elabExp : TyCtx → Exp → Typ → Core.Exp → Prop
  -- Γ ⊢ ? : Γ ⤳ ?
  | query (ctx : Typ)
    : elabExp ctx Exp.query ctx Core.Exp.query
  /-
    Γ ⊢ eˢ : A ⤳ eᶜ
    lookup(A, i) = B
    ─────────────────────
    Γ ⊢ eˢ.i : B ⤳ eᶜ.i
  -/
  | proj (ctx A B : Typ) (se : Exp) (ce : Core.Exp) (i : Nat)
    : elabExp ctx se A ce
    → IndexLookup A i B
    → elabExp ctx (Exp.proj se i) B (Core.Exp.proj ce i)
  /-
    ─────────────────────
    Γ ⊢ n : Int ⤳ n
  -/
  | lit (ctx : Typ) (n : Nat)
    : elabExp ctx (Exp.lit n) Typ.int (Core.Exp.lit n)
  /-
    ─────────────────────
    Γ ⊢ () : Unit ⤳ ()
  -/
  | unit (ctx : Typ)
    : elabExp ctx Exp.unit Typ.top Core.Exp.unit
  /-
    Γ & A ⊢ eˢ : B ⤳ eᶜ
    ──────────────────────────────
    Γ ⊢ λ A. eˢ : A → B ⤳ λ ⟦A⟧. eᶜ
  -/
  | lam (ctx A B : Typ) (se : Exp) (ce : Core.Exp)
    : elabExp (Typ.and ctx A) se B ce
    → elabExp ctx (Exp.lam A se) (Typ.arr A B) (Core.Exp.lam (elabTyp A) ce)
  /-
    Γ ⊢ eˢ₁ : Γ' ⤳ eᶜ₁
    Γ' ⊢ eˢ₂ : A ⤳ eᶜ₂
    ─────────────────────────────────────
    Γ ⊢ eˢ₁ |> eˢ₂ : A ⤳ box eᶜ₁ eᶜ₂
  -/
  | box (ctx ctx' A : Typ) (se1 se2 : Exp) (ce1 ce2 : Core.Exp)
    : elabExp ctx se1 ctx' ce1
    → elabExp ctx' se2 A ce2
    → elabExp ctx (Exp.box se1 se2) A (Core.Exp.box ce1 ce2)
  /-
    Γ ⊢ eˢ₁ : Γ' ⤳ eᶜ₁
    Γ' & A ⊢ eˢ₂ : B ⤳ eᶜ₂
    ──────────────────────────────────────────────────
    Γ ⊢ <eˢ₁, A, eˢ₂> : A → B ⤳ clos eᶜ₁ [A] eᶜ₂
  -/
  | clos (ctx ctx' A B : Typ) (se1 se2 : Exp) (ce1 ce2 : Core.Exp)
    : elabExp ctx se1 ctx' ce1
    → elabExp (Typ.and ctx' A) se2 B ce2
    → elabExp ctx (Exp.clos se1 A se2) (Typ.arr A B) (Core.Exp.clos ce1 (elabTyp A) ce2)
  /-
    Γ ⊢ eˢ₁ : A → B ⤳ eᶜ₁
    Γ ⊢ eˢ₂ : A ⤳ eᶜ₂
    ─────────────────────────────────────
    Γ ⊢ eˢ₁ eˢ₂ : B ⤳ eᶜ₁ eᶜ₂
  -/
  | app (ctx A B : Typ) (se1 se2 : Exp) (ce1 ce2 : Core.Exp)
    : elabExp ctx se1 (Typ.arr A B) ce1
    → elabExp ctx se2 A ce2
    → elabExp ctx (Exp.app se1 se2) B (Core.Exp.app ce1 ce2)
  /-
    Γ ⊢ eˢ₁ : A ⤳ eᶜ₁
    Γ & A ⊢ eˢ₂ : B ⤳ eᶜ₂
    ──────────────────────────────────────────
    Γ ⊢ eˢ₁ #d eˢ₂ : A & B ⤳ mrg eᶜ₁ eᶜ₂
  -/
  | dmrg (ctx A B : Typ) (se1 se2 : Exp) (ce1 ce2 : Core.Exp)
    : elabExp ctx se1 A ce1
    → elabExp (Typ.and ctx A) se2 B ce2
    → elabExp ctx (Exp.mrg se1 se2) (Typ.and A B) (Core.Exp.mrg ce1 ce2)
  /-
    Γ ⊢ eˢ₁ : A ⤳ eᶜ₁
    Γ ⊢ eˢ₂ : B ⤳ eᶜ₂
    ──────────────────────────────────────────────────────────
    Γ ⊢ eˢ₁ #n eˢ₂ : A & B ⤳ (λ⟦Γ⟧. mrg (box ?.0 eᶜ₁) (box ?.1 eᶜ₂)) ?
  -/
  | nmrg (ctx A B : Typ) (se1 se2 : Exp) (ce1 ce2 : Core.Exp)
    : elabExp ctx se1 A ce1
    → elabExp ctx se2 B ce2
    → elabExp ctx (Exp.nmrg se1 se2) (Typ.and A B)
        (Core.Exp.app
          (Core.Exp.lam (elabTyp ctx)
            (Core.Exp.mrg
              (Core.Exp.box (Core.Exp.proj Core.Exp.query 0) ce1)
              (Core.Exp.box (Core.Exp.proj Core.Exp.query 1) ce2)))
          Core.Exp.query)
  /-
    Γ ⊢ eˢ : A ⤳ eᶜ
    ──────────────────────────────────
    Γ ⊢ {l = eˢ} : {l : A} ⤳ {l = eᶜ}
  -/
  | lrec (ctx A : Typ) (se : Exp) (ce : Core.Exp) (l : String)
    : elabExp ctx se A ce
    → elabExp ctx (Exp.lrec l se) (Typ.rcd l A) (Core.Exp.lrec l ce)
  /-
    Γ ⊢ eˢ : B ⤳ eᶜ
    containment(l, B) = A
    ──────────────────────────────
    Γ ⊢ eˢ.l : A ⤳ eᶜ.l
  -/
  | rproj (ctx A B : Typ) (se : Exp) (ce : Core.Exp) (l : String) :
      elabExp ctx se B ce
      → RecordLookup B l A
      → elabExp ctx (Exp.rproj se l) A (Core.Exp.rproj ce l)
  /-
    Γ ⊢ eˢ₁ : A ⤳ eᶜ₁
    Γ & A ⊢ eˢ₂ : B ⤳ eᶜ₂
    ────────────────────────────────────────────────────
    Γ ⊢ let eˢ₁ : A in eˢ₂ : B ⤳ (lam [A] eᶜ₂) eᶜ₁
  -/
  | letb (ctx A B : Typ) (se1 se2 : Exp) (ce1 ce2 : Core.Exp)
    : elabExp ctx se1 A ce1
    → elabExp (Typ.and ctx A) se2 B ce2
    → elabExp ctx (Exp.letb se1 A se2) B
        (Core.Exp.app (Core.Exp.lam (elabTyp A) ce2) ce1)
  /-
    Γ ⊢ eˢ₁ : {l : A} ⤳ eᶜ₁
    Γ & A ⊢ eˢ₂ : B ⤳ eᶜ₂
    ────────────────────────────────────────────────────────────
    Γ ⊢ open eˢ₁ in eˢ₂ : B ⤳ (lam [A] eᶜ₂) (eᶜ₁.l)
  -/
  | openm (ctx A B : Typ) (se1 se2 : Exp) (ce1 ce2 : Core.Exp) (l : String)
    : elabExp ctx se1 (Typ.rcd l A) ce1
    → elabExp (Typ.and ctx A) se2 B ce2
    → elabExp ctx (Exp.openm se1 se2) B
        (Core.Exp.app (Core.Exp.lam (elabTyp A) ce2) (Core.Exp.rproj ce1 l))
  /-
    sandboxed: Unit & A ⊢ eˢ : B ⤳ eᶜ
    ────────────────────────────────────────────────────
    Γ ⊢ struct[sandboxed] eˢ : Sig(TyIntf B) ⤳ box () eᶜ

    open: Γ & A ⊢ eˢ : B ⤳ eᶜ
    ────────────────────────────────────────────────────
    Γ ⊢ struct[open] eˢ : Sig(TyIntf B) ⤳ box ? eᶜ
  -/
  | mstruct (ctx ctxInner B : Typ) (sb : Sandbox) (se : Exp) (ce envCore : Core.Exp)
    : (sb = Sandbox.sandboxed → ctxInner = Typ.top)
    → (sb = Sandbox.open_     → ctxInner = ctx)
    → elabExp ctxInner se B ce
    → elabExp ctx (Exp.mstruct sb se) (Typ.sig (ModTyp.TyIntf B))
        (Core.Exp.box
          (match sb with
            | Sandbox.sandboxed => Core.Exp.unit
            | Sandbox.open_     => Core.Exp.query)
          ce)
  /-
    sandboxed: Unit & A ⊢ eˢ : B ⤳ eᶜ
    ─────────────────────────────────────────────────────────────────
    Γ ⊢ functor[sandboxed](A) eˢ : Sig(A →m mt) ⤳ box () (lam [A] eᶜ)

    open: Γ & A ⊢ eˢ : B ⤳ eᶜ
    ──────────────────────────────────────────────────────────
    Γ ⊢ functor[open](A) eˢ : Sig(A →m mt) ⤳ lam [A] eᶜ
  -/
  | mfunctor (ctx ctxInner A B : Typ) (mt : ModTyp) (sb : Sandbox) (se : Exp) (ce : Core.Exp)
    : (sb = Sandbox.sandboxed → ctxInner = Typ.and Typ.top A)
    → (sb = Sandbox.open_     → ctxInner = Typ.and ctx A)
    → elabExp ctxInner se B ce
    → elabExp ctx (Exp.mfunctor sb A se) (Typ.sig mt)
        (match sb with
          | Sandbox.sandboxed => Core.Exp.box Core.Exp.unit (Core.Exp.lam (elabTyp A) ce)
          | Sandbox.open_     => Core.Exp.lam (elabTyp A) ce)
  /-
    Γ ⊢ eˢ₁ : Γ' ⤳ eᶜ₁
    Γ' & A ⊢ eˢ₂ : B ⤳ eᶜ₂
    ──────────────────────────────────────────────────────────
    Γ ⊢ mclos(eˢ₁, A, eˢ₂) : Sig(A →m mt) ⤳ clos eᶜ₁ [A] eᶜ₂
  -/
  | mclos (ctx ctx' A B : Typ) (mt : ModTyp) (se1 se2 : Exp) (ce1 ce2 : Core.Exp)
    : elabExp ctx se1 ctx' ce1
    → elabExp (Typ.and ctx' A) se2 B ce2
    → elabExp ctx (Exp.mclos se1 A se2) (Typ.sig mt)
        (Core.Exp.clos ce1 (elabTyp A) ce2)
  /-
    Γ ⊢ eˢ₁ : Sig(A →m mt) ⤳ eᶜ₁
    Γ ⊢ eˢ₂ : A ⤳ eᶜ₂
    ──────────────────────────────────────────
    Γ ⊢ link(eˢ₁, eˢ₂) : Sig(mt) ⤳ eᶜ₁ eᶜ₂
  -/
  | mapp (ctx A : Typ) (mt : ModTyp) (se1 se2 : Exp) (ce1 ce2 : Core.Exp)
    : elabExp ctx se1 (Typ.sig (ModTyp.TyArrM A mt)) ce1
    → elabExp ctx se2 A ce2
    → elabExp ctx (Exp.mlink se1 se2) (Typ.sig mt)
        (Core.Exp.app ce1 ce2)
  /-
    Γ ⊢ eˢ₁ : Sig(A →m mt) ⤳ eᶜ₁
    Γ ⊢ eˢ₂ : A ⤳ eᶜ₂
    ──────────────────────────────────────────────────────
    Γ ⊢ link(eˢ₁, eˢ₂) : Sig(A & mt) ⤳ mrg eᶜ₂ (eᶜ₁ eᶜ₂)
    -/
  | mlink (ctx A : Typ) (mt : ModTyp) (se1 se2 : Exp) (ce1 ce2 : Core.Exp)
    : elabExp ctx se1 (Typ.sig (ModTyp.TyArrM A mt)) ce1
    → elabExp ctx se2 A ce2
    → elabExp ctx (Exp.mlink se1 se2) (Typ.sig (ModTyp.TyArrM A mt))
        (Core.Exp.mrg ce2 (Core.Exp.app ce1 ce2))
