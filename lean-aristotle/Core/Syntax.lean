/-!
  ## Core Calculus λE — Syntax
```
  Types
    A, B, Γ  ::=  Int                -- integer type
               |  ε                  -- unit / top type
               |  A & B              -- intersection / product
               |  A → B              -- function type
               |  { l : A }          -- record type

  Expressions
    e        ::=  ?                  -- environment query
               |  e.n                -- de Bruijn projection
               |  i                  -- integer literal
               |  ε                  -- unit value
               |  λA. e              -- lambda abstraction
               |  e₁ ▷ e₂            -- environment box
               |  ⟨v, λA. e⟩         -- closure
               |  e₁ e₂              -- application
               |  e₁ # e₂            -- merge
               |  { l = e }          -- record
               |  e.l                -- record projection

  Values
    v        ::=  i                  -- integer
               |  ε                  -- unit
               |  ⟨v, λA. e⟩         -- closure value
               |  v₁ # v₂            -- merge value
               |  { l = v }          -- record value

  Contexts (Typing)
    Γ        ::=  A                  -- context is a type
                                     -- (first-class environments)
```

  ### Notes
  - Typing contexts `Γ` are **types**, not lists.
    The judgment `Γ ⊢ e : A` uses the same universe for
    contexts and types — environments are first-class values.
  - `?` reifies the current environment as a value.
  - `e₁ ▷ e₂` runs `e₂` under the environment produced by `e₁`.
  - Closures `⟨v, λA. e⟩` capture their environment explicitly,
    enabling the semantic model to reason about closed values.

  Fig. 1. λE Syntax
-/
namespace Core

inductive Typ where
  | int  : Typ
  | top  : Typ
  | arr  : Typ → Typ → Typ
  | and  : Typ → Typ → Typ
  | rcd  : String → Typ → Typ
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
  deriving Repr

inductive Value : Exp → Prop where
  | vint {n}      : Value (.lit n)
  | vunit         : Value .unit
  | vclos {v A e} : Value v → Value (.clos v A e)
  | vrcd {v l}    : Value v → Value (.lrec l v)
  | vmrg {v1 v2}  : Value v1 → Value v2 → Value (.mrg v1 v2)

inductive Lookup : Typ → Nat → Typ → Prop where
  | zero {A B}
    : Lookup (.and A B) 0 B
  | succ {A n C B}
    : Lookup A n C
    → Lookup (.and A B) (n+1) C

inductive Lin : String → Typ → Prop where
  | rcd {l A}     : Lin l (.rcd l A)
  | andl {l A B}  : Lin l A → Lin l (.and A B)
  | andr {l B A}  : Lin l B → Lin l (.and A B)

inductive RLookup : Typ → String → Typ → Prop where
  | zero {l A}
    : RLookup (.rcd l A) l A
  | landl {A l C B}
    : RLookup A l C
      → Lin l A ∧ ¬Lin l B
      → RLookup (.and A B) l C
  | landr {B l C A}
    : RLookup B l C
      → ¬Lin l A ∧ Lin l B
      → RLookup (.and A B) l C

end Core
