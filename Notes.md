# EnvML: Technical Notes

## Contributions

1. **EnvML source language with first-class modules**
   - ML-style modules, functors, signatures, and type definitions
   - Elaboration to Core FE where modules are modeled as environments

2. **Module elaboration scheme**
   - Module structures elaborate to environments with labeled record entries
   - Signatures elaborate to typing contexts
   - Module variables elaborate to `[i].m` (projection) vs term variables to `i` (index)

3. **Named Core FE intermediate representation**
   - Preserves variable names between elaboration and de Bruijn transformation
   - Distinguishes term bindings (`x = e`), module bindings (`m = e`), and type bindings (`t = A`)

4. **De Bruijn transformation for Core FE**
   - Binding-kind-aware index computation
   - Right-to-left environment scoping matching ML semantics

5. **Implementation with interactive playground**
   - Full pipeline: parsing → elaboration → de Bruijn → type checking → evaluation
   
---

## First-Class Modules

Modules are modeled as environments, so all module structures elaborate into records as environment elements. Interfaces elaborate into typing contexts.

**Example elaboration:**
```
⟦struct let x = e₁; ... end⟧ ⟿ [{x = e₁}, ...]
```

### Design Choice: Why Records?

We could choose to elaborate module structures into environment entries directly without records. For example:
```ml
struct 
  let x = 1
  let y = x
end
```

could be elaborated into `[1, x₀]`. However, this doesn't allow for module projection.
```ml
let m = struct let x = 1; let y = x end;
let v = m.x
```

If we were to access `x` inside the module `m`, we won't be able to, as during nameless transformation the above would elaborate to:
```
[
  [1, x₀],
  x₀.x
]
```

This has two issues:

1. Since projection is only defined on records `e.l`, the elaborated `x₀.x` will be an invalid term in Core FE.
2. Record projection requires `e` to have an environment structure where `e` is either a record `{l = ..}` or contains a record nested inside.

### Solution: Labeled Record Entries

We overcome this challenge by elaborating modules to environments with record entries:
```ml
struct
  let x = 1
  let y = x
end
```

becomes `[{x = 1}, {y = x₀.x}]`.

### The Nested Module Problem

However, one more issue persists. Since we have first-class modules, top-level structure is always wrapped as a module. Whenever we write:
```ml
let m = ...
let v = ...
```

it is implicitly wrapped in a struct:
```ml
struct 
  let m = struct let x = 1; let y = x end;
  let v = m.x
end
```

If we elaborate this with our previous scheme:
```
[
  {m = [{x = 1}, {y = x₀.x}]},
  {v = x₀.x}
]
```

But `x₀` in `{v = x₀.x}` refers to a record `{m = ...}`, so `x₀.x` becomes an invalid projection!

### Solution: Module vs Term Variables

To mitigate this correctly, we treat module variables differently than term variables:

| Variable Kind | Elaboration |
|---------------|-------------|
| Term variable `x` | de Bruijn index `i` |
| Module variable `m` | `[i].m` (index wrapped in environment + projection) |

This gives us:
```
[
  {m = [{x = 1}, {y = x₀.x}]},
  {v = [x₀].m.x}
]
```

Now `[x₀].m` accesses the module contents, and `.x` projects the field correctly.

---

## Named Core FE

To enable the module variable elaboration, we introduce a named version of Core FE with the transformation to nameless Core FE.

### Syntax
```
Exp   e  ::=  x                        (term variable)
          |   m                        (module variable)  
          |   λx. e                    (term abstraction)
          |   ⟨Δ | λx. e⟩             (term closure)
          |   e₁ e₂                    (application)
          |   Λt. e                    (type abstraction)
          |   ⟨Δ | Λt. e⟩             (type closure)
          |   e @A                     (type application)
          |   [Δ] ▷ e                  (box)
          |   {l = e}                  (record)
          |   e.l                      (projection)
          |   Δ                        (environment value)
          |   e : A                    (annotation)

Env   Δ  ::=  ·                        (empty)
          |   x = e, Δ                 (term binding)
          |   m = e, Δ                 (module binding)
          |   t = A, Δ                 (type binding)

Type  A  ::=  int | bool | string      (base types)
          |   t                        (type variable)
          |   A → B                    (function type)
          |   ∀t. A                    (universal type)
          |   [Γ] ▷ A                  (box type)
          |   [t := A] B               (type substitution)
          |   {l : A}                  (record type)
          |   Env[Γ]                   (environment type)

TyEnv Γ  ::=  ·                        (empty)
          |   t : A, Γ                 (type annotation)
          |   t : *, Γ                 (kind)
          |   t = A, Γ                 (type equality)
```

---

## De Bruijn Transformation

### Contexts
```
Γₑ  ∈  ExpCtx   ::=  ·  |  (x, Term) :: Γₑ  |  (m, Mod) :: Γₑ
Γₜ  ∈  TypeCtx  ::=  ·  |  t :: Γₜ

k   ∈  BindingKind  ::=  Term  |  Mod
```

### Index Lookup
```
indexₑ : Name → ExpCtx → ℕ × BindingKind

indexₑ(x, ·)                =  error
indexₑ(x, (x, k) :: Γₑ)     =  (0, k)
indexₑ(x, (y, _) :: Γₑ)     =  let (i, k) = indexₑ(x, Γₑ) in (i + 1, k)


indexₜ : Name → TypeCtx → ℕ

indexₜ(t, ·)           =  error
indexₜ(t, t :: Γₜ)     =  0
indexₜ(t, s :: Γₜ)     =  1 + indexₜ(t, Γₜ)
```

### Expression Translation
```
⟦_⟧ₑ : ExpCtx → TypeCtx → Exp → Exp'


⟦x⟧ₑ(Γₑ, Γₜ)  =  let (i, k) = indexₑ(x, Γₑ) in
                 case k of
                   Term  →  i
                   Mod   →  [i].x

⟦λx. e⟧ₑ(Γₑ, Γₜ)  =  λ. ⟦e⟧ₑ((x, Term) :: Γₑ, Γₜ)

⟦Λt. e⟧ₑ(Γₑ, Γₜ)  =  Λ. ⟦e⟧ₑ(Γₑ, t :: Γₜ)

⟦e₁ e₂⟧ₑ(Γₑ, Γₜ)  =  ⟦e₁⟧ₑ(Γₑ, Γₜ)  ⟦e₂⟧ₑ(Γₑ, Γₜ)

⟦e @A⟧ₑ(Γₑ, Γₜ)  =  ⟦e⟧ₑ(Γₑ, Γₜ) @⟦A⟧ₜ(Γₑ, Γₜ)

⟦{l = e}⟧ₑ(Γₑ, Γₜ)  =  {l = ⟦e⟧ₑ(Γₑ, Γₜ)}

⟦e.l⟧ₑ(Γₑ, Γₜ)  =  ⟦e⟧ₑ(Γₑ, Γₜ).l

⟦e : A⟧ₑ(Γₑ, Γₜ)  =  ⟦e⟧ₑ(Γₑ, Γₜ) : ⟦A⟧ₜ(Γₑ, Γₜ)

⟦Δ⟧ₑ(Γₑ, Γₜ)  =  ⟦Δ⟧ᵈ(Γₑ, Γₜ)

⟦[Δ] ▷ e⟧ₑ(Γₑ, Γₜ)  =  [⟦Δ⟧ᵈ(Γₑ, Γₜ)] ▷ ⟦e⟧ₑ(expNames(Δ), typeNames(Δ))

⟦⟨Δ | λx. e⟩⟧ₑ(Γₑ, Γₜ)  =  ⟨⟦Δ⟧ᵈ(Γₑ, Γₜ) | λ. ⟦e⟧ₑ(expNames(Δ), typeNames(Δ))⟩

⟦⟨Δ | Λt. e⟩⟧ₑ(Γₑ, Γₜ)  =  ⟨⟦Δ⟧ᵈ(Γₑ, Γₜ) | Λ. ⟦e⟧ₑ(expNames(Δ), typeNames(Δ))⟩
```

### Environment Translation

Environments are translated right-to-left. Each entry sees bindings from entries to its right:
```
⟦_⟧ᵈ : ExpCtx → TypeCtx → Env → Env'


⟦·⟧ᵈ(Γₑ, Γₜ)  =  ·

⟦(x = e), Δ⟧ᵈ(Γₑ, Γₜ)  =  ⟦e⟧ₑ(expNames(Δ) ++ Γₑ, typeNames(Δ) ++ Γₜ), ⟦Δ⟧ᵈ(Γₑ, Γₜ)

⟦(m = e), Δ⟧ᵈ(Γₑ, Γₜ)  =  {m = ⟦e⟧ₑ(expNames(Δ) ++ Γₑ, typeNames(Δ) ++ Γₜ)}, ⟦Δ⟧ᵈ(Γₑ, Γₜ)

⟦(t = A), Δ⟧ᵈ(Γₑ, Γₜ)  =  ⟦A⟧ₜ(expNames(Δ) ++ Γₑ, typeNames(Δ) ++ Γₜ), ⟦Δ⟧ᵈ(Γₑ, Γₜ)
```

**Note:** Module bindings `m = e` become labeled records `{m = e'}` in the nameless form.

### Type Translation
```
⟦_⟧ₜ : ExpCtx → TypeCtx → Type → Type'


⟦β⟧ₜ(Γₑ, Γₜ)  =  β                                        (base types)

⟦t⟧ₜ(Γₑ, Γₜ)  =  indexₜ(t, Γₜ)

⟦A → B⟧ₜ(Γₑ, Γₜ)  =  ⟦A⟧ₜ(Γₑ, Γₜ) → ⟦B⟧ₜ(Γₑ, Γₜ)

⟦∀t. A⟧ₜ(Γₑ, Γₜ)  =  ∀. ⟦A⟧ₜ(Γₑ, t :: Γₜ)

⟦[Γ] ▷ A⟧ₜ(Γₑ, Γₜ)  =  [⟦Γ⟧ᵧ(Γₑ, Γₜ)] ▷ ⟦A⟧ₜ(·, tyNames(Γ))

⟦[t := A] B⟧ₜ(Γₑ, Γₜ)  =  [⟦A⟧ₜ(Γₑ, Γₜ)] ⟦B⟧ₜ(Γₑ, t :: Γₜ)

⟦{l : A}⟧ₜ(Γₑ, Γₜ)  =  {l : ⟦A⟧ₜ(Γₑ, Γₜ)}

⟦Env[Γ]⟧ₜ(Γₑ, Γₜ)  =  Env[⟦Γ⟧ᵧ(Γₑ, Γₜ)]
```

### Type Environment Translation
```
⟦_⟧ᵧ : ExpCtx → TypeCtx → TyEnv → TyEnv'


⟦·⟧ᵧ(Γₑ, Γₜ)  =  ·

⟦(t : A), Γ⟧ᵧ(Γₑ, Γₜ)  =  ⟦A⟧ₜ(Γₑ, tyNames(Γ) ++ Γₜ), ⟦Γ⟧ᵧ(Γₑ, Γₜ)

⟦(t : *), Γ⟧ᵧ(Γₑ, Γₜ)  =  *, ⟦Γ⟧ᵧ(Γₑ, Γₜ)

⟦(t = A), Γ⟧ᵧ(Γₑ, Γₜ)  =  (= ⟦A⟧ₜ(Γₑ, tyNames(Γ) ++ Γₜ)), ⟦Γ⟧ᵧ(Γₑ, Γₜ)
```

### Helper Functions
```
expNames : Env → ExpCtx
expNames(·)            =  ·
expNames((x = e), Δ)   =  (x, Term) :: expNames(Δ)
expNames((m = e), Δ)   =  (m, Mod) :: expNames(Δ)
expNames((t = A), Δ)   =  expNames(Δ)


typeNames : Env → TypeCtx
typeNames(·)           =  ·
typeNames((x = e), Δ)  =  typeNames(Δ)
typeNames((m = e), Δ)  =  typeNames(Δ)
typeNames((t = A), Δ)  =  t :: typeNames(Δ)


tyNames : TyEnv → TypeCtx
tyNames(·)             =  ·
tyNames((t : A), Γ)    =  tyNames(Γ)              (* annotations don't bind *)
tyNames((t : *), Γ)    =  t :: tyNames(Γ)
tyNames((t = A), Γ)    =  t :: tyNames(Γ)
```

### Entry Point
```
toDeBruijn : Exp → Exp'
toDeBruijn(e)  =  ⟦e⟧ₑ(·, ·)
```

---

## Worked Example

### Source (EnvML)
```ml
let m = struct let x = 1 end;
let v = m.x;
```

### After Elaboration (Named Core FE)
```
Δ = [m = [{x = 1}], v = m.x]
```

With environment entries:
- `m = [{x = 1}]` is a **module binding**
- `v = m.x` is a **term binding**

### De Bruijn Transformation

**Step 1:** Process `v = m.x`

- Context: `Γₑ = [(m, Mod)]` (from entry to the right)
- `m` is a module variable, so `⟦m⟧ₑ = [0].m`
- `⟦m.x⟧ₑ = [0].m.x`
- Term binding becomes: `{v = [0].m.x}`

**Step 2:** Process `m = [{x = 1}]`

- Context: `Γₑ = ·` (no entries to the right)
- Module binding becomes: `{m = [{x = 1}]}`

### After De Bruijn (Nameless Core FE)
```
[{m = [{x = 1}]}, {v = [0].m.x}]
```

Now the projection works correctly:
- `[0]` wraps index 0 in an environment, giving `[{m = [...]}]`
- `.m` projects the module contents `[{x = 1}]`
- `.x` projects the field `1`