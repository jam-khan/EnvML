# Working context — EnvML / FE

Handoff note. **The Rocq mechanization is finished.** Read §1, then §4 if you
need to change anything.

---

## 1. Where things stand

**Haskell: done and committed** (`7b20cfb`, branch `POPL-27`).

**Rocq: done, unstaged.** `mech/fe_calculus/source/` has four files that compile
under a full `make`, with no admits and no axioms.

```coq
Theorem elab_preservation : forall G M e A, elab G M e A -> has_type G e A.
```

`Print Assumptions` reports *Closed under the global context* for both
`elab_preservation` and `elabd_preservation`.

`mech/` is **gitignored**, so none of this is under version control. `git status`
does not reflect it.

| File | Lines | Contents |
|---|---:|---|
| `source/Syntax.v` | 67 | `smod` / `sdecl`, `sig_shape`, `has_lbl`, `unique_labels` |
| `source/Elaboration.v` | 133 | `numv`, `expands`, `elab` / `elabd`, the mutual scheme |
| `source/Lemmas.v` | 258 | foundations, merge infrastructure, twelve `comp_*` lemmas |
| `source/Preservation.v` | 32 | the theorem |

`Probe.v` is gone; its five lemmas are §1 of `Lemmas.v`.

## 2. Building

```bash
cd mech/fe_calculus
export PATH="$HOME/.opam/default/bin:$PATH"
make
```

A full `make` from the current state is a no-op. From clean it is slow, mostly
`Teq.v` and `Safety.v`. The four `source/` files need only `Teq.v` and
`Safety.v`, and compile in seconds:

```bash
for f in Syntax Elaboration Lemmas Preservation; do coqc -R . Top source/$f.v; done
```

**Gotcha:** installing into the `default` opam switch can replace `rocq-stdlib`
and invalidate every `.vo` ("makes inconsistent assumptions over library
Corelib.Init.Prelude"). Delete the `.vo` files and rebuild.

Toolchain: Rocq 9.1.0 at `~/.opam/default/bin/coqc`; `pet` 0.2.5; rocq-mcp 0.3.1
registered as `rocq` in `~/.claude.json`. The `rocq_*` MCP tools show goal state
interactively and are much faster than reading `coqc` errors.

## 3. What the proof turned out to be

The design in the plan file survived intact except for one point, which is the
only thing here worth re-reading.

**The operand's de Bruijn index is not stable.** The plan assumed the shifts a
merge introduces vanish. They vanish on the *type* but not on the *index*.
`Lemmas.v` defines

```coq
Fixpoint numv (T : typ) : nat :=          (* term entries in T's left spine *)
  match T with
  | and T1 non _ => S (numv T1)
  | and T1 rt  _ => numv T1
  | ands T1      => numv T1
  | _            => 0
  end.
```

and proves the growth lemma unconditionally — no `lshape`, no closedness:

```coq
Lemma get_var_grow_gen : forall D T n A,
  get_var T n A -> get_var (T +++ D) (numv D + n) (mshift D A).
```

Closedness enters only to collapse the type, through `mshift_closed`, which
rests on `closed_tshift_id`. So `expands` emits
`rproj (var (numv Gd1 + k)) l`, not a constant index: every labelled entry
already emitted pushes a term binder and the operand recedes by one.  So in a
two-operand merge, operand 2 is nominally at index 0 but is reached at index 1
once operand 1 has contributed a labelled entry.

The two lemmas the plan budgeted at ~150 lines, `insert_tvar_mopen` and
`insert_tvar_rlk`, were never needed. Neither was a general typing weakening
lemma. Total is 490 lines against a budget of ~830.

`expands` carries the ambient so a transparent entry can state its own
well-formedness premise:

```coq
Inductive expands : typ -> nat -> typ -> typ -> exp -> typ -> exp -> typ -> Prop
  (* Amb  k  Gsrc  Gtodo  dIn  GIn  dOut  GOut *)
```

`expands_sound` is 14 lines. `comp_merge` is 17. `Preservation.v` is one
`apply elab_elabd_mut; intros; eauto using comp_*`.

## 4. Design decisions already settled — do not relitigate

**A merge's result type is the signature `expands` builds, not the flat
`Γ2 ++ Γ1`.** `rlk_hit` returns the `mopen`-wrapped type: projecting `x` from
`sig type A = int; val x : A -> A; end` gives `mani int (A -> A)`, not the bare
arrow. Reconciling that with a written
signature happens at the ascription via `e_eq`, whose `teq` premise `teq_dec`
(Decide.v) discharges for any concrete program. This mirrors `has_type`'s own
`t_eq`, and the theorem stays unconditional.

**Ordering is preserved.** `eq_and` matches constructor by constructor, so a
reordered signature is not `teq` to the declared one.

**`e_merge` requires both operand signatures closed** (`wft top G1`,
`wft top G2`), plus `sig_shape` and `unique_labels`, which are
`checkComposable`'s side conditions. Closedness is the sandbox discipline: `++`
flattens two independently-typed modules. Elab.hs's dependent `+` on two
literal structs does not go through `expandMerge` at all — it flattens into one
declaration block, which is `s_struct` here.

**`s_var n l` is a projection**, `rproj (var n) l`, matching Elab.hs's bare
`RProj`. The plan's `(unit ,, var n) - l` also typechecks but is not what the
implementation emits.

**A struct is `s_box (s_struct D)`.** Elab.hs's `box0` around a struct or
functor is the `s_box` wrapper; `s_struct` alone is `elabBodyRaw`.

## 5. Out of scope, and say so in the paper

Named-to-nameless resolution stays an unverified scope-checking pass
(`DeBruijn.hs` still calls `error` on an unbound name, which kills the REPL).
Elaboration completeness, dynamic correspondence, and the implicit variant are
not addressed. The adequacy corollary — that a merge's computed signature is
`teq` to the flat `Γ2 ++ Γ1` — is not needed for preservation and is not proved.
The Rocq `typ` has no list or string type, so examples using them are not
representable; the theorem is over the Rocq calculus.
