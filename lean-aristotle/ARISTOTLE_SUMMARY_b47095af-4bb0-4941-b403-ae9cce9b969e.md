# Summary of changes
## Summary

I systematically filled sorries in `Theories.lean` and fixed several formalization bugs discovered during the proof process. Here's what was accomplished:

### Theorems fully proved (sorry-free):
1. **`ValTrans.sce_value`** — ValTrans implies SCE Value (new helper theorem)
2. **`ValTrans.core_value`** — ValTrans implies Core Value (new helper theorem)
3. **`type_elaboration_uniqueness`** — already proved
4. **`index_lookup_uniqueness`** — already proved
5. **`record_lookup_uniqueness`** — proved by induction on RecordLookup
6. **`type_safe_index_lookup`** — already proved
7. **`type_safe_label_existence`** — both directions proved (required adding `sig_intf` constructor to `SCE.LabelIn`)
8. **`type_safe_label_nonexistence`** — follows from `type_safe_label_existence`
9. **`type_safe_record_lookup`** — proved via `type_safe_label_existence`
10. **`val_trans_index_lookup`** — proved by induction

### Theorems partially proved (some cases sorry):
11. **`inference_uniqueness`** — 15 of 17 cases proved. Remaining: `mapp`/`mlink` (see below)
12. **`type_preservation`** — 14 of 19 cases proved (query, lit, unit, proj, lam, app, box, dmrg, lrec, rproj, letb, openm, mstruct, mfunctor, mapp). Remaining: clos, nmrg, mclos, mlink
13. **`elaboration_uniqueness`** — proved (depends on inference_uniqueness sorry)
14. **`semantics_preservation`** — sorry (complex induction, budget exhausted)
15. **`separate_compilation`** — follows from semantics_preservation

### Formalization bugs discovered and fixed:

1. **`HasType.tapp`** (`Core/Typing.lean`): Second premise used `B` (return type) instead of `A` (argument type). Fixed.

2. **`elabExp.mfunctor`** (`Elaboration.lean`): Output type was unconstrained `Typ.sig mt` with `mt` free. Fixed to `Typ.sig (ModTyp.TyArrM A (ModTyp.TyIntf B))`.

3. **`elabExp.mclos`** (`Elaboration.lean`): Same issue — `mt` unconstrained. Fixed similarly.

4. **`ValTrans.vmclos`** (`Theories.lean`): Matching fix for constrained `mt`.

5. **`SCE.LabelIn`** (`SCE/Syntax.lean`): Missing constructor for `sig (TyIntf A)` types. Added `sig_intf` constructor.

### Known remaining issues:

- **`inference_uniqueness` for `mapp`/`mlink`**: Both rules elaborate `Exp.mlink` but produce different result types (`sig mt` vs `sig (TyArrM A mt)`). This makes type uniqueness genuinely unprovable. Fix would require separate source constructors (`Exp.mapp` vs `Exp.mlink`).

- **`type_preservation` for `clos`/`mclos`**: `HasType.tclos` requires `Value` and `HasType .top` premises not available from the induction hypothesis.

- **`type_preservation` for `nmrg`**: The core expression requires typing `proj query 1` which needs a nested `Lookup` on `elabTyp ctx` — only works if ctx is already an intersection type.

- **`type_preservation` for `mlink`**: Requires a weakening lemma (typing under larger context) or a non-dependent merge typing rule.