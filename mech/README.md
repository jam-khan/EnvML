# Mechanization: Polymorphic First-Class Environments

- Title of the submitted paper: **Polymorphic First-Class Environments**

## Introduction
This is the mechanical formalization of the $F_{E}$ calculus associated with the paper: Polymorphic First-Class Environments. All of the metatheory has been formalized in the Rocq theorem prover. The development is split into two folders: `fe_calculus`, for the explicitly-typed calculus (the main calculus presented in the paper), and `fe_implicit`, for the implicitly-typed variant (introduced in Section 5.2 and Appendix F).

## Correspondence between paper and Rocq proofs

### Explicitly-typed calculus (folder `fe_calculus`)

| Paper           | File             | Name in Rocq         |
| --------------- | ---------------- | -------------------- |
| Theorem 3.1                         | Teq.v      | teq_refl            |
| Theorem 3.2                            | Teq.v      | teq_sym             |
| Theorem 3.3                        | Teq.v      | teq_trans           |
| Theorem 3.4  | Erased.v   | sem_erase           |
| Lemma 4.1                         | Teq.v      | inst_teq            |
| Lemma 4.2             | Teq.v      | inst_teq_gen        |
| Lemma 4.3         | Teq.v      | teq_spine_keyLen    |
| Lemma 4.4                  | Teq.v      | dead_star_r         |
| Lemma 4.5  | Safety.v   | inst_typ            |
| Lemma 4.6              | Safety.v   | inst_typ_sp         |
| Lemma 4.7              | Decide.v   | teq_dec_size        |
| Corollary 4.8                      | Decide.v   | teq_dec             |
| Lemma 4.9       | Safety.v   | clos_inv            |
| Lemma 4.10      | Safety.v   | bclos_inv           |
| Lemma 4.11                   | Safety.v   | lookupv_prog        |
| Lemma 4.12               | Safety.v   | lookupv_pres        |
| Theorem 4.13               | Safety.v   | gprogress           |
| Theorem 4.14           | Safety.v   | gpreservation       |
| Lemma 4.15                     | Safety.v   | value_boxing        |
| Lemma 4.16        | Safety.v   | vtyp_refl           |
| Theorem 4.17                           | Safety.v   | progress            |
| Theorem 4.18                       | Safety.v   | preservation        |
| Theorem 4.19                | LogRel.v   | sem_sound           |
| Corollary 4.20                    | LogRel.v   | normalization       |
| Theorem 4.21         | Conserve.v | ccomplete           |
| Lemma 4.22    | Conserve.v | relate_gen          |
| Theorem 4.23       | Conserve.v | cconserve           |
| Lemma 4.24               | Conserve.v | cconserve_relaxed   |
| Lemma 4.25                           | Conserve.v | teq_tt_eq           |
| Theorem 4.26       | Conserve.v | dyn_complete        |
| Theorem 4.27     | Conserve.v | cdyn_conserve       |
| Theorem E.1                 | LogRel.v   | sem_sound           |
| Lemma E.2         | LogRel.v   | comp_eq             |
| Corollary E.3                     | LogRel.v   | normalization       |


### Implicitly-typed variant (folder `fe_implicit`)

| Paper           | File                       | Name in Rocq        |
| --------------- | -------------------------- | ------------------- |
| Theorem F.1             | LogRel.v                 | sem_sound         |
| Corollary F.2                 | LogRel.v                 | normalization     |
| Theorem F.3      | Conserve.v               | complete          |
| Theorem F.4    | Conserve.v               | conserve_new      |
| Theorem F.5    | DynamicConservativity.v  | dyn_complete_imp  |
| Theorem F.6  | DynamicConservativity.v  | dyn_conserve_imp  |

## Prerequisites

Our Rocq proofs are verified in **Rocq 9.1.1**. The recommended way to install Rocq is via `OPAM`. Please refer to [here](https://opam.ocaml.org/) for detailed steps. Alternatively, one could download the pre-built packages for Windows and MacOS via [here](https://github.com/rocq-prover/rocq/releases/tag/V9.1.1) (9.1.1). Choose a suitable installer according to your platform.

Make sure `Rocq` is installed (type `coqc` in the terminal, if you see "command not found" this means you have not properly installed Rocq).

We rely on Rocq library: [`LibTactics.v`](http://gallium.inria.fr/~fpottier/ssphs/LibTactics.html) (which is already included in both folders `fe_calculus` and `fe_implicit`) in our proofs.

## Build and Compile the Proofs
This development contains two folders, `fe_calculus` (the explicit calculus) and `fe_implicit` (the implicit calculus). Each folder is self-contained and is built the same way.
1. Enter the `fe_calculus` or `fe_implicit` directory.
2. Please make sure to run the command `$ eval $(opam env)` before running `make` if you installed Rocq via opam.
3. Type `make` in the terminal to build and compile the proofs.
4. You can remove the compiled proofs by `make clean`.
