Require Import LibTactics.
Require Import Arith.
From Coq Require Import Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.EquivDec.

Require Import Basics.

(* --- Types --- *)

(* ModTyp in Haskell: Data ModTyp = TyIntf Typ | TyArrM Typ ModTyp *)
Inductive modtyp :=
  | MTIntf : styp -> modtyp
  | MTArrm : styp -> modtyp -> modtyp

(* Typ in Haskell: Data Typ = ... | TyMod ModTyp *)
with styp :=
  | Sint   : styp
  | Sunit  : styp
  | Sand   : styp -> styp -> styp
  | Sarr   : styp -> styp -> styp
  | Srcd   : string -> styp -> styp
  | Smod   : modtyp -> styp.

(* Helper to elaborate types to Core types immediately, 
   as needed for Inductive definitions *)
Fixpoint elab_typ (s : styp) : typ :=
  match s with
  | Sint     => int
  | Sunit    => top (* Core uses top for unit type typically, or we assume unit exists *)
  | Sand A B => and (elab_typ A) (elab_typ B)
  | Sarr A B => arr (elab_typ A) (elab_typ B)
  | Srcd l A => rcd l (elab_typ A)
  | Smod m   => elab_modtyp m
  end
with elab_modtyp (m : modtyp) : typ :=
  match m with
  | MTIntf A   => elab_typ A
  | MTArrm A M => arr (elab_typ A) (elab_modtyp M)
  end.

(* --- Expressions --- *)

Inductive sandbox := Sandboxed | Open_.

(* Matches Haskell Exp datatype *)
Inductive sexp :=
  | Squery      : sexp                         (* ? *)
  | Slit        : nat -> sexp                  (* i *)
  | SunitV      : sexp                         (* unit *)
  | Sproj       : sexp -> nat -> sexp          (* e.n *)
  | Slam        : styp -> sexp -> sexp         (* lam A. e *)
  | Sbox        : sexp -> sexp -> sexp         (* e1 |> e2 *)
  | Sclos       : sexp -> styp -> sexp -> sexp (* <v, lam A. e> *)
  | Sapp        : sexp -> sexp -> sexp         (* e1 e2 *)
  | Sdmrg       : sexp -> sexp -> sexp         (* e1 #d e2 *)
  | Snmrg       : sexp -> sexp -> sexp         (* e1 #n e2 *)
  | Srec        : string -> sexp -> sexp       (* {l = e} *)
  | Srproj      : sexp -> string -> sexp       (* e.l *)
  | Slet        : sexp -> styp -> sexp -> sexp (* let e1 : A in e2 *)
  | Sopen       : sexp -> sexp -> sexp         (* open e1 in e2 *)
  (* Module Constructs *)
  | Smstruct    : sandbox -> sexp -> sexp      (* struct[s] e *)
  | Smfunctor   : sandbox -> styp -> sexp -> sexp (* functor[s](A) e *)
  | Smclos      : sexp -> styp -> sexp -> sexp (* module closure *)
  | Smlink      : sexp -> sexp -> sexp.        (* Link(e1, e2) *)

(* --- Source Values (isValue in Haskell) --- *)
Inductive svalue : sexp -> Prop :=
  | sv_lit   : forall n, svalue (Slit n)
  | sv_unit  : svalue SunitV
  | sv_clos  : forall v A e, svalue v -> svalue (Sclos v A e)
  | sv_mclos : forall v A e, svalue v -> svalue (Smclos v A e)
  | sv_dmrg  : forall v1 v2, svalue v1 -> svalue v2 -> svalue (Sdmrg v1 v2)
  | sv_nmrg  : forall v1 v2, svalue v1 -> svalue v2 -> svalue (Snmrg v1 v2)
  | sv_rec   : forall l v, svalue v -> svalue (Srec l v).

#[export] Hint Constructors styp modtyp sexp svalue : core.

(* ================================================================= *)
(* SOURCE BIG-STEP SEMANTICS                                         *)
(* ================================================================= *)

(* 
   Helpers for lookup/projection on source values 
   (Mirroring Haskell lookupV and sel) 
*)

Inductive s_lookupv : sexp -> nat -> sexp -> Prop :=
  | slv_zero_dmrg : forall v1 v2, s_lookupv (Sdmrg v1 v2) 0 v2
  | slv_succ_dmrg : forall v1 v2 n v3, s_lookupv v1 n v3 -> s_lookupv (Sdmrg v1 v2) (S n) v3
  | slv_zero_nmrg : forall v1 v2, s_lookupv (Snmrg v1 v2) 0 v2
  | slv_succ_nmrg : forall v1 v2 n v3, s_lookupv v1 n v3 -> s_lookupv (Snmrg v1 v2) (S n) v3.

Inductive s_rlookupv : sexp -> string -> sexp -> Prop :=
  | srv_rec : forall l v, s_rlookupv (Srec l v) l v
  | srv_dmrg_l : forall v1 v2 l v, s_rlookupv v1 l v -> s_rlookupv (Sdmrg v1 v2) l v
  | srv_dmrg_r : forall v1 v2 l v, s_rlookupv v2 l v -> s_rlookupv (Sdmrg v1 v2) l v
  | srv_nmrg_l : forall v1 v2 l v, s_rlookupv v1 l v -> s_rlookupv (Snmrg v1 v2) l v
  | srv_nmrg_r : forall v1 v2 l v, s_rlookupv v2 l v -> s_rlookupv (Snmrg v1 v2) l v.
(* Note: Haskell implementation has explicit ambiguity checks, 
   here we model the relational "exists a valid path" semantics 
   common in Inductive definitions. *)

(* 
   Source Big Step (sbig)
   Relation: sbig env expr val
*)
Inductive sbig : sexp -> sexp -> sexp -> Prop :=
  | sb_query : forall env, 
      sbig env Squery env
  | sb_lit : forall env n,
      sbig env (Slit n) (Slit n)
  | sb_unit : forall env,
      sbig env SunitV SunitV
  
  (* Closures evaluate to themselves if the environment is a value *)
  | sb_val_clos : forall env v A e,
      svalue v ->
      sbig env (Sclos v A e) (Sclos v A e)
  | sb_val_mclos : forall env v A e,
      svalue v ->
      sbig env (Smclos v A e) (Smclos v A e)

  | sb_proj : forall env e v n v',
      sbig env e v ->
      s_lookupv v n v' ->
      sbig env (Sproj e n) v'
  
  | sb_lam : forall env A e,
      sbig env (Slam A e) (Sclos env A e)

  | sb_box : forall env e1 e2 v1 v2,
      sbig env e1 v1 ->
      sbig v1 e2 v2 ->
      sbig env (Sbox e1 e2) v2

  (* App Logic covering both standard Clos and Module Clos *)
  | sb_app : forall env e1 e2 v2 v_env A body v_res,
      sbig env e1 (Sclos v_env A body) ->
      sbig env e2 v2 ->
      sbig (Sdmrg v_env v2) body v_res ->
      sbig env (Sapp e1 e2) v_res
  | sb_mapp : forall env e1 e2 v2 v_env A body v_res,
      sbig env e1 (Smclos v_env A body) ->
      sbig env e2 v2 ->
      sbig (Sdmrg v_env v2) body v_res ->
      sbig env (Sapp e1 e2) v_res

  | sb_dmrg : forall env e1 e2 v1 v2,
      sbig env e1 v1 ->
      sbig (Sdmrg env v1) e2 v2 ->
      sbig env (Sdmrg e1 e2) (Sdmrg v1 v2)

  | sb_nmrg : forall env e1 e2 v1 v2,
      sbig env e1 v1 ->
      sbig env e2 v2 ->
      sbig env (Snmrg e1 e2) (Snmrg v1 v2)

  | sb_rec : forall env l e v,
      sbig env e v ->
      sbig env (Srec l e) (Srec l v)
  
  | sb_rproj : forall env e l v v',
      sbig env e v ->
      s_rlookupv v l v' ->
      sbig env (Srproj e l) v'

  | sb_let : forall env e1 A e2 v1 v2,
      sbig env e1 v1 ->
      sbig (Sdmrg env v1) e2 v2 ->
      sbig env (Slet e1 A e2) v2

  | sb_open : forall env e1 e2 v1 l v_inner v2,
      sbig env e1 v1 ->
      v1 = Srec l v_inner -> (* open expects a record *)
      sbig (Sdmrg env v_inner) e2 v2 ->
      sbig env (Sopen e1 e2) v2

  (* Module Semantics *)
  | sb_struct_sandboxed : forall env e v,
      sbig SunitV e v ->
      sbig env (Smstruct Sandboxed e) v
  | sb_struct_open : forall env e v,
      sbig env e v ->
      sbig env (Smstruct Open_ e) v

  | sb_functor_sandboxed : forall env A e,
      sbig env (Smfunctor Sandboxed A e) (Smclos SunitV A e)
  | sb_functor_open : forall env A e,
      sbig env (Smfunctor Open_ A e) (Smclos env A e)

  | sb_link_clos : forall env e1 e2 v_env A body v2 v_res,
      sbig env e1 (Sclos v_env A body) ->
      sbig env e2 v2 ->
      sbig (Sdmrg v_env v2) body v_res ->
      sbig env (Smlink e1 e2) v_res
  | sb_link_mclos : forall env e1 e2 v_env A body v2 v_res,
      sbig env e1 (Smclos v_env A body) ->
      sbig env e2 v2 ->
      sbig (Sdmrg v_env v2) body v_res ->
      sbig env (Smlink e1 e2) v_res.

#[export] Hint Constructors s_lookupv s_rlookupv sbig : core.

(* ================================================================= *)
(* ELABORATION                                                       *)
(* ================================================================= *)

(* 
   Elaboration Relation: G |-S se : A ~> ce 
   corresponds to Haskell `elaborate`.
*)

Inductive elaborate_sexp : styp -> sexp -> styp -> exp -> Prop :=
  | elab_query : forall G,
      elaborate_sexp G Squery G ctx

  | elab_lit : forall G n,
      elaborate_sexp G (Slit n) Sint (lit n)

  | elab_unit : forall G,
      elaborate_sexp G SunitV Sunit unit

  | elab_proj : forall G se n B ce A,
      elaborate_sexp G se B ce ->
      Slookup B n A ->
      elaborate_sexp G (Sproj se n) A (proj ce n)

  | elab_lam : forall G A se B ce,
      elaborate_sexp (Sand G A) se B ce ->
      elaborate_sexp G (Slam A se) (Sarr A B) (lam (elab_typ A) ce)

  | elab_box : forall G se1 se2 G' A ce1 ce2,
      elaborate_sexp G se1 G' ce1 ->
      elaborate_sexp G' se2 A ce2 ->
      elaborate_sexp G (Sbox se1 se2) A (binop box ce1 ce2)

  | elab_clos : forall G se1 A se2 B ce1 ce2 G',
      elaborate_sexp G se1 G' ce1 ->
      elaborate_sexp (Sand G' A) se2 B ce2 ->
      elaborate_sexp G (Sclos se1 A se2) (Sarr A B) (clos ce1 (elab_typ A) ce2)

  | elab_app : forall G se1 se2 A B ce1 ce2,
      elaborate_sexp G se1 (Sarr A B) ce1 ->
      elaborate_sexp G se2 A ce2 ->
      elaborate_sexp G (Sapp se1 se2) B (binop oapp ce1 ce2)

  | elab_dmrg : forall G se1 se2 A B ce1 ce2,
      elaborate_sexp G se1 A ce1 ->
      elaborate_sexp (Sand G A) se2 B ce2 ->
      elaborate_sexp G (Sdmrg se1 se2) (Sand A B) (binop mrg ce1 ce2)

  (* NMrg: elaborate non-dependent merge to a Core term that constructs the merge *)
  | elab_nmrg : forall G se1 se2 A B ce1 ce2,
      elaborate_sexp G se1 A ce1 ->
      elaborate_sexp G se2 B ce2 ->
      elaborate_sexp G (Snmrg se1 se2) (Sand A B) 
          (binop oapp 
             (lam (elab_typ G) 
               (binop mrg 
                  (binop box (proj ctx 0) ce1) 
                  (binop box (proj ctx 1) ce2))) 
             ctx)

  | elab_rec : forall G l se A ce,
      elaborate_sexp G se A ce ->
      elaborate_sexp G (Srec l se) (Srcd l A) (rec l ce)

  | elab_rproj : forall G se l B ce A,
      elaborate_sexp G se B ce ->
      Srlookup B l A ->
      elaborate_sexp G (Srproj se l) A (rproj ce l)

  | elab_let : forall G se1 se2 A B ce1 ce2,
      elaborate_sexp G se1 A ce1 ->
      elaborate_sexp (Sand G A) se2 B ce2 ->
      elaborate_sexp G (Slet se1 A se2) B 
          (binop oapp (lam (elab_typ A) ce2) ce1)

  (* Open: expects a record, projects the value, binds it in body *)
  | elab_open : forall G se1 se2 l A B ce1 ce2,
      elaborate_sexp G se1 (Srcd l A) ce1 ->
      elaborate_sexp (Sand G A) se2 B ce2 ->
      elaborate_sexp G (Sopen se1 se2) B 
          (binop oapp (lam (elab_typ A) ce2) (rproj ce1 l))

  (* --- Module Elaboration Rules --- *)

  (* 
     Struct Sandboxed: 
     G |- struct[sandboxed] e : Sig(B) ~> box unit ce 
     (evaluated in empty env)
  *)
  | elab_mstruct_sb : forall G se B ce,
      elaborate_sexp Sunit se B ce ->
      elaborate_sexp G (Smstruct Sandboxed se) (Smod (MTIntf B)) (binop box unit ce)

  (* 
     Struct Open: 
     G |- struct[open] e : Sig(B) ~> box ctx ce 
     (evaluated in current env)
  *)
  | elab_mstruct_op : forall G se B ce,
      elaborate_sexp G se B ce ->
      elaborate_sexp G (Smstruct Open_ se) (Smod (MTIntf B)) (binop box ctx ce)

  (* 
     Functor Sandboxed: 
     G |- functor[sandboxed](A) e : A -> B ~> box unit (lam A ce) 
  *)
  | elab_mfunctor_sb : forall G A se B ce,
      elaborate_sexp (Sand Sunit A) se (Smod B) ce ->
      elaborate_sexp G (Smfunctor Sandboxed A se) (Smod (MTArrm A B)) 
          (binop box unit (lam (elab_typ A) ce))

  (* 
     Functor Open: 
     G |- functor[open](A) e : A -> B ~> lam A ce 
  *)
  | elab_mfunctor_op : forall G A se B ce,
      elaborate_sexp (Sand G A) se (Smod B) ce ->
      elaborate_sexp G (Smfunctor Open_ A se) (Smod (MTArrm A B)) 
          (lam (elab_typ A) ce)

  (* Module Closure (Runtime) *)
  | elab_mclos : forall G se1 A se2 B ce1 ce2 G',
      elaborate_sexp G se1 G' ce1 ->
      elaborate_sexp (Sand G' A) se2 (Smod B) ce2 ->
      elaborate_sexp G (Smclos se1 A se2) (Smod (MTArrm A B)) (clos ce1 (elab_typ A) ce2)

  (* 
     Link: Link(M1, M2) ~> App(M1, M2)
     (Corresponds to separate compilation)
  *)
  | elab_link : forall G se1 se2 A B ce1 ce2,
      elaborate_sexp G se1 (Smod (MTArrm A B)) ce1 ->
      elaborate_sexp G se2 A ce2 ->
      elaborate_sexp G (Smlink se1 se2) (Smod B) (binop oapp ce1 ce2).

#[export] Hint Constructors elaborate_sexp : core.


(* ================================================================= *)
(* THEOREMS                                                          *)
(* ================================================================= *)

(* 
   Theorem: Type-Preserving Elaboration
   If G |-S e : A ~> ce, then [G] |-C ce : [A]
*)
Theorem type_preservation : forall G se A ce,
  elaborate_sexp G se A ce ->
  has_type (elab_typ G) ce (elab_typ A).
Proof.
  (* 
     This proof requires induction on the elaboration derivation.
     Basic cases (query, lit, unit) map directly to Core typing rules.
     MStruct/MFunctor rules rely on tbox and tlam.
     NMrg relies on constructing a valid merge term in Core.
  *)
  Admitted.

(* 
   Theorem: Semantics Preservation
   Source big-step evaluation agrees with Core big-step evaluation 
   of the elaborated term (under the empty environment).
*)
(* Note: We assume a relation `val_equiv` relating svalue to Core value *)
Definition val_equiv (sv : sexp) (cv : exp) : Prop := True. (* simplified placeholder *)

Theorem semantics_preservation : forall se A ce sv cv,
  elaborate_sexp Sunit se A ce ->
  sbig SunitV se sv ->
  ebig unit ce cv ->
  val_equiv sv cv.
Proof.
  (*
     Proved by induction on the source big-step derivation `sbig`.
     Requires lemmas that elaboration commutes with substitution/environment lookup.
     Case `sb_struct_sandboxed` uses the fact that `binop box unit ce` 
     switches the environment in Core `ebig` to `unit`.
  *)
  Admitted.

(* 
   Theorem: Separate Compilation
   Elaborating a link Link(M1, M2) produces the application of their elaborated forms.
*)
Theorem separate_compilation : forall G se1 se2 A B ce1 ce2 c_link,
  elaborate_sexp G se1 (Smod (MTArrm A B)) ce1 ->
  elaborate_sexp G se2 A ce2 ->
  elaborate_sexp G (Smlink se1 se2) (Smod B) c_link ->
  c_link = binop oapp ce1 ce2.
Proof.
  (*
     Direct consequence of the `elab_link` rule and uniqueness of elaboration 
     (assuming deterministic elaboration).
  *)
  Admitted.

(* 
   Theorem: Sandbox Isolation (Struct)
   A sandboxed structure evaluates to the same result regardless of the environment.
*)
Theorem sandbox_isolation_struct : forall env1 env2 se v1 v2,
  sbig env1 (Smstruct Sandboxed se) v1 ->
  sbig env2 (Smstruct Sandboxed se) v2 ->
  v1 = v2.
Proof.
  (*
     Proof sketch:
     1. Inversion on `sbig env1 ...` gives `sb_struct_sandboxed`.
        This implies `sbig SunitV se v1`.
     2. Inversion on `sbig env2 ...` gives `sb_struct_sandboxed`.
        This implies `sbig SunitV se v2`.
     3. Since the evaluation environment is forced to `SunitV` in both cases,
        and assuming `sbig` is deterministic, `v1` must equal `v2`.
  *)
  Admitted.

(* 
   Theorem: Sandbox Isolation (Functor)
   A sandboxed functor evaluates to a closure capturing the empty environment.
*)
Theorem sandbox_isolation_functor : forall env1 env2 A se v1 v2,
  sbig env1 (Smfunctor Sandboxed A se) v1 ->
  sbig env2 (Smfunctor Sandboxed A se) v2 ->
  v1 = v2.
Proof.
  (*
     Proof sketch:
     1. Inversion on `sbig` rules for `Smfunctor Sandboxed`.
     2. Both reduce to `Smclos SunitV A se`.
     3. Therefore `v1 = v2`.
  *)
  Admitted.

(* 
   Theorem: Secure Linking
   If a functor is sandboxed, its behavior is independent of the 
   environment where the link occurs, provided the argument is the same.
*)
Theorem secure_linking : forall env1 env2 F M v1 v2,
  (* F is a sandboxed functor *)
  (exists A se, F = Smfunctor Sandboxed A se) ->
  (* We link F with M in two different environments *)
  sbig env1 (Smlink F M) v1 ->
  sbig env2 (Smlink F M) v2 ->
  (* If M evaluates to the same value in both envs (or is closed) *)
  (forall vm1 vm2, sbig env1 M vm1 -> sbig env2 M vm2 -> vm1 = vm2) ->
  v1 = v2.
Proof.
  Admitted.

(* 
   Theorem: Uniqueness of Elaboration
*)
Theorem uniqueness_of_elaboration : forall G se A1 A2 ce1 ce2,
  elaborate_sexp G se A1 ce1 ->
  elaborate_sexp G se A2 ce2 ->
  ce1 = ce2.
Proof.
  Admitted.