Require Import Arith.
From Coq Require Import Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.EquivDec.
Require Import Program.Equality.
Require Import Basics.
Require Import Big.

(* ============================================================ *)
(* Source types                                                  *)
(* ============================================================ *)

Inductive smodtyp :=
  | StyIntf : styp -> smodtyp
  | StyArrM : styp -> smodtyp -> smodtyp

with styp :=
  | Sint  : styp
  | Stop  : styp
  | Sarr  : styp -> styp -> styp
  | Sand  : styp -> styp -> styp
  | Srcd  : string -> styp -> styp
  | Smod  : smodtyp -> styp.

(* ============================================================ *)
(* Source expressions                                           *)
(* ============================================================ *)

Inductive sandbox := Sandboxed | Open.

Inductive sexp :=
  | Sctx      : sexp
  | Sunit     : sexp
  | Slit      : nat -> sexp
  | Slam      : styp -> sexp -> sexp
  | Sbox      : sexp -> sexp -> sexp
  | SClos     : sexp -> styp -> sexp -> sexp
  | Sapp      : sexp -> sexp -> sexp
  | SDmrg     : sexp -> sexp -> sexp
  | Sproj     : sexp -> nat -> sexp
  | Srec      : string -> sexp -> sexp
  | Srproj    : sexp -> string -> sexp
  (* Terms to be elaborated *)
  | SNmrg     : sexp -> sexp -> sexp
  | Slet      : sexp -> styp -> sexp -> sexp
  | Sopen     : sexp -> sexp -> sexp
  | SStruct   : sandbox -> sexp -> sexp
  | SFunctor  : sandbox -> styp -> sexp -> sexp
  | SMClos    : sexp -> styp -> sexp -> sexp
  | SMLink    : sexp -> sexp -> sexp.

(* ============================================================ *)
(* Source type elaboration                                      *)
(* ============================================================ *)

Fixpoint elaborate_modtyp (mt : smodtyp) : typ :=
  match mt with
  | StyIntf A    => elaborate_typ A
  | StyArrM A mt => arr (elaborate_typ A) (elaborate_modtyp mt)
  end

with elaborate_typ (s : styp) : typ :=
  match s with
  | Sint      => int
  | Stop      => top
  | Sarr A B  => arr (elaborate_typ A) (elaborate_typ B)
  | Sand A B  => and (elaborate_typ A) (elaborate_typ B)
  | Srcd l A  => rcd l (elaborate_typ A)
  | Smod mt   => elaborate_modtyp mt
  end.

(* ============================================================ *)
(* Source lookup                                                *)
(* ============================================================ *)

Inductive Slookup : styp -> nat -> styp -> Prop :=
  | Slzero : forall A B,
      Slookup (Sand A B) 0 B
  | Slsucc : forall A B n C,
      Slookup A n C ->
      Slookup (Sand A B) (S n) C.

Inductive Slin : string -> styp -> Prop :=
  | Slin_rcd  : forall A l, Slin l (Srcd l A)
  | Slin_andl : forall A B l, Slin l A -> Slin l (Sand A B)
  | Slin_andr : forall A B l, Slin l B -> Slin l (Sand A B).

Inductive Srlookup : styp -> string -> styp -> Prop :=
  | Srlzero : forall l B,
      Srlookup (Srcd l B) l B
  | Slandl : forall A B C l,
      Srlookup A l C ->
      ~ Slin l B ->
      Srlookup (Sand A B) l C
  | Slandr : forall A B C l,
      Srlookup B l C ->
      ~ Slin l A ->
      Srlookup (Sand A B) l C.

(* ============================================================ *)
(* Elaboration judgment                                         *)
(* ============================================================ *)

(* Helper: compute the module type from a functor body type *)
Definition mk_functor_modtyp (tyA : styp) (tyB : styp) : smodtyp :=
  match tyB with
  | Smod innerMt => StyArrM tyA innerMt
  | _            => StyArrM tyA (StyIntf tyB)
  end.

Inductive elaborate_sexp : styp -> sexp -> styp -> exp -> Prop :=

  (* --- core expression rules --- *)
  | infctx : forall E,
      elaborate_sexp E Sctx E ctx

  | infint : forall E n,
      elaborate_sexp E (Slit n) Sint (lit n)

  | infunit : forall E,
      elaborate_sexp E Sunit Stop unit

  | infproj : forall E n Se e A B,
      elaborate_sexp E Se B e ->
      Slookup B n A ->
      elaborate_sexp E (Sproj Se n) A (proj e n)

  | inflam : forall E A Se e B,
      elaborate_sexp (Sand E A) Se B e ->
      elaborate_sexp E (Slam A Se) (Sarr A B) (lam (elaborate_typ A) e)

  | infbox : forall E E' A Se1 Se2 e1 e2,
      elaborate_sexp E Se1 E' e1 ->
      elaborate_sexp E' Se2 A e2 ->
      elaborate_sexp E (Sbox Se1 Se2) A (binop box e1 e2)

  | infclos : forall E E' A B Se1 Se2 e1 e2,
      elaborate_sexp E Se1 E' e1 ->
      elaborate_sexp (Sand E' A) Se2 B e2 ->
      elaborate_sexp E (SClos Se1 A Se2) (Sarr A B)
        (clos e1 (elaborate_typ A) e2)

  | infapp : forall E A B sE1 sE2 cE1 cE2,
      elaborate_sexp E sE1 (Sarr A B) cE1 ->
      elaborate_sexp E sE2 A cE2 ->
      elaborate_sexp E (Sapp sE1 sE2) B (binop app cE1 cE2)

  | infdmrg : forall E A1 A2 sE1 sE2 e1 e2,
      elaborate_sexp E sE1 A1 e1 ->
      elaborate_sexp (Sand E A1) sE2 A2 e2 ->
      elaborate_sexp E (SDmrg sE1 sE2) (Sand A1 A2) (binop mrg e1 e2)

  | infrcd : forall E A Se l e,
      elaborate_sexp E Se A e ->
      elaborate_sexp E (Srec l Se) (Srcd l A) (rec l e)

  | infrproj : forall E A B Se e l,
      elaborate_sexp E Se B e ->
      Srlookup B l A ->
      elaborate_sexp E (Srproj Se l) A (rproj e l)

  | infnmrg : forall E A1 A2 sE1 sE2 e1 e2,
      elaborate_sexp E sE1 A1 e1 ->
      elaborate_sexp E sE2 A2 e2 ->
      elaborate_sexp E (SNmrg sE1 sE2) (Sand A1 A2)
        (binop app
          (lam (elaborate_typ E)
            (binop mrg
              (binop box (proj ctx 0) e1)
              (binop box (proj ctx 1) e2)))
          ctx)

  | inflet : forall E A B Se1 Se2 e1 e2,
      elaborate_sexp E Se1 A e1 ->
      elaborate_sexp (Sand E A) Se2 B e2 ->
      elaborate_sexp E (Slet Se1 A Se2) B
        (binop app (lam (elaborate_typ A) e2) e1)

  | infopen : forall E A B l Se1 e1 Se2 e2,
      elaborate_sexp E Se1 (Srcd l A) e1 ->
      elaborate_sexp (Sand E A) Se2 B e2 ->
      elaborate_sexp E (Sopen Se1 Se2) B
        (binop app (lam (elaborate_typ A) e2) (rproj e1 l))

  | infstruct_sandboxed : forall E B Se ce,
      elaborate_sexp Stop Se B ce ->
      elaborate_sexp E (SStruct Sandboxed Se) (Smod (StyIntf B))
        (binop box unit ce)

  | infstruct_open : forall E B Se ce,
      elaborate_sexp E Se B ce ->
      elaborate_sexp E (SStruct Open Se) (Smod (StyIntf B))
        (binop box ctx ce)

  | inffunctor_sandboxed : forall E A B Se ce mt,
      elaborate_sexp (Sand Stop A) Se B ce ->
      mt = mk_functor_modtyp A B ->
      elaborate_sexp E (SFunctor Sandboxed A Se) (Smod mt)
        (binop box unit (lam (elaborate_typ A) ce))

  | inffunctor_open : forall E A B Se ce mt,
      elaborate_sexp (Sand E A) Se B ce ->
      mt = mk_functor_modtyp A B ->
      elaborate_sexp E (SFunctor Open A Se) (Smod mt)
        (lam (elaborate_typ A) ce)

  (* module closure *)
  | infmclos : forall E E' A B Se1 Se2 e1 e2 mt,
      elaborate_sexp E Se1 E' e1 ->
      elaborate_sexp (Sand E' A) Se2 B e2 ->
      mt = mk_functor_modtyp A B ->
      elaborate_sexp E (SMClos Se1 A Se2) (Smod mt)
        (clos e1 (elaborate_typ A) e2)

  (* Link(e1, e2) where e1 : Smod (StyArrM A mt) *)
  | infmlink : forall E A mt sE1 sE2 cE1 cE2,
      elaborate_sexp E sE1 (Smod (StyArrM A mt)) cE1 ->
      elaborate_sexp E sE2 A cE2 ->
      elaborate_sexp E (SMLink sE1 sE2) (Smod mt) (binop app cE1 cE2).

#[export]
Hint Constructors styp smodtyp sexp sandbox
  Slookup Slin Srlookup elaborate_sexp : core.

(* ============================================================ *)
(* Source values                                                *)
(* ============================================================ *)

Inductive svalue : sexp -> Prop :=
  | svint  : forall n, svalue (Slit n)
  | svunit : svalue Sunit
  | svclos : forall sv A se, svalue sv -> svalue (SClos sv A se)
  | svmclos: forall sv A se, svalue sv -> svalue (SMClos sv A se)
  | svmrg  : forall sv1 sv2, svalue sv1 -> svalue sv2 -> svalue (SDmrg sv1 sv2)
  | svnmrg : forall sv1 sv2, svalue sv1 -> svalue sv2 -> svalue (SNmrg sv1 sv2)
  | svrcd  : forall l sv, svalue sv -> svalue (Srec l sv).

#[export]
Hint Constructors svalue : core.

(* ============================================================ *)
(* Source value lookup                                          *)
(* ============================================================ *)

Inductive slookupv : sexp -> nat -> sexp -> Prop :=
  | slvzero_d : forall v1 v2,
      slookupv (SDmrg v1 v2) 0 v2
  | slvsucc_d : forall v1 v2 n v3,
      slookupv v1 n v3 ->
      slookupv (SDmrg v1 v2) (S n) v3
  | slvzero_n : forall v1 v2,
      slookupv (SNmrg v1 v2) 0 v2
  | slvsucc_n : forall v1 v2 n v3,
      slookupv v1 n v3 ->
      slookupv (SNmrg v1 v2) (S n) v3.

Inductive srlookupv : sexp -> string -> sexp -> Prop :=
  | srvlzero : forall l e, srlookupv (Srec l e) l e
  | svlandl_d : forall e1 e2 e l,
      srlookupv e1 l e -> srlookupv (SDmrg e1 e2) l e
  | svlandr_d : forall e1 e2 e l,
      srlookupv e2 l e -> srlookupv (SDmrg e1 e2) l e
  | svlandl_n : forall e1 e2 e l,
      srlookupv e1 l e -> srlookupv (SNmrg e1 e2) l e
  | svlandr_n : forall e1 e2 e l,
      srlookupv e2 l e -> srlookupv (SNmrg e1 e2) l e.

#[export]
Hint Constructors slookupv srlookupv : core.

(* ============================================================ *)
(* Source big-step semantics                                    *)
(* ============================================================ *)

Inductive sebig : sexp -> sexp -> sexp -> Prop :=
  | seblit : forall sv i,
      svalue sv ->
      sebig sv (Slit i) (Slit i)
  | sebunit : forall sv,
      svalue sv ->
      sebig sv Sunit Sunit
  | sebctx : forall sv,
      svalue sv ->
      sebig sv Sctx sv
  | sebclosv : forall sv sv1 A se,
      svalue sv -> svalue sv1 ->
      sebig sv (SClos sv1 A se) (SClos sv1 A se)
  | sebmclosv : forall sv sv1 A se,
      svalue sv -> svalue sv1 ->
      sebig sv (SMClos sv1 A se) (SMClos sv1 A se)
  | sebproj : forall sv se sv' n sv'',
      sebig sv se sv' ->
      slookupv sv' n sv'' ->
      sebig sv (Sproj se n) sv''
  | seblam : forall sv A se,
      svalue sv ->
      sebig sv (Slam A se) (SClos sv A se)
  | sebbox : forall sv se1 se2 sv1 sv_res,
      sebig sv se1 sv1 ->
      sebig sv1 se2 sv_res ->
      sebig sv (Sbox se1 se2) sv_res
  | sebapp : forall sv se1 se2 sv2 A se_body sv_clos sv_res,
      sebig sv se1 (SClos sv_clos A se_body) ->
      sebig sv se2 sv2 ->
      sebig (SDmrg sv_clos sv2) se_body sv_res ->
      sebig sv (Sapp se1 se2) sv_res
  | sebapp_mclos : forall sv se1 se2 sv2 A se_body sv_clos sv_res,
      sebig sv se1 (SMClos sv_clos A se_body) ->
      sebig sv se2 sv2 ->
      sebig (SDmrg sv_clos sv2) se_body sv_res ->
      sebig sv (Sapp se1 se2) sv_res
  | sebdmrg : forall sv se1 se2 sv1 sv2,
      sebig sv se1 sv1 ->
      sebig (SDmrg sv sv1) se2 sv2 ->
      sebig sv (SDmrg se1 se2) (SDmrg sv1 sv2)
  | sebnmrg : forall sv se1 se2 sv1 sv2,
      sebig sv se1 sv1 ->
      sebig sv se2 sv2 ->
      sebig sv (SNmrg se1 se2) (SNmrg sv1 sv2)
  | sebrec : forall sv se sv' l,
      sebig sv se sv' ->
      sebig sv (Srec l se) (Srec l sv')
  | sebrproj : forall sv se sv' l sv'',
      sebig sv se sv' ->
      srlookupv sv' l sv'' ->
      sebig sv (Srproj se l) sv''
  | seblet : forall sv se1 A se2 sv1 sv_res,
      sebig sv se1 sv1 ->
      sebig (SDmrg sv sv1) se2 sv_res ->
      sebig sv (Slet se1 A se2) sv_res
  | sebopen : forall sv se1 se2 sv1 l sv_field sv_res,
      sebig sv se1 sv1 ->
      srlookupv sv1 l sv_field ->
      sebig (SDmrg sv sv_field) se2 sv_res ->
      sebig sv (Sopen se1 se2) sv_res
  | sebstruct_sandboxed : forall sv se sv_res,
      svalue sv ->
      sebig Sunit se sv_res ->
      sebig sv (SStruct Sandboxed se) sv_res
  | sebstruct_open : forall sv se sv_res,
      sebig sv se sv_res ->
      sebig sv (SStruct Open se) sv_res
  | sebfunctor_sandboxed : forall sv A se,
      svalue sv ->
      sebig sv (SFunctor Sandboxed A se) (SMClos Sunit A se)
  | sebfunctor_open : forall sv A se,
      svalue sv ->
      sebig sv (SFunctor Open A se) (SMClos sv A se)
  | sebmlink : forall sv se1 se2 sv_clos sv2 A se_body sv_res,
      sebig sv se1 (SMClos sv_clos A se_body) ->
      sebig sv se2 sv2 ->
      sebig (SDmrg sv_clos sv2) se_body sv_res ->
      sebig sv (SMLink se1 se2) sv_res
  | sebmlink_clos : forall sv se1 se2 sv_clos sv2 A se_body sv_res,
      sebig sv se1 (SClos sv_clos A se_body) ->
      sebig sv se2 sv2 ->
      sebig (SDmrg sv_clos sv2) se_body sv_res ->
      sebig sv (SMLink se1 se2) sv_res.

#[export]
Hint Constructors sebig : core.

(* ============================================================ *)
(* Type elaboration safety lemmas                               *)
(* ============================================================ *)

Lemma type_safe_lookup : forall A n B,
  Slookup A n B ->
  lookup (elaborate_typ A) n (elaborate_typ B).
Proof.
  intros. induction H; simpl; eauto.
Qed.

Lemma type_safe_lin : forall l B,
  Slin l B -> lin l (elaborate_typ B).
Proof.
  intros. induction H; simpl; eauto.
Qed.

Lemma type_safe_lin_inv : forall l B,
  lin l (elaborate_typ B) -> Slin l B.
Proof.
  intros l B. revert l.
  induction B; simpl; intros; try solve [inversion H].
  - inversion H; subst; eauto using Slin_andl, Slin_andr.
  - inversion H; subst. constructor.
Admitted.

Lemma neg_type_safe_lin : forall l B,
  ~ Slin l B -> ~ lin l (elaborate_typ B).
Proof.
  intros. intro. apply H. apply type_safe_lin_inv. assumption.
Qed.

Lemma type_safe_rlookup : forall A l B,
  Srlookup A l B ->
  rlookup (elaborate_typ A) l (elaborate_typ B).
Proof.
  intros. induction H; simpl.
  - constructor.
  - apply landl; auto. apply neg_type_safe_lin; auto.
  - apply landr; auto. apply neg_type_safe_lin; auto.
Qed.

(* ============================================================ *)
(* Type preservation                                            *)
(* ============================================================ *)

Theorem type_preservation : forall E SE A CE,
  elaborate_sexp E SE A CE ->
  has_type (elaborate_typ E) CE (elaborate_typ A).
Proof. Admitted.

(* ============================================================ *)
(* Uniqueness of type inference                                 *)
(* ============================================================ *)

Lemma uniqueness_of_Slookup : forall E n A1 A2,
  Slookup E n A1 -> Slookup E n A2 -> A1 = A2.
Proof.
  intros E n A1 A2 H1 H2. generalize dependent A2.
  induction H1; intros; inversion H2; subst; eauto.
Qed.

Lemma uniqueness_of_Srlookup : forall E l A1 A2,
  Srlookup E l A1 -> Srlookup E l A2 -> A1 = A2.
Proof. Admitted.

Theorem uniqueness_of_inference : forall E SE A1 A2 CE1 CE2,
  elaborate_sexp E SE A1 CE1 ->
  elaborate_sexp E SE A2 CE2 ->
  A1 = A2.
Proof. Admitted.

Theorem uniqueness_of_elaboration : forall E SE A1 A2 CE1 CE2,
  elaborate_sexp E SE A1 CE1 ->
  elaborate_sexp E SE A2 CE2 ->
  CE1 = CE2.
Proof. Admitted.

(* ============================================================ *)
(* Basic properties of source semantics                         *)
(* ============================================================ *)

Lemma sebig_env_value : forall senv se sv,
  sebig senv se sv -> svalue senv.
Proof. Admitted.

Lemma sebig_res_value : forall senv se sv,
  sebig senv se sv -> svalue sv.
Proof. Admitted.

Lemma svalue_sebig_refl : forall sv,
  svalue sv -> forall senv,
  svalue senv ->
  sebig senv sv sv.
Proof. Admitted.

(* ============================================================ *)
(* Value correspondence                                         *)
(* ============================================================ *)

Inductive val_corresp : sexp -> exp -> Prop :=
  | vc_int : forall i,
      val_corresp (Slit i) (lit i)
  | vc_unit :
      val_corresp Sunit unit
  | vc_rcd : forall l sv cv,
      val_corresp sv cv ->
      val_corresp (Srec l sv) (rec l cv)
  | vc_mrg : forall sv1 sv2 cv1 cv2,
      val_corresp sv1 cv1 ->
      val_corresp sv2 cv2 ->
      val_corresp (SDmrg sv1 sv2) (binop mrg cv1 cv2)
  | vc_arr : forall A sv_env se cv_env ce,
      val_corresp
        (SClos sv_env A se)
        (clos cv_env (elaborate_typ A) ce)
  | vc_mod_arr : forall A sv_env se cv_env ce,
      val_corresp
        (SMClos sv_env A se)
        (clos cv_env (elaborate_typ A) ce).

#[export]
Hint Constructors val_corresp : core.

(*  ──────────────────────────────────────────────────────────
    Theorem (Semantic Preservation).

    If    E ⊢ se ⟹ A ⇝ ce
    then  ∀ senv sv cenv,
            svalue(senv)
          → senv ⊢ se ⇓ sv
          → senv ≈ cenv
          → ∃ cv,  cenv ⊢ ce ⇓ cv  ∧  sv ≈ cv 
    ────────────────────────────────────────────────────────── *)
Theorem semantic_preservation : forall E se A ce,
  elaborate_sexp E se A ce ->
  forall senv sv,
  svalue senv ->
  sebig senv se sv ->
  forall cenv,
  val_corresp senv cenv ->
  exists cv,
    ebig cenv ce cv /\
    val_corresp sv cv.
Proof. Admitted.

(*  ──────────────────────────────────────────────────────────
    Theorem (Separate Compilation / Correct Linking).

    If    E ⊢ se₁ ⟹ Smod(A → mt) ⇝ ce₁
    and   E ⊢ se₂ ⟹ A ⇝ ce₂
    then  ∀ senv cenv,
            svalue(senv)
          → senv ≈ cenv
          → senv ⊢ SMLink se₁ se₂ ⇓ sv
          → ∃ cv,  cenv ⊢ (ce₁ · ce₂) ⇓ cv  ∧  sv ≈ cv
    ────────────────────────────────────────────────────────── *)
Theorem separate_compilation : forall E se1 se2 A mt ce1 ce2,
  elaborate_sexp E se1 (Smod (StyArrM A mt)) ce1 ->
  elaborate_sexp E se2 A ce2 ->
  forall senv sv,
  svalue senv ->
  sebig senv (SMLink se1 se2) sv ->
  forall cenv,
  val_corresp senv cenv ->
  exists cv,
    ebig cenv (binop app ce1 ce2) cv /\
    val_corresp sv cv.


(* ============================================================ *)
(* Sandbox isolation                                            *)
(* ============================================================ *)

(* Sandboxed struct produces same result under any environment *)
Theorem sandbox_struct_isolation : forall se sv1 sv2 env1 env2,
  svalue env1 -> svalue env2 ->
  sebig env1 (SStruct Sandboxed se) sv1 ->
  sebig env2 (SStruct Sandboxed se) sv2 ->
  sv1 = sv2.
Proof. Admitted.

(* ============================================================ *)
(* Secure linking                                               *)
(* ============================================================ *)

(* Sandboxed functor result is independent of linking environment *)
Theorem secure_linking : forall A arg1 arg2 env1 env2 sv1 sv2,
  svalue env1 -> svalue env2 ->
  svalue arg1 -> svalue arg2 ->
  sebig env1 (SMLink (SFunctor Sandboxed A (Slit 42)) arg1) sv1 ->
  sebig env2 (SMLink (SFunctor Sandboxed A (Slit 42)) arg2) sv2 ->
  sv1 = sv2.
Proof. Admitted.

(* ============================================================ *)
(* Link elaboration commutes with evaluation                    *)
(* ============================================================ *)

Theorem link_elab_commutes : forall E se1 se2 A mt ce1 ce2,
  elaborate_sexp E se1 (Smod (StyArrM A mt)) ce1 ->
  elaborate_sexp E se2 A ce2 ->
  forall cenv v1 v2,
  value cenv ->
  has_type top cenv (elaborate_typ E) ->
  ebig cenv (binop app ce1 ce2) v1 ->
  elaborate_sexp E (SMLink se1 se2) (Smod mt) (binop app ce1 ce2) ->
  ebig cenv (binop app ce1 ce2) v2 ->
  v1 = v2.
Proof. Admitted.

(* ============================================================ *)
(* NMrg independence                                            *)
(* ============================================================ *)

Theorem nmrg_independence : forall E se1 se2 A1 A2 ce_nmrg ce2 B,
  elaborate_sexp E (SNmrg se1 se2) (Sand A1 A2) ce_nmrg ->
  elaborate_sexp E se2 B ce2 ->
  A2 = B.
Proof. Admitted.

(* ============================================================ *)
(* DMrg allows dependency                                       *)
(* ============================================================ *)

Lemma dmrg_allows_dependency :
  elaborate_sexp Stop (SDmrg (Slit 1) (Sproj Sctx 0)) (Sand Sint Sint)
    (binop mrg (lit 1) (proj ctx 0)).
Proof. Admitted.

(* ============================================================ *)
(* Elaboration shapes                                           *)
(* ============================================================ *)

Theorem struct_shape_sandboxed : forall E se B ce,
  elaborate_sexp E (SStruct Sandboxed se) (Smod (StyIntf B)) ce ->
  exists ce_body, ce = binop box unit ce_body.
Proof. Admitted.

Theorem struct_shape_open : forall E se B ce,
  elaborate_sexp E (SStruct Open se) (Smod (StyIntf B)) ce ->
  exists ce_body, ce = binop box ctx ce_body.
Proof. Admitted.

Theorem functor_shape_sandboxed : forall E A se mt ce,
  elaborate_sexp E (SFunctor Sandboxed A se) (Smod mt) ce ->
  exists ce_body, ce = binop box unit (lam (elaborate_typ A) ce_body).
Proof. Admitted.

Theorem functor_shape_open : forall E A se mt ce,
  elaborate_sexp E (SFunctor Open A se) (Smod mt) ce ->
  exists ce_body, ce = lam (elaborate_typ A) ce_body.
Proof. Admitted.

(* ============================================================ *)
(* Sandbox elaboration context independence                     *)
(* ============================================================ *)

Theorem sandbox_elab_context_indep : forall E1 E2 se B ce1 ce2,
  elaborate_sexp E1 (SStruct Sandboxed se) (Smod (StyIntf B)) ce1 ->
  elaborate_sexp E2 (SStruct Sandboxed se) (Smod (StyIntf B)) ce2 ->
  ce1 = ce2.
Proof. Admitted.

(* ============================================================ *)
(* Values are normal forms                                      *)
(* ============================================================ *)

Theorem values_source_normal_form : forall sv env,
  svalue sv -> svalue env ->
  sebig env sv sv.
Proof. Admitted.

(* ============================================================ *)
(* Closed module authority                                      *)
(* ============================================================ *)

Theorem closed_module_authority : forall se A ce,
  elaborate_sexp Stop se A ce ->
  has_type top ce (elaborate_typ A).
Proof. Admitted.

(* ============================================================ *)
(* Compositionality of elaboration                              *)
(* ============================================================ *)

Theorem elaboration_compositional_mlink : forall E se1 se2 A mt ce1 ce2,
  elaborate_sexp E se1 (Smod (StyArrM A mt)) ce1 ->
  elaborate_sexp E se2 A ce2 ->
  elaborate_sexp E (SMLink se1 se2) (Smod mt) (binop app ce1 ce2).
Proof.
  intros. econstructor; eauto.
Qed.

(* ============================================================ *)
(* Full pipeline                                                *)
(* ============================================================ *)

Theorem full_pipeline : forall se A ce,
  elaborate_sexp Stop se A ce ->
  has_type top ce (elaborate_typ A) ->
  exists cv, value cv /\ mstep unit ce cv.
Proof.
  intros. eapply termination; eauto.
Qed.

Theorem full_pipeline_with_correspondence : forall se A ce,
  elaborate_sexp Stop se A ce ->
  forall sv,
  sebig Sunit se sv ->
  exists cv,
    ebig unit ce cv /\
    val_corresp sv cv.
Proof. Admitted.

(* ============================================================ *)
(* Interface sufficiency                                        *)
(* ============================================================ *)

Theorem interface_sufficiency : forall E A mt,
  forall e_client1 e_client2,
  has_type E e_client1 (elaborate_modtyp (StyArrM A mt)) ->
  has_type E e_client2 (elaborate_modtyp (StyArrM A mt)) ->
  forall e_prov1 e_prov2,
  has_type E e_prov1 (elaborate_typ A) ->
  has_type E e_prov2 (elaborate_typ A) ->
  has_type E (binop app e_client1 e_prov1) (elaborate_modtyp mt) /\
  has_type E (binop app e_client2 e_prov2) (elaborate_modtyp mt).
Proof.
  intros. simpl in *. split; eapply tapp; eauto.
Qed.

(* ============================================================ *)
(* Linking associativity                                        *)
(* ============================================================ *)

Theorem linking_associative : forall E e1 e2 e3 A B C,
  has_type E e1 (elaborate_typ A) ->
  has_type E e2 (arr (elaborate_typ A) (elaborate_typ B)) ->
  has_type E e3 (arr (elaborate_typ B) (elaborate_typ C)) ->
  has_type E (binop app e3 (binop app e2 e1)) (elaborate_typ C).
Proof.
Admitted.
