Require Import LibTactics.
From Stdlib Require Import Arith Lia.
From Stdlib Require Import Strings.String.
Require Import Top.source.Syntax.
Require Import Top.source.Elaboration.
Require Import Top.source.Lemmas.
Set Implicit Arguments.

(* -------------------------//-------------------------- *)
(* Elaboration preserves typing.  Mutual induction over elab / elabd, each
   case closed by its compatibility lemma. *)

Theorem elab_elabd_preservation :
  (forall G M e A,  elab  G M e A  -> has_type G e A) /\
  (forall G D d Gd, elabd G D d Gd -> has_type G d Gd).
Proof.
  apply elab_elabd_mut; intros;
  eauto using comp_var, comp_fun, comp_tfun, comp_app, comp_tapp, comp_eq,
              comp_box, comp_merge,
              comp_dnil, comp_dval, comp_dtyp, comp_dmod.
Qed.

Theorem elab_preservation : forall G M e A,
  elab G M e A -> has_type G e A.
Proof. apply (proj1 elab_elabd_preservation). Qed.

Theorem elabd_preservation : forall G D d Gd,
  elabd G D d Gd -> has_type G d Gd.
Proof. apply (proj2 elab_elabd_preservation). Qed.

Print Assumptions elab_preservation.
Print Assumptions elabd_preservation.
