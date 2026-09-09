Require Import LibTactics. 
From Stdlib Require Import Arith.
From Stdlib Require Import Lia. 
Require Import Stdlib.Lists.List. 
Require Import Stdlib.Classes.EquivDec. 
From Stdlib Require Import Strings.String.
Import ListNotations.
Require Import ExpSyntax Semantics Conserve.
Set Implicit Arguments.

Inductive er_exp :=
  | er_lit : nat -> er_exp
  | er_var : nat -> er_exp
  | er_lam : er_exp -> er_exp
  | er_box : er_exp -> er_exp -> er_exp
  | er_app : er_exp -> er_exp -> er_exp 
  | er_blam: er_exp -> er_exp
  | er_clos: er_exp -> er_exp -> er_exp
  | er_bclos: er_exp -> er_exp -> er_exp
  | er_unit : er_exp
  | er_merge : er_exp -> er_exp -> er_exp
  | er_rec: string -> er_exp -> er_exp
  | er_rproj: er_exp -> string -> er_exp
  | er_dummyApp: er_exp -> er_exp.

Notation "e1 ,,, e2" := (er_merge e1 e2) (at level 80).

Inductive er_value : er_exp -> Prop :=
  | er_vlit: forall i, er_value (er_lit i)
  | er_vclos: forall E e, 
      er_value E ->
      er_value (er_clos E e)
  | er_vbclos: forall E e,
      er_value E ->
      er_value (er_bclos E e)
  | er_lvnil: er_value er_unit
  | er_lvconsv: forall E v,
      er_value E ->
      er_value v ->
      er_value (E ,,, v)
  | er_vrec: forall l v,
      er_value v ->
      er_value (er_rec l v).

#[export]
Hint Constructors er_exp er_value : core.

Fixpoint reconcat (e1 e2: er_exp) : er_exp :=
  match e2 with
    | e3 ,,, e4 =>
        match e3 with
          | _ ,,, _ => 
              (reconcat e1 e3) ,,, e4
          | _ => e1 ,,, e4
        end
    | _ => e1
  end.

Notation "e1 ++r e2" := (reconcat e1 e2) (at level 180).

Lemma recon_cons: forall E1 E2 E3,
  ((E1 ++r E2) ,,, E3) = (E1 ++r (E2 ,,, E3)).
Proof.
  intros. destruct* E2. 
Qed.

Fixpoint erase (e: exp) : er_exp :=
  match e with
    | lit i => er_lit i
    | var n => er_var n
    | lam e => er_lam (erase e)
    | box E e => er_box (erase E) (erase e)
    | app e1 e2 => er_app (erase e1) (erase e2)
    | blam e => er_blam (erase e)
    | clos E e => er_clos (erase E) (erase e)
    | bclos E e => er_bclos (erase E) (erase e)
    | tapp e A => er_dummyApp (erase e)
    | unit => er_unit
    | merge e1 e2 => er_merge (erase e1) (erase e2)
    | tmerge e A => erase e
    | rec l e => er_rec l (erase e)
    | rproj e l => er_rproj (erase e) l
  end.


Inductive er_lookupv : er_exp -> nat -> er_exp -> Prop :=
  | lvzero : forall v ve, 
      er_lookupv (ve ,,, v) 0 v
  | lvsuccv : forall v v' n ve, 
      er_lookupv ve n v' -> 
      er_lookupv (ve ,,, v) (S n) v'.
  

Inductive er_rlookupv : er_exp -> string -> er_exp -> Prop :=
  | er_rvlzero : forall l v d, 
      er_rlookupv (d ,,, (er_rec l v)) l v
  | er_rvl_left : forall d v1 v l l1, 
      er_rlookupv d l v ->
      ~ l = l1 ->
      er_rlookupv (d ,,, (er_rec l1 v1)) l v
  | er_rvl_right : forall d1 d v l, 
      er_rlookupv d1 l v ->
      er_rlookupv (d ,,, d1) l v.

Inductive ebig : er_exp -> er_exp -> er_exp -> Prop :=
  | eb_var : forall ve n v',
      er_value ve ->
      er_lookupv ve n v' ->
      ebig ve (er_var n) v'
  | eb_lit: forall ve n,
      er_value ve ->
      ebig ve (er_lit n) (er_lit n)
  | eb_lam: forall ve e,
      er_value ve ->
      ebig ve (er_lam e) (er_clos ve e)
  | eb_clos: forall ve ve' e,
      er_value ve ->
      er_value ve' ->
      ebig ve (er_clos ve' e) (er_clos ve' e)
  | eb_blam: forall ve e,
      er_value ve ->
      ebig ve (er_blam e) (er_bclos ve e)
  | eb_bclos: forall ve e ve',
      er_value ve ->
      er_value ve' ->
      ebig ve (er_bclos ve' e) (er_bclos ve' e)
  | eb_beta : forall ve ve1 v2 e e1 e2 v, 
      er_value ve1 -> 
      ebig ve e1 (er_clos ve1 e) ->
      ebig ve e2 v2 ->
      ebig (ve1 ,,, v2) e v ->
      ebig ve (er_app e1 e2) v
  | eb_tbeta: forall ve ve1 e e1 v, 
      er_value ve1 -> 
      ebig ve e1 (er_bclos ve1 e) ->
      ebig ve1 e v ->
      ebig ve (er_dummyApp e1) v
  | eb_box: forall ve e1 v1 e2 v2, 
      ebig ve e1 v1 ->
      ebig v1 e2 v2 ->
      ebig ve (er_box e1 e2) v2
  | eb_nil: forall ve,
      er_value ve ->
      ebig ve er_unit er_unit
  | eb_edef: forall ve e1 ve1 e2 v2,
      ebig ve e1 ve1 ->
      ebig (ve ++r ve1) e2 v2 ->
      ebig ve (e1 ,,, e2) (ve1 ,,, v2)
  | eb_rec: forall ve e l v,
      ebig ve e v ->
      ebig ve (er_rec l e) (er_rec l v)
  | eb_proj: forall ve e v2 l dv,
      ebig ve e dv ->
      er_rlookupv dv l v2 ->
      ebig ve (er_rproj e l) v2.

#[export]
Hint Constructors er_lookupv er_rlookupv ebig: core.


Lemma erase_value: forall v,
  value v ->
  er_value (erase v).
Proof.
  introv Hv. inductions Hv; simpl; eauto.
Qed.


Lemma erase_k: forall ve n v',
  lookupv ve n v' ->
  er_lookupv (erase ve) n (erase v').
Proof.
  introv Hl. inductions Hl; simpl; eauto.
Qed.

Lemma erase_rlk: forall ve l v',
  rlookupv ve l v' ->
  er_rlookupv (erase ve) l (erase v').
Proof.
  introv Hl. inductions Hl; simpl; eauto.
Qed.

Lemma erase_app: forall ve1 ve2,
  erase (ve2 ++- ve1) = (erase ve2 ++r erase ve1).
Proof.
  introv. inductions ve1; try solve [simpl; eauto].
  - rewrite <-econ_cons. simpl. rewrite IHve1_1.
    destruct* (erase ve1_1).
  - rewrite <-econ_cons_typ. simpl. rewrite IHve1. eauto.
Qed.


Lemma ebig_erase: forall ve e v,
  big ve e v ->
  ebig (erase ve) (erase e) (erase v).
Proof.
  introv He. inductions He; try solve [simpl; eauto].
  - simpl. econstructor.
    eapply erase_value; eauto. eapply erase_k; eauto.
  - simpl. econstructor. eapply erase_value; eauto.
  - simpl. econstructor. eapply erase_value; eauto.
  - econstructor; try solve [eapply erase_value; eauto].
  - simpl. econstructor. 
    eapply erase_value; eauto. 
  - simpl. econstructor. 
    eapply erase_value; eauto. eapply erase_value; eauto. 
  - simpl. 
    simpl in IHHe1. 
    simpl in IHHe3. 
    econstructor; try eapply IHHe1; eauto.
    eapply erase_value; eauto.
  - simpl. 
    simpl in IHHe1. 
    simpl in IHHe2. 
    econstructor; try eapply IHHe1; eauto.
    eapply erase_value; eauto. 
  - simpl. econstructor. eapply erase_value; eauto. 
  - simpl. 
    simpl in IHHe1. 
    econstructor; eauto.
    rewrite <- erase_app. eauto.
  - simpl. 
    econstructor; eauto. 
    eapply erase_rlk; eauto.
Qed.


Inductive estep : er_exp -> er_exp -> er_exp -> Prop :=
  | esvar : forall ve n v',
      er_value ve ->
      er_lookupv ve n v' ->
      estep ve (er_var n) v'
  | esappl : forall ve e1 e2 e1', 
      er_value ve ->  
      estep ve e1 e1' -> 
      estep ve (er_app e1 e2) (er_app e1' e2)
  | esappr : forall ve v1 e2 e2', 
      er_value ve -> 
      er_value v1 -> 
      estep ve e2 e2' -> 
      estep ve (er_app v1 e2) (er_app v1 e2')
  | esboxl : forall ve e1 e2 e1', 
      er_value ve -> 
      estep ve e1 e1' -> 
      estep ve (er_box e1 e2) (er_box e1' e2)
  | esbox : forall ve e1 e2 e2', 
      er_value ve -> 
      er_value e1 -> 
      estep e1 e2 e2' -> 
      estep ve (er_box e1 e2) (er_box e1 e2')
  | esboxv : forall ve v1 v2, 
      er_value ve -> 
      er_value v1 -> 
      er_value v2 -> 
      estep ve (er_box v1 v2) v2
  | esclos: forall ve e,
      er_value ve ->
      estep ve (er_lam e) (er_clos ve e)
  | esbclos: forall ve e,
      er_value ve ->
      estep ve (er_blam e) (er_bclos ve e)
  | esbeta : forall ve v1 v2 e, 
      er_value v1 -> 
      er_value ve -> 
      er_value v2 -> 
      estep ve (er_app (er_clos v1 e) v2) (er_box (v1 ,,, v2) e)
  | estappl : forall ve e1 e1', 
      estep ve e1 e1' -> 
      estep ve (er_dummyApp e1) (er_dummyApp e1')
  | estapp: forall ve v1 e, 
      er_value ve ->
      er_value v1 -> 
      estep ve (er_dummyApp (er_bclos v1 e)) (er_box v1 e)
  | els_mrgl: forall ve e1 d1 d1', 
      er_value ve -> 
      estep ve d1 d1' -> 
      estep ve (d1,,,e1) (d1',,,e1)
  | els_mrgr: forall ve e1 e2 d1, 
      er_value ve -> 
      er_value d1 ->
      estep (ve ++r d1) e1 e2 ->
      estep ve (d1,,,e1) (d1,,,e2)
  | es_rec: forall ve l e e',
      er_value ve ->
      estep ve e e' ->
      estep ve (er_rec l e) (er_rec l e')
  | es_proj: forall ve l e e',
      er_value ve ->
      estep ve e e' ->
      estep ve (er_rproj e l) (er_rproj e' l)
  | esrprojv : forall ve l dv v2, 
      er_value ve ->
      er_value dv ->
      er_rlookupv dv l v2 ->
      estep ve (er_rproj dv l) v2.

Inductive mestep : er_exp -> er_exp -> er_exp -> Prop :=
  | mestep_base : forall ve e, er_value ve -> mestep ve e e
  | mestep_step : forall ve e e' e'', estep ve e e' -> mestep ve e' e'' -> mestep ve e e''.

#[export]
Hint Constructors estep mestep: core.


Lemma er_lookupv_value: forall v n v', 
  er_lookupv v n v' -> 
  er_value v -> 
  er_value v'.
Proof.
  introv Hl. inductions Hl; introv Hv; inverts* Hv.
Qed.

Lemma er_rl_value: forall dv l v',
  er_rlookupv dv l v' ->
  er_value dv ->
  er_value v'.
Proof.
  introv Hr. inductions Hr; introv Hv; try solve [inverts* Hv].
  - inverts Hv. inverts* H2. 
Qed.

Lemma ebig_value: forall ve e1 e2,
  ebig ve e1 e2 ->
  er_value e2.
Proof.
  introv Hm. inductions Hm; simpl; eauto.
  eapply er_lookupv_value; eauto.
  - eapply er_rl_value; eauto. 
Qed.

Lemma mestep_value: forall ve e1 e2,
  mestep ve e1 e2 ->
  er_value ve.
Proof.
  introv Hs. inductions Hs; eauto.
Qed.

Lemma estep_value: forall ve e1 e2,
  estep ve e1 e2 ->
  er_value ve.
Proof.
  introv Hs. inductions Hs; eauto.
Qed.

Lemma estep_is_mestep: forall ve e1 e2,
  estep ve e1 e2 ->
  mestep ve e1 e2.
Proof.
  introv Hm. forwards~: estep_value Hm. eauto.
Qed.


Lemma mestep_trans: forall ve e1 e2,
  mestep ve e1 e2 -> forall e3,
  mestep ve e2 e3 ->
  mestep ve e1 e3.
Proof.
  introv Hm1. inductions Hm1; introv Hm2; eauto.
Qed.

Lemma mestep_add: forall ve e1 e2,
  mestep ve e1 e2 -> forall ve1,
  er_value ve1 ->
  mestep ve1 (er_box ve e1) (er_box ve e2).
Proof.
  introv Hm. inductions Hm; introv Hl; eauto.
  - forwards~: IHHm Hl. forwards~: estep_value H.
    eapply mestep_trans; try eapply H0.
    eapply estep_is_mestep; eauto.
Qed.

Lemma mestep_add_tov: forall ve e1 v,
  mestep ve e1 v ->
  er_value v -> forall ve1,
  er_value ve1 ->
  mestep ve1 (er_box ve e1) v.
Proof.
  introv Hm Hv Hl. 
  forwards~: mestep_add Hm ve1.
  eapply mestep_trans; eauto.
  forwards~: mestep_value Hm.
  eapply estep_is_mestep; eauto.
Qed.


Lemma mestep_appl: forall ve e1 e2,
  mestep ve e1 e2 -> forall e3,
  mestep ve (er_app e1 e3) (er_app e2 e3).
Proof.
  introv Hm. inductions Hm; intros.
  - eauto.
  - forwards~: estep_value H. eauto.
Qed.


Lemma mestep_appr: forall ve e1 e2,
  mestep ve e1 e2 -> forall v,
  er_value v ->
  mestep ve (er_app v e1) (er_app v e2).
Proof.
  introv Hm. inductions Hm; intros.
  - eauto.
  - forwards~: estep_value H. eauto.
Qed.

Lemma mestep_dummyl: forall ve e1 e2,
  mestep ve e1 e2 -> 
  mestep ve (er_dummyApp e1) (er_dummyApp e2).
Proof.
  introv Hm. inductions Hm; intros; eauto.
Qed.

Lemma mestep_boxl: forall ve e1 e2,
  mestep ve e1 e2 -> forall e3,
  mestep ve (er_box e1 e3) (er_box e2 e3).
Proof.
  introv Hm. inductions Hm; intros; eauto.
  forwards~: estep_value H. eauto. 
Qed.

Lemma mestep_boxr: forall ve1 e1 e2,
  mestep ve1 e1 e2 -> forall ve,
  er_value ve ->
  mestep ve (er_box ve1 e1) (er_box ve1 e2).
Proof.
  introv Hm. inductions Hm; intros; eauto.
  forwards~: estep_value H. eauto.
Qed.


Lemma mestep_mrgl: forall ve d1 d2,
  mestep ve d1 d2 -> forall e,
  mestep ve (d1,,,e) (d2,,,e).
Proof.
  introv Hm. inductions Hm; intros; eauto.
  forwards~: estep_value H. inverts* H.
Qed.

Lemma ebig_env_lvalue: forall ve e v,
  ebig ve e v ->
  er_value ve.
Proof.
  introv He. inductions He; eauto.
Qed.

Lemma er_lv_old: forall ve1 ve,
  er_value (ve ++r ve1) ->
  er_value ve.
Proof.
  intros ve1. inductions ve1; intros; simpl; eauto.
  - rewrite <- recon_cons in H. inverts* H.
Qed.

Lemma mestep_mrgr: forall ve1 ve e1 e2,
  mestep (ve ++r ve1) e1 e2 -> 
  er_value ve1 ->
  mestep ve (ve1 ,,, e1) (ve1 ,,, e2).
Proof.
  introv Hm. inductions Hm; intros; eauto.
  - forwards~: er_lv_old H.
  - forwards~: estep_value H. forwards~: er_lv_old H1. 
    forwards~: IHHm ve1 ve. 
    eapply mestep_trans; try eapply H3.
    eapply estep_is_mestep. econstructor; eauto.
Qed.

Lemma mestep_rec: forall ve e1 e2,
  mestep ve e1 e2 -> forall l,
  mestep ve (er_rec l e1) (er_rec l e2).
Proof.
  introv Hm. inductions Hm; intros; eauto.
  forwards~: estep_value H. eauto.
Qed.

Lemma mestep_proj: forall ve e1 e2,
  mestep ve e1 e2 -> forall l,
  mestep ve (er_rproj e1 l) (er_rproj e2 l).
Proof.
  introv Hm. inductions Hm; intros; eauto.
  forwards~: estep_value H. eauto.
Qed.



Lemma ebig_sound: forall ve e1 e2,
  ebig ve e1 e2 ->
  mestep ve e1 e2.
Proof.
  introv Hb. inductions Hb; eauto.
  - forwards~ Hv: ebig_value Hb3. forwards~ Hl: mestep_value IHHb1.
    forwards~ Hs: mestep_add_tov IHHb3 Hv Hl.
    eapply mestep_trans; try eapply Hs. 
    forwards~: mestep_appl IHHb1 e2.
    forwards~: mestep_appr IHHb2 (er_clos ve1 e). 
    forwards~: mestep_trans H0 H1.
    eapply mestep_trans; eauto.
    eapply estep_is_mestep; eauto.
    econstructor; eauto. 
    eapply ebig_value; eauto.
  - forwards~ Hv: ebig_value Hb2. forwards~ Hl: mestep_value IHHb1.
    forwards~ Hs: mestep_add_tov IHHb2 Hv Hl.
    eapply mestep_trans; try eapply Hs.
    forwards~: mestep_dummyl IHHb1.
    eapply mestep_trans; eauto.
  - forwards~ Hve: ebig_env_lvalue Hb1.
    forwards~ Hv1: ebig_env_lvalue Hb2.
    forwards~: mestep_boxl IHHb1 e2.
    forwards~: mestep_boxr IHHb2 ve. 
    forwards~: mestep_trans H H0.
    eapply mestep_trans; try eapply H2; eauto.
    eapply estep_is_mestep; eauto.
    econstructor; eauto.
    forwards~: ebig_value Hb1. 
    eapply ebig_value; eauto.
  - forwards~: mestep_mrgl IHHb1 e2.
    forwards~: mestep_mrgr IHHb2.
    eapply ebig_value; eauto.
    forwards~: mestep_trans H H0.
  - forwards~: mestep_rec IHHb l.
  - forwards~: mestep_proj IHHb l.
    eapply mestep_trans; eauto.
    eapply estep_is_mestep; eauto.
    econstructor; eauto. eapply mestep_value; eauto.
    forwards~: ebig_value Hb. 
Qed.

Lemma sem_erase: forall ve e v,
  mstep ve e v ->
  value v ->
  mestep (erase ve) (erase e) (erase v).
Proof.
  introv Hm Hv. eapply ebig_sound. eapply ebig_erase. eapply big_complete; eauto.
Qed.

