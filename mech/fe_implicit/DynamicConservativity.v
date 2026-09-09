Require Import LibTactics. From Stdlib Require Import Arith Lia.
Require Import Stdlib.Lists.List.
Import ListNotations.
Require Import LogRel.
Require Import Conserve.

Set Implicit Arguments.

(* ---- numeric equality helpers ---- *)

Lemma eq_dec : forall x y : nat, {x = y} + {x <> y}.
Proof. intros x y. decide equality. Qed.

Lemma beq_dec : forall (i:nat) (n:nat),
  beq_nat i n = true \/ beq_nat i n = false.
Proof.
  intros i n. destruct (beq_nat i n); [left | right]; reflexivity.
Qed.

Lemma beq_true_eq: forall i1 i2,
  (beq_nat i1 i2) = true -> i1 = i2.
Proof.
  intro x. induction x.
  - intros y H. destruct y. reflexivity. simpl in *. congruence.
  - intros y H. destruct y. simpl in *. congruence. f_equal ; auto.
Qed.

Lemma beq_refl: forall n, beq_nat n n = true.
Proof. intros n. inductions n; eauto. Qed.

Lemma eq_beq_true: forall i1 i2,
  i1 = i2 -> (beq_nat i1 i2) = true.
Proof. introv Heq. subst*. eapply beq_refl. Qed.

Lemma beq_false_eq: forall i1 i2,
  (beq_nat i1 i2) = false -> i1 <> i2.
Proof.
  introv Hf. forwards~ [?|?]: eq_dec i1 i2.
  forwards~: eq_beq_true e. rewrite H in Hf. inverts* Hf.
Qed.

(* ==================================================================== *)
(*  System-F dynamics on [term]                                  *)
(* ==================================================================== *)

Inductive fvalue : term -> Prop :=
  | fv_lit: forall i, fvalue (flit i)
  | fv_abs: forall t, fvalue (fabs t).

(* term substitution (no type-level constructors) *)
Fixpoint subst (t : term) (x : nat) (t' : term) {struct t} : term :=
  match t with
  | fvar y      => if beq_nat x y then t' else fvar y
  | flit n      => flit n
  | fabs t2     => fabs (subst t2 (1 + x) t')
  | fapp t1 t2  => fapp (subst t1 x t') (subst t2 x t')
  end.

Inductive red : term -> term -> Prop :=
  | rappl: forall (t1 t2 t3 : term),
      red t1 t2 ->
      red (fapp t1 t3) (fapp t2 t3)
  | rappr: forall (t1 t2 w : term),
      red t1 t2 ->
      fvalue w ->
      red (fapp w t1) (fapp w t2)
  | rbeta : forall (t1 w : term),
      fvalue w ->
      red (fapp (fabs t1) w) (subst t1 0 w).

Inductive mred : term -> term -> Prop :=
  | mred_base : forall t, mred t t
  | mred_step : forall t t' t'', red t t' -> mred t' t'' -> mred t t''.

Inductive fbig: term -> term -> Prop :=
  | fb_lit: forall n, fbig (flit n) (flit n)
  | fb_abs: forall t1, fbig (fabs t1) (fabs t1)
  | fb_app: forall t1 t2 t3 w w1,
      fbig t1 (fabs t3) ->
      fbig t2 w ->
      fbig (subst t3 0 w) w1 ->
      fbig (fapp t1 t2) w1.

#[export]
Hint Constructors fvalue red mred fbig: core.

Lemma red_is_mred: forall t1 t2,
  red t1 t2 -> mred t1 t2.
Proof. introv Hm. eauto. Qed.

Lemma mred_trans: forall t1 t2,
  mred t1 t2 -> forall t3, mred t2 t3 -> mred t1 t3.
Proof. introv Hm1. inductions Hm1; introv Hm2; eauto. Qed.

Lemma mred_appl: forall t1 t2,
  mred t1 t2 -> forall t3, mred (fapp t1 t3) (fapp t2 t3).
Proof. introv Hm. inductions Hm; intros; eauto. Qed.

Lemma mred_appr: forall t1 t2,
  mred t1 t2 -> forall w, fvalue w -> mred (fapp w t1) (fapp w t2).
Proof. introv Hm. inductions Hm; intros; eauto. Qed.

Lemma fbig_fvalue: forall t1 t2,
  fbig t1 t2 -> fvalue t2.
Proof. introv Hm. inductions Hm; simpl; eauto. Qed.

Lemma fbig_sound: forall t1 t2,
  fbig t1 t2 -> mred t1 t2.
Proof.
  introv Hb. inductions Hb; eauto.
  - eapply mred_trans; try eapply IHHb3.
    forwards~: mred_appl IHHb1 t2.
    forwards~: mred_appr IHHb2 (fabs t3).
    forwards~: mred_trans H H0.
    eapply mred_trans; eauto.
    eapply red_is_mred; eauto.
    econstructor. eapply fbig_fvalue; eauto.
Qed.

Lemma fbig_refl: forall w,
  fvalue w -> fbig w w.
Proof. introv Hv. destruct* w; inverts Hv. Qed.

Lemma f_absorb: forall t1 t2,
  red t1 t2 -> forall t3, fbig t2 t3 -> fbig t1 t3.
Proof.
  introv Hr. inductions Hr; introv Hb;
  try solve [eauto];
  try solve [inverts* Hb].
  - econstructor; eauto. eapply fbig_refl; eauto.
Qed.

Lemma fbig_complete: forall t w,
  mred t w -> fvalue w -> fbig t w.
Proof.
  introv Hm. inductions Hm; introv Hv.
  - destruct* t; try solve [inverts* Hv].
  - forwards~: IHHm Hv. eapply f_absorb; eauto.
Qed.

(* ==================================================================== *)
(*  FE big-step on [exp] (no type-level constructs)               *)
(* ==================================================================== *)

Inductive big : exp -> exp -> exp -> Prop :=
  | b_var : forall ve n v',
      value ve ->
      lookupv ve n v' ->
      big ve (var n) v'
  | b_lit: forall ve n,
      value ve ->
      big ve (lit n) (lit n)
  | b_lam: forall ve e,
      value ve ->
      big ve (lam e) (clos ve e)
  | b_clos: forall ve ve' e,
      value ve ->
      value ve' ->
      big ve (clos ve' e) (clos ve' e)
  | b_beta : forall ve ve1 v2 e e1 e2 v,
      value ve1 ->
      big ve e1 (clos ve1 e) ->
      big ve e2 v2 ->
      big (ve1 ,, v2) e v ->
      big ve (app e1 e2) v
  | b_box: forall ve e1 v1 e2 v2,
      big ve e1 v1 ->
      big v1 e2 v2 ->
      big ve (box e1 e2) v2
  | b_nil: forall ve,
      value ve ->
      big ve unit unit
  | b_edef: forall ve e1 ve1 e2 v2,
      big ve e1 ve1 ->
      big (ve ++- ve1) e2 v2 ->
      big ve (e1 ,, e2) (ve1 ,, v2)
  | b_rec: forall ve e l v,
      big ve e v ->
      big ve (rec l e) (rec l v)
  | b_proj: forall ve e v2 l dv,
      big ve e dv ->
      rlookupv dv l v2 ->
      big ve (rproj e l) v2.

#[export]
Hint Constructors big: core.

Lemma big_refl: forall v,
  value v -> forall ve, value ve -> big ve v v.
Proof.
  introv Hv. inductions Hv; introv Hl; eauto.
  econstructor; eauto.
  eapply IHHv2. eapply value_app; eauto.
Qed.

Lemma big_value_eq: forall ve v e,
  big ve v e -> value v -> e = v.
Proof.
  introv Hb. inductions Hb; introv Hv;
  try solve [inverts* Hv].
  - inverts Hv. forwards~: IHHb1 H1. forwards~: IHHb2 H2. subst. eauto.
  - inverts Hv. forwards~: IHHb. subst. eauto.
Qed.

Lemma absorb: forall ve e1 e2,
  step ve e1 e2 -> forall e3, big ve e2 e3 -> big ve e1 e3.
Proof.
  introv Hr. inductions Hr; introv Hb;
  try solve [inverts* Hb].
  - (* svar *)
    forwards~: lookupv_value H0. forwards~: big_value_eq Hb. subst. eauto.
  - (* sbox: inner step changes the env to e1 *)
    inverts Hb. forwards~: big_value_eq H4. subst. econstructor; eauto.
  - (* sboxv: box of two values projects to the second *)
    forwards~: big_value_eq Hb. subst. econstructor; eapply big_refl; eauto.
  - (* sbeta: app of a closure builds a box *)
    inverts Hb. forwards~: big_value_eq H5. subst.
    eapply b_beta; try eapply big_refl; eauto.
  - (* ls_mrgr: right-merge steps under the extended env *)
    inverts Hb. forwards~: big_value_eq H4. subst. econstructor; eauto.
  - (* srprojv *)
    forwards~: big_value_eq Hb. eapply rl_value; eauto. subst. econstructor; eauto.
    eapply big_refl; eauto.
Qed.

Lemma big_complete: forall ve e v,
  mstep ve e v -> value v -> big ve e v.
Proof.
  introv Hm. inductions Hm; introv Hv.
  - eapply big_refl; eauto.
  - forwards~: IHHm Hv. eapply absorb; eauto.
Qed.

(* ==================================================================== *)
(*  The result relation [resrel] and the reconstruction [check]          *)
(* ==================================================================== *)

(* [check e E n t]: the FE source-shaped exp [e], evaluated under value   *)
(* env [E] with [n] locally-bound (lambda) variables, reconstructs the    *)
(* System-F term [t].  Variables >= n index into the env [E].             *)
Inductive check: exp -> exp -> nat -> term -> Prop :=
  | chvarl: forall E i n,
      value E ->
      n > i ->
      check (var i) E n (fvar i)
  | chvarlam: forall E i n e e1 E' s,
      value E ->
      i >= n ->
      lookupv E (minus i n) (clos E' e) ->
      e1 = e ->
      check e1 E' 1 s ->
      check (var i) E n (fabs s)
  | chvarlit: forall E i n j,
      value E ->
      i >= n ->
      lookupv E (minus i n) (lit j) ->
      check (var i) E n (flit j)
  | chlit: forall E i n,
      value E ->
      check (lit i) E n (flit i)
  | chlam: forall e E n e',
      check e E (S n) e' ->
      check (lam e) E n (fabs e')
  | chapp: forall e1 e2 E n e3 e4,
      check e1 E n e3 ->
      check e2 E n e4 ->
      check (app e1 e2) E n (fapp e3 e4).

Inductive resrel: term -> exp -> Prop :=
  | rrlit: forall i,
      resrel (flit i) (lit i)
  | rrlam: forall t e E,
      check e E 1 t ->
      resrel (fabs t) (clos E e).

#[export]
Hint Constructors check resrel: core.

(* ==================================================================== *)
(*  Boundedness / closedness on terms                                    *)
(* ==================================================================== *)

Inductive bound : term -> nat -> Prop :=
  | bvar k n :
      k > n ->
      bound (fvar n) k
  | blit i k :
      bound (flit i) k
  | bapp k e1 e2 :
      bound e1 k ->
      bound e2 k ->
      bound (fapp e1 e2) k
  | bslam k e:
      bound e (S k) ->
      bound (fabs e) k.

#[export]
Hint Constructors bound: core.

Definition closed s:= bound s 0.

Lemma bound_larger: forall e k,
  bound e k -> forall n, k <= n -> bound e n.
Proof.
  introv Hb. inductions Hb; introv Hl;
  try solve [eauto].
  - econstructor. lia.
  - econstructor. eapply IHHb. lia.
Qed.

Lemma bound_check: forall t n,
  bound t n -> forall E, value E -> forall e,
  trans_e t e -> check e E n t.
Proof.
  introv Hb. inductions Hb; introv Hl Ht;
  try solve [inverts* Ht].
Qed.

Lemma check_bound: forall e1 E e n,
  check e1 E n e -> bound e n.
Proof.
  introv Hc. inductions Hc;
  try solve [eauto].
  - eapply bound_larger; eauto. lia.
Qed.

Lemma bound_subst: forall e k,
  bound e k -> forall n e1, k <= n -> subst e n e1 = e.
Proof.
  introv Hb. inductions Hb; introv Hl;
  try solve [simpl; eauto].
  - simpl.
    destruct* (beq_dec n0 n).
    + forwards~: beq_true_eq H0. lia.
    + rewrite H0. eauto.
  - simpl.
    forwards~: IHHb1 n e0.
    forwards~: IHHb2 n e0.
    rewrite H. rewrite H0. eauto.
  - simpl.
    forwards~: IHHb (S n) e1. lia.
    rewrite H. eauto.
Qed.

Lemma check_lvalue: forall e E n t,
  check e E n t -> value E.
Proof. introv Hc. inductions Hc; eauto. Qed.

Lemma resrel_value: forall w v,
  resrel w v -> value v.
Proof.
  introv Hr. inverts* Hr.
  - econstructor. eapply check_lvalue; eauto.
Qed.

Lemma lookupv_minus: forall i E r,
  lookupv E i r -> forall v2, lookupv (E,,v2) (S i) r.
Proof.
  introv Hs. inductions Hs; intros.
  - simpl. eauto.
  - simpl. eauto.
Qed.

(* substitution lemma: extend the env with a value, lower the level *)
Lemma check_sn: forall e1 E n e2,
  check e1 E (S n) e2 -> forall w v2,
  resrel w v2 ->
  check e1 (E,,v2) n (subst e2 n w).
Proof.
  introv Hc. inductions Hc; introv Hw;
  try solve [forwards~: resrel_value Hw; simpl; eauto].
  - simpl. inverts Hw.
    + destruct* (beq_dec n i).
      * rewrite H1. forwards~: beq_true_eq H1.
        subst. eapply chvarlit; eauto.
        assert (i - i = 0). lia. rewrite H2. eauto.
      * rewrite H1. econstructor; eauto.
        forwards~: beq_false_eq H1. lia.
    + forwards~ Hv0: check_lvalue H1. destruct* (beq_dec n i) as [Hb|Hb].
      * rewrite Hb. forwards~: beq_true_eq Hb.
        subst. eapply chvarlam; eauto.
        assert (i - i = 0) as He. lia. rewrite He. eauto.
      * rewrite Hb. econstructor; eauto.
        forwards~: beq_false_eq Hb. lia.
  - simpl.
    forwards~: resrel_value Hw.
    forwards~: lookupv_minus H1 v2.
    assert (S (i - S n) = i - n) as He. lia. rewrite He in H3.
    forwards~: check_bound Hc.
    forwards~: bound_subst H4 (S n) w. lia.
    rewrite H5. eapply chvarlam; eauto. lia.
  - simpl. forwards~: resrel_value Hw.
    eapply chvarlit; eauto. lia.
    forwards~: lookupv_minus H1 v2.
    assert (S (i - S n) = i - n) as He. lia. rewrite He in H3. eauto.
Qed.

(* ==================================================================== *)
(*  The core dynamic conservativity (typing-independent)                 *)
(* ==================================================================== *)

(* the image of [trans_e] is exactly the pure-lambda fragment *)
Inductive isf : exp -> Prop :=
  | islit: forall i, isf (lit i)
  | isvar: forall n, isf (var n)
  | islam: forall e,
        isf e ->
        isf (lam e)
  | isapp: forall e1 e2,
        isf e1 ->
        isf e2 ->
        isf (app e1 e2).

#[export]
Hint Constructors isf: core.

Lemma lookupv_det: forall E n v1,
  lookupv E n v1 -> forall v2, lookupv E n v2 -> v1 = v2.
Proof. introv Hl. inductions Hl; introv Hl2; inverts* Hl2. Qed.

Inductive isfv : exp -> Prop:=
  | isfv_lit: forall i, isfv (lit i)
  | isfv_clos: forall E e,
      isf e ->
      isfv E ->
      isfv (clos E e)
  | isfe_nil: isfv unit
  | isfe_cons: forall E v,
      isfv v ->
      isfv E ->
      isfv (E,,v).

#[export]
Hint Constructors isfv : core.

Lemma lookup_isfv: forall E n v',
  lookupv E n v' -> isfv E -> isfv v'.
Proof. introv Hl. inductions Hl; introv Hs; inverts* Hs. Qed.

Lemma isf_isfv: forall E e v,
  big E e v -> isf e -> isfv E -> isfv v.
Proof.
  introv Hb. inductions Hb; introv Hs Hv;
  try solve [inverts* Hs].
  - eapply lookup_isfv; eauto.
  - inverts* Hs.
    forwards~: IHHb1 H2 Hv. inverts* H0.
Qed.

Lemma dyn_conserve_ori: forall E e v,
  big E e v ->
  isf e ->
  isfv E -> forall t,
  check e E 0 t -> exists w,
  fbig t w /\ resrel w v.
Proof.
  introv Hb. inductions Hb; introv Hi He Hc; try solve [inverts* Hi].
  - inverts Hi. inverts Hc.
    + lia.
    + exists (fabs s). assert (n - 0 = n) as Hn by lia. rewrite Hn in H4.
      forwards~: lookupv_det H0 H4. subst. split*.
    + exists (flit j). assert (n - 0 = n) as Hn by lia. rewrite Hn in H4.
      forwards~: lookupv_det H0 H4. subst. split*.
  - inverts Hi. inverts Hc. exists (flit n). split*.
  - inverts Hi. inverts Hc.
    exists (fabs e'). split*.
  - inverts Hi. inverts Hc.
    forwards~ (w1&Hf1&Hr1): IHHb1 H2 H4.
    forwards~ (w2&Hf2&Hr2): IHHb2 H3 H8.
    inverts Hr1.
    forwards~ Hsn: check_sn H5 Hr2.
    forwards~ Hfv: isf_isfv Hb1 He. inverts Hfv.
    forwards~ Hv2: isf_isfv Hb2.
    forwards~ (w&Hfw&Hrw): IHHb3 (subst t 0 w2).
    exists w. split. eapply fb_app; eauto. eauto.
Qed.

Lemma trans_isf: forall t e,
  trans_e t e -> isf e.
Proof. introv Ht. inductions Ht; eauto. Qed.

Lemma dyn_conserve_small: forall e v,
  mstep unit e v ->
  value v -> forall t,
  trans_e t e ->
  closed t -> exists w,
  mred t w /\ resrel w v.
Proof.
  introv Hm Hv Htr Hc.
  forwards~ Hb: big_complete Hm Hv.
  unfold closed in *.
  forwards~: bound_check Hc unit Htr.
  forwards~ (w&?&?): dyn_conserve_ori Hb H.
  eapply trans_isf; eauto.
  exists w. split*.
  eapply fbig_sound; eauto.
Qed.

(* ==================================================================== *)
(*  Closedness from typing (uses the shared System-F typing [ftyping])   *)
(* ==================================================================== *)

Fixpoint elen (T:fenv) : nat :=
  match T with
  | nil => 0
  | fevar _ :: T1 => S (elen T1)
  | fetvar :: T1 => elen T1
  end.

Lemma typed_bound: forall T e A,
  ftyping T e A -> bound e (elen T).
Proof.
  introv Hs. inductions Hs;
  try solve [eauto].
  - inductions T.
    + inverts H0.
    + destruct a.
      * simpl. destruct x.
        ** inverts H0. econstructor. lia.
        ** inverts H0. econstructor.
           forwards~: fwfe_inv H.
           forwards~: IHT H0 H2. inverts H1. lia.
      * inverts H0. forwards~: fwfe_inv H.
        forwards~ [?|?]: fgetv_none_some T x.
        ** rewrite H1 in H2. inverts H2.
        ** destruct H1. forwards~: IHT H0 H1.
Qed.

Lemma typed_closed: forall e A,
  ftyping nil e A -> closed e.
Proof.
  introv Hs. unfold closed.
  forwards~: typed_bound Hs.
Qed.

(* ==================================================================== *)
(*  HEADLINE: dynamic conservativity of the implicit FE calculus.        *)
(* ==================================================================== *)

Lemma dyn_conserve_imp : forall e v t A1 A,
  has_type top e A1 ->            (* well-typed CLOSED implicit FE term ... *)
  trans_e t e ->
  trans_t A A1 ->
  mstep unit e v ->               (* ... that FE-evaluates to a value v     *)
  value v ->
  exists w, mred t w /\ resrel w v.
Proof.
  introv Ht Hte Htt Hm Hv.
  (* implicit FE typing  ==>  System-F typing in the empty env *)
  assert (Hf: ftyping (@nil fbind) t A).
  { eapply conserve_new; eauto. }
  (* a closed System-F program is a closed term *)
  forwards~ Hcl: typed_closed Hf.
  eapply dyn_conserve_small; eauto.
Qed.

(* ==================================================================== *)
(*  System-F big-step is deterministic.                          *)
(* ==================================================================== *)
Lemma fbig_det: forall t w1, fbig t w1 -> forall w2, fbig t w2 -> w1 = w2.
Proof.
  introv Hb. inductions Hb; introv Hb'; inverts Hb'; auto.
  match goal with H: fbig t1 _ |- _ => forwards EQ: IHHb1 H end. inverts EQ.
  match goal with H: fbig t2 _ |- _ => forwards EQ2: IHHb2 H end. subst.
  match goal with H: fbig (subst _ _ _) _ |- _ => eapply IHHb3; exact H end.
Qed.


Lemma dyn_complete_imp : forall e t A1 A,
  has_type top e A1 ->
  trans_e t e ->
  trans_t A A1 ->
  forall w, mred t w -> fvalue w ->
  exists v, mstep unit e v /\ resrel w v.
Proof.
  introv Ht Hte Htt. introv Hmr Hfv.
  (* FE is normalizing: e evaluates to some value v *)
  forwards~ (v & Hm & Hv): normalization Ht.
  (* dynamic conservativity: t reduces to some w' matching v *)
  forwards~ (w' & Hmr' & Hrr): dyn_conserve_imp Ht Hte Htt Hm Hv.
  assert (Hfv': fvalue w') by (inverts Hrr; eauto).
  (* System-F reduction to a value is deterministic: w = w' *)
  forwards Hb:  fbig_complete Hmr  Hfv.
  forwards Hb': fbig_complete Hmr' Hfv'.
  forwards Heq: fbig_det Hb Hb'.
  exists v. split. assumption. rewrite Heq. assumption.
Qed.
