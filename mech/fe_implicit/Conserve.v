Require Import LibTactics.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
Require Import Stdlib.Lists.List.
Require Import Stdlib.Classes.EquivDec.
From Stdlib Require Import Strings.String.
Import ListNotations.
Require Export Teq ExpSyntax Semantics Typing.
Set Implicit Arguments.



(* Rocq 9.1 compat *)
Definition beq_nat (n m : nat) : bool := Nat.eqb n m.

Inductive ftyp : Set :=
  | ftvar : nat -> ftyp
  | fint : ftyp
  | farr : ftyp -> ftyp -> ftyp
  | fall : ftyp -> ftyp.


(* implicit System F terms: NO type abstraction or application. *)
Inductive term : Set :=
  | fvar : nat -> term
  | flit : nat -> term
  | fabs : term -> term
  | fapp : term -> term -> term.

Fixpoint ftshift (X : nat) (A : ftyp) {struct A} : ftyp :=
  match A with
    | ftvar Y      => ftvar (if le_gt_dec X Y then 1 + Y else Y)
    | fint         => fint
    | farr A1 A2 => farr (ftshift X A1) (ftshift X A2)
    | fall A2   => fall (ftshift (1 + X) A2)
  end.

Fixpoint tsubst (A : ftyp) (X : nat) (A' : ftyp) {struct A} : ftyp :=
  match A with
  | ftvar Y =>
      match lt_eq_lt_dec Y X with
      | inleft (left _)  => ftvar Y
      | inleft (right _) => A'
      | inright _        => ftvar (Y - 1)
      end
  | fint         => fint
  | farr A1 A2 => farr (tsubst A1 X A') (tsubst A2 X A')
  | fall A2   => fall (tsubst A2 (1 + X) (ftshift 0 A'))
  end.

Inductive fbind :=
  | fevar : ftyp -> fbind
  | fetvar: fbind.

Definition fenv := list fbind.

Fixpoint f_check (T : fenv) (X : nat) {struct T} : bool :=
  match T with
  | []     => false
  | fevar _ :: T' => f_check T' X
  | fetvar :: T' =>
      match X with
        | O    => true
        | S X' => f_check T' X'
      end
  end.

Definition opt_map (A B : Set) (f : A -> B) (x : option A) :=
  match x with
  | Some x => Some (f x)
  | None => None
  end.


Fixpoint fget_var (T : fenv) (x : nat) {struct T} : option ftyp :=
  match T with
  | []    => None
  | fetvar :: T'  => opt_map (ftshift 0) (fget_var T' x)
  | fevar A :: T' =>
      match x with
      | O    => Some A
      | S x' => fget_var T' x'
      end
  end.

Inductive fwfe: fenv -> Prop :=
  | fwe_nil: fwfe nil
  | fwe_tvar: forall T,
      fwfe T ->
      fwfe (fetvar :: T)
  | fwe_int: forall T,
      fwfe T ->
      fwfe (fevar fint :: T)
  | fwe_check: forall T i,
      fwfe T ->
      f_check T i = true ->
      fwfe ((fevar (ftvar i)) :: T)
  | fwe_arr: forall T A B,
      fwfe (fevar A :: T) ->
      fwfe (fevar B :: T) ->
      fwfe (fevar (farr A B) :: T)
  | fwe_all: forall T A,
      fwfe T ->
      fwfe (fevar A :: fetvar :: T) ->
      fwfe (fevar (fall A) :: T).

Definition fwft (T : fenv) (A : ftyp) : Prop :=
  fwfe (fevar A :: T).


(* System F typing: generalisation/instantiation keep the term. *)
Inductive ftyping : fenv -> term -> ftyp -> Prop :=
  | T_Lit: forall (T : fenv) (i : nat),
      fwfe T ->
      ftyping T (flit i) fint
  | T_Var : forall (T : fenv) (x : nat) (A : ftyp),
      fwfe T ->
      fget_var T x = Some A ->
      ftyping T (fvar x) A
  | T_Abs : forall (T : fenv) (t : term) (A1 A2 : ftyp),
      ftyping (fevar A1 :: T) t A2 ->
      ftyping T (fabs t) (farr A1 A2)
  | T_App : forall (T : fenv) (t1 t2 : term) (A1 A2 : ftyp),
      ftyping T t1 (farr A1 A2) ->
      ftyping T t2 A1 ->
      ftyping T (fapp t1 t2) A2
  | T_Tabs : forall (T : fenv) (t : term) (A2 : ftyp),
      ftyping (fetvar :: T) t A2 ->
      ftyping T t (fall A2)
  | T_Tapp : forall (T : fenv) (t1 : term) (A1 A2 : ftyp),
      ftyping T t1 (fall A1) ->
      fwft T A2 ->
      ftyping T t1 (tsubst A1 0 A2).

#[export]
Hint Constructors ftyp term fbind fwfe ftyping: core.

Inductive s_fwft: fenv -> ftyp -> Prop :=
  | s_fwft_var: forall T X,
      f_check T X = true ->
      s_fwft T (ftvar X)
  | s_fwft_int: forall T,
      s_fwft T fint
  | s_fwft_arr: forall T A1 A2,
      s_fwft T A1 ->
      s_fwft T A2 ->
      s_fwft T (farr A1 A2)
  | s_fwft_all: forall T A2,
      s_fwft (fetvar :: T) A2 ->
      s_fwft T (fall A2).

Inductive s_fwfe: fenv -> Prop :=
  | s_fwfe_nil: s_fwfe []
  | s_fwfe_evar: forall T A,
      s_fwfe T ->
      s_fwft T A ->
      s_fwfe (fevar A :: T)
  | s_fwfe_etvar: forall T,
      s_fwfe T ->
      s_fwfe (fetvar :: T).

#[export]
Hint Constructors s_fwft s_fwfe: core.



Lemma fwfe_inv_gen: forall T0,
  fwfe T0 -> forall t T,
  T0 = t :: T ->
  fwfe T.
Proof.
  introv Hw. induction Hw; introv Heq; try discriminate;
    injection Heq as ? ?; subst; eauto.
Qed.

Lemma fwfe_inv: forall t T,
  fwfe (t :: T) ->
  fwfe T.
Proof.
  introv Hw. eapply fwfe_inv_gen; eauto.
Qed.

Lemma fgetv_none_some: forall T n,
  (fget_var T n = None) \/ (exists A, fget_var T n = Some A).
Proof.
  intros T n. gen T. inductions n; introv; eauto.
  - inductions T.
    + left. eauto.
    + destruct* a.
      * right. exists* f.
      * destruct IHT.
        ** left. simpl. rewrite H. eauto.
        ** destruct* H. right. exists* (ftshift 0 x). simpl. rewrite H. eauto.
  - gen n. inductions T; intros; eauto.
    forwards~: IHT IHn.
    destruct* a.
    + forwards~ [?|?]: H.
      * left. simpl. rewrite H0. eauto.
      * right. destruct H0. exists* (ftshift 0 x). simpl. rewrite H0. eauto.
Qed.

Inductive fadde: fenv -> fenv -> Prop :=
  | fa_nil: fadde nil nil
  | fa_evar: forall T1 T2 A,
      fadde T1 T2 ->
      fadde (fevar A :: T1) (fevar A :: T2)
  | fa_tvar: forall T1 T2,
      fadde T1 T2 ->
      fadde (fetvar :: T1) (fetvar :: T2)
  | fa_add: forall T1 T2 A,
      fadde T1 T2 ->
      fwft T2 A ->
      fadde T1 (fevar A :: T2).

#[export]
Hint Constructors fadde : core.


Inductive finsert : nat -> fenv -> fenv -> Prop :=
  | fitv_here2 : forall (T : fenv),
      finsert 0 T (fetvar :: T)
  | fitv_var : forall (X : nat) (A : ftyp) (T T' : fenv),
      finsert X T T' ->
      finsert X (fevar A :: T) (fevar (ftshift X A) :: T')
  | itv_tvar: forall (X : nat) (T T' : fenv),
      finsert X T T' ->
      finsert (S X) (fetvar :: T) (fetvar :: T').

#[export]
Hint Constructors finsert: core.


Lemma check_finsert_ge: forall (X' : nat) (T T' : fenv),
  finsert X' T T' -> forall X,
  X' <= X ->
  f_check T' (1 + X) = f_check T X.
Proof.
  introv Hi. inductions Hi; introv Hl; try solve [simpl; eauto].
  - destruct* X0. lia.
    simpl. eapply IHHi. lia.
Qed.

Lemma check_finsert_lt: forall (X' : nat) (T T' : fenv),
  finsert X' T T' -> forall X,
  X' > X ->
  f_check T' X = f_check T X.
Proof.
  introv Hi. inductions Hi; introv Hl; try solve [simpl; eauto]; try solve [lia].
  - destruct* X0.
    simpl. eapply IHHi. lia.
Qed.


Inductive wfe2: typ -> Prop :=
  | we2_nil: wfe2 top
  | we2_tvar: forall T,
      wfe2 T ->
      wfe2 (T &s)
  | we2_int: forall T m,
      wfe2 T ->
      wfe2 (and T m int)
  | we2_check: forall T m i,
      wfe2 T ->
      check T i ->
      wfe2 (and T m (tvar i))
  | we2_get: forall T m i A,
      wfe2 T ->
      lookt T i A ->
      wfe2 (and T m (tvar i))
  | we2_arr: forall T m A B,
      wfe2 (T & A) ->
      wfe2 (T & B) ->
      wfe2 (and T m (arr A B))
  | we2_all: forall T m A,
      wfe2 T ->
      wfe2 (T &s & A) ->
      wfe2 (and T m (all A))
  | we2_box: forall T m A T1,
      wfe2 (T1 &= A) ->
      rigid 0 T1 A ->
      wfe2 T ->
      wfe2 (and T m (boxt T1 A))
  | we2_mani: forall T m A B,
      wfe2 (T &= A &= B) ->
      wfe2 (T &= A) ->
      wfe2 (and T m (mani A B))
  | we2_top: forall T m,
      wfe2 T ->
      wfe2 (and T m top)
  | we2_and: forall T m1 T1 A2 m2,
      wfe2 (T &= T1) ->
      wfe2 ((T +++ T1) &= A2) ->
      lshape T1 ->
      wfe2 (and T m1 (and T1 m2 A2))
  | we2_ands: forall T m1 T1,
      wfe2 (T &= T1) ->
      lshape T1 ->
      wfe2 (and T m1 (T1 &s))
  | we2_rcd: forall T l A m,
      wfe2 (T &= A) ->
      wfe2 (and T m (rcd l A)).

#[export]
Hint Constructors wfe2 : core.

Inductive trans_t : ftyp -> typ -> Prop :=
  | tt_tvar : forall n, trans_t (ftvar n) (tvar n)
  | tt_int: trans_t fint int
  | tt_arr: forall A B A1 B1,
      trans_t A A1 ->
      trans_t B B1 ->
      trans_t (farr A B) (arr A1 B1)
  | tt_all: forall A A1,
      trans_t A A1 ->
      trans_t (fall A) (all A1).


(* term translation: identity on var/lit/abs/app. *)
Inductive trans_e: term -> exp -> Prop :=
  | te_var: forall n, trans_e (fvar n) (var n)
  | te_lit: forall n, trans_e (flit n) (lit n)
  | te_abs: forall t e,
      trans_e t e ->
      trans_e (fabs t) (lam e)
  | te_app: forall t1 t2 e1 e2,
      trans_e t1 e1 ->
      trans_e t2 e2 ->
      trans_e (fapp t1 t2) (app e1 e2).

Inductive trans_env: fenv -> typ -> Prop :=
  | te_nil: trans_env [] top
  | te_cons1: forall A A1 T T1,
      trans_t A A1 ->
      trans_env T T1 ->
      trans_env (fevar A::T) (T1 & A1)
  | te_cons: forall T T1,
      trans_env T T1 ->
      trans_env (fetvar::T) (T1 &s).

#[export]
Hint Constructors trans_t trans_e trans_env : core.



(* ------------------------------- *)
Lemma f2check: forall T T1,
  trans_env T1 T -> forall i,
  f_check T1 i = true ->
  check T i.
Proof.
  introv Ht. inductions Ht; introv Hc.
  - inverts Hc.
  - inverts* Hc.
  - destruct* i.
Qed.


Lemma f2wfe: forall T0,
  fwfe T0 -> forall T,
  trans_env T0 T ->
  wfe T.
Proof.
  introv Hf. inductions Hf; introv Ht; try solve [eauto];
  try solve [inverts* Ht].
  - inverts Ht. inverts H1. eauto.
  - inverts Ht. inverts H2.
    forwards~: f2check H4 H.
  - inverts Ht. inverts H1.
    forwards~: IHHf1 (T2 & A2).
    forwards~: IHHf2 (T2 & B1).
    forwards~: wfe_evar_eteq H.
    forwards~: wfe_evar_eteq H0.
  - inverts Ht. inverts H1.
    forwards~: IHHf1 H3.
    forwards~: IHHf2 (T2 &s & A2).
    forwards~: wfe_evar_eteq H1.
Qed.


Lemma f2wft: forall T0 A0,
  fwft T0 A0 -> forall T,
  trans_env T0 T -> forall A,
  trans_t A0 A ->
  wft T A.
Proof.
  intros. unfold fwft in *. unfold wft in *.
  eapply wfe_evar_eteq; eauto.
  eapply f2wfe; eauto.
Qed.


Lemma trans_t_ex: forall A,
  exists A', trans_t A A'.
Proof.
  intros A. inductions A; eauto.
  - destruct* IHA1.
  - destruct* IHA.
Qed.


Fixpoint tsubst2 (A : typ) (X : nat) (A' : typ) {struct A} : typ :=
  match A with
  | tvar Y =>
      match lt_eq_lt_dec Y X with
      | inleft (left _)  => tvar Y
      | inleft (right _) => A'
      | inright _        => tvar (Y - 1)
      end
  | int         => int
  | arr A1 A2 => arr (tsubst2 A1 X A') (tsubst2 A2 X A')
  | all A2   => all (tsubst2 A2 (1 + X) (tshift 0 A'))
  | _ => A
  end.

Lemma tt_tshift: forall A1 A2,
  trans_t A1 A2-> forall X,
  trans_t (ftshift X A1) (tshift X A2).
Proof.
  introv Ht. inductions Ht; intros; simpl; eauto.
Qed.

Lemma tt_tsubsst: forall A1 A4,
  trans_t A1 A4 -> forall A2 A3,
  trans_t A2 A3 -> forall X,
  trans_t (tsubst A1 X A2) (tsubst2 A4 X A3).
Proof.
  introv Ht1. inductions Ht1; introv Ht2; intros;
  try solve [simpl; eauto].
  - simpl. destruct (lt_eq_lt_dec n X).
    + destruct s; eauto.
    + eauto.
  - simpl. forwards~: tt_tshift Ht2 0.
Qed.

Lemma tt_det: forall A1 A2,
  trans_t A1 A2 -> forall A3,
  trans_t A1 A3 ->
  A2 = A3.
Proof.
  introv Ht. inductions Ht; introv Hs; try solve [inverts* Hs].
  - inverts Hs. forwards~: IHHt1 H1. forwards~: IHHt2 H3. subst. eauto.
  - inverts Hs. forwards~: IHHt H0. subst. eauto.
Qed.

Inductive all_abs: typ -> Prop :=
  | abs_nil: all_abs top
  | abs_evar: forall A T,
      all_abs T ->
      all_abs (T & A)
  | abs_etvar: forall T,
      all_abs T ->
      all_abs (T &s).

#[export]
Hint Constructors all_abs : core.

Lemma tten_all_abs: forall T0 T,
  trans_env T0 T ->
  all_abs T.
Proof.
  introv Ht. inductions Ht; eauto.
Qed.

Lemma f_opt_map_inv: forall A X ot,
  opt_map (ftshift X) ot = Some A ->
  exists B, ot = Some B /\ A = ftshift X B.
Proof.
  intros. destruct ot.
  - exists f. split*. simpl in H. inverts H. eauto.
  - simpl in H. inverts H.
Qed.

Lemma fget_get: forall T0 T,
  trans_env T0 T -> forall n A0,
  fget_var T0 n = Some A0 -> exists A,
  get_var T n A /\ trans_t A0 A.
Proof.
  introv Ht. inductions Ht; intros; eauto.
  - inverts H.
  - destruct* n.
    + inverts* H0.
    + inverts* H0. forwards~ (B&?&?): IHHt H2. exists* B.
  - inverts* H.
    forwards~ (B&?&?): f_opt_map_inv H1. subst.
    forwards~ (C&?&?): IHHt H.
    exists (tshift 0 C). split*.
    eapply tt_tshift; eauto.
Qed.



(* ---------------------------------------- *)
Inductive ityp : nat -> typ -> typ -> typ -> Prop :=
  | ityp_here2 : forall A T,
      ityp 0 A T (T &= A)
  | ityp_var : forall (X : nat) B (A : typ) (T T' : typ),
      ityp X B T T' ->
      ityp X B (T & A) (T' & (tshift X A))
  | ityp_tvar: forall (X : nat) B (T T' : typ),
      ityp X B T T' ->
      ityp (S X) (tshift 0 B) (T &s) (T' &s)
  | ityp_teq: forall (X : nat) B (A : typ) (T T' : typ),
      ityp X B T T' ->
      ityp (S X) (tshift 0 B) (T &= A) (T' &= (tshift X A)).

#[export]
Hint Constructors ityp : core.

Lemma all_abs_lookt: forall T,
  all_abs T -> forall n A,
  lookt T n A ->
  False.
Proof.
  introv Ha. inductions Ha; introv Hl; try solve [inverts* Hl].
Qed.

Fixpoint kshift (k : nat) (A : typ) {struct k} : typ :=
  match k with
    | 0       => A
    | S k' => (tshift 0) (kshift k' A)
  end.

Lemma wft_arr_inv: forall T A B,
  wft T (arr A B) ->
  wft T A /\ wft T B.
Proof.
  intros. unfold wft in *.
  inverts* H; try solve [destruct* t; inverts* H0].
Qed.



Inductive repl_bot (A : typ) : nat -> typ -> typ -> Prop :=
  | rb_here  : forall T, all_abs T -> wft T A -> repl_bot A 0 (T &= A) (T &s)
  | rb_etvar : forall k GL GR,
      repl_bot A k GL GR -> repl_bot A (S k) (GL &s) (GR &s).

#[export] Hint Constructors repl_bot : core.

Lemma repl_bot_wfe_l : forall A k GL GR, repl_bot A k GL GR -> wfe GL.
Proof.
  introv H. inductions H; eauto.
Qed.

Lemma repl_bot_wfe_r : forall A k GL GR, repl_bot A k GL GR -> wfe GR.
Proof.
  introv H. inductions H.
  - eapply we_tvar. eapply wft_wfe; eauto.
  - eapply we_tvar; eauto.
Qed.

#[export] Hint Resolve repl_bot_wfe_l repl_bot_wfe_r : core.

Lemma repl_bot_lookt_k : forall A k GL GR, repl_bot A k GL GR ->
  lookt GL k (kshift (S k) A).
Proof.
  introv H. inductions H; simpl.
  - eapply lookt_zero.
  - replace (tshift 0 (tshift 0 (kshift k A)))
      with (tshift 0 (kshift (S k) A)) by reflexivity.
    eapply lookt_etvar; eauto.
Qed.

Lemma tshift_k_kshift : forall A k,
  tshift k (kshift k A) = kshift (S k) A.
Proof.
  intros A k. revert A. inductions k; intros A; simpl; eauto.
  forwards Hp: tshift_tshift_prop_1 (kshift k A) 0 k. simpl in Hp.
  rewrite <- Hp. rewrite IHk. reflexivity.
Qed.

Lemma repl_bot_check_r : forall A k GL GR, repl_bot A k GL GR ->
  forall n, n <> k -> check GR n -> check GL n.
Proof.
  introv H. inductions H; introv Hne Hc.
  - inverts Hc; try lia. econstructor; eauto.
  - inverts Hc.
    + econstructor.
    + econstructor. eapply IHrepl_bot; eauto.
Qed.

Lemma repl_bot_wft_check_r : forall A k GL GR, repl_bot A k GL GR ->
  forall n, wft GR (tvar n) -> check GR n.
Proof.
  introv Hrb Hw. unfold wft in Hw. inverts Hw; eauto.
  exfalso.
  assert (Hall: forall (G : typ), repl_bot A k GL G -> forall m B, lookt G m B -> False).
  { clear. introv Hr. inductions Hr; introv Hl.
    - inverts Hl. eapply all_abs_lookt; eauto.
    - inverts Hl. eapply IHHr; eauto. }
  eapply Hall; eauto.
Qed.

Lemma refl_relocate : forall Mt M, trans_t Mt M -> forall A k GL GR,
  repl_bot A k GL GR ->
  wft GR (tshift k M) ->
  teq GL (tshift k M) (tshift k M) GR.
Proof.
  introv Ht. inductions Ht; introv Hrb HwM.
  - forwards~ Hcr: repl_bot_wft_check_r Hrb HwM.
    eapply eq_tvar; eauto.
    eapply repl_bot_check_r; [ exact Hrb | | exact Hcr ].
    simpl in *. destruct (le_gt_dec k n); lia.
  - simpl in *. eapply eq_int; eauto.
  - simpl in *.
    forwards~ (HwA&HwB): wft_arr_inv HwM.
    eapply eq_arr; eauto.
  - simpl in *. unfold wft in HwM. inverts HwM.
    eapply eq_all.
    eapply IHHt with (A := A0) (k := S k) (GL := GL &s); eauto.
Qed.

Lemma tt_kshift : forall A1 A2, trans_t A1 A2 -> forall k,
  exists B1, trans_t B1 (kshift k A2).
Proof.
  introv Ht. inductions k; simpl.
  - exists A1. eauto.
  - destruct IHk as (B1 & HB). exists (ftshift 0 B1). eapply tt_tshift; eauto.
Qed.

Lemma repl_bot_wft_kshift : forall A k GL GR, repl_bot A k GL GR ->
  wft GR (kshift (S k) A).
Proof.
  introv H. inductions H; simpl.
  - eapply insert_tvar_wft; [ eapply itv_here2 | eapply we_tvar; eapply wft_wfe; eauto | eauto ].
  - eapply insert_tvar_wft; [ eapply itv_here2
      | eapply we_tvar; eapply wft_wfe; eauto | eauto ].
Qed.

Lemma repl_bot_wft_check_gr : forall A k GL GR, repl_bot A k GL GR ->
  forall n, wft GR (tvar n) -> check GR n.
Proof.
  intros. eapply repl_bot_wft_check_r; eauto.
Qed.

Lemma subst_fold_gen : forall Dt D, trans_t Dt D -> forall At A k GL GR,
  trans_t At A ->
  repl_bot A k GL GR ->
  wft GR D ->
  teq GL D (tshift k (tsubst2 D k (kshift k A))) GR.
Proof.
  introv Ht. inductions Ht; introv Hta Hrb HwD.
  - simpl. destruct (lt_eq_lt_dec n k) as [[Hlt|Heq]|Hgt].
    + simpl.
      destruct (le_gt_dec k n); try lia.
      forwards~ Hcr: repl_bot_wft_check_gr Hrb HwD.
      eapply eq_tvar; eauto. eapply repl_bot_check_r; [ exact Hrb | lia | exact Hcr ].
    + subst. rewrite tshift_k_kshift.
      eapply eq_eql; [ eapply repl_bot_lookt_k; exact Hrb | ].
      forwards (B1 & HB1): tt_kshift Hta k.
      forwards~ Hwk: repl_bot_wft_kshift Hrb.
      rewrite <- tshift_k_kshift.
      eapply refl_relocate; [ exact HB1 | exact Hrb | ].
      rewrite tshift_k_kshift; eauto.
    + simpl.
      destruct (le_gt_dec k (n - 1)); try lia.
      replace (S (n - 1)) with n by lia.
      forwards~ Hcr: repl_bot_wft_check_gr Hrb HwD.
      eapply eq_tvar; eauto. eapply repl_bot_check_r; [ exact Hrb | lia | exact Hcr ].
  - simpl. eapply eq_int; eauto.
  - simpl. unfold wft in HwD. forwards~ (HwA&HwB): wft_arr_inv HwD.
    eapply eq_arr; eauto.
  - simpl. unfold wft in HwD. inverts HwD.
    eapply eq_all.
    forwards Hr: IHHt Hta (rb_etvar Hrb); [ unfold wft; eauto | ].
    simpl in Hr.
    replace (tshift 0 (kshift k A0)) with (kshift (S k) A0) in Hr by reflexivity.
    exact Hr.
Qed.

Lemma relate_bal : forall T A B At Dt D,
  teq (T &s) B D (T &s) ->
  all_abs T ->
  wft T A ->
  trans_t At A ->
  trans_t Dt D ->
  teq (T &= A) B (tshift 0 (tsubst2 D 0 A)) (T &s).
Proof.
  introv Hb Ha Hw Hta Htt.
  assert (Hinst: teq (T &= A) B D (T &= A)).
  { eapply inst_teq; [ exact Hb | eapply teq_refl; exact Hw ]. }
  eapply teq_trans; [ exact Hinst | ].
  forwards Hsf: subst_fold_gen Htt Hta (rb_here Ha Hw).
  - eapply teq_wft_right; exact Hb.
  - simpl in Hsf. exact Hsf.
Qed.

Lemma relate_gen: forall T A B,
  teq (T &s) A B (T &s) -> forall B1,
  all_abs T ->
  trans_t B1 B -> forall C C1,
  trans_t C1 C ->
  wft T C ->
  teq (T &= C) A (tshift 0 (tsubst2 B 0 C)) (T &s).
Proof.
  introv Hb Ha Htb Htc Hwc.
  eapply relate_bal; eauto.
Qed.

(* ===== completeness (SF -> FE): generalisation reflects onto t_gen,
   instantiation onto t_tapp then teq. ===== *)
Lemma complete: forall T t A,
  ftyping T t A -> forall T1 e A1,
  trans_env T T1 ->
  trans_e t e ->
  trans_t A A1 ->
  has_type T1 e A1.
Proof.
  introv Ht. inductions Ht; introv Hten Hte Htt.
  - inverts Hte. inverts Htt. econstructor.
    eapply f2wfe; eauto.
  - inverts Hte.
    forwards~ (A0&?&?): fget_get Hten H0.
    forwards~: tt_det Htt H2. subst.
    econstructor; eauto.
    eapply f2wfe; eauto.
  - inverts Hte. inverts Htt.
    econstructor; eauto.
  - inverts Hte. forwards~ (A'&?): trans_t_ex A1.
    forwards~: tt_arr H Htt.
    forwards~: IHHt1 Hten H1 H0.
    forwards~: IHHt2 Hten H3 H.
    econstructor; eauto.
  (* T_Tabs : same term, onto t_gen *)
  - inverts Htt.
    econstructor. eapply IHHt; eauto.
  (* T_Tapp : same term, onto t_tapp then teq to substituted type *)
  - forwards~ (A4&?): trans_t_ex A1.
    forwards~: tt_all H0.
    forwards~: IHHt Hten Hte H1.
    forwards~ (A2'&Ha2): trans_t_ex A2.
    forwards~ Hwt: f2wft H Hten Ha2.
    forwards~ Hts: tt_tsubsst H0 Ha2 0.
    forwards~ Hd: tt_det Htt Hts. subst.
    eapply t_eq with (A := mani A2' A4).
    eapply t_tapp; eauto.
    econstructor.
    forwards~ Hwf: typ_ans_wft H2. inverts Hwf.
    eapply relate_gen with (B1 := A1) (C1 := A2);
      [ eapply teq_refl; unfold wft; eassumption
      | eapply tten_all_abs; eauto
      | exact H0 | exact Ha2 | exact Hwt ].
Qed.



Fixpoint sf (A : typ) : ftyp :=
  match A with
  | tvar n     => ftvar n
  | int        => fint
  | arr A B    => farr (sf A) (sf B)
  | all A      => fall (sf A)
  | mani A B   => tsubst (sf B) 0 (sf A)
  | _          => fint
  end.

(* sf is a left inverse of trans_t on the translatable fragment. *)
Lemma sf_tt: forall A0 A1,
  trans_t A0 A1 ->
  sf A1 = A0.
Proof.
  introv Ht. inductions Ht; simpl; try solve [eauto]; try solve [f_equal; eauto].
Qed.

(* sf commutes with shifting.  Needed for the var case (get_var shifts by
   tshift, fget_var by ftshift) and for the mani/tsubst collapse. *)

(* ftshift commutes with itself (lower cutoff first). *)
Lemma ftshift_ftshift: forall A X Y,
  Y <= X ->
  ftshift Y (ftshift X A) = ftshift (S X) (ftshift Y A).
Proof.
  intros A. inductions A; introv Hle; try solve [simpl; f_equal; eauto].
  - cbn [ftshift].
    destruct (le_gt_dec X n); destruct (le_gt_dec Y n); simpl;
      repeat match goal with |- context[if ?d then _ else _] => destruct d end;
      try lia; f_equal; lia.
  - simpl. f_equal. eapply IHA. lia.
Qed.

(* shift above a substitution point: cutoff X at-or-above subst point Y. *)
Lemma ftshift_tsubst_ge: forall A X Y A',
  Y <= X ->
  ftshift X (tsubst A Y A') = tsubst (ftshift (S X) A) Y (ftshift X A').
Proof.
  intros A. inductions A; introv Hle; try solve [simpl; f_equal; eauto].
  - cbn [tsubst ftshift].
    destruct (lt_eq_lt_dec n Y) as [[?|?]|?].
    + destruct (le_gt_dec (S X) n); try lia. cbn [tsubst].
      destruct (lt_eq_lt_dec n Y) as [[?|?]|?]; try lia. cbn [ftshift].
      destruct (le_gt_dec X n); try lia. eauto.
    + subst. destruct (le_gt_dec (S X) Y); try lia. cbn [tsubst].
      destruct (lt_eq_lt_dec Y Y) as [[?|?]|?]; try lia. eauto.
    + destruct (le_gt_dec (S X) n); cbn [tsubst].
      * destruct (lt_eq_lt_dec (1+n) Y) as [[?|?]|?]; try lia. cbn [ftshift].
        destruct (le_gt_dec X (n-1)); try lia. f_equal. lia.
      * destruct (lt_eq_lt_dec n Y) as [[?|?]|?]; try lia. cbn [ftshift].
        destruct (le_gt_dec X (n-1)); try lia. f_equal; lia.
  - simpl. f_equal. rewrite IHA; try lia. f_equal. symmetry. eapply ftshift_ftshift. lia.
Qed.

(* sf commutes with tshift on the whole typ algebra. *)
Lemma sf_tshift: forall A X,
  sf (tshift X A) = ftshift X (sf A).
Proof.
  intros A. inductions A; introv; simpl; try solve [eauto]; try solve [f_equal; eauto].
  - rewrite IHA1. rewrite IHA2.
    rewrite ftshift_tsubst_ge; try lia. eauto.
  - destruct m; simpl; eauto.
Qed.



Inductive genv: fenv -> typ -> Prop :=
  | ge_nil: genv [] top
  | ge_evar: forall A T T1,
      genv T T1 ->
      wft T1 A ->
      genv (fevar (sf A) :: T) (T1 & A)
  | ge_tvar: forall T T1,
      genv T T1 ->
      genv (fetvar :: T) (T1 &s).

#[export]
Hint Constructors genv : core.



Lemma genv_getvar: forall T0 T1,
  genv T0 T1 -> forall n B,
  get_var T1 n B ->
  fget_var T0 n = Some (sf B).
Proof.
  introv Hg. inductions Hg; introv Hl; try solve [inverts Hl].
  - inverts* Hl.
  - inverts Hl. forwards~ Hf: IHHg H0.
    simpl. rewrite Hf. f_equal. rewrite sf_tshift. eauto.
Qed.


(* lshape types are all sf-collapsed to fint (top / and / ands cases). *)
Lemma lshape_sf_fint: forall A,
  lshape A ->
  sf A = fint.
Proof.
  introv Hl. inductions Hl; simpl; eauto.
Qed.

(* ---- structural SF well-formedness <-> fwfe bridge ---- *)

Lemma s_fwft_fwft: forall T A,
  s_fwft T A -> fwfe T ->
  fwfe (fevar A :: T).
Proof.
  introv Hs. inductions Hs; introv Hw; eauto.
Qed.

Lemma s_fwfe_fwfe: forall T,
  s_fwfe T ->
  fwfe T.
Proof.
  introv Hs. inductions Hs; eauto.
  eapply s_fwft_fwft; eauto.
Qed.

Lemma s_fwft_to_fwft: forall T A,
  s_fwfe T ->
  s_fwft T A ->
  fwft T A.
Proof.
  intros. unfold fwft. eapply s_fwft_fwft; eauto. eapply s_fwfe_fwfe; eauto.
Qed.

(* ---- structural SF well-formedness: weakening + shifting + substitution ---- *)

Lemma s_fwft_finsert: forall T A,
  s_fwft T A -> forall X T',
  finsert X T T' ->
  s_fwft T' (ftshift X A).
Proof.
  introv Hs. inductions Hs; introv Hi; simpl; eauto.
  - destruct (le_gt_dec X0 X).
    + econstructor. forwards~ He: check_finsert_ge Hi X. simpl in He. rewrite He. eauto.
    + econstructor. forwards~ He: check_finsert_lt Hi X. rewrite He. eauto.
Qed.

Lemma s_fwft_weaken_tvar: forall T A,
  s_fwft T A ->
  s_fwft (fetvar :: T) (ftshift 0 A).
Proof.
  intros. eapply s_fwft_finsert; eauto.
Qed.

(* substitution preserves structural SF well-formedness. *)
Lemma s_fwft_subst: forall B T0 X T A,
  s_fwft T0 B ->
  finsert X T T0 ->
  s_fwft T A ->
  s_fwft T (tsubst B X A).
Proof.
  introv Hb. gen X T A. inductions Hb; introv Hi Ha; simpl; eauto.
  - destruct (lt_eq_lt_dec X X0) as [[?|?]|?].
    + econstructor. forwards~ He: check_finsert_lt Hi X. rewrite <- He. eauto.
    + subst. eauto.
    + econstructor. forwards~ He: check_finsert_ge Hi (X-1). lia.
      replace (1 + (X-1)) with X in He by lia. rewrite <- He. eauto.
  - econstructor. eapply IHHb; eauto. eapply s_fwft_weaken_tvar; eauto.
Qed.

(* ---- genvx: genv extended with the manifest (&=) slot, which the sf
   skeleton treats exactly like an abstract type-variable binder.  Needed so
   the mani case of genv_sf_s_fwft can recurse under the manifest binder. ---- *)
Inductive genvx: fenv -> typ -> Prop :=
  | gx_nil: genvx [] top
  | gx_evar: forall A T T1,
      genvx T T1 ->
      wft T1 A ->
      genvx (fevar (sf A) :: T) (T1 & A)
  | gx_tvar: forall T T1,
      genvx T T1 ->
      genvx (fetvar :: T) (T1 &s)
  | gx_teq: forall A T T1,
      genvx T T1 ->
      wft T1 A ->
      genvx (fetvar :: T) (T1 &= A).

#[export]
Hint Constructors genvx : core.

Lemma genv_genvx: forall T0 T1,
  genv T0 T1 ->
  genvx T0 T1.
Proof.
  introv Hg. inductions Hg; eauto.
Qed.

Lemma genvx_check: forall T0 T1,
  genvx T0 T1 -> forall i,
  check T1 i ->
  f_check T0 i = true.
Proof.
  introv Hg. inductions Hg; introv Hc; try solve [inverts Hc].
  - inverts Hc. simpl. eauto.
  - inverts Hc; simpl; eauto.
  - inverts Hc. simpl. eauto.
Qed.

Lemma genvx_lookt: forall T0 T1,
  genvx T0 T1 -> forall i A,
  lookt T1 i A ->
  f_check T0 i = true.
Proof.
  introv Hg. inductions Hg; introv Hl; try solve [inverts Hl].
  - inverts Hl. simpl. eauto.
  - inverts Hl. simpl. eauto.
  - inverts Hl; simpl; eauto.
Qed.

Lemma genvx_sf_s_fwft: forall T1 A,
  wft T1 A -> forall T0,
  genvx T0 T1 ->
  s_fwft T0 (sf A).
Proof.
  intros T1 A. gen T1. inductions A; introv Hw Hg; simpl; eauto;
    try solve [unfold wft in Hw; inverts Hw].
  - (* tvar *)
    unfold wft in Hw. inverts Hw.
    + econstructor. eapply genvx_check; eauto.
    + econstructor. eapply genvx_lookt; eauto.
  - (* arr *)
    unfold wft in Hw. inverts Hw.
    econstructor; [eapply IHA1 | eapply IHA2]; eauto;
      unfold wft; eapply wfe_eteq_evar; eauto.
  - (* all *)
    unfold wft in Hw. inverts Hw.
    econstructor. eapply IHA; eauto.
  - (* mani: sf (mani A B) = tsubst (sf B) 0 (sf A) *)
    unfold wft in Hw. inverts Hw.
    eapply s_fwft_subst with (T0 := fetvar :: T0) (X := 0).
    + eapply IHA2; eauto.
    + econstructor.
    + eapply IHA1; eauto.
Qed.

Lemma genv_sf_s_fwft: forall T0 T1,
  genv T0 T1 -> forall A,
  wft T1 A ->
  s_fwft T0 (sf A).
Proof.
  intros. eapply genvx_sf_s_fwft; eauto. eapply genv_genvx; eauto.
Qed.

Lemma genvx_s_fwfe: forall T0 T1,
  genvx T0 T1 ->
  s_fwfe T0.
Proof.
  introv Hg. inductions Hg; eauto.
  econstructor; eauto. eapply genvx_sf_s_fwft; eauto.
Qed.

Lemma genv_fwfe: forall T0 T1,
  genv T0 T1 ->
  fwfe T0.
Proof.
  introv Hg. eapply s_fwfe_fwfe. eapply genvx_s_fwfe. eapply genv_genvx; eauto.
Qed.

(* genv -> the canonical skeleton of a wft type is System-F well-formed. *)
Lemma genv_sf_fwft: forall T0 T1,
  genv T0 T1 -> forall A,
  wft T1 A ->
  fwft T0 (sf A).
Proof.
  intros. eapply s_fwft_to_fwft.
  - eapply genvx_s_fwfe. eapply genv_genvx; eauto.
  - eapply genv_sf_s_fwft; eauto.
Qed.



Unset Implicit Arguments.



Inductive box_free : typ -> Prop :=
  | bf_int : box_free int
  | bf_tvar : forall n, box_free (tvar n)
  | bf_arr : forall A B, box_free A -> box_free B -> box_free (arr A B)
  | bf_all : forall A, box_free A -> box_free (all A)
  | bf_mani : forall A B, box_free A -> box_free B -> box_free (mani A B)
  | bf_rcd : forall l A, box_free A -> box_free (rcd l A)
  | bf_top : box_free top
  | bf_and : forall A m B, box_free A -> box_free B -> box_free (and A m B)
  | bf_ands : forall A, box_free A -> box_free (ands A).
#[export] Hint Constructors box_free : core.

(* iterated lift on ftyp skeletons *)
Fixpoint liftn (k:nat)(C:ftyp) : ftyp :=
  match k with 0 => C | S k' => ftshift 0 (liftn k' C) end.

(* ---- msf: the ENV-RELATIVE skeleton.  Processes the env typ outermost
   (= de-Bruijn index 0) first.  & (term var) is transparent to type
   indices; &s keeps an abstract binder (raise the kept-depth k); &= is a
   manifest slot -- substitute its sf at depth k. ---- *)
Fixpoint msfk (T:typ)(k:nat)(C:ftyp) : ftyp :=
  match T with
  | top          => C
  | and T0 non _ => msfk T0 k C
  | and T0 rt A  => msfk T0 k (tsubst C k (liftn k (sf A)))
  | ands T0      => msfk T0 (S k) C
  | _            => C
  end.

Definition msf (T:typ)(C:ftyp) := msfk T 0 C.

(* FOUNDATIONAL LEMMA 1: the manifest binder unfolds to a substitution. *)
Lemma msf_eq_unfold: forall T A C,
  msf (and T rt A) C = msf T (tsubst C 0 (sf A)).
Proof.
  intros. unfold msf. reflexivity.
Qed.

(* sf (mani A B) is exactly the manifest unfold of sf B. *)
Lemma sf_mani_unfold: forall A B,
  sf (mani A B) = tsubst (sf B) 0 (sf A).
Proof. reflexivity. Qed.

(* FOUNDATIONAL LEMMA 2: over a genv env (no &= slots) msf is the identity. *)
Lemma msfk_genv_id: forall T0 T1,
  genv T0 T1 -> forall k C,
  msfk T1 k C = C.
Proof.
  introv Hg. inductions Hg; introv; simpl; eauto.
Qed.

Lemma msf_genv_id: forall T0 T1,
  genv T0 T1 -> forall C,
  msf T1 C = C.
Proof.
  intros. unfold msf. eapply msfk_genv_id; eauto.
Qed.

(* ==================================================================== *)
(*  box-free teq_sf_eq kernel                                            *)
(* ==================================================================== *)

(* ---- bf_env: every &= manifest slot stores a box_free type ---- *)
Inductive bf_env : typ -> Prop :=
  | bfe_top : bf_env top
  | bfe_evar : forall T A, bf_env T -> bf_env (and T non A)
  | bfe_tvar : forall T, bf_env T -> bf_env (ands T)
  | bfe_teq  : forall T A, bf_env T -> box_free A -> bf_env (and T rt A).
#[export] Hint Constructors bf_env : core.

(* box_free is preserved by tshift. *)
Lemma box_free_tshift: forall A n, box_free A -> box_free (tshift n A).
Proof.
  introv H. gen n. inductions H; introv; simpl;
    try (destruct m); try (match goal with |- context[le_gt_dec ?a ?b] => destruct (le_gt_dec a b) end); eauto.
Qed.

(* box_free is also reflected by tshift (tshift fixes boxt, so it cannot hide one). *)
Lemma box_free_tshift_rev: forall A n, box_free (tshift n A) -> box_free A.
Proof.
  induction A; introv Hb; simpl in Hb;
    try (destruct m); simpl in Hb; try (inverts Hb; econstructor; eauto; fail);
    try (econstructor; eauto).
Qed.

(* genv envs (only & and &s, no &=) are bf_env. *)
Lemma genv_bf_env: forall T0 T1, genv T0 T1 -> bf_env T1.
Proof.
  introv Hg. inductions Hg; eauto.
Qed.

(* ---- helper 1: fint is fixed by msfk ---- *)
Lemma msfk_fint: forall T k, msfk T k fint = fint.
Proof.
  induction T; introv; simpl; eauto.
  destruct m; simpl; eauto.
Qed.

(* ---- helper 2: msfk distributes over farr ---- *)
Lemma msfk_farr: forall T k X Y,
  msfk T k (farr X Y) = farr (msfk T k X) (msfk T k Y).
Proof.
  induction T; introv; simpl; eauto.
  destruct m; simpl; eauto.
Qed.

(* ---- helper 3: msfk over fall raises the kept-depth ---- *)
Lemma msfk_fall: forall T k X,
  msfk T k (fall X) = fall (msfk T (S k) X).
Proof.
  induction T as [ | | | | | | | | T1 IHT1 m T2 IHT2 | T0 IHT0 ]; introv; simpl; eauto.
  destruct m; simpl; [ apply IHT1 | ].
  (* &= case: tsubst (fall X) k (liftn k (sf T2)) = fall (tsubst X (S k) (ftshift 0 (liftn k (sf T2)))) *)
  rewrite IHT1. reflexivity.
Qed.

(* ---- helper 4: vars strictly below the kept-depth k are untouched ---- *)
Lemma msfk_below: forall T k j, j < k -> msfk T k (ftvar j) = ftvar j.
Proof.
  induction T as [ | | | | | | | | T1 IHT1 m T2 IHT2 | T0 IHT0 ]; introv Hlt; simpl; eauto.
  - destruct m; simpl; [ apply IHT1; auto | ].
    (* &= : tsubst (ftvar j) k (liftn k (sf T2)) = ftvar j  since j<k *)
    destruct (lt_eq_lt_dec j k) as [[?|?]|?]; try lia.
    apply IHT1; auto.
Qed.

(* tsubst of a free var above the cutoff just decrements it. *)
Lemma tsubst_ftvar_gt: forall Y j C, j < Y -> tsubst (ftvar Y) j C = ftvar (Y - 1).
Proof.
  introv Hlt. cbn [tsubst]. destruct (lt_eq_lt_dec Y j) as [[?|?]|?]; try lia. reflexivity.
Qed.

(* ---- helper 5: THE variable lemma (POSITIONAL).  Replaces the old
   inner-based msfk_inner / msf_inner.  For a checkable position X, msfk
   resolves [ftvar X] to [ftvar (rank T X)], where [rank] counts the position
   after collapsing the manifest (&=) binders below the resolving &s. ---- *)
Fixpoint rank (T : typ) (X : nat) {struct T} : nat :=
  match T with
  | and T0 non _ => rank T0 X
  | and T0 rt _  => match X with 0 => 0 | S X' => rank T0 X' end
  | ands T0      => match X with 0 => 0 | S X' => S (rank T0 X') end
  | _            => X
  end.

(* depth-k generalization (mirrors the old msfk_inner, with rank T X in place
   of the inner index i). *)
Lemma msfk_check: forall T X, check T X ->
  forall k, msfk T k (ftvar (X + k)) = ftvar (rank T X + k).
Proof.
  introv Hck. induction Hck; introv.
  - (* check_evar: T & A, transparent *) simpl. apply IHHck.
  - (* check_eteq: (T &= A) at (S X); k cut, tsubst drops by 1 *)
    cbn [msfk rank]. rewrite tsubst_ftvar_gt by lia.
    replace (S X + k - 1) with (X + k) by lia. apply IHHck.
  - (* check_zero: (T &s) at 0: msfk T (S k) (ftvar (0+k)) = ftvar (0+k) *)
    simpl. rewrite msfk_below by lia. reflexivity.
  - (* check_etvar: (T &s) at (S X) *)
    cbn [msfk rank].
    replace (S X + k) with (X + S k) by lia.
    replace (S (rank T X) + k) with (rank T X + S k) by lia.
    apply IHHck.
Qed.

(* k=0 specialization *)
Lemma msf_check: forall T X, check T X -> msf T (ftvar X) = ftvar (rank T X).
Proof.
  introv Hck. unfold msf.
  forwards Heq: msfk_check Hck 0.
  rewrite !Nat.add_0_r in Heq. exact Heq.
Qed.

(* tsubst cancels a fresh shift at the same cutoff: identity. *)
Lemma tsubst_ftshift_same: forall Z n W, tsubst (ftshift n Z) n W = Z.
Proof.
  induction Z; introv.
  - cbn [ftshift]. destruct (le_gt_dec n0 n);
      cbn [tsubst];
      [ destruct (lt_eq_lt_dec (1+n) n0) as [[?|?]|?]
      | destruct (lt_eq_lt_dec n n0) as [[?|?]|?] ];
      try lia; try reflexivity; f_equal; lia.
  - reflexivity.
  - simpl. rewrite IHZ1. rewrite IHZ2. reflexivity.
  - simpl. rewrite IHZ. reflexivity.
Qed.

Lemma tsubst_ftshift0: forall Z W, tsubst (ftshift 0 Z) 0 W = Z.
Proof. intros. apply tsubst_ftshift_same. Qed.

(* shift below a substitution point: cutoff Z at-or-below subst point Y. *)
Lemma ftshift_tsubst_le: forall A Z Y A',
  Z <= Y ->
  ftshift Z (tsubst A Y A') = tsubst (ftshift Z A) (S Y) (ftshift Z A').
Proof.
  intros A. inductions A; introv Hle; try solve [simpl; f_equal; eauto].
  - cbn [tsubst ftshift].
    destruct (lt_eq_lt_dec n Y) as [[?|?]|?].
    + destruct (le_gt_dec Z n); cbn [ftshift tsubst].
      * destruct (lt_eq_lt_dec (1+n) (S Y)) as [[?|?]|?]; try lia. cbn [ftshift].
        destruct (le_gt_dec Z n); try lia. reflexivity.
      * destruct (lt_eq_lt_dec n (S Y)) as [[?|?]|?]; try lia. cbn [ftshift].
        destruct (le_gt_dec Z n); try lia. reflexivity.
    + subst. destruct (le_gt_dec Z Y); try lia. cbn [tsubst].
      destruct (lt_eq_lt_dec (1+Y) (S Y)) as [[?|?]|?]; try lia. reflexivity.
    + destruct (le_gt_dec Z n); cbn [tsubst];
        try (destruct (lt_eq_lt_dec (1+n) (S Y)) as [[?|?]|?]);
        try (destruct (lt_eq_lt_dec n (S Y)) as [[?|?]|?]);
        cbn [ftshift];
        repeat (match goal with |- context[le_gt_dec ?a ?b] => destruct (le_gt_dec a b) end);
        try lia; try reflexivity; f_equal; lia.
  - simpl. f_equal. rewrite IHA; try lia. f_equal.
    symmetry. apply ftshift_ftshift. lia.
Qed.

(* msfk commutes with a fresh shift at cutoff 0 when the depth is bumped. *)
Lemma msfk_ftshift0: forall T k C,
  msfk T (S k) (ftshift 0 C) = ftshift 0 (msfk T k C).
Proof.
  induction T as [ | | | | | | | | T1 IHT1 m T2 IHT2 | T0 IHT0 ]; introv; simpl; eauto.
  - destruct m; simpl; [ apply IHT1 | ].
    (* &= : tsubst (ftshift 0 C) (S k) (liftn (S k) (sf T2)) = ftshift 0 (tsubst C k (liftn k (sf T2))) *)
    rewrite <- IHT1. f_equal.
    change (ftshift 0 (liftn k (sf T2))) with (liftn (S k) (sf T2)).
    rewrite ftshift_tsubst_le by lia. reflexivity.
Qed.

(* ---- helper 6: lookt resolution (at the top level, k=0). ---- *)
Lemma msf_lookt: forall T X A, lookt T X A ->
  msf T (ftvar X) = msf T (sf A).
Proof.
  introv Hl. unfold msf. induction Hl.
  - (* lookt_evar: T & A0, transparent *)
    simpl. exact IHHl.
  - (* lookt_zero: (T &= A), X=0, looked = tshift 0 A *)
    simpl. rewrite sf_tshift. rewrite tsubst_ftshift0. reflexivity.
  - (* lookt_eteq: (T &= A), X = S X', looked = tshift 0 B *)
    simpl. rewrite sf_tshift. rewrite tsubst_ftshift0.
    replace (X - 0) with X by lia. exact IHHl.
  - (* lookt_etvar: (T &s), X = S X', looked = tshift 0 B *)
    simpl. rewrite sf_tshift.
    change (ftvar (S X)) with (ftshift 0 (ftvar X)).
    rewrite !msfk_ftshift0. f_equal. exact IHHl.
Qed.

(* a looked-up type in a bf_env is box_free. *)
Lemma bf_env_lookt: forall T X A, lookt T X A -> bf_env T -> box_free A.
Proof.
  introv Hl. induction Hl; introv He.
  - inverts He. eauto.
  - inverts He. apply box_free_tshift. assumption.
  - inverts He. apply box_free_tshift. eauto.
  - inverts He. apply box_free_tshift. eauto.
Qed.

(* msf-level corollaries (so the IHs, stated with msf, line up). *)
Lemma msf_fint: forall T, msf T fint = fint.
Proof. intros. apply msfk_fint. Qed.

Lemma msf_farr: forall T X Y, msf T (farr X Y) = farr (msf T X) (msf T Y).
Proof. intros. apply msfk_farr. Qed.

Lemma msf_fall: forall T X, msf T (fall X) = fall (msfk T 1 X).
Proof. intros. apply msfk_fall. Qed.

(* ==================================================================== *)
(*  Abstract-depth (number of &s binders) of an environment, and the     *)
(*  liftn lemmas needed for the SHIFT-AWARE kernel invariant.            *)
(* ==================================================================== *)

(* ad T = number of abstract (&s) binders in the env spine. *)

(* Difference descriptor: head = innermost (de-Bruijn 0) binder boundary.
   dval : (T1 & _ , T2 & _)   -- value binder, transparent to skeleton
   dabs : (T1 &s  , T2 &s)    -- both abstract (eq_all): a kept binder
   dmanil:(T1 &= A, T2 &s)    -- eq_manil: left substituted, right kept
   dmanir:(T1 &s  , T2 &= A)  -- eq_manir: left kept, right substituted   *)
Inductive dr : Set :=
  | dnil   : dr
  | dval   : dr -> dr
  | dabs   : dr -> dr
  | dmanil : dr -> dr
  | dmanir : dr -> dr.

(* The F-skeleton renaming induced by a descriptor, at kept-depth k.
   - dmanil: the RIGHT skeleton carries an extra binder at level k that the
     LEFT substituted away; drop it (tsubst _ k fint).
   - dmanir: the LEFT carries an extra binder the RIGHT substituted; insert
     it (ftshift k).
   - dabs: a binder kept on both sides; recurse one level deeper.            *)
Fixpoint applyrho (d : dr) (k : nat) (C : ftyp) : ftyp :=
  match d with
  | dnil      => C
  | dval d'   => applyrho d' k C
  | dabs d'   => applyrho d' (S k) C
  | dmanil d' => applyrho d' k (tsubst C k fint)
  | dmanir d' => ftshift k (applyrho d' k C)
  end.

(* applyrho fixes fint and distributes over farr / fall (depth-bumped). *)
Lemma applyrho_fint: forall d k, applyrho d k fint = fint.
Proof.
  induction d; introv; simpl; try (rewrite IHd); simpl; reflexivity.
Qed.

Lemma applyrho_farr: forall d k X Y,
  applyrho d k (farr X Y) = farr (applyrho d k X) (applyrho d k Y).
Proof.
  induction d; introv; simpl; try (rewrite IHd); simpl; reflexivity.
Qed.

Lemma applyrho_fall: forall d k X,
  applyrho d k (fall X) = fall (applyrho d (S k) X).
Proof.
  induction d; introv; simpl.
  - (* dnil *) reflexivity.
  - (* dval *) apply IHd.
  - (* dabs *) apply IHd.
  - (* dmanil *) cbn [tsubst]. rewrite IHd. simpl. reflexivity.
  - (* dmanir *) rewrite IHd. simpl. reflexivity.
Qed.

(* variables strictly below the kept-depth are untouched. *)
Lemma applyrho_below: forall d k j, j < k -> applyrho d k (ftvar j) = ftvar j.
Proof.
  induction d; introv Hlt; simpl; eauto.
  - (* dmanil *) cbn [tsubst]. destruct (lt_eq_lt_dec j k) as [[?|?]|?]; try lia.
    apply IHd; auto.
  - (* dmanir *) rewrite IHd by lia. cbn [ftshift].
    destruct (le_gt_dec k j); [ lia | reflexivity ].
Qed.

(* Over a genv env (only & and &s, no &=) every CONSUMED index is an &s, so
   a checkable position has rank = X (its own de-Bruijn index).  This is the
   reason the renaming is the identity at the genv BASE even when the two
   genvs have different binder KINDS: ranks agree (= X) on both sides. *)
Lemma genv_rank_id: forall T0 T1, genv T0 T1 -> forall X, check T1 X -> rank T1 X = X.
Proof.
  introv Hg. induction Hg; introv Hc.
  - inverts Hc.
  - cbn [rank]. inverts Hc. apply IHHg; auto.
  - inverts Hc.
    + cbn [rank]. reflexivity.
    + cbn [rank]. f_equal. apply IHHg; auto.
Qed.

(* The environment-PAIR relation threaded through the teq induction.  The
   BASE relates two arbitrary genv environments (possibly different fenvs,
   hence possibly mismatched binder KINDS -- the renaming is still the
   identity there by genv_rank_id).  The inductive constructors record the
   matched env-moves produced by eq_all / eq_manil / eq_manir; each rule
   changes BOTH envs in lockstep, so only the base can be cross-kind. *)
Inductive senv : dr -> typ -> typ -> Prop :=
  | s_base  : forall T0 T0' T1 T2,
      genv T0 T1 -> genv T0' T2 -> senv dnil T1 T2
  | s_abs   : forall d T1 T2,
      senv d T1 T2 -> senv (dabs d) (T1 &s) (T2 &s)
  | s_manil : forall d T1 T2 A,
      senv d T1 T2 -> senv (dmanil d) (T1 &= A) (T2 &s)
  | s_manir : forall d T1 T2 A,
      senv d T1 T2 -> senv (dmanir d) (T1 &s) (T2 &= A).

(* THE variable lemma: on co-checkable positions the renaming maps the
   right rank to the left rank. *)
Lemma applyrho_rank: forall d T1 T2, senv d T1 T2 ->
  forall X, check T1 X -> check T2 X ->
  forall k, applyrho d k (ftvar (rank T2 X + k)) = ftvar (rank T1 X + k).
Proof.
  induction 1; introv Hc1 Hc2; introv.
  - (* s_base: two genvs; rank = X on both sides *)
    simpl. rewrite (genv_rank_id _ _ H _ Hc1). rewrite (genv_rank_id _ _ H0 _ Hc2). reflexivity.
  - (* s_abs *) inverts Hc1.
    + (* check_zero, X=0 *) cbn [rank]. simpl. apply applyrho_below. lia.
    + (* check_etvar, X = S X0 *) inverts Hc2.
      cbn [rank]. simpl.
      replace (S (rank T2 X0 + k)) with (rank T2 X0 + S k) by lia.
      replace (S (rank T1 X0 + k)) with (rank T1 X0 + S k) by lia.
      apply IHsenv; auto.
  - (* s_manil: T1 &= A, T2 &s *) inverts Hc1. inverts Hc2.
    cbn [rank applyrho].
    rewrite tsubst_ftvar_gt by lia.
    replace (S (rank T2 X0) + k - 1) with (rank T2 X0 + k) by lia.
    apply IHsenv; auto.
  - (* s_manir: T1 &s, T2 &= A *) inverts Hc2. inverts Hc1.
    cbn [rank applyrho].
    rewrite IHsenv; auto. cbn [ftshift].
    destruct (le_gt_dec k (rank T1 X0 + k)); [ | lia ].
    f_equal; lia.
Qed.

(* GENERALISED INVARIANT. *)
Lemma teqsf_msf_gen: forall T1 A B T2, teq T1 A B T2 ->
  forall d, senv d T1 T2 ->
  bf_env T1 -> bf_env T2 -> box_free A -> box_free B ->
  msf T1 (sf A) = applyrho d 0 (msf T2 (sf B)).
Proof.
  introv Ht. induction Ht; introv Hs He1 He2 Ba Bb.
  - (* eq_int *) cbn [sf]. rewrite !msf_fint. rewrite applyrho_fint. reflexivity.
  - (* eq_tvar *) cbn [sf]. rewrite (msf_check _ _ H1). rewrite (msf_check _ _ H2).
    forwards Hr: applyrho_rank Hs H1 H2 0. rewrite !Nat.add_0_r in Hr. rewrite Hr. reflexivity.
  - (* eq_eql: lookt T1 X A *)
    cbn [sf]. rewrite (msf_lookt _ _ _ H).
    apply IHHt; auto. eapply bf_env_lookt; eauto.
  - (* eq_eqr *)
    cbn [sf]. rewrite (msf_lookt _ _ _ H).
    apply IHHt; auto. eapply bf_env_lookt; eauto.
  - (* eq_boxl *) inverts Ba.
  - (* eq_boxr *) inverts Bb.
  - (* eq_arr *)
    cbn [sf]. rewrite !msf_farr. rewrite applyrho_farr.
    inverts Ba. inverts Bb.
    rewrite (IHHt1 _ Hs He1 He2); auto. rewrite (IHHt2 _ Hs He1 He2); auto.
  - (* eq_all *)
    cbn [sf]. rewrite !msf_fall. rewrite applyrho_fall.
    inverts Ba. inverts Bb.
    f_equal. specialize (IHHt (dabs d) (s_abs _ _ _ Hs) (bfe_tvar _ He1) (bfe_tvar _ He2) H0 H1).
    unfold msf in IHHt. simpl in IHHt. exact IHHt.
  - (* eq_manil: T1 (mani A B) C T2; premise (T1&=A) B (tshift 0 C) (T2&s) *)
    inverts Ba.
    rewrite sf_mani_unfold. rewrite <- msf_eq_unfold.
    assert (IH: msf (T1 &= A) (sf B) = applyrho (dmanil d) 0 (msf (T2 &s) (sf (tshift 0 C)))).
    { apply (IHHt (dmanil d)).
      - apply s_manil; auto.
      - apply bfe_teq; auto.
      - apply bfe_tvar; auto.
      - auto.
      - apply box_free_tshift; auto. }
    rewrite IH.
    (* RHS: applyrho (dmanil d) 0 (msf (T2&s) (sf (tshift 0 C)))
            = applyrho d 0 (tsubst (msf(T2&s)(sf(tshift 0 C))) 0 fint) *)
    cbn [applyrho]. f_equal.
    unfold msf. cbn [msfk]. rewrite sf_tshift. rewrite msfk_ftshift0.
    rewrite tsubst_ftshift0. reflexivity.
  - (* eq_manir: T1 B (mani A C) T2; premise (T1&s) (tshift 0 B) C (T2&=A) *)
    inverts Bb.
    rewrite sf_mani_unfold. rewrite <- (msf_eq_unfold T2 A (sf C)).
    assert (IH: msf (T1 &s) (sf (tshift 0 B)) = applyrho (dmanir d) 0 (msf (T2 &= A) (sf C))).
    { apply (IHHt (dmanir d)).
      - apply s_manir; auto.
      - apply bfe_tvar; auto.
      - apply bfe_teq; auto.
      - apply box_free_tshift; auto.
      - auto. }
    (* IH : msf (T1&s) (sf (tshift 0 B)) = applyrho (dmanir d) 0 (msf (T2&=A) (sf C)) *)
    cbn [applyrho] in IH.
    assert (Hlhs: msf (T1 &s) (sf (tshift 0 B)) = ftshift 0 (msf T1 (sf B))).
    { unfold msf. cbn [msfk]. rewrite sf_tshift. rewrite msfk_ftshift0. reflexivity. }
    rewrite Hlhs in IH.
    (* ftshift 0 (msf T1 (sf B)) = ftshift 0 (applyrho d 0 (msf(T2&=A)(sf C))) *)
    apply (f_equal (fun Z => tsubst Z 0 fint)) in IH.
    rewrite !tsubst_ftshift0 in IH. exact IH.
  - (* eq_top *) cbn [sf]. rewrite !msf_fint. rewrite applyrho_fint. reflexivity.
  - (* eq_and *) cbn [sf]. rewrite !msf_fint. rewrite applyrho_fint. reflexivity.
  - (* eq_ands *) cbn [sf]. rewrite !msf_fint. rewrite applyrho_fint. reflexivity.
  - (* eq_rcd *) cbn [sf]. rewrite !msf_fint. rewrite applyrho_fint. reflexivity.
Qed.

(* ==================================================================== *)
(*  DERIVED KERNEL: over genv environments msf collapses to identity,    *)
(*  so the teq'd box-free types have equal System-F skeletons.           *)
(* ==================================================================== *)
Lemma teq_sf_eq_bf: forall T1 A B T2, teq T1 A B T2 ->
  forall T0 T0', genv T0 T1 -> genv T0' T2 ->
  box_free A -> box_free B -> sf A = sf B.
Proof.
  introv Ht Hg1 Hg2 Ba Bb.
  forwards Heq: teqsf_msf_gen Ht (s_base _ _ _ _ Hg1 Hg2).
  - eapply genv_bf_env; eauto.
  - eapply genv_bf_env; eauto.
  - assumption.
  - assumption.
  - (* applyrho dnil 0 _ = _ ; msf collapses both genvs to identity *)
    cbn [applyrho] in Heq.
    rewrite (msf_genv_id _ _ Hg1) in Heq.
    rewrite (msf_genv_id _ _ Hg2) in Heq.
    exact Heq.
Qed.



(* ==================================================================== *)
(*  BOX-FREE INTERFACE lemmas for implicit -> System-F conservativity.   *)
(*  box_free is reused from kernel.                                       *)
(* ==================================================================== *)

(* wft inversion helpers *)
Lemma wft_arr_inv2: forall T A B, wft T (arr A B) -> wft T A /\ wft T B.
Proof. introv H. unfold wft in *. inverts H. split; assumption. Qed.
Lemma wft_rcd_inv: forall T l A, wft T (rcd l A) -> wft T A.
Proof. introv H. unfold wft in *. inverts H. assumption. Qed.
Lemma wft_all_inv: forall T A, wft T (all A) -> wft (T &s) A.
Proof. introv H. unfold wft in *. inverts H. assumption. Qed.
Lemma wft_mani_inv: forall T A B, wft T (mani A B) -> wft (T &= A) B /\ wft T A.
Proof. introv H. unfold wft in *. inverts H. split; assumption. Qed.
Lemma wft_ands_inv: forall T A, wft T (A &s) -> wft T A /\ lshape A.
Proof. introv H. unfold wft in *. inverts H. split; assumption. Qed.
Lemma wft_and_inv: forall T A m B,
  wft T (and A m B) -> wft T A /\ wft (T +++ A) B /\ lshape A.
Proof. introv H. unfold wft in *. inverts H. splits; assumption. Qed.


(* ==================================================================== *)
(*  FULL ALIGNMENT.  Unlike `aligned`, this relation has NO depth cap:    *)
(*  the two frames share their ENTIRE abstract spine (matching &s and &   *)
(*  slots), differing only in the CONTENTS of &= manifest slots.  Hence   *)
(*  inner-correspondence holds for *every* checkable variable, including  *)
(*  non-rigid (abstract / existential) uses.  Used to thread the          *)
(*  diverging body frames in the mani/and/ands cases of bf_interface,     *)
(*  where the left frame carries the original type and the right frame    *)
(*  carries its box-free interface.                                       *)
Inductive falign : typ -> typ -> Prop :=
  | falign_top  : falign top top
  | falign_tvar : forall T3 Ta, falign T3 Ta -> falign (T3 &s) (Ta &s)
  | falign_evar : forall T3 Ta C D, falign T3 Ta ->
      wfe (T3 & C) -> wfe (Ta & D) -> falign (T3 & C) (Ta & D)
  | falign_eteq : forall T3 Ta C D, falign T3 Ta ->
      wfe (T3 &= C) -> wfe (Ta &= D) -> falign (T3 &= C) (Ta &= D).
#[local] Hint Constructors falign : core.

Lemma falign_wfe: forall T3 Ta, falign T3 Ta -> wfe T3 /\ wfe Ta.
Proof.
  introv H. inductions H.
  - split; econstructor.
  - destruct IHfalign. split; eapply we_tvar; eauto.
  - split; assumption.
  - split; assumption.
Qed.

Lemma falign_refl: forall T, wfe T -> falign T T.
Proof.
  induction T; introv Hw; try solve [inverts Hw].
  - econstructor.
  - destruct m.
    + eapply falign_evar; eauto. eapply IHT1. eapply wfe_inv; eauto.
    + eapply falign_eteq; eauto. eapply IHT1. eapply wft_wfe; unfold wft; eauto.
  - eapply falign_tvar. eapply IHT. eapply wfe_sinv; eauto.
Qed.

(* Check-correspondence for ALL checkable variables (positional, no depth cap):
   falign is symmetric, so it preserves checkable POSITIONS exactly. *)
Lemma falign_check: forall T3 Ta, falign T3 Ta -> forall X,
  check T3 X -> check Ta X.
Proof.
  introv Hf. inductions Hf; introv Hck.
  - inverts Hck.
  - inverts Hck.
    + econstructor.
    + econstructor. eauto.
  - inverts Hck. econstructor. eauto.
  - inverts Hck. econstructor. eauto.
Qed.

(* Extend a full alignment over a matching pair of lshape rows. *)
Lemma falign_mconcat: forall A BA T3 Ta,
  falign T3 Ta -> teq T3 A BA Ta -> lshape A -> lshape BA ->
  wfe (T3 +++ A) -> wfe (Ta +++ BA) ->
  falign (T3 +++ A) (Ta +++ BA).
Proof.
  induction A; introv Hf Hq HlA HlBA Hw3 Hwa; try solve [inverts HlA].
  - (* top *) inverts Hq; try solve [inverts HlBA]. simpl. assumption.
  - (* and A1 m A2 *)
    inverts HlA. inverts Hq; try solve [inverts HlBA].
    inverts HlBA.
    rename T4 into BA1. rename B into BA2.
    repeat rewrite <- (mcon_cons T3) in *.
    repeat rewrite <- (mcon_cons Ta) in *.
    forwards~ Hsub: IHA1 BA1 T3 Ta Hf.
      eapply wfe_inv; eauto. eapply wfe_inv; eauto.
    destruct m.
    + simpl. eapply falign_evar; eauto.
    + simpl. eapply falign_eteq; eauto.
  - (* ands *)
    inverts HlA. inverts Hq; try solve [inverts HlBA].
    inverts HlBA. rename T4 into BA0.
    repeat rewrite <- (mcon_cons_st T3) in *.
    repeat rewrite <- (mcon_cons_st Ta) in *.
    simpl. eapply falign_tvar.
    forwards~ Hsub: IHA BA0 T3 Ta Hf.
      eapply wfe_sinv; eauto. eapply wfe_sinv; eauto.
Qed.

(* ==================================================================== *)
(*  RIGID INTERFACE (restored): a RIGID type has a box-free interface     *)
(*  over ANY depth-aligned ambient.  Used by bf_interface_al_size's box   *)
(*  case (unpacking a box body over the unrelated ambient frame).  The    *)
(*  conclusion carries a SHIFT-IMAGE invariant: the interface B avoids    *)
(*  every position that is non-checkable on the left (manifest/&=) and     *)
(*  non-lookt-able on the right (abstract/&s) — i.e. the abstracted        *)
(*  manifest-padding slots — so B is in the image of tshift there.  This   *)
(*  is exactly what the positional eq_manil needs to un-shift in the mani  *)
(*  case (where it was previously stuck), proved intrinsically here via    *)
(*  rigidity (the depth-0 box body has no bare abstract uses).             *)
(* ==================================================================== *)

(* aligned: cross-frame relation tracking the d trailing shared &s binders. *)
Inductive aligned : nat -> typ -> typ -> Prop :=
  | al_zero : forall T3 Ta, wfe T3 -> wfe Ta -> aligned 0 T3 Ta
  | al_tvar : forall d T3 Ta, aligned d T3 Ta -> aligned (S d) (T3 &s) (Ta &s)
  | al_eteq : forall d T3 Ta A, aligned d T3 Ta -> wfe (T3 &= A) -> aligned (S d) (T3 &= A) (Ta &s)
  | al_evar2 : forall d T3 Ta C D, aligned d T3 Ta ->
      wfe (T3 & C) -> wfe (Ta & D) -> aligned d (T3 & C) (Ta & D)
  | al_eteq2 : forall d T3 Ta C D, aligned d T3 Ta ->
      wfe (T3 &= C) -> wfe (Ta &= D) -> aligned (S d) (T3 &= C) (Ta &= D).
#[local] Hint Constructors aligned : core.

Lemma aligned_wfe: forall d T3 Ta, aligned d T3 Ta -> wfe T3 /\ wfe Ta.
Proof.
  introv H. inductions H.
  - split; assumption.
  - destruct IHaligned. split; eapply we_tvar; eauto.
  - destruct IHaligned. split; [ assumption | eapply we_tvar; eauto ].
  - split; assumption.
  - split; assumption.
Qed.

Lemma aligned_check: forall d T3 Ta, aligned d T3 Ta -> forall X,
  X < d -> check T3 X -> check Ta X.
Proof.
  introv Hal. inductions Hal; introv Hlt Hck;
    try solve [ lia ];
    inverts Hck;
    try solve [ econstructor ];
    match goal with H: check ?T ?Z |- _ =>
      forwards~ Hca: IHHal Z; try lia end;
    econstructor; eauto.
Qed.

Lemma aligned_mconcat: forall A BA T3 Ta d,
  aligned d T3 Ta -> teq T3 A BA Ta -> lshape A -> lshape BA ->
  wfe (T3 +++ A) -> wfe (Ta +++ BA) ->
  aligned (d + keyLen A) (T3 +++ A) (Ta +++ BA).
Proof.
  induction A; introv Hal Hq HlA HlBA Hw3 Hwa; try solve [inverts HlA].
  - inverts Hq; try solve [inverts HlBA].
    simpl. rewrite Nat.add_0_r. assumption.
  - inverts HlA. inverts Hq; try solve [inverts HlBA].
    inverts HlBA.
    rename T4 into BA1. rename B into BA2.
    repeat rewrite <- (mcon_cons T3) in *.
    repeat rewrite <- (mcon_cons Ta) in *.
    forwards~ Hsub: IHA1 BA1 T3 Ta Hal.
      eapply wfe_inv; eauto. eapply wfe_inv; eauto.
    destruct m.
    + simpl. eapply al_evar2; eauto.
    + simpl. rewrite Nat.add_succ_r. eapply al_eteq2; eauto.
  - inverts HlA. inverts Hq; try solve [inverts HlBA].
    inverts HlBA. rename T4 into BA0.
    repeat rewrite <- (mcon_cons_st T3) in *.
    repeat rewrite <- (mcon_cons_st Ta) in *.
    forwards~ Hsub: IHA BA0 T3 Ta Hal.
      eapply wfe_sinv; eauto. eapply wfe_sinv; eauto.
    simpl. rewrite Nat.add_succ_r. eapply al_tvar; eauto.
Qed.

Lemma rigid_interface: forall d T3 A,
  rigid d T3 A -> wft T3 A -> forall Ta, aligned d T3 Ta ->
  exists B, box_free B /\ teq T3 A B Ta /\ (lshape A -> lshape B)
         /\ (forall k, ~ (check T3 k /\ k < d) ->
               (forall C, ~ lookt Ta k C) -> tnotin k B).
Proof.
  introv Hr. inductions Hr; introv Hwft Hal; forwards~ (Hwf3&Hwfa): aligned_wfe Hal.
  - (* int *) exists int. splits; [ econstructor | econstructor; eauto
      | intro Hs; inverts Hs | intros k _ _; exact I ].
  - (* top *) exists top. splits; [ econstructor | econstructor; eauto
      | auto | intros k _ _; exact I ].
  - (* bvar : check T3 X, X < d *)
    forwards~ Hca: aligned_check Hal H0 H.
    exists (tvar X). splits; [ econstructor | eapply eq_tvar; eauto
      | intro Hs; inverts Hs
      | intros k Hck _; simpl; intro Heq; subst k; apply Hck; split; assumption ].
  - (* cvar : lookt T3 X B0, recurse on B0 (same frame) *)
    forwards~ Hwb: lookt_wft Hwf3 H.
    forwards~ (B0&Hbf&Hq&Hls&Hinv): IHHr Hwb Ta.
    exists B0. splits; [ assumption | eapply eq_eql; eauto
      | intro Hs; inverts Hs | exact Hinv ].
  - (* arr *)
    forwards~ (Hwa&Hwb): wft_arr_inv2 Hwft.
    forwards~ (B1&Hb1&Hq1&_&Hi1): IHHr1 Hwa Ta.
    forwards~ (B2&Hb2&Hq2&_&Hi2): IHHr2 Hwb Ta.
    exists (arr B1 B2). splits; [ econstructor; eauto | eapply eq_arr; eauto
      | intro Hs; inverts Hs
      | intros k Hck Hlk; simpl; split; [ eapply Hi1 | eapply Hi2 ]; eauto ].
  - (* rcd *)
    forwards~ Hwa: wft_rcd_inv Hwft.
    forwards~ (B0&Hb0&Hq0&_&Hinv): IHHr Hwa Ta.
    exists (rcd l B0). splits; [ econstructor; eauto | eapply eq_rcd; eauto
      | intro Hs; inverts Hs
      | intros k Hck Hlk; simpl; eapply Hinv; eauto ].
  - (* mani A0 B0 : recurse body over al_eteq (T3&=A0, Ta&s), unshift via tnotin *)
    forwards~ (Hwb&Hwa): wft_mani_inv Hwft.
    forwards~ (B0&Hbf0&Hq0&_&Hinv0): IHHr Hwb (al_eteq _ _ _ A Hal Hwa).
    (* slot 0: avoid + unshift *)
    forwards Ht0: Hinv0 0;
      [ intro Hcontra; destruct Hcontra as [Hc _]; inverts Hc
      | intros C0 Hlk; inverts Hlk | ].
    forwards (C&Heq): tnotin_image Ht0.
    exists C. splits.
    + eapply box_free_tshift_rev with (n := 0). rewrite <- Heq. exact Hbf0.
    + eapply eq_manil. rewrite <- Heq. exact Hq0.
    + intro Hs; inverts Hs.
    + intros k Hck Hlk.
      forwards HtSk: Hinv0 (S k).
      * intro Hcontra. destruct Hcontra as [Hc Hlt]. apply Hck.
        inverts Hc as Hc. split; [ exact Hc | lia ].
      * intros C0 Hlk0. inverts Hlk0 as Hlk0. apply (Hlk _ Hlk0).
      * rewrite Heq in HtSk. eapply tnotin_tshift_S with (j := 0); [ lia | exact HtSk ].
  - (* and A0 m B0 : head over (T3,Ta); tail over the +++-extended frames *)
    forwards~ (HwA&HwB&HlA): wft_and_inv Hwft.
    forwards~ (BA&HbfA&HqA&HlsA&HinvA): IHHr1 HwA Ta.
    forwards~ HlsBA: HlsA.
    forwards~ Hwfa3: wft_wfe HwB.
    forwards~ HwtaBA: teq_wft_right HqA.
    forwards~ HwfaBA: wfe_to_mcon_all HwtaBA.
    pose proof (aligned_mconcat _ _ _ _ _ Hal HqA HlA HlsBA Hwfa3 HwfaBA) as HalE.
    forwards~ (BB&HbfB&HqB&_&HinvB): IHHr2 HwB HalE.
    assert (HkL: keyLen A = keyLen BA)
      by (eapply teq_lshape_keyLen; [ exact HqA | exact HlA | exact HlsBA ]).
    exists (and BA m BB). splits.
    + econstructor; eauto.
    + eapply eq_and; eauto.
    + intro Hs. econstructor; eauto.
    + intros k Hck Hlk. simpl. split.
      * eapply HinvA; eauto.
      * eapply HinvB.
        -- intro Hcontra. destruct Hcontra as [Hc Hlt]. apply Hck.
           rewrite <- HkL in Hc. forwards Hc': check_under_rev HlA Hc.
           split; [ exact Hc' | rewrite <- HkL in Hlt; lia ].
        -- intros C0 Hlk0. forwards (C1&Hl1): lookt_under_rev HlsBA Hlk0.
           apply (Hlk _ Hl1).
  - (* ands : recurse body, same frame/depth *)
    forwards~ (Hwa&Hlsa): wft_ands_inv Hwft.
    forwards~ (B0&Hbf0&Hq0&Hls&Hinv): IHHr Hwa Ta.
    exists (B0 &s). splits; [ econstructor; eauto | eapply eq_ands; eauto
      | intro Hs; econstructor; eauto
      | intros k Hck Hlk; simpl; eapply Hinv; eauto ].
  - (* all : recurse body over (T3&s, Ta&s) at depth S d *)
    forwards~ Hwa: wft_all_inv Hwft.
    forwards~ (B0&Hbf0&Hq0&_&Hinv0): IHHr Hwa (Ta &s) (al_tvar _ _ _ Hal).
    exists (all B0). splits.
    + econstructor; eauto.
    + eapply eq_all; eauto.
    + intro Hs; inverts Hs.
    + intros k Hck Hlk. simpl. eapply Hinv0.
      * intro Hcontra. destruct Hcontra as [Hc Hlt]. apply Hck.
        inverts Hc as Hc. split; [ exact Hc | lia ].
      * intros C0 Hlk0. inverts Hlk0 as Hlk0. apply (Hlk _ Hlk0).
  - (* nested box : interface the body over a FRESH aligned 0 frame *)
    forwards~ (Hwb&Hwe&Hwe3): boxt_wft_inv Hwft.
    forwards~ (B0&Hbf0&Hq0&_&Hinv0): IHHr Hwb (@al_zero T3 Ta Hwe3 Hwfa).
    exists B0. splits.
    + assumption.
    + eapply eq_boxl; eauto.
    + intro Hs; inverts Hs.
    + intros k Hck Hlk. eapply Hinv0.
      * intro Hcontra. destruct Hcontra as [_ Hlt]. lia.
      * exact Hlk.
Qed.

(* Strengthened interface: any wft type has a box-free interface relating
   it to ANY fully-aligned frame Ta.  The non-rigid tvar case is handled
   because falign_inner gives inner-correspondence for all checkable vars.
   Size-indexed (bindings measure) so the concrete-variable (lookt) case
   may recurse on the looked-up type (smaller bindings, cf. teq_refl_size). *)
Lemma bf_interface_al_size: forall n A T3,
  bindings T3 A <= n ->
  wft T3 A -> forall Ta, falign T3 Ta ->
  exists B, box_free B /\ teq T3 A B Ta /\ (lshape A -> lshape B).
Proof.
  intros n. inductions n; introv Hl Hwft Hf;
    [ forwards~: bindings_min A T3; lia | ];
    forwards~ (Hwf3&Hwfa): falign_wfe Hf.
  destruct A.
  - (* int *) exists int. splits. econstructor. econstructor; eauto. intro Hs; inverts Hs.
  - (* tvar : positional check (eq_tvar, same index) or concrete (eq_eql) *)
    unfold wft in Hwft. inverts Hwft.
    + match goal with Hck: check T3 ?X |- _ =>
        forwards~ Hca: falign_check Hf Hck; exists (tvar X) end.
      splits. econstructor. eapply eq_tvar; eauto. intro Hs; inverts Hs.
    + match goal with Hg: lookt T3 ?X ?B0 |- _ =>
        forwards~ Hwb: lookt_wft Hwf3 Hg;
        forwards~ Hdec: var_decr Hwf3 Hg;
        forwards~ (B&Hbf&Hq&_): IHn B0 T3 Hwb Hf; [lia|] end.
      exists B. splits. assumption. eapply eq_eql; eauto. intro Hs; inverts Hs.
  - (* arr *)
    forwards~ (Hw1&Hw2): wft_arr_inv2 Hwft.
    forwards~ (B1&Hb1&Hq1&_): IHn A1 T3 Hw1 Hf. solve_size.
    forwards~ (B2&Hb2&Hq2&_): IHn A2 T3 Hw2 Hf. solve_size.
    exists (arr B1 B2). splits. econstructor; eauto. eapply eq_arr; eauto. intro Hs; inverts Hs.
  - (* all *)
    forwards~ Hw: wft_all_inv Hwft.
    forwards~ (B0&Hb0&Hq0&_): IHn A (T3 &s) Hw (Ta &s) (falign_tvar _ _ Hf). solve_size.
    exists (all B0). splits. econstructor; eauto. eapply eq_all; eauto. intro Hs; inverts Hs.
  - (* boxt A1 A2 : unpack via eq_boxl; the rigid body interface comes from
       rigid_interface over a fresh (aligned 0) frame (A1 unrelated to Ta). *)
    forwards~ (Hwb&Hwe&Hwe3): boxt_wft_inv Hwft.
    forwards~ Hrig: wft_box_rigid Hwft.
    forwards~ (B0&Hbf0&Hq0&_&_): rigid_interface Hrig Hwb (@al_zero A1 Ta Hwe3 Hwfa).
    exists B0. splits. assumption. eapply eq_boxl; eauto. intro Hs; inverts Hs.
  - (* mani A1 A2 : head + body interfaces, assembled positionally via
       eq_manil; eq_manir; teq_exch_s_neq (the non-reflexive binder exchange). *)
    forwards~ (Hwb&Hwa): wft_mani_inv Hwft.
    forwards~ (B1&Hb1&Hq1&_): IHn A1 T3 Hwa Hf. solve_size.
    assert (HwfaB1: wft Ta B1) by (eapply teq_wft_right; eauto).
    assert (Hf2: falign (T3 &= A1) (Ta &= B1)) by (eapply falign_eteq; eauto).
    forwards~ (B2&Hb2&Hq2&_): IHn A2 (T3 &= A1) Hwb Hf2. solve_size.
    exists (mani B1 B2). splits.
    + econstructor; eauto.
    + eapply eq_manil. eapply eq_manir. eapply teq_exch_s_neq; [exact Hq2 | exact Hwa | exact HwfaB1].
    + intro Hs; inverts Hs.
  - (* rcd *)
    forwards~ Hw: wft_rcd_inv Hwft.
    forwards~ (B0&Hb0&Hq0&_): IHn A T3 Hw Hf. solve_size.
    exists (rcd s B0). splits. econstructor; eauto. eapply eq_rcd; eauto. intro Hs; inverts Hs.
  - (* top *) exists top. splits. econstructor. econstructor; eauto. auto.
  - (* and A1 m A2 : head -> BA, tail over the +++-extended falign frames *)
    forwards~ (HwA&HwB&HlA): wft_and_inv Hwft.
    assert (Hsz1: bindings T3 A1 <= n) by (destruct m; solve_size).
    forwards~ (BA&HbfA&HqA&HlsA): IHn A1 T3 Hsz1 HwA Hf.
    forwards~ HlsBA: HlsA.
    forwards~ Hwfa3: wft_wfe HwB.
    forwards~ HwtaBA: teq_wft_right HqA.
    forwards~ HwfaBA: wfe_to_mcon_all HwtaBA.
    pose proof (falign_mconcat _ _ _ _ Hf HqA HlA HlsBA Hwfa3 HwfaBA) as HfE.
    assert (Hsz2: bindings (T3 +++ A1) A2 <= n).
    { destruct m; unfold bindings in *;
        [ rewrite weight_evar in Hl | rewrite weight_eteq in Hl ];
        rewrite <- mkb_eq; lia. }
    forwards~ (BB&HbfB&HqB&HlsB): IHn A2 (T3 +++ A1) HwB HfE.
    exists (and BA m BB). splits.
    + econstructor; eauto.
    + eapply eq_and; eauto.
    + intro Hs. econstructor; eauto.
  - (* ands *)
    forwards~ (Hwa2&Hlsa): wft_ands_inv Hwft.
    forwards~ (B0&Hbf0&Hq0&Hls): IHn A T3 Hwa2 Hf. solve_size.
    exists (B0 &s). splits. econstructor; eauto. eapply eq_ands; eauto. intro Hs; econstructor; eauto.
Qed.

Lemma bf_interface_al: forall A T3, wft T3 A -> forall Ta, falign T3 Ta ->
  exists B, box_free B /\ teq T3 A B Ta /\ (lshape A -> lshape B).
Proof.
  intros. eapply bf_interface_al_size; eauto.
Qed.

Lemma bf_interface: forall A T, wft T A -> exists B, box_free B /\ teq T A B T.
Proof.
  introv Hwft. forwards~ Hwf: wft_wfe Hwft.
  forwards~ (B&Hb&Hq&_): bf_interface_al Hwft (falign_refl _ Hwf).
  exists B. split; assumption.
Qed.

(* ==================================================================== *)
(*  Needs Set Implicit Arguments.                                        *)
(* ==================================================================== *)
Set Implicit Arguments.


(* ====================================================================
   Box-free reachability: close the implicit->System-F static conserve
   using the proven kernel `teq_sf_eq_bf` and the proven `bf_interface`.

   Architecture: a BOX-FREE-GUARDED induction.  The guard `teq T A B T`
   with `box_free B` makes:
     - t_eq FREE (compose the coercion into the guard, teq_trans);
     - the leaves (t_int / t_var) close via the kernel teq_sf_eq_bf;
     - the structural cases build a typing at a box-free INTERFACE
       (bf_interface) then kernel-rewrite to the guard target.
   ==================================================================== *)

Inductive bfgenv : fenv -> typ -> Prop :=
  | bge_nil : bfgenv [] top
  | bge_evar : forall A T T1,
      bfgenv T T1 -> wft T1 A -> box_free A ->
      bfgenv (fevar (sf A) :: T) (T1 & A)
  | bge_tvar : forall T T1,
      bfgenv T T1 -> bfgenv (fetvar :: T) (T1 &s).
#[export] Hint Constructors bfgenv : core.

Lemma bfgenv_genv: forall T0 T1, bfgenv T0 T1 -> genv T0 T1.
Proof. introv H. inductions H; eauto. Qed.

(* looked-up types in a bfgenv are box_free *)
Lemma bfgenv_getvar_bf: forall T0 T1, bfgenv T0 T1 -> forall n A,
  get_var T1 n A -> box_free A.
Proof.
  introv Hg. inductions Hg; introv Hv; try solve [inverts Hv].
  - inverts Hv; eauto.
  - inverts Hv. apply box_free_tshift. eauto.
Qed.

Lemma trans_t_box_free: forall Asf A, trans_t Asf A -> box_free A.
Proof. introv H. inductions H; eauto. Qed.

Lemma trans_env_bfgenv: forall T0 T1, trans_env T0 T1 -> wfe T1 -> bfgenv T0 T1.
Proof.
  introv Ht. inductions Ht; introv Hw.
  - eauto.
  - forwards~ Hwi: wfe_inv Hw. forwards~ Hee: wfe_evar_eteq Hw.
    forwards~: sf_tt H. subst. eapply bge_evar; eauto.
    eapply trans_t_box_free; eauto.
  - forwards~: wfe_sinv Hw.
Qed.

(* ==================================================================== *)
(*  STEP 1: binder narrowing (re-type term-binders to teq-equal types).  *)
(* ==================================================================== *)

Inductive eqv_env : typ -> typ -> Prop :=
  | ev_top : eqv_env top top
  | ev_evar : forall T1 T2 A B, eqv_env T1 T2 -> eqv_env (T1 & A) (T2 & B)
  | ev_etvar : forall T1 T2, eqv_env T1 T2 -> eqv_env (T1 &s) (T2 &s)
  | ev_eteq : forall T1 T2 A, eqv_env T1 T2 -> eqv_env (T1 &= A) (T2 &= A).
#[export] Hint Constructors eqv_env : core.

Lemma eqv_refl: forall T, lshape T -> eqv_env T T.
Proof. introv Hl. inductions Hl; eauto. destruct* m. Qed.

Lemma eqv_check: forall T1 T2, eqv_env T1 T2 -> forall X, check T1 X -> check T2 X.
Proof. introv H. inductions H; introv Hc; try solve [inverts* Hc]; eauto. Qed.

Lemma eqv_lookt: forall T1 T2, eqv_env T1 T2 -> forall X A, lookt T1 X A -> lookt T2 X A.
Proof. introv H. inductions H; introv Hl; try solve [inverts* Hl]; eauto. Qed.

Lemma eqv_mconcat: forall T3 T1 T2,
  eqv_env T1 T2 ->
  eqv_env (T1 +++ T3) (T2 +++ T3).
Proof.
  inductions T3; introv H; simpl; eauto; try destruct m.
  - destruct T3_1; simpl; econstructor; eauto.
  - destruct T3_1; simpl; econstructor; eauto.
  - destruct T3; simpl; econstructor; eauto.
Qed.

Lemma eqv_wfe_gen: forall S,
  wfe S -> forall T A T',
  S = (T &= A) ->
  eqv_env T T' ->
  wfe T' ->
  wfe (T' &= A).
Proof.
  introv Hw. inductions Hw; introv He Hev Hwt; try solve [inverts He];
  inverts He;
  try solve [ econstructor; eauto using eqv_check, eqv_lookt
            | eapply we_get; eauto using eqv_lookt
            | eapply we_all; eauto; eapply IHHw2; eauto
            | eapply we_mani; eauto; [eapply IHHw1; eauto | eapply IHHw2; eauto]
            | eapply we_ands; eauto; eapply IHHw; eauto ].
  assert (Hw1': wfe (T' &= T1)) by (eapply IHHw1 with (T:=T0); eauto).
  eapply we_and; eauto.
  eapply IHHw2 with (T := T0 +++ T1); eauto.
  eapply eqv_mconcat; eauto.
  eapply wfe_to_mcon_all; eauto.
Qed.

Lemma eqv_wft: forall T A T',
  wft T A -> eqv_env T T' -> wfe T' -> wft T' A.
Proof. introv Hw He Hwt. unfold wft in *. eapply (eqv_wfe_gen Hw eq_refl He Hwt). Qed.

Lemma eqv_teq: forall T1 A B T2,
  teq T1 A B T2 -> forall T1' T2',
  eqv_env T1 T1' -> eqv_env T2 T2' ->
  wfe T1' -> wfe T2' ->
  teq T1' A B T2'.
Proof.
  introv Ht. inductions Ht; introv He1 He2 Hw1 Hw2;
  try solve [econstructor; eauto using eqv_check, eqv_lookt].
  - eapply eq_boxl.
    eapply IHHt; eauto. eapply eqv_refl. eapply wfe_lshape.
    forwards~ Hw3: teq_wfe_left Ht. eauto.
    forwards~ Hw3: teq_wfe_left Ht.
    eapply eqv_wft; eauto.
  - eapply eq_boxr.
    eapply IHHt; eauto. eapply eqv_refl. eapply wfe_lshape.
    forwards~ Hw3: teq_wfe_right Ht. eauto.
    forwards~ Hw3: teq_wfe_right Ht.
    eapply eqv_wft; eauto.
  - eapply eq_all. eapply IHHt; eauto.
  - eapply eq_manil. eapply IHHt; eauto.
    forwards~ Hwt: teq_wfe_left Ht. eapply eqv_wfe_gen; eauto.
  - eapply eq_manir. eapply IHHt; eauto.
    forwards~ Hwt: teq_wfe_right Ht. eapply eqv_wfe_gen; eauto.
  - forwards~ Hq1: IHHt1 He1 He2 Hw1 Hw2.
    eapply eq_and; eauto.
    eapply IHHt2; eauto using eqv_mconcat.
    eapply wfe_to_mcon_all. eapply teq_wft_left; eauto.
    eapply wfe_to_mcon_all. eapply teq_wft_right; eauto.
Qed.

Inductive conv_env : typ -> typ -> Prop :=
  | cv_top : conv_env top top
  | cv_evar : forall T1 T2 A B,
      conv_env T1 T2 -> teq T2 B A T2 -> wft T2 A -> wft T2 B ->
      conv_env (T1 & A) (T2 & B)
  | cv_etvar : forall T1 T2, conv_env T1 T2 -> conv_env (T1 &s) (T2 &s)
  | cv_eteq : forall T1 T2 A, conv_env T1 T2 -> wft T2 A -> conv_env (T1 &= A) (T2 &= A).
#[export] Hint Constructors conv_env : core.

Lemma conv_eqv: forall T1 T2, conv_env T1 T2 -> eqv_env T1 T2.
Proof. introv H. inductions H; eauto. Qed.

(* reflexivity of conv_env on well-formed envs: each evar slot carries
   the trivial self-teq. *)
Lemma conv_refl: forall T, wfe T -> conv_env T T.
Proof.
  assert (bind_wft: forall T m A, wfe (and T m A) -> wft T A).
  { introv Hw. unfold wft. destruct m; eauto using wfe_evar_eteq. }
  introv Hw. inductions T; eauto;
    try solve [false; inverts Hw].
  - forwards~ HwT1: wfe_inv Hw.
    forwards~ HwftBind: bind_wft Hw.
    destruct m.
    + eapply cv_evar; eauto. eapply teq_refl; eauto.
    + eapply cv_eteq; eauto.
  - inverts Hw. eapply cv_etvar; eauto.
Qed.

Lemma teq_st_both: forall T X Y,
  teq T X Y T -> wfe (T &s) ->
  teq (T &s) (tshift 0 X) (tshift 0 Y) (T &s).
Proof.
  introv Ht Hw.
  eapply shift_tvar_both with (T1:=T)(T2:=T); [ exact Ht | econstructor | exact Hw | exact Hw ].
Qed.

Lemma teq_eteq_both: forall T A X Y,
  teq T X Y T -> wfe (T &= A) ->
  teq (T &= A) (tshift 0 X) (tshift 0 Y) (T &= A).
Proof.
  introv Ht Hw.
  forwards Hwt: wft_wfe Hw.
  (* insert a fresh abstract binder on BOTH sides, then turn the matched &s
     into the manifest &= A on both sides via inst_teq (the missing-link that
     the positional design needs in place of two one-sided shifts). *)
  forwards Hs: shift_tvar_both Ht (ib_here2 T T) (we_tvar Hwt) (we_tvar Hwt).
  eapply inst_teq; [ exact Hs | eapply teq_refl; exact Hw ].
Qed.

Lemma conv_getvar: forall T1 T2,
  conv_env T1 T2 -> forall n A,
  get_var T1 n A ->
  exists B, get_var T2 n B /\ teq T2 B A T2.
Proof.
  introv Hc. inductions Hc; introv Hg; try solve [inverts Hg].
  - inverts Hg.
    + exists B. split. econstructor.
      eapply adde_teq_l; eauto. eapply adde_teq_r; eauto.
    + match goal with H: get_var T1 _ _ |- _ => forwards~ (B0&?&?): IHHc H end.
      exists B0. split. econstructor; eauto.
      eapply adde_teq_l; eauto. eapply adde_teq_r; eauto.
  - inverts Hg.
    match goal with H: get_var T1 _ _ |- _ => forwards~ (B0&?&?): IHHc H end.
    exists (tshift 0 B0). split. econstructor; eauto.
    eapply teq_st_both; eauto.
    match goal with H: teq T2 B0 _ T2 |- _ => forwards~ Hwf: teq_wfe_left H end.
  - inverts Hg.
    match goal with H: get_var T1 _ _ |- _ => forwards~ (B0&?&?): IHHc H end.
    exists (tshift 0 B0). split. econstructor; eauto.
    eapply teq_eteq_both; eauto.
Qed.

Lemma conv_wfe_r: forall T1 T2, conv_env T1 T2 -> wfe T2.
Proof. introv H. inductions H; eauto. eapply wfe_eteq_evar; eauto. Qed.

Inductive is_te : exp -> Prop :=
  | ite_var: forall n, is_te (var n)
  | ite_lit: forall n, is_te (lit n)
  | ite_lam: forall e, is_te e -> is_te (lam e)
  | ite_app: forall e1 e2, is_te e1 -> is_te e2 -> is_te (app e1 e2).
#[export] Hint Constructors is_te : core.

(* ==================================================================== *)
(*  STEP 2: the box-free-guarded conservativity.                         *)
(*                                                                        *)
(*  The env is parameterised by a conv_env narrowing T1 ~> T2: the        *)
(*  induction stays on the ORIGINAL has_type derivation [Ht], while the   *)
(*  binder-narrowing needed for the lambda case is supplied through the   *)
(*  [conv_env] argument (so we never recurse on a re-typed derivation).   *)
(*  bfgenv T0 T2 stores box-free binder skeletons.                        *)
(* ==================================================================== *)
Lemma conserve_guard: forall T1 e A,
  has_type T1 e A -> forall T2,
  conv_env T1 T2 ->
  forall T0 t,
  bfgenv T0 T2 ->
  trans_e t e ->
  forall B, teq T2 A B T2 -> box_free B ->
  ftyping T0 t (sf B).
Proof.
  introv Ht. inductions Ht; introv Hc Hg Hte; introv Hq Hbf;
    try solve [inverts Hte].
  - (* t_int *)
    inverts Hte.
    forwards~ Heq: teq_sf_eq_bf Hq T0 T0 (bfgenv_genv Hg) (bfgenv_genv Hg).
    rewrite <- Heq. simpl. econstructor. eapply genv_fwfe. eapply bfgenv_genv; eauto.
  - (* t_var *)
    inverts Hte.
    forwards~ (A2 & Hgv & Hqv): conv_getvar Hc H0.
    forwards~ Hbfa: bfgenv_getvar_bf Hg Hgv.
    forwards~ HqA2: teq_trans Hqv Hq.
    forwards~ Heq: teq_sf_eq_bf HqA2 T0 T0 (bfgenv_genv Hg) (bfgenv_genv Hg).
    rewrite <- Heq. econstructor. eapply genv_fwfe. eapply bfgenv_genv; eauto.
    eapply genv_getvar. eapply bfgenv_genv; eauto. eauto.
  - (* t_lam *)
    inverts Hte.
    forwards~ Hwfe2: conv_wfe_r Hc.
    forwards~ Hwfe1: typ_wfe Ht. forwards~ HwftA1: wfe_evar_eteq Hwfe1.
    forwards~ HwftA2: eqv_wft HwftA1 (conv_eqv Hc) Hwfe2.
    forwards~ (A1 & Hb1 & Hq1): bf_interface A HwftA2.
    forwards~ HwftA1bf: teq_wft_right Hq1.
    assert (Hconv: conv_env (T & A) (T2 & A1)).
    { eapply cv_evar.
      - exact Hc.
      - eapply teq_sym; eauto.
      - exact HwftA2.
      - exact HwftA1bf. }
    forwards~ HwftBbody: typ_ans_wft Ht.
    assert (HwftB_eA1: wft (T2 & A1) B).
    { eapply eqv_wft. exact HwftBbody.
      eapply conv_eqv. exact Hconv.
      eapply wfe_eteq_evar. exact HwftA1bf. }
    assert (HwftB2: wft T2 B).
    { eapply del_evar_wft. eapply del_evar_devar. eapply del_evar_refl.
      exact HwftB_eA1. }
    forwards~ (B1 & Hb2 & Hq2): bf_interface B HwftB2.
    assert (Hq2L: teq (T2 & A1) B B1 (T2 & A1)).
    { eapply adde_teq_r. eapply adde_teq_l. exact Hq2. exact HwftA1bf. exact HwftA1bf. }
    forwards~ Hft: IHHt Hconv (bge_evar Hg HwftA1bf Hb1) H1 Hq2L Hb2.
    assert (HTabs: ftyping T0 (fabs t0) (farr (sf A1) (sf B1)))
      by (econstructor; eauto).
    assert (HqArr: teq T2 (arr A B) (arr A1 B1) T2) by (eapply eq_arr; eauto).
    forwards~ HqB0: teq_trans (teq_sym HqArr) Hq.
    assert (HbfArr: box_free (arr A1 B1)) by (econstructor; eauto).
    forwards~ Heq: teq_sf_eq_bf HqB0 T0 T0 (bfgenv_genv Hg) (bfgenv_genv Hg).
    simpl in Heq. rewrite <- Heq. exact HTabs.
  - (* t_app *)
    inverts Hte.
    forwards~ HwftAdom1: typ_ans_wft Ht2.
    forwards~ Hwfe2: conv_wfe_r Hc.
    forwards~ HwftAdom2: eqv_wft HwftAdom1 (conv_eqv Hc) Hwfe2.
    forwards~ (Adom1 & Hbd & Hqd): bf_interface A HwftAdom2.
    assert (HqArr: teq T2 (arr A B) (arr Adom1 B0) T2) by (eapply eq_arr; eauto).
    assert (HbfArr: box_free (arr Adom1 B0)) by (econstructor; eauto).
    forwards~ Hft1: IHHt1 Hc Hg H2 HqArr HbfArr.
    simpl in Hft1.
    forwards~ Hft2: IHHt2 Hc Hg H3 Hqd Hbd.
    econstructor; eauto.
  - (* t_gen *)
    forwards~ HwftA1: typ_ans_wft Ht.
    forwards~ Hwfe2: conv_wfe_r Hc.
    assert (Hconv: conv_env (T &s) (T2 &s)) by (eapply cv_etvar; eauto).
    forwards~ HwftA2: eqv_wft HwftA1 (conv_eqv Hconv) ltac:(eapply we_tvar; eauto).
    forwards~ (A1 & Hb1 & Hq1): bf_interface A HwftA2.
    forwards~ Hft: IHHt Hconv (bge_tvar Hg) Hte Hq1 Hb1.
    assert (HTabs: ftyping T0 t (fall (sf A1))) by (econstructor; eauto).
    assert (HqAll: teq T2 (all A) (all A1) T2) by (eapply eq_all; eauto).
    forwards~ HqB0: teq_trans (teq_sym HqAll) Hq.
    assert (HbfAll: box_free (all A1)) by (econstructor; eauto).
    forwards~ Heq: teq_sf_eq_bf HqB0 T0 T0 (bfgenv_genv Hg) (bfgenv_genv Hg).
    simpl in Heq. rewrite <- Heq. exact HTabs.
  - (* t_tapp : the mani is assembled positionally via eq_manil; eq_manir;
       teq_exch_s_neq (the non-reflexive binder exchange), replacing the index
       calculus's one-sided eq_manir; eq_manil. *)
    forwards~ Hwfe2: conv_wfe_r Hc.
    forwards~ HwftA2: eqv_wft H (conv_eqv Hc) Hwfe2.
    forwards~ (A'' & HbA & HqA): bf_interface A HwftA2.
    forwards~ HwftA''2: teq_wft_right HqA.
    forwards~ Hwftall1: typ_ans_wft Ht.
    forwards~ HwftBs1: wft_all_inv Hwftall1.
    assert (Hconvs: conv_env (T &s) (T2 &s)) by (eapply cv_etvar; eauto).
    forwards~ Hwfe2s: we_tvar Hwfe2.
    forwards~ HwftBs2: eqv_wft HwftBs1 (conv_eqv Hconvs) Hwfe2s.
    forwards~ (Bs & HbBs & HqBs): bf_interface B HwftBs2.
    assert (HqallBs: teq T2 (all B) (all Bs) T2) by (eapply eq_all; eauto).
    assert (HbfallBs: box_free (all Bs)) by (econstructor; eauto).
    forwards~ Hftbody: IHHt Hc Hg Hte HqallBs HbfallBs.
    simpl in Hftbody.
    assert (HfwftA'': fwft T0 (sf A'')).
    { eapply genv_sf_fwft. eapply bfgenv_genv; eauto. exact HwftA''2. }
    forwards~ HftTapp: T_Tapp Hftbody HfwftA''.
    assert (HqEteq: teq (T2 &= A) B Bs (T2 &= A'')).
    { eapply inst_teq; eauto. }
    assert (HqMani: teq T2 (mani A B) (mani A'' Bs) T2).
    { eapply eq_manil. eapply eq_manir.
      eapply teq_exch_s_neq; [ exact HqEteq | exact HwftA2 | exact HwftA''2 ]. }
    forwards~ HqM: teq_trans (teq_sym HqMani) Hq.
    assert (HbfMani: box_free (mani A'' Bs)) by (econstructor; eauto).
    forwards~ Heq: teq_sf_eq_bf HqM T0 T0 (bfgenv_genv Hg) (bfgenv_genv Hg).
    simpl in Heq.
    rewrite <- Heq. exact HftTapp.
  - (* t_eq *)
    forwards~ Hwfe2: conv_wfe_r Hc.
    forwards~ HqT2: eqv_teq H (conv_eqv Hc) (conv_eqv Hc) Hwfe2 Hwfe2.
    eapply IHHt; eauto. eapply teq_trans. exact HqT2. exact Hq.
  - (* t_mani *)
    forwards~ Hwft1: typ_ans_wft (t_mani Ht H H0).
    forwards~ Hwfe2: conv_wfe_r Hc.
    forwards~ Hwft2: eqv_wft Hwft1 (conv_eqv Hc) Hwfe2.
    forwards~ (M & HbM & HqM & HlsM): bf_interface_al Hwft2 (falign_refl _ (wft_wfe Hwft2)).
    assert (HlsConc: lshape (A &= B)) by (econstructor; eauto).
    forwards~ HlsMm: HlsM HlsConc.
    forwards~ HqMB: teq_trans (teq_sym HqM) Hq.
    forwards~ Heq: teq_sf_eq_bf HqMB T0 T0 (bfgenv_genv Hg) (bfgenv_genv Hg).
    forwards~ HsfM: lshape_sf_fint HlsMm.
    rewrite HsfM in Heq.
    rewrite <- Heq.
    forwards~ HwftA1: typ_ans_wft Ht.
    forwards~ HwftA2: eqv_wft HwftA1 (conv_eqv Hc) Hwfe2.
    forwards~ (MA & HbMA & HqMA & HlsMA): bf_interface_al HwftA2 (falign_refl _ (wft_wfe HwftA2)).
    forwards~ HlsMAm: HlsMA H.
    forwards~ HsfMA: lshape_sf_fint HlsMAm.
    forwards~ Hft: IHHt Hc Hg Hte HqMA HbMA.
    rewrite HsfMA in Hft. exact Hft.
Qed.

(* ==================================================================== *)
(*  STEP 3: HEADLINE static conservativity, via conserve_guard.          *)
(* ==================================================================== *)
Lemma conserve_new: forall T1 e A1,
  has_type T1 e A1 -> forall T t A,
  trans_env T T1 ->
  trans_e t e ->
  trans_t A A1 ->
  ftyping T t A.
Proof.
  introv Ht Hten Hte Htt.
  forwards~ Hwe: typ_wfe Ht.
  forwards~ Hg: trans_env_bfgenv Hten.
  forwards~ Hwft: typ_ans_wft Ht.
  forwards~ Hbf: trans_t_box_free Htt.
  forwards~ Hcr: conv_refl Hwe.
  forwards~ Hqr: teq_refl Hwft.
  assert (Hf: ftyping T t (sf A1)).
  { eapply conserve_guard. exact Ht. exact Hcr. exact Hg. exact Hte. exact Hqr. exact Hbf. }
  forwards~ Heq: sf_tt Htt. rewrite Heq in Hf. eauto.
Qed.
