Require Import LibTactics. 
From Stdlib Require Import Arith.
From Stdlib Require Import Lia. 
Require Import Stdlib.Lists.List. 
Require Import Stdlib.Classes.EquivDec. 
From Stdlib Require Import Strings.String.
Import ListNotations.
Require Export Teq ExpSyntax Semantics.
Set Implicit Arguments.

(* Rocq 9.1 compat *)
Definition beq_nat (n m : nat) : bool := Nat.eqb n m.

Inductive ftyp : Set :=
  | ftvar : nat -> ftyp
  | fint : ftyp
  | farr : ftyp -> ftyp -> ftyp
  | fall : ftyp -> ftyp.


Inductive term : Set :=
  | fvar : nat -> term
  | flit : nat -> term
  | fabs : term -> term
  | fapp : term -> term -> term
  | ftabs : term -> term
  | ftapp : term -> ftyp -> term.

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
      ftyping T (ftabs t) (fall A2)
  | T_Tapp : forall (T : fenv) (t1 : term) (A1 A2 : ftyp),
      ftyping T t1 (fall A1) ->
      fwft T A2 ->
      ftyping T (ftapp t1 A2) (tsubst A1 0 A2).

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

Lemma fgetv_etvar_inv: forall n T A,
  fget_var (fetvar :: T) n = Some A -> exists B,
  A = ftshift 0 B /\ fget_var T n = Some B.
Proof.
  intros n. inductions n; intros; eauto.
  - forwards~ [?|?]: fgetv_none_some T 0.
    + inverts H. rewrite H0 in H2. inverts H2. 
    + inverts H. inverts H0. rewrite H in H2. inverts H2.
      exists*.
  - forwards~ [?|?]: fgetv_none_some T (S n).
    + inverts H. rewrite H0 in H2. inverts H2.
    + inverts H. inverts H0. rewrite H in H2. inverts H2.
      exists*.
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


Lemma fadde_refl: forall T,
  fadde T T.
Proof.
  intros T. inductions T; eauto.
  destruct* a.
Qed.

Lemma check_fadde: forall T1 T2,
  fadde T1 T2 -> forall i,
  f_check T1 i = true ->
  f_check T2 i = true.
Proof.
  introv He. inductions He; introv Hc; try solve [simpl in *; eauto].
  - destruct* i.
Qed.

Lemma fadde_wfe: forall T1,
  fwfe T1 -> forall T2,
  fadde T1 T2 -> 
  fwfe T2.
Proof.
  introv Hw. inductions Hw; introv He; try solve [eauto];
  try solve [inverts* He].
  - inverts* He. econstructor; eauto. eapply check_fadde; eauto. 
  - inverts* He. econstructor; eauto.
  - inverts* He. econstructor; eauto.
Qed. 

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

Lemma finsert_wft: forall (A : ftyp) (X : nat) (T T' : fenv),
  finsert X T T' ->
  fwfe T' ->
  fwft T A -> 
  fwft T' (ftshift X A).
Proof.
  intros A. inductions A; introv Hi He Hw; unfold fwft in *; try solve [eauto].
  - simpl. inverts Hw. 
    destruct (le_gt_dec X n).
    + forwards~: check_finsert_ge Hi n.
      rewrite H2 in H. econstructor; eauto. 
    + forwards~: check_finsert_lt Hi n.
      rewrite H2 in H. econstructor; eauto. 
  - simpl. inverts Hw. eauto. 
  - simpl. inverts Hw. 
    forwards~: IHA (S X) (fetvar :: T) (fetvar :: T').
Qed.

Lemma fgetv_wft: forall T,
  fwfe T -> forall n A,
  fget_var T n = Some A ->
  fwft T A.
Proof.
  intros T. induction T; introv Hw Hl; eauto.
  - inverts* Hl.
  - destruct* a.
    + destruct* n.
      * inverts Hl. unfold fwft. 
        eapply fadde_wfe; eauto. econstructor; eauto.
        econstructor; eauto.
        eapply fadde_refl; eauto.
      * inverts Hl. forwards~: fwfe_inv Hw. 
        forwards~: IHT H H0.
        unfold fwft in *. 
        eapply fadde_wfe; eauto. econstructor; eauto.
        econstructor; eauto.
        eapply fadde_refl; eauto.
    + simpl. forwards~ (C&?&?): fgetv_etvar_inv Hl. subst.
      forwards~: fwfe_inv Hw.
      forwards~: IHT H H0.
      eapply finsert_wft; eauto.
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

Lemma wfe_eteq_evar2: forall T A,
  wfe2 (T &= A) ->
  wfe2 (T & A).
Proof.
  introv Hw. inductions Hw; eauto. 
Qed.

Lemma we_eq1: forall T,
  wfe T ->
  wfe2 T.
Proof.
  introv Hw. inductions Hw; eauto.
  - forwards~: wfe_eteq_evar2 IHHw1.
    forwards~: wfe_eteq_evar2 IHHw2.
  - forwards~: wfe_eteq_evar2 IHHw2.
Qed.

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


Inductive trans_e: term -> exp -> Prop :=
  | te_var: forall n, trans_e (fvar n) (var n)
  | te_lit: forall n, trans_e (flit n) (lit n)
  | te_abs: forall t e,
      trans_e t e ->
      trans_e (fabs t) (lam e)
  | te_app: forall t1 t2 e1 e2,
      trans_e t1 e1 ->
      trans_e t2 e2 ->
      trans_e (fapp t1 t2) (app e1 e2)
  | te_tabs: forall t e,
      trans_e t e ->
      trans_e (ftabs t) (blam e)
  | te_tapp: forall t e A A1,
      trans_e t e -> 
      trans_t A A1 ->
      trans_e (ftapp t A) (tapp e A1).

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

Inductive lb_in: string -> typ -> Prop :=
  | lbin_rcd: forall A l T, 
      lb_in l (T & (rcd l A))
  | lbin_andl: forall T A l,
      lb_in l T ->
      lb_in l (T & A)
  | lbin_tandl: forall T A l,
      lb_in l T ->
      lb_in l (T &= A).

Inductive mopen: typ -> typ -> typ -> Prop :=
  | mopen_base: forall A,
      mopen top A A
  | mopen_evar: forall T A B C,
      mopen T A B ->
      mopen (T & C) A B
  | mopen_eteq: forall T A B C,
      mopen T (mani C A) B ->
      mopen (T &= C) A B.

#[export]
Hint Constructors mopen : core.


Inductive rlk : typ -> string -> typ -> Prop :=
  | rlk_hit : forall l A B T1, 
      ~ lb_in l T1 ->
      mopen T1 A B ->
      rlk (T1 & (rcd l A)) l B
  | rlk_left : forall l A B T1 l1,
      rlk T1 l B ->
      ~ l = l1 ->
      rlk (T1 & (rcd l1 A)) l B
  | rlk_right : forall l T2 B C T1,
      ~ lb_in l T1 ->
      rlk T2 l B ->
      mopen T1 B C ->
      rlk (T1 & T2) l C
  | rlk_left_t : forall l A B T1,
      rlk T1 l B ->
      rlk (T1 &= A) l B.

Inductive get_var : typ -> nat -> typ -> Prop :=
  | get_var_etvar : forall T x A,
      get_var T x A ->
      get_var (T &s) x (tshift 0 A)
  | get_var_eteq : forall T x B A,
      get_var T x A ->
      get_var (T &= B) x (tshift 0 A)
  | get_var_zero : forall T A,
      get_var (T & A) 0 A
  | get_var_evar : forall T x A B,
      get_var T x A ->
      get_var (T & B) (S x) A.



#[export]
Hint Constructors lb_in rlk get_var: core.

Lemma tten_lookt: forall T0 T1,
  trans_env T0 T1 -> forall X A,
  lookt T1 X A ->
  False.
Proof.
  introv Ht. inductions Ht; introv Hl.
  - inverts Hl.
  - inverts* Hl.
  - inverts* Hl.
Qed.



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


Lemma check2f: forall T T1,
  trans_env T1 T -> forall i,
  check T i ->
  f_check T1 i = true.
Proof.
  introv Ht. inductions Ht; introv Hc.
  - inverts Hc.
  - inverts* Hc.
  - inverts* Hc.
Qed.

Lemma tenv_m: forall T0 T m A,
  trans_env T0 (and T m A) -> 
  m = non.
Proof.
  intros. inductions H; eauto.
Qed.

Lemma wfe2f_aux: forall T,
  wfe2 T -> forall T0,
  trans_env T0 T ->
  fwfe T0.
Proof.
  introv Hf. inductions Hf; introv Ht; try forwards~ Hm: tenv_m Ht; subst;
  try solve [eauto];
  try solve [inverts* Ht]. 
  - inverts Ht. inverts* H2.
  - inverts Ht. inverts* H3. forwards~: IHHf H4. econstructor; eauto. eapply check2f; eauto.
  - inverts Ht. inverts H3. exfalso. eapply tten_lookt; eauto.
  - inverts Ht. inverts H2. econstructor; eauto.
  - inverts Ht. inverts H2. econstructor; eauto.
  - inverts Ht. inverts H3.
    (* [trans_t] has no boxt case, so a box type never has a System-F translation:
       the [trans_t _ (boxt _ _)] hypothesis is vacuous. *)
    all: match goal with Hb: trans_t _ (boxt _ _) |- _ => inverts Hb end.
  - inverts Ht. inverts H2.
  - inverts Ht. inverts H2.
  - inverts Ht. inverts H3.
  - inverts Ht. inverts H3.
  - inverts Ht. inverts H2.
Qed.

Lemma wfe2f: forall T,
  wfe T -> forall T0,
  trans_env T0 T ->
  fwfe T0.
Proof. 
  intros. forwards~: we_eq1 H.
  eapply wfe2f_aux; eauto.
Qed.

Lemma wft2f: forall T A,
  wft T A -> forall T0,
  trans_env T0 T -> forall A0,
  trans_t A0 A ->
  fwft T0 A0.
Proof.
  intros. unfold wft in *. unfold fwft in *.
  forwards~: wfe_eteq_evar H.
  eapply wfe2f; eauto. 
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



(* Balanced positional check correspondence for ityp: positions strictly
   to the right of the inserted &= binder are unchanged. *)

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

(* Position [k] (the differing binder) is the abstract var on GR, and the
   manifest [&= A] on GL.  At GL the var [k] resolves (lookt) to A weakened
   over the whole frame above it = [kshift (S k) A]. *)
Lemma repl_bot_lookt_k : forall A k GL GR, repl_bot A k GL GR ->
  lookt GL k (kshift (S k) A).
Proof.
  introv H. inductions H; simpl.
  - eapply lookt_zero.
  - replace (tshift 0 (tshift 0 (kshift k A)))
      with (tshift 0 (kshift (S k) A)) by reflexivity.
    eapply lookt_etvar; eauto.
Qed.

(* tshift k absorbs into kshift (S k): every var of [kshift k A] is >= k, so
   the cutoff-[k] shift acts as a plain bottom shift. *)
Lemma tshift_k_kshift : forall A k,
  tshift k (kshift k A) = kshift (S k) A.
Proof.
  intros A k. revert A. inductions k; intros A; simpl; eauto.
  (* goal: tshift (S k) (tshift 0 (kshift k A)) = tshift 0 (tshift 0 (kshift k A)) *)
  forwards Hp: tshift_tshift_prop_1 (kshift k A) 0 k. simpl in Hp.
  (* Hp: tshift 0 (tshift k (kshift k A)) = tshift (S k) (tshift 0 (kshift k A)) *)
  rewrite <- Hp. rewrite IHk. reflexivity.
Qed.

(* check of GL/GR at positions OTHER than the differing bottom binder [k]
   coincide and are inherited from the underlying frame.  [check_repl_l]:
   from a check in GR (abstract everywhere) at [n <> k] we get the same check
   in GL.  [check_repl_r]: from check at [n] in the [k]-spine-extended base we
   get check in GR at the same shifted position. *)
Lemma repl_bot_check_r : forall A k GL GR, repl_bot A k GL GR ->
  forall n, n <> k -> check GR n -> check GL n.
Proof.
  introv H. inductions H; introv Hne Hc.
  - inverts Hc; try lia. econstructor; eauto.
  - inverts Hc.
    + econstructor.
    + econstructor. eapply IHrepl_bot; eauto.
Qed.

(* [tshift k _] never produces position [k]. *)

(* GR is fully abstract, so a var that is well-formed in GR satisfies [check]. *)
Lemma repl_bot_wft_check_r : forall A k GL GR, repl_bot A k GL GR ->
  forall n, wft GR (tvar n) -> check GR n.
Proof.
  introv Hrb Hw. unfold wft in Hw. inverts Hw; eauto.
  exfalso. (* lookt in a fully abstract context is impossible *)
  assert (Hall: forall (G : typ), repl_bot A k GL G -> forall m B, lookt G m B -> False).
  { clear. introv Hr. inductions Hr; introv Hl.
    - inverts Hl. eapply all_abs_lookt; eauto.
    - inverts Hl. eapply IHHr; eauto. }
  eapply Hall; eauto.
Qed.

(* Reflexivity across the asymmetric bottom binder, for any trans-image [M]
   whose relocation [tshift k M] is well-formed in the fully-abstract [GR].
   [tshift k] inserts the bottom binder at position [k]; [M]'s vars therefore
   never land AT position [k], so the manifest/abstract difference is
   invisible.  Induction on [trans_t M]. *)
Lemma refl_relocate : forall Mt M, trans_t Mt M -> forall A k GL GR,
  repl_bot A k GL GR ->
  wft GR (tshift k M) ->
  teq GL (tshift k M) (tshift k M) GR.
Proof.
  introv Ht. inductions Ht; introv Hrb HwM.
  - (* tvar *)
    forwards~ Hcr: repl_bot_wft_check_r Hrb HwM.
    eapply eq_tvar; eauto.
    eapply repl_bot_check_r; [ exact Hrb | | exact Hcr ].
    simpl in *. destruct (le_gt_dec k n); lia.
  - (* int *) simpl in *. eapply eq_int; eauto.
  - (* arr *) simpl in *.
    forwards~ (HwA&HwB): wft_arr_inv HwM.
    eapply eq_arr; eauto.
  - (* all *) simpl in *. unfold wft in HwM. inverts HwM.
    eapply eq_all.
    eapply IHHt with (A := A0) (k := S k) (GL := GL &s); eauto.
Qed.

(* kshift preserves trans-image shape *)
Lemma tt_kshift : forall A1 A2, trans_t A1 A2 -> forall k,
  exists B1, trans_t B1 (kshift k A2).
Proof.
  introv Ht. inductions k; simpl.
  - exists A1. eauto.
  - destruct IHk as (B1 & HB). exists (ftshift 0 B1). eapply tt_tshift; eauto.
Qed.

(* kshift (S k) A is wft in GR (A weakened over the whole inserted frame). *)
Lemma repl_bot_wft_kshift : forall A k GL GR, repl_bot A k GL GR ->
  wft GR (kshift (S k) A).
Proof.
  introv H. inductions H; simpl.
  - (* T &s , kshift 1 A = tshift 0 A *)
    eapply insert_tvar_wft; [ eapply itv_here2 | eapply we_tvar; eapply wft_wfe; eauto | eauto ].
  - (* (GR &s) , kshift (S (S k)) A = tshift 0 (kshift (S k) A) *)
    eapply insert_tvar_wft; [ eapply itv_here2
      | eapply we_tvar; eapply wft_wfe; eauto | eauto ].
Qed.

(* check of a base position in GR (fully abstract): a var well-formed in GR
   resolves by [check]. *)
Lemma repl_bot_wft_check_gr : forall A k GL GR, repl_bot A k GL GR ->
  forall n, wft GR (tvar n) -> check GR n.
Proof.
  intros. eapply repl_bot_wft_check_r; eauto.
Qed.

(* BALANCED "fold the manifest into the substitution".  In the asymmetric
   context [GL = ... &= A ...] / [GR = ... &s ...] (repl_bot), the trans-image
   [D] (read on the LEFT against the manifest binder) equals its key-[k]
   substitution [tshift k (tsubst2 D k (kshift k A))] (read on the abstract
   RIGHT).  Induction on [trans_t D]. *)
Lemma subst_fold_gen : forall Dt D, trans_t Dt D -> forall At A k GL GR,
  trans_t At A ->
  repl_bot A k GL GR ->
  wft GR D ->
  teq GL D (tshift k (tsubst2 D k (kshift k A))) GR.
Proof.
  introv Ht. inductions Ht; introv Hta Hrb HwD.
  - (* tvar n *) simpl. destruct (lt_eq_lt_dec n k) as [[Hlt|Heq]|Hgt].
    + (* n < k *) simpl.
      destruct (le_gt_dec k n); try lia.
      forwards~ Hcr: repl_bot_wft_check_gr Hrb HwD.
      eapply eq_tvar; eauto. eapply repl_bot_check_r; [ exact Hrb | lia | exact Hcr ].
    + (* n = k : manifest resolves via lookt; then refl_relocate *)
      subst. rewrite tshift_k_kshift.
      eapply eq_eql; [ eapply repl_bot_lookt_k; exact Hrb | ].
      forwards (B1 & HB1): tt_kshift Hta k.
      forwards~ Hwk: repl_bot_wft_kshift Hrb.
      rewrite <- tshift_k_kshift.
      eapply refl_relocate; [ exact HB1 | exact Hrb | ].
      rewrite tshift_k_kshift; eauto.
    + (* n > k *) simpl.
      destruct (le_gt_dec k (n - 1)); try lia.
      replace (S (n - 1)) with n by lia.
      forwards~ Hcr: repl_bot_wft_check_gr Hrb HwD.
      eapply eq_tvar; eauto. eapply repl_bot_check_r; [ exact Hrb | lia | exact Hcr ].
  - (* int *) simpl. eapply eq_int; eauto.
  - (* arr *) simpl. unfold wft in HwD. forwards~ (HwA&HwB): wft_arr_inv HwD.
    eapply eq_arr; eauto.
  - (* all *) simpl. unfold wft in HwD. inverts HwD.
    eapply eq_all.
    forwards Hr: IHHt Hta (rb_etvar Hrb); [ unfold wft; eauto | ].
    simpl in Hr.
    replace (tshift 0 (kshift k A0)) with (kshift (S k) A0) in Hr by reflexivity.
    exact Hr.
Qed.

(* Position-0 balanced relate: the conservativity [tapp] target.  [Hb] relates
   the two [all]-bodies under the abstract binder; instantiating the binder
   with the manifest [A] on BOTH sides ([inst_teq]) and folding the manifest
   into the right substitution ([subst_fold_gen]) gives the padded goal. *)
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
  - (* wft (T &s) D : the right body is well-formed in the abstract context *)
    eapply teq_wft_right; exact Hb.
  - simpl in Hsf. exact Hsf.
Qed.


Lemma getv_wft: forall T,
  wfe T -> forall n A,
  get_var T n A ->
  wft T A.
Proof.
  introv Hw Hl. inductions Hl; eauto.
  - inverts Hw. forwards~: IHHl H0.
    eapply insert_tvar_wft; eauto.
  - forwards~: wfe_inv Hw. forwards~: IHHl H. 
    eapply insert_teq_wft; eauto.
  - forwards~: wfe_inv Hw.
    forwards~: wfe_evar_eteq Hw. 
    eapply add_evar_wfe; try eapply H0; eauto.
    econstructor. econstructor; eauto.
    eapply add_evar_refl; eauto.
  - forwards~: wfe_inv Hw.
    forwards~: wfe_evar_eteq Hw.
    forwards~: IHHl H. 
    eapply add_evar_wfe; try eapply H1; eauto.
    econstructor. econstructor; eauto.
    eapply add_evar_refl; eauto.
Qed.

Lemma mopen_wft: forall T1 A B,
  mopen T1 A B -> forall T,
  wft (T +++ T1) A ->
  wft T B.
Proof.
  introv Hm. inductions Hm; introv Hw; eauto.
  - eapply IHHm.
    eapply del_wft; eauto. rewrite <-mcon_cons. 
    simpl.
    econstructor. eapply del_refl; eauto.
  - eapply IHHm. 
    rewrite <-mcon_cons in Hw. 
    econstructor; eauto.
    eapply wft_wfe; eauto. 
Qed.

Lemma rl_wft: forall T1 l A,
  rlk T1 l A -> forall T,
  wft T T1 ->
  wft T A.
Proof.
  introv Hr. inductions Hr; introv Hw.
  - inverts Hw. inverts H7. 
    eapply mopen_wft; eauto.
  - eapply IHHr; eauto. inverts Hw; eauto.
  - eapply mopen_wft; eauto.
    eapply IHHr.
    inverts Hw. eauto.
  - eapply IHHr.
    inverts Hw.
    forwards~: wfe_inv H2.
Qed.




Lemma get_fget: forall T0 T,
  trans_env T0 T -> forall n A,
  get_var T n A -> exists A0,
  fget_var T0 n = Some A0 /\ trans_t A0 A.
Proof.
  introv Ht. inductions Ht; intros; eauto.
  - inverts H.
  - inverts* H0.
    + exists* A.
    + forwards~: IHHt H5.
  - inverts* H. forwards~ (A1&?&?): IHHt H1.
    exists (ftshift 0 A1). split*.
    simpl. rewrite H. eauto.
    eapply tt_tshift; eauto.
Qed.

Lemma tt_det_pre: forall A1 A2,
  trans_t A2 A1 -> forall A3,
  trans_t A3 A1 -> 
  A2 = A3.
Proof.
  introv Ht. inductions Ht; introv Hs; try solve [inverts* Hs].
  - inverts Hs. forwards~: IHHt1 H2. forwards~: IHHt2 H3. subst. eauto.
  - inverts Hs. forwards~: IHHt H1. subst. eauto.
Qed.


Lemma teq_all_tt: forall B A T,
  teq T (all B) A T -> forall C,
  trans_t C A -> forall T0,
  trans_env T0 T -> exists D,
  A = all D.
Proof.
  introv Ht. inductions Ht; introv Htt Htn; try solve [inverts Htt].
  - exfalso. eapply tten_lookt; eauto.
  - exists C. split*. 
Qed.

Lemma teq_arr_tt: forall B1 B2 A T,
  teq T (arr B1 B2) A T -> forall C,
  trans_t C A -> forall T0,
  trans_env T0 T -> exists D1 D2,
  A = arr D1 D2.
Proof.
  introv Ht. inductions Ht; introv Htt Htn; try solve [inverts Htt].
  - exfalso. eapply tten_lookt; eauto.
  - exists C D. split*. 
Qed.




Lemma teq_tt_eq: forall A B T,
  teq T A B T -> forall T0,
  trans_env T0 T -> forall A1,
  trans_t A1 A -> forall B1,
  trans_t B1 B ->
  A = B.
Proof.
  introv Ht. inductions Ht; introv Hten Hta Htb;
  try solve [eauto]; try solve [inverts Hta; inverts Htb].
  - exfalso. eapply tten_lookt; eauto.
  - exfalso. eapply tten_lookt; eauto.
  - inverts Hta. inverts Htb.
    forwards~: IHHt1 Hten H2 H4.
    forwards~: IHHt2 Hten H3 H5. subst. eauto.
  - inverts Hta. inverts Htb.
    forwards~: IHHt (fetvar :: T0) H1 H2. subst. eauto.
Qed.

(* relies on inst lemma and transitivity *)
(* BALANCED relate (padded conclusion).  The old conclusion
   [teq (T &= C) A (tsubst2 B 0 C) T] (right ambient [T]) is the IMBALANCED
   form that is FALSE under positional eq_tvar.  The padded form below
   (right ambient [T &s], target shifted by [tshift 0]) is exactly the subgoal
   the redesigned [eq_manil] leaves for the type-application case. *)
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


Lemma eq_dec : forall x y : nat, {x = y} + {x <> y}.
Proof.
  intros x y. destruct* (x == y). 
Qed.

Lemma beq_dec : forall (i:nat) (n:nat),
  beq_nat i n = true \/ beq_nat i n = false.
Proof.
  intros i n.
  destruct (beq_nat i n); [left | right]; reflexivity.
Qed.


Lemma beq_true_eq: forall i1 i2,
  (beq_nat i1 i2) = true ->
  i1 = i2.
Proof.
  intro x.
  induction x.
  intros y H.
  destruct y. reflexivity. simpl in *. congruence.
  intros y H. destruct y.
  simpl in *. congruence. f_equal ; auto.
Qed.

Lemma beq_refl: forall n, beq_nat n n = true. 
Proof.
  intros n. inductions n; eauto.
Qed.

Lemma eq_beq_true: forall i1 i2,
  i1 = i2 ->
  (beq_nat i1 i2) = true.
Proof.
  introv Heq.
  subst*.
  eapply beq_refl.
Qed.

Lemma beq_false_eq: forall i1 i2,
  (beq_nat i1 i2) = false ->
  i1 <> i2.
Proof.
  introv Hf.
  forwards~ [?|?]: eq_dec i1 i2.
  forwards~: eq_beq_true e.
  rewrite H in Hf. inverts* Hf.
Qed.

Inductive fvalue : term -> Prop :=
  | fv_lit: forall i, fvalue (flit i)
  | fv_abs: forall t, 
      fvalue (fabs t)
  | fv_tabs: forall t,
      fvalue (ftabs t).


Fixpoint subst (t : term) (x : nat) (t' : term) {struct t} : term :=
  match t with
  | fvar y      => if beq_nat x y then t' else fvar y
  | flit n      => flit n
  | fabs t2     => fabs (subst t2 (1 + x) t')
  | fapp t1 t2  => fapp (subst t1 x t') (subst t2 x t')
  | ftabs t2    => ftabs (subst t2 x t')
  | ftapp t1 T2 => ftapp (subst t1 x t') T2
  end.


Fixpoint sp_tsubst (A : ftyp) (X : nat) (A' : ftyp) {struct A} : ftyp :=
  match A with
  | ftvar Y    => if beq_nat X Y then A' else ftvar Y
  | fint       => fint
  | farr A1 A2 => farr (sp_tsubst A1 X A') (sp_tsubst A2 X A')
  | fall A2    => fall (sp_tsubst A2 (1 + X) A')
  end.


Fixpoint subst_typ (t : term) (X : nat) (T : ftyp) {struct t} : term :=
  match t with
  | fvar y      => fvar y
  | flit n      => flit n
  | fabs t2     => fabs (subst_typ t2 X T)
  | fapp t1 t2  => fapp (subst_typ t1 X T) (subst_typ t2 X T)
  | ftabs t1    => ftabs (subst_typ t1 (1 + X) T)
  | ftapp t1 T2 => ftapp (subst_typ t1 X T) (sp_tsubst T2 X T)
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
      red (fapp (fabs t1) w) (subst t1 0 w)
  | rtappl: forall (A : ftyp) (t1 t2 : term),
      red t1 t2 -> 
      red (ftapp t1 A) (ftapp t2 A)
  | rtbeta : forall (A : ftyp) (t1 : term),
      red (ftapp (ftabs t1) A) (subst_typ t1 0 A).

Inductive mred : term -> term -> Prop :=
  | mred_base : forall t, mred t t
  | mred_step : forall t t' t'', red t t' -> mred t' t'' -> mred t t''.


Inductive fbig: term -> term -> Prop :=
  | fb_lit: forall n, fbig (flit n) (flit n)
  | fb_abs: forall t1, fbig (fabs t1) (fabs t1)
  | fb_tabs: forall t1, fbig (ftabs t1) (ftabs t1)
  | fb_app: forall t1 t2 t3 w w1,
      fbig t1 (fabs t3) -> 
      fbig t2 w -> 
      fbig (subst t3 0 w) w1 ->
      fbig (fapp t1 t2) w1
  | fb_tapp: forall t1 t2 w A,
      fbig t1 (ftabs t2) -> 
      fbig (subst_typ t2 0 A) w -> 
      fbig (ftapp t1 A) w.

#[export]
Hint Constructors fvalue red mred fbig: core.


Lemma red_is_mred: forall t1 t2,
  red t1 t2 ->
  mred t1 t2.
Proof.
  introv Hm. eauto.
Qed.

Lemma mred_trans: forall t1 t2,
  mred t1 t2 -> forall t3,
  mred t2 t3 ->
  mred t1 t3.
Proof.
  introv Hm1. inductions Hm1; introv Hm2; eauto.
Qed.

Lemma mred_appl: forall t1 t2,
  mred t1 t2 -> forall t3,
  mred (fapp t1 t3) (fapp t2 t3).
Proof.
  introv Hm. inductions Hm; intros; eauto.
Qed.

Lemma mred_appr: forall t1 t2,
  mred t1 t2 -> forall w,
  fvalue w ->
  mred (fapp w t1) (fapp w t2).
Proof.
  introv Hm. inductions Hm; intros; eauto.
Qed.

Lemma mred_tappl: forall t1 t2,
  mred t1 t2 -> forall A,
  mred (ftapp t1 A) (ftapp t2 A).
Proof.
  introv Hm. inductions Hm; intros; eauto.
Qed.

Lemma fbig_fvalue: forall t1 t2,
  fbig t1 t2 ->
  fvalue t2.
Proof.
  introv Hm. inductions Hm; simpl; eauto.
Qed.

Lemma fbig_sound: forall t1 t2,
  fbig t1 t2 ->
  mred t1 t2.
Proof.
  introv Hb. inductions Hb; eauto.
  - eapply mred_trans; try eapply IHHb3. 
    forwards~: mred_appl IHHb1 t2.
    forwards~: mred_appr IHHb2 (fabs t3).
    forwards~: mred_trans H H0.
    eapply mred_trans; eauto.
    eapply red_is_mred; eauto.
    econstructor. eapply fbig_fvalue; eauto.
  - eapply mred_trans; try eapply IHHb2.
    forwards~: mred_tappl IHHb1 A.
    eapply mred_trans; eauto.
Qed.

Lemma fbig_refl: forall w,
  fvalue w ->
  fbig w w.
Proof.
  introv Hv. destruct* w; inverts Hv.
Qed.

Lemma f_absorb: forall t1 t2,
  red t1 t2 -> forall t3,
  fbig t2 t3 ->
  fbig t1 t3.
Proof.
  introv Hr. inductions Hr; introv Hb; 
  try solve [eauto];
  try solve [inverts* Hb].
  - econstructor; eauto. eapply fbig_refl; eauto.
Qed.

Lemma fbig_complete: forall t w,
  mred t w ->
  fvalue w ->
  fbig t w.
Proof.
  introv Hm. inductions Hm; introv Hv.
  - destruct* t; try solve [inverts* Hv]. 
  - forwards~: IHHm Hv.
    eapply f_absorb; eauto.
Qed.


Inductive big_box: typ -> typ -> typ -> Prop :=
  | bb_is_box: forall T T1 A,
      big_box T (boxt T1 A) (boxt T1 A)
  |bb_not_box: forall T A,
      ~ is_box A ->
      big_box T A (boxt T A).

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
  | b_blam: forall ve e,
      value ve ->
      big ve (blam e) (bclos ve e)
  | b_bclos: forall ve e ve',
      value ve ->
      value ve' ->
      big ve (bclos ve' e) (bclos ve' e)
  | b_beta : forall ve ve1 v2 e e1 e2 v, 
      value ve1 -> 
      big ve e1 (clos ve1 e) ->
      big ve e2 v2 ->
      big (ve1 ,, v2) e v ->
      big ve (app e1 e2) v
  | b_tbeta: forall ve ve1 e A e1 v, 
      value ve1 -> 
      big ve e1 (bclos ve1 e) ->
      big (ve1 ;; (boxt (c2g ve) A)) e v ->
      big ve (tapp e1 A) v
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
  | b_tdef: forall ve e1 ve1 A B,
      big ve e1 ve1 ->
      big_box (c2g (ve ++- ve1)) A B ->
      big ve (e1 ;; A) (ve1 ;; B)
  | b_rec: forall ve e l v,
      big ve e v ->
      big ve (rec l e) (rec l v)
  | b_proj: forall ve e v2 l dv,
      big ve e dv ->
      rlookupv dv l v2 ->
      big ve (rproj e l) v2.

#[export]
Hint Constructors big_box big: core.


Lemma mstep_value: forall ve e1 e2,
  mstep ve e1 e2 ->
  value ve.
Proof.
  introv Hs. inductions Hs; eauto.
Qed.

Lemma step_value: forall ve e1 e2,
  step ve e1 e2 ->
  value ve.
Proof.
  introv Hs. inductions Hs; eauto.
Qed.

Lemma step_is_mstep: forall ve e1 e2,
  step ve e1 e2 ->
  mstep ve e1 e2.
Proof.
  introv Hm. forwards~: step_value Hm. eauto.
Qed.

Lemma mstep_trans: forall ve e1 e2,
  mstep ve e1 e2 -> forall e3,
  mstep ve e2 e3 ->
  mstep ve e1 e3.
Proof.
  introv Hm1. inductions Hm1; introv Hm2; eauto.
Qed.

Lemma mstep_appl: forall ve e1 e2,
  mstep ve e1 e2 -> forall e3,
  mstep ve (app e1 e3) (app e2 e3).
Proof.
  introv Hm. inductions Hm; intros.
  - eauto.
  - forwards~: step_value H. eauto.
Qed.

Lemma mstep_appr: forall ve e1 e2,
  mstep ve e1 e2 -> forall v,
  value v ->
  mstep ve (app v e1) (app v e2).
Proof.
  introv Hm. inductions Hm; intros.
  - eauto.
  - forwards~: step_value H. eauto.
Qed.


Lemma mstep_tappl: forall ve e1 e2,
  mstep ve e1 e2 -> forall A,
  mstep ve (tapp e1 A) (tapp e2 A).
Proof.
  introv Hm. inductions Hm; intros; eauto.
Qed.

Lemma mstep_boxl: forall ve e1 e2,
  mstep ve e1 e2 -> forall e3,
  mstep ve (box e1 e3) (box e2 e3).
Proof.
  introv Hm. inductions Hm; intros; eauto.
  forwards~: step_value H. eauto. 
Qed.

Lemma mstep_boxr: forall ve1 e1 e2,
  mstep ve1 e1 e2 -> forall ve,
  value ve ->
  mstep ve (box ve1 e1) (box ve1 e2).
Proof.
  introv Hm. inductions Hm; intros; eauto.
  forwards~: step_value H. eauto.
Qed.

Lemma mstep_mrgl: forall ve d1 d2,
  mstep ve d1 d2 -> forall e,
  mstep ve (d1,,e) (d2,,e).
Proof.
  introv Hm. inductions Hm; intros; eauto.
  forwards~: step_value H. inverts* H.
Qed.

Lemma lv_old: forall ve1 ve,
  value (ve ++- ve1) ->
  value ve.
Proof.
  intros ve1. inductions ve1; intros; simpl; eauto.
  - rewrite <- econ_cons in H. inverts* H.
  - rewrite <- econ_cons_typ in H. inverts* H.
Qed.


Lemma mstep_mrgr: forall ve1 ve e1 e2,
  mstep (ve ++- ve1) e1 e2 -> 
  value ve1 ->
  mstep ve (ve1 ,, e1) (ve1 ,, e2).
Proof.
  introv Hm. inductions Hm; introv Hv; eauto.
  - forwards~: lv_old H.
  - forwards~: step_value H. forwards~: lv_old H0.
   (* forwards~: lv_new H0. *)
    forwards~: IHHm ve1 ve. 
    eapply mstep_trans; try eapply H2.
    eapply step_is_mstep. econstructor; eauto.
Qed.

Lemma mstep_tmrgl: forall ve d1 d2,
  mstep ve d1 d2 -> forall A,
  mstep ve (d1 ;; A) (d2 ;; A).
Proof.
  introv Hm. inductions Hm; intros; eauto.
  forwards~: step_value H. inverts* H.
Qed.

Lemma mstep_tmrgr: forall ve d1 A,
  ~ is_box A ->
  value d1 ->
  value ve ->
  mstep ve (d1 ;; A) (d1 ;; (boxt (c2g (ve ++- d1)) A)).
Proof.
  intros. eapply step_is_mstep. econstructor; eauto.
Qed.

Lemma big_box_res: forall T A B,
  big_box T A B -> exists T1 C,
  B = boxt T1 C.
Proof.
  introv Hb. forwards~ [?|?]: is_box_dec A.
  - inverts* H. inverts* Hb.
  - inverts* Hb.
Qed.

Lemma big_value: forall ve e1 e2,
  big ve e1 e2 ->
  value e2.
Proof.
  introv Hm. inductions Hm; simpl; eauto.
  eapply lookupv_value; eauto.
  - forwards~ (T1&C&?): big_box_res H. subst. inverts* IHHm.
  - eapply rl_value; eauto. 
Qed.

Lemma mstep_add: forall ve e1 e2,
  mstep ve e1 e2 -> forall ve1,
  value ve1 ->
  mstep ve1 (box ve e1) (box ve e2).
Proof.
  introv Hm. inductions Hm; introv Hl; eauto.
  - forwards~: IHHm Hl. forwards~: step_value H.
    eapply mstep_trans; try eapply H0.
    eapply step_is_mstep; eauto.
Qed.

Lemma mstep_add_tov: forall ve e1 v,
  mstep ve e1 v ->
  value v -> forall ve1,
  value ve1 ->
  mstep ve1 (box ve e1) v.
Proof.
  introv Hm Hv Hl. 
  forwards~: mstep_add Hm ve1.
  eapply mstep_trans; eauto.
  forwards~: mstep_value Hm.
  eapply step_is_mstep; eauto.
Qed.

Lemma mstep_rec: forall ve e1 e2,
  mstep ve e1 e2 -> forall l,
  mstep ve (rec l e1) (rec l e2).
Proof.
  introv Hm. inductions Hm; intros; eauto.
  forwards~: step_value H. eauto.
Qed.

Lemma mstep_proj: forall ve e1 e2,
  mstep ve e1 e2 -> forall l,
  mstep ve (rproj e1 l) (rproj e2 l).
Proof.
  introv Hm. inductions Hm; intros; eauto.
  forwards~: step_value H. eauto.
Qed.

Lemma big_env_lvalue: forall ve e v,
  big ve e v ->
  value ve.
Proof.
  introv He. inductions He; eauto.
Qed.


Lemma big_sound: forall ve e1 e2,
  big ve e1 e2 ->
  mstep ve e1 e2.
Proof.
  introv Hb. inductions Hb; eauto.
  - forwards~ Hv: big_value Hb3. forwards~ Hl: mstep_value IHHb1.
    forwards~ Hs: mstep_add_tov IHHb3 Hv Hl.
    eapply mstep_trans; try eapply Hs. 
    forwards~: mstep_appl IHHb1 e2.
    forwards~: mstep_appr IHHb2 (clos ve1 e). 
    forwards~: mstep_trans H0 H1.
    eapply mstep_trans; eauto.
    eapply step_is_mstep; eauto.
    econstructor; eauto. 
    eapply big_value; eauto.
  - forwards~ Hv: big_value Hb2. forwards~ Hl: mstep_value IHHb1.
    forwards~ Hs: mstep_add_tov IHHb2 Hv Hl.
    eapply mstep_trans; try eapply Hs.
    forwards~: mstep_tappl IHHb1 A.
    eapply mstep_trans; eauto.
  - forwards~ Hve: big_env_lvalue Hb1.
    forwards~ Hv1: big_env_lvalue Hb2.
    forwards~: mstep_boxl IHHb1 e2.
    forwards~: mstep_boxr IHHb2 ve. 
    forwards~: mstep_trans H H0.
    eapply mstep_trans; try eapply H2; eauto.
    eapply step_is_mstep; eauto.
    econstructor; eauto.
    forwards~: big_value Hb1. 
    eapply big_value; eauto.
  - forwards~: mstep_mrgl IHHb1 e2.
    forwards~: mstep_mrgr IHHb2.
    eapply big_value; eauto.
    forwards~: mstep_trans H H0.
  - forwards~: mstep_tmrgl IHHb A.
    forwards~: big_value Hb.
    forwards~ [?|?]: is_box_dec A.
    + inverts* H. exfalso. contradiction.
    + inverts* H. forwards~: mstep_value IHHb. 
      forwards~: mstep_tmrgr H2 H1 H.
      forwards~: mstep_trans H0 H4.
  - forwards~: mstep_rec IHHb l.
  - forwards~: mstep_proj IHHb l.
    eapply mstep_trans; eauto.
    eapply step_is_mstep; eauto.
    econstructor; eauto. eapply mstep_value; eauto.
    forwards~: big_value Hb. 
Qed.

Lemma big_refl: forall v,
  value v -> forall ve,
  value ve ->
  big ve v v.
Proof.
  introv Hv. inductions Hv; introv Hl; eauto.
  econstructor; eauto.
  eapply IHHv2. eapply value_app; eauto. 
Qed.

Lemma big_value_eq: forall ve v e,
  big ve v e ->
  value v ->
  e = v.
Proof.
  introv Hb. inductions Hb; introv Hv;
  try solve [inverts* Hv].
  - inverts Hv. forwards~: IHHb1 H1. forwards~: IHHb2 H2. subst. eauto.
  - inverts Hv. forwards~: IHHb H1. subst. inverts* H. exfalso. eapply H0. eauto.
  - inverts* Hv. forwards~: IHHb H0. subst. eauto.
Qed.

Lemma absorb: forall ve e1 e2,
  step ve e1 e2 -> forall e3,
  big ve e2 e3 ->
  big ve e1 e3.
Proof.
  introv Hr. inductions Hr; introv Hb;
  try solve [inverts* Hb].
  - forwards~: lookupv_value H0.
    forwards~: big_value_eq Hb H1. subst. eauto.
  - inverts* Hb. forwards~: big_value_eq H4. inverts H1. 
    econstructor; eauto.
  - forwards~: big_refl v1 ve. forwards~: big_refl v2 v1.
    forwards~: big_value_eq Hb. subst. econstructor; eauto.
  - econstructor; try eapply big_refl; eauto. inverts* Hb.
    forwards~: big_value_eq H5. inverts H2. eauto. 
  - econstructor; try eapply big_refl; eauto. inverts* Hb.
    forwards~: big_value_eq H4. inverts H1. eauto.
  - inverts* Hb. forwards~: big_value_eq H4. inverts* H1.
  - inverts* Hb. inverts H7.
    + forwards~: big_value_eq H5. inverts* H2.
    + exfalso. eapply H2. eauto.  
  - forwards~: big_value_eq Hb. eapply rl_value; eauto. subst.  econstructor; eauto.
    eapply big_refl; eauto.
Qed.

Lemma big_complete: forall ve e v,
  mstep ve e v ->
  value v ->
  big ve e v.
Proof.
  introv Hm. inductions Hm; introv Hv.
  - eapply big_refl; eauto.
  - forwards~: IHHm Hv.
    eapply absorb; eauto.
Qed.





(* --------------- *)
Inductive olookt : typ -> nat -> typ -> Prop :=
  | olookt_evar : forall X T A B,
      olookt T X B ->
      olookt (T & A) X B
  | olookt_zero : forall T A,
      olookt (T &= A) 0 A
  | olookt_eteq : forall X T A B,
      olookt T X B ->
      olookt (T &= A) (S X) B
  | olookt_etvar : forall X T B,
      olookt T X B ->
      olookt (T &s) (S X) B.

Inductive closing: typ -> typ -> nat -> typ -> Prop :=
  | clovarl: forall T i n,
      i < n ->
      closing (tvar i) T n (tvar i)
  | clovarint: forall T i n,
      i >= n ->
      olookt T (minus i n) int ->
      closing (tvar i) T n int
  | clovarbox: forall T i n A1 T1 A,
      i >= n ->
      olookt T (minus i n) (boxt T1 A1) ->
      closing A1 T1 0 A ->
      closing (tvar i) T n A
  | cloint: forall T n,
      closing int T n int
  | cloarr: forall A1 A2 T n A3 A4,
      closing A1 T n A3 ->
      closing A2 T n A4 ->
      closing (arr A1 A2) T n (arr A3 A4)
  | cloall: forall A T n A1,
      closing A T (S n) A1 ->
      closing (all A) T n (all A1).

Inductive tcheck: exp -> exp -> nat -> exp -> Prop :=
  | tchvar: forall E i n,
      value E ->
      tcheck (var i) E n (var i)
  | tchlit: forall E i n,
      value E ->
      tcheck (lit i) E n (lit i)
  | tchlam: forall e E n e',
      tcheck e E n e' ->
      tcheck (lam e) E n (lam e')
  | tchapp: forall e1 e2 E n e3 e4,
      tcheck e1 E n e3 ->
      tcheck e2 E n e4 ->
      tcheck (app e1 e2) E n (app e3 e4)
  | tchblam: forall e E n e',
      tcheck e E (S n) e' ->
      tcheck (blam e) E n (blam e')
  | tchtapp: forall e E n e' A1 A,
      tcheck e E n e' ->
      closing A1 (c2g E) n A ->
      tcheck (tapp e A1) E n (tapp e' A).



Inductive check: exp -> exp -> nat -> term -> Prop :=
  | chvarl: forall E i n,
      value E ->
      n > i ->
      check (var i) E n (fvar i)
  | chvarlam: forall E i n e e1 E' s,
      value E ->
      i >= n ->
      lookupv E (minus i n) (clos E' e) ->
      tcheck e E' 0 e1 ->
      check e1 E' 1 s ->
      check (var i) E n (fabs s)
  | chvarblam: forall E i n e e1 E' s,
      value E ->
      i >= n ->
      lookupv E (minus i n) (bclos E' e) ->
      tcheck e E' 1 e1 ->
      check e1 E' 0 s ->
      check (var i) E n (ftabs s)
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
      check (app e1 e2) E n (fapp e3 e4)
  | chblam: forall e E n e',
      check e E n e' ->
      check (blam e) E n (ftabs e')
  | chtapp: forall e A E n e' A1,
      check e E n e' ->
      trans_t A A1 ->
      check (tapp e A1) E n (ftapp e' A).

Inductive resrel: term -> exp -> Prop :=
  | rrlit: forall i,
      resrel (flit i) (lit i)
  | rrlam: forall e1 t e E,
      tcheck e E 0 e1 ->
      check e1 E 1 t ->
      resrel (fabs t) (clos E e)
  | rrblam: forall e1 t e E,
      tcheck e E 1 e1 ->
      check e1 E 0 t ->
      resrel (ftabs t) (bclos E e).
      
#[export]
Hint Constructors olookt check closing tcheck resrel: core.

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
      bound (fabs e) k
  | bbiglam k e: 
      bound e k -> 
      bound (ftabs e) k
  | bbigapp k e A: 
      bound e k -> 
      bound (ftapp e A) k.

#[export]
Hint Constructors bound: core.

Definition closed s:= bound s 0.

Lemma bound_larger: forall e k,
  bound e k -> forall n,
  k <= n ->
  bound e n.
Proof.
  introv Hb. inductions Hb; introv Hl;
  try solve [eauto].
  - econstructor. lia.
  - econstructor.
    eapply IHHb. lia. 
Qed.

Lemma bound_check: forall t n,
  bound t n -> forall E,
  value E -> forall e,
  trans_e t e ->
  check e E n t.
Proof.
  introv Hb. inductions Hb; introv Hl Ht;
  try solve [inverts* Ht].
Qed.


Lemma check_bound: forall e1 E e n,
  check e1 E n e ->
  bound e n.
Proof.
  introv Hc. inductions Hc;
  try solve [eauto].
  - eapply bound_larger; eauto. lia.
  - eapply bound_larger; eauto. lia.
Qed.

Lemma bound_subst: forall e k,
  bound e k -> forall n e1,
  k <= n -> 
  subst e n e1 = e.
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
  - forwards~: IHHb n e1. simpl. rewrite H. eauto.
  - forwards~: IHHb n e1. simpl. rewrite H. eauto.
Qed.

Lemma check_lvalue: forall e E n t,
  check e E n t ->
  value E.
Proof.
  introv Hc. inductions Hc; eauto.
Qed.

Lemma tcheck_lvalue: forall e E n t,
  tcheck e E n t ->
  value E.
Proof.
  introv Hc. inductions Hc; eauto.
Qed.

Lemma resrel_value: forall w v,
  resrel w v ->
  value v.
Proof.
  introv Hr. inverts* Hr.
  - econstructor. eapply check_lvalue; eauto.
  - econstructor. eapply tcheck_lvalue; eauto.
Qed.

Lemma lookupv_minus: forall i E r,
  lookupv E i r -> forall v2,
  lookupv (E,,v2) (S i) r.
Proof.
  introv Hs. inductions Hs; intros.
  - simpl. eauto.
  - simpl. eauto. 
  - econstructor. econstructor. eauto. 
Qed.


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
    + forwards~: check_lvalue H2.
      destruct* (beq_dec n i).
      * rewrite H4. forwards~: beq_true_eq H4.
        subst. eapply chvarlam; eauto.
        assert (i - i = 0). lia. rewrite H5. eauto.
      * rewrite H4. econstructor; eauto.
        forwards~: beq_false_eq H4. lia.
    + (* todo *)
      forwards~: tcheck_lvalue H1.
      destruct* (beq_dec n i).
      * rewrite H4. forwards~: beq_true_eq H4.
        subst. eapply chvarblam; eauto.
        assert (i - i = 0). lia. rewrite H5. eauto.
      * rewrite H4. econstructor; eauto.
        forwards~: beq_false_eq H4. lia.
  - simpl.
    forwards~: resrel_value Hw.
    forwards~: lookupv_minus H1 v2.
    assert (S (i - S n) = i - n). lia. rewrite H5 in H4.
    forwards~: check_bound Hc.
    forwards~: bound_subst H6 (S n) w. lia.
    rewrite H7. econstructor; eauto. lia.
  - simpl. 
    forwards~: resrel_value Hw.
    forwards~: lookupv_minus H1 v2.
    assert (S (i - S n) = i - n). lia. rewrite H5 in H4.
    forwards~: check_bound Hc.
    forwards~: bound_subst H6 n w. lia.
    rewrite H7. econstructor; eauto. lia.
  - simpl. forwards~: resrel_value Hw.
    eapply chvarlit; eauto. lia.
    forwards~: lookupv_minus H1 v2.
    assert (S (i - S n) = i - n). lia. rewrite H4 in H3. eauto.
Qed.


Fixpoint osp_tsubst (A : typ) (X : nat) (A' : typ) {struct A} : typ :=
  match A with
  | tvar Y => if beq_nat X Y then A' else tvar Y
  | int       => int
  | arr A1 A2 => arr (osp_tsubst A1 X A') (osp_tsubst A2 X A')
  | all A2    => all (osp_tsubst A2 (1 + X) A')
  | _         => A
  end.


Fixpoint osubst_typ (t : exp) (X : nat) (T : typ) {struct t} : exp :=
  match t with
  | var y      => var y
  | lit n      => lit n
  | lam t2     => lam (osubst_typ t2 X T)
  | app t1 t2  => app (osubst_typ t1 X T) (osubst_typ t2 X T)
  | tapp t1 T2 => tapp (osubst_typ t1 X T) (osp_tsubst T2 X T)
  | blam t1    => blam (osubst_typ t1 (1 + X) T)
  | _ => t
  end.

Lemma olookt_minus: forall i T B,
  olookt T i B -> forall A,
  olookt (T &= A) (S i) B.
Proof.
  introv Hs. intros. eauto. 
Qed.


Inductive tbound : typ -> nat -> Prop :=
  | tb_tvar k n : 
      k > n -> 
      tbound (tvar n) k
  | tb_int k :  
      tbound int k
  | tb_arr k e1 e2 : 
      tbound e1 k -> 
      tbound e2 k -> 
      tbound (arr e1 e2) k
  | tb_all k A: 
      tbound A (S k) -> 
      tbound (all A) k.

#[export]
Hint Constructors tbound: core.

Lemma tbound_larger: forall e k,
  tbound e k -> forall n,
  k <= n ->
  tbound e n.
Proof.
  introv Hb. inductions Hb; introv Hl;
  try solve [eauto].
  - econstructor. lia.
  - econstructor. eapply IHHb. lia.
Qed.

Lemma closing_tbound: forall A1 T A n,
  closing A1 T n A ->
  tbound A n.
Proof.
  introv Hc. inductions Hc;
  try solve [eauto].
  - eapply tbound_larger; eauto. lia.
Qed.

Lemma tbound_osp_tsubst: forall A k,
  tbound A k -> forall n A1,
  k <= n -> 
  osp_tsubst A n A1 = A.
Proof.
  introv Hb. inductions Hb; introv Hl;
  try solve [simpl; eauto].
  - simpl.
    destruct* (beq_dec n0 n).
    + forwards~: beq_true_eq H0. lia. 
    + rewrite H0. eauto. 
  - simpl. forwards~: IHHb1 n A1. forwards~: IHHb2 n A1. 
    rewrite H. rewrite H0. eauto.
  - simpl.
    forwards~: IHHb (S n) A1. lia. 
    rewrite H. eauto.
Qed.


Lemma closing_sn: forall T1 A1 n A,
  closing A1 T1 (S n) A -> forall T A0 A2,
  closing A0 T 0 A2 ->
  closing A1 (T1 &= (boxt T A0)) n (osp_tsubst A n A2).
Proof.
  introv Hc. inductions Hc; introv Hc0; try solve [simpl; econstructor; eauto].
  - simpl. destruct* (beq_dec n i).
    + rewrite H0. forwards~: beq_true_eq H0. subst.
      econstructor; eauto. replace (i - i) with 0 by lia.
      eauto. 
    + rewrite H0. econstructor. forwards~: beq_false_eq H0. lia.
  - simpl. econstructor. lia. 
    forwards~: olookt_minus H0 (boxt T0 A0).
    replace (i - n) with (S (i - S n)) by lia. eauto.
  - forwards~: olookt_minus H0 (boxt T0 A0).
    assert (S (i - S n) = i - n). lia. rewrite H2 in H1.
    econstructor; eauto. lia. 
    forwards~: closing_tbound Hc.
    forwards~: tbound_osp_tsubst H3 n A2. lia. rewrite H4. eauto.
Qed.



Lemma tcheck_sn: forall e1 E n e2,
  tcheck e1 E (S n) e2 -> forall T A A1,
  closing A T 0 A1 -> 
  tcheck e1 (E;;(boxt T A)) n (osubst_typ e2 n A1).
Proof.
  introv Hc. inductions Hc; introv Hw; try solve [simpl; eauto].
  - simpl. econstructor; eauto. 
    forwards~: closing_sn H Hw.
Qed.


Inductive te_bound : exp -> nat -> Prop :=
  | teb_var k n : 
      te_bound (var n) k
  | teb_lit i k :  
      te_bound (lit i) k
  | teb_app k e1 e2 : 
      te_bound e1 k -> 
      te_bound e2 k -> 
      te_bound (app e1 e2) k
  | teb_slam k e: 
      te_bound e k -> 
      te_bound (lam e) k
  | teb_biglam k e: 
      te_bound e (S k) -> 
      te_bound (blam e) k
  | teb_bigapp k e A: 
      te_bound e k -> 
      tbound A k ->
      te_bound (tapp e A) k.

#[export]
Hint Constructors te_bound: core.

Lemma tcheck_te_bound: forall e1 E e n,
  tcheck e E n e1 ->
  te_bound e1 n.
Proof.
  introv Hc. inductions Hc; try solve [eauto].
  - econstructor; eauto. eapply closing_tbound; eauto. 
Qed.

Inductive ftbound : ftyp -> nat -> Prop :=
  | ftb_tvar k n : 
      k > n -> 
      ftbound (ftvar n) k
  | ftb_int k :  
      ftbound fint k
  | ftb_arr k e1 e2 : 
      ftbound e1 k -> 
      ftbound e2 k -> 
      ftbound (farr e1 e2) k
  | ftb_all k A: 
      ftbound A (S k) -> 
      ftbound (fall A) k.

Inductive fte_bound : term -> nat -> Prop :=
  | fteb_var k n : 
      fte_bound (fvar n) k
  | fteb_lit i k :  
      fte_bound (flit i) k
  | fteb_app k e1 e2 : 
      fte_bound e1 k -> 
      fte_bound e2 k -> 
      fte_bound (fapp e1 e2) k
  | fteb_slam k e: 
      fte_bound e k -> 
      fte_bound (fabs e) k
  | fteb_biglam k e: 
      fte_bound e (S k) -> 
      fte_bound (ftabs e) k
  | fteb_bigapp k e A: 
      fte_bound e k -> 
      ftbound A k ->
      fte_bound (ftapp e A) k.

Definition fte_closed s:= fte_bound s 0.

#[export]
Hint Constructors ftbound fte_bound: core.

Lemma te_bound_larger: forall e k,
  te_bound e k -> forall n,
  k <= n ->
  te_bound e n.
Proof.
  introv Hb. inductions Hb; introv Hl;
  try solve [eauto].
  - econstructor. eapply IHHb. lia.
  - econstructor; eauto. eapply tbound_larger; eauto.
Qed.

Lemma tbound_keep: forall A1 n,
  tbound A1 n -> forall A,
  trans_t A A1 ->
  ftbound A n.
Proof.
  introv Ht. inductions Ht; introv Htr; try solve [inverts* Htr].
Qed.

Lemma check_keep_tebound: forall e E m t,
  check e E m t -> forall n,
  te_bound e n ->
  fte_bound t n.
Proof.
  introv Hc. inductions Hc; introv Hte; try solve [inverts* Hte].
  - econstructor. eapply IHHc. 
    forwards~: tcheck_te_bound H2. eapply te_bound_larger; eauto. lia.
  - econstructor. eapply IHHc.
    forwards~: tcheck_te_bound H2. eapply te_bound_larger; eauto. lia.
  - inverts Hte. econstructor; eauto. eapply tbound_keep; eauto.
Qed.

Lemma ftbound_sp_tsubst: forall A k,
  ftbound A k -> forall n A1,
  k <= n -> 
  sp_tsubst A n A1 = A.
Proof.
  introv Hb. inductions Hb; introv Hl;
  try solve [simpl; eauto].
  - simpl.
    destruct* (beq_dec n0 n).
    + forwards~: beq_true_eq H0. lia. 
    + rewrite H0. eauto. 
  - simpl. forwards~: IHHb1 n A1. forwards~: IHHb2 n A1. 
    rewrite H. rewrite H0. eauto.
  - simpl.
    forwards~: IHHb (S n) A1. lia. 
    rewrite H. eauto.
Qed.

Lemma ftebound_subst_typ: forall s k,
  fte_bound s k -> forall n A1,
  k <= n -> 
  subst_typ s n A1 = s.
Proof.
  introv Hb. inductions Hb; introv Hl;
  try solve [simpl; eauto].
  - simpl. forwards~: IHHb1 n A1. forwards~: IHHb2 n A1. 
    rewrite H. rewrite H0. eauto.
  - simpl. forwards~: IHHb n A1.  
    rewrite H. eauto.
  - simpl. forwards~: IHHb (S n) A1. lia.  
    rewrite H. eauto.
  - simpl. forwards~: IHHb n A1. rewrite H0.
    forwards~: ftbound_sp_tsubst H n A1. rewrite H1. eauto.
Qed.

Lemma tt_sp_tsubst: forall A1 A4,
  trans_t A1 A4 -> forall A2 A3,
  trans_t A2 A3 -> forall X,
  trans_t (sp_tsubst A1 X A2) (osp_tsubst A4 X A3).
Proof.
  introv Ht1. inductions Ht1; introv Ht2; intros;
  try solve [simpl; eauto].
  - simpl. destruct (beq_dec X n).
    + rewrite H. eauto. 
    + rewrite H. eauto. 
Qed.

Lemma check_subst_typ: forall e E0 n e2,
  tcheck e E0 (S n) e2 -> forall m t,
  check e2 E0 m t -> forall A1 A,
  trans_t A A1 -> forall T A0,
  closing A0 T 0 A1 ->
  check (osubst_typ e2 n A1) (E0;;(boxt T A0)) m (subst_typ t n A).
Proof. 
  introv Ht. inductions Ht; introv Hc Htr Hcl; try solve [inverts Hc; simpl; eauto].
  - inverts Hc; simpl; try solve [eauto].
    + forwards~: tcheck_te_bound H4.
      forwards~: check_keep_tebound H5 H0.
      forwards~ Hs: ftebound_subst_typ H6 n A. lia. 
      rewrite Hs. eauto.
    + forwards~: tcheck_te_bound H4.
      forwards~: check_keep_tebound H5 H0.
      forwards~ Hs: ftebound_subst_typ H6 (S n) A. lia. 
      rewrite Hs. eauto.
  - inverts Hc. simpl. econstructor; eauto.
    eapply tt_sp_tsubst; eauto.
Qed.

Lemma tcheck_weaken: forall e E n e1,
  tcheck e E n e1 -> forall v,
  value v ->
  tcheck e (E,,v) n e1.
Proof.
  introv Ht. inductions Ht; intros; eauto.
Qed.


Lemma dyn_complete_ori: forall t w,
  fbig t w -> forall e E e1,
  tcheck e E 0 e1 ->
  check e1 E 0 t -> exists v,
  big E e v /\ resrel w v.
Proof.
  introv Hf. inductions Hf; introv Ht Hc.
  - inductions Hc.
    + exists (lit n). split*. assert (i - 0 = i) by lia. rewrite H2 in H1.
      inverts Ht. eauto.
    + exists (lit n). inverts Ht. split*.
  - inverts keep Hc.
    * inverts Ht. exists* (clos E' e0). split*. 
      econstructor; eauto.
      assert (i - 0 = i). lia. 
      rewrite H in H2. auto. 
    * inverts Ht. forwards~: check_lvalue H3.
      exists* (clos E e1). 
  - inverts keep Hc.
    * inverts Ht. exists* (bclos E' e0). split*.
      econstructor; eauto. 
      assert (i - 0 = i). lia. 
      rewrite H in H2. auto.
    * inverts Ht. forwards~: check_lvalue H3.
      exists* (bclos E e1). 
  - inverts keep Hc. inverts Ht. 
    forwards~ (v1&?&?): IHHf1 H6 H4. forwards~ (v2&?&?): IHHf2 H7 H5.
    inverts H0.
    forwards~: check_sn H9 H2.
    forwards~ Hcl: check_lvalue H0. inverts Hcl.
    forwards~ Hl: check_lvalue H4. 
    forwards~ Htt: tcheck_weaken H8 v2. 

    forwards~ (v&?&?): IHHf3 Htt H0. 
    exists* v. 
  - (* type application *)
    inverts keep Hc. inverts Ht.
    forwards~ (v1&?&?): IHHf1 H6 H4.
    inverts H0.
    forwards~ Hvl: check_lvalue H3.
    forwards~ Hvl2: check_lvalue H4.

    assert (tcheck e (E0;;(boxt (c2g E) A0)) 0 (osubst_typ e2 0 A1)).
    { eapply tcheck_sn; eauto. }

    forwards~: IHHf2 e (E0;;(boxt (c2g E) A0)) H0.
    eapply check_subst_typ; eauto.
    destruct H1 as (v&?&?). exists* v. 
Qed.

Lemma ftbound_closing: forall A k,
  ftbound A k -> forall A1,
  trans_t A A1 -> forall T,
  closing A1 T k A1.
Proof.
  introv Hb. inductions Hb; introv Ht; intros; try solve [inverts* Ht].
Qed.

Lemma fte_bound_check: forall t n,
  fte_bound t n -> forall E,
  value E -> forall e,
  trans_e t e ->
  tcheck e E n e.
Proof.
  introv Hb. inductions Hb; introv Hl Ht;
  try solve [inverts* Ht].
  - inverts Ht. econstructor; eauto.
    eapply ftbound_closing; eauto.
Qed.

Lemma dyn_complete_small: forall t w,
  mred t w -> 
  fvalue w -> forall e,
  trans_e t e ->
  fte_closed t ->
  closed t -> exists v,
  mstep unit e v /\ resrel w v.
Proof.
  introv Hf Hw Htr Hfte Hc.
  forwards~ Hm: fbig_complete Hf Hw.  
  
  unfold fte_closed in *. unfold closed in *.
  forwards~: fte_bound_check Hfte unit e.
  forwards~: bound_check Hc unit Htr.
  forwards~ (v&?&?): dyn_complete_ori Hm H H0. exists v. split*.
  eapply big_sound; eauto.
Qed.


Fixpoint elen (T:fenv) : nat :=
  match T with
  | nil => 0
  | fevar _ :: T1 => S (elen T1)
  | fetvar :: T1 => elen T1
  end.

Lemma typed_bound: forall T e A,
  ftyping T e A ->
  bound e (elen T).
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
  ftyping nil e A ->
  closed e.
Proof.
  introv Hs. unfold closed.
  forwards~: typed_bound Hs.
Qed. 


Fixpoint tlen (T:fenv) : nat :=
  match T with
  | nil => 0
  | fevar _ :: T1 => tlen T1
  | fetvar :: T1 => S (tlen T1)
  end.

Lemma f_check_bound: forall T i,
  f_check T i = true ->
  tlen T > i.
Proof.
  intros T. inductions T; introv Hf.
  - inverts Hf.
  - destruct a.
    + simpl. inverts* Hf. 
    + simpl. destruct* i. 
      ** lia.
      ** simpl in Hf. forwards~: IHT Hf. lia. 
Qed.

Lemma wft_bound_gen: forall T0,
  fwfe T0 -> forall A T,
  T0 = fevar A :: T ->
  ftbound A (tlen T).
Proof.
  introv Hf. induction Hf; introv Heq; try discriminate;
    injection Heq as ? ?; subst; try solve [eauto].
  - econstructor. eapply f_check_bound; eauto.
  - econstructor.
    eapply (IHHf2 A (fetvar :: T0)); reflexivity.
Qed.

Lemma wft_bound: forall T A,
  fwft T A ->
  ftbound A (tlen T).
Proof.
  introv Hf. unfold fwft in *. eapply wft_bound_gen; eauto.
Qed.


Lemma typed_bound_t: forall T e A,
  ftyping T e A ->
  fte_bound e (tlen T).
Proof.
  introv Ht. inductions Ht; try solve [eauto].
  - econstructor; eauto.
    apply wft_bound. eauto.
Qed.

Lemma typed_closed_t: forall e A,
  ftyping [] e A ->
  fte_closed e.
Proof.
  introv Hs. unfold fte_closed.
  forwards~: typed_bound_t Hs.
Qed. 

Lemma dyn_complete: forall t w,
  mred t w -> 
  fvalue w -> forall e A,
  trans_e t e ->
  ftyping [] t A -> exists v,
  mstep unit e v /\ resrel w v.
Proof.
  intros. eapply dyn_complete_small; eauto.
  eapply typed_closed_t; eauto.
  eapply typed_closed; eauto.
Qed.


Inductive isft: typ -> Prop :=
  | is_tvar: forall n, isft (tvar n)
  | is_int : isft int 
  | is_arr : forall A B, 
      isft A ->
      isft B ->
      isft (arr A B)
  | is_all : forall A,
      isft A ->
      isft (all A).

Inductive isf : exp -> Prop :=
  | islit: forall i, isf (lit i)
  | isvar: forall n, isf (var n)
  | islam: forall e,
        isf e ->
        isf (lam e)
  | isapp: forall e1 e2,
        isf e1 ->
        isf e2 ->
        isf (app e1 e2)
  | isblam: forall e,
        isf e ->
        isf (blam e)
  | istapp: forall e A,
        isf e ->
        isft A ->
        isf (tapp e A).

#[export]
Hint Constructors isft isf: core.
  
Lemma lookupv_det: forall E n v1,
  lookupv E n v1 -> forall v2,
  lookupv E n v2 ->
  v1 = v2.
Proof.
  introv Hl. inductions Hl; introv Hl2; inverts* Hl2.
Qed.

Inductive isfv : exp -> Prop:=
  | isfv_lit: forall i, isfv (lit i)
  | isfv_clos: forall E e,
      isf e ->
      isfv E ->
      isfv (clos E e)
  | isfv_bclos: forall E e,
      isf e ->
      isfv E ->
      isfv (bclos E e)
  | isfe_nil: isfv unit
  | isfe_cons: forall E v,
      isfv v ->
      isfv E ->
      isfv (E,,v)
  | isfe_cons2: forall A E,
      isfv E ->
      is_box A ->
      isfv (E;;A).

#[export]
Hint Constructors isfv : core.

Lemma lookup_isfv: forall E n v',
  lookupv E n v' ->
  isfv E ->
  isfv v'.
Proof.
  introv Hl. inductions Hl; introv Hs; inverts* Hs.
Qed.

Lemma isf_isfv: forall E e v,
  big E e v ->
  isf e ->
  isfv E ->
  isfv v.
Proof.
  introv Hb. inductions Hb; introv Hs Hv; 
  try solve [inverts* Hs].
  - eapply lookup_isfv; eauto.
  - inverts* Hs.
    forwards~: IHHb1 H2 Hv. inverts* H0.
  - inverts* Hs.
    forwards~: IHHb1 H2 Hv. inverts* H0.
Qed.


Lemma dyn_conserve_ori: forall E e v,
  big E e v -> 
  isf e ->
  isfv E -> forall e1,
  tcheck e E 0 e1 -> forall t,
  check e1 E 0 t -> exists w,
  fbig t w /\ resrel w v.
Proof.
  introv Hb. inductions Hb; introv Hi He Ht Hc; try solve [inverts* Hi].
  - inverts Hi. inverts Ht. assert (n - 0 = n) as Hn by lia.
    inverts Hc.
    + lia.
    + exists (fabs s). rewrite Hn in H5. 
      forwards~: lookupv_det H0 H5. subst. split*. 
    + exists (ftabs s). rewrite Hn in H5. 
      forwards~: lookupv_det H0 H5. subst. split*. 
    + exists (flit j). rewrite Hn in H5. 
      forwards~: lookupv_det H0 H5. subst. split*. 
  - inverts Hi. inverts Ht. inverts Hc. exists (flit n). split*.
  - inverts Hi. inverts Ht. inverts Hc.
    exists (fabs e'0). split*.
  - inverts Hi. inverts Ht. inverts Hc.
    exists (ftabs e'0). split*.
  - inverts Hi. inverts Ht. inverts Hc.
    forwards~ (w1&Hf1&Hr1): IHHb1 H4 H5.
    forwards~ (w2&Hf2&Hr2): IHHb2 H8 H10.
    inverts Hr1. 
    forwards~: check_sn H9 Hr2.
    forwards~: isf_isfv Hb1 He. inverts H1.
    forwards~ Hv: big_value Hb2.
    forwards~: isf_isfv Hb2.
    forwards~: IHHb3 e0 (subst t 0 w2).
    eapply tcheck_weaken; eauto.
    destruct H6 as (w&?&?). exists* w.
  - inverts Hi. inverts Ht. inverts Hc.
    forwards~ (w1&Hf1&Hr1): IHHb1 H4 H5.
    inverts Hr1.
    forwards~: tcheck_sn H7 H8.
    forwards~: check_subst_typ H7 H9 H10 H8.
    forwards~: isf_isfv Hb1 He. inverts H6.
    forwards~ Hv: big_value Hb2.
    forwards~: IHHb2 (osubst_typ e0 0 A0) (subst_typ t 0 A1).
    destruct H6 as (w&?&?). exists* w.
Qed.

Lemma trans_isft: forall A A1,
  trans_t A A1 ->
  isft A1.
Proof.
  introv Ht. inductions Ht; eauto.
Qed.

Lemma trans_isf: forall t e,
  trans_e t e ->
  isf e.
Proof.
  introv Ht. inductions Ht; eauto.
  - econstructor; eauto. eapply trans_isft; eauto.
Qed.

Lemma dyn_conserve_small: forall e v,
  mstep unit e v -> 
  value v -> forall t,
  trans_e t e ->
  fte_closed t ->
  closed t -> exists w,
  mred t w /\ resrel w v.
Proof.
  introv Hm Hv Htr Hfte Hc.
  forwards~ Hb: big_complete Hm Hv.  
  
  unfold fte_closed in *. unfold closed in *.
  forwards~: fte_bound_check Hfte unit e.
  forwards~: bound_check Hc unit Htr.
  forwards~ (w&?&?): dyn_conserve_ori Hb H H0.
  eapply trans_isf; eauto.
  exists w. split*.
  eapply fbig_sound; eauto.
Qed.



Inductive cexp :=
  | clit  : nat -> cexp
  | cvar  : nat -> cexp
  | clam  : typ -> cexp -> cexp
  | cbox  : cexp -> cexp -> cexp
  | capp  : cexp -> cexp -> cexp
  | cblam : cexp -> cexp
  | cclos : cexp -> cexp -> cexp
  | cbclos: cexp -> cexp -> cexp
  | ctapp : cexp -> typ -> cexp
  | crec  : string -> cexp -> cexp
  | crproj: cexp -> string -> cexp
  | cunit : cexp
  | cmerge: cexp -> cexp -> cexp
  | ctmerge: cexp -> typ -> cexp.

Inductive cvalue : cexp -> Prop :=
  | cvlit  : forall i, cvalue (clit i)
  | cvclos : forall E e, cvalue E -> cvalue (cclos E e)
  | cvbclos: forall E e, cvalue E -> cvalue (cbclos E e)
  | cvrec  : forall l v, cvalue v -> cvalue (crec l v)
  | clvnil : cvalue cunit
  | clvconsv: forall E v, cvalue E -> cvalue v -> cvalue (cmerge E v)
  | clvconst: forall E T A, cvalue E -> cvalue (ctmerge E (boxt T A)).


Inductive chas_type : typ -> cexp -> typ -> Prop :=
  | ct_int : forall T i, wfe T -> chas_type T (clit i) int
  | ct_var : forall T A n, wfe T -> get_var T n A -> chas_type T (cvar n) A
  | ct_lam : forall T A e B,
      chas_type (T & A) e B ->
      chas_type T (clam A e) (arr A B)
  | ct_app : forall T A B e1 e2,
      chas_type T e1 (arr A B) -> chas_type T e2 A -> chas_type T (capp e1 e2) B
  | ct_blam: forall T B e,
      chas_type (T &s) e B -> chas_type T (cblam e) (all B)
  | ct_tapp: forall T e A B,
      chas_type T e (all B) -> wft T A -> chas_type T (ctapp e A) (mani A B)
  | ct_box: forall T e1 T1 A e2,
      chas_type T e1 T1 -> chas_type T1 e2 A -> rigid 0 T1 A ->
      chas_type T (cbox e1 e2) (boxt T1 A)
  | ct_clos: forall T E1 T1 A B e2,
      chas_type top E1 T1 -> chas_type (T1 & A) e2 B -> cvalue E1 ->
      rigid 0 T1 (arr A B) -> wfe T ->
      chas_type T (cclos E1 e2) (boxt T1 (arr A B))
  | ct_bclos: forall T E1 T1 A e2,
      chas_type top E1 T1 -> chas_type (T1 &s) e2 A -> cvalue E1 ->
      rigid 0 T1 (all A) -> wfe T ->
      chas_type T (cbclos E1 e2) (boxt T1 (all A))
  | ct_eq: forall T e A B,
      chas_type T e A -> teq T A B T -> chas_type T e B
  | clt_nil: forall T, wfe T -> chas_type T cunit top
  | clt_conse: forall T E T1 e A,
      chas_type T E T1 -> lshape T1 -> chas_type (T +++ T1) e A ->
      chas_type T (cmerge E e) (T1 & A)
  | clt_const: forall T T1 E A,
      chas_type T E T1 -> lshape T1 -> wft (T +++ T1) A ->
      chas_type T (ctmerge E A) (T1 &= A)
  | ct_rec: forall T l e A, chas_type T e A -> chas_type T (crec l e) (rcd l A)
  | ct_trproj : forall T e T1 l A,
      chas_type T e T1 -> rlk T1 l A -> chas_type T (crproj e l) A.

#[export] Hint Constructors cvalue chas_type : core.


Inductive ctrans_e: term -> cexp -> Prop :=
  | cte_var: forall n, ctrans_e (fvar n) (cvar n)
  | cte_lit: forall n, ctrans_e (flit n) (clit n)
  | cte_abs: forall t e A A1,
      ctrans_e t e ->
      trans_t A1 A ->
      ctrans_e (fabs t) (clam A e)
  | cte_app: forall t1 t2 e1 e2,
      ctrans_e t1 e1 -> ctrans_e t2 e2 -> ctrans_e (fapp t1 t2) (capp e1 e2)
  | cte_tabs: forall t e, ctrans_e t e -> ctrans_e (ftabs t) (cblam e)
  | cte_tapp: forall t e A A1,
      ctrans_e t e -> trans_t A A1 -> ctrans_e (ftapp t A) (ctapp e A1).
#[export] Hint Constructors ctrans_e : core.

(* ---- mirror typ_wfe / typ_ans_wft for chas_type ---- *)
Lemma ctyp_wfe: forall T e A, chas_type T e A -> wfe T.
Proof.
  introv Ht. inductions Ht; try solve [eauto]; try solve [inverts* IHHt].
  - eapply wfe_inv; eauto.
Qed.

Lemma ctyp_ans_wft: forall T e A, chas_type T e A -> wft T A.
Proof.
  introv Ht. inductions Ht; try solve [eauto].
  - unfold wft. forwards~: we_int T rt.
  - unfold wft. eapply getv_wft; eauto.
  - forwards~: ctyp_wfe Ht. forwards~: wfe_evar_eteq H.
    econstructor; eauto. eapply del_wft; eauto. econstructor. eapply del_refl.
  - inverts* IHHt1.
  - econstructor; eauto. forwards~: wft_wfe IHHt. eapply wfe_sinv; eauto.
  - eapply wft_all_mani; eauto.
  - econstructor; eauto. forwards~: wft_wfe IHHt1.
  - forwards~ Hw2: ctyp_wfe Ht2. forwards~: wfe_evar_eteq Hw2.
    econstructor; eauto. econstructor; eauto.
    eapply del_wft; eauto. econstructor. eapply del_refl.
  - forwards~: ctyp_wfe Ht2. econstructor; eauto.
    econstructor; eauto. eapply wfe_sinv; eauto.
  - eapply teq_wft_right; eauto.
  - econstructor; eauto.
  - econstructor; eauto.
  - econstructor; eauto.
  - econstructor; eauto.
  - eapply rl_wft; eauto.
Qed.

Lemma cconserve_relaxed: forall T1 e A1,
  chas_type T1 e A1 -> forall T t,
  trans_env T T1 ->
  ctrans_e t e -> exists A A2,
  teq T1 A1 A2 T1 /\ ftyping T t A /\ trans_t A A2.
Proof.
  introv Ht. induction Ht; introv Hten Hte; try solve [inverts Hte].
  - (* int *) exists fint int. split*. split*. inverts Hte.
    econstructor. eapply wfe2f; eauto.
  - (* var *) forwards~ Hwe: wfe2f H Hten.
    inverts Hte. forwards~ (A0&?&?): get_fget Hten H0.
    exists A0 A. split*. eapply teq_refl; eauto.
    eapply f2wft; eauto. eapply fgetv_wft; eauto.
  - (* lam: SF binder type [Asf] and [trans_t Asf A] come from cte_abs *)
    inverts Hte.
    match goal with
    | Hr: ctrans_e _ e, Htt: trans_t ?Asf A |- _ =>
      forwards~ (A2 & A3 & Hteqb & Hftb & Httb): IHHt (fevar Asf :: T0) Hr;
      exists (farr Asf A2) (arr A A3);
      assert (HwfA: wft T A) by (forwards~ Hw: teq_wfe_left Hteqb; eapply wfe_evar_eteq; exact Hw);
      assert (Hdel: del_evar (T & A) T) by (econstructor; eapply del_refl; eauto);
      splits;
      [ econstructor;
          [ eapply teq_refl; exact HwfA
          | eapply teq_sym; eapply del_eq; [| exact Hdel];
            eapply teq_sym; eapply del_eq; [exact Hteqb | exact Hdel] ]
      | econstructor; exact Hftb
      | econstructor; [ exact Htt | exact Httb ] ]
    end.
  - (* app *) inverts Hte.
    forwards~ (C&A1&?&?&?): IHHt1 Hten H2.
    forwards~ (D&A2&?&?&?): IHHt2 Hten H3.
    forwards~ (D1&D2&?): teq_arr_tt H H1 Hten. subst.
    inverts H1. inverts H.
    forwards~: teq_tt_eq Hten H6 H10. eapply teq_trans; eauto; eapply teq_sym; eauto. subst.
    forwards~: tt_det_pre H6 H10. subst.
    exists B0 D2. split*.
  - (* blam *) inverts Hte.
    forwards~ (C&A1&?&?&?): IHHt (fetvar :: T0) H1.
    exists (fall C) (all A1). split*.
  - (* tapp *) inverts Hte.
    forwards~ (C&A1&?&?&?): IHHt Hten H3.
    forwards~ (D&?): teq_all_tt H0 H2 Hten. subst.
    inverts H2.
    exists (tsubst A1 0 A0) (tsubst2 D 0 A).
    split.
    2: {
      split.
      econstructor; eauto. eapply wft2f; eauto.
      eapply tt_tsubsst; eauto.
    }
    econstructor. inverts H0.
    eapply relate_gen with (B1 := A1) (C1 := A0);
      [ eassumption | eapply tten_all_abs; eauto | eassumption | eassumption | eassumption ].
  - (* teq *) forwards~ (C&A2&?&?&?): IHHt Hten Hte.
    exists C A2. split*.
    eapply teq_trans; eauto. eapply teq_sym; eauto.
Qed.

Lemma cconserve: forall T1 e A1,
  chas_type T1 e A1 -> forall T t A,
  trans_env T T1 ->
  ctrans_e t e ->
  trans_t A A1 ->
  ftyping T t A.
Proof.
  introv Ht Hte He Htt.
  forwards~ (A3&A2&?&?&?): cconserve_relaxed Ht Hte He.
  forwards~: teq_tt_eq H Hte Htt H1. subst.
  forwards~: tt_det_pre Htt H1. subst. eauto.
Qed.



Fixpoint cerase (e : cexp) : exp :=
  match e with
  | clit i       => lit i
  | cvar n       => var n
  | clam _ e     => lam (cerase e)         (* drop the binder annotation *)
  | cbox e1 e2   => box (cerase e1) (cerase e2)
  | capp e1 e2   => app (cerase e1) (cerase e2)
  | cblam e      => blam (cerase e)
  | cclos e1 e2  => clos (cerase e1) (cerase e2)
  | cbclos e1 e2 => bclos (cerase e1) (cerase e2)
  | ctapp e A    => tapp (cerase e) A
  | crec l e     => rec l (cerase e)
  | crproj e l   => rproj (cerase e) l
  | cunit        => unit
  | cmerge e1 e2 => merge (cerase e1) (cerase e2)
  | ctmerge e A  => tmerge (cerase e) A
  end.

Lemma ctrans_cerase: forall t e, ctrans_e t e -> trans_e t (cerase e).
Proof. introv H. inductions H; simpl; econstructor; eauto. Qed.

Lemma cdyn_conserve: forall e v,
  mstep unit (cerase e) v ->
  value v -> forall t A A1,
  ctrans_e t e ->
  trans_t A1 A ->
  chas_type top e A -> exists w,
  mred t w /\ resrel w v.
Proof.
  intros.
  forwards~ Hft: cconserve H3 te_nil H1 H2.
  eapply dyn_conserve_small; eauto.
  - eapply ctrans_cerase; eauto.
  - eapply typed_closed_t; eauto.
  - eapply typed_closed; eauto.
Qed.

Lemma ccomplete: forall T t A,
  ftyping T t A -> forall T1 A1,
  trans_env T T1 ->
  trans_t A A1 ->
  exists e, ctrans_e t e /\ chas_type T1 e A1.
Proof.
  introv Ht. inductions Ht; introv Hten Htt.
  - (* T_Lit *) inverts Htt. exists (clit i). split. econstructor.
    econstructor. eapply f2wfe; eauto.
  - (* T_Var *) forwards~ (A0&Hg&Htt0): fget_get Hten H0.
    forwards~: tt_det Htt Htt0. subst.
    exists (cvar x). split. econstructor. econstructor; eauto. eapply f2wfe; eauto.
  - (* T_Abs *) inverts Htt.
    match goal with
    | Hbind: trans_t _ ?Afe, Hcod: trans_t _ ?Bfe |- exists e, _ /\ chas_type _ e (arr ?Afe ?Bfe) =>
      forwards~ (e' & Hce & Hct): IHHt (T1 & Afe) (te_cons1 Hbind Hten) Hcod;
      exists (clam Afe e'); split; econstructor; eauto
    end.
  - (* T_App *) forwards~ (A'&HA'): trans_t_ex A1.
    forwards~ Harr: tt_arr HA' Htt.
    forwards~ (e1 & Hce1 & Hct1): IHHt1 Hten Harr.
    forwards~ (e2 & Hce2 & Hct2): IHHt2 Hten HA'.
    exists (capp e1 e2). split; econstructor; eauto.
  - (* T_Tabs *) inverts Htt as Hcod.
    forwards~ (e' & Hce & Hct): IHHt (T1 &s) (te_cons Hten) Hcod.
    exists (cblam e'). split; econstructor; eauto.
  - (* T_Tapp *) forwards~ (A4 & HA4): trans_t_ex A1.
    forwards~ (e' & Hce & Hct): IHHt Hten (tt_all HA4).
    forwards~ (A2fe & HA2fe): trans_t_ex A2.
    forwards~ Hwt: f2wft H Hten HA2fe.
    exists (ctapp e' A2fe). split.
    + econstructor; eauto.
    + eapply ct_eq.
      * econstructor; eauto.
      * forwards~ Hts: tt_tsubsst HA4 HA2fe 0.
        forwards~: tt_det Htt Hts. subst.
        econstructor.
        forwards~ Hwt2: ctyp_ans_wft Hct. inverts Hwt2.
        eapply relate_gen with (B1 := A1) (C1 := A2);
          [ eapply teq_refl; unfold wft; eassumption
          | eapply tten_all_abs; eauto
          | exact HA4 | exact HA2fe | exact Hwt ].
Qed.

