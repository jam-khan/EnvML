Require Import LibTactics. 
From Stdlib Require Import Arith.
From Stdlib Require Import Lia. 
Require Import Stdlib.Lists.List. 
Require Import Stdlib.Classes.EquivDec. 
From Stdlib Require Import Strings.String.
Import ListNotations.
Set Implicit Arguments.

(* -------------------------//-------------------------- *)
Inductive mode :=
  | non : mode
  | rt  : mode.
  
Inductive typ :=
  | int  : typ
  | tvar : nat -> typ
  | arr  : typ -> typ -> typ
  | all : typ -> typ
  | boxt : typ -> typ -> typ
  | mani : typ -> typ -> typ
  | rcd : string -> typ -> typ
  | top : typ
  | and: typ -> mode -> typ -> typ
  | ands: typ -> typ.

Notation "A1 & A2" := (and A1 non A2) (at level 80).
Notation "A1 &= A2" := (and A1 rt A2) (at level 80).
Notation "A &s" := (ands A) (at level 80).

Inductive check : typ -> nat -> Prop :=
  | check_evar : forall X T A,
      check T X ->
      check (T & A) X
  | check_eteq : forall X T A,
      check T X ->
      check (T &= A) (S X)
  | check_zero : forall T,
      check (T &s) 0 
  | check_etvar : forall X T,
      check T X ->
      check (T &s) (S X). 

Fixpoint keyLen (T : typ) : nat :=
  match T with
  | T1 & _ => keyLen T1
  | T1 &s => 1 + keyLen T1
  | T1 &= _ => 1 + keyLen T1
  | _ => 0
  end.

Fixpoint tshift (X : nat) (A : typ) {struct A} : typ :=
  match A with
  | tvar Y      => tvar (if le_gt_dec X Y then 1 + Y else Y)
  | int         => int
  | arr A1 A2   => arr (tshift X A1) (tshift X A2)
  | all A2   => all (tshift (1 + X) A2)
  | boxt T A1   => boxt T A1
  | mani A1 A2  => mani (tshift X A1) (tshift (1 + X) A2)
  | top => top
  | T1 & A2 => (tshift X T1) & (tshift (keyLen T1 + X) A2)
  | T1 &= A2 => (tshift X T1) &= (tshift (keyLen T1 + X) A2)
  | T1 &s => (tshift X T1) &s
  | rcd l A => rcd l (tshift X A)
  end.

Fixpoint mshift (T : typ) (A : typ) {struct T} : typ :=
  match T with
    | T' & _  => mshift T' A
    | T' &s   => (tshift 0) (mshift T' A)
    | T' &= _ => (tshift 0) (mshift T' A)
    | _       => A
  end.

Inductive is_box : typ -> Prop :=
  | isb : forall T A,
      is_box (boxt T A).



Inductive lookt : typ -> nat -> typ -> Prop :=
  | lookt_evar : forall X T A B,
      lookt T X B ->
      lookt (T & A) X B
  | lookt_zero : forall T A,
      lookt (T &= A) 0 ((tshift 0) A)
  | lookt_eteq : forall X T A B,
      lookt T X B ->
      lookt (T &= A) (S X) ((tshift 0) B)
  | lookt_etvar : forall X T B,
      lookt T X B ->
      lookt (T &s) (S X) ((tshift 0) B).


Fixpoint mconcat (T1 T2: typ) : typ :=
  match T2 with
    | and A m B =>
        match A with
          | and _ _ _ => 
              and (mconcat T1 A) m B
          | ands _ => 
              and (mconcat T1 A) m B
          | _ => and T1 m B 
        end
    | A &s =>
        match A with
          | and _ _ _ => 
              (mconcat T1 A) &s 
          | ands _ => 
              (mconcat T1 A) &s 
          | _ => T1 &s 
        end
    | _ => T1
  end.

Notation "T1 +++ T2" := (mconcat T1 T2) (at level 180).

Inductive lshape: typ -> Prop :=
  | lsh_nil: lshape top
  | lsh_evar: forall T A m,
      lshape T ->
      lshape (and T m A)
  | lsh_ands: forall T,
      lshape T ->
      lshape (T &s).

(* rigid T A: A uses no ambient abstract variable. *)
Inductive rigid : nat -> typ -> typ -> Prop :=
  | rigid_int  : forall d T, rigid d T int
  | rigid_top  : forall d T, rigid d T top
  | rigid_bvar : forall d T X, check T X -> X < d -> rigid d T (tvar X)
  | rigid_cvar : forall d T X B, lookt T X B -> rigid d T B -> rigid d T (tvar X)
  | rigid_arr  : forall d T A B, rigid d T A -> rigid d T B -> rigid d T (arr A B)
  | rigid_rcd  : forall d T l A, rigid d T A -> rigid d T (rcd l A)
  | rigid_mani : forall d T A B, rigid (S d) (T &= A) B -> rigid d T (mani A B)
  | rigid_and  : forall d T A m B, rigid d T A -> rigid (d + keyLen A) (T +++ A) B -> rigid d T (and A m B)
  | rigid_ands : forall d T A, rigid d T A -> rigid d T (A &s)
  | rigid_all  : forall d T A, rigid (S d) (T &s) A -> rigid d T (all A)
  | rigid_box  : forall d T T3 A, rigid 0 T3 A -> rigid d T (boxt T3 A).

Inductive wfe: typ -> Prop :=
  | we_nil: wfe top
  | we_tvar: forall T,
      wfe T ->
      wfe (T &s)
  | we_int: forall T m,
      wfe T ->
      wfe (and T m int)
  | we_check: forall T m i,
      wfe T ->
      check T i ->
      wfe (and T m (tvar i))
  | we_get: forall T m i A,
      wfe T ->
      lookt T i A ->
      wfe (and T m (tvar i))
  | we_arr: forall T m A B,
      wfe (T &= A) ->
      wfe (T &= B) ->
      wfe (and T m (arr A B))
  | we_all: forall T m A,
      wfe T ->
      wfe (T &s &= A) ->
      wfe (and T m (all A))
  | we_box: forall T m A T1,
      wfe (T1 &= A) ->
      rigid 0 T1 A ->
      wfe T ->
      wfe (and T m (boxt T1 A))
  | we_mani: forall T m A B,
      wfe (T &= A &= B) ->
      wfe (T &= A) ->
      wfe (and T m (mani A B))
  | we_top: forall T m,
      wfe T ->
      wfe (and T m top)
  | we_and: forall T m1 T1 A2 m2,
      wfe (T &= T1) ->
      wfe ((T +++ T1) &= A2) ->
      lshape T1 ->
      wfe (and T m1 (and T1 m2 A2))
  | we_ands: forall T m1 T1,
      wfe (T &= T1) ->
      lshape T1 ->
      wfe (and T m1 (T1 &s))
  | we_rcd: forall T l A m,
      wfe (T &= A) ->
      wfe (and T m (rcd l A)).

Definition wft (T: typ) (A : typ) : Prop := wfe (T &= A).

Inductive rbox : typ -> typ -> Prop :=
  | rbox_box : forall T T3 A, rbox T (boxt T3 A)
  | rbox_var : forall T X B, lookt T X B -> rbox T B -> rbox T (tvar X).

Inductive teq: typ -> typ -> typ -> typ -> Prop :=
  | eq_int: forall T1 T2, wfe T1 -> wfe T2 -> teq T1 int int T2
  | eq_tvar: forall T1 T2 X,
      wfe T1 -> wfe T2 -> check T1 X -> check T2 X -> teq T1 (tvar X) (tvar X) T2
  | eq_eql: forall T1 T2 X A B, lookt T1 X A -> teq T1 A B T2 -> teq T1 (tvar X) B T2
  | eq_eqr: forall T1 T2 X A B, lookt T2 X B -> teq T1 A B T2 -> teq T1 A (tvar X) T2
  | eq_boxl: forall T1 T2 T3 A B,
      teq T3 A B T2 ->
      wft T1 (boxt T3 A) ->
      teq T1 (boxt T3 A) B T2
  | eq_boxr: forall T1 T2 T3 A B,
      teq T1 A B T3 ->
      wft T2 (boxt T3 B) ->
      teq T1 A (boxt T3 B) T2
  | eq_arr: forall T1 T2 A B C D,
      teq T1 A C T2 -> teq T1 B D T2 -> teq T1 (arr A B) (arr C D) T2
  | eq_all: forall T1 T2 A C, teq (T1 &s) A C (T2 &s) -> teq T1 (all A) (all C) T2
  | eq_manil: forall T1 T2 A B C, teq (T1 &= A) B (tshift 0 C) (T2 &s) -> teq T1 (mani A B) C T2
  | eq_manir: forall T1 T2 A B C, teq (T1 &s) (tshift 0 B) C (T2 &= A) -> teq T1 B (mani A C) T2
  | eq_top: forall T1 T2, wfe T1 -> wfe T2 -> teq T1 top top T2
  | eq_and: forall T1 T2 T3 T4 A B m,
      teq T1 T3 T4 T2 -> lshape T3 -> lshape T4 ->
      teq (T1+++T3) A B (T2+++T4) -> teq T1 (and T3 m A) (and T4 m B) T2
  | eq_ands: forall T1 T2 T3 T4,
      teq T1 T3 T4 T2 -> lshape T3 -> lshape T4 -> teq T1 (T3 &s) (T4 &s) T2
  | eq_rcd: forall T1 T2 l A B, teq T1 A B T2 -> teq T1 (rcd l A) (rcd l B) T2.



#[export]
Hint Constructors mode typ check lookt wfe lshape rigid rbox teq: core.

Hint Mode teq + ! ! + : core.




Lemma wfe_inv: forall T m A,
  wfe (and T m A) ->
  wfe T.
Proof.
  introv Hw. inductions Hw; try solve [inverts* Hw]; try solve [eauto].
Qed.

Lemma wft_wfe: forall T A,
  wft T A ->
  wfe T.
Proof.
  introv Hw. unfold wft in Hw. eapply wfe_inv; eauto.
Qed.


Lemma lookt_check_false: forall T X A,
  lookt T X A -> check T X -> False.
Proof.
  introv Hl. inductions Hl; intros Hc; inverts* Hc.
Qed.

Lemma lookt_det: forall T X A,
  lookt T X A -> forall B,
  lookt T X B ->
  A = B.
Proof.
  introv Ha. inductions Ha; introv Hb; try solve [inverts* Hb].
  - inverts Hb; try solve [eauto].
    + forwards~: IHHa H3. subst. eauto.
  - inverts Hb; try solve [eauto].
    + forwards~: IHHa H1. subst. eauto. 
Qed.

Lemma wfe_sinv: forall T,
  wfe (T &s) ->
  wfe T.
Proof.
  introv Hw. inductions Hw; try solve [inverts* Hw]; try solve [eauto].
Qed.

Lemma teq_sym: forall T1 A B T2,
  teq T1 A B T2 -> 
  teq T2 B A T1.
Proof.
  introv Ht. inductions Ht; eauto.
Qed.


Lemma boxt_wft_inv: forall T T1 A,
  wft T (boxt T1 A) ->
  wft T1 A /\ wfe T /\ wfe T1.
Proof.
  introv Hw. inverts Hw. splits; eauto. eapply wft_wfe; eauto.
Qed.


Lemma wft_box_rigid: forall T T3 A,
  wft T (boxt T3 A) ->
  rigid 0 T3 A.
Proof.
  introv Hw. unfold wft in Hw. inverts Hw. assumption.
Qed.

Lemma wfe_eteq_evar: forall T A,
  wfe (T &= A) ->
  wfe (T & A).
Proof.
  introv Hw. inductions Hw; eauto. 
Qed.

Lemma wfe_evar_eteq: forall T A,
  wfe (T & A) ->
  wfe (T &= A).
Proof.
  introv Hw. inductions Hw; eauto.
Qed.



Lemma keyLen_same: forall T1 X,
  keyLen T1 = keyLen (tshift X T1).
Proof.
  intros T1. inductions T1; intros; try solve [simpl; eauto].
  - destruct m.
    + simpl. forwards~: IHT1_1 X.
     + simpl. forwards~: IHT1_1 X.
Qed.


Lemma tshift_tshift_prop_1 : forall (A : typ) (n n' : nat),
  tshift n (tshift (n + n') A) = tshift (1 + (n + n')) (tshift n A).
Proof.
  intros A. inductions A; intros; try solve [eauto].
  - destruct (le_gt_dec n0 n).
    + unfold tshift. destruct (le_gt_dec (n0 + n') n). 
      * destruct (le_gt_dec n0 (1 + n)); try solve [lia].
        destruct (le_gt_dec n0 n); try solve [lia].
        destruct (le_gt_dec (1 + (n0 + n')) (1 + n)); try solve [lia]. eauto.
      * destruct (le_gt_dec n0 n); try solve [lia].
        destruct (le_gt_dec (1 + (n0 + n')) (1 + n)); try solve [lia]. eauto.
    + unfold tshift. destruct (le_gt_dec (n0 + n') n).
      * destruct (le_gt_dec n0 (1 + n)); try solve [lia].
      * destruct (le_gt_dec n0 n); try solve [lia].
        destruct (le_gt_dec (1 + (n0 + n')) n); try solve [lia]. eauto.
  - simpl.
    rewrite IHA1. simpl.
    rewrite IHA2. simpl. eauto.
  - simpl. 
    forwards~: IHA (S n) n'. simpl in H.
    rewrite H. eauto.
  - simpl. rewrite IHA1. simpl. 
    forwards~: IHA2 (S n) n'. simpl in H.
    rewrite H. eauto.
  - simpl. rewrite IHA. simpl. eauto.
  - destruct m.
    + simpl. rewrite <- keyLen_same.
      rewrite <- keyLen_same. rewrite IHA1.
      forwards~: IHA2 (keyLen A1 + n) n'.
      simpl.
      replace (keyLen A1 + (n + n')) with (keyLen A1 + n + n').
      rewrite H.
      replace (S (keyLen A1 + n + n')) with (keyLen A1 + S (n + n')).
      eauto.
      lia. lia.
    + simpl. rewrite <- keyLen_same.
      rewrite <- keyLen_same. rewrite IHA1.
      forwards~: IHA2 (keyLen A1 + n) n'.
      simpl.
      replace (keyLen A1 + (n + n')) with (keyLen A1 + n + n').
      rewrite H.
      replace (S (keyLen A1 + n + n')) with (keyLen A1 + S (n + n')).
      eauto.
      lia. lia.
  - simpl. rewrite IHA. simpl. eauto.
Qed.

Inductive insert_tvar : nat -> typ -> typ -> Prop :=
  | itv_here2 : forall T,
      insert_tvar 0 T (T &s)
  | itv_var : forall (X : nat) (A : typ) T T',
      insert_tvar X T T' ->
      insert_tvar X (T & A) (T' & (tshift X A))
  | itv_tvar: forall (X : nat) T T',
      insert_tvar X T T' ->
      insert_tvar (S X) (T &s) (T' &s)
  | itv_teq: forall (X : nat) (A : typ) T T',
      insert_tvar X T T' ->
      insert_tvar (S X) (T &= A) (T' &= (tshift X A)).

#[export]
Hint Constructors insert_tvar: core.





Lemma lookt_insert_tvar_ge: forall (X' : nat) T T',
  insert_tvar X' T T' -> forall X,
  X' <= X -> forall A,
  lookt T X A ->
  lookt T' (1 + X) (tshift X' A).
Proof.
  introv Hi. inductions Hi; introv Hl Hk; try solve [eauto]; try solve [invert* Hk].
  - inverts Hk.
    + forwards~: IHHi H0. lia. 
      forwards~: tshift_tshift_prop_1 B 0 X. simpl in H1.
      rewrite <- H1. eapply lookt_etvar; eauto. 
  - inverts Hk.
    + lia.
    + forwards~: IHHi H3. lia. 
      forwards~: tshift_tshift_prop_1 B 0 X. simpl in H0.
      rewrite <- H0. econstructor; eauto.
Qed.

Lemma lookt_insert_tvar_lt: forall (X' : nat) T T',
  insert_tvar X' T T' -> forall X,
  X' > X -> forall A,
  lookt T X A ->
  lookt T' X (tshift X' A).
Proof.
  introv Hi. inductions Hi; introv Hl Hk; try solve [lia]; try solve [eauto]; try solve [invert* Hk].
  - inverts Hk.
    + forwards~: IHHi H0. lia.
      forwards~: tshift_tshift_prop_1 B 0 X. simpl in H1.
      rewrite <- H1. eapply lookt_etvar; eauto.
  - inverts Hk.
    + forwards~: tshift_tshift_prop_1 A 0 X. simpl in H.
      rewrite <- H. econstructor; eauto.
    + forwards~: IHHi H3. lia.
      forwards~: tshift_tshift_prop_1 B 0 X. simpl in H0.
      rewrite <- H0. econstructor; eauto.
Qed.

Lemma check_insert_tvar_ge: forall (X' : nat) T T',
  insert_tvar X' T T' -> forall X,
  X' <= X ->
  check T X ->
  check T' (1 + X).
Proof.
  introv Hi. inductions Hi; introv Hl Hc;
    try solve [replace (1 + X) with (S X) by lia; eapply check_eteq; exact Hc];
    try solve [inverts* Hc].
  - destruct* X0. lia. inverts Hc.
    + eapply check_etvar. eapply IHHi; eauto. lia.
  - destruct* X0. lia. inverts Hc.
    + forwards~: IHHi H0. lia.
Qed.

Lemma check_insert_tvar_lt: forall (X' : nat) T T',
  insert_tvar X' T T' -> forall X,
  X' > X ->
  check T X ->
  check T' X.
Proof.
  introv Hi. inductions Hi; introv Hl Hc; try solve [lia]; try solve [inverts* Hc].
  - destruct* X0. inverts Hc.
    + eapply check_etvar. eapply IHHi; eauto. lia.
  - destruct* X0.
    + inverts Hc.
    + inverts Hc.
      * forwards~: IHHi H0. lia.
Qed.

Inductive ord : typ -> Prop :=
  | ord_int: ord int
  | ord_tvar: forall n, ord (tvar n)
  | ord_arr: forall A1 A2,
      ord (arr A1 A2)
  | ord_all: forall A,
      ord (all A)
  | ord_boxt: forall A1 A2,
      ord (boxt A1 A2)
  | ord_mani: forall A1 A2,
      ord (mani A1 A2)
  | ord_top: ord top
  | ord_rcd: forall l A, 
      ord (rcd l A).

#[export]
Hint Constructors ord: core.

Lemma ord_dec: forall T,
  ord T \/ (exists A m B, T = and A m B) \/ (exists A, T = (A &s)).
Proof.
  intros T. inductions T; eauto.
  - destruct* IHT1; destruct* IHT2.
    + right. left. exists*.
    + right. left. exists*.
    + right. left. exists*.
    + right. left. exists*.
Qed.

Lemma ord_inert: forall A,
  ord A -> forall T,
  (T +++ A) = T.
Proof.
  intros A. inductions A; introv Ho; intros; eauto.
  - inverts* Ho.
  - inverts* Ho.
Qed.

Lemma mcon_cons: forall T T1 A m,
  (and (T +++ T1) m A) = (T +++ (and T1 m A)).
Proof.
  intros. destruct* T1. 
Qed.

Lemma mcon_cons_st: forall T T1,
  ((T +++ T1) &s) = (T +++ (T1 &s)).
Proof.
  intros. destruct* T1. 
Qed.

Lemma check_app: forall T i, check T i -> forall T1, check (T1 +++ T) i.
Proof.
  introv Hc. inductions Hc; introv;
    try solve [rewrite <- mcon_cons; econstructor; eauto];
    try solve [rewrite <- mcon_cons_st; econstructor; eauto].
Qed.

Lemma lookt_app: forall T i A, lookt T i A -> forall T1, lookt (T1 +++ T) i A.
Proof.
  introv Hl. inductions Hl; introv;
    try solve [rewrite <- mcon_cons; econstructor; eauto];
    try solve [rewrite <- mcon_cons_st; econstructor; eauto].
Qed.


Lemma mapp_ass: forall T3 T1 T2,
  ((T1 +++ T2) +++ T3) = (T1 +++ (T2 +++ T3)).
Proof.
  intros T3. inductions T3; intros; 
  try solve [simpl; eauto].
  - destruct m.
    + rewrite <-mcon_cons. rewrite IHT3_1.
      rewrite mcon_cons. rewrite mcon_cons. eauto.
    + rewrite <-mcon_cons. rewrite IHT3_1.
      rewrite mcon_cons. rewrite mcon_cons. eauto.
  - rewrite <-mcon_cons_st. rewrite IHT3.
    rewrite mcon_cons_st. rewrite mcon_cons_st. eauto.
Qed.

Lemma wfe_app: forall T2 T1, wfe T2 -> wfe T1 -> wfe (T1 +++ T2).
Proof.
  introv Hw2. inductions Hw2; introv Hw1;
    try solve [simpl; eauto];
    try solve [rewrite <- mcon_cons_st; eapply we_tvar; eauto];
    try solve [rewrite <- mcon_cons; eapply we_get; eauto using lookt_app];
    try solve [rewrite <- mcon_cons; eapply we_check; eauto using check_app];
    try solve [rewrite <- mcon_cons;
               first [eapply we_int | eapply we_arr | eapply we_all | eapply we_box
                     | eapply we_mani | eapply we_top | eapply we_and | eapply we_ands
                     | eapply we_rcd];
               match type of Hw1 with wfe ?S =>
                 repeat rewrite mapp_ass;
                 repeat (match goal with
                         | |- context[and (S +++ ?X) ?m ?A] => rewrite mcon_cons
                         | |- context[(S +++ ?X) &s] => rewrite mcon_cons_st
                         end)
               end;
               eauto using check_app, lookt_app].
Qed.

(* wft preserved when an OUTER frame is prepended (for the new prepend box rules). *)
Lemma wft_prepend: forall T A, wft T A -> forall T0, wfe T0 -> wft (T0 +++ T) A.
Proof.
  introv Hw Hw0. unfold wft in *. rewrite mcon_cons. eapply wfe_app; eauto.
Qed.

Lemma tshift_and: forall T1 T2 m X,
  tshift X (and T1 m T2) = and (tshift X T1) m (tshift (keyLen T1 + X) T2).
Proof.
  intros T1. inductions T1; intros; try solve [destruct m; simpl; eauto].
  - destruct m0; simpl; eauto.
Qed.

Lemma tshift_st: forall T1 X,
  tshift X (T1 &s) = ((tshift X T1) &s).
Proof.
  intros T1. inductions T1; intros X; try solve [simpl; eauto].
Qed.


Fixpoint tnotin (k : nat) (A : typ) {struct A} : Prop :=
  match A with
  | tvar Y      => Y <> k
  | int         => True
  | arr A1 A2   => tnotin k A1 /\ tnotin k A2
  | all A2      => tnotin (S k) A2
  | boxt T A1   => True
  | mani A1 A2  => tnotin k A1 /\ tnotin (S k) A2
  | top         => True
  | and T1 _ A2 => tnotin k T1 /\ tnotin (keyLen T1 + k) A2
  | T1 &s       => tnotin k T1
  | rcd l A     => tnotin k A
  end.


Lemma tnotin_image: forall A k, tnotin k A -> exists C, A = tshift k C.
Proof.
  induction A; introv Hn; simpl in Hn.
  - exists int. reflexivity.
  - (* tvar n *) destruct (lt_eq_lt_dec n k) as [[Hlt|Heq]|Hgt].
    + exists (tvar n). simpl. destruct (le_gt_dec k n); [lia | reflexivity].
    + subst. exfalso. apply Hn. reflexivity.
    + exists (tvar (n - 1)). simpl. destruct (le_gt_dec k (n-1)); [|lia].
      f_equal. lia.
  - destruct Hn as [H1 H2]. forwards (C1&E1): IHA1 H1. forwards (C2&E2): IHA2 H2.
    exists (arr C1 C2). simpl. subst. reflexivity.
  - forwards (C&E): IHA Hn. exists (all C). simpl. subst. reflexivity.
  - (* boxt: tshift fixes it *) match goal with |- exists _, ?B = _ => exists B end. reflexivity.
  - destruct Hn as [H1 H2]. forwards (C1&E1): IHA1 H1. forwards (C2&E2): IHA2 H2.
    exists (mani C1 C2). simpl. subst. reflexivity.
  - forwards (C&E): IHA Hn. match goal with |- exists _, rcd ?l _ = _ => exists (rcd l C) end. simpl. subst. reflexivity.
  - exists top. reflexivity.
  - destruct Hn as [H1 H2]. forwards (C1&E1): IHA1 H1.
    assert (HkL: keyLen A1 = keyLen C1) by (rewrite E1; symmetry; eapply keyLen_same).
    rewrite HkL in H2. forwards (C2&E2): IHA2 H2.
    exists (and C1 m C2). rewrite tshift_and. subst. reflexivity.
  - forwards (C&E): IHA Hn. exists (C &s). rewrite tshift_st. subst. reflexivity.
Qed.

Lemma tnotin_tshift_S: forall C i j, j <= i -> tnotin (S i) (tshift j C) -> tnotin i C.
Proof.
  induction C; introv Hle Hn; simpl in *.
  - (* int *) exact I.
  - (* tvar n *) destruct (le_gt_dec j n); simpl in Hn; lia.
  - (* arr *) destruct Hn as [H1 H2]. split;
      [ eapply IHC1; [ exact Hle | exact H1 ] | eapply IHC2; [ exact Hle | exact H2 ] ].
  - (* all *) eapply IHC with (j := S j); [ lia | exact Hn ].
  - (* boxt *) exact I.
  - (* mani *) destruct Hn as [H1 H2]. split;
      [ eapply IHC1; [ exact Hle | exact H1 ]
      | eapply IHC2 with (j := S j); [ lia | exact H2 ] ].
  - (* rcd *) eapply IHC; [ exact Hle | exact Hn ].
  - (* top *) exact I.
  - (* and _ m _ *) destruct m; simpl in Hn; destruct Hn as [H1 H2]; split;
      first [ eapply IHC1; [ exact Hle | exact H1 ]
            | rewrite <- (keyLen_same C1 j) in H2;
              replace (keyLen C1 + S i) with (S (keyLen C1 + i)) in H2 by lia;
              eapply IHC2 with (j := keyLen C1 + j); [ lia | exact H2 ] ].
  - (* ands *) eapply IHC; [ exact Hle | exact Hn ].
Qed.

Lemma insert_tvar_env: forall X T T',
  insert_tvar X T T' -> forall T1,
  insert_tvar (keyLen T1 + X) (T +++ T1) (T' +++ tshift X T1).
Proof.
  introv Hi. intros. gen T T'. inductions T1; introv Hi; 
  try solve [simpl; eauto].
  - rewrite <- mcon_cons. 
    rewrite tshift_and. rewrite <- mcon_cons.
    destruct m.
    + replace (keyLen (T1_1 & T1_2) + X) with (keyLen T1_1 + X).
      eauto.
      simpl. eauto.
    + replace (keyLen (T1_1 &= T1_2) + X) with (S (keyLen T1_1 + X)).
      eauto.
      simpl. eauto.
  - rewrite <- mcon_cons_st. 
    rewrite tshift_st. repeat rewrite <- mcon_cons_st.
    replace (keyLen (T1 &s) + X) with (S (keyLen T1 + X)).
    eauto.
    simpl. eauto.
Qed.

Lemma wfe_mcon: forall A T,
  wfe (T +++ A) ->
  lshape A ->
  wfe (T &= A).
Proof.
  intros A. inductions A; introv Hw Hl;
  try solve [inverts* Hl].
  - inverts Hl. 
    rewrite <- mcon_cons in Hw.
    econstructor; eauto.
    eapply IHA1; eauto. eapply wfe_inv; eauto.
    inverts* Hw.
  - inverts Hl. rewrite <- mcon_cons_st in Hw.
    econstructor; eauto.
    eapply IHA; eauto. eapply wfe_sinv; eauto.
Qed.

Lemma mode_both: forall T B,
  wfe (T &= B) -> forall m,
  wfe (and T m B).
Proof.
  intros. destruct* m. eapply wfe_eteq_evar; eauto.
Qed.

Lemma wfe_to_mcon: forall A T m B,
  wfe (T &= and A m B) ->
  wfe (T +++ and A m B).
Proof.
  intros A. inductions A; introv Hw; try solve [inverts Hw; simpl in *; eapply mode_both; eauto].
Qed.

Lemma lshape_tshift: forall A,
  lshape A -> forall X,
  lshape (tshift X A).
Proof.
  introv Hl. inductions Hl; intros X; try solve [simpl; eauto].
  - destruct m; simpl; eauto.
Qed.

Lemma wfe_to_mcon_st: forall A T,
  wfe (T &= (A &s)) ->
  wfe (T +++ A &s).
Proof.
  intros A. inductions A; introv Hw. 
  1-8: try solve [inverts Hw; simpl in *; econstructor; eapply wfe_inv; eauto].
  - inverts Hw. inverts H3.
    rewrite <- mcon_cons_st.
    econstructor. eapply wfe_to_mcon; eauto.
  - inverts Hw.
    rewrite <- mcon_cons_st.
    econstructor. eauto.
Qed. 

Lemma wfe_to_mcon_all: forall A T,
  wfe (T &= A) ->
  wfe (T +++ A).
Proof.
  intros A. inductions A; introv Hw; try solve [inverts Hw; simpl in *; eauto].
  - simpl. eapply wfe_inv; eauto.
  - simpl. eapply wfe_inv; eauto.
  - simpl. eapply wfe_inv; eauto.
  - eapply wfe_to_mcon; eauto.
  - eapply wfe_to_mcon_st; eauto.
Qed. 

Lemma insert_tvar_wft: forall (A : typ) (X : nat) T T',
  insert_tvar X T T' ->
  wfe T' ->
  wft T A -> 
  wft T' (tshift X A).
Proof.
  intros A. inductions A; introv Hi He Hw; unfold wft in *; try solve [eauto]; try solve [simpl; inverts* Hw].
  - simpl. 
    inverts Hw. 
    (* check *)
    + destruct (le_gt_dec X n).
      * forwards~: check_insert_tvar_ge Hi n.
      * forwards~: check_insert_tvar_lt Hi n.
    (* lookt *) 
    + destruct (le_gt_dec X n).
      * forwards~: lookt_insert_tvar_ge Hi H3.
        eapply we_get; eauto.
      * forwards~: lookt_insert_tvar_lt Hi H3.
        eapply we_get; eauto.
  - simpl. inverts Hw.
    forwards~: IHA1 Hi H4.
    forwards~: IHA2 (S X) (T &= A1) (T' &= (tshift X A1)).
  - destruct m.
    + simpl. inverts Hw.
      econstructor; eauto; try solve [eapply lshape_tshift; eauto].
      eapply IHA2; eauto.
      eapply insert_tvar_env; eauto.
      forwards~: wfe_inv H5.

      forwards~ [?|[?|?]]: ord_dec A1.
      * inverts H0; subst; simpl; eauto.
      * destruct H0 as (A & m & B & ?). subst.
        forwards~: wfe_mcon H. inverts* H6.
        forwards~: IHA1 Hi H0.
        
        rewrite tshift_and in H1. rewrite tshift_and.
        eapply wfe_to_mcon; eauto.
      * destruct H0 as (A & ?). subst.
        forwards~: wfe_mcon H.
        forwards~: IHA1 Hi H0.
        
        rewrite tshift_st in H1. rewrite tshift_st.
        eapply wfe_to_mcon_st; eauto.
    + simpl. inverts Hw.
      econstructor; eauto; try solve [eapply lshape_tshift; eauto].
      eapply IHA2; eauto.
      eapply insert_tvar_env; eauto.
      forwards~: wfe_inv H5.

      forwards~ [?|[?|?]]: ord_dec A1.
      * inverts H0; subst; simpl; eauto.
      * destruct H0 as (A & m & B & ?). subst.
        forwards~: wfe_mcon H. inverts* H6.
        forwards~: IHA1 Hi H0.
        
        rewrite tshift_and in H1. rewrite tshift_and.
        eapply wfe_to_mcon; eauto.
      * destruct H0 as (A & ?). subst.
        forwards~: wfe_mcon H.
        forwards~: IHA1 Hi H0.
        
        rewrite tshift_st in H1. rewrite tshift_st.
        eapply wfe_to_mcon_st; eauto.
  - simpl. inverts Hw.
    econstructor; eauto.
    eapply lshape_tshift; eauto.
Qed.


Lemma check_insert_tvar_ge_rev: forall (X' : nat) T T',
  insert_tvar X' T T' -> forall X,
  X' <= X -> check T' (1 + X) -> check T X.
Proof.
  introv Hi. inductions Hi; introv Hl Hc.
  - inverts Hc; eauto.
  - inverts Hc. eapply check_evar. eapply IHHi; eauto.
  - destruct X0; [lia|]. inverts Hc. eapply check_etvar. eapply IHHi; eauto. lia.
  - destruct X0; [lia|]. inverts Hc. eapply check_eteq. eapply IHHi; eauto. lia.
Qed.

Lemma check_insert_tvar_lt_rev: forall (X' : nat) T T',
  insert_tvar X' T T' -> forall X,
  X' > X -> check T' X -> check T X.
Proof.
  introv Hi. inductions Hi; introv Hl Hc.
  - lia.
  - inverts Hc. eapply check_evar. eapply IHHi; eauto.
  - destruct X0.
    + eapply check_zero.
    + inverts Hc. eapply check_etvar. eapply IHHi; eauto. lia.
  - destruct X0.
    + inverts Hc.
    + inverts Hc. eapply check_eteq. eapply IHHi; eauto. lia.
Qed.

Lemma lookt_insert_tvar_ge_rev: forall (X' : nat) T T',
  insert_tvar X' T T' -> forall Y B,
  X' <= Y -> lookt T' (1 + Y) B -> exists A, lookt T Y A.
Proof.
  introv Hi. inductions Hi; introv Hl Hk.
  - inverts Hk; eauto.
  - inverts Hk as Hk. forwards (A0&?): IHHi Hl Hk. eauto.
  - destruct Y as [|Y]; [lia|]. inverts Hk as Hk.
    assert (Hle: X <= Y) by lia. forwards (A0&?): IHHi Hle Hk. eauto.
  - destruct Y as [|Y]; [lia|]. inverts Hk as Hk.
    assert (Hle: X <= Y) by lia. forwards (A0&?): IHHi Hle Hk. eauto.
Qed.

Lemma lookt_insert_tvar_lt_rev: forall (X' : nat) T T',
  insert_tvar X' T T' -> forall Y B,
  X' > Y -> lookt T' Y B -> exists A, lookt T Y A.
Proof.
  introv Hi. inductions Hi; introv Hl Hk.
  - lia.
  - inverts Hk as Hk. forwards (A0&?): IHHi Hl Hk. eauto.
  - destruct Y as [|Y].
    + inverts Hk.
    + inverts Hk as Hk. assert (Hlt: X > Y) by lia. forwards (A0&?): IHHi Hlt Hk. eauto.
  - destruct Y as [|Y].
    + inverts Hk; eauto.
    + inverts Hk as Hk. assert (Hlt: X > Y) by lia. forwards (A0&?): IHHi Hlt Hk. eauto.
Qed.

Lemma lshape_tshift_rev: forall A X, lshape (tshift X A) -> lshape A.
Proof.
  intros A. inductions A; introv Hl; simpl in Hl;
    try solve [inverts Hl]; try solve [eauto].
  - destruct m; simpl in Hl; inverts Hl; econstructor; eapply IHA1; eauto.
  - inverts Hl. econstructor. eapply IHA; eauto.
Qed.

Lemma insert_tvar_wft_rev: forall (A : typ) (X : nat) T T',
  insert_tvar X T T' -> wfe T ->
  wft T' (tshift X A) -> wft T A.
Proof.
  intros A. inductions A; introv Hi He Hw; unfold wft in *; simpl in Hw;
    try solve [eauto]; try solve [inverts* Hw].
  - (* tvar *) destruct (le_gt_dec X n); inverts Hw.
    + eapply we_check; eauto. eapply check_insert_tvar_ge_rev; eauto.
    + forwards (A0&?): lookt_insert_tvar_ge_rev Hi H3; [lia|]. eapply we_get; eauto.
    + eapply we_check; eauto. eapply check_insert_tvar_lt_rev; eauto.
    + forwards (A0&?): lookt_insert_tvar_lt_rev Hi H3; [lia|]. eapply we_get; eauto.
  - (* mani *) inverts Hw.
    assert (HwA1: wfe (T &= A1)) by (eapply IHA1; eauto).
    eapply we_mani; [ | eapply HwA1 ].
    eapply IHA2 with (X := S X) (T := T &= A1) (T' := T' &= tshift X A1);
      [ eapply itv_teq; eauto | eapply HwA1 | eauto ].
  - (* and *) destruct m; simpl in Hw; inverts Hw;
      (assert (HwA1: wfe (T &= A1)) by (eapply IHA1; eauto));
      (eapply we_and;
        [ exact HwA1
        | eapply IHA2 with (X := keyLen A1 + X) (T := T +++ A1) (T' := T' +++ tshift X A1);
            [ eapply insert_tvar_env; eauto | eapply wfe_to_mcon_all; exact HwA1 | eassumption ]
        | eapply lshape_tshift_rev; eassumption ]).
  - (* ands *) simpl in Hw. inverts Hw.
    eapply we_ands; [ eapply IHA; eauto | eapply lshape_tshift_rev; eassumption ].
Qed.


Lemma itvar_wfe_rev: forall X T T',
  insert_tvar X T T' -> wfe T' -> wfe T.
Proof.
  introv Hi. inductions Hi; introv Hw.
  - eapply wfe_sinv; exact Hw.
  - forwards Hwt': wfe_inv Hw. forwards HwT: IHHi Hwt'.
    forwards Hwft': wfe_evar_eteq Hw.
    forwards Hwft: insert_tvar_wft_rev Hi HwT Hwft'.
    eapply wfe_eteq_evar; exact Hwft.
  - forwards Hwt': wfe_sinv Hw. forwards HwT: IHHi Hwt'. eapply we_tvar; exact HwT.
  - forwards Hwt': wfe_inv Hw. forwards HwT: IHHi Hwt'.
    forwards Hwft: insert_tvar_wft_rev Hi HwT Hw.
    exact Hwft.
Qed.

(* ---- RELOCATED teq_wft block (needs insert_tvar_wft_rev above) ----------- *)
Lemma teq_wft: forall T1 A B T2,
  teq T1 A B T2 ->
  wft T1 A /\ wft T2 B.
Proof.
  introv Ht. inductions Ht; try solve [unfold wft in *; split*];
    try solve [unfold wft in *; split; solve [eapply we_box; eauto | eauto]].
  - (* eq_eql *) inverts IHHt. split. eapply we_get; eauto. eapply wft_wfe; eauto. assumption.
  - (* eq_eqr *) inverts IHHt. split. assumption. eapply we_get; eauto. eapply wft_wfe; eauto.
  - (* eq_all *) inverts IHHt.
    split; eapply we_all; eauto; [eapply wfe_sinv; eapply wft_wfe | eapply wfe_sinv; eapply wft_wfe]; eauto.
  - (* eq_manil: IH = wft (T1&=A) B /\ wft (T2&s) (tshift 0 C) *)
    destruct IHHt as [HBl HCr]. split.
    + forwards~ Hwa: wft_wfe HBl. eapply we_mani; eauto.
    + eapply insert_tvar_wft_rev; [eapply itv_here2 | eapply wfe_sinv; eapply wft_wfe; exact HCr | exact HCr].
  - (* eq_manir: IH = wft (T1&s) (tshift 0 B) /\ wft (T2&=A) C *)
    destruct IHHt as [HBl HCr]. split.
    + eapply insert_tvar_wft_rev; [eapply itv_here2 | eapply wfe_sinv; eapply wft_wfe; exact HBl | exact HBl].
    + forwards~ Hwa: wft_wfe HCr. eapply we_mani; eauto.
Qed.

Lemma teq_wft_left: forall T1 A B T2,
  teq T1 A B T2 ->
  wft T1 A.
Proof.
  intros. forwards~: teq_wft H. destruct* H0.
Qed.

Lemma teq_wft_right: forall T1 A B T2,
  teq T1 A B T2 ->
  wft T2 B.
Proof.
  intros. forwards~: teq_wft H. destruct* H0.
Qed.

Lemma teq_wfe: forall T1 A B T2,
  teq T1 A B T2 ->
  wfe T1 /\ wfe T2.
Proof.
  introv Ht.
  forwards~: teq_wft Ht. destruct* H. split; try eapply wft_wfe; eauto.
Qed.

Lemma teq_wfe_left: forall T1 A B T2,
  teq T1 A B T2 ->
  wfe T1.
Proof.
  introv Ht. forwards~: teq_wfe Ht. destruct* H.
Qed.

Lemma teq_wfe_right: forall T1 A B T2,
  teq T1 A B T2 ->
  wfe T2.
Proof.
  introv Ht. forwards~: teq_wfe Ht. destruct* H.
Qed.



Inductive insert_teq : nat -> typ -> typ -> Prop :=
  | it_here2 : forall A T, 
      insert_teq 0 T (T &= A)
  | it_var : forall (X : nat) (A : typ) T T',
      insert_teq X T T' ->
      insert_teq X (T & A) (T' & (tshift X A))
  | it_tvar: forall (X : nat) T T',
      insert_teq X T T' ->
      insert_teq (S X) (T &s) (T' &s)
  | it_teq: forall (X : nat) (A : typ) T T',
      insert_teq X T T' ->
      insert_teq (S X) (T &= A) (T' &= (tshift X A)).

#[export]
Hint Constructors insert_teq: core.




Lemma lookt_insert_teq_ge: forall (X' : nat) T T',
  insert_teq X' T T' -> forall X,
  X' <= X -> forall A,
  lookt T X A ->
  lookt T' (1 + X) (tshift X' A).
Proof.
  introv Hi. inductions Hi; introv Hl Hk; try solve [eauto]; try solve [invert* Hk].
  - inverts Hk.
    + forwards~: IHHi H0. lia. 
      forwards~: tshift_tshift_prop_1 B 0 X. simpl in H1.
      rewrite <- H1. eapply lookt_etvar; eauto. 
  - inverts Hk.
    + lia.
    + forwards~: IHHi H3. lia. 
      forwards~: tshift_tshift_prop_1 B 0 X. simpl in H0.
      rewrite <- H0. econstructor; eauto.
Qed.

Lemma lookt_insert_teq_lt: forall (X' : nat) T T',
  insert_teq X' T T' -> forall X,
  X' > X -> forall A,
  lookt T X A ->
  lookt T' X (tshift X' A).
Proof.
  introv Hi. inductions Hi; introv Hl Hk; try solve [eauto]; try solve [invert* Hk].
  - lia.
  - inverts Hk.
    + forwards~: IHHi H0. lia. 
      forwards~: tshift_tshift_prop_1 B 0 X. simpl in H1.
      rewrite <- H1. eapply lookt_etvar; eauto. 
  - inverts Hk.
    + forwards~: tshift_tshift_prop_1 A 0 X. simpl in H.
      rewrite <- H. econstructor; eauto.
    + forwards~: IHHi H3. lia.
      forwards~: tshift_tshift_prop_1 B 0 X. simpl in H0.
      rewrite <- H0. econstructor; eauto.
Qed.

Lemma check_insert_teq_ge: forall (X' : nat) T T',
  insert_teq X' T T' -> forall X,
  X' <= X ->
  check T X ->
  check T' (1 + X).
Proof.
  introv Hi. inductions Hi; introv Hl Hc; try solve [inverts* Hc].
  - destruct* X0. lia. inverts Hc.
    + eapply check_etvar. eapply IHHi; eauto. lia.
  - destruct* X0. lia. inverts Hc.
    + forwards~: IHHi H0. lia. 
Qed.

Lemma check_insert_teq_lt: forall (X' : nat) T T',
  insert_teq X' T T' -> forall X,
  X' > X ->
  check T X ->
  check T' X.
Proof.
  introv Hi. inductions Hi; introv Hl Hc; try solve [inverts* Hc].
  - lia.
  - destruct* X0. inverts Hc.
    + eapply check_etvar. eapply IHHi; eauto. lia.
  - destruct* X0.
    + inverts Hc. 
    + inverts Hc. 
      * forwards~: IHHi H0. lia.
Qed.

Lemma insert_teq_env: forall X T T',
  insert_teq X T T' -> forall T1,
  insert_teq (keyLen T1 + X) (T +++ T1) (T' +++ tshift X T1).
Proof.
  introv Hi. intros. gen T T'. inductions T1; introv Hi; 
  try solve [simpl; eauto].
  - rewrite <- mcon_cons. 
    rewrite tshift_and. rewrite <- mcon_cons.
    destruct m.
    + replace (keyLen (T1_1 & T1_2) + X) with (keyLen T1_1 + X).
      eauto.
      simpl. eauto.
    + replace (keyLen (T1_1 &= T1_2) + X) with (S (keyLen T1_1 + X)).
      eauto.
      simpl. eauto.
  - rewrite <- mcon_cons_st. 
    rewrite tshift_st. repeat rewrite <- mcon_cons_st.
    replace (keyLen (T1 &s) + X) with (S (keyLen T1 + X)).
    eauto.
    simpl. eauto.
Qed.

Lemma insert_teq_wft: forall (A : typ) (X : nat) T T',
  insert_teq X T T' ->
  wfe T' ->
  wft T A -> 
  wft T' (tshift X A).
Proof.
  intros A. inductions A; introv Hi He Hw; unfold wft in *; try solve [eauto]; try solve [simpl; inverts* Hw].
  - simpl. 
    inverts Hw. 
    (* check *)
    + destruct (le_gt_dec X n).
      * forwards~: check_insert_teq_ge Hi n.
      * forwards~: check_insert_teq_lt Hi n.
    (* lookt *) 
    + destruct (le_gt_dec X n).
      * forwards~: lookt_insert_teq_ge Hi H3.
        eapply we_get; eauto.
      * forwards~: lookt_insert_teq_lt Hi H3.
        eapply we_get; eauto.
  - simpl. inverts Hw.
    forwards~: IHA1 Hi H4.
    forwards~: IHA2 (S X) (T &= A1) (T' &= (tshift X A1)).
  - destruct m.
    + simpl. inverts Hw.
      econstructor; eauto; try solve [eapply lshape_tshift; eauto].
      eapply IHA2; eauto.
      eapply insert_teq_env; eauto.
      forwards~: wfe_inv H5.

      forwards~ [?|[?|?]]: ord_dec A1.
      * inverts H0; subst; simpl; eauto.
      * destruct H0 as (A & m & B & ?). subst.
        forwards~: wfe_mcon H. inverts* H6.
        forwards~: IHA1 Hi H0.
        
        rewrite tshift_and in H1. rewrite tshift_and.
        eapply wfe_to_mcon; eauto.
      * destruct H0 as (A & ?). subst.
        forwards~: wfe_mcon H.
        forwards~: IHA1 Hi H0.
        
        rewrite tshift_st in H1. rewrite tshift_st.
        eapply wfe_to_mcon_st; eauto.
    + simpl. inverts Hw.
      econstructor; eauto; try solve [eapply lshape_tshift; eauto].
      eapply IHA2; eauto.
      eapply insert_teq_env; eauto.
      forwards~: wfe_inv H5.

      forwards~ [?|[?|?]]: ord_dec A1.
      * inverts H0; subst; simpl; eauto.
      * destruct H0 as (A & m & B & ?). subst.
        forwards~: wfe_mcon H. inverts* H6.
        forwards~: IHA1 Hi H0.
        
        rewrite tshift_and in H1. rewrite tshift_and.
        eapply wfe_to_mcon; eauto.
      * destruct H0 as (A & ?). subst.
        forwards~: wfe_mcon H.
        forwards~: IHA1 Hi H0.
        
        rewrite tshift_st in H1. rewrite tshift_st.
        eapply wfe_to_mcon_st; eauto.
  - simpl. inverts Hw.
    econstructor; eauto.
    eapply lshape_tshift; eauto.    
Qed.




Inductive add_evar: typ -> typ -> Prop :=
  | ae_nil: forall T1,
      ord T1 ->
      add_evar T1 T1
  | ae_evar: forall T1 T2 A,
      add_evar T1 T2 ->
      add_evar (T1 & A) (T2 & A)
  | ae_teq: forall T1 T2 A,
      add_evar T1 T2 ->
      add_evar (T1 &= A) (T2 &= A)
  | ae_star: forall T1 T2,
      add_evar T1 T2 ->
      add_evar (T1 &s) (T2 &s)
  (* add a term variable *)
  | ae_add: forall T1 T2 A,
      add_evar T1 T2 ->
      wft T2 A ->
      add_evar T1 (T2 & A).

#[export]
Hint Constructors add_evar : core.

Lemma check_add_evar: forall T1 T2,
  add_evar T1 T2 -> forall i,
  check T1 i ->
  check T2 i.
Proof.
  introv He. inductions He; introv Hc; try solve [inverts* Hc].
Qed.

Lemma lookt_add_evar: forall T1 T2,
  add_evar T1 T2 -> forall i A,
  lookt T1 i A ->
  lookt T2 i A.
Proof.
  introv He. inductions He; introv Hc; try solve [inverts* Hc].
Qed.

Lemma add_evar_refl: forall T,
  add_evar T T.
Proof.
  intros T. inductions T; eauto.
  destruct* m.
Qed.

Lemma add_app: forall T1 T2,
  add_evar T1 T2 -> forall T3,
  wft T1 T3 ->
  add_evar (T1 +++ T3) (T2 +++ T3).
Proof.
  introv Hl Ht. gen T2. unfold wft in *. inductions Ht; introv Hl;
  try solve [simpl; eauto].
  - repeat rewrite <- mcon_cons.
    destruct* m2.
  - repeat rewrite <- mcon_cons_st. eauto.
Qed. 

Lemma add_evar_wfe: forall T1,
  wfe T1 -> forall T2,
  add_evar T1 T2 -> 
  wfe T2.
Proof.
  introv Hw. inductions Hw; introv He; try solve [eauto];
  try solve [inverts* He; eapply wfe_eteq_evar; eauto].
  - inverts* He.
    + forwards~: check_add_evar H4 H.
    + forwards~: check_add_evar H4 H.
    + eapply wfe_eteq_evar. eauto.
  - inverts* He.
    + forwards~: lookt_add_evar H4 H.
      forwards~: we_get T0 non i A.
    + forwards~: lookt_add_evar H4 H.
      forwards~: we_get T0 rt i A.
    + eapply wfe_eteq_evar. eauto.
  - inverts* He.
    + forwards~: we_arr T0 non A B.
    + forwards~: we_arr T0 rt A B.
    + eapply wfe_eteq_evar. eauto.
  - inverts* He.
    + forwards~: we_all T0 non A.
    + forwards~: we_all T0 rt A.
    + eapply wfe_eteq_evar. eauto.
  - inverts* He.
    + forwards~: we_mani T0 non A B.
    + forwards~: we_mani T0 rt A B.
    + eapply wfe_eteq_evar. eauto.
  - inverts* He.
    + econstructor; eauto.
      eapply IHHw2; eauto.
      econstructor. eapply add_app; eauto.
    + econstructor; eauto.
      eapply IHHw2; eauto.
      econstructor. eapply add_app; eauto.
    + eapply wfe_eteq_evar. eauto.
Qed. 

Lemma add_evar_wft: forall T1 A,
  wft T1 A -> forall T2,
  add_evar T1 T2 -> 
  wft T2 A.
Proof.
  intros. unfold wft in *. eapply add_evar_wfe; eauto.
Qed.


Lemma lookt_wft: forall T,
  wfe T -> forall X A,
  lookt T X A ->
  wft T A.
Proof.
  intros T. inductions T; introv Hw Hgt; unfold wft in *;
  try solve [inverts* Hgt].
  - destruct* m.
    + inverts Hgt. forwards~: IHT1 H3. eapply wfe_inv; eauto. 
      eapply add_evar_wfe; eauto.
      econstructor; eauto.
      econstructor. eapply add_evar_refl; eauto.
      unfold wft. eapply wfe_evar_eteq; eauto.
    + destruct* X. 
      * inverts Hgt.
        eapply insert_teq_wft; eauto.
      * inverts Hgt.
        eapply insert_teq_wft; eauto.
        eapply IHT1; eauto. eapply wfe_inv; eauto.
  - inverts Hgt.
    eapply insert_tvar_wft; eauto.
    eapply IHT; eauto. eapply wfe_sinv; eauto. 
Qed.





Lemma add_evar_app: forall T1 T2,
  add_evar T1 T2 -> forall T3,
  add_evar (T1 +++ T3) (T2 +++ T3).
Proof.
  introv Ha. inductions T3; try solve [simpl; eauto].
  - destruct m.
    + rewrite <- mcon_cons. rewrite <- mcon_cons. econstructor; eauto.
    + rewrite <- mcon_cons. rewrite <- mcon_cons. econstructor; eauto.
  - rewrite <- mcon_cons_st. rewrite <- mcon_cons_st. econstructor; eauto.
Qed.

(* prepend variant of add_evar_app, for the new eq_boxr context T3+++T1 *)
Lemma add_evar_pre: forall T1 T2, add_evar T1 T2 -> forall T3, wfe T3 ->
  add_evar (T3 +++ T1) (T3 +++ T2).
Proof.
  introv H. inductions H; introv Hw.
  - eapply add_evar_refl.
  - rewrite <- mcon_cons. rewrite <- mcon_cons. econstructor; eauto.
  - rewrite <- mcon_cons. rewrite <- mcon_cons. econstructor; eauto.
  - rewrite <- mcon_cons_st. rewrite <- mcon_cons_st. econstructor; eauto.
  - rewrite <- mcon_cons. econstructor; eauto using wft_prepend.
Qed.

Lemma add_evar_teq: forall T1 A B T2,
  teq T1 A B T2 -> forall T3,
  add_evar T1 T3 ->
  teq T3 A B T2.
Proof.
  introv Ht. inductions Ht; introv Ha; try solve [eauto];
    try solve [econstructor; eauto;
      solve [ match goal with |- teq _ _ _ _ =>
                eapply IHHt;
                solve [ eauto | eapply add_evar_app; eauto
                      | eapply add_evar_pre; eauto using wft_wfe ] end
            | eapply add_evar_wfe; try eapply Ha; eauto
            | eapply add_evar_wft; try eapply Ha; eauto
            | eapply check_add_evar; eauto
            | eapply lookt_add_evar; eauto ]].
  - (* eq_and *) econstructor; eauto.
    eapply IHHt2. eapply add_app; eauto.
    eapply teq_wft_left; eauto.
Qed.

Lemma adde_teq_sp: forall T1 A B T2,
  teq T1 A B T2 -> forall C,
  wft (T1 & C) A ->
  teq (T1 & C) A B T2.
Proof.
  intros. eapply add_evar_teq; eauto.
  econstructor; eauto. 
  eapply add_evar_refl; eauto.
  forwards~: wft_wfe H0. unfold wft. eapply wfe_evar_eteq; eauto.
Qed.


Inductive insert_both : nat -> typ -> typ -> typ -> typ -> Prop :=
  | ib_here2 : forall TL TR,
      insert_both 0 TL (TL &s) TR (TR &s)
  | ib_var_l : forall (X : nat) (A : typ) TL TL' TR TR',
      insert_both X TL TL' TR TR' ->
      insert_both X (TL & A) (TL' & (tshift X A)) TR TR'
  | ib_var_r : forall (X : nat) (A : typ) TL TL' TR TR',
      insert_both X TL TL' TR TR' ->
      insert_both X TL TL' (TR & A) (TR' & (tshift X A))
  | ib_tvar : forall (X : nat) TL TL' TR TR',
      insert_both X TL TL' TR TR' ->
      insert_both (S X) (TL &s) (TL' &s) (TR &s) (TR' &s)
  | ib_teq : forall (X : nat) (A B : typ) TL TL' TR TR',
      insert_both X TL TL' TR TR' ->
      insert_both (S X) (TL &= A) (TL' &= (tshift X A)) (TR &= B) (TR' &= (tshift X B))
  | ib_manil : forall (X : nat) (A : typ) TL TL' TR TR',
      insert_both X TL TL' TR TR' ->
      insert_both (S X) (TL &= A) (TL' &= (tshift X A)) (TR &s) (TR' &s)
  | ib_manir : forall (X : nat) (A : typ) TL TL' TR TR',
      insert_both X TL TL' TR TR' ->
      insert_both (S X) (TL &s) (TL' &s) (TR &= A) (TR' &= (tshift X A)).

#[export]
Hint Constructors insert_both: core.

Lemma insert_both_left: forall X TL TL' TR TR',
  insert_both X TL TL' TR TR'->
  insert_tvar X TL TL'.
Proof.
  introv Hi. inductions Hi; eauto.
Qed.


Lemma insert_both_right: forall X TL TL' TR TR',
  insert_both X TL TL' TR TR'->
  insert_tvar X TR TR'.
Proof.
  introv Hi. inductions Hi; eauto.
Qed.


Lemma itvar_wfe: forall X T T1, 
  insert_tvar X T T1 -> 
  wfe T ->
  wfe T1.
Proof.
  introv Hi. inductions Hi; introv Hw; eauto.
  - forwards~: wfe_inv Hw.
    forwards~: IHHi H.
    forwards~: wfe_evar_eteq Hw. 
    forwards~: insert_tvar_wft Hi H1.
    eapply wfe_eteq_evar; eauto.
  - forwards~: wfe_sinv Hw. 
  - forwards~: wfe_inv Hw.
    forwards~: IHHi H.
    forwards~: insert_tvar_wft Hi Hw.
Qed.


Lemma teq_lshape_keyLen: forall T1 T2 T3 T4,
  teq T1 T3 T4 T2 -> lshape T3 -> lshape T4 -> keyLen T3 = keyLen T4.
Proof.
  introv Ht. inductions Ht; introv Hl1 Hl2;
  try solve [inverts Hl1; inverts Hl2; simpl; f_equal; eauto].
  inverts Hl1; inverts Hl2.
  destruct m; [ eapply IHHt1; eauto | simpl; f_equal; eapply IHHt1; eauto ].
Qed.

Lemma insert_both_env: forall T1 T2 T3 T4,
  teq T1 T3 T4 T2 ->
  lshape T3 ->
  lshape T4 -> forall X T1 T1' T2 T2',
  insert_both X T1 T1' T2 T2' ->
  insert_both (keyLen T3 + X) (T1 +++ T3) (T1' +++ tshift X T3)
  (T2 +++ T4) (T2' +++ tshift X T4).
Proof.
  introv Ht. inductions Ht; introv Hl1 Hl2 Hi;
  try solve [inverts Hl1; inverts Hl2; eauto].
  - forwards HkL: teq_lshape_keyLen Ht1 H H0.
    inverts Hl1. inverts Hl2.
    repeat rewrite tshift_and.
    repeat rewrite <-mcon_cons.
    destruct m.
    + simpl keyLen. rewrite <- HkL.
      eapply ib_var_r. eapply ib_var_l. eapply IHHt1; eauto.
    + simpl keyLen. rewrite <- HkL.
      replace (S (keyLen T3) + X) with (S (keyLen T3 + X)) by lia.
      eapply ib_teq. eapply IHHt1; eauto.
  - inverts Hl1. inverts Hl2.
    repeat rewrite tshift_st.
    repeat rewrite <-mcon_cons_st.
    simpl keyLen. replace (S (keyLen T3) + X) with (S (keyLen T3 + X)) by lia.
    eapply ib_tvar. eapply IHHt; eauto.
Qed.


Inductive del_evar: typ -> typ -> Prop :=
  | del_evar_nil: forall T1,
      ord T1 ->
      del_evar T1 T1
  | del_evar_evar: forall T1 T2 A,
      del_evar T1 T2 ->
      del_evar (T1 & A) (T2 & A)
  | del_evar_teq: forall T1 T2 A,
      del_evar T1 T2 ->
      del_evar (T1 &= A) (T2 &= A)
  | del_evar_star: forall T1 T2,
      del_evar T1 T2 ->
      del_evar (T1 &s) (T2 &s)
  | del_evar_devar: forall T1 T2 A,
      del_evar T1 T2 ->
      del_evar (T1 & A) T2.

#[export]
Hint Constructors del_evar : core.


Lemma del_lookt_inv: forall T1 T2,
  del_evar T1 T2 -> forall i A,
  lookt T1 i A ->
  lookt T2 i A.
Proof.
  introv He. inductions He; introv Hc; try solve [eauto].
  - destruct* i; inverts* Hc.
  - destruct* i; inverts* Hc.
  - destruct* i; inverts* Hc.
  - destruct* i; inverts* Hc.
Qed.

Lemma del_check_inv: forall T1 T2,
  del_evar T1 T2 -> forall i,
  check T1 i ->
  check T2 i.
Proof.
  introv He. inductions He; introv Hc; try solve [eauto].
  - destruct* i; inverts* Hc.
  - destruct* i; inverts* Hc.
  - destruct* i; inverts* Hc.
  - destruct* i; inverts* Hc.
Qed.

Lemma del_app: forall T1 T2,
  del_evar T1 T2 -> forall T3,
  wft T1 T3 ->
  del_evar (T1 +++ T3) (T2 +++ T3).
Proof.
  introv Hl Ht. gen T2. unfold wft in *. inductions Ht; introv Hl;
    try solve [simpl; eauto].
  - repeat rewrite <- mcon_cons.
    destruct* m2.
  - repeat rewrite <- mcon_cons_st. eauto.
Qed.

Lemma del_evar_wfe: forall T1,
  wfe T1 -> forall T2,
  del_evar T1 T2 -> 
  wfe T2.
Proof.
  introv Hw. inductions Hw; introv He; try solve [inverts* He]; try solve [eauto].
  - inverts* He.
    + forwards~: del_check_inv H4 H. 
    + forwards~: del_check_inv H4 H. 
  - inverts* He.
    + forwards~: del_lookt_inv H4 H. eapply we_get; eauto.
    + forwards~: del_lookt_inv H4 H. eapply we_get; eauto.
  - inverts* He.
    + eapply wfe_eteq_evar. econstructor; eauto.
    + econstructor; eauto.
    + eapply wfe_inv; eauto. 
  - inverts* He.
    + eapply wfe_eteq_evar. econstructor; eauto. 
    + econstructor; eauto. 
  - inverts* He.
    + eapply wfe_eteq_evar. econstructor; eauto. 
    + econstructor; eauto. 
    + eapply wfe_inv; eauto.
  - inverts* He.
    + eapply wfe_eteq_evar. econstructor; eauto.
      eapply IHHw2.
      econstructor. eapply del_app; eauto.
    + econstructor; eauto.
      eapply IHHw2.
      econstructor. eapply del_app; eauto.
    + eapply wfe_inv; eauto. 
  - inverts* He. eapply wfe_inv; eauto.
  - inverts* He. eapply wfe_inv; eauto. 
Qed.


Lemma del_wft: forall T1 A,
  wft T1 A -> forall T2,
  del_evar T1 T2 -> 
  wft T2 A.
Proof.
  intros. unfold wft in *. eapply del_evar_wfe; eauto.
Qed.

Lemma del_refl: forall T,
  del_evar T T.
Proof.
  intros T. inductions T; eauto.  
  destruct* m.
Qed.

Lemma del_evar_refl: forall T, del_evar T T.
Proof.
  induction T; try solve [eapply del_evar_nil; constructor].
  - destruct m; [eapply del_evar_evar | eapply del_evar_teq]; eauto.
  - eapply del_evar_star; eauto.
Qed.

Lemma del_evar_app: forall T1 T2,
  del_evar T1 T2 -> forall T3,
  del_evar (T1 +++ T3) (T2 +++ T3).
Proof.
  introv Ha. inductions T3; try solve [simpl; eauto].
  - destruct m.
    + rewrite <- mcon_cons. rewrite <- mcon_cons. econstructor; eauto.
    + rewrite <- mcon_cons. rewrite <- mcon_cons. econstructor; eauto.
  - rewrite <- mcon_cons_st. rewrite <- mcon_cons_st. econstructor; eauto.
Qed.

(* prepend variant of del_evar_app, for the new eq_boxr context T3+++T1 *)
Lemma del_evar_pre: forall T1 T2, del_evar T1 T2 -> forall T3,
  del_evar (T3 +++ T1) (T3 +++ T2).
Proof.
  introv H. inductions H; introv.
  - eapply del_evar_refl.
  - rewrite <- mcon_cons. rewrite <- mcon_cons. econstructor; eauto.
  - rewrite <- mcon_cons. rewrite <- mcon_cons. econstructor; eauto.
  - rewrite <- mcon_cons_st. rewrite <- mcon_cons_st. econstructor; eauto.
  - rewrite <- mcon_cons. econstructor; eauto.
Qed.

Lemma del_evar_wft: forall T1 T2 A,
  del_evar T1 T2 -> wft T1 A -> wft T2 A.
Proof.
  introv Hd Hw. unfold wft in *.
  eapply del_evar_wfe. exact Hw. econstructor; eauto.
Qed.



#[export]
Hint Constructors is_box: core.




Inductive sign := 
  | esign: nat -> sign 
  | tsign: nat -> sign.

#[export]
Hint Constructors sign: core.

Definition genv := list sign.

Fixpoint findX (X:nat) (G: genv) :=
  match G with
    | esign _ :: G' => findX X G'
    | tsign v :: G' =>
      (match X with
        | O    => Some v
        | S X' => findX X' G' 
      end)
    | nil => None
  end.

Fixpoint weight (G: genv) (A : typ) {struct A} : nat :=
  match A with
    | int => 1
    | tvar i => 1 + match findX i G with
                    | Some k => k
                    | None => 0
                    end
    | arr A1 A2 => 1 + (weight G A1) + (weight G A2)
    | all A2 => 1 + weight (tsign 1 :: G) A2
    | boxt T A2 => 
        let fix mkb (T:typ) : genv :=
          match T with
            | T' & A  => let G := mkb T' in esign (weight G A) :: G
            | T' &s   => tsign 1 :: mkb T'
            | T' &= A => let G := mkb T' in tsign (weight G A) :: G
            | _ => []
          end in
        1 + weight (mkb T) A2
    | mani A1 A2 => 
        let w1 := weight G A1 in 
        1 + w1 + weight (tsign w1 :: G) A2
    | top => 1
    | A1 &= A2 => 
        let fix mkb_list (G: genv) (T:typ) : genv :=
          match T with
            | T' & A => let G1 := mkb_list G T' in esign (weight (G1 ++ G) A) :: G1
            | T' &s => tsign 1 :: mkb_list G T'
            | T' &= A => let G1 := mkb_list G T' in tsign (weight (G1 ++ G) A) :: G1
            | _ => []
        end in
        1 + weight G A1 + weight (mkb_list G A1 ++ G) A2
    | A1 & A2 => 
        let fix mkb_list (G: genv) (T:typ) : genv :=
          match T with
            | T' & A => let G1 := mkb_list G T' in esign (weight (G1 ++ G) A) :: G1
            | T' &s => tsign 1 :: mkb_list G T'
            | T' &= A => let G1 := mkb_list G T' in tsign (weight (G1 ++ G) A) :: G1
            | _ => []
        end in
        1 + weight G A1 + weight (mkb_list G A1 ++ G) A2
    | A1 &s => 
        1 + weight G A1
    | rcd l A1 => 1 + weight G A1
  end.

Fixpoint mkb (T:typ) : genv :=
  match T with
    | T' & A  => let G := mkb T' in esign (weight G A) :: G
    | T' &s   => tsign 1 :: mkb T'
    | T' &= A => let G := mkb T' in tsign (weight G A) :: G
    | _ => []
  end.

Fixpoint mkb_list (G: genv) (T:typ) : genv :=
  match T with
    | T' & A => let G1 := mkb_list G T' in esign (weight (G1 ++ G) A) :: G1
    | T' &s => tsign 1 :: mkb_list G T'
    | T' &= A => let G1 := mkb_list G T' in tsign (weight (G1 ++ G) A) :: G1
    | _ => []
  end.

Definition bindings T A := weight (mkb T) A.

Lemma weight_min: forall A G, 
  1 <= weight G A.
Proof.
  intros A; inductions A; intros G;
  try solve [simpl; unfold bindings in *; simpl in *; lia].
  - destruct m.
    + simpl. fold mkb_list in *. lia.
    + simpl. fold mkb_list in *. lia. 
Qed.

Lemma bindings_min: forall A T, 
  1 <= bindings T A.
Proof.
  intros. unfold bindings. eapply weight_min.
Qed.


Lemma weight_etvar: forall G T,
  weight G (T &s) = S (weight G T).
Proof.
  intros. simpl. eauto.
Qed.

Lemma weight_evar: forall G T A,
  weight G (T & A) = 1 + weight (mkb_list G T ++ G) A + weight G T.
Proof.
  intros. simpl. fold mkb_list. lia. 
Qed.

Lemma weight_eteq: forall G T A,
  weight G (T &= A) = 1 + weight (mkb_list G T ++ G) A + weight G T.
Proof.
  intros. simpl. fold mkb_list. lia. 
Qed.


Fixpoint len (A : typ) : nat :=
  match A with
    | and A m B => 1 + len A
    | A1 &s => 1 + len A1
    | _ => 0
  end.

Ltac solve_size :=
  match goal with
    | [ Hl : _ <= S(?n) |- _ <= ?n ] =>
      unfold bindings in Hl; simpl in Hl; fold mkb in Hl; 
      unfold bindings; simpl; 
      lia
  end.

Lemma mkb_eq: forall T1 T,
  mkb_list (mkb T) T1 ++ mkb T = mkb (T +++ T1).
Proof. 
  intros T1. inductions T1; intros; try solve [eauto].
  - destruct* m.
    + rewrite <- mcon_cons. simpl. rewrite IHT1_1. eauto. 
    + rewrite <- mcon_cons. simpl. rewrite IHT1_1. eauto. 
  - rewrite <- mcon_cons_st. simpl. rewrite IHT1. eauto. 
Qed.

Lemma len_app: forall T1 T,
  len (T +++ T1) = len T + len T1.
Proof.
  intros T1. inductions T1; intros; try solve [simpl; eauto].
  - destruct* m.
    + rewrite <- mcon_cons. simpl. rewrite IHT1_1. lia.
    + rewrite <- mcon_cons. simpl. rewrite IHT1_1. lia.
  - rewrite <- mcon_cons_st. simpl. rewrite IHT1. lia.
Qed.

Lemma larger_len: forall T1 T,
  weight (mkb T) T1 > len T1.
Proof.
  inductions T1; intros; try solve [simpl; lia].
  - destruct m.
    + rewrite weight_evar. 
      forwards: IHT1_1 T. simpl. fold mkb_list in *. lia.
    + rewrite weight_eteq. 
      forwards: IHT1_1 T. simpl. fold mkb_list in *. lia.
  - rewrite weight_etvar. 
    forwards: IHT1 T. simpl. fold mkb_list in *. lia.
Qed.

Lemma bindings_it_size1: forall n A X T T',
  len T + 2 * bindings T A <= S n ->
  insert_teq X T T' -> 
  bindings T A = bindings T' (tshift X A).
Proof.
  intro n. inductions n. 
  intros. forwards~: bindings_min A T. lia.

  introv Hl Hi.
  destruct A.
  - simpl. unfold bindings. simpl. lia.
  - inverts* Hi.
    (* evar *)
    + forwards~: IHn (tvar n0) X T0 T'0.
      unfold bindings in Hl. simpl in Hl.
      unfold bindings. simpl. lia.
    (* etvar *)
    + destruct* n0.
      unfold bindings in Hl. 
      forwards~: IHn (tvar n0) X0 T0 T'0.
      simpl. simpl in Hl. lia. clear IHn. clear Hl. simpl in H0.
      unfold tshift.
      destruct (le_gt_dec X0 n0).
      * assert (S X0 <= S n0) by lia.
        destruct (le_gt_dec (S X0) (S n0)); try solve [lia].       
        unfold bindings in *.   
        unfold weight in *. simpl in *. lia. 
      * assert (S X0 > S n0) by lia.
        destruct (le_gt_dec (S X0) (S n0)); try solve [lia].       
        unfold bindings in *.  
        unfold weight in *. simpl in *. lia.
    (* eteq *)
    + destruct n0.
      (* key case where should use bindings as a measure *)
      * simpl. unfold bindings. simpl. 
        assert (bindings T0 A = bindings T'0 (tshift X0 A)). {
          eapply IHn; eauto.
          simpl in Hl. unfold bindings. lia.
        }
        unfold bindings in H0. lia.
      * unfold bindings in Hl. 
        forwards~: IHn (tvar n0) X0 T0 T'0.
        simpl. simpl in Hl. lia. clear IHn. clear Hl. simpl in H0.
        unfold tshift. fold tshift.
        destruct (le_gt_dec X0 n0).
        ** assert (S X0 <= S n0) by lia.
          destruct (le_gt_dec (S X0) (S n0)); try solve [lia].       
          unfold bindings in *.   
          unfold weight in *. simpl in *. lia. 
        ** assert (S X0 > S n0) by lia.
          destruct (le_gt_dec (S X0) (S n0)); try solve [lia].       
          unfold bindings in *.  
          unfold weight in *. simpl in *. lia.
  - unfold bindings.
    simpl. unfold bindings in Hl. simpl in Hl.
    forwards~: IHn A1 X T T'. 
    unfold bindings. lia.
    forwards~: IHn A2 X T T'. 
    unfold bindings. lia.
  - unfold bindings in Hl. simpl in Hl.
    forwards~: IHn A (S X) (T &s) (T' &s). 
    unfold bindings. simpl. lia.
    unfold bindings in *.
    simpl. simpl in H. rewrite H. eauto.
  - simpl. unfold bindings. simpl. lia.
  - unfold bindings in Hl. simpl in Hl.
    forwards~: IHn A1 X T T'.
    unfold bindings. lia.
    forwards~: IHn A2 (S X) (T &= A1) (T' &= (tshift X A1)). 
    unfold bindings. simpl. lia.
    unfold bindings in *.
    simpl. simpl in H0. rewrite H0. rewrite H. eauto.
  - simpl. unfold bindings in *. simpl in *. 
    forwards~: IHn A X T T'. lia. 
  - simpl. unfold bindings. simpl. lia.
  (* and *)
  - destruct m.
    + simpl.
      forwards~: IHn A1 Hi. solve_size.
      forwards~: insert_teq_env Hi A1.
      forwards~: IHn A2 H0.
      unfold bindings in *. rewrite weight_evar in *.
      rewrite <-mkb_eq. 
      rewrite len_app. 
      specialize (larger_len A1 T). intros. lia.

      unfold bindings in *. repeat rewrite weight_evar.
      repeat rewrite mkb_eq. lia.
    + simpl.
      forwards~: IHn A1 Hi. solve_size.
      forwards~: insert_teq_env Hi A1.
      forwards~: IHn A2 H0.
      unfold bindings in *. rewrite weight_eteq in *.
      rewrite <-mkb_eq. 
      rewrite len_app. 
      specialize (larger_len A1 T). intros. lia.

      unfold bindings in *. repeat rewrite weight_eteq.
      repeat rewrite mkb_eq. lia.
  (* ands *)
  - simpl. forwards~: IHn A Hi. solve_size. 
    unfold bindings in *. 
    repeat rewrite weight_etvar. lia.
Qed.

Lemma bindings_it1: forall A X T T',
  insert_teq X T T' ->
  bindings T A = bindings T' (tshift X A).
Proof.
  intros. eapply bindings_it_size1; eauto.
Qed.

Lemma bindings_zero1: forall A T B,
  bindings T A = bindings (T &= B) (tshift 0 A).
Proof.
  intros. eapply bindings_it1; eauto.
Qed.

Lemma bindings_shift1: forall A T i B,
  bindings T (tvar i) > bindings T A-> 
  bindings (T &= B) (tvar (S i)) > bindings (T &= B) (tshift 0 A).
Proof.
  intros. forwards~: bindings_zero1 A T B. 
  rewrite <- H0. eauto. 
Qed.


Lemma bindings_it_size2: forall n A X T T',
  len T + 2 * bindings T A <= S n ->
  insert_tvar X T T' -> 
  bindings T A = bindings T' (tshift X A).
Proof.
  intro n. inductions n. 
  intros. forwards~: bindings_min A T. lia.

  introv Hl Hi.
  destruct A.
  - simpl. unfold bindings. simpl. lia.
  - inverts* Hi.
    (* evar *)
    + forwards~: IHn (tvar n0) X T0 T'0.
      unfold bindings in Hl. simpl in Hl.
      unfold bindings. simpl. lia.
    (* etvar *)
    + destruct* n0.
      unfold bindings in Hl. 
      forwards~: IHn (tvar n0) X0 T0 T'0.
      simpl. simpl in Hl. lia. clear IHn. clear Hl. simpl in H0.
      unfold tshift.
      destruct (le_gt_dec X0 n0).
      * assert (S X0 <= S n0) by lia.
        destruct (le_gt_dec (S X0) (S n0)); try solve [lia].       
        unfold bindings in *.   
        unfold weight in *. simpl in *. lia. 
      * assert (S X0 > S n0) by lia.
        destruct (le_gt_dec (S X0) (S n0)); try solve [lia].       
        unfold bindings in *.  
        unfold weight in *. simpl in *. lia.
    (* eteq *)
    + destruct n0.
      (* key case where should use bindings as a measure *)
      * simpl. unfold bindings. simpl. 
        assert (bindings T0 A = bindings T'0 (tshift X0 A)). {
          eapply IHn; eauto.
          simpl in Hl. unfold bindings. lia.
        }
        unfold bindings in H0. lia.
      * unfold bindings in Hl. 
        forwards~: IHn (tvar n0) X0 T0 T'0.
        simpl. simpl in Hl. lia. clear IHn. clear Hl. simpl in H0.
        unfold tshift. fold tshift.
        destruct (le_gt_dec X0 n0).
        ** assert (S X0 <= S n0) by lia.
          destruct (le_gt_dec (S X0) (S n0)); try solve [lia].       
          unfold bindings in *.   
          unfold weight in *. simpl in *. lia. 
        ** assert (S X0 > S n0) by lia.
          destruct (le_gt_dec (S X0) (S n0)); try solve [lia].       
          unfold bindings in *.  
          unfold weight in *. simpl in *. lia.
  - unfold bindings.
    simpl. unfold bindings in Hl. simpl in Hl.
    forwards~: IHn A1 X T T'. 
    unfold bindings. lia.
    forwards~: IHn A2 X T T'. 
    unfold bindings. lia.
  - unfold bindings in Hl. simpl in Hl.
    forwards~: IHn A (S X) (T &s) (T' &s). 
    unfold bindings. simpl. lia.
    unfold bindings in *.
    simpl. simpl in H. rewrite H. eauto.
  - simpl. unfold bindings. simpl. lia.
  - unfold bindings in Hl. simpl in Hl.
    forwards~: IHn A1 X T T'.
    unfold bindings. lia.
    forwards~: IHn A2 (S X) (T &= A1) (T' &= (tshift X A1)). 
    unfold bindings. simpl. lia.
    unfold bindings in *.
    simpl. simpl in H0. rewrite H0. rewrite H. eauto.
  - simpl. unfold bindings in *. simpl in *. 
    forwards~: IHn A X T T'. lia. 
  - simpl. unfold bindings. simpl. lia.
  (* and *)
  - destruct m.
    + simpl.
      forwards~: IHn A1 Hi. solve_size.
      forwards~: insert_tvar_env Hi A1.
      forwards~: IHn A2 H0.
      unfold bindings in *. rewrite weight_evar in *.
      rewrite <-mkb_eq. 
      rewrite len_app. 
      specialize (larger_len A1 T). intros. lia.

      unfold bindings in *. repeat rewrite weight_evar.
      repeat rewrite mkb_eq. lia.
    + simpl.
      forwards~: IHn A1 Hi. solve_size.
      forwards~: insert_tvar_env Hi A1.
      forwards~: IHn A2 H0.
      unfold bindings in *. rewrite weight_eteq in *.
      rewrite <-mkb_eq. 
      rewrite len_app. 
      specialize (larger_len A1 T). intros. lia.

      unfold bindings in *. repeat rewrite weight_eteq.
      repeat rewrite mkb_eq. lia.
  (* ands *)
  - simpl. forwards~: IHn A Hi. solve_size. 
    unfold bindings in *. 
    repeat rewrite weight_etvar. lia.
Qed.

Lemma bindings_it2: forall A X T T',
  insert_tvar X T T' ->
  bindings T A = bindings T' (tshift X A).
Proof.
  intros. eapply bindings_it_size2; eauto.
Qed.

Lemma bindings_zero2: forall A T,
  bindings T A = bindings (T &s) (tshift 0 A).
Proof.
  intros. eapply bindings_it2; eauto.
Qed.

Lemma bindings_shift2: forall A T i,
  bindings T (tvar i) > bindings T A-> 
  bindings (T &s) (tvar (S i)) > bindings (T &s) (tshift 0 A).
Proof.
  intros. forwards~: bindings_zero2 A T. 
  rewrite <- H0. eauto. 
Qed.


Inductive nadd: typ -> typ -> Prop :=
  | nae_nil: forall T1,
      ord T1 ->
      nadd T1 T1
  | nae_evar: forall T1 T2 A,
      nadd T1 T2 ->
      nadd (T1 & A) (T2 & A)
  | nae_teq: forall T1 T2 A,
      nadd T1 T2 ->
      nadd (T1 &= A) (T2 &= A)
  | nae_star: forall T1 T2,
      nadd T1 T2 ->
      nadd (T1 &s) (T2 &s)
  (* add a term variable *)
  | nae_add: forall T1 T2 A,
      nadd T1 T2 ->
      nadd T1 (T2 & A).

#[export]
Hint Constructors nadd : core.


Lemma nadd_app: forall T3 T1 T2,
  nadd T1 T2 -> 
  nadd (T1 +++ T3) (T2 +++ T3).
Proof.
  intros T3. inductions T3; intros; eauto. 
  - repeat rewrite <- mcon_cons.
    destruct* m.
  - repeat rewrite <- mcon_cons_st. eauto.
Qed.


Lemma bindings_evar_size: forall n A T T1,
  len T + len T1 + 3 * bindings T A <= n ->
  nadd T T1 -> 
  bindings T A = bindings T1 A.
Proof.
  intros n. inductions n; introv Hl Ha.
  intros. forwards~: bindings_min A T. lia.

  destruct* A.
  (* key case *)
  - inverts* Ha.
    + forwards~: IHn (tvar n0) T0 T2. unfold bindings in *. simpl in Hl. simpl. lia.
    + destruct* n0.
      * unfold bindings in *. simpl in *.
        forwards~: IHn A H. solve_size.
      * unfold bindings in *.
        forwards~: IHn (tvar n0) T0 T2. simpl. simpl in Hl. lia.
    + destruct* n0.
      * unfold bindings in *.
        forwards~: IHn (tvar n0) T0 T2. simpl. simpl in Hl. lia.
    + forwards~: IHn (tvar n0) T T2. unfold bindings in *. simpl in Hl. simpl. lia.
  - unfold bindings in *. simpl in Hl.
    forwards~: IHn A1 T T1. simpl. lia.
    forwards~: IHn A2 T T1. simpl. lia.
    simpl. lia.
  - unfold bindings in *. simpl in Hl.
    forwards~: IHn A (T &s) (T1 &s).
    simpl. lia.
    simpl. simpl in H. lia.
  - unfold bindings in *. simpl in Hl.
    forwards~: IHn A1 T T1. simpl. lia.
    forwards~: IHn A2 (T &= A1) (T1 &= A1). simpl. lia.
    simpl. simpl in H0. lia.
  - unfold bindings in *. simpl in Hl.
    forwards~: IHn A T T1. simpl. lia. simpl. lia.
  - destruct m. 
    + unfold bindings in *. repeat rewrite weight_evar in *.
      forwards~: IHn A1 Ha.
      forwards~: weight_min A2 (mkb_list (mkb T) A1 ++ mkb T). lia. 
      forwards~: IHn A2 (T +++ A1) (T1 +++ A1); try solve [eapply nadd_app; eauto].

      repeat rewrite len_app. 
      forwards~: weight_min A2 (mkb (T +++ A1)).
      rewrite mkb_eq in Hl. 
      specialize (larger_len A1 T). intros. lia. 
      repeat rewrite weight_eteq. repeat rewrite mkb_eq. lia.
    + unfold bindings in *. repeat rewrite weight_eteq in *.
      forwards~: IHn A1 Ha.
      forwards~: weight_min A2 (mkb_list (mkb T) A1 ++ mkb T). lia. 
      forwards~: IHn A2 (T +++ A1) (T1 +++ A1); try solve [eapply nadd_app; eauto].

      repeat rewrite len_app. 
      forwards~: weight_min A2 (mkb (T +++ A1)).
      rewrite mkb_eq in Hl. 
      specialize (larger_len A1 T). intros. lia. 
      repeat rewrite weight_eteq. repeat rewrite mkb_eq. lia.
  - unfold bindings in *. rewrite weight_etvar in *.
    forwards~: IHn A Ha. lia. simpl in *. lia.
Qed.
  
Lemma bindings_evar: forall A T T1,
  nadd T T1 -> 
  bindings T A = bindings T1 A.
Proof.
  intros. eapply bindings_evar_size; eauto.
Qed.

Lemma nadd_refl: forall T,
  nadd T T.
Proof.
  intros T. inductions T; eauto. destruct* m.
Qed.

Lemma bindings_evar_sp: forall A T B,
  bindings T A = bindings (T & B) A.
Proof.
  intros. eapply bindings_evar; eauto.
  econstructor. eapply nadd_refl; eauto.
Qed.



Lemma var_decr_size: forall n T,
  len T + 1 <= n -> 
  wfe T -> forall A i,
  lookt T i A ->
  bindings T A < bindings T (tvar i).
Proof.
  intros n. inductions n; introv Hl Hw Hgt.
  lia.

  inverts Hw; try solve [inverts* Hgt].
  (* etvar *)
  - destruct* i.
    + inverts* Hgt.
    + inverts* Hgt. 
      forwards~: IHn T0 H2. simpl in Hl. lia.
      eapply bindings_shift2; eauto.
  (* int *)
  - destruct* m.
    { simpl. inverts Hgt.
      forwards~: IHn T0 H4. simpl in Hl. lia.
      repeat rewrite <-bindings_evar_sp. eauto.
    }
    { destruct* i.
      + inverts* Hgt. 
      + inverts* Hgt. 
        forwards~: IHn T0 H4. simpl in Hl. lia.
        eapply bindings_shift1; eauto.
    }
  (* check *)
  - destruct* m.
    { simpl. inverts Hgt.
      forwards~: IHn T0 H5. simpl in Hl. lia.
      repeat rewrite <-bindings_evar_sp. eauto.
    }
    { destruct* i.
      + inverts* Hgt. 
      + inverts* Hgt. 
        forwards~: IHn T0 H5. simpl in Hl. lia.
        eapply bindings_shift1; eauto.
    }
  (* lookt *)
  - destruct* m.
    { simpl. inverts Hgt.
      forwards~: IHn T0 H5. simpl in Hl. lia.
      repeat rewrite <-bindings_evar_sp. eauto.
    }
    { destruct* i.
      + inverts* Hgt. 
      + inverts* Hgt. 
        forwards~: IHn T0 H5. simpl in Hl. lia.
        eapply bindings_shift1; eauto.
    }
  (* arr *)
  - destruct* m.
    + inverts* Hgt. forwards~: IHn H5. simpl in Hl. lia.
      eapply wfe_inv; eauto.
      repeat rewrite <-bindings_evar_sp. eauto.
    + inverts* Hgt.
      * forwards~: bindings_zero1 (arr A0 B) T0 ((arr A0 B)).
        unfold bindings in H1. simpl in H1.
        unfold bindings. simpl. lia.
      * forwards~: IHn H5. simpl in Hl. lia.
        eapply wfe_inv; eauto.
        eapply bindings_shift1; eauto.
  (* all *)
  - destruct* m.
    + inverts* Hgt. forwards~: IHn H5. simpl in Hl. lia.
      repeat rewrite <-bindings_evar_sp. eauto.
    + inverts* Hgt.
      * forwards~: bindings_zero1 (all A0) T0 ((all A0)).
        unfold bindings in H1. simpl in H1.
        unfold bindings. simpl. lia.
      * forwards~: IHn H5. simpl in Hl. lia.
        eapply bindings_shift1; eauto.
  (* box *)
  - destruct* m.
    + inverts* Hgt. forwards~: IHn H6. simpl in Hl. lia.
      repeat rewrite <-bindings_evar_sp. eauto.
    + inverts* Hgt.
      eapply bindings_shift1; eauto.
      eapply IHn; eauto. simpl in Hl. lia. 
  (* mani *)
  - destruct* m.
    + inverts* Hgt. forwards~: IHn H5. simpl in Hl. lia.
      eapply wfe_inv; eauto.
      repeat rewrite <-bindings_evar_sp. eauto.
    + inverts* Hgt.
      * forwards~: bindings_zero1 (mani A0 B) T0 ((mani A0 B)).
        unfold bindings in H1. simpl in H1.
        unfold bindings. simpl. lia.
      * forwards~: IHn H5. simpl in Hl. lia.
        eapply wfe_inv; eauto.
        eapply bindings_shift1; eauto.
  (* top *)
  - destruct* m.
    { simpl. inverts Hgt.
      forwards~: IHn T0 H4. simpl in Hl. lia.
      repeat rewrite <-bindings_evar_sp. eauto.
    }
    { destruct* i.
      + inverts* Hgt. 
      + inverts* Hgt. 
        forwards~: IHn T0 H4. simpl in Hl. lia.
        eapply bindings_shift1; eauto.
    }
  - destruct m1.
    + inverts* Hgt. forwards~: IHn H6. simpl in Hl. lia.
      eapply wfe_inv; eauto.
      simpl. repeat rewrite <-bindings_evar_sp. eauto.
    + destruct m2.
      {
        inverts* Hgt. 
        * forwards~: bindings_zero1 (T1 & A2) T0 (T1 & A2).
          unfold bindings in H2. simpl in H2.
          unfold bindings. simpl. lia.
        * forwards~: IHn H6. simpl in Hl. lia.
          eapply wfe_inv; eauto.
          eapply bindings_shift1; eauto.
      }
      {
        inverts* Hgt. 
        * forwards~: bindings_zero1 (T1 & A2) T0 (T1 & A2).
          unfold bindings in H2. simpl in H2.
          unfold bindings. simpl. lia.
        * forwards~: IHn H6. simpl in Hl. lia.
          eapply wfe_inv; eauto.
          eapply bindings_shift1; eauto.
      } 
  - destruct m1.
    + inverts* Hgt. forwards~: IHn H5. simpl in Hl. lia.
      eapply wfe_inv; eauto.
      repeat rewrite <-bindings_evar_sp. eauto.
    + inverts* Hgt. 
      * forwards~: bindings_zero1 (T1 &s) T0 (T1 &s).
        unfold bindings in H1. simpl in H1.
        unfold bindings. simpl. lia.
      * forwards~: IHn H5. simpl in Hl. lia.
        eapply wfe_inv; eauto.
        eapply bindings_shift1; eauto.
  - destruct* m.
    + inverts* Hgt. forwards~: IHn H4. simpl in Hl. lia.
      eapply wfe_inv; eauto.
      repeat rewrite <-bindings_evar_sp. eauto.
    + inverts* Hgt.
      * forwards~: bindings_zero1 (rcd l0 A0) T0 ((rcd l0  A0)).
        unfold bindings in H0. simpl in H0.
        unfold bindings. simpl. lia.
      * forwards~: IHn H4. simpl in Hl. lia.
        eapply wfe_inv; eauto.
        eapply bindings_shift1; eauto.
Qed.

Lemma var_decr: forall T A i,
  wfe T ->
  lookt T i A ->
  bindings T A < bindings T (tvar i).
Proof.
  intros. eapply var_decr_size; eauto.
Qed.


Inductive orel: typ -> typ -> Prop :=
  | orel_nil: forall T1,
      ord T1 ->
      orel T1 T1
  | orel_evar: forall T1 T2 A,
      orel T1 T2 ->
      orel (T1 & A) (T2 & A)
  | orel_teq: forall T1 T2 A,
      orel T1 T2 ->
      orel (T1 &= A) (T2 &= A)
  | orel_star: forall T1 T2,
      orel T1 T2 ->
      orel (T1 &s) (T2 &s)
  (* key case *)
  | orel_teq_var: forall T1 T2 A,
      orel T1 T2 ->
      wft T2 A ->
      orel (T1 &s) (T2 &= A).

#[export]
Hint Constructors orel : core.

Notation "T1 <: T2" := (orel T1 T2) (at level 80).

Lemma orel_refl: forall T,
  orel T T.
Proof.
  intros T. inductions T; eauto.  
  destruct* m.
Qed.

Lemma check_orel: forall T1 T2,
  orel T1 T2 -> forall i,
  check T1 i ->
  (check T2 i) \/ (exists A, lookt T2 i A).
Proof.
  introv He. inductions He; introv Hc; try solve [eauto].
  - inverts Hc. forwards~ [?|?]: IHHe H2. destruct* H.
  - inverts* Hc. 
    + forwards~ [?|?]: IHHe H2. destruct* H.
  - inverts* Hc. 
    + forwards~ [?|?]: IHHe H0. destruct* H.
  - inverts* Hc. 
    + forwards~ [?|?]: IHHe H1. destruct* H0.
Qed.

Lemma lookt_orel: forall T1 T2,
  orel T1 T2 -> forall i A,
  lookt T1 i A ->
  lookt T2 i A.
Proof.
  introv He. inductions He; introv Hc; try solve [eauto]; try solve [inverts* Hc].
Qed.

Lemma orel_app: forall T1 T T0, 
  T <: T0 -> 
  (T +++ T1) <: (T0 +++ T1).
Proof.
  intros T1. inductions T1; introv He;
  try solve [simpl; eauto].
  - repeat rewrite <- mcon_cons.
    destruct* m.
  - repeat rewrite <- mcon_cons_st. eauto.
Qed.

Lemma orel_wfe: forall T1,
  wfe T1 -> forall T2,
  T1 <: T2 -> 
  wfe T2.
Proof.
  introv Hw. inductions Hw; introv He; try solve [eauto];
  try solve [inverts* He].
  - inverts* He.
    + forwards~ [?|?]: check_orel H4 H. destruct H0.
      eapply we_get; eauto.
    + forwards~ [?|?]: check_orel H4 H. destruct H0.
      eapply we_get; eauto.
  - inverts* He.
    + forwards~: lookt_orel H4 H. eapply we_get; eauto. 
    + forwards~: lookt_orel H4 H. eapply we_get; eauto.  
  - inverts* He.
    + econstructor; eauto.
    + econstructor; eauto. 
  - inverts* He.
    + econstructor; eauto.
    + econstructor; eauto. 
  - inverts* He.
    + econstructor; eauto.
    + econstructor; eauto. 
  - inverts* He.
    + econstructor; eauto. eapply IHHw2. econstructor.
      eapply orel_app; eauto.
    + econstructor; eauto. eapply IHHw2. econstructor.
      eapply orel_app; eauto.
Qed.

Lemma orel_wfe_sp: forall A T B,
  wft T A -> 
  wfe ((T &s) &= B) -> 
  wfe ((T &= A) &= B).
Proof.
  intros. unfold wft in H.
  eapply orel_wfe; eauto.
  econstructor.
  econstructor; eauto.
  eapply orel_refl; eauto.
Qed.

Lemma wft_all_mani: forall T A B,
  wft T A ->
  wft T (all B) ->
  wft T (mani A B).
Proof.
  intros. unfold wft in *. inverts H0. 
  forwards~: orel_wfe_sp A T B. 
Qed.

Lemma inst_orel: forall T3 T1 C,
  wfe ((T1 &s) +++ T3) ->
  wft T1 C ->
  orel ((T1 &s) +++ T3) ((T1 &= C) +++ T3).
Proof.
  intros.
  eapply orel_app.
  econstructor; eauto.
  eapply orel_refl; eauto.
Qed.


(* -------------------------------------- *)
(* inst: teq *)
(* -------------------------------------- *)
Lemma inst_wfe: forall T3 T1 C,
  wfe ((T1 &s) +++ T3) ->
  wft T1 C ->
  wfe ((T1 &= C) +++ T3).
Proof.
  intros.
  eapply orel_wfe; try eapply H; eauto.
  eapply inst_orel; eauto.
Qed.

Lemma wfe_cut: forall T1 T2,
  wfe (T2 +++ T1) ->
  wfe T2.
Proof.
  intros. gen T2. inductions T1; intros; eauto.
  - destruct m.
    + rewrite <-mcon_cons in H. eapply IHT1_1; eauto.
      eapply wfe_inv; eauto.
    + rewrite <-mcon_cons in H. eapply IHT1_1; eauto.
      eapply wfe_inv; eauto.
  - rewrite <-mcon_cons_st in H. eapply IHT1; eauto.
    eapply wfe_sinv; eauto.
Qed.


Inductive teqd : nat -> typ -> typ -> typ -> typ -> Prop :=
  | dq_int: forall T1 T2, wfe T1 -> wfe T2 -> teqd 1 T1 int int T2
  | dq_tvar: forall T1 T2 X, wfe T1 -> wfe T2 -> check T1 X -> check T2 X ->
      teqd 1 T1 (tvar X) (tvar X) T2
  | dq_eql: forall n T1 T2 X A B, lookt T1 X A -> teqd n T1 A B T2 -> teqd (S n) T1 (tvar X) B T2
  | dq_eqr: forall n T1 T2 X A B, lookt T2 X B -> teqd n T1 A B T2 -> teqd (S n) T1 A (tvar X) T2
  | dq_boxl: forall n T1 T2 T3 A B,
      teqd n T3 A B T2 ->
      wft T1 (boxt T3 A) ->
      teqd (S n) T1 (boxt T3 A) B T2
  | dq_boxr: forall n T1 T2 T3 A B,
      teqd n T1 A B T3 ->
      wft T2 (boxt T3 B) ->
      teqd (S n) T1 A (boxt T3 B) T2
  | dq_arr: forall n1 n2 T1 T2 A B C D, teqd n1 T1 A C T2 -> teqd n2 T1 B D T2 ->
      teqd (S (n1 + n2)) T1 (arr A B) (arr C D) T2
  | dq_all: forall n T1 T2 A C, teqd n (T1 &s) A C (T2 &s) -> teqd (S n) T1 (all A) (all C) T2
  | dq_manil: forall n T1 T2 A B C, teqd n (T1 &= A) B (tshift 0 C) (T2 &s) -> teqd (S n) T1 (mani A B) C T2
  | dq_manir: forall n T1 T2 A B C, teqd n (T1 &s) (tshift 0 B) C (T2 &= A) -> teqd (S n) T1 B (mani A C) T2
  | dq_top: forall T1 T2, wfe T1 -> wfe T2 -> teqd 1 T1 top top T2
  | dq_and: forall n1 n2 T1 T2 T3 T4 A B m, teqd n1 T1 T3 T4 T2 -> lshape T3 -> lshape T4 ->
      teqd n2 (T1 +++ T3) A B (T2 +++ T4) -> teqd (S (n1 + n2)) T1 (and T3 m A) (and T4 m B) T2
  | dq_ands: forall n T1 T2 T3 T4, teqd n T1 T3 T4 T2 -> lshape T3 -> lshape T4 ->
      teqd (S n) T1 (T3 &s) (T4 &s) T2
  | dq_rcd: forall n T1 T2 l A B, teqd n T1 A B T2 -> teqd (S n) T1 (rcd l A) (rcd l B) T2.

#[local] Hint Constructors teqd : core.

Lemma mcon_top: forall T, wfe T -> (top +++ T) = T.
Proof.
  inductions T; introv Hw; try solve [inverts Hw].
  - reflexivity.
  - assert (wfe T1) by (eapply wfe_inv; eauto).
    rewrite <- mcon_cons. rewrite IHT1; auto.
  - rewrite <- mcon_cons_st. f_equal.
    match goal with |- (top +++ ?X) = ?X =>
      match goal with IH: wfe X -> _ |- _ => apply IH; eapply wfe_sinv; eauto end end.
Qed.

Lemma lookt_from_check: forall T2 X, check T2 X ->
  forall T1 A, lookt (T1 +++ T2) X A -> lookt T2 X A.
Proof.
  introv Hc. inductions Hc; introv Hl.
  - rewrite <- mcon_cons in Hl. inverts Hl. econstructor. eapply IHHc; eauto.
  - rewrite <- mcon_cons in Hl. inverts Hl. econstructor. eapply IHHc; eauto.
  - rewrite <- mcon_cons_st in Hl. inverts Hl.
  - rewrite <- mcon_cons_st in Hl. inverts Hl. econstructor. eapply IHHc; eauto.
Qed.

Lemma lookt_strip_wft: forall T2 X, wft T2 (tvar X) ->
  forall T1 A, lookt (T1 +++ T2) X A -> lookt T2 X A.
Proof.
  introv Hwf Hl. unfold wft in Hwf. inverts Hwf.
  - eapply lookt_from_check; eassumption.
  - match goal with Hg: lookt T2 X ?A0 |- _ =>
      forwards Hla: lookt_app Hg T1; forwards: lookt_det Hl Hla; subst; eassumption end.
Qed.

Lemma lookt_swap_wft: forall T2 X, wft T2 (tvar X) ->
  forall T1 A, lookt (T1 +++ T2) X A -> forall T1', lookt (T1' +++ T2) X A.
Proof.
  introv Hwf Hl. forwards Hlt: lookt_strip_wft Hwf Hl. introv. eapply lookt_app; eauto.
Qed.

(* If X is a wft tvar in T2 and is a check-position of T1+++T2, then it is a
   check-position of T2 (the lookt alternative is impossible), so it swaps. *)
Lemma check_swap_wft: forall T2 X, wft T2 (tvar X) ->
  forall T1, check (T1 +++ T2) X -> forall T1', check (T1' +++ T2) X.
Proof.
  introv Hwf Hc. unfold wft in Hwf. inverts Hwf.
  - introv. eapply check_app; eassumption.
  - match goal with Hg: lookt T2 X ?A0 |- _ =>
      forwards Hla: lookt_app Hg T1;
      exfalso; eapply lookt_check_false; eassumption end.
Qed.


Lemma teqd_teq: forall n T1 A B T2, teqd n T1 A B T2 -> teq T1 A B T2.
Proof.
  introv H. inductions H; eauto.
Qed.

Lemma teq_teqd: forall T1 A B T2, teq T1 A B T2 -> exists n, teqd n T1 A B T2.
Proof.
  introv H. inductions H;
    repeat match goal with He: exists _, _ |- _ => destruct He end;
    eexists; econstructor; eauto.
Qed.

Lemma teqd_wft_left: forall n T1 A B T2, teqd n T1 A B T2 -> wft T1 A.
Proof. introv H. eapply teq_wft_left. eapply teqd_teq; eauto. Qed.

Lemma teqd_wft_right: forall n T1 A B T2, teqd n T1 A B T2 -> wft T2 B.
Proof. introv H. eapply teq_wft_right. eapply teqd_teq; eauto. Qed.

Lemma teq_spine_keyLen: forall G1 T4 T5 G2,
  teq G1 T4 T5 G2 -> lshape T4 -> lshape T5 -> keyLen T4 = keyLen T5.
Proof.
  introv H. inductions H; introv Hl4 Hl5;
    try solve [inverts Hl4 | inverts Hl5]; simpl; eauto.
  - inverts Hl4; inverts Hl5; destruct m; simpl;
      [ eapply IHteq1; eauto | f_equal; eapply IHteq1; eauto ].
Qed.



Lemma check_app_dec: forall T4, lshape T4 -> forall T2 Y0,
  check (T2 +++ T4) Y0 ->
  (Y0 < keyLen T4) \/
  (exists Y0', Y0 = keyLen T4 + Y0' /\ check T2 Y0').
Proof.
  introv Hl. inductions Hl; intros T2 Y0 Hc.
  - (* top *) simpl in *. right. exists Y0. split; eauto.
  - (* and T m A *) rewrite <- mcon_cons in Hc; inverts Hc;
      match goal with Hh: check (T2 +++ _) _ |- _ => forwards Hdis: IHHl Hh end;
      (destruct Hdis as [Hlt | (Y0'&Heq1&Hin)];
        [ left; simpl; lia | right; exists Y0'; simpl; subst; split; eauto ]).
  - (* T &s : binding, +1 key *)
    rewrite <- mcon_cons_st in Hc; inverts Hc.
    + left. simpl. lia.
    + match goal with Hh: check (T2 +++ _) _ |- _ => forwards Hdis: IHHl Hh end.
      destruct Hdis as [Hlt | (Y0'&Heq1&Hin)];
        [ left; simpl; lia | right; exists Y0'; simpl; subst; split; eauto ].
Qed.


Lemma rigid_insert_rev: forall dd T' B, rigid dd T' B ->
  forall X T A d, insert_tvar X T T' -> B = tshift X A -> dd = S d -> X <= d ->
  rigid d T A.
Proof.
  introv Hr. induction Hr; introv Hi Heq Hdd Hle.
  - (* rigid_int *) destruct A; simpl in Heq;
      try (destruct m); try (destruct (le_gt_dec X n)); try discriminate; constructor.
  - (* rigid_top *) destruct A; simpl in Heq;
      try (destruct m); try (destruct (le_gt_dec X n)); try discriminate; constructor.
  - (* rigid_bvar: tvar X0, check T' X0, X0 < dd *)
    destruct A; simpl in Heq; try (destruct m); try discriminate;
      try (destruct (le_gt_dec X n0); discriminate).
    subst d. destruct (le_gt_dec X0 n).
    + inverts Heq. eapply rigid_bvar; [ eapply check_insert_tvar_ge_rev; eauto | lia ].
    + inverts Heq. eapply rigid_bvar; [ eapply check_insert_tvar_lt_rev; eauto | lia ].
  - (* rigid_cvar: tvar X0, lookt T' X0 B, rigid dd T' B *)
    destruct A; simpl in Heq; try (destruct m); try discriminate;
      try (destruct (le_gt_dec X n0); discriminate).
    destruct (le_gt_dec X0 n).
    + inverts Heq.
      forwards (A0 & Hlk0): lookt_insert_tvar_ge_rev Hi H; [ lia | ].
      forwards Hfwd: lookt_insert_tvar_ge Hi Hlk0; [ lia | ].
      forwards Heqb: lookt_det H Hfwd. subst B.
      eapply rigid_cvar; [ exact Hlk0 | eapply IHHr; eauto ].
    + inverts Heq.
      forwards (A0 & Hlk0): lookt_insert_tvar_lt_rev Hi H; [ lia | ].
      forwards Hfwd: lookt_insert_tvar_lt Hi Hlk0; [ lia | ].
      forwards Heqb: lookt_det H Hfwd. subst B.
      eapply rigid_cvar; [ exact Hlk0 | eapply IHHr; eauto ].
  - (* rigid_arr *) destruct A0; simpl in Heq; try (destruct m); try discriminate;
      try (destruct (le_gt_dec X n); discriminate).
    inverts Heq. constructor; [ eapply IHHr1; eauto | eapply IHHr2; eauto ].
  - (* rigid_rcd *) destruct A0; simpl in Heq; try (destruct m); try discriminate;
      try (destruct (le_gt_dec X n); discriminate).
    inverts Heq. eapply rigid_rcd. eapply IHHr; eauto.
  - (* rigid_mani: rigid (S dd) (T' &= A) B -> rigid dd T' (mani A B) *)
    destruct A0; simpl in Heq; try (destruct m); try discriminate;
      try (destruct (le_gt_dec X n); discriminate).
    inverts Heq. eapply rigid_mani.
    eapply IHHr with (X := S X) (T := T0 &= A0_1);
      [ eapply itv_teq; eauto | reflexivity | lia | lia ].
  - (* rigid_and *) destruct A0; rewrite ?tshift_and in Heq; simpl in Heq;
      try discriminate; try (destruct (le_gt_dec X n); discriminate).
    (* A0 = and A0_1 m0 A0_2; Heq : and A m B = and (tshift X A0_1) m0 (tshift (keyLen A0_1 + X) A0_2) *)
    inverts Heq.
    eapply rigid_and.
    + eapply IHHr1; eauto.
    + eapply IHHr2 with (X := keyLen A0_1 + X) (T := T0 +++ A0_1);
        [ eapply insert_tvar_env; eauto | reflexivity
        | rewrite <- (keyLen_same A0_1 X); lia | lia ].
  - (* rigid_ands *) destruct A0; simpl in Heq; try (destruct m); try discriminate;
      try (destruct (le_gt_dec X n); discriminate).
    inverts Heq. eapply rigid_ands. eapply IHHr; eauto.
  - (* rigid_all *) destruct A0; simpl in Heq; try (destruct m); try discriminate;
      try (destruct (le_gt_dec X n); discriminate).
    inverts Heq. eapply rigid_all.
    eapply IHHr with (X := S X) (T := T0 &s);
      [ eapply itv_tvar; eauto | reflexivity | lia | lia ].
  - (* rigid_box: tshift does not descend into boxt *)
    destruct A0; simpl in Heq; try (destruct m); try discriminate;
      try (destruct (le_gt_dec X n); discriminate).
    inverts Heq. eapply rigid_box. eassumption.
Qed.

Lemma rigid_unpad_s: forall d T C, rigid (S d) (T &s) (tshift 0 C) -> rigid d T C.
Proof.
  introv Hr. eapply rigid_insert_rev;
    [ exact Hr | eapply itv_here2 | reflexivity | reflexivity | lia ].
Qed.

(* Forward direction: inserting an unreferenced binder splices one bound-variable
   level into the rigid window, so the depth grows by one and the type is shifted
   over the insertion point. *)
Lemma rigid_insert: forall d T A, rigid d T A ->
  forall X T', insert_tvar X T T' -> X <= d ->
  rigid (S d) T' (tshift X A).
Proof.
  introv Hr. induction Hr; introv Hi Hle.
  - simpl. constructor.
  - simpl. constructor.
  - (* rigid_bvar *) simpl. destruct (le_gt_dec X0 X).
    + eapply rigid_bvar; [ eapply check_insert_tvar_ge; eauto | lia ].
    + eapply rigid_bvar; [ eapply check_insert_tvar_lt; eauto; lia | lia ].
  - (* rigid_cvar *) simpl. destruct (le_gt_dec X0 X).
    + eapply rigid_cvar; [ eapply lookt_insert_tvar_ge; eauto | eapply IHHr; eauto ].
    + eapply rigid_cvar; [ eapply lookt_insert_tvar_lt; eauto; lia | eapply IHHr; eauto ].
  - (* rigid_arr *) simpl. constructor; [ eapply IHHr1; eauto | eapply IHHr2; eauto ].
  - (* rigid_rcd *) simpl. eapply rigid_rcd. eapply IHHr; eauto.
  - (* rigid_mani *) simpl. eapply rigid_mani.
    eapply IHHr with (X := S X); [ eapply itv_teq; eauto | lia ].
  - (* rigid_and *) rewrite tshift_and. eapply rigid_and.
    + eapply IHHr1; eauto.
    + replace (S d + keyLen (tshift X A)) with (S (d + keyLen A))
        by (rewrite <- (keyLen_same A X); lia).
      eapply IHHr2 with (X := keyLen A + X);
        [ eapply insert_tvar_env; eauto | lia ].
  - (* rigid_ands *) rewrite tshift_st. eapply rigid_ands. eapply IHHr; eauto.
  - (* rigid_all *) simpl. eapply rigid_all.
    eapply IHHr with (X := S X); [ eapply itv_tvar; eauto | lia ].
  - (* rigid_box *) simpl. eapply rigid_box. eassumption.
Qed.

Lemma rigid_pad_s: forall d T A, rigid d T A -> rigid (S d) (T &s) (tshift 0 A).
Proof.
  introv Hr. eapply rigid_insert; [ exact Hr | eapply itv_here2 | lia ].
Qed.

Lemma teqd_rigid_gen_r: forall n T1 A B T2, teqd n T1 A B T2 ->
  forall d1 d2, (forall X, check T1 X -> X < d1 -> check T2 X -> X < d2) ->
  rigid d1 T1 A -> rigid d2 T2 B.
Proof.
  introv H. induction H; introv Hal Hrig.
  - (* dq_int *) inverts Hrig. constructor.
  - (* dq_tvar *) inverts Hrig.
    + eapply rigid_bvar; [ eassumption | eapply Hal; eassumption ].
    + exfalso. eapply lookt_check_false; [ eassumption | exact H1 ].
  - (* dq_eql *) inverts Hrig.
    + exfalso. match goal with Hck: check T1 X |- _ =>
        eapply lookt_check_false; [ eassumption | exact Hck ] end.
    + eapply IHteqd; eauto.
      match goal with Hlk: lookt T1 X ?B1, Hlk2: lookt T1 X A |- _ =>
        forwards Heqv: lookt_det Hlk Hlk2; subst end. eauto.
  - (* dq_eqr *) eapply rigid_cvar; [ exact H | eapply IHteqd; eauto ].
  - (* dq_boxl: goal rigid d2 T2 B; IH at d1:=0 on teqd n T3 A B T2, rigid 0 T3 A
       (recovered from box-wft via wft_box_rigid) *)
    apply (IHteqd 0 d2); [ intros X Hc1 Hlt Hc2; lia | eapply wft_box_rigid; eassumption ].
  - (* dq_boxr: goal rigid d2 T2 (boxt T3 B) from rigid 0 T3 B via box-wft *)
    eapply rigid_box; eapply wft_box_rigid; eassumption.
  - (* dq_arr *) inverts Hrig. constructor; [ apply (IHteqd1 d1 d2); auto | apply (IHteqd2 d1 d2); auto ].
  - (* dq_all *) inverts Hrig. eapply rigid_all.
    apply (IHteqd (S d1) (S d2)); [ | assumption ].
    intros X Hc1 HltX Hc2. destruct X as [|X].
    + lia.
    + inverts Hc1. inverts Hc2.
      forwards: Hal; [ eassumption | lia | eassumption | lia ].
  - (* dq_manil: left ctx pads &= (index bumps), right ctx pads &s.  Both contexts
       grow by one binder; bump BOTH d1 and d2.  Conclusion rigid d2 T2 C from IH's
       rigid (S d2) (T2 &s) (tshift 0 C) via rigid_unpad_s. *)
    inverts Hrig. eapply rigid_unpad_s.
    apply (IHteqd (S d1) (S d2)); [ | assumption ].
    intros X Hc1 HltX Hc2. destruct X as [|X].
    + lia.
    + inverts Hc1. inverts Hc2.
      forwards: Hal; [ eassumption | lia | eassumption | lia ].
  - (* dq_manir: symmetric.  Left input B must be PADDED into ctx T1&s via
       rigid_pad_s; the right output C in ctx T2&=A is exactly rigid_mani's premise. *)
    eapply rigid_mani.
    apply (IHteqd (S d1) (S d2)); [ | eapply rigid_pad_s; assumption ].
    intros X Hc1 HltX Hc2. destruct X as [|X].
    + lia.
    + inverts Hc1. inverts Hc2.
      forwards: Hal; [ eassumption | lia | eassumption | lia ].
  - (* dq_top *) inverts Hrig. constructor.
  - (* dq_and *) inverts Hrig.
    assert (HkL: keyLen T3 = keyLen T4) by
      (eapply teq_spine_keyLen; [ eapply teqd_teq; exact H | exact H0 | exact H1 ]).
    eapply rigid_and;
      [ apply (IHteqd1 d1 d2); auto
      | apply (IHteqd2 (d1 + keyLen T3) (d2 + keyLen T4)); [ | assumption ];
        intros X Hc1 HltX Hc2;
        forwards [HltX3 | (X1&HeqX1&HcT1)]: check_app_dec H0 Hc1;
        [ lia
        | forwards [HltX4 | (X2&HeqX2&HcT2)]: check_app_dec H1 Hc2;
          [ lia
          | subst X; assert (X1 = X2) by lia; subst X2;
            forwards: Hal HcT1; [ lia | exact HcT2 | lia ] ] ] ].
  - (* dq_ands *) inverts Hrig. eapply rigid_ands. apply (IHteqd d1 d2); auto.
  - (* dq_rcd *) inverts Hrig. eapply rigid_rcd. apply (IHteqd d1 d2); auto.
Qed.

Lemma teqd_rigid_r: forall n T1 A B T2,
  teqd n T1 A B T2 -> rigid 0 T1 A -> rigid 0 T2 B.
Proof.
  introv H Hr. eapply teqd_rigid_gen_r with (d1 := 0) (d2 := 0);
    [ exact H | intros X Hc1 Hlt Hc2; lia | exact Hr ].
Qed.

(* Peel a resolved middle type variable: if the left operand of a teqd is a tvar
   that lookt-resolves to B, the teqd can be re-stated on B directly (the
   resolution chain on the OTHER side, dq_eqr/boxr/manir, is preserved). *)
Lemma teqd_peel_l: forall n T X C T', teqd n T (tvar X) C T' ->
  forall B, lookt T X B -> exists m, m < n /\ teqd m T B C T'.
Proof.
  intros n. induction n using lt_wf_ind. introv Hd Hlk. inverts Hd;
    try solve [exfalso; eauto using lookt_check_false].
  - match goal with Hl: lookt T X ?A0 |- _ => forwards Heq: lookt_det Hl Hlk; subst end.
    eexists. split; [ | eassumption ]. lia.
  - match goal with Hi: teqd ?k T (tvar X) ?B0 ?T'' |- _ =>
      forwards (m & Hm & Hd'): H Hi Hlk; [ lia | ] end.
    eexists. split; [ | eapply dq_eqr; eassumption ]. lia.
  - match goal with Hi: teqd ?k T (tvar X) ?B0 ?T'' |- _ =>
      forwards (m & Hm & Hd'): H Hi Hlk; [ lia | ] end.
    eexists. split; [ | eapply dq_boxr; [ exact Hd' | eassumption ] ]. lia.
  - (* dq_manir: H0 : teqd n0 (T &s) (tshift 0 (tvar X)) C0 (T' &= A);
       tshift 0 (tvar X) = tvar (S X).  Peel the shifted var via the &s-padded lookt. *)
    match goal with Hi: teqd ?k (T &s) (tshift 0 (tvar X)) ?C0 (?T' &= ?A) |- _ =>
      forwards (m & Hm & Hd'): H Hi (lookt_etvar Hlk); [ lia | ] end.
    eexists. split; [ | eapply dq_manir; simpl in Hd'; eassumption ]. lia.
Qed.

Lemma teqd_peel_r: forall n T A X T', teqd n T A (tvar X) T' ->
  forall B, lookt T' X B -> exists m, m < n /\ teqd m T A B T'.
Proof.
  intros n. induction n using lt_wf_ind. introv Hd Hlk. inverts Hd;
    try solve [exfalso; eauto using lookt_check_false].
  - match goal with Hi: teqd ?k ?Tf ?A0 (tvar X) ?T'' |- _ =>
      forwards (m & Hm & Hd'): H Hi Hlk; [ lia | ] end.
    eexists. split; [ | eapply dq_eql; eassumption ]. lia.
  - match goal with Hl: lookt T' X ?A0 |- _ => forwards Heq: lookt_det Hl Hlk; subst end.
    eexists. split; [ | eassumption ]. lia.
  - match goal with Hi: teqd ?k ?Tf ?A0 (tvar X) ?T'' |- _ =>
      forwards (m & Hm & Hd'): H Hi Hlk; [ lia | ] end.
    eexists. split; [ | eapply dq_boxl; [ exact Hd' | eassumption ] ]. lia.
  - (* dq_manil: H0 : teqd n0 (T &= A0) B0 (tshift 0 (tvar X)) (T' &s);
       peel the &s-padded right var via lookt_etvar. *)
    match goal with Hi: teqd ?k (?Tf &= ?A0) ?B0 (tshift 0 (tvar X)) (T' &s) |- _ =>
      forwards (m & Hm & Hd'): H Hi (lookt_etvar Hlk); [ lia | ] end.
    eexists. split; [ | eapply dq_manil; simpl in Hd'; eassumption ]. lia.
Qed.

(* ===== align / rigid_lookt RELOCATED here (needed by the size-preserving teqd
   shift suite below, which the manil/manir composition cases of teqd_trans use). *)
Definition align (T1 T2 : typ) (d Y : nat) : Prop :=
  forall X, check T1 X -> X < d -> check T2 X -> X < Y.

Lemma align_and: forall T1 T2 T3 T4 d Y,
  align T1 T2 d Y -> lshape T3 -> lshape T4 ->
  keyLen T3 = keyLen T4 ->
  align (T1 +++ T3) (T2 +++ T4) (d + keyLen T3) (keyLen T4 + Y).
Proof.
  introv Hal Hl3 Hl4 HkL. unfold align in *. introv Hc1 Hlt Hc2.
  forwards [HltX | (X'&HeqX&HcX)]: check_app_dec Hl3 Hc1.
  - lia.
  - subst.
    forwards [HltY | (X''&HeqY&HcY)]: check_app_dec Hl4 Hc2.
    + lia.
    + assert (X' = X'') by lia. subst.
      forwards HY: Hal HcX; [ lia | exact HcY | ]. lia.
Qed.

Lemma rigid_lookt: forall d T X A,
  rigid d T (tvar X) -> lookt T X A -> rigid d T A.
Proof.
  introv Hr Hl. inverts Hr.
  - match goal with Hck: check T X |- _ =>
      exfalso; eapply lookt_check_false; [ exact Hl | exact Hck ] end.
  - match goal with Hlk: lookt T X ?B0, Hrb: rigid d T ?B0 |- _ =>
      forwards Heq: lookt_det Hl Hlk; subst; exact Hrb end.
Qed.

(* ===== size-preserving teqd shift suite (teqd analog of the teq rigid/both
   shift lemmas).  Needed by the manil/manir composition cases of teqd_trans. *)
Lemma teqd_shift_tvar_r_rigid_aux: forall n T1 A B T2,
  teqd n T1 A B T2 -> forall d Y T2', rigid d T1 A ->
  insert_tvar Y T2 T2' -> wfe T2' -> align T1 T2 d Y ->
  teqd n T1 A (tshift Y B) T2'.
Proof.
  introv Ht. inductions Ht; introv Hr Hi Hw2 Hal.
  - simpl. eapply dq_int; eauto.
  - rename H1 into HcX. rename H2 into HcY. inverts Hr.
    + match goal with Hxd: _ < d |- _ =>
        forwards~ HY: Hal HcX Hxd HcY end.
      simpl. match goal with |- context[le_gt_dec ?a ?b] => destruct (le_gt_dec a b) as [Hle|Hgt]; [lia|] end.
      eapply dq_tvar; eauto. eapply check_insert_tvar_lt; eauto.
    + exfalso. eapply lookt_check_false; [ eassumption | exact HcX ].
  - eapply dq_eql; [ exact H |]. eapply IHHt; eauto.
    eapply rigid_lookt; [ exact Hr | exact H ].
  - simpl. destruct (le_gt_dec Y X) eqn:E.
    + eapply dq_eqr.
      * forwards~ HL: lookt_insert_tvar_ge Hi l H. simpl in HL. exact HL.
      * eapply IHHt; eauto.
    + eapply dq_eqr.
      * forwards~ HL: lookt_insert_tvar_lt Hi g H. exact HL.
      * eapply IHHt; eauto.
  - inverts Hr.
    eapply dq_boxl;
      [ eapply IHHt; [ eassumption | exact Hi | exact Hw2 |];
        unfold align; introv Hin Hlt Hin2; lia
      | match goal with Hb: wft T1 (boxt T3 A) |- _ => exact Hb end ].
  - assert (Hbe: tshift Y (boxt T3 B) = boxt T3 B) by reflexivity.
    rewrite Hbe.
    match goal with Hb: wft T2 (boxt T3 B) |- _ =>
      forwards (Hbd & _ & _): boxt_wft_inv Hb;
      forwards Hrg: wft_box_rigid Hb end.
    eapply dq_boxr;
      [ eassumption
      | unfold wft; eapply we_box; [ exact Hbd | exact Hrg | exact Hw2 ] ].
  - inverts Hr. simpl. eapply dq_arr; eauto.
  - inverts Hr. simpl. eapply dq_all.
    eapply IHHt; [ eassumption | eapply itv_tvar; exact Hi | eapply we_tvar; exact Hw2 |].
    unfold align. introv Hc1 Hlt Hc2. destruct X as [|X].
    + lia.
    + inverts Hc1. inverts Hc2.
      forwards HY: Hal; [ eassumption | lia | eassumption | ]. lia.
  - inverts Hr. simpl. eapply dq_manil.
    forwards Heq: tshift_tshift_prop_1 C 0 Y. simpl in Heq. rewrite Heq.
    eapply IHHt; [ eassumption | eapply itv_tvar; exact Hi | eapply we_tvar; exact Hw2 |].
    unfold align. introv Hin Hlt Hin2. destruct X as [|X].
    + lia.
    + inverts Hin. inverts Hin2.
      match goal with Hc1: check T1 ?xx, Hc2: check T2 ?xx |- _ =>
        forwards HY: Hal Hc1; [ lia | exact Hc2 | ] end. lia.
  - simpl. eapply dq_manir.
    forwards Hwr: teqd_wft_right Ht.
    eapply IHHt; [ eapply rigid_pad_s; exact Hr | eapply itv_teq; exact Hi
                 | eapply itvar_wfe; [ eapply itv_teq; exact Hi | eapply wft_wfe; exact Hwr ] |].
    unfold align. introv Hin Hlt Hin2. destruct X as [|X].
    + lia.
    + inverts Hin. inverts Hin2.
      match goal with Hc1: check T1 ?xx, Hc2: check T2 ?xx |- _ =>
        forwards HY: Hal Hc1; [ lia | exact Hc2 | ] end. lia.
  - simpl. eapply dq_top; eauto.
  - inverts Hr.
    forwards Hwr: teqd_wft_right Ht2.
    forwards Hins: insert_tvar_env Hi T4.
    assert (HkL: keyLen T3 = keyLen T4) by
      (eapply teq_spine_keyLen; [ eapply teqd_teq; exact Ht1 | exact H | exact H0 ]).
    rewrite tshift_and. eapply dq_and;
      [ eapply IHHt1; [ eassumption | exact Hi | exact Hw2 |];
        solve [ unfold align; introv Hin Hlt Hin2; eapply Hal; eauto ]
      | assumption
      | eapply lshape_tshift; assumption
      | eapply IHHt2;
          [ eassumption
          | exact Hins
          | eapply itvar_wfe; [ exact Hins | eapply wft_wfe; exact Hwr ]
          | solve [ eapply align_and; eauto ] ] ].
  - inverts Hr. simpl. eapply dq_ands.
    + eapply IHHt; [ eassumption | exact Hi | exact Hw2 | exact Hal ].
    + assumption.
    + eapply lshape_tshift; assumption.
  - inverts Hr. simpl. eapply dq_rcd; eauto.
Qed.

Lemma teqd_shift_tvar_r_rigid: forall n T1 A B T2,
  teqd n T1 A B T2 -> forall Y T2', rigid 0 T1 A ->
  insert_tvar Y T2 T2' -> wfe T2' ->
  teqd n T1 A (tshift Y B) T2'.
Proof.
  introv Ht Hr Hi Hw2.
  eapply teqd_shift_tvar_r_rigid_aux; eauto.
  unfold align. introv Hin Hlt Hin2. lia.
Qed.

Lemma teqd_sym: forall n T1 A B T2, teqd n T1 A B T2 -> teqd n T2 B A T1.
Proof.
  introv Ht. inductions Ht; try solve [econstructor; eauto].
Qed.


Lemma teqd_shift_tvar_l_rigid: forall n T1 A B T2,
  teqd n T1 A B T2 -> forall X T1', rigid 0 T2 B ->
  insert_tvar X T1 T1' -> wfe T1' ->
  teqd n T1' (tshift X A) B T2.
Proof.
  introv Ht Hr Hi Hw1.
  eapply teqd_sym.
  eapply teqd_shift_tvar_r_rigid; [ eapply teqd_sym; exact Ht | exact Hr | exact Hi | exact Hw1 ].
Qed.

(* size-preserving two-sided shift at a SINGLE shared keyLen-position. *)
Lemma teqd_shift_both: forall n T1 A B T2,
  teqd n T1 A B T2 -> forall X T1' T2',
  insert_both X T1 T1' T2 T2' ->
  wfe T1' -> wfe T2' ->
  teqd n T1' (tshift X A) (tshift X B) T2'.
Proof.
  introv Ht. inductions Ht; introv Hi Hw1 Hw2;
  forwards Hi1: insert_both_left Hi; forwards Hi2: insert_both_right Hi.
  - simpl. eapply dq_int; eauto.
  - simpl. destruct (le_gt_dec X0 X).
    + forwards Hca: check_insert_tvar_ge Hi1 l H1.
      forwards Hcb: check_insert_tvar_ge Hi2 l H2.
      eapply dq_tvar; [ exact Hw1 | exact Hw2 | exact Hca | exact Hcb ].
    + forwards Hca: check_insert_tvar_lt Hi1 g H1.
      forwards Hcb: check_insert_tvar_lt Hi2 g H2.
      eapply dq_tvar; [ exact Hw1 | exact Hw2 | exact Hca | exact Hcb ].
  - forwards HIH: IHHt Hi Hw1 Hw2. simpl.
    destruct (le_gt_dec X0 X).
    + forwards HL: lookt_insert_tvar_ge Hi1 l H. eapply dq_eql; eauto.
    + forwards HL: lookt_insert_tvar_lt Hi1 g H. eapply dq_eql; eauto.
  - forwards HIH: IHHt Hi Hw1 Hw2. simpl.
    destruct (le_gt_dec X0 X).
    + forwards HL: lookt_insert_tvar_ge Hi2 l H. eapply dq_eqr; eauto.
    + forwards HL: lookt_insert_tvar_lt Hi2 g H. eapply dq_eqr; eauto.
  - assert (Hbe: tshift X (boxt T3 A) = boxt T3 A) by reflexivity.
    rewrite Hbe. eapply dq_boxl.
    + eapply teqd_shift_tvar_r_rigid; [ exact Ht | eapply wft_box_rigid; exact H | exact Hi2 | exact Hw2 ].
    + forwards Hbox: insert_tvar_wft Hi1 Hw1 H. simpl in Hbox. exact Hbox.
  - assert (Hbe: tshift X (boxt T3 B) = boxt T3 B) by reflexivity.
    rewrite Hbe. eapply dq_boxr.
    + eapply teqd_shift_tvar_l_rigid; [ exact Ht | eapply wft_box_rigid; exact H | exact Hi1 | exact Hw1 ].
    + forwards Hbox: insert_tvar_wft Hi2 Hw2 H. simpl in Hbox. exact Hbox.
  - simpl. eapply dq_arr; eauto.
  - simpl. eapply dq_all.
    eapply IHHt with (X := S X); eauto.
  - simpl. eapply dq_manil.
    forwards Heq: tshift_tshift_prop_1 C 0 X. simpl in Heq. rewrite Heq.
    forwards Hwl: teqd_wft_left Ht.
    forwards Hib: ib_manil A Hi.
    eapply IHHt with (X := S X).
    + exact Hib.
    + eapply itvar_wfe; [ eapply insert_both_left; exact Hib | eapply wft_wfe; exact Hwl ].
    + eapply we_tvar; exact Hw2.
  - simpl. eapply dq_manir.
    forwards Heq: tshift_tshift_prop_1 B 0 X. simpl in Heq. rewrite Heq.
    forwards Hwr: teqd_wft_right Ht.
    forwards Hib: ib_manir A Hi.
    eapply IHHt with (X := S X).
    + exact Hib.
    + eapply we_tvar; exact Hw1.
    + eapply itvar_wfe; [ eapply insert_both_right; exact Hib | eapply wft_wfe; exact Hwr ].
  - simpl. eapply dq_top; eauto.
  - forwards Hwl: teqd_wft_left Ht2.
    forwards Hwr: teqd_wft_right Ht2.
    forwards Hib: insert_both_env (teqd_teq Ht1) H H0 Hi.
    assert (HkL: keyLen T3 = keyLen T4) by
      (eapply teq_spine_keyLen; [ eapply teqd_teq; exact Ht1 | exact H | exact H0 ]).
    destruct m; simpl; rewrite <- HkL; eapply dq_and;
      [ eapply IHHt1; [ exact Hi | exact Hw1 | exact Hw2 ]
      | eapply lshape_tshift; exact H
      | eapply lshape_tshift; exact H0
      | eapply IHHt2;
          [ exact Hib
          | eapply itvar_wfe; [ eapply insert_both_left; exact Hib | eapply wft_wfe; exact Hwl ]
          | eapply itvar_wfe; [ eapply insert_both_right; exact Hib | eapply wft_wfe; exact Hwr ] ]
      | eapply IHHt1; [ exact Hi | exact Hw1 | exact Hw2 ]
      | eapply lshape_tshift; exact H
      | eapply lshape_tshift; exact H0
      | eapply IHHt2;
          [ exact Hib
          | eapply itvar_wfe; [ eapply insert_both_left; exact Hib | eapply wft_wfe; exact Hwl ]
          | eapply itvar_wfe; [ eapply insert_both_right; exact Hib | eapply wft_wfe; exact Hwr ] ] ].
  - simpl. eapply dq_ands;
      [ eapply IHHt; [ exact Hi | exact Hw1 | exact Hw2 ]
      | eapply lshape_tshift; exact H
      | eapply lshape_tshift; exact H0 ].
  - simpl. eapply dq_rcd; eauto.
Qed.

(* ===== REVERSE one-sided rigid shift (the inverse of teq_shift_tvar_r_rigid_aux).
   Strips a dead inserted &s binder from the RIGHT env (insert_tvar Y T2 T2') and
   un-shifts the right type (C = tshift Y B), keeping the rigid LEFT type A fixed.
   Rigidity of A + positional eq_tvar makes the right var inherit `< d <= Y`, so the
   shift never moved it and the reverse-unshift is the identity on it. *)
Lemma teq_shift_tvar_r_rigid_rev_aux: forall T1 A C T2',
  teq T1 A C T2' -> forall d Y T2 Bz, rigid d T1 A ->
  insert_tvar Y T2 T2' -> C = tshift Y Bz -> wfe T2 ->
  d <= Y ->
  teq T1 A Bz T2.
Proof.
  introv Ht. inductions Ht; introv Hr Hi Heq Hw2 Hal.
  - (* eq_int *) destruct Bz; rewrite ?tshift_and in Heq; simpl in Heq;
      try (destruct m); try discriminate;
      try (destruct (le_gt_dec Y n); discriminate). eapply eq_int; eauto.
  - (* eq_tvar *) inverts Hr.
    + (* rigid_bvar : X < d <= Y ; the right var is unmoved ; Bz must be tvar X *)
      match goal with HcX: check T1 ?X, Hxd: ?X < d, HcY: check ?TR ?X |- _ =>
        assert (HltY: X < Y) by lia end.
      destruct Bz as [ | nv | ? ? | ? | ? ? | ? ? | ? ? | | ? ? ? | ? ];
        rewrite ?tshift_and in Heq; simpl in Heq; try (destruct m); try discriminate.
      destruct (le_gt_dec Y nv); inverts Heq; [lia|].
      eapply eq_tvar; eauto. eapply check_insert_tvar_lt_rev; eauto.
    + (* rigid_cvar : lookt T1 X B0 contradicts check T1 X *)
      exfalso. match goal with HcX: check T1 ?X |- _ =>
        eapply lookt_check_false; [ eassumption | exact HcX ] end.
  - (* eq_eql : left var, lookt T1 X A; recurse, right unshifts *)
    eapply eq_eql; [ exact H |].
    eapply IHHt; eauto.
    eapply rigid_lookt; [ exact Hr | exact H ].
  - (* eq_eqr : right var, lookt T2' X B0 ; Bz must be a tvar *)
    destruct Bz as [ | nv | ? ? | ? | ? ? | ? ? | ? ? | | ? ? ? | ? ];
      rewrite ?tshift_and in Heq; simpl in Heq; try (destruct m); try discriminate.
    destruct (le_gt_dec Y nv) eqn:E.
    + (* X = S nv, nv >= Y *)
      inverts Heq.
      forwards (A0 & Hlk0): lookt_insert_tvar_ge_rev Hi H; [lia|].
      forwards Hfwd: lookt_insert_tvar_ge Hi Hlk0; [lia|].
      forwards Heqb: lookt_det H Hfwd. subst B.
      eapply eq_eqr; [ exact Hlk0 |].
      eapply IHHt; eauto.
    + (* X = nv < Y *)
      inverts Heq.
      forwards (A0 & Hlk0): lookt_insert_tvar_lt_rev Hi H; [lia|].
      forwards Hfwd: lookt_insert_tvar_lt Hi Hlk0; [lia|].
      forwards Heqb: lookt_det H Hfwd. subst B.
      eapply eq_eqr; [ exact Hlk0 |].
      eapply IHHt; eauto.
  - (* eq_boxl : left box ; frame rigid, recurse body at d:=0 (0 <= Y) *)
    inverts Hr.
    eapply eq_boxl;
      [ eapply IHHt; [ eassumption | exact Hi | exact Heq | exact Hw2 | lia ]
      | match goal with Hb: wft T1 (boxt T3 A) |- _ => exact Hb end ].
  - (* eq_boxr : right box ; Bz = the box itself (tshift identity), rebuild wft over T2 *)
    destruct Bz; rewrite ?tshift_and in Heq; simpl in Heq;
      try (destruct m); try discriminate;
      try (destruct (le_gt_dec Y n); discriminate).
    inverts Heq.
    eapply eq_boxr; [ eassumption |].
    eapply insert_tvar_wft_rev; [ exact Hi | exact Hw2 |].
    match goal with Hb: wft ?TR (boxt ?Tb ?Bb) |- _ =>
      assert (Hbe: tshift Y (boxt Tb Bb) = boxt Tb Bb) by reflexivity;
      rewrite Hbe; exact Hb end.
  - (* eq_arr *) inverts Hr.
    destruct Bz; rewrite ?tshift_and in Heq; simpl in Heq;
      try (destruct m); try discriminate;
      try (destruct (le_gt_dec Y n); discriminate).
    inverts Heq. eapply eq_arr; [ eapply IHHt1; eauto | eapply IHHt2; eauto ].
  - (* eq_all *) inverts Hr.
    destruct Bz; rewrite ?tshift_and in Heq; simpl in Heq;
      try (destruct m); try discriminate;
      try (destruct (le_gt_dec Y n); discriminate).
    inverts Heq. eapply eq_all.
    eapply IHHt; [ eassumption | eapply itv_tvar; exact Hi | reflexivity | eapply we_tvar; exact Hw2 | lia ].
  - (* eq_manil : left mani ; right premise carries tshift 0 C *)
    inverts Hr.
    eapply eq_manil.
    forwards Heq2: tshift_tshift_prop_1 Bz 0 Y. simpl in Heq2.
    eapply IHHt;
      [ eassumption | eapply itv_tvar; exact Hi
      | (* tshift 0 C = tshift (S Y) (tshift 0 Bz) *)
        subst C; rewrite Heq2; reflexivity
      | eapply we_tvar; exact Hw2 | lia ].
  - (* eq_manir : right mani ; right env pads &= ; Bz = mani Bp Bq *)
    destruct Bz; rewrite ?tshift_and in Heq; simpl in Heq;
      try (destruct m); try discriminate;
      try (destruct (le_gt_dec Y n); discriminate).
    inverts Heq.
    eapply eq_manir.
    forwards Hwr: teq_wfe_right Ht.
    forwards HwT3: itvar_wfe_rev (itv_teq Bz1 Hi) Hwr; [].
    eapply IHHt;
      [ eapply rigid_pad_s; exact Hr | eapply itv_teq; exact Hi
      | reflexivity
      | exact HwT3 | lia ].
  - (* eq_top *) destruct Bz; rewrite ?tshift_and in Heq; simpl in Heq;
      try (destruct m); try discriminate;
      try (destruct (le_gt_dec Y n); discriminate). eapply eq_top; eauto.
  - (* eq_and *) inverts Hr.
    (* Bz = and Bz1 m Bz2 ; T4 = tshift Y Bz1 ; right body type = tshift (keyLen Bz1+Y) Bz2 *)
    destruct Bz as [ | ? | ? ? | ? | ? ? | ? ? | ? ? | | Bz1 mz Bz2 | ? ];
      rewrite ?tshift_and in Heq; simpl in Heq; try discriminate;
      try (destruct (le_gt_dec Y n); discriminate).
    destruct mz; inverts Heq.
    all: (
    forwards Hwr2: teq_wfe_right Ht2;
    assert (HkLB: keyLen T3 = keyLen Bz1) by
      (rewrite (keyLen_same Bz1 Y);
       eapply teq_spine_keyLen; [ exact Ht1 | exact H | exact H0 ]);
    assert (Hlb1: lshape Bz1) by (eapply lshape_tshift_rev; exact H0);
    forwards Hins: insert_tvar_env Hi Bz1;
    forwards HwB1: itvar_wfe_rev Hins Hwr2;
    eapply eq_and;
      [ eapply IHHt1; [ eassumption | exact Hi | reflexivity | exact Hw2 | exact Hal ]
      | assumption
      | exact Hlb1
      | eapply IHHt2;
          [ eassumption
          | exact Hins
          | reflexivity
          | exact HwB1
          | (* d + keyLen T3 <= keyLen Bz1 + Y *) lia ] ]).
  - (* eq_ands *) inverts Hr.
    destruct Bz; rewrite ?tshift_and in Heq; simpl in Heq;
      try (destruct m); try discriminate;
      try (destruct (le_gt_dec Y n); discriminate).
    inverts Heq. eapply eq_ands;
      [ eapply IHHt; [ eassumption | exact Hi | reflexivity | exact Hw2 | exact Hal ]
      | assumption
      | eapply lshape_tshift_rev; eassumption ].
  - (* eq_rcd *) inverts Hr.
    destruct Bz; rewrite ?tshift_and in Heq; simpl in Heq;
      try (destruct m); try discriminate;
      try (destruct (le_gt_dec Y n); discriminate).
    inverts Heq. eapply eq_rcd. eapply IHHt; eauto.
Qed.

(* Public form at depth 0 (frame-rigid box body): align is vacuous. *)
Lemma teq_shift_tvar_r_rigid_rev: forall T1 A C T2',
  teq T1 A C T2' -> forall Y T2 B, rigid 0 T1 A ->
  insert_tvar Y T2 T2' -> C = tshift Y B -> wfe T2 ->
  teq T1 A B T2.
Proof.
  introv Ht Hr Hi Heq Hw2.
  eapply teq_shift_tvar_r_rigid_rev_aux; eauto. lia.
Qed.

Lemma teq_shift_tvar_l_rigid_rev: forall T1' A C T2,
  teq T1' A C T2 -> forall X T1 B, rigid 0 T2 C ->
  insert_tvar X T1 T1' -> A = tshift X B -> wfe T1 ->
  teq T1 B C T2.
Proof.
  introv Ht Hr Hi Heq Hw1.
  eapply teq_sym.
  eapply teq_shift_tvar_r_rigid_rev;
    [ eapply teq_sym; exact Ht | exact Hr | exact Hi | exact Heq | exact Hw1 ].
Qed.


Lemma teq_shift_r_self_rigid_rev_aux: forall T1 A C T2',
  teq T1 A C T2' -> forall d Y T2 Bz, rigid d T2 Bz ->
  insert_tvar Y T2 T2' -> C = tshift Y Bz -> wfe T2 ->
  d <= Y ->
  teq T1 A Bz T2.
Proof.
  introv Ht. inductions Ht; introv Hr Hi Heq Hw2 Hal.
  destruct Bz; rewrite ?tshift_and in Heq; simpl in Heq; try (destruct m); try discriminate; try (destruct (le_gt_dec Y n); discriminate); eapply eq_int; eauto.
  { destruct Bz as [ | nv | ? ? | ? | ? ? | ? ? | ? ? | | ? ? ? | ? ];
      rewrite ?tshift_and in Heq; simpl in Heq; try (destruct m); try discriminate.
    destruct (le_gt_dec Y nv) eqn:E; inverts Heq.
    - inverts Hr.
      + lia.
      + exfalso.
        match goal with Hlk: lookt ?Tc nv ?BB |- _ =>
          forwards Hlk2: lookt_insert_tvar_ge Hi Hlk; [ lia | ] end.
        eapply lookt_check_false; [ exact Hlk2 | exact H2 ].
    - inverts Hr.
      + eapply eq_tvar; eauto.
      + exfalso.
        match goal with Hlk: lookt ?Tc nv ?BB |- _ =>
          forwards Hlk2: lookt_insert_tvar_lt Hi Hlk; [ lia | ] end.
        eapply lookt_check_false; [ exact Hlk2 | exact H2 ]. }
  { (* eq_eql *) eapply eq_eql; [ eassumption | ].
    eapply IHHt; [ exact Hr | exact Hi | exact Heq | exact Hw2 | exact Hal ]. }
  { (* eq_eqr *) destruct Bz as [ | nv | ? ? | ? | ? ? | ? ? | ? ? | | ? ? ? | ? ];
      rewrite ?tshift_and in Heq; simpl in Heq; try (destruct m); try discriminate.
    destruct (le_gt_dec Y nv) eqn:E.
    - inverts Heq.
      forwards (A0 & Hlk0): lookt_insert_tvar_ge_rev Hi H; [lia|].
      forwards Hfwd: lookt_insert_tvar_ge Hi Hlk0; [lia|].
      forwards Heqb: lookt_det H Hfwd. subst.
      eapply eq_eqr; [ exact Hlk0 | ]. inverts Hr.
      + lia.
      + match goal with H1: lookt T0 nv ?BB |- _ => forwards Heqd: lookt_det H1 Hlk0; subst end.
        eapply IHHt; [ eassumption | exact Hi | reflexivity | exact Hw2 | exact Hal ].
    - inverts Heq.
      forwards (A0 & Hlk0): lookt_insert_tvar_lt_rev Hi H; [lia|].
      forwards Hfwd: lookt_insert_tvar_lt Hi Hlk0; [lia|].
      forwards Heqb: lookt_det H Hfwd. subst.
      eapply eq_eqr; [ exact Hlk0 | ]. inverts Hr.
      + exfalso. match goal with Hc: check T0 nv |- _ =>
          eapply lookt_check_false; [ exact Hlk0 | exact Hc ] end.
      + match goal with H1: lookt T0 nv ?BB |- _ => forwards Heqd: lookt_det H1 Hlk0; subst end.
        eapply IHHt; [ eassumption | exact Hi | reflexivity | exact Hw2 | exact Hal ]. }
  { (* eq_boxl *) eapply eq_boxl; [ eapply IHHt; [ exact Hr | exact Hi | exact Heq | exact Hw2 | exact Hal ] | exact H ]. }
  { (* eq_boxr *)
    destruct Bz; rewrite ?tshift_and in Heq; simpl in Heq;
      try (destruct m); try discriminate;
      try (destruct (le_gt_dec Y n); discriminate).
    inverts Heq.
    eapply eq_boxr; [ eassumption | ].
    eapply insert_tvar_wft_rev; [ exact Hi | exact Hw2 | ].
    match goal with Hb: wft T2 (boxt ?Tb ?Bb) |- _ =>
      assert (Hbe: tshift Y (boxt Tb Bb) = boxt Tb Bb) by reflexivity;
      rewrite Hbe; exact Hb end. }
  { (* eq_arr *)
    destruct Bz; rewrite ?tshift_and in Heq; simpl in Heq;
      try (destruct m); try discriminate;
      try (destruct (le_gt_dec Y n); discriminate).
    inverts Heq. inverts Hr.
    eapply eq_arr; [ eapply IHHt1 | eapply IHHt2 ]; eauto. }
  { (* eq_all *)
    destruct Bz; rewrite ?tshift_and in Heq; simpl in Heq;
      try (destruct m); try discriminate;
      try (destruct (le_gt_dec Y n); discriminate).
    inverts Heq. inverts Hr.
    eapply eq_all.
    eapply IHHt; [ eassumption | eapply itv_tvar; exact Hi | reflexivity | eapply we_tvar; exact Hw2 | lia ]. }
  { (* eq_manil *)
    eapply eq_manil.
    forwards Heq2: tshift_tshift_prop_1 Bz 0 Y. simpl in Heq2.
    eapply IHHt;
      [ eapply rigid_pad_s; exact Hr | eapply itv_tvar; exact Hi
      | subst C; rewrite Heq2; reflexivity
      | eapply we_tvar; exact Hw2 | lia ]. }
  { (* eq_manir *)
    destruct Bz; rewrite ?tshift_and in Heq; simpl in Heq;
      try (destruct m); try discriminate;
      try (destruct (le_gt_dec Y n); discriminate).
    inverts Heq. inverts Hr.
    eapply eq_manir.
    forwards Hwr: teq_wfe_right Ht.
    forwards HwT3: itvar_wfe_rev (itv_teq Bz1 Hi) Hwr; [].
    eapply IHHt;
      [ eassumption | eapply itv_teq; exact Hi
      | reflexivity
      | exact HwT3
      | lia ]. }
  { (* eq_top *) destruct Bz; rewrite ?tshift_and in Heq; simpl in Heq;
      try (destruct m); try discriminate;
      try (destruct (le_gt_dec Y n); discriminate). eapply eq_top; eauto. }
  { (* eq_and *)
    destruct Bz as [ | ? | ? ? | ? | ? ? | ? ? | ? ? | | Bz1 mz Bz2 | ? ];
      rewrite ?tshift_and in Heq; simpl in Heq; try discriminate;
      try (destruct (le_gt_dec Y n); discriminate).
    destruct mz; inverts Heq; inverts Hr.
    all: (
    forwards Hwr2: teq_wfe_right Ht2;
    assert (HkLB: keyLen T3 = keyLen Bz1) by
      (rewrite (keyLen_same Bz1 Y);
       eapply teq_spine_keyLen; [ exact Ht1 | exact H | exact H0 ]);
    assert (Hlb1: lshape Bz1) by (eapply lshape_tshift_rev; exact H0);
    forwards Hins: insert_tvar_env Hi Bz1;
    forwards HwB1: itvar_wfe_rev Hins Hwr2;
    eapply eq_and;
      [ eapply IHHt1; [ eassumption | exact Hi | reflexivity | exact Hw2 | exact Hal ]
      | assumption
      | exact Hlb1
      | eapply IHHt2;
          [ eassumption
          | exact Hins
          | reflexivity
          | exact HwB1
          | lia ] ]). }
  { (* eq_ands *)
    destruct Bz; rewrite ?tshift_and in Heq; simpl in Heq;
      try (destruct m); try discriminate;
      try (destruct (le_gt_dec Y n); discriminate).
    inverts Heq. inverts Hr. eapply eq_ands;
      [ eapply IHHt; [ eassumption | exact Hi | reflexivity | exact Hw2 | exact Hal ]
      | assumption
      | eapply lshape_tshift_rev; eassumption ]. }
  { (* eq_rcd *)
    destruct Bz; rewrite ?tshift_and in Heq; simpl in Heq;
      try (destruct m); try discriminate;
      try (destruct (le_gt_dec Y n); discriminate).
    inverts Heq. inverts Hr. eapply eq_rcd.
    eapply IHHt; [ eassumption | exact Hi | reflexivity | exact Hw2 | exact Hal ]. }
Qed.

(* SELF-side reverse rigid shift on the LEFT, by symmetry. *)
Lemma teq_unpad_s_r_rigid: forall T1 A C T2,
  teq T1 A (tshift 0 C) (T2 &s) -> rigid 0 T2 C -> wfe T2 ->
  teq T1 A C T2.
Proof.
  introv Ht Hr Hw.
  eapply teq_shift_r_self_rigid_rev_aux;
    [ exact Ht | exact Hr | eapply itv_here2 | reflexivity | exact Hw | lia ].
Qed.


Lemma shift_tvar_both_rev: forall T1' AC CC T2',
  teq T1' AC CC T2' -> forall Xz T1 Az Cz T2,
  insert_both Xz T1 T1' T2 T2' -> AC = tshift Xz Az -> CC = tshift Xz Cz ->
  wfe T1 -> wfe T2 ->
  teq T1 Az Cz T2.
Proof.
  introv Ht. inductions Ht; introv Hi HeqA HeqC Hw1 Hw2;
  forwards Hi1: insert_both_left Hi; forwards Hi2: insert_both_right Hi.
  - (* eq_int *)
    destruct Az; rewrite ?tshift_and in HeqA; simpl in HeqA; try (destruct m); try discriminate;
      try (destruct (le_gt_dec Xz n); discriminate).
    destruct Cz; rewrite ?tshift_and in HeqC; simpl in HeqC; try (destruct m); try discriminate;
      try (destruct (le_gt_dec Xz n); discriminate).
    eapply eq_int; eauto.
  - (* eq_tvar : single shared position ; both vars un-shift to the same var *)
    rename H1 into HcA. rename H2 into HcC.
    destruct Az as [ | na | ? ? | ? | ? ? | ? ? | ? ? | | ? ? ? | ? ];
      rewrite ?tshift_and in HeqA; simpl in HeqA; try (destruct m); try discriminate.
    destruct Cz as [ | nc | ? ? | ? | ? ? | ? ? | ? ? | | ? ? ? | ? ];
      rewrite ?tshift_and in HeqC; simpl in HeqC; try (destruct m); try discriminate.
    destruct (le_gt_dec Xz na) eqn:Ea; destruct (le_gt_dec Xz nc) eqn:Ec;
      inverts HeqA; inverts HeqC.
    + (* both ge : na = nc forced ; vars both S nc *)
      eapply eq_tvar; eauto;
        [ eapply check_insert_tvar_ge_rev; [ exact Hi1 | lia | replace (1 + nc) with (S nc) by lia; exact HcA ]
        | eapply check_insert_tvar_ge_rev; [ exact Hi2 | lia | replace (1 + nc) with (S nc) by lia; exact HcC ] ].
    + lia.
    + lia.
    + (* both lt : na = nc *)
      eapply eq_tvar; eauto;
        [ eapply check_insert_tvar_lt_rev; [ exact Hi1 | lia | exact HcA ]
        | eapply check_insert_tvar_lt_rev; [ exact Hi2 | lia | exact HcC ] ].
  - (* eq_eql : left var resolves ; recurse, Az unshifts to a tvar *)
    destruct Az as [ | na | ? ? | ? | ? ? | ? ? | ? ? | | ? ? ? | ? ];
      rewrite ?tshift_and in HeqA; simpl in HeqA; try (destruct m); try discriminate.
    destruct (le_gt_dec Xz na) eqn:E; inverts HeqA.
    + forwards (A0 & Hlk0): lookt_insert_tvar_ge_rev Hi1 H; [lia|].
      forwards Hfwd: lookt_insert_tvar_ge Hi1 Hlk0; [lia|].
      forwards Heqb: lookt_det H Hfwd. subst A.
      eapply eq_eql; [ exact Hlk0 |]. eapply IHHt; eauto.
    + forwards (A0 & Hlk0): lookt_insert_tvar_lt_rev Hi1 H; [lia|].
      forwards Hfwd: lookt_insert_tvar_lt Hi1 Hlk0; [lia|].
      forwards Heqb: lookt_det H Hfwd. subst A.
      eapply eq_eql; [ exact Hlk0 |]. eapply IHHt; eauto.
  - (* eq_eqr : right var resolves *)
    destruct Cz as [ | nc | ? ? | ? | ? ? | ? ? | ? ? | | ? ? ? | ? ];
      rewrite ?tshift_and in HeqC; simpl in HeqC; try (destruct m); try discriminate.
    destruct (le_gt_dec Xz nc) eqn:E; inverts HeqC.
    + forwards (A0 & Hlk0): lookt_insert_tvar_ge_rev Hi2 H; [lia|].
      forwards Hfwd: lookt_insert_tvar_ge Hi2 Hlk0; [lia|].
      forwards Heqb: lookt_det H Hfwd. subst B.
      eapply eq_eqr; [ exact Hlk0 |]. eapply IHHt; eauto.
    + forwards (A0 & Hlk0): lookt_insert_tvar_lt_rev Hi2 H; [lia|].
      forwards Hfwd: lookt_insert_tvar_lt Hi2 Hlk0; [lia|].
      forwards Heqb: lookt_det H Hfwd. subst B.
      eapply eq_eqr; [ exact Hlk0 |]. eapply IHHt; eauto.
  - (* eq_boxl : left box ; Az = the box ; body's left rigid, reverse one-sided right *)
    destruct Az; rewrite ?tshift_and in HeqA; simpl in HeqA; try (destruct m); try discriminate;
      try (destruct (le_gt_dec Xz n); discriminate).
    inverts HeqA.
    eapply eq_boxl;
      [ eapply teq_shift_tvar_r_rigid_rev;
          [ exact Ht | eapply wft_box_rigid; exact H | exact Hi2 | exact HeqC | exact Hw2 ]
      | eapply insert_tvar_wft_rev; [ exact Hi1 | exact Hw1 |];
        match goal with Hb: wft ?TL (boxt ?Tb ?Bb) |- _ =>
          assert (Hbe: tshift Xz (boxt Tb Bb) = boxt Tb Bb) by reflexivity;
          rewrite Hbe; exact Hb end ].
  - (* eq_boxr : right box ; Cz = the box ; body's right rigid, reverse one-sided left *)
    destruct Cz; rewrite ?tshift_and in HeqC; simpl in HeqC; try (destruct m); try discriminate;
      try (destruct (le_gt_dec Xz n); discriminate).
    inverts HeqC.
    eapply eq_boxr;
      [ eapply teq_shift_tvar_l_rigid_rev;
          [ exact Ht | eapply wft_box_rigid; exact H | exact Hi1 | exact HeqA | exact Hw1 ]
      | eapply insert_tvar_wft_rev; [ exact Hi2 | exact Hw2 |];
        match goal with Hb: wft ?TR (boxt ?Tb ?Bb) |- _ =>
          assert (Hbe: tshift Xz (boxt Tb Bb) = boxt Tb Bb) by reflexivity;
          rewrite Hbe; exact Hb end ].
  - (* eq_arr *)
    destruct Az; rewrite ?tshift_and in HeqA; simpl in HeqA; try (destruct m); try discriminate;
      try (destruct (le_gt_dec Xz n); discriminate).
    destruct Cz; rewrite ?tshift_and in HeqC; simpl in HeqC; try (destruct m); try discriminate;
      try (destruct (le_gt_dec Xz n); discriminate).
    inverts HeqA. inverts HeqC. eapply eq_arr; [ eapply IHHt1; eauto | eapply IHHt2; eauto ].
  - (* eq_all *)
    destruct Az; rewrite ?tshift_and in HeqA; simpl in HeqA; try (destruct m); try discriminate;
      try (destruct (le_gt_dec Xz n); discriminate).
    destruct Cz; rewrite ?tshift_and in HeqC; simpl in HeqC; try (destruct m); try discriminate;
      try (destruct (le_gt_dec Xz n); discriminate).
    inverts HeqA. inverts HeqC. eapply eq_all.
    eapply IHHt with (Xz := S Xz); eauto.
  - (* eq_manil : left mani *)
    destruct Az; rewrite ?tshift_and in HeqA; simpl in HeqA; try (destruct m); try discriminate;
      try (destruct (le_gt_dec Xz n); discriminate).
    inverts HeqA.
    eapply eq_manil.
    forwards Heq2: tshift_tshift_prop_1 Cz 0 Xz. simpl in Heq2.
    forwards Hwl: teq_wfe_left Ht.
    forwards HwTL: itvar_wfe_rev (itv_teq Az1 Hi1) Hwl; [].
    eapply IHHt with (Xz := S Xz) (Az := Az2) (Cz := tshift 0 Cz);
      [ eapply ib_manil; exact Hi
      | reflexivity
      | rewrite HeqC; rewrite Heq2; reflexivity
      | exact HwTL
      | eapply we_tvar; exact Hw2 ].
  - (* eq_manir : right mani *)
    destruct Cz; rewrite ?tshift_and in HeqC; simpl in HeqC; try (destruct m); try discriminate;
      try (destruct (le_gt_dec Xz n); discriminate).
    inverts HeqC.
    eapply eq_manir.
    forwards Heq2: tshift_tshift_prop_1 Az 0 Xz. simpl in Heq2.
    forwards Hwr: teq_wfe_right Ht.
    forwards HwTR: itvar_wfe_rev (itv_teq Cz1 Hi2) Hwr; [].
    eapply IHHt with (Xz := S Xz) (Az := tshift 0 Az) (Cz := Cz2);
      [ eapply ib_manir; exact Hi
      | rewrite HeqA; rewrite Heq2; reflexivity
      | reflexivity
      | eapply we_tvar; exact Hw1
      | exact HwTR ].
  - (* eq_top *)
    destruct Az; rewrite ?tshift_and in HeqA; simpl in HeqA; try (destruct m); try discriminate;
      try (destruct (le_gt_dec Xz n); discriminate).
    destruct Cz; rewrite ?tshift_and in HeqC; simpl in HeqC; try (destruct m); try discriminate;
      try (destruct (le_gt_dec Xz n); discriminate).
    eapply eq_top; eauto.
  - (* eq_and *)
    destruct Az as [ | ? | ? ? | ? | ? ? | ? ? | ? ? | | Az1 maz Az2 | ? ];
      rewrite ?tshift_and in HeqA; simpl in HeqA; try discriminate;
      try (destruct (le_gt_dec Xz n); discriminate).
    destruct Cz as [ | ? | ? ? | ? | ? ? | ? ? | ? ? | | Cz1 mcz Cz2 | ? ];
      rewrite ?tshift_and in HeqC; simpl in HeqC; try discriminate;
      try (destruct (le_gt_dec Xz n); discriminate).
    destruct maz; inverts HeqA; destruct mcz; inverts HeqC.
    all: (
      forwards Hwl: teq_wfe_left Ht2;
      forwards Hwr: teq_wfe_right Ht2;
      assert (Hla1: lshape Az1) by (eapply lshape_tshift_rev; exact H);
      assert (Hlc1: lshape Cz1) by (eapply lshape_tshift_rev; exact H0);
      assert (HkLac: keyLen Az1 = keyLen Cz1) by
        (rewrite (keyLen_same Az1 Xz); rewrite (keyLen_same Cz1 Xz);
         eapply teq_spine_keyLen; [ exact Ht1 | exact H | exact H0 ]);
      forwards Hsp: (IHHt1 Xz _ Az1 Cz1 _ Hi eq_refl eq_refl Hw1 Hw2);
      forwards Hib: insert_both_env Hsp Hla1 Hlc1 Hi;
      forwards HwL: itvar_wfe_rev (insert_both_left Hib) Hwl;
      forwards HwR: itvar_wfe_rev (insert_both_right Hib) Hwr;
      eapply eq_and;
        [ exact Hsp
        | exact Hla1
        | exact Hlc1
        | eapply IHHt2 with (Xz := keyLen Az1 + Xz) (Az := Az2) (Cz := Cz2);
            [ exact Hib
            | reflexivity
            | (* tshift (keyLen Cz1 + Xz) Cz2 = tshift (keyLen Az1 + Xz) Cz2 *)
              rewrite HkLac; reflexivity
            | exact HwL
            | exact HwR ] ]).
  - (* eq_ands *)
    destruct Az; rewrite ?tshift_and in HeqA; simpl in HeqA; try (destruct m); try discriminate;
      try (destruct (le_gt_dec Xz n); discriminate).
    destruct Cz; rewrite ?tshift_and in HeqC; simpl in HeqC; try (destruct m); try discriminate;
      try (destruct (le_gt_dec Xz n); discriminate).
    inverts HeqA. inverts HeqC. eapply eq_ands;
      [ eapply IHHt; eauto
      | eapply lshape_tshift_rev; exact H
      | eapply lshape_tshift_rev; exact H0 ].
  - (* eq_rcd *)
    destruct Az; rewrite ?tshift_and in HeqA; simpl in HeqA; try (destruct m); try discriminate;
      try (destruct (le_gt_dec Xz n); discriminate).
    destruct Cz; rewrite ?tshift_and in HeqC; simpl in HeqC; try (destruct m); try discriminate;
      try (destruct (le_gt_dec Xz n); discriminate).
    inverts HeqA. inverts HeqC. eapply eq_rcd. eapply IHHt; eauto.
Qed.

(* unpad: strip a dead leading &s on both sides and undo tshift 0. *)
Lemma teq_unpad_s: forall T1 A C T3,
  teq (T1 &s) (tshift 0 A) (tshift 0 C) (T3 &s) -> wfe T1 -> wfe T3 ->
  teq T1 A C T3.
Proof.
  introv Ht Hw1 Hw3.
  eapply shift_tvar_both_rev with (Xz := 0) (T1' := T1 &s) (T2' := T3 &s);
    [ exact Ht | eapply ib_here2 | reflexivity | reflexivity | exact Hw1 | exact Hw3 ].
Qed.


Lemma teqd_trans: forall N n1 n2 T1 A B T2 C T3, n1 + n2 <= N ->
  teqd n1 T1 A B T2 -> teqd n2 T2 B C T3 -> teq T1 A C T3.
Proof.
  induction N; introv Hle Ht Hs.
  - inverts Ht; simpl in Hle; lia.
  - pose proof Ht as HtW; pose proof Hs as HsW; inverts Ht; inverts Hs;
    try solve [eauto];
    try solve [exfalso; eauto using lookt_check_false];
    try solve [match goal with Ha: lookt ?T ?X ?a, Hb: lookt ?T ?X ?b |- _ =>
                 forwards: lookt_det Ha Hb; subst; eauto end];
    (* structural / binder recursive cases via the sized IH (solve teqd then lia) *)
    try solve [econstructor;
      first [ (eapply IHN; [idtac | eassumption | eassumption]); lia
            | eassumption | eauto ]];
    (* eql on the left tvar: recurse on Ht's inner ; HsW whole on the right *)
    try solve [eapply eq_eql;
      [ eassumption | (eapply IHN; [idtac | eassumption | exact HsW]); lia ]];
    (* eqr on the right tvar: HtW whole on the left ; recurse on Hs's inner *)
    try solve [eapply eq_eqr;
      [ eassumption | (eapply IHN; [idtac | exact HtW | eassumption]); lia ]];
    (* manil: left mani, recurse on Ht's inner ; HsW whole *)
    try solve [eapply eq_manil; (eapply IHN; [idtac | eassumption | exact HsW]); lia];
    (* manir: right mani, HtW whole ; recurse on Hs's inner *)
    try solve [eapply eq_manir; (eapply IHN; [idtac | exact HtW | eassumption]); lia];
    (* middle tvar resolved on both sides (same var X in T2): det then recurse *)
    try solve [match goal with Ha: lookt ?T ?X ?a, Hb: lookt ?T ?X ?b |- _ =>
                 forwards: lookt_det Ha Hb; subst end;
               (eapply IHN; [idtac | eassumption | eassumption]); lia];
    (* middle tvar resolved on Ht's right: peel HsW's left, then compose *)
    try solve [match goal with
      | Hl: lookt ?Tm ?X ?B0, Hh: teqd _ ?Ta ?Aa ?B0 ?Tm, Hsw: teqd _ ?Tm (tvar ?X) ?Cc ?Tc |- _ =>
          forwards (m & Hm & Hd'): teqd_peel_l Hsw Hl;
          (eapply IHN; [ idtac | exact Hh | exact Hd' ]); lia
      end];
    (* middle tvar resolved on Hs's left: peel HtW's right, then compose *)
    try solve [match goal with
      | Hl: lookt ?Tm ?X ?A0, Htw: teqd _ ?Ta ?Aa (tvar ?X) ?Tm, Hh: teqd _ ?Tm ?A0 ?Cc ?Tc |- _ =>
          forwards (m & Hm & Hd'): teqd_peel_r Htw Hl;
          (eapply IHN; [ idtac | exact Hd' | exact Hh ]); lia
      end];
    (* box-RIGHT: the right operand is a box (Hs ends in dq_boxr, body Hbody whose
       LEFT equals the shared middle = HtW's right).  Compose HtW o Hbody.  The
       box-wft on the outer right frame is exactly the inverted dq_boxr premise. *)
    try solve [match goal with
      | Hbody: teqd _ T2 _ ?Bb ?Tr
          |- teq ?T1 ?Aa (boxt ?Tr ?Bb) ?Tc =>
          eapply eq_boxr;
            [ (eapply IHN; [ idtac | exact HtW | exact Hbody ]); lia
            | match goal with Hwbox: wft Tc (boxt Tr Bb) |- _ => exact Hwbox end ]
      end];
    (* box-LEFT: the left operand is a box (Ht ends in dq_boxl, body Hbody whose
       RIGHT equals the shared middle = HsW's left).  Compose Hbody o HsW. *)
    try solve [match goal with
      | Hbody: teqd _ ?Tl ?Ab _ T2
          |- teq ?T1 (boxt ?Tl ?Ab) ?Cc ?Tc =>
          eapply eq_boxl;
            [ (eapply IHN; [ idtac | exact Hbody | exact HsW ]); lia
            | match goal with Hwbox: wft T1 (boxt Tl Ab) |- _ => exact Hwbox end ]
      end];
    (* compatible compose: middle resolved the same on both sides (box/mani body) *)
    try solve [(eapply IHN; [idtac | eassumption | eassumption]); lia];
    (* manir family: HtW (non-mani) lifted via teqd_shift_both o ib_here2, then
       composed by IHN with the inverted padded dq_manir premise H1. *)
    try solve [
      match goal with
      | HtW: teqd ?n1 ?T1 ?A ?B ?T2, H1: teqd ?n0 (?T2 &s) (tshift 0 ?B) ?C0 (?T3 &= ?A0)
          |- teq ?T1 ?A (mani ?A0 ?C0) ?T3 =>
          eapply eq_manir;
          forwards Hwl: teq_wfe_left (teqd_teq HtW);
          forwards Hwr: teq_wfe_right (teqd_teq HtW);
          forwards Hlift: teqd_shift_both HtW (ib_here2 T1 T2) (we_tvar Hwl) (we_tvar Hwr);
          simpl in Hlift;
          (eapply IHN; [ | exact Hlift | exact H1 ]); lia
      end ];
    (* manil family: HsW (non-mani) lifted via teqd_shift_both o ib_here2, then
       composed by IHN with the inverted padded dq_manil premise H. *)
    try solve [
      match goal with
      | H: teqd ?n0 (?T1 &= ?A0) ?B0 (tshift 0 ?B) (?T2 &s), HsW: teqd ?n2 ?T2 ?B ?C ?T3
          |- teq ?T1 (mani ?A0 ?B0) ?C ?T3 =>
          eapply eq_manil;
          forwards Hwl: teq_wfe_left (teqd_teq HsW);
          forwards Hwr: teq_wfe_right (teqd_teq HsW);
          forwards Hlift: teqd_shift_both HsW (ib_here2 T2 T3) (we_tvar Hwl) (we_tvar Hwr);
          simpl in Hlift;
          (eapply IHN; [ | exact H | exact Hlift ]); lia
      end ];
    idtac.
  (* manir o manil : middle is mani on BOTH sides ; compose the &s/&= padded
     premises by IHN to get teq (T1&s)(tshift 0 A)(tshift 0 C)(T3&s), then unpad. *)
  all:
    (forwards Hw1: teq_wfe_left (teqd_teq HtW);
     forwards Hw3: teq_wfe_right (teqd_teq HsW);
     eapply teq_unpad_s; [ (eapply IHN; [ | exact H | exact H6 ]); lia | exact Hw1 | exact Hw3 ]).
Qed.

Lemma teq_trans: forall T1 A B T2,
  teq T1 A B T2 -> forall T3 C, teq T2 B C T3 -> teq T1 A C T3.
Proof.
  introv Ht Hs. forwards [n1 Hd1]: teq_teqd Ht. forwards [n2 Hd2]: teq_teqd Hs.
  eapply teqd_trans with (N := n1 + n2); eauto.
Qed.

Lemma teq_boxbox: forall T1 T2 T3 T4 A B,
  teq T3 A B T4 ->
  wft T1 (boxt T3 A) -> wft T2 (boxt T4 B) ->
  teq T1 (boxt T3 A) (boxt T4 B) T2.
Proof.
  introv Hbody HwfA HwfB.
  (* eq_boxr packs the right box; its body eq_boxl unpacks the left box.  Both
     box-wfts are now premises in hand. *)
  eapply eq_boxr; [ eapply eq_boxl; [ exact Hbody | exact HwfA ] | exact HwfB ].
Qed.

(* teq_refl_size / teq_refl RELOCATED below shift_tvar_both: the mani case needs the
   binder-exchange lemma teq_exch_s_eq, which is built from shift_tvar_both. *)

Fixpoint tsize (A:typ) : nat :=
  match A with
  | int => 1
  | tvar _ => 1
  | top => 1
  | arr A1 A2 => 1 + tsize A1 + tsize A2
  | all A1 => 1 + tsize A1
  | boxt T A1 => 1 + tsize T + tsize A1
  | mani A1 A2 => 1 + tsize A1 + tsize A2
  | rcd _ A1 => 1 + tsize A1
  | and A1 _ A2 => 1 + tsize A1 + tsize A2
  | ands A1 => 1 + tsize A1
  end.


Ltac str_rec :=
  match goal with He: _ = tshift _ ?a |- _ =>
    destruct a; repeat (match goal with mm: mode |- _ => destruct mm end);
    simpl in He; try (inverts He) end.

Local Hint Extern 4 (tsize _ + tsize _ + tsize _ <= _) => simpl in *; lia : core.





(* teq_spine_num and inner_app_dec relocated earlier (before teqd_rigid_l). *)

(* lookt is preserved under &s->&=C: the star has no lookt, so any X with a
   lookt is not the star and keeps its (shifted) binding. *)
Lemma lookt_inst: forall p T1 C X A,
  wfe ((T1 &s) +++ p) -> wft T1 C ->
  lookt ((T1 &s) +++ p) X A -> lookt ((T1 &= C) +++ p) X A.
Proof.
  introv Hwfe Hwft Hl. eapply lookt_orel; [ eapply inst_orel; eauto | exact Hl ].
Qed.



Lemma teq_shift_tvar_r_rigid_aux: forall T1 A B T2,
  teq T1 A B T2 -> forall d Y T2', rigid d T1 A ->
  insert_tvar Y T2 T2' -> wfe T2' ->
  align T1 T2 d Y ->
  teq T1 A (tshift Y B) T2'.
Proof.
  introv Ht. inductions Ht; introv Hr Hi Hw2 Hal.
  - (* eq_int *) simpl. eapply eq_int; eauto.
  - (* eq_tvar : the crux.  H1 : check T1 X, H2 : check T2 X (positional). *)
    rename H1 into HcX. rename H2 into HcY.
    inverts Hr.
    + (* rigid_bvar : X < d ; align gives X < Y so the shift keeps X *)
      match goal with Hxd: _ < d |- _ =>
        forwards~ HY: Hal HcX Hxd HcY end.
      simpl.
      match goal with |- context[le_gt_dec ?a ?b] => destruct (le_gt_dec a b) as [Hle|Hgt]; [lia|] end.
      eapply eq_tvar; eauto. eapply check_insert_tvar_lt; eauto.
    + (* rigid_cvar : lookt T1 X B0 -- contradicts check T1 X *)
      exfalso. eapply lookt_check_false; [ eassumption | exact HcX ].
  - (* eq_eql : left var, lookt T1 X A; recurse, right shifts.
       Need rigid d T1 A (rigidity of the resolved value) for the IH. *)
    eapply eq_eql; [ exact H |].
    eapply IHHt; eauto.
    eapply rigid_lookt; [ exact Hr | exact H ].
  - (* eq_eqr : right var, lookt T2 X B0 *)
    simpl. destruct (le_gt_dec Y X) eqn:E.
    + (* X >= Y : index bumps to S X, lookt_insert_tvar_ge *)
      eapply eq_eqr.
      * forwards~ HL: lookt_insert_tvar_ge Hi l H. simpl in HL. exact HL.
      * eapply IHHt; eauto.
    + (* X < Y : index stays, lookt_insert_tvar_lt *)
      eapply eq_eqr.
      * forwards~ HL: lookt_insert_tvar_lt Hi g H. exact HL.
      * eapply IHHt; eauto.
  - (* eq_boxl : left box; tshift identity on left, recurse box body into T2.
       Box-wft (H0) is on the LEFT frame T1, untouched by the right-frame insert. *)
    inverts Hr.
    eapply eq_boxl;
      [ eapply IHHt; [ eassumption | exact Hi | exact Hw2 |];
        unfold align; introv Hin Hlt Hin2; lia
      | match goal with Hb: wft T1 (boxt T3 A) |- _ => exact Hb end ].
  - (* eq_boxr : right box; tshift identity on the box, rebuild box-wft over T2' *)
    assert (Hbe: tshift Y (boxt T3 B) = boxt T3 B) by reflexivity.
    rewrite Hbe.
    match goal with Hb: wft T2 (boxt T3 B) |- _ =>
      forwards (Hbd & _ & _): boxt_wft_inv Hb;
      forwards Hrg: wft_box_rigid Hb end.
    eapply eq_boxr;
      [ eassumption
      | unfold wft; eapply we_box; [ exact Hbd | exact Hrg | exact Hw2 ] ].
  - (* eq_arr *)
    inverts Hr. simpl. eapply eq_arr; eauto.
  - (* eq_all *)
    inverts Hr. simpl. eapply eq_all.
    eapply IHHt; [ eassumption | eapply itv_tvar; exact Hi | eapply we_tvar; exact Hw2 |].
    (* align (T1 &s) (T2 &s) (S d) (S Y) *)
    unfold align. introv Hc1 Hlt Hc2. destruct X as [|X].
    + (* position 0 : check_zero, trivially < S Y *) lia.
    + inverts Hc1. inverts Hc2.
      forwards HY: Hal; [ eassumption | lia | eassumption | ]. lia.
  - (* eq_manil : left mani (L gets &=A0), right gets &s ; right type C double-shifted *)
    inverts Hr. simpl. eapply eq_manil.
    forwards Heq: tshift_tshift_prop_1 C 0 Y. simpl in Heq. rewrite Heq.
    eapply IHHt with (Y := S Y);
      [ eassumption | eapply itv_tvar; exact Hi | eapply we_tvar; exact Hw2 |].
    (* align (T1 &= A) (T2 &s) (S d) (S Y) *)
    unfold align. introv Hc1 Hlt Hc2.
    inverts Hc1. (* check (T1&=A): X = S X0, check T1 X0 *)
    inverts Hc2. (* check (T2&s) (S X0): check_etvar -> check T2 X0 *)
    match goal with Ha: check T1 ?xx, Hb: check T2 _ |- _ =>
      assert (Hx0d: xx < d) by lia;
      forwards HY: Hal Ha Hx0d Hb end; lia.
  - (* eq_manir : right mani (R gets &=A0), left gets &s ; left double-shifted *)
    simpl. eapply eq_manir.
    forwards Hwr: teq_wfe_right Ht.
    eapply IHHt with (d := S d) (Y := S Y);
      [ eapply rigid_pad_s; exact Hr
      | eapply itv_teq; exact Hi
      | eapply itvar_wfe; [ eapply itv_teq; exact Hi | exact Hwr ] |].
    (* align (T1 &s) (T2 &= A) (S d) (S Y) *)
    unfold align. introv Hc1 Hlt Hc2.
    inverts Hc2. (* check (T2&=A) (S X0): check_eteq -> check T2 X0 *)
    inverts Hc1. (* check (T1&s) (S X0): check_etvar -> check T1 X0 *)
    match goal with Ha: check T1 ?xx, Hb: check T2 _ |- _ =>
      assert (Hx0d: xx < d) by lia;
      forwards HY: Hal Ha Hx0d Hb end; lia.
  - (* eq_top *) simpl. eapply eq_top; eauto.
  - (* eq_and *)
    inverts Hr.
    forwards Hwr: teq_wfe_right Ht2.
    forwards Hins: insert_tvar_env Hi T4.
    assert (HkL: keyLen T3 = keyLen T4) by
      (eapply teq_spine_keyLen; [ exact Ht1 | exact H | exact H0 ]).
    destruct m; simpl; eapply eq_and;
      [ (* spine *) eapply IHHt1; [ eassumption | exact Hi | exact Hw2 |];
        solve [ unfold align; introv Hc1 Hlt Hc2; eapply Hal; eauto ]
      | (* lshape T3 *) assumption
      | (* lshape (tshift Y T4) *) eapply lshape_tshift; assumption
      | (* body *) eapply IHHt2;
          [ eassumption
          | exact Hins
          | eapply itvar_wfe; [ exact Hins | exact Hwr ]
          | eapply align_and; [ exact Hal | exact H | exact H0 | exact HkL ] ]
      | (* spine *) eapply IHHt1; [ eassumption | exact Hi | exact Hw2 |];
        solve [ unfold align; introv Hc1 Hlt Hc2; eapply Hal; eauto ]
      | assumption
      | eapply lshape_tshift; assumption
      | eapply IHHt2;
          [ eassumption
          | exact Hins
          | eapply itvar_wfe; [ exact Hins | exact Hwr ]
          | eapply align_and; [ exact Hal | exact H | exact H0 | exact HkL ] ] ].
  - (* eq_ands *)
    inverts Hr. simpl. eapply eq_ands.
    + eapply IHHt; [ eassumption | exact Hi | exact Hw2 | exact Hal ].
    + assumption.
    + eapply lshape_tshift; assumption.
  - (* eq_rcd *)
    inverts Hr. simpl. eapply eq_rcd; eauto.
Qed.

(* Public form at depth 0 (frame-rigid box body): the align premise is then VACUOUS
   (no left bound var: X < 0 is impossible), so the one-sided ambient insert is sound
   for ANY insert position Y.  NB: the general-depth `d <= Y` form is FALSE -- a bound
   var sitting at a high de-Bruijn index can be passed by an insert at Y >= d, bumping
   its depth (concrete counterexample: d=1, T2 = ((top &s) &= int) &= int, Y=1); the
   real invariant is `align`, which collapses to True at d=0. *)
Lemma teq_shift_tvar_r_rigid: forall T1 A B T2,
  teq T1 A B T2 -> forall Y T2', rigid 0 T1 A ->
  insert_tvar Y T2 T2' -> wfe T2' ->
  teq T1 A (tshift Y B) T2'.
Proof.
  introv Ht Hr Hi Hw2.
  eapply teq_shift_tvar_r_rigid_aux; eauto.
  unfold align. introv Hin Hlt Hin2. lia.
Qed.

Lemma teq_shift_tvar_l_rigid: forall T1 A B T2,
  teq T1 A B T2 -> forall X T1', rigid 0 T2 B ->
  insert_tvar X T1 T1' -> wfe T1' ->
  teq T1' (tshift X A) B T2.
Proof.
  introv Ht Hr Hi Hw1.
  eapply teq_sym.
  eapply teq_shift_tvar_r_rigid; [ eapply teq_sym; exact Ht | exact Hr | exact Hi | exact Hw1 ].
Qed.

(* Two-sided shift: aligned insert_both keeps abstract depths matched on both sides,
   so all non-box cases carry from the old proof; the eq_boxl/eq_boxr cases reduce
   the box BODY to a one-sided ambient insert closed by teq_shift_tvar_{r,l}_rigid
   (frame-rigid body), with rbox/wft rebuilt via not_rbox_insert_tvar/insert_tvar_wft. *)
Lemma shift_tvar_both: forall T1 A B T2,
  teq T1 A B T2 -> forall X T1' T2',
  insert_both X T1 T1' T2 T2' ->
  wfe T1' -> wfe T2' ->
  teq T1' (tshift X A) (tshift X B) T2'.
Proof.
  introv Ht. inductions Ht; introv Hi Hw1 Hw2;
  forwards Hi1: insert_both_left Hi; forwards Hi2: insert_both_right Hi.
  - (* eq_int *) simpl. eapply eq_int; [ exact Hw1 | exact Hw2 ].
  - (* eq_tvar : single shared position makes both vars shift identically *)
    simpl. destruct (le_gt_dec X0 X).
    + forwards Hca: check_insert_tvar_ge Hi1 l H1.
      forwards Hcb: check_insert_tvar_ge Hi2 l H2.
      eapply eq_tvar; [ exact Hw1 | exact Hw2 | exact Hca | exact Hcb ].
    + forwards Hca: check_insert_tvar_lt Hi1 g H1.
      forwards Hcb: check_insert_tvar_lt Hi2 g H2.
      eapply eq_tvar; [ exact Hw1 | exact Hw2 | exact Hca | exact Hcb ].
  - (* eq_eql *) forwards HIH: IHHt Hi Hw1 Hw2. simpl.
    destruct (le_gt_dec X0 X).
    + forwards HL: lookt_insert_tvar_ge Hi1 l H. eapply eq_eql; eauto.
    + forwards HL: lookt_insert_tvar_lt Hi1 g H. eapply eq_eql; eauto.
  - (* eq_eqr *) forwards HIH: IHHt Hi Hw1 Hw2. simpl.
    destruct (le_gt_dec X0 X).
    + forwards HL: lookt_insert_tvar_ge Hi2 l H. eapply eq_eqr; eauto.
    + forwards HL: lookt_insert_tvar_lt Hi2 g H. eapply eq_eqr; eauto.
  - (* eq_boxl *) assert (Hbe: tshift X (boxt T3 A) = boxt T3 A) by reflexivity.
    rewrite Hbe. eapply eq_boxl.
    + eapply teq_shift_tvar_r_rigid;
        [ exact Ht | eapply wft_box_rigid; exact H | exact Hi2 | exact Hw2 ].
    + forwards Hbox: insert_tvar_wft Hi1 Hw1 H. simpl in Hbox. exact Hbox.
  - (* eq_boxr *) assert (Hbe: tshift X (boxt T3 B) = boxt T3 B) by reflexivity.
    rewrite Hbe. eapply eq_boxr.
    + eapply teq_shift_tvar_l_rigid;
        [ exact Ht | eapply wft_box_rigid; exact H | exact Hi1 | exact Hw1 ].
    + forwards Hbox: insert_tvar_wft Hi2 Hw2 H. simpl in Hbox. exact Hbox.
  - (* eq_arr *) simpl. econstructor; eauto.
  - (* eq_all *) simpl. econstructor.
    eapply IHHt with (X := S X); eauto.
  - (* eq_manil *) simpl. eapply eq_manil.
    forwards Heq: tshift_tshift_prop_1 C 0 X. simpl in Heq. rewrite Heq.
    forwards Hwl: teq_wfe_left Ht.
    forwards Hib: ib_manil A Hi.
    eapply IHHt with (X := S X).
    + exact Hib.
    + eapply itvar_wfe; [ eapply insert_both_left; exact Hib | exact Hwl ].
    + eapply we_tvar; exact Hw2.
  - (* eq_manir *) simpl. eapply eq_manir.
    forwards Heq: tshift_tshift_prop_1 B 0 X. simpl in Heq. rewrite Heq.
    forwards Hwr: teq_wfe_right Ht.
    forwards Hib: ib_manir A Hi.
    eapply IHHt with (X := S X).
    + exact Hib.
    + eapply we_tvar; exact Hw1.
    + eapply itvar_wfe; [ eapply insert_both_right; exact Hib | exact Hwr ].
  - (* eq_top *) simpl. econstructor; eauto.
  - (* eq_and *)
    forwards Hwl: teq_wfe_left Ht2.
    forwards Hwr: teq_wfe_right Ht2.
    forwards Hib: insert_both_env Ht1 H H0 Hi.
    assert (HkL: keyLen T3 = keyLen T4) by
      (eapply teq_spine_keyLen; [ exact Ht1 | exact H | exact H0 ]).
    destruct m; simpl; rewrite <- HkL; eapply eq_and;
      [ eapply IHHt1; [ exact Hi | exact Hw1 | exact Hw2 ]
      | eapply lshape_tshift; exact H
      | eapply lshape_tshift; exact H0
      | eapply IHHt2;
          [ exact Hib
          | eapply itvar_wfe; [ eapply insert_both_left; exact Hib | exact Hwl ]
          | eapply itvar_wfe; [ eapply insert_both_right; exact Hib | exact Hwr ] ]
      | eapply IHHt1; [ exact Hi | exact Hw1 | exact Hw2 ]
      | eapply lshape_tshift; exact H
      | eapply lshape_tshift; exact H0
      | eapply IHHt2;
          [ exact Hib
          | eapply itvar_wfe; [ eapply insert_both_left; exact Hib | exact Hwl ]
          | eapply itvar_wfe; [ eapply insert_both_right; exact Hib | exact Hwr ] ] ].
  - (* eq_ands *) simpl. eapply eq_ands;
      [ eapply IHHt; [ exact Hi | exact Hw1 | exact Hw2 ]
      | eapply lshape_tshift; exact H
      | eapply lshape_tshift; exact H0 ].
  - (* eq_rcd *) simpl. econstructor; eauto.
Qed.

(* ===== binder exchange: a dummy &s inserted ABOVE the top &= on the left and
   BELOW it on the right (the two orders of the same independent pair).  The left
   shift position is XL, the right is XR = S XL, kept in lockstep by every
   descent constructor; only the asymmetric base diverges.  Forward preservation
   mirrors shift_tvar_both. *)
Inductive exb : nat -> nat -> typ -> typ -> typ -> typ -> Prop :=
  | exb_base : forall TL AL TR AR,
      exb 0 1 (TL &= AL) ((TL &= AL) &s) (TR &= AR) ((TR &s) &= tshift 0 AR)
  | exb_var_l : forall XL XR (A : typ) TL TL' TR TR',
      exb XL XR TL TL' TR TR' ->
      exb XL XR (TL & A) (TL' & (tshift XL A)) TR TR'
  | exb_var_r : forall XL XR (A : typ) TL TL' TR TR',
      exb XL XR TL TL' TR TR' ->
      exb XL XR TL TL' (TR & A) (TR' & (tshift XR A))
  | exb_tvar : forall XL XR TL TL' TR TR',
      exb XL XR TL TL' TR TR' ->
      exb (S XL) (S XR) (TL &s) (TL' &s) (TR &s) (TR' &s)
  | exb_teq : forall XL XR (A B : typ) TL TL' TR TR',
      exb XL XR TL TL' TR TR' ->
      exb (S XL) (S XR) (TL &= A) (TL' &= (tshift XL A)) (TR &= B) (TR' &= (tshift XR B))
  | exb_manil : forall XL XR (A : typ) TL TL' TR TR',
      exb XL XR TL TL' TR TR' ->
      exb (S XL) (S XR) (TL &= A) (TL' &= (tshift XL A)) (TR &s) (TR' &s)
  | exb_manir : forall XL XR (A : typ) TL TL' TR TR',
      exb XL XR TL TL' TR TR' ->
      exb (S XL) (S XR) (TL &s) (TL' &s) (TR &= A) (TR' &= (tshift XR A)).

#[export] Hint Constructors exb : core.

Lemma exb_left: forall XL XR TL TL' TR TR',
  exb XL XR TL TL' TR TR' -> insert_tvar XL TL TL'.
Proof.
  introv He. inductions He; eauto.
Qed.

Lemma exb_right: forall XL XR TL TL' TR TR',
  exb XL XR TL TL' TR TR' -> insert_tvar XR TR TR'.
Proof.
  introv He. inductions He; eauto.
Qed.

Lemma exb_off: forall XL XR TL TL' TR TR',
  exb XL XR TL TL' TR TR' -> XR = S XL.
Proof.
  introv He. inductions He; eauto.
Qed.

(* the exchange env-extension lemma (for eq_and bodies) *)
Lemma exb_env: forall T1 T2 T3 T4,
  teq T1 T3 T4 T2 -> lshape T3 -> lshape T4 -> forall XL XR TL TL' TR TR',
  exb XL XR TL TL' TR TR' ->
  exb (keyLen T3 + XL) (keyLen T4 + XR)
      (TL +++ T3) (TL' +++ tshift XL T3)
      (TR +++ T4) (TR' +++ tshift XR T4).
Proof.
  introv Ht. inductions Ht; introv Hl1 Hl2 He;
  try solve [inverts Hl1; inverts Hl2; eauto].
  - inverts Hl1. inverts Hl2.
    repeat rewrite tshift_and.
    repeat rewrite <-mcon_cons.
    destruct m.
    + simpl keyLen.
      eapply exb_var_r. eapply exb_var_l. eapply IHHt1; eauto.
    + simpl keyLen.
      replace (S (keyLen T3) + XL) with (S (keyLen T3 + XL)) by lia.
      replace (S (keyLen T4) + XR) with (S (keyLen T4 + XR)) by lia.
      eapply exb_teq. eapply IHHt1; eauto.
  - inverts Hl1. inverts Hl2.
    repeat rewrite tshift_st.
    repeat rewrite <-mcon_cons_st.
    simpl keyLen.
    replace (S (keyLen T3) + XL) with (S (keyLen T3 + XL)) by lia.
    replace (S (keyLen T4) + XR) with (S (keyLen T4 + XR)) by lia.
    eapply exb_tvar. eapply IHHt; eauto.
Qed.

(* the left split position XL always lands on the &= binder of the base, which is
   not a check var (check has no rule for index 0 of a &=). *)
Lemma exb_no_check_l: forall XL XR TL TL' TR TR',
  exb XL XR TL TL' TR TR' -> ~ check TL XL.
Proof.
  introv He. inductions He; introv Hc; try solve [inverts Hc; eauto].
Qed.

(* FORWARD preservation under exchange.  Mirrors shift_tvar_both; the eq_tvar case
   relies on XR = S XL together with check-vars being >= 1 at the split (the &= var
   at index 0 is never a check var, it is resolved by lookt / eq_eql/eq_eqr). *)
Lemma teq_exch: forall T1 A B T2,
  teq T1 A B T2 -> forall XL XR T1' T2',
  exb XL XR T1 T1' T2 T2' ->
  wfe T1' -> wfe T2' ->
  teq T1' (tshift XL A) (tshift XR B) T2'.
Proof.
  introv Ht. inductions Ht; introv He Hw1 Hw2;
  forwards Hi1: exb_left He; forwards Hi2: exb_right He;
  forwards Hoff: exb_off He.
  - (* eq_int *) simpl. eapply eq_int; [ exact Hw1 | exact Hw2 ].
  - (* eq_tvar : X checks both; X is never 0 at the split, so XL and XR shift it
       identically (XR = S XL). *)
    rename H1 into HcA. rename H2 into HcB.
    simpl. destruct (le_gt_dec XL X) eqn:EL; destruct (le_gt_dec XR X) eqn:ER.
    + (* both shift *)
      forwards Hca: check_insert_tvar_ge Hi1 l HcA.
      forwards Hcb: check_insert_tvar_ge Hi2 l0 HcB.
      eapply eq_tvar; [ exact Hw1 | exact Hw2
        | replace (1 + X) with (S X) in Hca by lia; exact Hca
        | replace (1 + X) with (S X) in Hcb by lia; exact Hcb ].
    + (* XL <= X but XR > X : with XR = S XL forces X = XL, the &= split position,
         which is not a check var on the left. *)
      assert (X = XL) by lia. subst.
      exfalso. eapply exb_no_check_l; [ exact He | exact HcA ].
    + lia.
    + (* both keep *)
      forwards Hca: check_insert_tvar_lt Hi1 g HcA.
      forwards Hcb: check_insert_tvar_lt Hi2 g0 HcB.
      eapply eq_tvar; [ exact Hw1 | exact Hw2 | exact Hca | exact Hcb ].
  - (* eq_eql *) forwards HIH: IHHt He Hw1 Hw2. simpl.
    destruct (le_gt_dec XL X).
    + forwards HL: lookt_insert_tvar_ge Hi1 l H. eapply eq_eql; eauto.
    + forwards HL: lookt_insert_tvar_lt Hi1 g H. eapply eq_eql; eauto.
  - (* eq_eqr *) forwards HIH: IHHt He Hw1 Hw2. simpl.
    destruct (le_gt_dec XR X).
    + forwards HL: lookt_insert_tvar_ge Hi2 l H. eapply eq_eqr; eauto.
    + forwards HL: lookt_insert_tvar_lt Hi2 g H. eapply eq_eqr; eauto.
  - (* eq_boxl : box on left is tshift-invariant; only the right side B shifts (by XR),
       reduce to one-sided rigid right shift *)
    assert (Hbe: tshift XL (boxt T3 A) = boxt T3 A) by reflexivity.
    rewrite Hbe. eapply eq_boxl.
    + eapply teq_shift_tvar_r_rigid;
        [ exact Ht | eapply wft_box_rigid; exact H | exact Hi2 | exact Hw2 ].
    + forwards Hbox: insert_tvar_wft Hi1 Hw1 H. simpl in Hbox. exact Hbox.
  - (* eq_boxr *)
    assert (Hbe: tshift XR (boxt T3 B) = boxt T3 B) by reflexivity.
    rewrite Hbe. eapply eq_boxr.
    + eapply teq_shift_tvar_l_rigid;
        [ exact Ht | eapply wft_box_rigid; exact H | exact Hi1 | exact Hw1 ].
    + forwards Hbox: insert_tvar_wft Hi2 Hw2 H. simpl in Hbox. exact Hbox.
  - (* eq_arr *) simpl. econstructor; eauto.
  - (* eq_all *) simpl. econstructor.
    eapply IHHt with (XL := S XL) (XR := S XR); eauto.
  - (* eq_manil : L gets &=A, R gets &s ; right type C double-shifted by XR *)
    simpl. eapply eq_manil.
    forwards Heq: tshift_tshift_prop_1 C 0 XR. simpl in Heq. rewrite Heq.
    forwards Hwl: teq_wfe_left Ht.
    forwards Hib: exb_manil A He.
    eapply IHHt with (XL := S XL) (XR := S XR).
    + exact Hib.
    + eapply itvar_wfe; [ eapply exb_left; exact Hib | exact Hwl ].
    + eapply we_tvar; exact Hw2.
  - (* eq_manir : R gets &=A, L gets &s ; left type B double-shifted by XL *)
    simpl. eapply eq_manir.
    forwards Heq: tshift_tshift_prop_1 B 0 XL. simpl in Heq. rewrite Heq.
    forwards Hwr: teq_wfe_right Ht.
    forwards Hib: exb_manir A He.
    eapply IHHt with (XL := S XL) (XR := S XR).
    + exact Hib.
    + eapply we_tvar; exact Hw1.
    + eapply itvar_wfe; [ eapply exb_right; exact Hib | exact Hwr ].
  - (* eq_top *) simpl. econstructor; eauto.
  - (* eq_and *)
    forwards Hwl: teq_wfe_left Ht2.
    forwards Hwr: teq_wfe_right Ht2.
    forwards Hib: exb_env Ht1 H H0 He.
    assert (HkL: keyLen T3 = keyLen T4) by
      (eapply teq_spine_keyLen; [ exact Ht1 | exact H | exact H0 ]).
    forwards Hoff2: exb_off He.
    destruct m; simpl; rewrite Hoff2 in *; eapply eq_and;
      [ eapply IHHt1; [ exact He | exact Hw1 | exact Hw2 ]
      | eapply lshape_tshift; exact H
      | eapply lshape_tshift; exact H0
      | eapply IHHt2;
          [ exact Hib
          | eapply itvar_wfe; [ eapply exb_left; exact Hib | exact Hwl ]
          | eapply itvar_wfe; [ eapply exb_right; exact Hib | exact Hwr ] ]
      | eapply IHHt1; [ exact He | exact Hw1 | exact Hw2 ]
      | eapply lshape_tshift; exact H
      | eapply lshape_tshift; exact H0
      | eapply IHHt2;
          [ exact Hib
          | eapply itvar_wfe; [ eapply exb_left; exact Hib | exact Hwl ]
          | eapply itvar_wfe; [ eapply exb_right; exact Hib | exact Hwr ] ] ].
  - (* eq_ands *) simpl. eapply eq_ands;
      [ eapply IHHt; [ exact He | exact Hw1 | exact Hw2 ]
      | eapply lshape_tshift; exact H
      | eapply lshape_tshift; exact H0 ].
  - (* eq_rcd *) simpl. econstructor; eauto.
Qed.

(* Public binder-exchange leaf (reflexive instantiation T1'=T1, A0'=A0, C=B):
   a dummy &s inserted ABOVE the top &= on the left and BELOW it on the right. *)
Lemma teq_exch_s_eq: forall T1 A0 B,
  teq (T1 &= A0) B B (T1 &= A0) ->
  wfe (T1 &= A0) ->
  teq ((T1 &= A0) &s) (tshift 0 B) (tshift 1 B) ((T1 &s) &= tshift 0 A0).
Proof.
  introv Ht Hw.
  forwards Hw1: wfe_inv Hw.            (* wfe T1 *)
  assert (HwsR: wfe ((T1 &s) &= tshift 0 A0)).
  { unfold wft. eapply insert_tvar_wft;
      [ eapply itv_here2 | eapply we_tvar; exact Hw1 | exact Hw ]. }
  eapply teq_exch with (XL := 0) (XR := 1);
    [ exact Ht
    | eapply exb_base
    | eapply we_tvar; exact Hw
    | exact HwsR ].
Qed.

(* NON-reflexive binder exchange: left/right manifest contents (AL/AR) and the
   related body types (B/C) may differ.  The congruence the positional mani
   assembly needs; generalises teq_exch_s_eq (its AL=AR, B=C instance). *)
Lemma teq_exch_s_neq: forall TL AL TR AR B C,
  teq (TL &= AL) B C (TR &= AR) ->
  wfe (TL &= AL) -> wfe (TR &= AR) ->
  teq ((TL &= AL) &s) (tshift 0 B) (tshift 1 C) ((TR &s) &= tshift 0 AR).
Proof.
  introv Ht Hw1 Hw2.
  assert (HwsR: wfe ((TR &s) &= tshift 0 AR)).
  { unfold wft. eapply insert_tvar_wft;
      [ eapply itv_here2 | eapply we_tvar; eapply wfe_inv; exact Hw2 | exact Hw2 ]. }
  eapply teq_exch with (XL := 0) (XR := 1);
    [ exact Ht | eapply exb_base | eapply we_tvar; exact Hw1 | exact HwsR ].
Qed.

Lemma teq_refl_size: forall n T1 A,
  bindings T1 A <= n ->
  wft T1 A ->
  teq T1 A A T1.
Proof.
  intros n. inductions n; introv Hl Ht.
  forwards~: bindings_min A T1. lia.

  unfold wft in *. inverts Ht; eauto.
  - eapply eq_eql; eauto.
    eapply eq_eqr; eauto.
    eapply IHn; eauto.
    forwards~: var_decr H3. lia.
    eapply lookt_wft; eauto.
  - econstructor.
    + eapply IHn; eauto. solve_size.
    + eapply IHn; eauto. solve_size.
  - econstructor.
    + eapply IHn; eauto. solve_size.
  - (* boxt: new boxbox design (frame-only context); box-wfts rebuilt via we_box *)
    eapply teq_boxbox;
      [ eapply IHn; [ solve_size | unfold wft; eassumption ]
      | unfold wft; eapply we_box; eauto
      | unfold wft; eapply we_box; eauto ].
  - (* mani A0 B : eq_manil + eq_manir reduce to the binder-EXCHANGE leaf,
       closed by teq_exch_s_eq (reflexivity of B at context T1&=A0). *)
    eapply eq_manil. eapply eq_manir.
    eapply teq_exch_s_eq;
      [ eapply IHn; [ solve_size | unfold wft; eassumption ]
      | unfold wft; eassumption ].
  - destruct m2.
    + econstructor; eauto. eapply IHn; eauto.
      unfold bindings in *. rewrite weight_evar in *. lia.
      eapply IHn; eauto. unfold bindings in *.
      rewrite weight_evar in *.
      rewrite <-mkb_eq. lia.
    + econstructor; eauto. eapply IHn; eauto.
      unfold bindings in *. rewrite weight_eteq in *. lia.
      eapply IHn; eauto. unfold bindings in *.
      rewrite weight_eteq in *.
      rewrite <-mkb_eq. lia.
  - econstructor; eauto. eapply IHn; eauto.
    unfold bindings in *. rewrite weight_etvar in *. lia.
  - econstructor. eapply IHn; eauto. solve_size.
Qed.

Lemma teq_refl: forall T A,
  wft T A ->
  teq T A A T.
Proof.
  intros. eapply teq_refl_size; eauto.
Qed.

(* ===== BALANCED (padded) mani inversion, the correct replacement for the old
   (now FALSE, and since removed) one-sided mani-inversion forms.  This
   is literally an inversion of eq_manil.  The eq_eqr / eq_boxr cases close via the
   self-side rigid rev unpad (teq_unpad_s_r_rigid); the eq_manir case (mani on the
   RIGHT too) closes by composing two reflexive binder exchanges (teq_exch_s_eq)
   around the IH using transitivity -- NO one-sided context op is used. *)
Lemma teq_mani_inv_l: forall T1 A B C T2,
  teq T1 (mani A B) C T2 ->
  teq (T1 &= A) B (tshift 0 C) (T2 &s).
Proof.
  introv Ht. inductions Ht.
  - (* eq_eqr : C = tvar X *) simpl.
    eapply eq_eqr; [ eapply lookt_etvar; exact H | ].
    eapply IHHt; reflexivity.
  - (* eq_boxr : C = boxt T3 B0 ; box rigid, body unpadded via self-side rev *)
    forwards IHe: IHHt; [ reflexivity | ].
    forwards Hrig: wft_box_rigid H.
    assert (Hbe: tshift 0 (boxt T3 B0) = boxt T3 B0) by reflexivity. rewrite Hbe.
    forwards HwfT3': wfe_sinv (wft_wfe (teq_wft_right IHe)).
    forwards Hbody: teq_unpad_s_r_rigid IHe Hrig HwfT3'.
    eapply eq_boxr; [ exact Hbody | ].
    rewrite <- Hbe.
    eapply insert_tvar_wft; [ eapply itv_here2 | eapply we_tvar; eapply wft_wfe; exact H | exact H ].
  - (* eq_manil : direct *) exact Ht.
  - (* eq_manir : mani on the RIGHT too; the IH is the exchanged form, restored to
       the goal premise by composing two reflexive binder exchanges (teq_exch_s_eq)
       around the IH using transitivity.  NO one-sided context op is used. *)
    assert (IHe: teq ((T1 &s) &= tshift 0 A) (tshift 1 B) (tshift 0 C) ((T2 &= A0) &s)).
    { eapply IHHt. simpl. reflexivity. }
    simpl.
    forwards Htop: eq_manir Ht.
    forwards HwftL: teq_wft_left Htop.
    forwards HwftR: teq_wft_right Htop.
    unfold wft in HwftL, HwftR. inverts HwftL. inverts HwftR.
    eapply eq_manir.
    eapply teq_trans with (B := tshift 0 C).
    eapply teq_trans with (B := tshift 1 B).
    + eapply teq_exch_s_eq; [ eapply teq_refl; unfold wft; eassumption | eassumption ].
    + exact IHe.
    + eapply teq_exch_s_eq; [ eapply teq_refl; unfold wft; eassumption | eassumption ].
Qed.


(* ===== RELOCATED dead-star block (stale tail; depends on deleted one-sided shifts) ===== *)
Lemma mcon_lshape: forall q, lshape q -> forall p, lshape p -> lshape (p +++ q).
Proof.
  introv Hq. inductions Hq; introv Hp.
  - simpl. exact Hp.
  - rewrite <- mcon_cons. eapply lsh_evar. eapply IHHq; exact Hp.
  - rewrite <- mcon_cons_st. eapply lsh_ands. eapply IHHq; exact Hp.
Qed.

Lemma keyLen_app: forall q p, keyLen (p +++ q) = keyLen p + keyLen q.
Proof.
  intros q. inductions q; intros; try solve [simpl; lia].
  - destruct m.
    + rewrite <- mcon_cons. simpl. eapply IHq1.
    + rewrite <- mcon_cons. simpl. rewrite IHq1. lia.
  - rewrite <- mcon_cons_st. simpl. rewrite IHq. lia.
Qed.

(* a check position strictly below keyLen p lives entirely in p, so it transfers
   across ANY base context. *)
Lemma check_below: forall p, lshape p -> forall G1 G2 V,
  check (G1 +++ p) V -> V < keyLen p -> check (G2 +++ p) V.
Proof.
  introv Hl. inductions Hl; introv Hc Hlt.
  - simpl in Hlt. lia.
  - rewrite <- mcon_cons in *. destruct m.
    + inverts Hc as Hc. eapply check_evar. eapply IHHl; [ exact Hc | simpl in Hlt; exact Hlt ].
    + inverts Hc as Hc. eapply check_eteq. eapply IHHl; [ exact Hc | simpl in Hlt; lia ].
  - rewrite <- mcon_cons_st in *. inverts Hc as Hc.
    + eapply check_zero.
    + eapply check_etvar. eapply IHHl; [ exact Hc | simpl in Hlt; lia ].
Qed.

Lemma dead_star_r_gen: forall L A B G2, teq L A B G2 ->
  forall T2 p D d, G2 = ((T2 &s) +++ p) -> lshape p ->
  rigid d L A ->
  (forall X, check ((T2 &s) +++ p) X -> X < d -> X < keyLen p) ->
  wft T2 D -> wfe ((T2 &= D) +++ p) ->
  teq L A B ((T2 &= D) +++ p).
Proof.
  introv H. inductions H; introv He Hlp Hrig HinvR Hwd Hwfe; subst.
  - (* eq_int *) econstructor; eauto.
  - (* eq_tvar : positional.  HcL : check L X, HcR : check ((T2&s)+++p) X. *)
    rename H1 into HcL. rename H2 into HcR.
    inverts Hrig.
    + (* rigid_bvar: X < d.  By HinvR, X < keyLen p, so X is a pure-prefix position
         that transfers across the &s -> &=D edit (check_below). *)
      match goal with Hlt: X < d |- _ => forwards HltK: HinvR HcR Hlt end.
      eapply eq_tvar;
        [ eauto | exact Hwfe | exact HcL
        | eapply check_below; [ exact Hlp | exact HcR | exact HltK ] ].
    + (* rigid_cvar: lookt L X _ contradicts check L X *)
      exfalso. eapply lookt_check_false; eauto.
  - (* eq_eql *)
    eapply eq_eql; [ exact H | ].
    eapply IHteq with (d := d);
      [ reflexivity | exact Hlp | eapply rigid_lookt; [ exact Hrig | exact H ] | exact HinvR | exact Hwd | exact Hwfe ].
  - (* eq_eqr *)
    eapply eq_eqr;
      [ eapply lookt_orel; [ eapply inst_orel; eauto using teq_wfe_right | exact H ]
      | eapply IHteq with (d := d); [ reflexivity | exact Hlp | exact Hrig | exact HinvR | exact Hwd | exact Hwfe ] ].
  - (* eq_boxl: A=(boxt T3 A0); the body's left frame is T3, fresh depth 0, Hinv
       vacuous (X<0 impossible).  Box-wft (H0) is unchanged by the right-frame edit. *)
    inverts Hrig as Hrb.
    eapply eq_boxl with (T3 := T3);
      [ eapply IHteq with (d := 0);
          [ reflexivity | exact Hlp | exact Hrb | intros X Hii Hlt; lia | exact Hwd | exact Hwfe ]
      | exact H0 ].
  - (* eq_boxr: body frame-local (T3); rebuild box-wft over the edited ambient *)
    forwards (Hbd & _ & _): boxt_wft_inv H0.
    eapply eq_boxr;
      [ exact H
      | unfold wft; eapply we_box;
          [ exact Hbd | eapply wft_box_rigid; exact H0 | exact Hwfe ] ].
  - (* eq_arr *)
    inverts Hrig as Hra Hrb.
    eapply eq_arr;
      [ eapply IHteq1 with (d := d); [ reflexivity | exact Hlp | exact Hra | exact HinvR | exact Hwd | exact Hwfe ]
      | eapply IHteq2 with (d := d); [ reflexivity | exact Hlp | exact Hrb | exact HinvR | exact Hwd | exact Hwfe ] ].
  - (* eq_all *)
    inverts Hrig as Hrb.
    eapply eq_all. rewrite mcon_cons_st.
    eapply (IHteq _ (p &s) _ (S d));
      [ apply mcon_cons_st | apply lsh_ands; exact Hlp | exact Hrb
      | (* HinvR for (G2&s) = (T2&s)+++(p&s) = ((T2&s)+++p)&s *)
        rewrite <- mcon_cons_st; intros X Hii Hlt; inverts Hii;
          [ simpl; lia
          | simpl; match goal with Hc: check (_ &s +++ _) ?X0 |- _ =>
              forwards: HinvR Hc; [ lia | lia ] end ]
      | exact Hwd
      | rewrite <- mcon_cons_st; apply we_tvar; exact Hwfe ].
  - (* eq_manil *)
    inverts Hrig as Hrb.
    eapply eq_manil. rewrite mcon_cons_st.
    eapply (IHteq _ (p &s) _ (S d));
      [ apply mcon_cons_st | apply lsh_ands; exact Hlp | exact Hrb
      | (* HinvR for (G2&s) = (T2&s)+++(p&s): right padded with &s, same shape as eq_all *)
        rewrite <- mcon_cons_st; intros X Hii Hlt; inverts Hii;
          [ simpl; lia
          | simpl; match goal with Hc: check (_ &s +++ _) ?X0 |- _ =>
              forwards: HinvR Hc; [ lia | lia ] end ]
      | exact Hwd
      | rewrite <- mcon_cons_st; apply we_tvar; exact Hwfe ].
  - (* eq_manir: left ctx pads &s (rigid depth bumps to S d via rigid_pad_s); right
       ctx pads &= (keyLen unchanged), so HinvR re-keys at S d on (G2&=A). *)
    eapply eq_manir. rewrite mcon_cons.
    eapply (IHteq _ (p &= A) _ (S d)).
    + rewrite mcon_cons. reflexivity.
    + apply lsh_evar; exact Hlp.
    + eapply rigid_pad_s. exact Hrig.
    + (* HinvR for (G2&=A) = (T2&s)+++(p&=A): right padded with &=, key +1 *)
      rewrite <- mcon_cons. intros X Hii Hlt. inverts Hii.
      match goal with Hc: check (_ &s +++ _) ?X0 |- _ =>
        forwards: HinvR Hc; [ lia | ] end. simpl. lia.
    + exact Hwd.
    + eapply inst_wfe; [ | exact Hwd ].
      forwards Hwr: teq_wfe_right H. rewrite mcon_cons in Hwr. exact Hwr.
  - (* eq_top *) econstructor; eauto.
  - (* eq_and *)
    inverts Hrig as Hra Hrb.
    forwards HsK: teq_spine_keyLen H H0 H1.
    eapply eq_and;
      [ eapply IHteq1 with (d := d); [ reflexivity | exact Hlp | exact Hra | exact HinvR | exact Hwd | exact Hwfe ]
      | exact H0 | exact H1 | ].
    rewrite mapp_ass. eapply (IHteq2 _ (p +++ T4) _ (d + keyLen T3)).
    + rewrite mapp_ass. reflexivity.
    + eapply mcon_lshape; [ exact H1 | exact Hlp ].
    + exact Hrb.
    + (* HinvR for (G2+++T4) = (T2&s)+++(p+++T4) = ((T2&s)+++p)+++T4 *)
      intros X Hii Hlt.
      rewrite keyLen_app.
      rewrite <- mapp_ass in Hii.
      forwards [HltK|(X'&HeqX&HcX)]: check_app_dec H1 Hii.
      * lia.
      * subst X. forwards Hd: HinvR HcX; [ lia | ]. lia.
    + exact Hwd.
    + eapply inst_wfe; [ | exact Hwd ].
      forwards Hwr: teq_wfe_right H2. rewrite mapp_ass in Hwr. exact Hwr.
  - (* eq_ands *)
    inverts Hrig as Hrb.
    eapply eq_ands;
      [ eapply IHteq with (d := d); [ reflexivity | exact Hlp | exact Hrb | exact HinvR | exact Hwd | exact Hwfe ]
      | exact H0 | exact H1 ].
  - (* eq_rcd *)
    inverts Hrig as Hrb.
    eapply eq_rcd.
    eapply IHteq with (d := d); [ reflexivity | exact Hlp | exact Hrb | exact HinvR | exact Hwd | exact Hwfe ].
Qed.

Lemma dead_star_r: forall L A B p T2 D,
  teq L A B ((T2 &s) +++ p) -> lshape p ->
  rigid 0 L A -> wft T2 D -> wfe ((T2 &= D) +++ p) ->
  teq L A B ((T2 &= D) +++ p).
Proof.
  introv H Hlp Hr Hwd Hwfe.
  eapply dead_star_r_gen with (d := 0);
    [ exact H | reflexivity | exact Hlp | exact Hr | intros X Hii Hlt; lia | exact Hwd | exact Hwfe ].
Qed.

Lemma dead_star_l: forall R A B p T1 C,
  teq ((T1 &s) +++ p) A B R -> lshape p ->
  rigid 0 R B -> wft T1 C -> wfe ((T1 &= C) +++ p) ->
  teq ((T1 &= C) +++ p) A B R.
Proof.
  introv H Hlp Hr Hwc Hwfe.
  eapply teq_sym. eapply dead_star_r; [ eapply teq_sym; exact H | exact Hlp | exact Hr | exact Hwc | exact Hwfe ].
Qed.


Lemma mshift_ord: forall T A, ord T -> mshift T A = A.
Proof. introv Ho. inverts Ho; reflexivity. Qed.

(* coherence weakening: the original coherence teq T1 cc dd T2 lifted into the
   instantiated, prefixed contexts.  Both types are mshift-lifted through their
   respective prefixes; the abstract-binder counts of p3,p4 must match so the
   star alignment of eq_tvar is preserved. *)

(* ===== insl: ONE-SIDED binder insertion allowing a &= (manifest) base.  Exactly
   insert_tvar plus the base &= constructor.  Native check/lookt/wft/env projections
   (the forward wft lemma takes wfe of the GROWN context, so a &= value is fine; we
   never need an unconditional wfe-forward lemma). *)
Inductive insl : nat -> typ -> typ -> Prop :=
  | isl_here_s : forall T, insl 0 T (T &s)
  | isl_here_e : forall T A, wft T A -> insl 0 T (T &= A)
  | isl_var : forall (X : nat) (A : typ) T T',
      insl X T T' -> insl X (T & A) (T' & (tshift X A))
  | isl_tvar : forall (X : nat) T T',
      insl X T T' -> insl (S X) (T &s) (T' &s)
  | isl_teq : forall (X : nat) (A : typ) T T',
      insl X T T' -> insl (S X) (T &= A) (T' &= (tshift X A)).

#[export] Hint Constructors insl : core.

Lemma insl_check_ge: forall X T T', insl X T T' -> forall Z,
  X <= Z -> check T Z -> check T' (1 + Z).
Proof.
  introv Hi. inductions Hi; introv Hl Hc;
    try solve [replace (1 + Z) with (S Z) by lia; eauto].
  - inverts Hc. eapply check_evar. eapply IHHi; eauto.
  - destruct Z; [lia|]. inverts Hc. eapply check_etvar. eapply IHHi; eauto. lia.
  - destruct Z; [lia|]. inverts Hc. eapply check_eteq. eapply IHHi; eauto. lia.
Qed.

Lemma insl_check_lt: forall X T T', insl X T T' -> forall Z,
  X > Z -> check T Z -> check T' Z.
Proof.
  introv Hi. inductions Hi; introv Hl Hc; try solve [lia].
  - inverts Hc. eapply check_evar. eapply IHHi; eauto.
  - destruct Z; [eapply check_zero|]. inverts Hc. eapply check_etvar. eapply IHHi; eauto. lia.
  - destruct Z; [inverts Hc|]. inverts Hc. eapply check_eteq. eapply IHHi; eauto. lia.
Qed.

Lemma insl_lookt_ge: forall X T T', insl X T T' -> forall Z Av,
  X <= Z -> lookt T Z Av -> lookt T' (1 + Z) (tshift X Av).
Proof.
  introv Hi. inductions Hi; introv Hl Hk;
    try solve [simpl; eapply lookt_eteq; eauto]; try solve [simpl; eapply lookt_etvar; eauto].
  - inverts Hk. simpl. eapply lookt_evar. eapply IHHi; eauto.
  - inverts Hk as Hk.
    forwards~ Hr: IHHi Hk; [lia|].
    match type of Hk with lookt _ ?k ?bv =>
      forwards~ He: tshift_tshift_prop_1 bv 0 X end;
    simpl in He; rewrite <- He; eapply lookt_etvar; eauto.
  - inverts Hk as Hk; [lia|].
    forwards~ Hr: IHHi Hk; [lia|].
    match type of Hk with lookt _ ?k ?bv =>
      forwards~ He: tshift_tshift_prop_1 bv 0 X end;
    simpl in He; rewrite <- He; eapply lookt_eteq; eauto.
Qed.

Lemma insl_lookt_lt: forall X T T', insl X T T' -> forall Z Av,
  X > Z -> lookt T Z Av -> lookt T' Z (tshift X Av).
Proof.
  introv Hi. inductions Hi; introv Hl Hk; try solve [lia].
  - inverts Hk. simpl. eapply lookt_evar. eapply IHHi; eauto.
  - inverts Hk as Hk.
    forwards~ Hr: IHHi Hk; [lia|].
    match type of Hk with lookt _ ?k ?bv =>
      forwards~ He: tshift_tshift_prop_1 bv 0 X end;
    simpl in He; rewrite <- He; eapply lookt_etvar; eauto.
  - inverts Hk as Hk.
    + forwards~ He: tshift_tshift_prop_1 A 0 X.
      simpl in He; rewrite <- He; eapply lookt_zero.
    + forwards~ Hr: IHHi Hk; [lia|].
      match type of Hk with lookt _ ?k ?bv =>
        forwards~ He: tshift_tshift_prop_1 bv 0 X end;
      simpl in He; rewrite <- He; eapply lookt_eteq; eauto.
Qed.

Lemma insl_env: forall X T T', insl X T T' -> forall T1,
  insl (keyLen T1 + X) (T +++ T1) (T' +++ tshift X T1).
Proof.
  introv Hi. intros. gen T T'. inductions T1; introv Hi;
    try solve [simpl; eauto].
  - rewrite <- mcon_cons. rewrite tshift_and. rewrite <- mcon_cons.
    destruct m.
    + replace (keyLen (T1_1 & T1_2) + X) with (keyLen T1_1 + X) by (simpl; eauto).
      eauto.
    + replace (keyLen (T1_1 &= T1_2) + X) with (S (keyLen T1_1 + X)) by (simpl; eauto).
      eauto.
  - rewrite <- mcon_cons_st. rewrite tshift_st. repeat rewrite <- mcon_cons_st.
    replace (keyLen (T1 &s) + X) with (S (keyLen T1 + X)) by (simpl; eauto).
    eauto.
Qed.

Lemma insl_wft: forall (A : typ) X T T',
  insl X T T' -> wfe T' -> wft T A -> wft T' (tshift X A).
Proof.
  intros A. inductions A; introv Hi He Hw; unfold wft in *; try solve [eauto];
    try solve [simpl; inverts* Hw].
  - simpl. inverts Hw.
    + destruct (le_gt_dec X n).
      * forwards~: insl_check_ge Hi n.
      * forwards~: insl_check_lt Hi n.
    + destruct (le_gt_dec X n).
      * forwards~ Hl: insl_lookt_ge Hi H3. eapply we_get; eauto.
      * forwards~ Hl: insl_lookt_lt Hi H3. eapply we_get; eauto.
  - simpl. inverts Hw.
    forwards~: IHA1 Hi H4.
    forwards~: IHA2 (S X) (T &= A1) (T' &= (tshift X A1)).
  - destruct m.
    + simpl. inverts Hw.
      econstructor; eauto; try solve [eapply lshape_tshift; eauto].
      eapply IHA2; eauto.
      eapply insl_env; eauto.
      forwards~: wfe_inv H5.
      forwards~ [?|[?|?]]: ord_dec A1.
      * inverts H0; subst; simpl; eauto.
      * destruct H0 as (A & m & B & ?). subst.
        forwards~: wfe_mcon H. inverts* H6.
        forwards~: IHA1 Hi H0.
        rewrite tshift_and in H1. rewrite tshift_and.
        eapply wfe_to_mcon; eauto.
      * destruct H0 as (A & ?). subst.
        forwards~: wfe_mcon H.
        forwards~: IHA1 Hi H0.
        rewrite tshift_st in H1. rewrite tshift_st.
        eapply wfe_to_mcon_st; eauto.
    + simpl. inverts Hw.
      econstructor; eauto; try solve [eapply lshape_tshift; eauto].
      eapply IHA2; eauto.
      eapply insl_env; eauto.
      forwards~: wfe_inv H5.
      forwards~ [?|[?|?]]: ord_dec A1.
      * inverts H0; subst; simpl; eauto.
      * destruct H0 as (A & m & B & ?). subst.
        forwards~: wfe_mcon H. inverts* H6.
        forwards~: IHA1 Hi H0.
        rewrite tshift_and in H1. rewrite tshift_and.
        eapply wfe_to_mcon; eauto.
      * destruct H0 as (A & ?). subst.
        forwards~: wfe_mcon H.
        forwards~: IHA1 Hi H0.
        rewrite tshift_st in H1. rewrite tshift_st.
        eapply wfe_to_mcon_st; eauto.
  - simpl. inverts Hw.
    econstructor; eauto.
    eapply lshape_tshift; eauto.
Qed.

(* up-direction wfe: the &= base carries its value's wft, so the grown context is
   well-formed.  (Mirrors itvar_wfe but valid for the &= base too.) *)
Lemma insl_wfe_up: forall X T T', insl X T T' -> wfe T -> wfe T'.
Proof.
  introv Hi. inductions Hi; introv Hw.
  - (* isl_here_s *) eapply we_tvar; exact Hw.
  - (* isl_here_e *) unfold wft in *. exact H.
  - (* isl_var : & value *)
    forwards Hwt: wfe_inv Hw.
    forwards HwT: IHHi Hwt.
    forwards Hwet: wfe_evar_eteq Hw.
    forwards Hwft: insl_wft Hi HwT Hwet.
    eapply wfe_eteq_evar; exact Hwft.
  - (* isl_tvar : &s *)
    forwards Hwt: wfe_sinv Hw. forwards HwT: IHHi Hwt. eapply we_tvar; exact HwT.
  - (* isl_teq : &= key *)
    forwards Hwt: wfe_inv Hw.
    forwards HwT: IHHi Hwt.
    forwards Hwft: insl_wft Hi HwT Hw.
    exact Hwft.
Qed.

(* insl-based rigid box shift: ambient insert may be a &= base (insl); the
   frame-rigid body never uses the ambient var, so the insert kind is irrelevant.
   itvar_wfe (unconditional) is replaced by insl_wft (value wft from grown ctx). *)
Lemma teq_shift_tvar_r_rigid_insl_aux: forall T1 A B T2,
  teq T1 A B T2 -> forall d Y T2', rigid d T1 A ->
  insl Y T2 T2' -> wfe T2' ->
  align T1 T2 d Y ->
  teq T1 A (tshift Y B) T2'.
Proof.
  introv Ht. inductions Ht; introv Hr Hi Hw2 Hal.
  - (* eq_int *) simpl. eapply eq_int; eauto.
  - (* eq_tvar : the crux.  H1 : check T1 X, H2 : check T2 X (positional). *)
    rename H1 into HcX. rename H2 into HcY.
    inverts Hr.
    + (* rigid_bvar : X < d ; align gives X < Y so the shift keeps X *)
      match goal with Hxd: _ < d |- _ =>
        forwards~ HY: Hal HcX Hxd HcY end.
      simpl.
      match goal with |- context[le_gt_dec ?a ?b] => destruct (le_gt_dec a b) as [Hle|Hgt]; [lia|] end.
      eapply eq_tvar; eauto. eapply insl_check_lt; eauto.
    + (* rigid_cvar : lookt T1 X B0 -- contradicts check T1 X *)
      exfalso. eapply lookt_check_false; [ eassumption | exact HcX ].
  - (* eq_eql : left var, lookt T1 X A; recurse, right shifts.
       Need rigid d T1 A (rigidity of the resolved value) for the IH. *)
    eapply eq_eql; [ exact H |].
    eapply IHHt; eauto.
    eapply rigid_lookt; [ exact Hr | exact H ].
  - (* eq_eqr : right var, lookt T2 X B0 *)
    simpl. destruct (le_gt_dec Y X) eqn:E.
    + (* X >= Y : index bumps to S X, insl_lookt_ge *)
      eapply eq_eqr.
      * forwards~ HL: insl_lookt_ge Hi l H. simpl in HL. exact HL.
      * eapply IHHt; eauto.
    + (* X < Y : index stays, insl_lookt_lt *)
      eapply eq_eqr.
      * forwards~ HL: insl_lookt_lt Hi g H. exact HL.
      * eapply IHHt; eauto.
  - (* eq_boxl : left box; tshift identity on left, recurse box body into T2.
       Box-wft (H0) is on the LEFT frame T1, untouched by the right-frame insert. *)
    inverts Hr.
    eapply eq_boxl;
      [ eapply IHHt; [ eassumption | exact Hi | exact Hw2 |];
        unfold align; introv Hin Hlt Hin2; lia
      | match goal with Hb: wft T1 (boxt T3 A) |- _ => exact Hb end ].
  - (* eq_boxr : right box; tshift identity on the box, rebuild box-wft over T2' *)
    assert (Hbe: tshift Y (boxt T3 B) = boxt T3 B) by reflexivity.
    rewrite Hbe.
    match goal with Hb: wft T2 (boxt T3 B) |- _ =>
      forwards (Hbd & _ & _): boxt_wft_inv Hb;
      forwards Hrg: wft_box_rigid Hb end.
    eapply eq_boxr;
      [ eassumption
      | unfold wft; eapply we_box; [ exact Hbd | exact Hrg | exact Hw2 ] ].
  - (* eq_arr *)
    inverts Hr. simpl. eapply eq_arr; eauto.
  - (* eq_all *)
    inverts Hr. simpl. eapply eq_all.
    eapply IHHt; [ eassumption | eapply isl_tvar; exact Hi | eapply we_tvar; exact Hw2 |].
    (* align (T1 &s) (T2 &s) (S d) (S Y) *)
    unfold align. introv Hc1 Hlt Hc2. destruct X as [|X].
    + (* position 0 : check_zero, trivially < S Y *) lia.
    + inverts Hc1. inverts Hc2.
      forwards HY: Hal; [ eassumption | lia | eassumption | ]. lia.
  - (* eq_manil : left mani (L gets &=A0), right gets &s ; right type C double-shifted *)
    inverts Hr. simpl. eapply eq_manil.
    forwards Heq: tshift_tshift_prop_1 C 0 Y. simpl in Heq. rewrite Heq.
    eapply IHHt with (Y := S Y);
      [ eassumption | eapply isl_tvar; exact Hi | eapply we_tvar; exact Hw2 |].
    (* align (T1 &= A) (T2 &s) (S d) (S Y) *)
    unfold align. introv Hc1 Hlt Hc2.
    inverts Hc1. (* check (T1&=A): X = S X0, check T1 X0 *)
    inverts Hc2. (* check (T2&s) (S X0): check_etvar -> check T2 X0 *)
    match goal with Ha: check T1 ?xx, Hb: check T2 _ |- _ =>
      assert (Hx0d: xx < d) by lia;
      forwards HY: Hal Ha Hx0d Hb end; lia.
  - (* eq_manir : right mani (R gets &=A0), left gets &s ; left double-shifted *)
    simpl. eapply eq_manir.
    forwards Hwr: teq_wfe_right Ht.
    eapply IHHt with (d := S d) (Y := S Y);
      [ eapply rigid_pad_s; exact Hr
      | eapply isl_teq; exact Hi
      | eapply insl_wfe_up; [ eapply isl_teq; exact Hi | exact Hwr ] |].
    (* align (T1 &s) (T2 &= A) (S d) (S Y) *)
    unfold align. introv Hc1 Hlt Hc2.
    inverts Hc2. (* check (T2&=A) (S X0): check_eteq -> check T2 X0 *)
    inverts Hc1. (* check (T1&s) (S X0): check_etvar -> check T1 X0 *)
    match goal with Ha: check T1 ?xx, Hb: check T2 _ |- _ =>
      assert (Hx0d: xx < d) by lia;
      forwards HY: Hal Ha Hx0d Hb end; lia.
  - (* eq_top *) simpl. eapply eq_top; eauto.
  - (* eq_and *)
    inverts Hr.
    forwards Hwr: teq_wfe_right Ht2.
    forwards Hins: insl_env Hi T4.
    assert (HkL: keyLen T3 = keyLen T4) by
      (eapply teq_spine_keyLen; [ exact Ht1 | exact H | exact H0 ]).
    destruct m; simpl; eapply eq_and;
      [ (* spine *) eapply IHHt1; [ eassumption | exact Hi | exact Hw2 |];
        solve [ unfold align; introv Hc1 Hlt Hc2; eapply Hal; eauto ]
      | (* lshape T3 *) assumption
      | (* lshape (tshift Y T4) *) eapply lshape_tshift; assumption
      | (* body *) eapply IHHt2;
          [ eassumption
          | exact Hins
          | eapply insl_wfe_up; [ exact Hins | exact Hwr ]
          | eapply align_and; [ exact Hal | exact H | exact H0 | exact HkL ] ]
      | (* spine *) eapply IHHt1; [ eassumption | exact Hi | exact Hw2 |];
        solve [ unfold align; introv Hc1 Hlt Hc2; eapply Hal; eauto ]
      | assumption
      | eapply lshape_tshift; assumption
      | eapply IHHt2;
          [ eassumption
          | exact Hins
          | eapply insl_wfe_up; [ exact Hins | exact Hwr ]
          | eapply align_and; [ exact Hal | exact H | exact H0 | exact HkL ] ] ].
  - (* eq_ands *)
    inverts Hr. simpl. eapply eq_ands.
    + eapply IHHt; [ eassumption | exact Hi | exact Hw2 | exact Hal ].
    + assumption.
    + eapply lshape_tshift; assumption.
  - (* eq_rcd *)
    inverts Hr. simpl. eapply eq_rcd; eauto.
Qed.

Lemma teq_shift_tvar_r_rigid_insl: forall T1 A B T2,
  teq T1 A B T2 -> forall Y T2', rigid 0 T1 A ->
  insl Y T2 T2' -> wfe T2' ->
  teq T1 A (tshift Y B) T2'.
Proof.
  introv Ht Hr Hi Hw2.
  eapply teq_shift_tvar_r_rigid_insl_aux; eauto.
  unfold align. introv Hin Hlt Hin2. lia.
Qed.

Lemma teq_shift_tvar_l_rigid_insl: forall T1 A B T2,
  teq T1 A B T2 -> forall X T1', rigid 0 T2 B ->
  insl X T1 T1' -> wfe T1' ->
  teq T1' (tshift X A) B T2.
Proof.
  introv Ht Hr Hi Hw1.
  eapply teq_sym.
  eapply teq_shift_tvar_r_rigid_insl; [ eapply teq_sym; exact Ht | exact Hr | exact Hi | exact Hw1 ].
Qed.

(* Depth-general left-frame insertion, keyed by rigidity on the RIGHT side.
   Symmetric of teq_shift_tvar_r_rigid_insl_aux via teq_sym. *)

(* ===== insb: two-sided, left/right projecting to insl ===== *)
Inductive insb : nat -> typ -> typ -> typ -> typ -> Prop :=
  | isb_here_ss : forall TL TR, insb 0 TL (TL &s) TR (TR &s)
  | isb_here_ee : forall TL A TR B, wft TL A -> wft TR B -> insb 0 TL (TL &= A) TR (TR &= B)
  | isb_here_es : forall TL A TR, wft TL A -> insb 0 TL (TL &= A) TR (TR &s)
  | isb_here_se : forall TL TR B, wft TR B -> insb 0 TL (TL &s) TR (TR &= B)
  | isb_var_l : forall (X : nat) (A : typ) TL TL' TR TR',
      insb X TL TL' TR TR' -> insb X (TL & A) (TL' & (tshift X A)) TR TR'
  | isb_var_r : forall (X : nat) (A : typ) TL TL' TR TR',
      insb X TL TL' TR TR' -> insb X TL TL' (TR & A) (TR' & (tshift X A))
  | isb_tvar : forall (X : nat) TL TL' TR TR',
      insb X TL TL' TR TR' -> insb (S X) (TL &s) (TL' &s) (TR &s) (TR' &s)
  | isb_teq : forall (X : nat) (A B : typ) TL TL' TR TR',
      insb X TL TL' TR TR' -> insb (S X) (TL &= A) (TL' &= (tshift X A)) (TR &= B) (TR' &= (tshift X B))
  | isb_manil : forall (X : nat) (A : typ) TL TL' TR TR',
      insb X TL TL' TR TR' -> insb (S X) (TL &= A) (TL' &= (tshift X A)) (TR &s) (TR' &s)
  | isb_manir : forall (X : nat) (A : typ) TL TL' TR TR',
      insb X TL TL' TR TR' -> insb (S X) (TL &s) (TL' &s) (TR &= A) (TR' &= (tshift X A)).

#[export] Hint Constructors insb : core.

Lemma insb_left: forall X TL TL' TR TR', insb X TL TL' TR TR' -> insl X TL TL'.
Proof. introv Hi. inductions Hi; eauto. Qed.

Lemma insb_right: forall X TL TL' TR TR', insb X TL TL' TR TR' -> insl X TR TR'.
Proof. introv Hi. inductions Hi; eauto. Qed.

Lemma insb_env: forall T1 T2 T3 T4,
  teq T1 T3 T4 T2 -> lshape T3 -> lshape T4 -> forall X TL TL' TR TR',
  insb X TL TL' TR TR' ->
  insb (keyLen T3 + X) (TL +++ T3) (TL' +++ tshift X T3)
       (TR +++ T4) (TR' +++ tshift X T4).
Proof.
  introv Ht. inductions Ht; introv Hl1 Hl2 Hi;
  try solve [inverts Hl1; inverts Hl2; eauto].
  - forwards HkL: teq_lshape_keyLen Ht1 H H0.
    inverts Hl1. inverts Hl2.
    repeat rewrite tshift_and. repeat rewrite <-mcon_cons.
    destruct m.
    + simpl keyLen. rewrite <- HkL.
      eapply isb_var_r. eapply isb_var_l. eapply IHHt1; eauto.
    + simpl keyLen. rewrite <- HkL.
      replace (S (keyLen T3) + X) with (S (keyLen T3 + X)) by lia.
      eapply isb_teq. eapply IHHt1; eauto.
  - inverts Hl1. inverts Hl2.
    repeat rewrite tshift_st. repeat rewrite <-mcon_cons_st.
    simpl keyLen. replace (S (keyLen T3) + X) with (S (keyLen T3 + X)) by lia.
    eapply isb_tvar. eapply IHHt; eauto.
Qed.

(* forward two-sided shift over insb (analog of shift_tvar_both) *)
Lemma shift_insb: forall T1 A B T2,
  teq T1 A B T2 -> forall X T1' T2',
  insb X T1 T1' T2 T2' -> wfe T1' -> wfe T2' ->
  teq T1' (tshift X A) (tshift X B) T2'.
Proof.
  introv Ht. inductions Ht; introv Hi Hw1 Hw2;
  forwards Hi1: insb_left Hi; forwards Hi2: insb_right Hi.
  - simpl. eapply eq_int; [ exact Hw1 | exact Hw2 ].
  - simpl. destruct (le_gt_dec X0 X).
    + forwards Hca: insl_check_ge Hi1 l H1.
      forwards Hcb: insl_check_ge Hi2 l H2.
      eapply eq_tvar; [ exact Hw1 | exact Hw2 | exact Hca | exact Hcb ].
    + forwards Hca: insl_check_lt Hi1 g H1.
      forwards Hcb: insl_check_lt Hi2 g H2.
      eapply eq_tvar; [ exact Hw1 | exact Hw2 | exact Hca | exact Hcb ].
  - forwards HIH: IHHt Hi Hw1 Hw2. simpl.
    destruct (le_gt_dec X0 X).
    + forwards HL: insl_lookt_ge Hi1 l H. eapply eq_eql; eauto.
    + forwards HL: insl_lookt_lt Hi1 g H. eapply eq_eql; eauto.
  - forwards HIH: IHHt Hi Hw1 Hw2. simpl.
    destruct (le_gt_dec X0 X).
    + forwards HL: insl_lookt_ge Hi2 l H. eapply eq_eqr; eauto.
    + forwards HL: insl_lookt_lt Hi2 g H. eapply eq_eqr; eauto.
  - assert (Hbe: tshift X (boxt T3 A) = boxt T3 A) by reflexivity.
    rewrite Hbe. eapply eq_boxl.
    + eapply teq_shift_tvar_r_rigid_insl;
        [ exact Ht | eapply wft_box_rigid; exact H | exact Hi2 | exact Hw2 ].
    + forwards Hbox: insl_wft Hi1 Hw1 H. simpl in Hbox. exact Hbox.
  - assert (Hbe: tshift X (boxt T3 B) = boxt T3 B) by reflexivity.
    rewrite Hbe. eapply eq_boxr.
    + eapply teq_shift_tvar_l_rigid_insl;
        [ exact Ht | eapply wft_box_rigid; exact H | exact Hi1 | exact Hw1 ].
    + forwards Hbox: insl_wft Hi2 Hw2 H. simpl in Hbox. exact Hbox.
  - simpl. econstructor; eauto.
  - simpl. econstructor. eapply IHHt with (X := S X); eauto.
  - (* eq_manil : left gets &= A (isb_manil), right gets &s *)
    simpl. eapply eq_manil.
    forwards Heq: tshift_tshift_prop_1 C 0 X. simpl in Heq. rewrite Heq.
    forwards Hwl: teq_wfe_left Ht.
    forwards Hib: isb_manil A Hi.
    eapply IHHt with (X := S X).
    + exact Hib.
    + eapply insl_wfe_up; [ eapply insb_left; exact Hib | exact Hwl ].
    + eapply we_tvar; exact Hw2.
  - (* eq_manir : right gets &= A (isb_manir), left gets &s *)
    simpl. eapply eq_manir.
    forwards Heq: tshift_tshift_prop_1 B 0 X. simpl in Heq. rewrite Heq.
    forwards Hwr: teq_wfe_right Ht.
    forwards Hib: isb_manir A Hi.
    eapply IHHt with (X := S X).
    + exact Hib.
    + eapply we_tvar; exact Hw1.
    + eapply insl_wfe_up; [ eapply insb_right; exact Hib | exact Hwr ].
  - simpl. econstructor; eauto.
  - (* eq_and *)
    forwards Hwl: teq_wfe_left Ht2.
    forwards Hwr: teq_wfe_right Ht2.
    forwards Hib: insb_env Ht1 H H0 Hi.
    assert (HkL: keyLen T3 = keyLen T4) by
      (eapply teq_spine_keyLen; [ exact Ht1 | exact H | exact H0 ]).
    destruct m; simpl; rewrite <- HkL; eapply eq_and;
      [ eapply IHHt1; [ exact Hi | exact Hw1 | exact Hw2 ]
      | eapply lshape_tshift; exact H
      | eapply lshape_tshift; exact H0
      | eapply IHHt2;
          [ exact Hib
          | eapply insl_wfe_up; [ eapply insb_left; exact Hib | exact Hwl ]
          | eapply insl_wfe_up; [ eapply insb_right; exact Hib | exact Hwr ] ]
      | eapply IHHt1; [ exact Hi | exact Hw1 | exact Hw2 ]
      | eapply lshape_tshift; exact H
      | eapply lshape_tshift; exact H0
      | eapply IHHt2;
          [ exact Hib
          | eapply insl_wfe_up; [ eapply insb_left; exact Hib | exact Hwl ]
          | eapply insl_wfe_up; [ eapply insb_right; exact Hib | exact Hwr ] ] ].
  - simpl. eapply eq_ands;
      [ eapply IHHt; [ exact Hi | exact Hw1 | exact Hw2 ]
      | eapply lshape_tshift; exact H
      | eapply lshape_tshift; exact H0 ].
  - simpl. econstructor; eauto.
Qed.

(* add a term variable (&) on the LEFT: peels to add_evar's ae_add; only the new binder's
   type must be wft, the equated types A,B are untouched. *)
Lemma adde_teq_l: forall T1 A B T2 C,
  teq T1 A B T2 -> wft T1 C -> teq (T1 & C) A B T2.
Proof.
  introv Ht Hw. eapply add_evar_teq; [ exact Ht | eapply ae_add; [ eapply add_evar_refl | exact Hw ] ].
Qed.

Lemma adde_teq_r: forall T1 A B T2 C,
  teq T1 A B T2 -> wft T2 C -> teq T1 A B (T2 & C).
Proof.
  introv Ht Hw. eapply teq_sym. eapply adde_teq_l; [ eapply teq_sym; exact Ht | exact Hw ].
Qed.

(* base case: insert the matched &=cc/&=dd pair at position 0 (shift by tshift 0). *)
Lemma coh_weaken_base: forall T1 T2 cc dd,
  teq T1 cc dd T2 -> wfe (T1 &= cc) -> wfe (T2 &= dd) ->
  teq (T1 &= cc) (tshift 0 cc) (tshift 0 dd) (T2 &= dd).
Proof.
  introv Ht Hw1 Hw2.
  eapply shift_insb; [ exact Ht | eapply isb_here_ee; [ exact Hw1 | exact Hw2 ] | exact Hw1 | exact Hw2 ].
Qed.

(* keyLen of the entry constructors *)
Lemma keyLen_teq2: forall p A, keyLen (and p rt A) = S (keyLen p).
Proof. reflexivity. Qed.
Lemma keyLen_st2: forall p, keyLen (p &s) = S (keyLen p).
Proof. reflexivity. Qed.

Lemma ord_keyLen_0: forall T, ord T -> keyLen T = 0.
Proof. introv Ho. inverts Ho; reflexivity. Qed.

(* coherence weakening (lockstep over equal-keyLen prefixes).  Strong induction on
   combined tsize.  Outer term-variable entries (&) peel one-sided; outer key
   entries pair two-sided at position 0 via shift_insb (isb_here_ss/_ee/_es/_se),
   each shifting by tshift 0 (matching mshift). *)
Lemma coh_weaken_n: forall n p3 p4 T1 T2 cc dd,
  tsize p3 + tsize p4 <= n ->
  teq T1 cc dd T2 ->
  keyLen p3 = keyLen p4 ->
  wfe ((T1 &= cc) +++ p3) -> wfe ((T2 &= dd) +++ p4) ->
  teq ((T1 &= cc) +++ p3) (mshift p3 (tshift 0 cc)) (mshift p4 (tshift 0 dd)) ((T2 &= dd) +++ p4).
Proof.
  induction n; introv Hsz Ht Hkey Hw1 Hw2.
  { destruct p3; simpl in Hsz; lia. }
  assert (Hwb1: wfe (T1 &= cc)) by (eapply wfe_cut; exact Hw1).
  assert (Hwb2: wfe (T2 &= dd)) by (eapply wfe_cut; exact Hw2).
  forwards Hbase: coh_weaken_base Ht Hwb1 Hwb2.
  forwards~ [Ho3|Hd3]: ord_dec p3.
  - (* LEFT ord : keyLen p3 = 0 *)
    rewrite (ord_inert Ho3) in *. rewrite (mshift_ord _ Ho3).
    forwards Hk3: ord_keyLen_0 Ho3.
    forwards~ [Ho4|Hd4]: ord_dec p4.
    + rewrite (ord_inert Ho4) in *. rewrite (mshift_ord _ Ho4). exact Hbase.
    + destruct Hd4 as [(p4a&m4&A4&?)|(p4a&?)]; subst.
      * destruct m4.
        ** (* right & value *)
           assert (Hkey2: keyLen p3 = keyLen p4a) by (simpl in Hkey; exact Hkey).
           assert (Hw1p: wfe ((T1 &= cc) +++ p3)) by (rewrite (ord_inert Ho3); exact Hw1).
           rewrite <- mcon_cons in *. cbn [mshift].
           assert (Hw2a: wfe ((T2 &= dd) +++ p4a)) by (eapply wfe_inv; exact Hw2).
           forwards Hr: (IHn p3 p4a T1 T2 cc dd);
             [ simpl in Hsz; lia | exact Ht
             | exact Hkey2 | exact Hw1p | exact Hw2a |].
           rewrite (ord_inert Ho3) in Hr. rewrite (mshift_ord _ Ho3) in Hr.
           eapply adde_teq_r; [ exact Hr |]. unfold wft. eapply wfe_evar_eteq; exact Hw2.
        ** rewrite keyLen_teq2 in Hkey. lia.
      * rewrite keyLen_st2 in Hkey. lia.
  - destruct Hd3 as [(p3a&m3&A3&?)|(p3a&?)]; subst.
    + destruct m3.
      * (* left & value *)
        assert (Hkey2: keyLen p3a = keyLen p4) by (simpl in Hkey; exact Hkey).
        rewrite <- mcon_cons in *. cbn [mshift].
        assert (Hw1a: wfe ((T1 &= cc) +++ p3a)) by (eapply wfe_inv; exact Hw1).
        forwards Hr: (IHn p3a p4 T1 T2 cc dd);
          [ simpl in Hsz; lia | exact Ht
          | exact Hkey2 | exact Hw1a | exact Hw2 |].
        eapply adde_teq_l; [ exact Hr |]. unfold wft. eapply wfe_evar_eteq; exact Hw1.
      * (* LEFT &= key (A3) : strip right & values then pair *)
        rewrite keyLen_teq2 in Hkey.
        forwards~ [Ho4|Hd4]: ord_dec p4.
        { forwards Hk4: ord_keyLen_0 Ho4. lia. }
        destruct Hd4 as [(p4a&m4&A4&?)|(p4a&?)]; subst.
        ** destruct m4.
           *** (* right & value : peel right one-sided *)
               assert (Hkey2: keyLen (and p3a rt A3) = keyLen p4a) by (simpl in Hkey |- *; lia).
               rewrite <- (mcon_cons (T2 &= dd) p4a) in *. cbn [mshift].
               assert (Hw2a: wfe ((T2 &= dd) +++ p4a)) by (eapply wfe_inv; exact Hw2).
               forwards Hr: (IHn (and p3a rt A3) p4a T1 T2 cc dd);
                 [ simpl in Hsz; lia | exact Ht
                 | exact Hkey2 | exact Hw1 | exact Hw2a |].
               eapply adde_teq_r; [ exact Hr |]. unfold wft. eapply wfe_evar_eteq; exact Hw2.
           *** (* right &= key : pair &= / &= via isb_here_ee *)
               rewrite <- (mcon_cons (T1 &= cc) p3a) in *.
               rewrite <- (mcon_cons (T2 &= dd) p4a) in *. cbn [mshift].
               assert (Hw1a: wfe ((T1 &= cc) +++ p3a)) by (eapply wfe_inv; exact Hw1).
               assert (Hw2a: wfe ((T2 &= dd) +++ p4a)) by (eapply wfe_inv; exact Hw2).
               assert (Hkey2: keyLen p3a = keyLen p4a) by (simpl in Hkey; lia).
               forwards Hr: (IHn p3a p4a T1 T2 cc dd);
                 [ simpl in Hsz; lia | exact Ht | exact Hkey2 | exact Hw1a | exact Hw2a |].
               eapply shift_insb; [ exact Hr | eapply isb_here_ee; [ exact Hw1 | exact Hw2 ] | exact Hw1 | exact Hw2 ].
        ** (* right &s key : pair &= / &s via isb_here_es *)
           rewrite <- (mcon_cons (T1 &= cc) p3a) in *.
           rewrite <- (mcon_cons_st (T2 &= dd) p4a) in *. cbn [mshift].
           assert (Hw1a: wfe ((T1 &= cc) +++ p3a)) by (eapply wfe_inv; exact Hw1).
           assert (Hw2a: wfe ((T2 &= dd) +++ p4a)) by (eapply wfe_sinv; exact Hw2).
           assert (Hkey2: keyLen p3a = keyLen p4a) by (simpl in Hkey; lia).
           forwards Hr: (IHn p3a p4a T1 T2 cc dd);
             [ simpl in Hsz; lia | exact Ht | exact Hkey2 | exact Hw1a | exact Hw2a |].
           eapply shift_insb; [ exact Hr | eapply isb_here_es; exact Hw1 | exact Hw1 | exact Hw2 ].
    + (* LEFT &s key : strip right & values then pair *)
      rewrite keyLen_st2 in Hkey.
      forwards~ [Ho4|Hd4]: ord_dec p4.
      { forwards Hk4: ord_keyLen_0 Ho4. lia. }
      destruct Hd4 as [(p4a&m4&A4&?)|(p4a&?)]; subst.
      ** destruct m4.
         *** (* right & value : peel right one-sided *)
             assert (Hkey2: keyLen (p3a &s) = keyLen p4a) by (simpl in Hkey |- *; lia).
             rewrite <- (mcon_cons (T2 &= dd) p4a) in *. cbn [mshift].
             assert (Hw2a: wfe ((T2 &= dd) +++ p4a)) by (eapply wfe_inv; exact Hw2).
             forwards Hr: (IHn (p3a &s) p4a T1 T2 cc dd);
               [ simpl in Hsz; lia | exact Ht
               | exact Hkey2 | exact Hw1 | exact Hw2a |].
             eapply adde_teq_r; [ exact Hr |]. unfold wft. eapply wfe_evar_eteq; exact Hw2.
         *** (* right &= key : pair &s / &= via isb_here_se *)
             rewrite <- (mcon_cons_st (T1 &= cc) p3a) in *.
             rewrite <- (mcon_cons (T2 &= dd) p4a) in *. cbn [mshift].
             assert (Hw1a: wfe ((T1 &= cc) +++ p3a)) by (eapply wfe_sinv; exact Hw1).
             assert (Hw2a: wfe ((T2 &= dd) +++ p4a)) by (eapply wfe_inv; exact Hw2).
             assert (Hkey2: keyLen p3a = keyLen p4a) by (simpl in Hkey; lia).
             forwards Hr: (IHn p3a p4a T1 T2 cc dd);
               [ simpl in Hsz; lia | exact Ht | exact Hkey2 | exact Hw1a | exact Hw2a |].
             eapply shift_insb; [ exact Hr | eapply isb_here_se; exact Hw2 | exact Hw1 | exact Hw2 ].
      ** (* right &s key : pair &s / &s via isb_here_ss *)
         rewrite <- (mcon_cons_st (T1 &= cc) p3a) in *.
         rewrite <- (mcon_cons_st (T2 &= dd) p4a) in *. cbn [mshift].
         assert (Hw1a: wfe ((T1 &= cc) +++ p3a)) by (eapply wfe_sinv; exact Hw1).
         assert (Hw2a: wfe ((T2 &= dd) +++ p4a)) by (eapply wfe_sinv; exact Hw2).
         assert (Hkey2: keyLen p3a = keyLen p4a) by (simpl in Hkey; lia).
         forwards Hr: (IHn p3a p4a T1 T2 cc dd);
           [ simpl in Hsz; lia | exact Ht | exact Hkey2 | exact Hw1a | exact Hw2a |].
         eapply shift_insb; [ exact Hr | eapply isb_here_ss | exact Hw1 | exact Hw2 ].
Qed.

Lemma coh_weaken: forall p3 p4 T1 T2 cc dd,
  teq T1 cc dd T2 ->
  keyLen p3 = keyLen p4 ->
  wfe ((T1 &= cc) +++ p3) -> wfe ((T2 &= dd) +++ p4) ->
  teq ((T1 &= cc) +++ p3) (mshift p3 (tshift 0 cc)) (mshift p4 (tshift 0 dd)) ((T2 &= dd) +++ p4).
Proof.
  intros. eapply coh_weaken_n; eauto.
Qed.

(* a check position in the BASE, lifted under the prefix p (index += keyLen p) *)
Lemma check_under: forall p, lshape p -> forall G V,
  check G V -> check (G +++ p) (keyLen p + V).
Proof.
  introv Hl. inductions Hl; introv Hc.
  - simpl. exact Hc.
  - rewrite <- mcon_cons. destruct m; simpl.
    + eapply check_evar. eapply IHHl; exact Hc.
    + eapply check_eteq. eapply IHHl; exact Hc.
  - rewrite <- mcon_cons_st. simpl. eapply check_etvar. eapply IHHl; exact Hc.
Qed.

(* reverse of check_under: a check position in the base, read off the lifted index *)
Lemma check_under_rev: forall p, lshape p -> forall G V,
  check (G +++ p) (keyLen p + V) -> check G V.
Proof.
  introv Hl. inductions Hl; introv Hc.
  - simpl in Hc. exact Hc.
  - rewrite <- mcon_cons in Hc. destruct m; simpl in Hc.
    + inverts Hc as Hc. eapply IHHl; exact Hc.
    + replace (S (keyLen T) + V) with (S (keyLen T + V)) in Hc by lia.
      inverts Hc as Hc. eapply IHHl; exact Hc.
  - rewrite <- mcon_cons_st in Hc.
    replace (S (keyLen T) + V) with (S (keyLen T + V)) in Hc by lia.
    inverts Hc as Hc. eapply IHHl; exact Hc.
Qed.

(* reverse base-lookt: a lookt position in the base (existence suffices) *)
Lemma lookt_under_rev: forall p, lshape p -> forall G V C,
  lookt (G +++ p) (keyLen p + V) C -> exists C', lookt G V C'.
Proof.
  introv Hl. inductions Hl; introv Hc.
  - simpl in Hc. exists C. exact Hc.
  - rewrite <- mcon_cons in Hc. destruct m; simpl in Hc.
    + inverts Hc as Hc. eapply IHHl; exact Hc.
    + replace (S (keyLen T) + V) with (S (keyLen T + V)) in Hc by lia.
      inverts Hc as Hc. eapply IHHl; exact Hc.
  - rewrite <- mcon_cons_st in Hc.
    replace (S (keyLen T) + V) with (S (keyLen T + V)) in Hc by lia.
    inverts Hc as Hc. eapply IHHl; exact Hc.
Qed.

(* The buried base star, after instantiation by &= cc, resolves by lookt to the
   cc value lifted through the prefix p (mshift p (tshift 0 cc)), at key position
   keyLen p.  POSITIONAL: proved directly by induction on the spine shape, replacing
   the old inner_base_star + lookt_inst_star + not_inner_keyLen detour. *)
Lemma lookt_inst_base_star: forall p, lshape p -> forall T cc,
  lookt ((T &= cc) +++ p) (keyLen p) (mshift p (tshift 0 cc)).
Proof.
  introv Hl. inductions Hl; introv.
  - simpl. eapply lookt_zero.
  - rewrite <- mcon_cons. destruct m; simpl.
    + eapply lookt_evar. eapply IHHl.
    + eapply lookt_eteq. eapply IHHl.
  - rewrite <- mcon_cons_st. simpl. eapply lookt_etvar. eapply IHHl.
Qed.

(* POSITIONAL instantiation of a paired var.  V is the SAME on both sides (positional
   eq_tvar).  Either V is the buried base star (resolves to cc/dd via lookt, closed by
   coh_weaken), or V is another key position preserved by &s->&= (keyLen-preserving). *)
Lemma inst_tvar: forall p3 p4 T1 T2 V cc dd,
  lshape p3 -> lshape p4 ->
  check ((T1 &s) +++ p3) V -> check ((T2 &s) +++ p4) V ->
  keyLen p3 = keyLen p4 -> teq T1 cc dd T2 ->
  wfe ((T1 &= cc) +++ p3) -> wfe ((T2 &= dd) +++ p4) ->
  teq ((T1 &= cc) +++ p3) (tvar V) (tvar V) ((T2 &= dd) +++ p4).
Proof.
  introv Hl3 Hl4 Hc1 Hc2 Hkey hcd Hwfe1 Hwfe2.
  forwards [Hlt|(V'&Hve&Hcv)]: check_app_dec Hl3 Hc1.
  - (* V < keyLen p3 : pure prefix position, preserved on both sides *)
    eapply eq_tvar; [ exact Hwfe1 | exact Hwfe2 | | ].
    + eapply check_below; [ exact Hl3 | exact Hc1 | exact Hlt ].
    + eapply check_below; [ exact Hl4 | exact Hc2 | rewrite <- Hkey; exact Hlt ].
  - (* V = keyLen p3 + V' with check (T1&s) V' *)
    subst V.
    forwards [Hlt2|(V2&Hve2&Hcv2)]: check_app_dec Hl4 Hc2.
    { rewrite <- Hkey in Hlt2. lia. }
    rewrite <- Hkey in Hve2.
    assert (HV: V' = V2) by lia. subst V2.
    destruct V' as [|V''].
    + (* base star : lookt resolves to cc/dd, coh_weaken *)
      forwards HlX: lookt_inst_base_star Hl3 T1 cc.
      forwards HlY: lookt_inst_base_star Hl4 T2 dd.
      rewrite Nat.add_0_r. rewrite <- Hkey in HlY.
      eapply eq_eql; [ exact HlX |].
      eapply eq_eqr; [ exact HlY |].
      eapply coh_weaken; eauto.
    + (* V' = S V'' : check T1 V'', check T2 V'' ; &s->&= preserves check at S V'' *)
      inverts Hcv. inverts Hcv2.
      eapply eq_tvar; [ exact Hwfe1 | exact Hwfe2 | | ].
      * eapply check_under; [ exact Hl3 | eapply check_eteq; eauto ].
      * rewrite Hkey. eapply check_under; [ exact Hl4 | eapply check_eteq; eauto ].
Qed.
(* main two-sided instantiation: replace the paired buried stars with C (left)
   and D (right); at eq_tvar, a var hitting the instantiated star resolves to
   C / D and coherence `teq T1 C D T2` (weakened) closes it. *)

Lemma inst_teq_gen: forall T3 T4 T1 A B T2,
  teq ((T1 &s) +++ T3) A B ((T2 &s) +++ T4) ->
  lshape T3 -> lshape T4 ->
  keyLen T3 = keyLen T4 -> forall C D,
  teq T1 C D T2 ->
  teq ((T1 &= C) +++ T3) A B ((T2 &= D) +++ T4).
Proof.
  intros T3 T4 T1 A B T2 H.
  remember (T1 &s +++ T3) as G1 eqn:E1.
  remember (T2 &s +++ T4) as G2 eqn:E2.
  revert T3 T4 E1 E2.
  induction H; intros p3 p4 he1 he2 Hl3 Hl4 hkey cc dd hcd; subst;
    try solve [ eapply eq_int; eapply inst_wfe; eauto using teq_wft_left, teq_wft_right
              | eapply eq_top; eapply inst_wfe; eauto using teq_wft_left, teq_wft_right
              | eapply eq_arr; [eapply IHteq1 | eapply IHteq2]; eauto
              | eapply eq_rcd; eapply IHteq; eauto ].
  - eapply inst_tvar; eauto using inst_wfe, teq_wft_left, teq_wft_right.
  - eapply eq_eql; [ eapply lookt_inst; [ eapply teq_wfe_left; exact H0 | eapply teq_wft_left; exact hcd | exact H ] | eapply IHteq; eauto ].
  - eapply eq_eqr; [ eapply lookt_inst; [ eapply teq_wfe_right; exact H0 | eapply teq_wft_right; exact hcd | exact H ] | eapply IHteq; eauto ].
  - (* eq_boxl *)
    assert (Hwd: wft T2 dd) by (eapply teq_wft_right; eauto).
    assert (Hwf2: wfe (T2 &= dd +++ p4)) by (eapply inst_wfe; [ eapply teq_wfe_right; eauto | exact Hwd ]).
    forwards Hrg: wft_box_rigid H0.
    forwards (Hbd & Hwfg & _): boxt_wft_inv H0.
    forwards Hb: dead_star_r H Hl4 Hrg Hwd Hwf2.
    eapply eq_boxl; [ exact Hb
      | unfold wft; eapply we_box; [ exact Hbd | exact Hrg
        | eapply inst_wfe; [ exact Hwfg | eapply teq_wft_left; exact hcd ] ] ].
  - (* eq_boxr *)
    assert (Hwc: wft T1 cc) by (eapply teq_wft_left; eauto).
    assert (Hwf1: wfe (T1 &= cc +++ p3)) by (eapply inst_wfe; [ eapply teq_wfe_left; eauto | exact Hwc ]).
    forwards Hrg: wft_box_rigid H0.
    forwards (Hbd & Hwfg & _): boxt_wft_inv H0.
    forwards Hb: dead_star_l H Hl3 Hrg Hwc Hwf1.
    eapply eq_boxr; [ exact Hb
      | unfold wft; eapply we_box; [ exact Hbd | exact Hrg
        | eapply inst_wfe; [ exact Hwfg | eapply teq_wft_right; exact hcd ] ] ].
  - eapply eq_all; rewrite !mcon_cons_st;
      eapply IHteq; [ apply mcon_cons_st | apply mcon_cons_st
        | eapply lsh_ands; exact Hl3 | eapply lsh_ands; exact Hl4 | simpl; lia | exact hcd ].
  - eapply eq_manil; rewrite (mcon_cons (T1 &= cc) p3); rewrite (mcon_cons_st (T2 &= dd) p4);
      eapply IHteq; [ apply mcon_cons | apply mcon_cons_st
        | eapply lsh_evar; exact Hl3 | eapply lsh_ands; exact Hl4 | simpl; lia | exact hcd ].
  - eapply eq_manir; rewrite (mcon_cons (T2 &= dd) p4); rewrite (mcon_cons_st (T1 &= cc) p3);
      eapply IHteq; [ apply mcon_cons_st | apply mcon_cons
        | eapply lsh_ands; exact Hl3 | eapply lsh_evar; exact Hl4 | simpl; lia | exact hcd ].
  - assert (HsK: keyLen T4 = keyLen T5) by (eapply teq_spine_keyLen; eauto).
    eapply eq_and; [ eapply IHteq1; eauto | exact H0 | exact H1 | ].
    rewrite !mapp_ass.
    eapply IHteq2; [ apply mapp_ass | apply mapp_ass
      | eapply mcon_lshape; eauto | eapply mcon_lshape; eauto
      | rewrite !keyLen_app; lia | exact hcd ].
  - eapply eq_ands; [ eapply IHteq; eauto | exact H0 | exact H1 ].
Qed.

Lemma inst_teq: forall T1 T2 A B,
  teq (T1 &s) A B (T2 &s) -> forall C D,
  teq T1 C D T2 ->
  teq (T1 &= C) A B (T2 &= D).
Proof.
  introv H Hcd.
  assert (Hr: teq ((T1 &= C) +++ top) A B ((T2 &= D) +++ top)).
  { eapply inst_teq_gen;
      [ simpl; exact H | eapply lsh_nil | eapply lsh_nil | reflexivity | exact Hcd ]. }
  simpl in Hr. exact Hr.
Qed.
