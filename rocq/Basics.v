
Require Import LibTactics.
Require Import Arith.
Require Import Lia.
From Coq Require Import Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.EquivDec.


Inductive typ :=
  | int : typ
  | top : typ
  | arr : typ -> typ -> typ
  | and : typ -> typ -> typ
  | rcd : string -> typ -> typ.

Inductive op := app | box | mrg.

Inductive exp :=
  | ctx : exp
  | lit : nat -> exp
  | unit : exp
  | binop : op -> exp -> exp -> exp 
  | lam : typ -> exp -> exp
  | proj: exp -> nat -> exp
  | clos: exp -> typ -> exp -> exp
  | rec : string -> exp -> exp
  | rproj : exp -> string -> exp.

Inductive lookup : typ -> nat -> typ -> Prop :=
  | lzero : forall A B, 
      lookup (and A B) 0 B
  | lsucc : forall A B n C, 
      lookup A n C -> 
      lookup (and A B) (S n) C.

Inductive value : exp -> Prop :=
  | vint : forall n, value (lit n)
  | vunit : value unit
  | vclos : forall v A e, value v -> value (clos v A e)
  | vrcd : forall l v, value v -> value (rec l v)
  | vmrg : forall v1 v2, value v1 -> value v2 -> value (binop mrg v1 v2).

Inductive lin: string -> typ -> Prop :=
  | lin_rcd: forall A l, lin l (rcd l A)
  | lin_andl: forall A B l,
      lin l A ->
      lin l (and A B)
  | lin_andr: forall A B l,
     lin l B ->
     lin l (and A B).

Inductive rlookup : typ -> string -> typ -> Prop :=
  | rlzero : forall l B, 
      rlookup (rcd l B) l B
  | landl : forall A B C l, 
      rlookup A l C ->
      ~ lin l B ->
      rlookup (and A B) l C
  | landr : forall A B C l, 
      rlookup B l C ->
      ~ lin l A ->
      rlookup (and A B) l C.

Inductive has_type : typ -> exp -> typ -> Prop :=
  | tctx: forall E, has_type E ctx E
  | tint : forall E i, has_type E (lit i) int
  | tunit : forall E, has_type E unit top
  | tapp : forall E A B e1 e2,
      has_type E e1 (arr A B) -> has_type E e2 A -> has_type E (binop app e1 e2) B
  | tbox : forall E A E1 e1 e2,
      has_type E e1 E1 -> has_type E1 e2 A -> has_type E (binop box e1 e2) A
  | tmrg : forall E e1 e2 A B,
      has_type E e1 A -> has_type (and E A) e2 B -> has_type E (binop mrg e1 e2) (and A B)
  | tlam : forall E A e B,
      has_type (and E A) e B -> has_type E (lam A e) (arr A B)
  | tproj: forall E A e B n,
      has_type E e A ->
      lookup A n B ->
      has_type E (proj e n) B
  | tclos : forall E E1 A e ev B, 
      value ev ->
      has_type top ev E1 -> 
      has_type (and E1 A) e B -> 
      has_type E (clos ev A e) (arr A B)
  | trcd : forall E e A l,
      has_type E e A ->
      has_type E (rec l e) (rcd l A)
  | trproj : forall E e B l A,
      has_type E e B ->
      rlookup B l A ->
      has_type E (rproj e l) A.
  
Inductive lookupv : exp -> nat -> exp -> Prop :=
  | lvzero : forall v1 v2, 
      lookupv (binop mrg v1 v2) 0 v2
  | lvsucc : forall v1 v2 n v3, 
      lookupv v1 n v3 -> 
      lookupv (binop mrg v1 v2) (S n) v3.

Inductive rlookupv : exp -> string -> exp -> Prop :=
  | rvlzero : forall l e, 
      rlookupv (rec l e) l e
  | vlandl : forall e1 e2 e l, 
      rlookupv e1 l e ->
      rlookupv (binop mrg e1 e2) l e
  | vlandr : forall e1 e2 e l, 
      rlookupv e2 l e ->
      rlookupv (binop mrg e1 e2) l e.

Inductive step : exp -> exp -> exp -> Prop :=
  | sctx: forall v,
      value v ->
      step v ctx v
  | sbl : forall v e1 e2 e1' o,
      value v -> 
      step v e1 e1' -> 
      step v (binop o e1 e2) (binop o e1' e2)
  | sbapp : forall v v1 e2 e2', 
      value v -> 
      value v1 -> 
      step v e2 e2' -> 
      step v (binop app v1 e2) (binop app v1 e2')
  | sbbox : forall v v1 e2 e2', 
      value v -> 
      value v1 -> 
      step v1 e2 e2' -> 
      step v (binop box v1 e2) (binop box v1 e2')
  | sbmrg : forall v v1 e' e,
      value v -> 
      value v1 -> 
      step (binop mrg v v1) e e' -> 
      step v (binop mrg v1 e) (binop mrg v1 e')
  | sclos : forall v A e, 
      value v -> 
      step v (lam A e) (clos v A e)
  | sbeta : forall v v1 v2 A e, value v -> value v1 -> value v2 -> 
      step v (binop app (clos v2 A e) v1) (binop box (binop mrg v2 v1) e)
  | sboxv : forall v v1 v2,
      value v -> 
      value v1 -> 
      value v2 -> 
      step v (binop box v1 v2) v2
  | sproj: forall v e1 e2 n,
      value v ->
      step v e1 e2 ->
      step v (proj e1 n) (proj e2 n)
  | sprojv : forall v n v1 v2, 
      value v ->
      value v1 ->
      lookupv v1 n v2 ->
      step v (proj v1 n) v2
  | srec: forall v e1 e2 l,
      value v ->
      step v e1 e2 ->
      step v (rec l e1) (rec l e2)
  | srproj: forall v e1 e2 l,
      value v ->
      step v e1 e2 ->
      step v (rproj e1 l) (rproj e2 l)
  | srprojv : forall v l v1 v2, 
      value v ->
      value v1 ->
      rlookupv v1 l v2 ->
      step v (rproj v1 l) v2.

#[export]
Hint Constructors typ op exp lookup lookupv lin rlookup has_type value rlookupv step : core.


Require Import Program.Equality.


(* ---------------------------------------------------- *)
(* Type soundness *)
Lemma value_weaken : forall E v A, 
  has_type E v A -> forall E', 
  value v -> 
  has_type E' v A.
Proof.
  introv Ht. inductions Ht; introv Hv;
  try solve [eauto];
  try solve [inverts* Hv].
Qed.

Lemma lookupv_value: forall v n v', 
  lookupv v n v' -> 
  value v -> 
  value v'.
Proof.
  introv Hl. inductions Hl; introv Hv; inverts* Hv.
Qed.

Lemma lookup_pres_ctx: forall E n A,
  lookup E n A -> forall v v',
  lookupv v n v' -> 
  value v ->
  has_type top v E ->
  has_type E v' A.
Proof.
  introv Hl. inductions Hl; introv Hlv Hv Ht.
  - inverts* Hlv. inverts* Ht. inverts Hv.
    eapply value_weaken; eauto.
  - inverts* Hlv. inverts* Ht. inverts Hv.
    forwards~: IHHl H1 H2.
    eapply value_weaken; eauto.
    eapply lookupv_value; eauto.
Qed.

Lemma lookup_pres: forall E n A,
  lookup E n A -> forall v v',
  lookupv v n v' -> 
  value v ->
  has_type top v E ->
  has_type top v' A.
Proof.
  introv Hl Hlv Hv Ht.
  forwards~: lookup_pres_ctx Hl Hlv Hv Ht.
  eapply value_weaken; eauto.
  eapply lookupv_value; eauto. 
Qed.


Lemma rlookupv_value: forall v l v', 
  rlookupv v l v' -> 
  value v -> 
  value v'.
Proof.
  introv Hl. inductions Hl; introv Hv; inverts* Hv.
Qed.


Lemma rcd_shape: forall E v l B, 
  has_type E v (rcd l B) -> 
  value v -> exists v',
  v = rec l v'.
Proof.
  introv Ht. inductions Ht; introv Hv;
  try solve [inverts* Hv].
Qed. 

Lemma notin_false: forall E v A,
  has_type E v A -> forall l v',
  rlookupv v l v' ->
  ~ lin l A ->
  False.
Proof.
  introv Ht. inductions Ht; introv Hr Hnl;
  try solve [inverts* Hr].
Qed.

Lemma rlookup_pres_aux: forall E l A,
  rlookup E l A -> forall v v',
  rlookupv v l v' -> 
  value v ->
  has_type top v E ->
  has_type E v' A.
Proof.
  introv Hl. inductions Hl; introv Hlv Hv Ht.
  - inverts* Ht; try solve [inverts Hv].
    inverts Hlv. inverts Hv.
    eapply value_weaken; eauto.
  - inverts* Hlv; try solve [inverts* Ht]. 
    + inverts Ht. inverts Hv.
      forwards~: IHHl H0 H5. 
      eapply value_weaken; eauto.
      eapply rlookupv_value; eauto.
    + inverts Ht. inverts Hv. 
      exfalso. eapply notin_false; eauto.
  - inverts* Hlv; try solve [inverts* Ht]. 
    + inverts Ht. inverts Hv. 
      exfalso. eapply notin_false; try eapply H; eauto.
    + inverts Ht. inverts Hv.
      forwards~: IHHl H0. 
      eapply value_weaken; eauto.
      eapply value_weaken; eauto.
      eapply rlookupv_value; eauto.
Qed. 

Lemma rlookup_pres: forall E l A,
  rlookup E l A -> forall v v',
  rlookupv v l v' -> 
  value v ->
  has_type top v E ->
  has_type top v' A.
Proof.
  introv Hl Hlv Hv Ht.
  forwards~: rlookup_pres_aux Hl Hlv Hv Ht.
  eapply value_weaken; eauto.
  eapply rlookupv_value; eauto.
Qed.


Lemma gpreservation : forall e e' v, 
  step v e e' -> forall E A, 
  has_type E e A -> 
  has_type top v E -> 
  has_type E e' A.
Proof.
  introv Hs. inductions Hs; introv Ht Htv; 
  try solve [eauto];
  try solve [inverts* Ht].
  - inverts* Ht.
    eapply value_weaken; eauto.
  - inverts* Ht.
    econstructor; eauto.
    eapply IHHs; eauto.
    eapply value_weaken; eauto.
  - inverts* Ht.
    econstructor; eauto.
    eapply IHHs; eauto.
    econstructor; eauto.
    eapply value_weaken; eauto.
  - inverts* Ht. inverts H5.
    econstructor; eauto.
    econstructor.
    eapply value_weaken; eauto.
    eapply value_weaken; eauto.
  - inverts* Ht.
    eapply value_weaken; eauto.
  - inverts* Ht.
    forwards~: lookup_pres H7 H1.
    eapply value_weaken; eauto.
    eapply value_weaken; eauto.
    eapply lookupv_value; eauto.
  - inverts* Ht.
    forwards~: rlookup_pres H7 H1.
    eapply value_weaken; eauto.
    eapply value_weaken; eauto.
    eapply rlookupv_value; eauto.
Qed.

    
Lemma lookup_prog: forall n A B,
  lookup A n B -> forall v,
  has_type top v A ->
  value v ->
  exists e', lookupv v n e'.
Proof.
  introv Hl. inductions Hl; introv Ht Hv.
  - inverts* Ht; try solve [inverts* Hv].
  - inverts* Ht; try solve [inverts* Hv].
    + inverts* Hv. 
      forwards~ (e'&Hs): IHHl H3.
      inverts* Hs.
Qed.

Lemma rlookup_prog: forall n A B,
  rlookup A n B -> forall v,
  has_type top v A ->
  value v ->
  exists e', rlookupv v n e'.
Proof.
  introv Hl. inductions Hl; introv Ht Hv.
  - inverts* Ht; try solve [inverts* Hv].
  - inverts* Ht; try solve [inverts* Hv].
    inverts Hv.
    forwards~ (?&?): IHHl H4.
    exists* x.
  - inverts* Ht; try solve [inverts* Hv].
    inverts Hv.
    forwards~ (?&?): IHHl e2.
    eapply value_weaken; eauto.
    exists* x.
Qed.


Lemma gprogress : forall E e A, 
  has_type E e A -> forall v, 
  value v -> 
  has_type top v E -> 
  value e \/ exists e', step v e e'.
Proof.
  introv Ht.
  inductions Ht; introv Hv Htv; eauto.
  - right. 
    forwards~: IHHt1 Htv.
    forwards~: IHHt2 Htv.
    destruct* H; destruct* H0.
    + inverts* Ht1; inverts* H.
  - forwards~: IHHt1 Htv.
    destruct H.
    + forwards~: IHHt2 H.
      eapply value_weaken; eauto.
      destruct* H0.
    + inverts* H.
  - forwards~: IHHt1 Htv.
    destruct H.
    + forwards~: IHHt2 (binop mrg v e1).
      econstructor; eauto.
      eapply value_weaken; eauto.
      destruct* H0.
    + inverts* H.
  - right.
    forwards~: IHHt Hv.
    inverts H0.
    + forwards~: value_weaken Ht top.
      forwards~ (?&?): lookup_prog H H0.
      exists* x.
    + inverts* H1.
  - forwards~: IHHt Hv Htv. destruct* H.
  - right.
    forwards~: IHHt Hv.
    inverts H0.
    + forwards~: value_weaken Ht top.
      forwards~ (?&?): rlookup_prog H H0.
      exists* x. 
    + inverts* H1.
Qed.

Lemma preservation : forall e e' A, has_type top e A -> step unit e e' -> has_type top e' A.
  intros.
  eapply gpreservation; eauto.
Defined.
      
Lemma progress :  forall e A, has_type top e A -> value e \/ exists e', step unit e e'.
  intros.
  eapply gprogress; eauto.
Defined.


(* ---------------------------------------------------- *)
(* Determinism *)
Lemma step_value : forall e, 
  value e -> forall v e', 
  step v e e' -> 
  False.
Proof.
  induction 1; intros v' e' st; dependent destruction st; eauto.
Qed.

Ltac solve_value_step :=
  match goal with
    | [ Hv : value ?v, H : step _ ?v _ |- _ ] => 
          exfalso; forwards~: step_value Hv H
    | [ Hv : value ?v, H : step _ (clos ?v _ _) _ |- _ ] => 
          exfalso; eapply step_value; try eapply H; eauto 
  end. 

Lemma lookupv_det: forall v n v1,
  lookupv v n v1 -> forall v2,
  lookupv v n v2 ->
  v1 = v2.
Proof.
  introv Hl. inductions Hl; introv Hl2; inverts* Hl2.
Qed.

Inductive mstep : exp -> exp -> exp -> Prop :=
  | mstep_base : forall v e, value v -> mstep v e e
  | mstep_step : forall v e e' e'', step v e e' -> mstep v e' e'' -> mstep v e e''.

#[export]
Hint Constructors mstep: core.


Lemma rlookupv_det: forall v E B,
  has_type E v B ->
  value v -> forall l A,
  rlookup B l A -> forall v1,
  rlookupv v l v1 -> forall v2,
  rlookupv v l v2 ->
  v1 = v2.
Proof.
  introv Ht. inductions Ht; introv Hv Hr Hl1 Hl2;
  try solve [inverts Hl1].
  - inverts Hv. inverts Hr. 
    + inverts Hl1; inverts Hl2.
      * eapply IHHt1; eauto.
      * exfalso. eapply notin_false; eauto.
      * exfalso. eapply notin_false; eauto.
      * exfalso. eapply notin_false; eauto.
    + inverts Hl1; inverts Hl2.
      * exfalso. eapply notin_false; try eapply H6; eauto.
      * exfalso. eapply notin_false; try eapply H6; eauto.
      * exfalso. eapply notin_false; try eapply H6; eauto.
      * eapply IHHt2; eauto.
  - inverts Hl1. inverts Hl2. eauto. 
Qed. 

Lemma sel_det: forall v l E A,
  has_type E (rproj v l) A ->
  value v -> forall v1,
  rlookupv v l v1 -> forall v2,
  rlookupv v l v2 ->
  v1 = v2.
Proof.
  introv Hs. inverts Hs; intros.
  eapply rlookupv_det; eauto.
Qed.


Lemma gen_step_unique: forall e A G, 
  has_type G e A -> forall v e1 e2, 
  has_type top v G -> 
  step v e e1 ->
  step v e e2 -> 
  e1 = e2.
Proof.
  intros e A G H.
  inductions H; introv Typv Red1 Red2;
  try solve [inverts Red1].
  - inverts* Red1. inverts* Red2.
  - inverts Red1; inverts Red2; 
    try solve_value_step.
    + forwards~: IHhas_type1 H7 H9. subst. eauto.
    + forwards~: IHhas_type2 H7 H10. subst. eauto.
    + eauto.
  - inverts Red1; inverts Red2; 
    try solve_value_step.
    + forwards~: IHhas_type1 H7 H9. subst. eauto.
    + forwards~: IHhas_type2 H7 H10. 
      eapply value_weaken; eauto.
      subst. eauto.
    + eauto.
  - inverts Red1; inverts Red2; 
    try solve_value_step.
    + forwards~: IHhas_type1 H7 H9. subst. eauto.
    + forwards~: IHhas_type2 H7 H10.
      econstructor; eauto. 
      eapply value_weaken; eauto.
      subst. eauto.
  - inverts Red1; inverts Red2. eauto.
  - inverts Red1; inverts Red2; 
    try solve_value_step.
    + forwards~: IHhas_type H6 H8. subst. eauto.
    + eapply lookupv_det; eauto.
  - inverts Red1; inverts Red2; 
    try solve_value_step.
    + forwards~: IHhas_type H5 H7. subst. eauto.
  - inverts Red1; inverts Red2; 
    try solve_value_step.
    + forwards~: IHhas_type H6 H8. subst. eauto.
    + eapply rlookupv_det; try eapply H7; eauto.
Qed.


Corollary step_unique: forall e A, 
  has_type top e A -> forall e1 e2, 
  step unit e e1 ->
  step unit e e2 -> 
  e1 = e2.
Proof.
  introv Ht Hs1 Hs2.
  forwards~: gen_step_unique Ht Hs1 Hs2.
Qed.



Lemma mstep_trans : forall v e1 e2, 
  mstep v e1 e2 -> forall e3, 
  mstep v e2 e3 -> 
  mstep v e1 e3.
  intros v e1 e2 ms.
  induction ms; intros e3 ms2; eauto.
Defined.


Lemma mstep_det: forall v e v1,
  mstep v e v1 -> forall v2,
  mstep v e v2 -> forall A G, 
  has_type G e A ->  
  has_type top v G -> 
  value v1 ->
  value v2 ->
  v1 = v2.
Proof.
  introv Hm. inductions Hm; introv Hm2 Ht Hs Hv1 Hv2.
  - inductions Hm2; eauto.
    exfalso. forwards~: step_value H0.
  - inverts Hm2; eauto.
    + exfalso. forwards~: step_value H.
    + forwards~: gen_step_unique Ht Hs H H0. subst.
      eapply IHHm; eauto.
      eapply gpreservation; eauto.
Qed.


(* ---------------------------------------------------- *)
(* Termination *)


Fixpoint sem_typ_val (e: exp) (A : typ) : Prop :=
  match A with
  | top => e = unit 
  | int => exists i, e = lit i 
  | and B1 B2 => exists v1 v2, e = binop mrg v1 v2 /\ sem_typ_val v1 B1 /\ sem_typ_val v2 B2
  | arr B1 B2 => exists v e', 
      value v /\ e = clos v B1 e' /\
        (forall v1, value v1 -> sem_typ_val v1 B1 -> exists v2,
                    (mstep unit (binop box (binop mrg v v1) e') v2) /\ sem_typ_val v2 B2) 
  | rcd l A => exists v, e = rec l v /\ sem_typ_val v A
  end.


Lemma stv_value : forall A e, sem_typ_val e A -> value e.
  induction A; simpl in *; intros; eauto.
  - destruct H; subst; eauto.
  - subst; eauto.
  - destruct H as (? & ? & ? & ? & ?); subst; eauto.
  - destruct H as (? & ? & ? & ? & ?); subst; eauto.
  - destruct H as (? & ? & ?); subst; eauto.
Defined.

Lemma sem_lookup_preservation : forall A n B, 
  lookup A n B -> forall v v',
  lookupv v n v' -> 
  value v -> 
  sem_typ_val v A -> 
  sem_typ_val v' B.
  intros A n B l.
  induction l; intros; eauto; dependent destruction H; dependent destruction H0; simpl in *; eauto.
  - destruct H1. destruct H. destruct H. destruct H0.
    injection H; intros; subst; eauto.
  - destruct H1. destruct H0. destruct H0. destruct H1.
    injection H0; intros; subst; eauto.    
Defined.


Lemma notin_false_sem: forall A v,
  sem_typ_val v A -> 
  value v -> forall l v',
  rlookupv v l v' ->
  ~ lin l A ->
  False.
Proof.
  intros A. inductions A; introv Hs Hv;
  try solve [inverts* Hv]; intros.
  - simpl in Hs. destruct* Hs. subst*. inverts* H. 
  - simpl in Hs. subst*. inverts* H.
  - simpl in Hs.
    destruct Hs. destruct H1.
    destruct H1. destruct H2. subst. inverts H.
  - simpl in Hs.
    destruct Hs. destruct H1.
    destruct H1. destruct H2. subst. inverts Hv. inverts* H.
  - simpl in Hs.
    destruct Hs. destruct H1. subst. inverts H. 
    eapply H0. eauto.
Qed.

Lemma sem_rlookup_preservation : forall A n B, 
  rlookup A n B -> forall v v',
  rlookupv v n v' -> 
  value v -> 
  sem_typ_val v A -> 
  sem_typ_val v' B.
Proof.
  introv Hl. inductions Hl; introv Hlv Hv Ht.
  - simpl in Ht. forwards~ (?&?&?): Ht.
    subst*. inverts* Hlv.
  - simpl in Ht. forwards~ (?&?&?&?&?): Ht.
    subst*. inverts* Hlv.
    + eapply IHHl; eauto.
      eapply stv_value; eauto.
    + exfalso. eapply notin_false_sem; eauto.
      eapply stv_value; eauto.
  - simpl in Ht. forwards~ (?&?&?&?&?): Ht.
  subst*. inverts* Hlv.
    + exfalso. eapply notin_false_sem; try eapply H; eauto.
    eapply stv_value; eauto.
    + eapply IHHl; eauto.
      eapply stv_value; eauto.
Defined.

Definition comp_env (o : op) (v v1 : exp) : exp :=
  match o with
  | mrg => binop mrg v v1
  | box => v1
  | _ => v 
  end.

Lemma mstep_value: forall v venv v',
  mstep venv v v' ->
  value v ->
  v = v'.
Proof.
  introv Hm. inductions Hm; introv Hv; eauto.
  exfalso. eapply step_value; eauto.
Qed.

Lemma weaken_box : forall v e1 e2 e, 
  value e1 -> 
  mstep v (binop box e1 e2) e -> forall v', 
  value v' -> 
  mstep v' (binop box e1 e2) e.
  intros.
  dependent induction H0; eauto.
  dependent destruction H1; eauto.
  apply step_value in H1; eauto. inversion H1.
  rewrite (mstep_value _ _ _ H2) in *; eauto.
Defined.

Lemma sound_lookup : forall A n B, 
  lookup A n B -> forall v, 
  sem_typ_val v A -> exists v', 
  lookupv v n v'.
  induction 1; simpl; intros v sv; eauto.
  - destruct sv as (? & ? & ? & ? & ?). subst; eauto.
  - destruct sv as (? & ? & ? & ? & ?). subst; eauto.
    apply IHlookup in H1. destruct H1. exists x1. eauto.
Defined.

Lemma mstep_split : forall v e1 v1, mstep v e1 v1 -> value v -> value v1 ->
                                     forall e2 e2' o, mstep (comp_env o v v1) e2 e2' -> mstep v (binop o e1 e2) (binop o v1 e2').
  intros v e1 v1 ms. induction ms; intros valv valv1 e2 e2' o ms2; eauto.
  dependent induction ms2; eauto.
  destruct o; simpl; eauto.
Defined.

Lemma step_env_value: forall v e1 e2,
  step v e1 e2 ->
  value v.
Proof.
  introv Hs. inductions Hs; eauto.
Qed.

Lemma mstep_env_value: forall v e1 e2,
  mstep v e1 e2 ->
  value v.
Proof.
  introv Hs. inductions Hs; eauto.
Qed.

Lemma step_is_mstep: forall v e1 e2,
  step v e1 e2 ->
  mstep v e1 e2.
Proof.
  introv Hs. econstructor; eauto.
  eapply mstep_base; eauto.
  eapply step_env_value; eauto.
Qed.

Lemma mstep_rec: forall v e1 e2 l,
  mstep v e1 e2 -> 
  mstep v (rec l e1) (rec l e2).
Proof.
  introv Hm.
  inductions Hm; eauto.
  eapply mstep_trans; eauto.
  eapply step_is_mstep; eauto.
  econstructor; eauto.
  eapply step_env_value; eauto.
Qed.

Lemma sound_rlookup : forall A n B, 
  rlookup A n B -> forall v, 
  sem_typ_val v A -> exists v', 
  rlookupv v n v'.
  induction 1; simpl; intros v sv; eauto.
  - destruct sv as (? & ? & ?). subst; eauto.
  - destruct sv as (? & ? & ? & ? & ?). subst; eauto.
    forwards~ (?&?): IHrlookup H2. exists*.
  - destruct sv as (? & ? & ? & ? & ?). subst; eauto.
    forwards~ (?&?): IHrlookup H3. exists*.
Defined.

Lemma mstep_rproj: forall v e1 e2 l,
  mstep v e1 e2 -> 
  mstep v (rproj e1 l) (rproj e2 l).
Proof.
  introv Hm.
  inductions Hm; eauto.
  eapply mstep_trans; eauto.
  eapply step_is_mstep; eauto.
  econstructor; eauto.
  eapply step_env_value; eauto.
Qed.

Lemma mstep_proj: forall v e1 e2 n,
  mstep v e1 e2 -> 
  mstep v (proj e1 n) (proj e2 n).
Proof.
  introv Hm.
  inductions Hm; eauto.
  eapply mstep_trans; eauto.
  eapply step_is_mstep; eauto.
  econstructor; eauto.
  eapply step_env_value; eauto.
Qed.

Definition sem_typ (E : typ) (e : exp) (A : typ) : Prop := forall venv,
  sem_typ_val venv E ->
  exists v, mstep venv e v /\ sem_typ_val v A.


Ltac pre_unfold :=
  unfold sem_typ; 
  introv msv; 
  match goal with
    | [ msv : _ |- _ ] => 
      try forwards~ Hv: stv_value msv
  end. 

Lemma sound_ctx: forall E,
  sem_typ E ctx E.
Proof.
  pre_unfold. exists* venv.
Qed.

Lemma sound_box: forall E e1 E1 e2 A,
  sem_typ E e1 E1 ->
  sem_typ E1 e2 A ->
  sem_typ E (binop box e1 e2) A.
Proof.
  introv IHht1 IHht2. pre_unfold.
  destruct (IHht1 _ msv) as (? & ? & ?).
  assert (value venv). eapply stv_value; eauto.
  assert (value x). eapply stv_value; eauto.
  unfold sem_typ in *.
  destruct (IHht2 _ H0) as (? & ? & ?); simpl.
  exists x0. split; eauto.
  assert (value x0). eapply stv_value; eauto.
  apply mstep_trans with (e2 := binop box x x0); eauto.
  apply mstep_split; eauto.
Qed.


Lemma sound_lam: forall E A e B,
  sem_typ (and E A) e B ->
  sem_typ E (lam A e) (arr A B).
Proof.
  introv IHht. pre_unfold.
  exists (clos venv A e). split; eauto.
  simpl. exists venv. exists e. split; eauto. split; eauto.
  intros.
  destruct (IHht (binop mrg venv v1)).
  simpl. exists venv. exists v1. repeat (split; eauto).
  destruct H1. exists x. split; eauto.
  assert (value x). eapply stv_value; eauto.
  apply mstep_trans with (e2 := binop box (binop mrg venv v1) x); eauto.
  apply mstep_split; eauto.
Qed.


Lemma soundness : forall e A E, 
  has_type E e A -> 
  sem_typ E e A.
Proof.
  introv ht. inductions ht.
  - eapply sound_ctx.
  - pre_unfold. 
    exists (lit i); split; unfold sem_typ_val; eauto.
  - pre_unfold.
    exists unit; split; unfold sem_typ_val; eauto.
  - pre_unfold. 
    destruct (IHht1 _ msv). destruct (IHht2 _ msv).
    destruct H0. destruct H.
    simpl in H2.
    destruct H2 as (? & ? & ? & ? & ?). subst.
    assert (value x0). eapply stv_value; eauto.
    edestruct H4 as (? & ? & ?); eauto.
    apply weaken_box with (v' := venv) in H5; eauto.    
    exists x. split; eauto.
    eapply mstep_trans; try (exact H5).
    eapply mstep_trans with (e2 := binop app (clos x1 A x2) x0); eauto.
    apply mstep_split; eauto.
  - eapply sound_box; eauto.
  - pre_unfold.
    destruct (IHht1 _ msv) as (? & ? & ?).
    unfold sem_typ in *.
    assert (value venv). eapply stv_value; eauto.
    assert (value x). eapply stv_value; eauto.
    destruct (IHht2 (binop mrg venv x)) as (? & ? & ?); simpl.
    exists venv. exists x. split; eauto.
    exists (binop mrg x x0). split; eauto.    
    apply mstep_split; eauto.
  - eapply sound_lam; eauto. 
  - pre_unfold.
    forwards~ (?&?&?): IHht msv.
    forwards~ (?&?): sound_lookup H H1.    
    forwards~: sem_lookup_preservation H H2 H1.
    eapply stv_value; eauto.
    exists* x0. split*.

    eapply mstep_trans.
    + eapply mstep_proj; eauto.
    + eapply step_is_mstep. econstructor; eauto.
      eapply stv_value; eauto.
  - pre_unfold.
    exists (clos ev A e). split; simpl; eauto.
    exists ev. exists e. split; eauto. split; eauto.
    intros.

    destruct (IHht1 unit); simpl; eauto. destruct H2.
    destruct (IHht2 (binop mrg ev v1)).
    forwards~: mstep_value H2. subst.
    simpl. exists x. exists v1. repeat (split; eauto).
    destruct H4. exists x0; split; eauto.
    assert (value x0). eapply stv_value; eauto.
    apply mstep_trans with (e2 := binop box (binop mrg ev v1) x0); eauto.
    apply mstep_split; eauto. 
  - pre_unfold.
    forwards~ (?&?&?): IHht msv. exists* (rec l x). split*.
    + eapply mstep_rec; eauto.
    + simpl. exists*.
  - pre_unfold.
    forwards~ (?&?&?): IHht msv.
    forwards~ (?&?): sound_rlookup H H1.    
    forwards~: sem_rlookup_preservation H H2 H1.
    eapply stv_value; eauto.
    exists* x0. split*.

    eapply mstep_trans.
    + eapply mstep_rproj; eauto.
    + eapply step_is_mstep. econstructor; eauto.
      eapply stv_value; eauto.
Qed.


Lemma termination : forall e A, has_type top e A -> exists v, value v /\ mstep unit e v.
Proof.
  intros.
  apply soundness with (E := top) in H; simpl; eauto.
  unfold sem_typ in H.
  forwards~ (?&?&?): H unit. exists x. split*.
  eapply stv_value; eauto.
Qed.