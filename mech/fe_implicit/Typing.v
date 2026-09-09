Require Import LibTactics.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
Require Import Stdlib.Lists.List.
Require Import Stdlib.Classes.EquivDec.
From Stdlib Require Import Strings.String.
Import ListNotations.
Require Export Teq ExpSyntax Semantics.
Set Implicit Arguments.




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


Inductive has_type : typ -> exp -> typ -> Prop :=
  | t_int : forall T i, 
      wfe T ->
      has_type T (lit i) int
  | t_var : forall T A n, 
      wfe T ->
      get_var T n A ->
      has_type T (var n) A
  | t_lam : forall T A e B,
      has_type (T & A) e B -> 
      has_type T (lam e) (arr A B)
  | t_app : forall T A B e1 e2,
      has_type T e1 (arr A B) -> 
      has_type T e2 A -> 
      has_type T (app e1 e2) B
  | t_gen: forall T A e,
      has_type (T &s) e A ->
      has_type T e (all A)
  | t_tapp: forall T e A B,
      has_type T e (all B) ->
      wft T A ->
      has_type T e (mani A B)
  | t_box: forall T e1 T1 A e2,
      has_type T e1 T1 ->
      has_type T1 e2 A ->
      rigid 0 T1 A ->
      has_type T (box e1 e2) (boxt T1 A)
  | t_clos: forall T E1 T1 A B e2,
      has_type top E1 T1 ->
      has_type (T1 & A) e2 B ->
      value E1 ->
      wfe T ->
      rigid 0 T1 (arr A B) ->
      has_type T (clos E1 e2) (boxt T1 (arr A B))
  | t_eq: forall T e A B,
      has_type T e A ->
      teq T A B T ->
      has_type T e B
  | lt_nil: forall T,  
      wfe T ->
      has_type T unit top
  | lt_conse: forall T E T1 e A,
      has_type T E T1 ->
      lshape T1 ->
      has_type (T +++ T1) e A -> 
      has_type T (E ,, e) (T1 & A)
  | t_rec: forall T l e A,
      has_type T e A ->
      has_type T (rec l e) (rcd l A)
  | trproj : forall T e T1 l A,
      has_type T e T1 ->
      rlk T1 l A ->
      has_type T (rproj e l) A
  | t_mani: forall T e A B,
      has_type T e A ->
      lshape A ->
      wft (T +++ A) B ->
      has_type T e (A &= B).

#[export]
Hint Constructors lb_in rlk get_var has_type: core.


Remove Hints t_mani : core.

Lemma wfe_lshape: forall T,
  wfe T -> lshape T.
Proof.
  introv Hw. inductions Hw; try solve [econstructor; eauto];
  try solve [inverts IHHw; econstructor; eauto];
  try solve [inverts IHHw1; econstructor; eauto];
  try solve [inverts IHHw2; econstructor; eauto].
Qed.

Lemma typ_wfe: forall T e A,
  has_type T e A ->
  wfe T.
Proof.
  introv Ht. inductions Ht; try solve [eauto]; try solve [inverts* IHHt].
  - eapply wfe_inv; eauto.
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

Lemma typ_ans_wft: forall T e A,
  has_type T e A ->
  wft T A.
Proof.
  introv Ht. inductions Ht; try solve [eauto].
  (* lit *)
  - unfold wft. forwards~: we_int T rt.
  (* var *)
  - unfold wft. eapply getv_wft; eauto.
  (* lam *)
  - forwards~: typ_wfe Ht.
    forwards~: wfe_evar_eteq H.
    econstructor; eauto.
    eapply del_wft; eauto. econstructor. eapply del_refl.
  (* app *)
  - inverts* IHHt1.
  (* gen / all *)
  - econstructor; eauto.
    forwards~: wft_wfe IHHt. eapply wfe_sinv; eauto.
  (* tapp / mani *)
  - eapply wft_all_mani; eauto.
  (* box *)
  - econstructor; eauto.
    forwards~: wft_wfe IHHt1.
  (* clos *)
  - forwards~: typ_wfe Ht2.
    forwards~: wfe_evar_eteq H2.
    econstructor; eauto.
    econstructor; eauto.
    eapply del_wft; eauto. econstructor. eapply del_refl.
  (* teq *)
  - eapply teq_wft_right; eauto.
  (* nil / top *)
  - econstructor; eauto.
  (* lt_conse / T1 & A *)
  - econstructor; eauto.
  (* rec *)
  - econstructor; eauto.
  (* proj *)
  - eapply rl_wft; eauto.
  (* t_mani : guarded with lshape A and wft (T+++A) B *)
  - unfold wft. econstructor; eauto.
Qed.

