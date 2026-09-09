Require Import LibTactics. 
From Stdlib Require Import Arith.
From Stdlib Require Import Lia. 
Require Import Stdlib.Lists.List. 
Require Import Stdlib.Classes.EquivDec. 
From Stdlib Require Import Strings.String.
Import ListNotations.
Require Export Teq ExpSyntax Semantics.
Set Implicit Arguments.



(* -------------------------//-------------------------- *)
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
  | t_blam: forall T B e,
      has_type (T &s) e B ->
      has_type T (blam e) (all B)
  | t_tapp: forall T e A B,
      has_type T e (all B) ->
      wft T A ->
      has_type T (tapp e A) (mani A B)
  | t_box: forall T e1 T1 A e2,
      has_type T e1 T1 ->
      has_type T1 e2 A ->
      rigid 0 T1 A ->
      has_type T (box e1 e2) (boxt T1 A)
  | t_clos: forall T E1 T1 A B e2,
      has_type top E1 T1 ->
      has_type (T1 & A) e2 B ->
      value E1 ->
      rigid 0 T1 (arr A B) ->
      wfe T ->
      has_type T (clos E1 e2) (boxt T1 (arr A B))
  | t_bclos: forall T E1 T1 A e2,
      has_type top E1 T1 ->
      has_type (T1 &s) e2 A ->
      value E1 ->
      rigid 0 T1 (all A) ->
      wfe T ->
      has_type T (bclos E1 e2) (boxt T1 (all A))
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
  | lt_const: forall T T1 E A,
      has_type T E T1 ->
      lshape T1 ->
      wft (T +++ T1) A ->
      has_type T (E ;; A) (T1 &= A)
  | t_rec: forall T l e A,
      has_type T e A ->
      has_type T (rec l e) (rcd l A)
  | trproj : forall T e T1 l A,
      has_type T e T1 ->
      rlk T1 l A ->
      has_type T (rproj e l) A.

#[export]
Hint Constructors lb_in rlk get_var has_type: core.


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

Lemma check_add_old: forall T i,
  check T i -> forall T2,
  check (T2 +++ T) i.
Proof.
  introv Hc. inductions Hc; intros T2.
  - rewrite <-mcon_cons. eauto. 
  - rewrite <-mcon_cons. eauto.
  - rewrite <-mcon_cons_st. eauto.
  - rewrite <-mcon_cons_st. eauto.
Qed.

Lemma wft_weaken: forall T A,
  wft T A -> forall T1,
  wfe (T1 +++ T) ->
  wft (T1 +++ T) A.
Proof.  
  introv Hw. unfold wft in *. inductions Hw; introv Hwe;
  try solve [eauto].
  - econstructor; eauto. eapply check_add_old; eauto.
  - eapply we_get; eauto. eapply lookt_add_old; eauto.
  - econstructor; eauto. 
    forwards~: IHHw2 (T &s) A0 T1.
    rewrite <-mcon_cons_st. eauto.
    rewrite mcon_cons_st. eauto.
  - econstructor; eauto.
    forwards~: IHHw1 (T &= A0) B T1.
    rewrite <-mcon_cons. eauto.
    rewrite mcon_cons. eauto.
  - econstructor; eauto.
    rewrite mapp_ass. eapply IHHw2; eauto.
    forwards~: IHHw1 T T1 T0.
    rewrite <-mapp_ass. eapply wfe_to_mcon_all; eauto.
Qed.

Lemma teq_weaken: forall T1 A B T2,
  teq T1 A B T2 -> forall T3,
  wfe (T3 +++ T2) ->
  teq T1 A B (T3 +++ T2).
Proof.
  introv Ht. inductions Ht; introv Hwe;
  try solve [eauto];
  try solve [econstructor; eauto; eapply check_app; eauto];
  try solve [econstructor; eauto; eapply lookt_add_old; eauto];
  try solve [econstructor; eauto; rewrite mcon_cons_st; eapply IHHt; rewrite <-mcon_cons_st; eauto];
  try solve [econstructor; eauto; rewrite mcon_cons; eapply IHHt; rewrite <-mcon_cons;
             eapply wft_weaken; eauto; eapply teq_wfe_right; eauto];
  try solve [econstructor; eauto; forwards~: IHHt2 T0; rewrite <-mapp_ass;
             eapply wfe_to_mcon_all; [eapply wft_weaken; eauto; eapply teq_wft_right; eauto | rewrite mapp_ass; eauto]];
  (* eq_boxl: new (box-wft) rule.  The body's right ambient is T2, weaken via IH;
     the box-wft side condition is over the LEFT ambient T1, untouched. *)
  try solve [
    eapply eq_boxl;
      [ eapply IHHt; eauto
      | eauto ] ];
  (* eq_boxr: body teq is over T3 (no T2); the box-wft is over the weakened ambient T2. *)
  try solve [ eapply eq_boxr; [ eauto | eapply wft_weaken; eauto ] ];
  (* eq_and *)
  try solve [
    assert (Hw0: wfe T0) by (eapply wfe_cut; exact Hwe);
    eapply eq_and;
    [ eapply IHHt1; exact Hwe
    | eauto | eauto
    | rewrite mapp_ass; eapply IHHt2;
      eapply wfe_app; [ eapply teq_wfe_right; eauto | exact Hw0 ] ] ];
  (* eq_tvar: positional; weaken check on the right ambient *)
  try solve [eapply eq_tvar; eauto; eapply check_add_old; eauto].
Qed.

(* concrete and lshape *)
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
  (* all *)
  - econstructor; eauto.
    forwards~: wft_wfe IHHt. eapply wfe_sinv; eauto. 
  (* tapp *)
  - eapply wft_all_mani; eauto. 
  (* box *)
  - econstructor; eauto.
    forwards~: wft_wfe IHHt1.
  (* clos *)
  - forwards~ Hw2: typ_wfe Ht2.
    forwards~: wfe_evar_eteq Hw2.
    econstructor; eauto.
    econstructor; eauto.
    eapply del_wft; eauto. econstructor. eapply del_refl.
  - forwards~: typ_wfe Ht2.
    econstructor; eauto.
    econstructor; eauto. eapply wfe_sinv; eauto.
  (* teq *)
  - eapply teq_wft_right; eauto.
  - econstructor; eauto.
  - econstructor; eauto.
  - econstructor; eauto. 
  - econstructor; eauto.
  - eapply rl_wft; eauto.
Qed.

Lemma ve_star_aux: forall T ve A,
  has_type T ve A -> forall T1 T2,
  teq T A (T1 &s) T2 ->
  value ve ->
  False.
Proof.
  introv Ht. inductions Ht; introv He Hv;
  try solve [inverts* Hv];
  try solve [inverts* He];
  try solve [match goal with H: teq _ (boxt _ _) (_ &s) _ |- _ =>
               inverts H; match goal with Hb: teq _ _ (_ &s) _ |- _ => inverts Hb end end];
  try solve [inverts He; match goal with Hb: teq _ _ _ _ |- _ => inverts Hb end];
  try solve [forwards~: teq_trans H He; eauto].
Qed.

Lemma ve_star: forall T ve T1,
  has_type T ve (T1 &s) ->
  value ve ->
  False.
Proof.
  intros. forwards~: typ_ans_wft H.
  forwards~: teq_refl H1.
  eapply ve_star_aux; eauto.
Qed.

Lemma merge_inv_aux: forall T v A',
  has_type T v A' -> forall T1 B,
  teq T A' (T1 & B) T ->
  value v -> exists v1 ve C T2,
  v = (ve ,, v1) /\
  value v1 /\
  value ve /\
  has_type (T +++ T2) v1 C /\
  has_type T ve T1 /\
  teq T T2 T1 T /\
  teq T (T2 & C) (T1 & B) T.
Proof.
  introv Ht. inductions Ht; introv Heq Hv;
  try solve [inverts Hv];
  try solve [inductions Heq];
  try solve [match goal with H: teq _ (boxt _ _) (and _ _ _) _ |- _ =>
               inverts H; match goal with Hb: teq _ _ (and _ _ _) _ |- _ => inverts Hb end end];
  try solve [inverts* Heq; inverts* Hv];
  try solve [
    match goal with
    | Hab: teq ?Tc ?Aa ?Bb ?Tc, Hand: teq ?Tc ?Bb (and _ _ _) ?Tc |- _ =>
      forwards Hc: teq_trans Hab Hand;
      forwards~ (?&?&?&?&?&?&?&?&?&?&?): IHHt Hc;
      do 4 eexists; repeat split; eauto
    end ].
Qed.

Lemma merge_inv: forall T v T1 B,
  has_type T v (T1 & B) -> 
  value v -> exists v1 ve C T2,
  v = (ve ,, v1) /\
  value v1 /\
  value ve /\
  has_type (T +++ T2) v1 C /\
  has_type T ve T1 /\
  teq T T2 T1 T /\
  teq T (T2 & C) (T1 & B) T.
Proof.
  introv Ht Hv.
  forwards~: typ_ans_wft Ht. forwards~: teq_refl H.
  eapply merge_inv_aux; eauto.
Qed.

Lemma tmerge_inv_aux: forall T v A',
  has_type T v A' -> forall T1 B,
  teq T A' (T1 &= B) T ->
  value v -> exists A ve T2,
  v = (ve ;; A) /\
  is_box A /\
  value ve /\
  wft (T +++ T2) A /\
  has_type T ve T1 /\
  teq T T2 T1 T /\
  teq T (T2 &= A) (T1 &= B) T.
Proof.
  introv Ht. inductions Ht; introv Heq Hv;
  try solve [inverts Hv];
  try solve [inductions Heq];
  try solve [match goal with H: teq _ (boxt _ _) (and _ _ _) _ |- _ =>
               inverts H; match goal with Hb: teq _ _ (and _ _ _) _ |- _ => inverts Hb end end];
  try solve [inverts* Heq; inverts* Hv];
  try solve [
    match goal with
    | Hab: teq ?Tc ?Aa ?Bb ?Tc, Hand: teq ?Tc ?Bb (and _ _ _) ?Tc |- _ =>
      forwards Hc: teq_trans Hab Hand;
      forwards~ (?&?&?&?&?&?&?&?&?&?): IHHt Hc;
      do 3 eexists; repeat split; eauto
    end ].
Qed.

Lemma tmerge_inv: forall T v T1 B,
  has_type T v (T1 &= B) ->
  value v -> exists A ve T2,
  v = (ve ;; A) /\
  is_box A /\
  value ve /\
  wft (T +++ T2) A /\
  has_type T ve T1 /\
  teq T T2 T1 T /\
  teq T (T2 &= A) (T1 &= B) T.
Proof.
  intros.
  eapply tmerge_inv_aux; eauto.
  eapply teq_refl; eauto.
  eapply typ_ans_wft; eauto.
Qed.

Lemma lookupv_prog: forall T n A,
  get_var T n A -> forall ve,
  has_type top ve T ->
  value ve -> exists v, 
  lookupv ve n v.
Proof.
  introv Hl. inductions Hl; introv Ht Hve. 
  - exfalso. eapply ve_star; eauto. 
  - forwards~ (D&ve1&?&?&?&?&?&?&?&?): tmerge_inv Ht Hve. subst.
    forwards~: IHHl H3. destruct* H.
  - forwards~ (v1&ve0&C&T2&?&?): merge_inv Ht.
    subst. eauto.
  - forwards~ (v1&ve0&C&T2&?&?&?&?&?&?): merge_inv Ht.
    forwards~: IHHl H1.
    subst. inverts* H5. 
Qed.

Lemma canonical_clos_aux: forall A0 A B T v,
  has_type T v A0 ->
  teq T A0 (arr A B) T -> 
  value v -> exists ve e,
  v = clos ve e /\ value ve.
Proof.
  introv Ht. inductions Ht; introv Heq Hv;
  try solve [inverts* Hv];
  try solve [inverts* Heq];
  try solve [match goal with H: teq _ (boxt _ _) (arr _ _) _ |- _ =>
               inverts H; match goal with Hb: teq _ (all _) (arr _ _) _ |- _ => inverts Hb end end];
  try solve [forwards~: teq_trans H Heq].
Qed.

Lemma canonical_clos: forall A B T v,
  has_type T v (arr A B) ->
  value v -> exists ve e,
  v = clos ve e /\ value ve.
Proof.
  introv Ht Hv.
  forwards~: typ_ans_wft Ht. forwards~: teq_refl H.
  eapply canonical_clos_aux; eauto.
Qed.

Lemma canonical_bclos_aux: forall A0 A T v,
  has_type T v A0 ->
  teq T A0 (all A) T -> 
  value v -> exists ve e,
  v = bclos ve e /\ value ve.
Proof.
  introv Ht. inductions Ht; introv Heq Hv;
  try solve [inverts* Hv];
  try solve [inverts* Heq];
  try solve [match goal with H: teq _ (boxt _ _) (all _) _ |- _ =>
               inverts H; match goal with Hb: teq _ (arr _ _) (all _) _ |- _ => inverts Hb end end];
  try solve [forwards~: teq_trans H Heq].
Qed.

Lemma canonical_bclos: forall A T v,
  has_type T v (all A) ->
  value v -> exists ve e,
  v = bclos ve e /\ value ve.
Proof.
  introv Ht Hv.
  forwards~: typ_ans_wft Ht. forwards~: teq_refl H.
  eapply canonical_bclos_aux; eauto.
Qed.

Lemma merge_inv2_aux: forall T v E1 A,
  has_type T (E1 ,, v) A -> forall T1,
  teq T A T1 T ->
  lshape T1 ->
  value v -> 
  value E1 -> exists B T2,
  T1 = (T2 & B).
Proof.
  introv Ht He Hs Hv Hl. inductions Ht.
  - forwards~: teq_trans H He.
    forwards~: IHHt v E1 H0.
  - inverts* He; try solve [inverts* Hs]. 
Qed.

Lemma merge_inv2: forall T v E1 T1,
  has_type T (E1 ,, v) T1 ->
  lshape T1 ->
  value v -> 
  value E1 -> exists B T2,
  T1 = (T2 & B).
Proof.
  introv Ht Hv Hl. 
  eapply merge_inv2_aux; eauto.
  eapply teq_refl; eauto.
  eapply typ_ans_wft; eauto.
Qed.

Lemma tmerge_inv2_aux: forall T C E1 A,
  has_type T (E1 ;; C) A -> forall T1,
  teq T A T1 T ->
  lshape T1 ->
  value E1 -> exists B T2,
  T1 = (T2 &= B).
Proof.
  introv Ht He Hs Hv. inductions Ht.
  - forwards~: teq_trans H He.
    forwards~: IHHt E1 H0.
  - inverts* He; try solve [inverts* Hs]. 
Qed.

Lemma tmerge_inv2: forall T C E1 T1,
  has_type T (E1 ;; C) T1 -> 
  lshape T1 ->
  value E1 -> exists B T2,
  T1 = (T2 &= B).
Proof.
  introv Ht Hv Hl. 
  eapply tmerge_inv2_aux; eauto.
  eapply teq_refl; eauto.
  eapply typ_ans_wft; eauto.
Qed.


Lemma wfe_app: forall T1, 
  wfe T1 -> forall T2,
  wfe T2 ->
  wfe (T2 +++ T1).
Proof.
  introv Hw. inductions Hw; introv Hwe; try solve [simpl in *; eauto];
  try solve [rewrite <-mcon_cons_st; eauto];
  try solve [rewrite <-mcon_cons; eauto].
  - rewrite <-mcon_cons. 
    econstructor; eauto. eapply check_add_old; eauto.
  - rewrite <-mcon_cons. 
    eapply we_get; eauto. eapply lookt_add_old; eauto.
  - rewrite <-mcon_cons in *.
    econstructor; eauto; rewrite mcon_cons; eauto.
  - rewrite <-mcon_cons in *.
    econstructor; eauto. rewrite mcon_cons_st; eauto.
  - rewrite <-mcon_cons in *.
    econstructor; eauto; rewrite mcon_cons; eauto.
  - rewrite <-mcon_cons in *.
    econstructor; eauto. rewrite mcon_cons; eauto.
    rewrite mapp_ass. rewrite mcon_cons; eauto.
  - rewrite <-mcon_cons in *.
    econstructor; eauto. rewrite mcon_cons; eauto.
  - rewrite <-mcon_cons in *.
    econstructor; eauto; rewrite mcon_cons; eauto.
Qed.


Definition conc_above (d:nat) (T:typ) : Prop := forall X, check T X -> X < d.

Lemma check_num_of_abs: forall T X, check T X -> num_of_abs T > 0.
Proof.
  introv Hc. inductions Hc; simpl; lia.
Qed.

Lemma conc_above_zero: forall T, num_of_abs T = 0 -> conc_above 0 T.
Proof.
  introv Hn. unfold conc_above. introv Hc.
  forwards~: check_num_of_abs Hc. lia.
Qed.

Lemma conc_above_st: forall d T, conc_above d T -> conc_above (S d) (T &s).
Proof.
  introv Hc. unfold conc_above in *. introv Hck. inverts Hck.
  - lia.
  - match goal with H: check _ _ |- _ => forwards~: Hc H end. lia.
Qed.

Lemma conc_above_eq: forall d T A, conc_above d T -> conc_above (S d) (T &= A).
Proof.
  introv Hc. unfold conc_above in *. introv Hck. inverts Hck.
  match goal with H: check _ _ |- _ => forwards~: Hc H end. lia.
Qed.

Lemma conc_above_and: forall T1 d T, conc_above d T -> conc_above (d + keyLen T1) (T +++ T1).
Proof.
  intros T1. inductions T1; introv Hc;
    try solve [simpl keyLen; rewrite Nat.add_0_r; eauto].
  - destruct m.
    + replace (keyLen (T1_1 & T1_2)) with (keyLen T1_1) by reflexivity.
      rewrite <- mcon_cons. unfold conc_above in *. introv Hck. inverts Hck.
      match goal with H: check _ _ |- _ => forwards~: IHT1_1 Hc H end.
    + replace (keyLen (T1_1 &= T1_2)) with (S (keyLen T1_1)) by reflexivity.
      rewrite <- mcon_cons.
      forwards~ Hr: IHT1_1 d Hc.
      unfold conc_above in *. introv Hck. inverts Hck.
      match goal with H: check _ _ |- _ => forwards~: Hr H end. lia.
  - replace (keyLen (T1 &s)) with (S (keyLen T1)) by reflexivity.
    rewrite <- mcon_cons_st.
    forwards~ Hr: IHT1 d Hc.
    unfold conc_above in *. introv Hck. inverts Hck.
    + lia.
    + match goal with H: check _ _ |- _ => forwards~: Hr H end. lia.
Qed.

Lemma c2g_num0: forall ve, num_of_abs (c2g ve) = 0.
Proof.
  induction ve; simpl; auto.
Qed.

Lemma rigid_of_wft_gen: forall n d T A,
  bindings T A <= n ->
  conc_above d T ->
  wft T A ->
  rigid d T A.
Proof.
  intros n. inductions n; introv Hle Hca Hw.
  - forwards~: bindings_min A T. lia.
  - unfold wft in Hw. inverts Hw;
      try solve [econstructor; eauto].
    + (* tvar via we_get : concrete var, recurse on its lookt type *)
      eapply rigid_cvar; eauto.
      eapply IHn; eauto.
      forwards~: var_decr H3. lia.
      eapply lookt_wft; eauto.
    + (* arr *)
      econstructor; eapply IHn; eauto; solve_size.
    + (* all : descend under the real &s, bump d (conc_above_st) *)
      eapply rigid_all. eapply IHn; eauto.
      solve_size. eapply conc_above_st; eauto.
    + (* mani : descend under &= A0, bump d (conc_above_eq) *)
      eapply rigid_mani. eapply IHn; eauto.
      solve_size. eapply conc_above_eq; eauto.
    + (* and : spine A2 at d + keyLen T1 (conc_above_and) *)
      destruct m2.
      * eapply rigid_and.
        -- eapply IHn; eauto. unfold bindings in *. rewrite weight_evar in *. lia.
        -- eapply IHn; eauto.
           unfold bindings in *. rewrite weight_evar in *. rewrite <-mkb_eq. lia.
           eapply conc_above_and; eauto.
      * eapply rigid_and.
        -- eapply IHn; eauto. unfold bindings in *. rewrite weight_eteq in *. lia.
        -- eapply IHn; eauto.
           unfold bindings in *. rewrite weight_eteq in *. rewrite <-mkb_eq. lia.
           eapply conc_above_and; eauto.
    + (* ands *)
      eapply rigid_ands. eapply IHn; eauto. solve_size.
    + (* rcd *)
      econstructor; eapply IHn; eauto; solve_size.
Qed.

Lemma rigid_of_wft: forall T A,
  num_of_abs T = 0 ->
  wft T A ->
  rigid 0 T A.
Proof.
  intros. eapply rigid_of_wft_gen with (d := 0); eauto.
  eapply conc_above_zero; eauto.
Qed.

Lemma teq_strengthen: forall T1 A B T2 T3,
  teq T1 A B (T3 +++ T2) ->
  wft T2 B ->
  teq T1 A B T2.
Proof.
  introv Ht Hw2.
  forwards Hw1: teq_wft_left Ht.
  forwards HwfeT1: teq_wfe_left Ht.
  forwards HwfeT2: wft_wfe Hw2.
  (* Decompose the left ambient as (top +++ T1) and the right as (T3 +++ T2), then
     use teq_swap_outer to set the right outer frame T3 -> top, leaving the inner
     T2 in place.  The left outer frame stays top (left inner = T1 = whole). *)
  assert (E1: (top +++ T1) = T1) by (eapply mcon_top; eauto).
  assert (E2: (top +++ T2) = T2) by (eapply mcon_top; eauto).
  assert (Hsw: teq (top +++ T1) A B (top +++ T2)).
  { eapply teq_swap_outer with (T2 := T1) (T4 := T2).
    - exact Hw1.
    - exact Hw2.
    - rewrite E1. exact Ht.
    - rewrite E1. exact HwfeT1.
    - rewrite E2. exact HwfeT2. }
  rewrite E1, E2 in Hsw. exact Hsw.
Qed.

Lemma teq_old: forall T1 A B T2 T0,
  teq T1 A B (T0 +++ T2) ->
  wft T2 B -> forall T3,
  wfe (T3 +++ T2) ->
  teq T1 A B (T3 +++ T2).
Proof.
  intros. eapply teq_weaken; eauto.
  eapply teq_strengthen; eauto.
Qed.


Lemma lshape_int: forall T T1,
  teq T int T1 T ->
  lshape T1 ->
  False.
Proof.
  introv Ht Hs. inductions Ht; inverts* Hs.
Qed.


(* lt_closed_gen / lt_closed are placed AFTER the typ_shape_* shape-mismatch
   lemmas below, since the proof of lt_closed_gen uses them. *)
Lemma typ_shape_nil_aux: forall T A,
  has_type T unit A -> forall T2,
  teq T A T2 T ->
  lshape T2 ->
  T2 = top.
Proof.
  introv Ht. inductions Ht; intros.
  - forwards~: teq_trans H H0.
  - inverts* H0; inverts* H1.
Qed.

Lemma typ_shape_nil: forall T T2,
  has_type T unit T2 ->
  lshape T2 -> 
  T2 = top.
Proof.
  introv Ht. 
  eapply typ_shape_nil_aux; eauto.
  eapply teq_refl.
  eapply typ_ans_wft; eauto.
Qed.

Lemma typ_shape_lit_aux: forall T A n,
  has_type T (lit n) A -> forall T2,
  teq T A T2 T ->
  lshape T2 ->
  False.
Proof.
  introv Ht. inductions Ht; intros.
  - inverts* H0; inverts* H1.
  - forwards~: teq_trans H H0. eauto.
Qed.

Lemma typ_shape_lit: forall T T2 n,
  has_type T (lit n) T2 -> 
  lshape T2 ->
  False.
Proof.
  introv Ht. 
  eapply typ_shape_lit_aux; eauto.
  eapply teq_refl.
  eapply typ_ans_wft; eauto.
Qed.

Lemma typ_shape_clos_aux: forall T A E e,
  has_type T (clos E e) A -> forall T2,
  teq T A T2 T ->
  lshape T2 ->
  False.
Proof.
  introv Ht. inductions Ht; introv He Hl;
  try solve [inverts* Hl];
  try solve [inverts He; inverts Hl;
    match goal with Hb: teq _ (arr _ _) _ _ |- _ => inverts Hb end];
  try solve [forwards~: teq_trans H He; eauto].
Qed.

Lemma typ_shape_clos: forall T T2 E e,
  has_type T (clos E e) T2 -> 
  lshape T2 ->
  False.
Proof.
  introv Ht. 
  eapply typ_shape_clos_aux; eauto.
  eapply teq_refl.
  eapply typ_ans_wft; eauto.
Qed.

Lemma typ_shape_bclos_aux: forall T A E e,
  has_type T (bclos E e) A -> forall T2,
  teq T A T2 T ->
  lshape T2 ->
  False.
Proof.
  introv Ht. inductions Ht; introv He Hl;
  try solve [inverts* Hl];
  try solve [inverts He; inverts Hl;
    match goal with Hb: teq _ (all _) _ _ |- _ => inverts Hb end];
  try solve [forwards~: teq_trans H He; eauto].
Qed.

Lemma typ_shape_bclos: forall T T2 E e,
  has_type T (bclos E e) T2 -> 
  lshape T2 ->
  False.
Proof.
  introv Ht. 
  eapply typ_shape_bclos_aux; eauto.
  eapply teq_refl.
  eapply typ_ans_wft; eauto.
Qed.

Lemma typ_shape_rec_aux: forall T A l e,
  has_type T (rec l e) A -> forall T2,
  teq T A T2 T ->
  lshape T2 ->
  False.
Proof.
  introv Ht. inductions Ht; intros.
  - forwards~: teq_trans H H0. eauto.
  - inverts* H; inverts* H0.
Qed.

Lemma typ_shape_rec: forall T T2 l e,
  has_type T (rec l e) T2 -> 
  lshape T2 ->
  False.
Proof.
  introv Ht. 
  eapply typ_shape_rec_aux; eauto.
  eapply teq_refl.
  eapply typ_ans_wft; eauto.
Qed.

Lemma lshape_app: forall T1 T,
  lshape T ->
  lshape (T +++ T1).
Proof.
  intros T1. inductions T1; introv Hl; try solve [simpl; eauto].
  - rewrite <-mcon_cons. eauto.
  - rewrite <-mcon_cons_st. eauto.
Qed.


(* ===================================================================== *)
(* check positions transfer across a teq-equal lshape spine: only the spine
   modes (which eq_and forces equal) matter, the element types are irrelevant.
   POSITIONAL replacement for inner_spine_teq + check_inner_tvar. *)
Lemma check_spine_teq: forall T S1 S2,
  teq T S1 S2 T -> lshape S1 -> lshape S2 ->
  forall X, check (T +++ S1) X -> check (T +++ S2) X.
Proof.
  introv Hsp. inductions Hsp; introv Hl1 Hl2 Hin.
  all: try solve [inverts Hl1 | inverts Hl2].
  - assumption.
  - rewrite <- mcon_cons in *. destruct m.
    + inverts Hin. eapply check_evar. eapply IHHsp1; eauto.
    + inverts Hin. eapply check_eteq. eapply IHHsp1; eauto.
  - rewrite <- mcon_cons_st in *. inverts Hin.
    + eapply check_zero.
    + eapply check_etvar. eapply IHHsp; eauto.
Qed.

(* lookt resolutions transfer across a teq-equal lshape spine: a concrete var in
   the left spine resolves to a type teq-related (through the spine's element
   equalities) to the right spine's resolution at the same index. *)
Lemma lookt_spine_teq: forall T S1 S2,
  teq T S1 S2 T -> lshape S1 -> lshape S2 ->
  forall X A, lookt (T +++ S1) X A ->
  exists B, lookt (T +++ S2) X B /\ teq (T +++ S1) A B (T +++ S2).
Proof.
  introv Hsp. inductions Hsp; introv Hl1 Hl2 Hlk.
  all: try solve [inverts Hl1 | inverts Hl2].
  - (* top *) simpl in *. exists A. split; [assumption|].
    eapply teq_refl. eapply lookt_wft; eauto.
  - (* and *) rewrite <- mcon_cons in *.
    forwards~ (HwA0 & HwB0): teq_wft Hsp2.
    destruct m.
    + (* evar & : index unchanged, element irrelevant *)
      inverts Hlk.
      forwards~ (B0 & Hlk2 & Hteq0): IHHsp1 H5.
      exists B0. split.
      * eapply lookt_evar; exact Hlk2.
      * rewrite <- (mcon_cons T1 T3 A non).
        eapply adde_teq_r; [ eapply adde_teq_l; [ exact Hteq0 | exact HwA0 ] | exact HwB0 ].
    + (* eteq &= : either resolves to the head element or below, both tshift'd *)
      inverts Hlk.
      * (* lookt_zero: head element, A0 = tshift 0 A, B0 = tshift 0 B *)
        exists (tshift 0 B). split.
        ** eapply lookt_zero.
        ** rewrite <- (mcon_cons T1 T3 A rt).
           assert (wfe ((T1+++T3) &= A)) by eauto;
           assert (wfe ((T1+++T4) &= B)) by eauto;
           eapply coh_weaken_base; eauto.
      * (* lookt_eteq: below the head, S X', resolves in the spine, tshift'd *)
        forwards~ (Bq & Hlk2 & Hteq0): IHHsp1 H5.
        exists (tshift 0 Bq). split.
        ** eapply lookt_eteq; exact Hlk2.
        ** rewrite <- (mcon_cons T1 T3 A rt).
           assert (wfe ((T1+++T3) &= A)) by eauto;
           assert (wfe ((T1+++T4) &= B)) by eauto;
           eapply shift_insb;
             [ exact Hteq0 | eapply isb_here_ee; [ exact HwA0 | exact HwB0 ]
             | eauto | eauto ].
  - (* ands &s : index S X', resolves in the spine, tshift'd; both heads &s *)
    rewrite <- mcon_cons_st in *. inverts Hlk.
    forwards~ (Bq & Hlk2 & Hteq0): IHHsp H2.
    exists (tshift 0 Bq). split.
    + eapply lookt_etvar; exact Hlk2.
    + rewrite <- (mcon_cons_st T1 T3).
      eapply shift_tvar_both with (X := 0);
        [ exact Hteq0 | eapply ib_here2
        | eapply we_tvar; eapply teq_wfe_left; exact Hteq0
        | eapply we_tvar; eapply teq_wfe_right; exact Hteq0 ].
Qed.

(* A common lshape suffix can be appended to a spine teq.  This threads the
   reframe (reframe_refl_size, below) through the appended elements; proved by
   mutual size induction with reframe_refl_size via a shared fuel n. *)
(* The two mutually-dependent size-bounded lemmas are proved together by a SINGLE
   well-founded induction on the fuel n (a plain [induction n], so the guard checker
   does not need to reconcile a mutual fixpoint).  The conjunction's two IHs at the
   predecessor n are [IHspine]/[IHreframe]; all the cross/self recursive calls go
   through them.  spine_app_size / reframe_refl_size are then projections. *)
Lemma spine_reframe_size: forall n,
  (forall U T S1 S2,
     bindings (T +++ S1) U <= n ->
     teq T S1 S2 T -> lshape S1 -> lshape S2 -> lshape U ->
     wfe ((T +++ S1) +++ U) ->
     wfe ((T +++ S2) +++ U) ->
     teq T (S1 +++ U) (S2 +++ U) T)
  /\ (forall B T S1 S2,
     bindings (T +++ S1) B <= n ->
     teq T S1 S2 T -> lshape S1 -> lshape S2 ->
     wft (T +++ S1) B ->
     wfe (T +++ S2) ->
     teq (T +++ S1) B B (T +++ S2)).
Proof.
  induction n as [| n [IHspine IHreframe]]; split.
  - (* spine, n = 0 : vacuous by the strictly-positive weight bound *)
    introv Hb Hsp Hl1 Hl2 HlU Hw Hwfe.
    forwards~: bindings_min U (T +++ S1). lia.
  - (* reframe, n = 0 : vacuous *)
    introv Hb Hsp Hl1 Hl2 Hw Hwfe.
    forwards~: bindings_min B (T +++ S1). lia.
  - (* spine_app_size : append the common lshape suffix U to the spine teq Hsp. *)
    introv Hb Hsp Hl1 Hl2 HlU Hw Hwfe.
    destruct U; try solve [inverts HlU].
    + (* top *) simpl. exact Hsp.
    + (* and U1 m U2 : split off the last element; spine via IHspine, body via IHreframe *)
      inverts HlU.
      rewrite <- mcon_cons in Hw, Hwfe.
      forwards~ HwpfL: wfe_inv Hw.
      forwards~ HwpfR: wfe_inv Hwfe.
      assert (HwU2: wft ((T +++ S1) +++ U1) U2).
      { destruct m; [ eapply wfe_evar_eteq | idtac ]; unfold wft; exact Hw. }
      assert (Hb1: bindings (T +++ S1) U1 <= n).
      { unfold bindings in *. destruct m;
        [ rewrite weight_evar in Hb | rewrite weight_eteq in Hb ]; lia. }
      assert (Hb2: bindings ((T +++ S1) +++ U1) U2 <= n).
      { unfold bindings in *. rewrite <- (mkb_eq U1 (T +++ S1)). destruct m;
        [ rewrite weight_evar in Hb | rewrite weight_eteq in Hb ]; lia. }
      rewrite <- (mcon_cons S1 U1 U2 m).
      rewrite <- (mcon_cons S2 U1 U2 m).
      assert (HspU: teq T (S1 +++ U1) (S2 +++ U1) T).
      { eapply IHspine;
          [ exact Hb1 | exact Hsp | exact Hl1 | exact Hl2 | exact H0
          | exact HwpfL | exact HwpfR ]. }
      eapply eq_and.
      * exact HspU.
      * eapply lshape_app; exact Hl1.
      * eapply lshape_app; exact Hl2.
      * repeat rewrite mapp_ass.
        eapply IHreframe with (T := T) (S1 := S1 +++ U1) (S2 := S2 +++ U1).
        --- unfold bindings in *. repeat rewrite <- mapp_ass. exact Hb2.
        --- exact HspU.
        --- eapply lshape_app; exact Hl1.
        --- eapply lshape_app; exact Hl2.
        --- rewrite <- mapp_ass. exact HwU2.
        --- rewrite <- mapp_ass. exact HwpfR.
    + (* U1 &s : append an abstract binder *)
      inverts HlU.
      rewrite <- mcon_cons_st in Hw, Hwfe.
      rewrite <- (mcon_cons_st S1 U). rewrite <- (mcon_cons_st S2 U).
      eapply eq_ands; [ | eapply lshape_app; exact Hl1 | eapply lshape_app; exact Hl2 ].
      eapply IHspine;
        [ unfold bindings in *; rewrite weight_etvar in Hb; lia
        | exact Hsp | exact Hl1 | exact Hl2 | exact H0
        | eapply wfe_sinv; exact Hw | eapply wfe_sinv; exact Hwfe ].
  - (* reframe_refl_size *)
    introv Hb Hsp Hl1 Hl2 Hw Hwfe.
    unfold wft in Hw. inverts Hw;
      try solve [ eauto ].
    all: fold wft in *.
    (* tvar i, abstract (via check): positional eq_tvar needs check on BOTH
       sides at the SAME var; transfer the check position across the spine. *)
    all: try solve [
      match goal with H: check _ ?i |- teq _ (tvar ?i) _ _ =>
        eapply eq_tvar;
          [ eauto | exact Hwfe | exact H | eapply check_spine_teq; [ exact Hsp | exact Hl1 | exact Hl2 | exact H ] ] end ].
    (* tvar i, concrete (lookt): resolve through the spine and reflect *)
    all: try solve [
      match goal with H: lookt _ ?i _ |- teq _ (tvar ?i) _ _ =>
        forwards~ (C & Hlk2 & Hteq0): lookt_spine_teq Hsp Hl1 Hl2 H;
        eapply eq_eql; [ exact H | ];
        eapply eq_eqr; [ exact Hlk2 | exact Hteq0 ] end ].
    (* arr *)
    all: try solve [
      match goal with |- teq _ (arr _ _) _ _ =>
        eapply eq_arr; [ eapply IHreframe; eauto; solve_size
                       | eapply IHreframe; eauto; solve_size ] end ].
    (* rcd *)
    all: try solve [
      match goal with |- teq _ (rcd _ _) _ _ =>
        eapply eq_rcd; eapply IHreframe; eauto; solve_size end ].
    (* boxt : box body is ambient-independent; reflexivity via the admissible
       teq_boxbox lemma (eq_boxbox is no longer a constructor).  The body wft and
       rigidity come from inverting the source box's wft (we_box premises). *)
    all: try solve [
      match goal with H: rigid 0 ?Tf ?Bd |- teq _ (boxt ?Tf ?Bd) _ _ =>
        eapply teq_boxbox;
          [ eapply teq_refl; unfold wft; eassumption
          | unfold wft; eapply we_box; eauto
          | unfold wft; eapply we_box; eauto ] end ].
    (* all : extend both ambients by &s, recurse on the spine S1&s / S2&s *)
    all: try solve [
      match goal with H: wfe ((_ &s) &= ?A) |- teq _ (all ?A) _ _ =>
        eapply eq_all;
        rewrite (mcon_cons_st T S1); rewrite (mcon_cons_st T S2);
        eapply IHreframe with (T := T) (S1 := S1 &s) (S2 := S2 &s);
          [ rewrite <- (mcon_cons_st T S1); unfold bindings in *;
            simpl in Hb; fold mkb in Hb; simpl; fold mkb; lia
          | eapply eq_ands; [ exact Hsp | exact Hl1 | exact Hl2 ]
          | econstructor; exact Hl1 | econstructor; exact Hl2
          | rewrite <- (mcon_cons_st T S1); unfold wft; exact H
          | rewrite <- (mcon_cons_st T S2); eapply we_tvar; exact Hwfe ] end ].
    (* ands : B = T1 &s (a standalone star-list); reframe the list T1 then eq_ands *)
    all: try solve [
      match goal with Hsls: lshape ?T1b |- teq _ (?T1b &s) _ _ =>
        eapply eq_ands;
          [ eapply IHreframe;
              [ unfold bindings in *; rewrite weight_etvar in Hb; lia
              | exact Hsp | exact Hl1 | exact Hl2 | unfold wft; eassumption | exact Hwfe ]
          | exact Hsls | exact Hsls ] end ].
    (* mani : with the new PADDING eq_manil/eq_manir, the body reduces to a
       binder-EXCHANGE leaf (a &s inserted ABOVE the &= on the left, BELOW it on the
       right) at CROSS ambients (spine S1 on the left, S2 on the right).  We build it
       as a transitivity: (1) teq_exch_s_eq gives the exchange at the SAME spine S1,
       (2) shift_tvar_both (via ib_teq o ib_here2, a symmetric &s-insertion below the
       top &=) reframes the right ambient S1 -> S2 on the already-shifted body.  The
       cross-ambient reflexive body HrefB0 is the &=A1-extended spine reflexivity. *)
    all: try (match goal with HmA: wfe (_ &= ?A1), HmB: wfe ((_ &= ?A1) &= ?A2)
        |- teq _ (mani ?A1 ?A2) _ _ =>
        assert (HwA1: wft (T +++ S1) A1) by (unfold wft; exact HmA);
        assert (HrefA1: teq (T +++ S1) A1 A1 (T +++ S2)) by
          (eapply IHreframe;
            [ unfold bindings in *; simpl in Hb; fold mkb in Hb; lia
            | exact Hsp | exact Hl1 | exact Hl2 | exact HwA1 | exact Hwfe ]);
        assert (HrefB0: teq ((T +++ S1) &= A1) A2 A2 ((T +++ S2) &= A1)) by
          (rewrite (mcon_cons T S1 A1 rt); rewrite (mcon_cons T S2 A1 rt);
           eapply IHreframe with (T := T) (S1 := S1 &= A1) (S2 := S2 &= A1);
             [ rewrite <- (mcon_cons T S1 A1 rt); unfold bindings in *;
               simpl in Hb; fold mkb in Hb; simpl; fold mkb; lia
             | eapply eq_and; [ exact Hsp | exact Hl1 | exact Hl2 | exact HrefA1 ]
             | eapply lsh_evar; exact Hl1 | eapply lsh_evar; exact Hl2
             | rewrite <- (mcon_cons T S1 A1 rt); unfold wft; exact HmB
             | rewrite <- (mcon_cons T S2 A1 rt); unfold wft;
               eapply teq_wft_right; exact HrefA1 ]);
        eapply eq_manil; eapply eq_manir;
        assert (Hrefl1: teq ((T +++ S1) &= A1) A2 A2 ((T +++ S1) &= A1)) by
          (eapply teq_refl; unfold wft; exact HmB);
        forwards Hstep1: teq_exch_s_eq Hrefl1 HmA;
        assert (Hstep2: teq (((T +++ S1) &s) &= tshift 0 A1) (tshift 1 A2) (tshift 1 A2)
                            (((T +++ S2) &s) &= tshift 0 A1)) by
          (eapply shift_tvar_both with (X := 1);
            [ exact HrefB0
            | eapply ib_teq; eapply ib_here2
            | eapply teq_wfe_right; exact Hstep1
            | eapply teq_wfe_right; eapply teq_exch_s_eq;
                [ eapply teq_refl; unfold wft; eapply teq_wft_right; exact HrefB0
                | eapply teq_wfe_right; exact HrefB0 ] ]);
        eapply teq_trans; [ exact Hstep1 | exact Hstep2 ] end).
    (* and (list) : the spine prefix T1b is reframed reflexively (Href_T1, via IHreframe),
       the appended spine S1+++T1b / S2+++T1b is built (HspT1, via IHspine), and the body
       A2b is reframed over that appended spine (IHreframe again).  HwpfR comes from
       teq_wft_right of Href_T1, avoiding a standalone wfe of the spine fragment. *)
    all: try (match goal with Hsub: wfe (_ &= ?T1b), Hbody: wfe ((_ +++ ?T1b) &= ?A2b),
        Hls: lshape ?T1b |- teq _ (and ?T1b ?mb ?A2b) _ _ =>
        assert (HwpfL: wfe ((T +++ S1) +++ T1b)) by (eapply wfe_inv; exact Hbody);
        assert (Href_T1: teq (T +++ S1) T1b T1b (T +++ S2)) by
          (eapply IHreframe;
            [ unfold bindings in *; destruct mb;
                [ rewrite weight_evar in Hb | rewrite weight_eteq in Hb ];
              forwards~ Hwm: weight_min A2b (mkb_list (mkb (T +++ S1)) T1b ++ mkb (T +++ S1));
              lia
            | exact Hsp | exact Hl1 | exact Hl2 | unfold wft; exact Hsub | exact Hwfe ]);
        assert (HwpfR: wfe ((T +++ S2) +++ T1b)) by
          (eapply wfe_to_mcon_all; eapply teq_wft_right; exact Href_T1);
        assert (HspT1: teq T (S1 +++ T1b) (S2 +++ T1b) T) by
          (eapply IHspine;
            [ unfold bindings in *; destruct mb;
                [ rewrite weight_evar in Hb | rewrite weight_eteq in Hb ];
              forwards~ Hwm: weight_min A2b (mkb_list (mkb (T +++ S1)) T1b ++ mkb (T +++ S1));
              lia
            | exact Hsp | exact Hl1 | exact Hl2 | exact Hls | exact HwpfL | exact HwpfR ]);
        eapply eq_and;
          [ exact Href_T1 | exact Hls | exact Hls | ];
        repeat rewrite mapp_ass;
        eapply IHreframe with (T := T) (S1 := S1 +++ T1b) (S2 := S2 +++ T1b);
          [ unfold bindings in *; repeat rewrite <- mapp_ass; rewrite <- (mkb_eq T1b (T +++ S1));
            destruct mb;
              [ rewrite weight_evar in Hb | rewrite weight_eteq in Hb ];
            forwards~ Hwm: weight_min T1b (mkb (T +++ S1)); lia
          | exact HspT1 | eapply lshape_app; exact Hl1 | eapply lshape_app; exact Hl2
          | rewrite <- mapp_ass; unfold wft; exact Hbody
          | rewrite <- mapp_ass; exact HwpfR ] end).
Qed.

Lemma reframe_refl_size: forall n B T S1 S2,
  bindings (T +++ S1) B <= n ->
  teq T S1 S2 T -> lshape S1 -> lshape S2 ->
  wft (T +++ S1) B ->
  wfe (T +++ S2) ->
  teq (T +++ S1) B B (T +++ S2).
Proof. intros n. apply (proj2 (spine_reframe_size n)). Qed.

Lemma reframe_refl: forall B T S1 S2,
  teq T S1 S2 T -> lshape S1 -> lshape S2 ->
  wft (T +++ S1) B ->
  wfe (T +++ S2) ->
  teq (T +++ S1) B B (T +++ S2).
Proof.
  intros. eapply reframe_refl_size; eauto.
Qed.

(* The ambient-tail substitution keystone: substitute the right local head S2 by
   the left local head S1 in an element equality, using the reframed reflexivity of
   B across the two teq-equal spines and transitivity. *)
Lemma ambient_tail_subst: forall T S1 S2 A B,
  teq (T +++ S1) A B (T +++ S2) ->
  teq T S1 S2 T -> lshape S1 -> lshape S2 ->
  teq (T +++ S1) A B (T +++ S1).
Proof.
  introv Hel Hsp Hl1 Hl2.
  forwards~ (HwA & HwB): teq_wft Hel.
  eapply teq_trans; [ exact Hel | ].
  (* teq (T+++S2) B B (T+++S1) is reframe along the symmetric spine *)
  eapply reframe_refl; [ eapply teq_sym; exact Hsp | exact Hl2 | exact Hl1 | exact HwB | ].
  eapply teq_wfe_left; exact Hel.
Qed.


Lemma add_top_lshape: forall T,
  lshape T ->
  T = (top +++ T).
Proof.
  introv Hs. inductions Hs; eauto.
  - rewrite <-mcon_cons. rewrite <-IHHs. eauto.
  - rewrite <-mcon_cons_st. rewrite <- IHHs. eauto.
Qed.

Lemma teq_box_inv: forall T1 T3 A C T2,
  teq T1 (boxt T3 A) C T2 ->
  teq T3 A C T2.
Proof.
  introv Ht. inductions Ht; try solve [eauto];
  try solve [ eapply eq_boxr; eauto ].
  forwards Hbody: IHHt; [ reflexivity | ].
  forwards Hwl: teq_wft_left Ht.
  unfold wft in Hwl. simpl in Hwl. inverts Hwl.
  eapply eq_manir.
  forwards (nn & Hd): teq_teqd Hbody.
  forwards Hrc: teqd_rigid_r Hd H4.
  eapply teq_shift_tvar_l_rigid;
    [ exact Hbody | exact Hrc | eapply itv_here2 | eapply we_tvar; eapply teq_wfe_left; exact Hbody ].
Qed.

Lemma c2g_typ: forall e1 A,
  c2g (e1 ;; A) = ((c2g e1) &= A).
Proof.
  intros. simpl. eauto.
Qed.


Lemma c2g_wfe_gen: forall ve T1 A,
  has_type T1 ve A ->
  value ve -> forall T,
  teq T1 A T T1 ->
  lshape T ->
  wfe (T1 +++ T) ->
  wfe (T1 +++ c2g ve).
Proof.
  introv Ht. inductions Ht; introv Hv He Hs Hw; try solve [eauto]; try solve [inverts* Hv].
  - forwards~: teq_trans H He.
    eapply IHHt; eauto.
  - inverts He; inverts* Hs. inverts Hv. simpl. eapply IHHt1; eauto. eapply teq_wfe_right; eauto.
  - inverts He; inverts* Hs. inverts Hv. rewrite c2g_typ.
    rewrite <-mcon_cons in *.
    forwards~: teq_wfe_left H10.
    forwards~: IHHt T1.
    eapply teq_refl. eapply wfe_mcon; eauto.

    forwards~: teq_wft_left H10.
    forwards~ (?&?&?): boxt_wft_inv H7.
    eapply we_box; eauto.
    eapply wft_box_rigid; eauto.
  - inverts He; inverts* Hs.
Qed.


Lemma c2g_wfe: forall ve T1 T,
  has_type T1 ve T ->
  value ve ->
  lshape T ->
  wfe (T1 +++ T) ->
  wfe (T1 +++ c2g ve).
Proof.
  intros. eapply c2g_wfe_gen; eauto.
  eapply teq_refl; eauto.
  eapply typ_ans_wft; eauto.
Qed.

Lemma c2g_lshape: forall ve,
  lshape (c2g ve).
Proof.
  intros ve. inductions ve; simpl; eauto.
Qed.


Lemma c2g_wfe_sp: forall ve T,
  has_type top ve T ->
  lshape T ->
  value ve ->
  wfe (c2g ve).
Proof.
  introv Ht Hs Hv.
  forwards~: c2g_wfe ve top T.
  forwards~: typ_ans_wft Ht.
  eapply wfe_to_mcon_all; eauto.
  rewrite add_top_lshape; eauto.
  eapply c2g_lshape; eauto.
Qed.

Inductive lrel: typ -> typ -> Prop :=
  | lrel_nil:
      lrel top top
  | lrel_eteq: forall T1 T2 A B,
      lrel T1 T2 ->
      teq T1 A B T2 ->
      lrel (T1 &= A) (T2 &= B)
  | lrel_etvar: forall T1 T2,
      lrel T1 T2 ->
      lrel (T1 &s) (T2 &s)
  | lrel_evar: forall T1 T2 A B,
      lrel T1 T2 ->
      teq T1 A B T2 ->
      lrel (T1 & A) (T2 & B)
  (* can delete an entry of term variable *)
  | lrel_devar: forall T1 T2 A,
     lrel T1 T2 ->
     lrel (T1 & A) T2.

#[export]
Hint Constructors lrel: core.

Lemma vtyp_lrel_gen: forall ve A,
  has_type top ve A -> forall T,
  teq top A T top ->
  lshape T ->
  value ve ->
  lrel T (c2g ve).
Proof.
  introv Ht. inductions Ht; introv Heq Hs Hv; try solve [inverts Hv]; try solve [inverts Heq; inverts Hs].
  - (* clos *) simpl. inverts Heq; inverts Hs; try solve [eapply lrel_nil];
      (* leftover lshape cases (T = and/star) contradict the unpacked body teq
         [teq T1 (arr _ _) T top] since arr cannot relate to a context shape. *)
      match goal with H1: teq _ (arr _ _) _ _ |- _ => solve [inverts H1] end.
  - (* bclos *) simpl. inverts Heq; inverts Hs; try solve [eapply lrel_nil];
      match goal with H1: teq _ (all _) _ _ |- _ => solve [inverts H1] end.
  - (* t_eq *) forwards~ Hc: teq_trans H Heq.
  - (* unit *) simpl. inverts Heq; inverts Hs; try solve [eapply lrel_nil].
  - (* ,, *) simpl. inverts Heq; try solve [inverts Hs]. inverts Hs. inverts Hv.
    forwards~ HlE: IHHt1 H3 H8.
  - (* ;; *) simpl. inverts Heq; try solve [inverts Hs]. inverts Hs. inverts Hv.
    rewrite <-add_top_lshape in H10; eauto.
    rewrite <-add_top_lshape in H10; eauto.
    forwards~ Hl4: IHHt H4 H9.
    forwards~ HwcE: c2g_wfe_sp Ht.
    eapply lrel_eteq; [ exact Hl4 | ].
    forwards~ HrigA0: wft_box_rigid H0.
    forwards~ (HwT & HwA0 & HwfeT): boxt_wft_inv H0.
    forwards~ HwB: teq_wft_right H10.
    forwards Hbi: teq_box_inv H10.
    forwards Hbis: teq_sym Hbi.
    (* ~rbox-free re-box on the right: eq_boxr directly (no rbox_dec split).
       The box-wft side condition [wft (c2g E) (boxt T A0)] is rebuilt via we_box
       from the rigid body (HrigA0), the body wft (HwT), and the frame wfe (HwcE). *)
    eapply eq_boxr; eauto.
    unfold wft. eapply we_box; eauto.
Qed.


Lemma vtyp_lrel: forall ve T,
  has_type top ve T ->
  lshape T ->
  value ve ->
  lrel T (c2g ve).
Proof.
  intros. eapply vtyp_lrel_gen; eauto.
  eapply teq_refl; eauto. eapply typ_ans_wft; eauto.
Qed.


Lemma lrel_wfe: forall T1 T2,
  lrel T1 T2 ->
  wfe T1 ->
  wfe T2.
Proof.
  introv He. inductions He; introv Hw; try solve [inverts* Hw]; eauto.
  - forwards~: teq_wft_right H.
  - forwards~: teq_wft_right H. eapply wfe_eteq_evar; eauto.
  - eapply IHHe; eauto. eapply wfe_inv; eauto.
Qed.


Lemma check_lrel: forall T1 T2,
  lrel T1 T2 -> forall X,
  check T1 X ->
  check T2 X.
Proof.
  introv Hl. inductions Hl; introv Hc;
    try solve [inverts Hc; econstructor; eauto];
    try solve [econstructor; eauto].
  - (* lrel_devar : T1 & A ~> T2 ; check (T1 & A) X gives check T1 X *)
    inverts Hc. eauto.
Qed.


Lemma lookt_lrel_gen: forall T1 T2,
  wfe T1 ->
  lrel T1 T2 -> forall n A,
  lookt T1 n A -> exists B,
  lookt T2 n B /\ teq T2 B A T1.
Proof.
  introv Hw Hl. inductions Hl; introv Hk; eauto.
  - inverts* Hk.
  - destruct* n.
    + inverts* Hk. exists* (tshift 0 B). split*.
      forwards Hsy: teq_sym H;
      assert (wft T2 B) by (eapply teq_wft_left; exact Hsy);
      assert (wft T1 A) by (eapply teq_wft_right; exact Hsy);
      eapply shift_insb; [ exact Hsy | eapply isb_here_ee; eauto | eauto | eauto ].
    + forwards~ Hwi: wfe_inv Hw. inverts* Hk.
      match goal with Hlk: lookt T1 _ _ |- _ =>
        forwards~ (C&Hc1&Hc2): IHHl Hwi Hlk end.
      exists (tshift 0 C). split*.
      assert (wft T2 B) by (eapply teq_wft_right; exact H);
      assert (wft T1 A) by (eapply teq_wft_left; exact H);
      eapply shift_insb; [ exact Hc2 | eapply isb_here_ee; eauto | eauto | eauto ].
  - inverts Hk.
    forwards~ Hwi: wfe_sinv Hw.
    forwards~ Hwt2: lrel_wfe Hl Hwi.
    match goal with Hlk: lookt T1 _ _ |- _ =>
      forwards~ (C&Hc1&Hc2): IHHl Hwi Hlk end.
    exists (tshift 0 C). split.
    + eapply lookt_etvar; eauto.
    + eapply shift_tvar_both;
        [ exact Hc2 | eapply ib_here2 | eapply we_tvar; exact Hwt2 | exact Hw ].
  - assert (Hk1: lookt T1 n A0).
    { eapply del_lookt_inv; eauto. econstructor. eapply del_refl. }
    forwards~ Hwi: wfe_inv Hw.
    forwards~ (C&Hc1&Hc2): IHHl Hwi Hk1.
    exists C. split*.
    eapply add_evar_teq with (T1:=T2).
    eapply teq_sym. eapply teq_sym in Hc2.
    eapply add_evar_teq; eauto.
    econstructor. eapply add_evar_refl; eauto. eapply teq_wft_left; eauto.
    econstructor. eapply add_evar_refl; eauto. eapply teq_wft_right; eauto.
  - assert (Hk1: lookt T1 n A0).
    { eapply del_lookt_inv; eauto. econstructor. eapply del_refl. }
    forwards~ Hwi: wfe_inv Hw.
    forwards~ (B&Hb1&Hb2): IHHl Hwi Hk1.
    exists B. split*.
    eapply adde_teq_sp_r; eauto.
    eapply add_evar_wft; eauto.
    eapply teq_wft_right; eauto.
    econstructor. eapply add_evar_refl; eauto.
    eapply wfe_evar_eteq; eauto.
Qed.

Lemma lrel_app2: forall T1 T2,
  lrel T1 T2 -> forall T3 T4,
  teq T1 T3 T4 T2 ->
  lshape T3 ->
  lshape T4 ->
  lrel (T1 +++ T3) (T2 +++ T4).
Proof.
  introv Hl1 Hl2 Hs1 Hs2. inductions Hl2;
  try solve [inverts* Hs1];
  try solve [inverts* Hs2].
  - rewrite <- mcon_cons. rewrite <- mcon_cons.
    destruct* m.
  - rewrite <- mcon_cons_st. rewrite <- mcon_cons_st.
    econstructor; eauto.
Qed.

Lemma teq_mani_inv: forall T1 A B C T2,
  teq T1 (mani A B) C T2 ->
  teq (T1 &= A) B (tshift 0 C) (T2 &s).
Proof.
  exact teq_mani_inv_l.
Qed.


Fixpoint size_t (A: typ) : nat :=
  match A with
    | int => 1
    | tvar _ => 1
    | arr A B => S (size_t A + size_t B)
    | all B => S (size_t B)
    | boxt A B => S (size_t B)
    | mani A B => S (size_t A + size_t B)
    | and A m B => S (size_t A + size_t B)
    | A1&s => S (size_t A1)
    | top => 1
    | rcd l A => S (size_t A)
  end.

Lemma size_t_pos: forall A,
  size_t A > 0.
Proof.
  intros A. inductions A; eauto; try solve [simpl in *; lia].
Qed.


Lemma size_t_and: forall T A m n,
  size_t (and T m A) <= S n ->
  size_t T <= n /\ size_t A <= n.
Proof.
  introv Hs. split.
  - forwards~ Hp: size_t_pos A.
    simpl in Hs.
    destruct* m; try lia.
  - simpl in Hs. lia.
Qed.

Lemma size_t_tshift: forall A X,
  size_t (tshift X A) = size_t A.
Proof.
  inductions A; introv; simpl;
    try solve [reflexivity];
    try solve [destruct (le_gt_dec X n); reflexivity];
    try solve [rewrite IHA; reflexivity];
    try solve [rewrite IHA1; rewrite IHA2; reflexivity].
  - destruct m; simpl; rewrite IHA1; rewrite IHA2; reflexivity.
Qed.

Lemma lrel_eq_size: forall n T A,
  size_t A <= n ->
  teq T A A T -> forall T1,
  lrel T T1 ->
  teq T A A T1.
Proof.
  intros n. inductions n; introv Hlen Ht Hl; intros.
  forwards~: size_t_pos A. lia.

  inverts Ht;
    try solve [match goal with
        Hwb: wft _ (boxt ?T3 ?A0) |- teq _ (boxt ?T3 ?A0) (boxt ?T3 ?A0) _ =>
          forwards~ Hrig0: wft_box_rigid Hwb;
          forwards~ (HwT0 & HwA0 & HwfeT0): boxt_wft_inv Hwb;
          eapply teq_boxbox;
            [ eapply teq_refl; unfold wft; eassumption
            | unfold wft; exact Hwb
            | unfold wft; eapply we_box; [ exact HwT0 | exact Hrig0 | eapply lrel_wfe; eauto ] ] end];
    try solve [forwards~: lrel_wfe Hl]; try solve [eauto].
  - (* eq_tvar : positional ; transfer check along lrel *)
    eapply eq_tvar; [ exact H | eapply lrel_wfe; eauto | exact H1 | eapply check_lrel; eauto ].
  - forwards~: teq_wfe_left H0.
    forwards~ (B&?&?): lookt_lrel_gen Hl H.
    eapply eq_eql; eauto.
    eapply eq_eqr; eauto.
    eapply teq_sym; eauto.
  - forwards~: teq_wfe_left H0.
    forwards~ (C&?&?): lookt_lrel_gen Hl H.
    eapply eq_eql; eauto.
    eapply eq_eqr; eauto.
    eapply teq_sym; eauto.
  - econstructor; eauto.
    eapply IHn; eauto. simpl in Hlen. lia.
    eapply IHn; eauto. simpl in Hlen. lia.
  - econstructor; eauto.
    eapply IHn; eauto. simpl in Hlen. lia.
  - (* mani, derived via eq_manil (H carries the mani on the RIGHT, padded).
       Invert to the exchanged body, then transitively transfer the right ambient
       T -> T1 with a reflexive bridge built by the IH; recompose via manil+manir. *)
    rename A0 into A0m. rename B into Bm.
    assert (Hbody: teq ((T &= A0m) &s) (tshift 0 Bm) (tshift 1 Bm) ((T &s) &= tshift 0 A0m)).
    { forwards HH: teq_mani_inv_r H. simpl in HH. exact HH. }
    simpl in Hlen.
    assert (HlB: size_t Bm <= n) by lia.
    assert (HlA0: size_t A0m <= n) by lia.
    forwards Hwa0: teq_wfe_left H.
    forwards Hwt: wfe_inv Hwa0.
    assert (HA0s: teq (T &s) (tshift 0 A0m) (tshift 0 A0m) (T1 &s)).
    { eapply IHn with (A := tshift 0 A0m).
      - rewrite size_t_tshift; exact HlA0.
      - eapply teq_refl. unfold wft.
        eapply insert_tvar_wft; [ eapply itv_here2 | eapply we_tvar; exact Hwt | exact Hwa0 ].
      - eapply lrel_etvar; exact Hl. }
    assert (HlrelR: lrel ((T &s) &= tshift 0 A0m) ((T1 &s) &= tshift 0 A0m)).
    { eapply lrel_eteq; [ eapply lrel_etvar; exact Hl | exact HA0s ]. }
    forwards HwftBodyR: teq_wft_right Hbody.
    assert (Hbridge: teq ((T &s) &= tshift 0 A0m) (tshift 1 Bm) (tshift 1 Bm) ((T1 &s) &= tshift 0 A0m)).
    { eapply IHn with (A := tshift 1 Bm).
      - rewrite size_t_tshift; exact HlB.
      - eapply teq_refl. unfold wft. exact HwftBodyR.
      - exact HlrelR. }
    forwards Hfull: teq_trans Hbody Hbridge.
    eapply eq_manil. simpl. eapply eq_manir. exact Hfull.
  - (* mani, derived via eq_manir (H carries the mani on the LEFT, padded).
       Symmetric to the previous case. *)
    rename A0 into A0m. rename C into Cm.
    assert (Hbody: teq ((T &s) &= tshift 0 A0m) (tshift 1 Cm) (tshift 0 Cm) ((T &= A0m) &s)).
    { forwards HH: teq_mani_inv H. simpl in HH. exact HH. }
    simpl in Hlen.
    assert (HlC: size_t Cm <= n) by lia.
    assert (HlA0: size_t A0m <= n) by lia.
    forwards Hwt0: teq_wfe_right H.
    forwards Hwt: wfe_inv Hwt0.
    assert (HA0s: teq T A0m A0m T1).
    { eapply IHn with (A := A0m); [ exact HlA0 | eapply teq_refl; unfold wft; exact Hwt0 | exact Hl ]. }
    assert (HlrelR: lrel ((T &= A0m) &s) ((T1 &= A0m) &s)).
    { eapply lrel_etvar. eapply lrel_eteq; [ exact Hl | exact HA0s ]. }
    assert (Hbridge: teq ((T &= A0m) &s) (tshift 0 Cm) (tshift 0 Cm) ((T1 &= A0m) &s)).
    { eapply IHn with (A := tshift 0 Cm).
      - rewrite size_t_tshift; exact HlC.
      - eapply teq_refl. unfold wft. eapply teq_wft_right. exact Hbody.
      - exact HlrelR. }
    forwards Hfull: teq_trans Hbody Hbridge.
    eapply eq_manir. simpl. eapply eq_manil. exact Hfull.
  - forwards~ (?&?): size_t_and Hlen.
    econstructor; eauto. eapply IHn; eauto.
    eapply lrel_app2; eauto.
  - econstructor; eauto. eapply IHn; eauto.
    simpl in *. lia.
  - econstructor; eauto. eapply IHn; eauto. simpl in Hlen. lia.
Qed.

Lemma lrel_eq: forall T A,
  teq T A A T -> forall T1,
  lrel T T1 ->
  teq T A A T1.
Proof.
  intros. eapply lrel_eq_size; eauto.
Qed.

Lemma lrel_wft: forall T1 T2,
  lrel T1 T2 -> forall A,
  wft T1 A ->
  wft T2 A.
Proof.
  intros. unfold wft in *.
  eapply lrel_wfe; eauto. econstructor; eauto.
  eapply lrel_eq; eauto.
  eapply teq_refl; eauto.
Qed.


Lemma vtyp_refl: forall T A,
  wft T A -> forall ve,
  has_type top ve T ->
  value ve ->
  lshape T ->
  teq (c2g ve) A A T.
Proof.
  intros. eapply teq_sym.
  eapply lrel_eq; eauto.
  - eapply teq_refl; eauto.
  - eapply vtyp_lrel; eauto.
Qed.

(* The value's type, reframed to its own concrete frame [c2g ve], is RIGID:
   [c2g ve] has num_of_abs 0, so wft over it = rigid (rigid_of_wft).  This
   discharges the rigidity gate of the box rules for free on value types,
   resolving the value-concreteness design tension for the c2g frame. *)
Lemma vtyp_rigid: forall T A,
  wft T A -> forall ve,
  has_type top ve T ->
  lshape T ->
  value ve ->
  rigid 0 (c2g ve) A.
Proof.
  introv Hw Ht Hs Hv.
  eapply rigid_of_wft.
  - eapply c2g_num0.
  - eapply lrel_wft; eauto. eapply vtyp_lrel; eauto.
Qed.

Lemma vtyp_eq: forall T A,
  wft T A -> forall ve,
  has_type top ve T ->
  lshape T ->
  value ve -> forall T1,
  wfe T1 ->
  rigid 0 (c2g ve) A ->
  teq T1 (boxt (c2g ve) A) A T.
Proof.
  introv Hw Ht Hs Hl Hwe Hrig.
  forwards Hr: vtyp_refl Hw Ht Hl Hs; auto.
  forwards HwcA: teq_wft_left Hr.
  eapply eq_boxl; eauto.
  unfold wft. eapply we_box; eauto.
Qed.

Lemma vtyp_wft: forall T A,
  wft T A -> forall ve,
  has_type top ve T ->
  lshape T ->
  value ve -> forall T1,
  wfe T1 ->
  rigid 0 (c2g ve) A ->
  wft T1 (boxt (c2g ve) A).
Proof.
  intros. econstructor; eauto.
  - eapply lrel_wft; eauto.
    eapply vtyp_lrel; eauto.
Qed.

(* Convenience wrappers that DISCHARGE the rigidity premise internally via
   vtyp_rigid (value over a concrete c2g frame is always rigid). *)
Lemma vtyp_eq_c: forall T A,
  wft T A -> forall ve,
  has_type top ve T ->
  lshape T ->
  value ve -> forall T1,
  wfe T1 ->
  teq T1 (boxt (c2g ve) A) A T.
Proof.
  intros. eapply vtyp_eq; eauto. eapply vtyp_rigid; eauto.
Qed.

Lemma vtyp_wft_c: forall T A,
  wft T A -> forall ve,
  has_type top ve T ->
  lshape T ->
  value ve -> forall T1,
  wfe T1 ->
  wft T1 (boxt (c2g ve) A).
Proof.
  intros. eapply vtyp_wft; eauto. eapply vtyp_rigid; eauto.
Qed.


Lemma teq_swap_left_int: forall T1 B T2,
  teq T1 int B T2 -> forall T1', wfe T1' -> teq T1' int B T2.
Proof.
  introv Ht. remember int as I. inductions Ht; introv Hwfe; try solve [inverts HeqI];
    try solve [econstructor; eauto];
  (* eq_boxr (~rbox-free): box on the RIGHT; box-wft on the untouched RHS ambient
     is a hypothesis; body re-ambients via the IH. *)
  try solve [ subst A; eapply eq_boxr; eauto ];
  (* eq_manir: int on the LEFT (B = int); &s-pad the swapped left ambient. *)
  try solve [ subst B; simpl in *; eapply eq_manir;
              eapply IHHt; [ reflexivity | eapply we_tvar; exact Hwfe ] ].
Qed.

Lemma teq_swap_left_top: forall T1 B T2,
  teq T1 top B T2 -> forall T1', wfe T1' -> teq T1' top B T2.
Proof.
  introv Ht. remember top as I. inductions Ht; introv Hwfe; try solve [inverts HeqI];
    try solve [econstructor; eauto];
  (* eq_boxr (~rbox-free): box on the RIGHT; box-wft on the untouched RHS ambient
     is a hypothesis; body re-ambients via the IH. *)
  try solve [ subst A; eapply eq_boxr; eauto ];
  (* eq_manir: top on the LEFT (B = top); &s-pad the swapped left ambient. *)
  try solve [ subst B; simpl in *; eapply eq_manir;
              eapply IHHt; [ reflexivity | eapply we_tvar; exact Hwfe ] ].
Qed.

(* teq_swap_left_box: a closed box LHS may swap its outer LEFT ambient
   freely (it is ambient-independent). *)
Lemma teq_swap_left_box: forall T1 T3 A C T2,
  teq T1 (boxt T3 A) C T2 -> forall T1', wfe T1' -> teq T1' (boxt T3 A) C T2.
Proof.
  introv Ht. remember (boxt T3 A) as BX. inductions Ht; introv Hwfe;
    try solve [inverts HeqBX];
    try solve [econstructor; eauto];
  try solve [
    eapply eq_boxl;
      [ eassumption
      | match goal with H: wft _ (boxt ?T0 ?A0) |- _ =>
          forwards~ (HwT0 & ? & ?): boxt_wft_inv H;
          forwards~ HrigBX: wft_box_rigid H end;
        unfold wft; eapply we_box; eauto ] ];
  (* eq_manir: box on the LEFT (B = boxt T3 A, tshift-invariant); &s-pad swapped left ambient. *)
  try solve [ subst B; simpl in *; eapply eq_manir;
              eapply IHHt; [ reflexivity | eapply we_tvar; exact Hwfe ] ].
Qed.

(* ==================================================================== *)
(* CANONICAL-TYPE BRIDGES: for each value form, the natural concrete type *)
(* relates (teq, same ambient) to ANY type the value can be subsumed to.  *)
(* These absorb t_eq subsumption, exposing the value's structural type.   *)
(* ==================================================================== *)
Lemma lit_teq_int1: forall T n A, has_type T (lit n) A -> teq T int A T.
Proof. introv Ht. remember (lit n) as e. induction Ht; try solve [inverts Heqe].
  - eapply eq_int; eauto.
  - eapply teq_trans; [ eapply IHHt; eauto | exact H ]. Qed.

Lemma unit_teq_top1: forall T A, has_type T unit A -> teq T top A T.
Proof. introv Ht. remember unit as e. induction Ht; try solve [inverts Heqe].
  - eapply teq_trans; [ eapply IHHt; eauto | exact H ].
  - eapply eq_top; eauto. Qed.

Lemma clos_teq_box1: forall T E e A, has_type T (clos E e) A ->
  exists Tb Ab Bb, teq T (boxt Tb (arr Ab Bb)) A T /\ wft T (boxt Tb (arr Ab Bb)) /\ has_type T (clos E e) (boxt Tb (arr Ab Bb)).
Proof. introv Ht. remember (clos E e) as ec. induction Ht; try solve [inverts Heqec].
  - inverts Heqec. exists T1 A B. splits.
    + eapply teq_refl. eapply typ_ans_wft. eapply t_clos; eauto.
    + eapply typ_ans_wft. eapply t_clos; eauto.
    + eapply t_clos; eauto.
  - forwards~ (Tb&Ab&Bb&Hteq&Hwft&Hty): IHHt. exists Tb Ab Bb. splits; eauto.
    eapply teq_trans; [ exact Hteq | exact H ]. Qed.

Lemma bclos_teq_box1: forall T E e A, has_type T (bclos E e) A ->
  exists Tb Ab, teq T (boxt Tb (all Ab)) A T /\ wft T (boxt Tb (all Ab)) /\ has_type T (bclos E e) (boxt Tb (all Ab)).
Proof. introv Ht. remember (bclos E e) as ec. induction Ht; try solve [inverts Heqec].
  - inverts Heqec. exists T1 A. splits.
    + eapply teq_refl. eapply typ_ans_wft. eapply t_bclos; eauto.
    + eapply typ_ans_wft. eapply t_bclos; eauto.
    + eapply t_bclos; eauto.
  - forwards~ (Tb&Ab&Hteq&Hwft&Hty): IHHt. exists Tb Ab. splits; eauto.
    eapply teq_trans; [ exact Hteq | exact H ]. Qed.

Lemma rec_teq_rcd1: forall T l v A, has_type T (rec l v) A ->
  exists Bbody, teq T (rcd l Bbody) A T /\ has_type T v Bbody.
Proof. introv Ht. remember (rec l v) as ec. induction Ht; try solve [inverts Heqec].
  - forwards~ (Bbody&Hteq&Hty): IHHt. exists Bbody. splits; eauto.
    eapply teq_trans; [ exact Hteq | exact H ].
  - inverts Heqec. exists A. splits; eauto.
    eapply teq_refl. eapply typ_ans_wft. eapply t_rec; eauto. Qed.

Lemma tmerge_teq1: forall T E A C, has_type T (E ;; A) C ->
  exists T1, has_type T E T1 /\ lshape T1 /\ wft (T +++ T1) A /\ teq T (T1 &= A) C T.
Proof. introv Ht. remember (E ;; A) as ec. induction Ht; try solve [inverts Heqec].
  - forwards~ (T1&HtE&Hls&Hwf&Hteq): IHHt. exists T1. splits; eauto.
    eapply teq_trans; [ exact Hteq | exact H ].
  - inverts Heqec. exists T1. splits; eauto.
    eapply teq_refl. eapply typ_ans_wft. eapply lt_const; eauto. Qed.

Lemma merge_teq1: forall T E v C, has_type T (E ,, v) C ->
  exists T1 A, has_type T E T1 /\ lshape T1 /\ has_type (T +++ T1) v A /\ teq T (T1 & A) C T.
Proof. introv Ht. remember (E ,, v) as ec. induction Ht; try solve [inverts Heqec].
  - destruct (IHHt Heqec) as (T1&A0&HtE&Hls&Htv&Hteq).
    exists T1 A0. splits; eauto.
    eapply teq_trans; [ exact Hteq | exact H ].
  - inverts Heqec. exists T1 A. splits; eauto.
    eapply teq_refl. eapply typ_ans_wft. eapply lt_conse; eauto. Qed.

Lemma teq_num0: forall T1 A B T2, teq T1 A B T2 ->
  num_of_abs A = 0 ->
  (forall X, A <> tvar X) ->
  (forall P Q, A <> boxt P Q) ->
  (forall P Q, A <> mani P Q) ->
  num_of_abs B = 0.
Proof.
  introv Ht. induction Ht; introv Hn Hv Hbx Hmn; eauto;
    try solve [false; eapply (Hv 0); reflexivity];
    try solve [false; eapply Hv; reflexivity];
    try solve [false; eapply Hbx; reflexivity];
    try solve [false; eapply Hmn; reflexivity];
    try reflexivity.
  - simpl in *.
    assert (HnT3: num_of_abs T3 = 0) by (destruct m; exact Hn).
    assert (HnT4: num_of_abs T4 = 0).
    { eapply IHHt1; eauto; inverts H; try (intros; discriminate);
      simpl in HnT3; lia. }
    destruct m; rewrite HnT4; reflexivity.
  - simpl in Hn. lia.
Qed.

Lemma teq_num0_box: forall T1 P Q B T2, teq T1 (boxt P Q) B T2 ->
  (forall X, Q <> tvar X) -> (forall R S, Q <> boxt R S) -> (forall R S, Q <> mani R S) ->
  num_of_abs Q = 0 ->
  num_of_abs B = 0.
Proof.
  introv Ht. remember (boxt P Q) as A eqn:HA.
  induction Ht; introv Hv Hbx Hmn Hn; try solve [inverts HA]; subst; eauto; try reflexivity.
  - inverts HA. eapply teq_num0; eauto.
Qed.

Lemma value_num0: forall T e A, has_type T e A -> value e -> num_of_abs T = 0 -> num_of_abs A = 0.
Proof.
  introv Ht Hval. gen T A. induction Hval; introv Ht Hnum.
  - (* lit *) forwards~ Hb: lit_teq_int1 Ht.
    eapply teq_num0; [ exact Hb | reflexivity | intros; discriminate | intros; discriminate | intros; discriminate ].
  - (* clos *) forwards~ (Tb&Ab&Bb&Hbteq&Hbwft&Hbty): clos_teq_box1 Ht.
    eapply teq_num0_box; [ exact Hbteq | intros; discriminate | intros; discriminate | intros; discriminate | reflexivity ].
  - (* bclos *) forwards~ (Tb&Ab&Hbteq&Hbwft&Hbty): bclos_teq_box1 Ht.
    eapply teq_num0_box; [ exact Hbteq | intros; discriminate | intros; discriminate | intros; discriminate | reflexivity ].
  - (* rec *) forwards~ (Bbody&Hbteq&Htv): rec_teq_rcd1 Ht.
    eapply teq_num0; [ exact Hbteq | reflexivity | intros; discriminate | intros; discriminate | intros; discriminate ].
  - (* unit *) forwards~ Hb: unit_teq_top1 Ht.
    eapply teq_num0; [ exact Hb | reflexivity | intros; discriminate | intros; discriminate | intros; discriminate ].
  - (* E ,, v *) forwards~ (T1&A0&HtE&Hls&Htv&Hbteq): merge_teq1 Ht.
    forwards~ HnT1: IHHval1 HtE Hnum.
    eapply teq_num0; [ exact Hbteq | simpl; exact HnT1 | intros; discriminate | intros; discriminate | intros; discriminate ].
  - (* E ;; boxt T A *) forwards~ (T1&HtE&Hls&HwfA&Hbteq): tmerge_teq1 Ht.
    forwards~ HnT1: IHHval HtE Hnum.
    eapply teq_num0; [ exact Hbteq | simpl; exact HnT1 | intros; discriminate | intros; discriminate | intros; discriminate ].
Qed.

(* A box-headed value (clos/bclos) is typed by a SELF-CONTAINED box whose
   frame is ambient-independent, so it may be re-typed at ANY wfe ambient. *)
Lemma clos_nat_prem: forall T E e A, has_type T (clos E e) A ->
  exists T1 Aa Bb, has_type top E T1 /\ has_type (T1 & Aa) e Bb /\ value E /\ rigid 0 T1 (arr Aa Bb) /\ teq T (boxt T1 (arr Aa Bb)) A T.
Proof. introv Ht. remember (clos E e) as ec. induction Ht; try solve [inverts Heqec].
  - inverts Heqec. exists T1 A B. splits; eauto. eapply teq_refl. eapply typ_ans_wft. eapply t_clos; eauto.
  - forwards~ (T1&Aa&Bb&HtE&Hte&Hve&Hrig&Hteq): IHHt. exists T1 Aa Bb. splits; eauto.
    eapply teq_trans; [ exact Hteq | exact H ]. Qed.

Lemma clos_reambient1: forall T E e Tb A, has_type T (clos E e) (boxt Tb A) -> forall T2, wfe T2 -> has_type T2 (clos E e) (boxt Tb A).
Proof. introv Ht Hwfe. forwards~ (T1&Aa&Bb&HtE&Hte&Hve&Hrig&Hteq): clos_nat_prem Ht.
  forwards~ Hc2: t_clos HtE Hte Hve Hrig Hwfe.
  eapply t_eq; [ exact Hc2 | ].
  eapply teq_swap_left_box in Hteq; [ | exact Hwfe ].
  eapply teq_sym in Hteq.
  eapply teq_swap_left_box in Hteq; [ | exact Hwfe ].
  eapply teq_sym in Hteq. exact Hteq. Qed.

Lemma bclos_nat_prem: forall T E e A, has_type T (bclos E e) A ->
  exists T1 Aa, has_type top E T1 /\ has_type (T1 &s) e Aa /\ value E /\ rigid 0 T1 (all Aa) /\ teq T (boxt T1 (all Aa)) A T.
Proof. introv Ht. remember (bclos E e) as ec. induction Ht; try solve [inverts Heqec].
  - inverts Heqec. exists T1 A. splits; eauto. eapply teq_refl. eapply typ_ans_wft. eapply t_bclos; eauto.
  - forwards~ (T1&Aa&HtE&Hte&Hve&Hrig&Hteq): IHHt. exists T1 Aa. splits; eauto.
    eapply teq_trans; [ exact Hteq | exact H ]. Qed.

Lemma bclos_reambient1: forall T E e Tb A, has_type T (bclos E e) (boxt Tb A) -> forall T2, wfe T2 -> has_type T2 (bclos E e) (boxt Tb A).
Proof. introv Ht Hwfe. forwards~ (T1&Aa&HtE&Hte&Hve&Hrig&Hteq): bclos_nat_prem Ht.
  forwards~ Hc2: t_bclos HtE Hte Hve Hrig Hwfe.
  eapply t_eq; [ exact Hc2 | ].
  eapply teq_swap_left_box in Hteq; [ | exact Hwfe ].
  eapply teq_sym in Hteq.
  eapply teq_swap_left_box in Hteq; [ | exact Hwfe ].
  eapply teq_sym in Hteq. exact Hteq. Qed.

(* exp_size: a structural size measure on exps, used to drive the
   value re-ambient keystone vrt by well-founded induction. *)
Fixpoint exp_size (e : exp) : nat :=
  match e with
  | lit _      => 1
  | var _      => 1
  | lam e1     => S (exp_size e1)
  | box e1 e2  => S (exp_size e1 + exp_size e2)
  | app e1 e2  => S (exp_size e1 + exp_size e2)
  | blam e1    => S (exp_size e1)
  | clos e1 e2 => S (exp_size e1 + exp_size e2)
  | bclos e1 e2=> S (exp_size e1 + exp_size e2)
  | tapp e1 _  => S (exp_size e1)
  | rec _ e1   => S (exp_size e1)
  | rproj e1 _ => S (exp_size e1)
  | unit       => 1
  | merge e1 e2=> S (exp_size e1 + exp_size e2)
  | tmerge e1 _=> S (exp_size e1)
  end.

(* ==================================================================== *)
(* lshape "non-shape" helpers for the leaf/box targets of                 *)
(* rigid_retype_bridge: when a value's canonical type (int/top/box-of-    *)
(* arrow/box-of-forall) is teq-related to the rigid frame body B, that B   *)
(* cannot be list-shaped (the conjunct [lshape B -> lshape D] is then      *)
(* discharged by deriving False, except for [unit] whose D = top IS        *)
(* lshape).  Proved by induction on the teq, peeling eq_eql/eq_boxl.       *)
(* ==================================================================== *)
Lemma int_teq_not_lshape: forall G1 B T3, teq G1 int B T3 -> lshape B -> False.
Proof.
  introv Ht. remember int as ii eqn:Hi. induction Ht; introv Hls; try solve [inverts Hi];
  try solve [inverts Hls]; try solve [eapply IHHt; eauto].
Qed.

Lemma arr_teq_not_lshape: forall G1 A0 B0 B T3, teq G1 (arr A0 B0) B T3 -> lshape B -> False.
Proof.
  introv Ht. remember (arr A0 B0) as aa eqn:Hi. induction Ht; introv Hls; try solve [inverts Hi];
  try solve [inverts Hls]; try solve [eapply IHHt; eauto].
Qed.

Lemma all_teq_not_lshape: forall G1 A0 B T3, teq G1 (all A0) B T3 -> lshape B -> False.
Proof.
  introv Ht. remember (all A0) as aa eqn:Hi. induction Ht; introv Hls; try solve [inverts Hi];
  try solve [inverts Hls]; try solve [eapply IHHt; eauto].
Qed.

Lemma boxarr_teq_not_lshape: forall G1 Tb A0 B0 B T3, teq G1 (boxt Tb (arr A0 B0)) B T3 -> lshape B -> False.
Proof.
  introv Ht. remember (boxt Tb (arr A0 B0)) as bb eqn:Hi. induction Ht; introv Hls; try solve [inverts Hi];
  try solve [inverts Hls]; try solve [eapply IHHt; eauto].
  inverts Hi. eapply arr_teq_not_lshape; eauto.
Qed.

Lemma boxall_teq_not_lshape: forall G1 Tb A0 B T3, teq G1 (boxt Tb (all A0)) B T3 -> lshape B -> False.
Proof.
  introv Ht. remember (boxt Tb (all A0)) as bb eqn:Hi. induction Ht; introv Hls; try solve [inverts Hi];
  try solve [inverts Hls]; try solve [eapply IHHt; eauto].
  inverts Hi. eapply all_teq_not_lshape; eauto.
Qed.

Lemma rcd_teq_not_lshape: forall G1 l A0 B T3, teq G1 (rcd l A0) B T3 -> lshape B -> False.
Proof.
  introv Ht. remember (rcd l A0) as rr eqn:Hi. induction Ht; introv Hls; try solve [inverts Hi];
  try solve [inverts Hls]; try solve [eapply IHHt; eauto].
Qed.

(* Every checked (abstract) variable index in T is below keyLen T, so
   [conc_above (keyLen T) T] holds for ANY T.  Combined with rigid_of_wft_gen
   this gives [rigid (keyLen T) T A] from [wft T A] WITHOUT a num0 side
   condition -- the depth-keyLen rigidity that the depth-generalized
   rigid_retype_bridge consumes to discharge the eq_manir (mani) targets. *)
Lemma check_lt_keyLen: forall X T, check T X -> X < keyLen T.
Proof. introv Hc. induction Hc; simpl; lia. Qed.

Lemma conc_above_keyLen: forall T, conc_above (keyLen T) T.
Proof. unfold conc_above; introv Hc. eapply check_lt_keyLen; exact Hc. Qed.

(* rigid at the natural depth keyLen from wft alone (no num0). *)
Lemma rigid_of_wft_keyLen: forall T A, wft T A -> rigid (keyLen T) T A.
Proof.
  introv Hw. eapply rigid_of_wft_gen with (n := bindings T A);
  [ lia | eapply conc_above_keyLen | exact Hw ].
Qed.

(* ==================================================================== *)
(* rigid_retype_bridge: the value-re-type KEYSTONE in BRIDGE form.        *)
(* A value [e] typed at the SOURCE ambient [G1] with type [A], related to *)
(* a RIGID type [B] at frame [T3] only by a BRIDGE [teq G1 A B T3], can   *)
(* be re-typed at ANY wfe ambient [T2] to a [D] that relates back to [B]  *)
(* over [T3] ([teq T2 D B T3]).  Getting [e] to [T3] IS the transport.    *)
(* ==================================================================== *)

Lemma value_insert: forall T e A,
  has_type T e A -> value e -> forall X T',
  insert_tvar X T T' -> wfe T' ->
  has_type T' e (tshift X A).
Proof.
  introv Ht. inductions Ht; introv Hval Hi Hwfe;
    try solve [inverts Hval].
  - (* t_int : lit i : int *)
    simpl. eapply t_int; exact Hwfe.
  - (* t_clos : boxt _ (arr ..) tshift-invariant; ambient T -> T' *)
    match goal with |- has_type _ _ (tshift _ (boxt ?Tb ?Ab)) =>
      assert (Hbe: tshift X (boxt Tb Ab) = boxt Tb Ab) by reflexivity end.
    rewrite Hbe. eapply t_clos; eauto.
  - (* t_bclos *)
    match goal with |- has_type _ _ (tshift _ (boxt ?Tb ?Ab)) =>
      assert (Hbe: tshift X (boxt Tb Ab) = boxt Tb Ab) by reflexivity end.
    rewrite Hbe. eapply t_bclos; eauto.
  - (* t_eq : recurse on body typing, then re-equate via the inserted (diagonal) teq *)
    eapply t_eq.
    + eapply IHHt; [ exact Hval | exact Hi | exact Hwfe ].
    + eapply shift_tvar_both; [ exact H | eapply ib_diag; exact Hi | exact Hwfe | exact Hwfe ].
  - (* lt_nil : unit : top *)
    simpl. eapply lt_nil; exact Hwfe.
  - (* lt_conse : E,,v : T1 & A *)
    inverts Hval. rewrite tshift_and.
    forwards Hins: insert_tvar_env Hi T1.
    eapply lt_conse.
    + eapply IHHt1; eauto.
    + eapply lshape_tshift; eauto.
    + eapply IHHt2;
        [ eassumption | exact Hins
        | eapply itvar_wfe; [ exact Hins | eapply typ_wfe; exact Ht2 ] ].
  - (* lt_const : E;;A (value form: A a box) : T1 &= A *)
    inverts Hval. rewrite tshift_and.
    forwards Hins: insert_tvar_env Hi T1.
    eapply lt_const.
    + eapply IHHt; eauto.
    + eapply lshape_tshift; eauto.
    + eapply insert_tvar_wft;
        [ exact Hins | eapply itvar_wfe; [ exact Hins | eapply wft_wfe; exact H0 ] | exact H0 ].
  - (* t_rec : rec l e : rcd l A *)
    inverts Hval. simpl. eapply t_rec. eapply IHHt; eauto.
Qed.

(* ==================================================================== *)
(* COMBINED keystone: vd (value de-insertion, general insl) + bridge      *)
(* (rigid_retype_bridge) + vrt (value re-ambient), by ONE well-founded    *)
(* induction on exp_size.  The IH supplies all three for strictly-smaller  *)
(* exps.  Per e we prove, in order: vd_e (uses IH only), br_e (uses IH +   *)
(* vd_e), vrt_e (uses br_e + IH).  vrt and rigid_retype_bridge are then    *)
(* projected back out as corollaries with their EXACT original statements. *)
(* ==================================================================== *)
Lemma vrt_bridge: forall e,
  (forall T' D', has_type T' e D' -> value e -> forall X T, insl X T T' -> wfe T ->
     exists A, has_type T e A /\ teq T' (tshift X A) D' T' /\ (lshape D' -> lshape A))
  /\ (forall A B G1 T3 T2 d,
     value e -> has_type G1 e A -> teq G1 A B T3 -> rigid d T3 B -> wft T3 B -> wfe T2 ->
     exists D, has_type T2 e D /\ teq T2 D B T3 /\ wft T2 D /\ (lshape B -> lshape D))
  /\ (forall G1 A B G2,
     has_type G1 e A -> value e -> teq G1 A B G2 -> wfe G2 -> has_type G2 e B).
Proof.
  intro e.
  induction e as [e IH] using (well_founded_induction (well_founded_ltof exp exp_size)).
  assert (IHvd : forall y, ltof exp exp_size y e ->
     forall T' D', has_type T' y D' -> value y -> forall X T, insl X T T' -> wfe T ->
       exists A, has_type T y A /\ teq T' (tshift X A) D' T' /\ (lshape D' -> lshape A))
    by (intros y Hy; exact (proj1 (IH y Hy))).
  assert (IHB : forall y, ltof exp exp_size y e ->
     forall A B G1 T3 T2 d, value y -> has_type G1 y A -> teq G1 A B T3 -> rigid d T3 B -> wft T3 B -> wfe T2 ->
       exists D, has_type T2 y D /\ teq T2 D B T3 /\ wft T2 D /\ (lshape B -> lshape D))
    by (intros y Hy; exact (proj1 (proj2 (IH y Hy)))).
  assert (IHV : forall y, ltof exp exp_size y e ->
     forall G1 A B G2, has_type G1 y A -> value y -> teq G1 A B G2 -> wfe G2 -> has_type G2 y B)
    by (intros y Hy; exact (proj2 (proj2 (IH y Hy)))).
  clear IH.
  assert (vd_e : forall T' D', has_type T' e D' -> value e -> forall X T, insl X T T' -> wfe T ->
     exists A, has_type T e A /\ teq T' (tshift X A) D' T' /\ (lshape D' -> lshape A)).
  {
    introv Ht Hval.
    destruct Hval; introv Hi Hwfe.
    - (* lit i *)
      forwards~ Hb: lit_teq_int1 Ht.
      exists int. splits.
      + eapply t_int; exact Hwfe.
      + simpl. exact Hb.
      + intro Hls; exfalso. eapply int_teq_not_lshape; [ exact Hb | exact Hls ].
    - (* clos E e *)
      forwards~ (Tb&Ab&Bb&Hbteq&Hbwft&Hbty): clos_teq_box1 Ht.
      assert (HwfeT: wfe T) by exact Hwfe.
      exists (boxt Tb (arr Ab Bb)). splits.
      + eapply clos_reambient1; [ exact Hbty | exact HwfeT ].
      + simpl. exact Hbteq.
      + intro Hls; exfalso. eapply boxarr_teq_not_lshape; [ exact Hbteq | exact Hls ].
    - (* bclos E e *)
      forwards~ (Tb&Ab&Hbteq&Hbwft&Hbty): bclos_teq_box1 Ht.
      assert (HwfeT: wfe T) by exact Hwfe.
      exists (boxt Tb (all Ab)). splits.
      + eapply bclos_reambient1; [ exact Hbty | exact HwfeT ].
      + simpl. exact Hbteq.
      + intro Hls; exfalso. eapply boxall_teq_not_lshape; [ exact Hbteq | exact Hls ].
    - (* rec l v *)
      forwards~ (Bbody&Hcanrcd&Htv): rec_teq_rcd1 Ht.
      assert (Hltv: ltof exp exp_size v (rec l v)) by (unfold ltof; simpl; lia).
      pose proof (IHvd v Hltv T' Bbody Htv Hval X T Hi Hwfe) as IHrec.
      destruct IHrec as (Aw&HtAw&HteqAw&HlsAw).
      exists (rcd l Aw). splits.
      + eapply t_rec; exact HtAw.
      + simpl. eapply teq_trans; [ eapply eq_rcd; exact HteqAw | exact Hcanrcd ].
      + intro Hls; exfalso. eapply rcd_teq_not_lshape; [ exact Hcanrcd | exact Hls ].
    - (* unit *)
      forwards~ Hb: unit_teq_top1 Ht.
      exists top. splits.
      + eapply lt_nil; exact Hwfe.
      + simpl. exact Hb.
      + intro Hls; econstructor.
    - (* E ,, v : bare element value *)
      forwards~ (T1&A0&HtE&HlsT1&Htv&Hcanand): merge_teq1 Ht.
      assert (HltE: ltof exp exp_size E (E,, v)) by (unfold ltof; simpl; lia).
      assert (Hltv: ltof exp exp_size v (E,, v)) by (unfold ltof; simpl; lia).
      pose proof (IHvd E HltE T' T1 HtE Hval1 X T Hi Hwfe) as IHe0.
      destruct IHe0 as (EA&HtEA&HteqEA&HlsEA0).
      forwards~ HlsEA: HlsEA0 HlsT1.
      assert (HlssEA: lshape (tshift X EA)) by (eapply lshape_tshift; exact HlsEA).
      forwards~ HwftA0: typ_ans_wft Htv.
      assert (HwfeTEA: wfe (T +++ EA)).
      { eapply wfe_to_mcon_all; eapply typ_ans_wft; exact HtEA. }
      assert (HwfeT'sEA: wfe (T' +++ tshift X EA)).
      { eapply wfe_to_mcon_all; eapply teq_wft_left; exact HteqEA. }
      assert (HwfeT'T1: wfe (T' +++ T1)) by (eapply typ_wfe; exact Htv).
      assert (HrefA0: teq (T' +++ T1) A0 A0 (T' +++ tshift X EA)).
      { eapply reframe_refl;
          [ eapply teq_sym; exact HteqEA | exact HlsT1 | exact HlssEA | exact HwftA0 | exact HwfeT'sEA ]. }
      pose proof (IHV v Hltv (T' +++ T1) A0 A0 (T' +++ tshift X EA) Htv Hval2 HrefA0 HwfeT'sEA) as Helt2.
      forwards~ Hins: insl_env Hi EA.
      pose proof (IHvd v Hltv (T' +++ tshift X EA) A0 Helt2 Hval2 (keyLen EA + X) (T +++ EA) Hins HwfeTEA) as IHv0.
      destruct IHv0 as (AW&HtAW&HteqAW0&HlsAW).
      assert (HrefAW: teq (T' +++ tshift X EA) A0 A0 (T' +++ T1)).
      { eapply reframe_refl;
          [ exact HteqEA | exact HlssEA | exact HlsT1
          | eapply teq_wft_right; exact HrefA0 | exact HwfeT'T1 ]. }
      assert (HteqAW: teq (T' +++ tshift X EA) (tshift (keyLen EA + X) AW) A0 (T' +++ T1)).
      { eapply teq_trans; [ exact HteqAW0 | exact HrefAW ]. }
      exists (EA & AW). splits.
      + eapply lt_conse; [ exact HtEA | exact HlsEA | exact HtAW ].
      + rewrite tshift_and.
        eapply teq_trans; [ | exact Hcanand ].
        eapply eq_and; [ exact HteqEA | exact HlssEA | exact HlsT1 | exact HteqAW ].
      + intro Hls; econstructor; exact HlsEA.
    - (* E ;; boxt T A : box element value (box frame named T, vd-frame is T0) *)
      forwards~ (T1&HtE&HlsT1&HwftBoxA&Hcantm): tmerge_teq1 Ht.
      assert (HltE: ltof exp exp_size E (E;; boxt T A)) by (unfold ltof; simpl; lia).
      pose proof (IHvd E HltE T' T1 HtE Hval X T0 Hi Hwfe) as IHe0.
      destruct IHe0 as (EA&HtEA&HteqEA&HlsEA0).
      forwards~ HlsEA: HlsEA0 HlsT1.
      assert (HlssEA: lshape (tshift X EA)) by (eapply lshape_tshift; exact HlsEA).
      assert (HwfeTEA: wfe (T0 +++ EA)).
      { eapply wfe_to_mcon_all; eapply typ_ans_wft; exact HtEA. }
      assert (HwfeT'sEA: wfe (T' +++ tshift X EA)).
      { eapply wfe_to_mcon_all; eapply teq_wft_left; exact HteqEA. }
      assert (HwfeT'T1: wfe (T' +++ T1)).
      { eapply wfe_to_mcon_all; eapply teq_wft_right; exact HteqEA. }
      forwards~ HrigA: wft_box_rigid HwftBoxA.
      forwards~ (HwT0 & HwA & HwfeBody): boxt_wft_inv HwftBoxA.
      assert (HwftBoxNew: wft (T0 +++ EA) (boxt T A)).
      { unfold wft. eapply we_box; [ exact HwT0 | exact HrigA | exact HwfeTEA ]. }
      exists (EA &= boxt T A). splits.
      + eapply lt_const; [ exact HtEA | exact HlsEA | exact HwftBoxNew ].
      + rewrite tshift_and.
        assert (Hboxsh: tshift (keyLen EA + X) (boxt T A) = boxt T A) by reflexivity.
        rewrite Hboxsh.
        eapply teq_trans; [ | exact Hcantm ].
        eapply eq_and; [ exact HteqEA | exact HlssEA | exact HlsT1 | ].
        eapply reframe_refl;
          [ exact HteqEA | exact HlssEA | exact HlsT1
          | unfold wft; eapply we_box; [ exact HwT0 | exact HrigA | exact HwfeT'sEA ]
          | exact HwfeT'T1 ].
      + intro Hls; econstructor; exact HlsEA.

  }
  assert (br_e : forall A B G1 T3 T2 d,
     value e -> has_type G1 e A -> teq G1 A B T3 -> rigid d T3 B -> wft T3 B -> wfe T2 ->
     exists D, has_type T2 e D /\ teq T2 D B T3 /\ wft T2 D /\ (lshape B -> lshape D)).
  {
    introv Hval Ht Hbr Hrig Hwft Hwfe.

  destruct Hval.
  - (* lit i : leaf int *)
    forwards~ Hb: lit_teq_int1 Ht.
    forwards~ HbrB: teq_trans Hb Hbr.
    exists int. splits.
    + eapply t_int; eauto.
    + eapply teq_swap_left_int; eauto.
    + unfold wft; eapply we_int; eauto.
    + intro Hls; exfalso. eapply int_teq_not_lshape; [ exact HbrB | exact Hls ].
  - (* clos E e : box source *)
    forwards~ (Tb&Ab&Bb&Hbteq&Hbwft&Hbty): clos_teq_box1 Ht.
    forwards~ HbrB: teq_trans Hbteq Hbr.
    exists (boxt Tb (arr Ab Bb)). splits.
    + eapply clos_reambient1; eauto.
    + eapply teq_swap_left_box; eauto.
    + eapply teq_wft_left; eapply teq_swap_left_box; [ exact HbrB | exact Hwfe ].
    + intro Hls; exfalso. eapply boxarr_teq_not_lshape; [ exact HbrB | exact Hls ].
  - (* bclos E e : box source *)
    forwards~ (Tb&Ab&Hbteq&Hbwft&Hbty): bclos_teq_box1 Ht.
    forwards~ HbrB: teq_trans Hbteq Hbr.
    exists (boxt Tb (all Ab)). splits.
    + eapply bclos_reambient1; eauto.
    + eapply teq_swap_left_box; eauto.
    + eapply teq_wft_left; eapply teq_swap_left_box; [ exact HbrB | exact Hwfe ].
    + intro Hls; exfalso. eapply boxall_teq_not_lshape; [ exact HbrB | exact Hls ].
  - (* rec l v : record *)
    forwards~ (Bbody&Hcanrcd&Htv): rec_teq_rcd1 Ht.
    forwards~ Hcan: teq_trans Hcanrcd Hbr.
    clear Hbr Ht Hcanrcd A.
    forwards~ (m & Hd): teq_teqd Hcan.
    clear Hcan.
    gen B T3 d. gen Bbody. gen G1. gen Hwfe. gen T2.
    induction m as [m IHm] using (well_founded_induction lt_wf).
    intros T2 Hwfe G1 Bbody Htv. introv Hwft Hd Hrig.
    inverts Hd.
    { (* eq_eqr : concrete tvar target *)
      forwards~ HrB0: rigid_lookt Hrig H;
      assert (HwB0: wft T3 B0) by (eapply lookt_wft; [ eapply wft_wfe; exact Hwft | exact H ]);
      assert (HltS: n < S n) by lia;
      lets IHa0: (IHm n HltS T2 Hwfe G1 Bbody Htv B0 T3 HwB0); lets IHa: IHa0 H0 d HrB0;
      destruct IHa as (Dv&HtDv&HteqDv&HwftDv&HlsDv);
      exists Dv; splits; [ exact HtDv | eapply eq_eqr; [ exact H | exact HteqDv ] | exact HwftDv | intro Hls; inverts Hls ]. }
    { (* eq_boxr (~rbox-free) : box target -- self-contained box body, rigid 0.
         Recurse on the body at frame T4 / depth 0, then re-box via eq_boxr. *)
      forwards~ (HwB0 & ? & ?): boxt_wft_inv H0;
      forwards~ Hr0: wft_box_rigid H0;
      assert (HltS: n < S n) by lia;
      lets IHa0: (IHm n HltS T2 Hwfe G1 Bbody Htv B0 T4 HwB0); lets IHa: IHa0 H 0 Hr0;
      destruct IHa as (Dv&HtDv&HteqDv&HwftDv&HlsDv);
      exists Dv; splits;
      [ exact HtDv
      | eapply eq_boxr; [ exact HteqDv | exact H0 ]
      | exact HwftDv
      | intro Hls; inverts Hls ]. }
    { (* eq_manir : mani target -- source padded (G1 &s), recurse, then de-insert via vd_e *)
      inverts Hrig as HrC;
      assert (HwftC: wft (T3 &= A) C) by (unfold wft; inverts Hwft as HwC; exact HwC);
      assert (HltS: n < S n) by lia;
      assert (Hwfe1: wfe (G1 &s)) by (eapply we_tvar; eapply typ_wfe; exact Htv);
      forwards~ Htv': (value_insert Htv Hval (@itv_here2 G1) Hwfe1);
      assert (Hwfe2: wfe (T2 &s)) by (eapply we_tvar; exact Hwfe);
      lets IHa0: (IHm n HltS (T2 &s) Hwfe2 (G1 &s) (tshift 0 Bbody) Htv' C (T3 &= A) HwftC);
      lets IHa: IHa0 H (S d) HrC;
      destruct IHa as (Dv&HtDv&HteqDv&HwftDv&HlsDv);
      forwards~ (Aw&HtAw&HteqAw&HlsAw): (vd_e (T2 &s) Dv HtDv (@vrec l v Hval) 0 T2 (isl_here_s T2) Hwfe);
      exists Aw; splits;
        [ exact HtAw
        | eapply eq_manir; eapply teq_trans; [ exact HteqAw | exact HteqDv ]
        | eapply typ_ans_wft; exact HtAw
        | intro Hls; inverts Hls ]. }
    { (* eq_rcd : structural recursion on the field via exp-size IH *)
      inverts Hrig as HrB;
      assert (HwftB0: wft T3 B0) by (unfold wft; inverts Hwft as HwB; exact HwB);
      forwards~ Hbody: teqd_teq H5;
      assert (Hlt: ltof exp exp_size v (rec l v)) by (unfold ltof; simpl; lia);
      lets IHa0: IHB v Hlt Hval Htv Hbody; lets IHa: IHa0 HrB HwftB0 Hwfe;
      destruct IHa as (Dv&HtDv&HteqDv&HwftDv&HlsDv);
      exists (rcd l Dv); splits;
      [ eapply t_rec; exact HtDv
      | eapply eq_rcd; exact HteqDv
      | unfold wft; unfold wft in HwftDv; eapply we_rcd; eauto
      | intro Hls; inverts Hls ]. }
  - (* unit : leaf top *)
    forwards~ Hb: unit_teq_top1 Ht.
    forwards~ HbrB: teq_trans Hb Hbr.
    exists top. splits.
    + eapply lt_nil; eauto.
    + eapply teq_swap_left_top; eauto.
    + unfold wft; eapply we_top; eauto.
    + intro Hls; econstructor.
  - (* E ,, v : list cons (bare element value) *)
    forwards~ (T1&A0&HtE&HlsT1&Htv&Hcanand): merge_teq1 Ht.
    forwards~ Hcan: teq_trans Hcanand Hbr.
    clear Hbr Ht Hcanand A.
    forwards~ (m & Hd): teq_teqd Hcan.
    clear Hcan.
    gen B T3 d. gen Htv HlsT1 HtE. gen A0 T1. gen G1. gen Hwfe. gen T2.
    induction m as [m IHm] using (well_founded_induction lt_wf).
    intros T2 Hwfe G1 A0 T1 Htv HlsT1 HtE. introv Hwft Hd Hrig.
    inverts Hd.
    { (* eq_eqr : concrete tvar target *)
      forwards~ HrB0: rigid_lookt Hrig H;
      assert (HwB0: wft T3 B0) by (eapply lookt_wft; [ eapply wft_wfe; exact Hwft | exact H ]);
      assert (HltS: n < S n) by lia;
      lets IHa0: (IHm n HltS T2 Hwfe G1 A0 T1 Htv HlsT1 HtE B0 T3 HwB0); lets IHa: IHa0 H0 d HrB0;
      destruct IHa as (Dv&HtDv&HteqDv&HwftDv&HlsDv);
      exists Dv; splits; [ exact HtDv | eapply eq_eqr; [ exact H | exact HteqDv ] | exact HwftDv | intro Hls; inverts Hls ]. }
    { (* eq_boxr (~rbox-free) : box target.  Re-box via eq_boxr. *)
      forwards~ (HwB0 & ? & ?): boxt_wft_inv H0;
      forwards~ Hr0: wft_box_rigid H0;
      assert (HltS: n < S n) by lia;
      lets IHa0: (IHm n HltS T2 Hwfe G1 A0 T1 Htv HlsT1 HtE B0 T5 HwB0); lets IHa: IHa0 H 0 Hr0;
      destruct IHa as (Dv&HtDv&HteqDv&HwftDv&HlsDv);
      exists Dv; splits;
      [ exact HtDv
      | eapply eq_boxr; [ exact HteqDv | exact H0 ]
      | exact HwftDv
      | intro Hls; inverts Hls ]. }
    { (* eq_manir : mani target -- source padded (G1 &s), recurse, de-insert via vd_e *)
      inverts Hrig as HrC;
      assert (HwftC: wft (T3 &= A) C) by (unfold wft; inverts Hwft as HwC; exact HwC);
      assert (HltS: n < S n) by lia;
      assert (Hwfe1: wfe (G1 &s)) by (eapply we_tvar; eapply typ_wfe; exact HtE);
      forwards~ HtE': (value_insert HtE Hval1 (@itv_here2 G1) Hwfe1);
      assert (Hwfe1': wfe ((G1 &s) +++ tshift 0 T1)) by (eapply wfe_to_mcon_all; eapply typ_ans_wft; exact HtE');
      forwards~ Htv': (value_insert Htv Hval2 (insert_tvar_env (@itv_here2 G1) T1) Hwfe1');
      assert (HlssT1: lshape (tshift 0 T1)) by (eapply lshape_tshift; exact HlsT1);
      assert (Hwfe2: wfe (T2 &s)) by (eapply we_tvar; exact Hwfe);
      lets IHa0: (IHm n HltS (T2 &s) Hwfe2 (G1 &s) (tshift (keyLen T1 + 0) A0) (tshift 0 T1) Htv' HlssT1 HtE' C (T3 &= A) HwftC);
      lets IHa: IHa0 H (S d) HrC;
      destruct IHa as (Dv&HtDv&HteqDv&HwftDv&HlsDv);
      forwards~ (Aw&HtAw&HteqAw&HlsAw): (vd_e (T2 &s) Dv HtDv (lvconsv Hval1 Hval2) 0 T2 (isl_here_s T2) Hwfe);
      exists Aw; splits;
        [ exact HtAw
        | eapply eq_manir; eapply teq_trans; [ exact HteqAw | exact HteqDv ]
        | eapply typ_ans_wft; exact HtAw
        | intro Hls; inverts Hls ]. }
    { (* eq_and : STRUCTURAL -- head/element via exp-size IH; depth threaded *)
      inverts Hrig as HrHead HrElt;
      inverts Hwft as HwHead HwElt HlsT6;
      forwards~ HheadTeq: teqd_teq H2;
      forwards~ HeltTeq: teqd_teq H9;
      assert (HwftT3T6: wft T3 T6) by (unfold wft; exact HwHead);
      assert (HwftT36B0: wft (T3+++T6) B0) by (unfold wft; exact HwElt);
      assert (HltE: ltof exp exp_size E (E,,v)) by (unfold ltof; simpl; lia);
      assert (Hltv: ltof exp exp_size v (E,,v)) by (unfold ltof; simpl; lia);
      lets IHE1: IHB E HltE Hval1 HtE HheadTeq; lets IHE2: IHE1 HrHead HwftT3T6 Hwfe;
      destruct IHE2 as (DE&HtDE&HteqDE&HwftDE&HlsDE0);
      forwards~ HlsDE: HlsDE0 H8;
      assert (HwfeT2DE: wfe (T2 +++ DE)) by (eapply wfe_to_mcon_all; exact HwftDE);
      lets IHv1: IHB v Hltv Hval2 Htv HeltTeq; lets IHv2: IHv1 HrElt HwftT36B0 HwfeT2DE;
      destruct IHv2 as (Delt&HtDelt&HteqDelt&HwftDelt&HlsDeltX);
      exists (DE & Delt); splits;
      [ eapply lt_conse; [ exact HtDE | exact HlsDE | exact HtDelt ]
      | eapply eq_and; [ exact HteqDE | exact HlsDE | exact H8 | exact HteqDelt ]
      | unfold wft; eapply we_and; [ unfold wft in HwftDE; exact HwftDE | unfold wft in HwftDelt; exact HwftDelt | exact HlsDE ]
      | intro Hls2; econstructor; exact HlsDE ]. }
  - (* E ;; boxt T A0 : list cons (box element) *)
    forwards~ (T1&HtE&HlsT1&HwftBoxA&Hcantm): tmerge_teq1 Ht.
    forwards~ Hcan: teq_trans Hcantm Hbr.
    clear Hbr Ht Hcantm A.
    forwards~ (m & Hd): teq_teqd Hcan.
    clear Hcan.
    gen B T3 d. gen HwftBoxA HlsT1 HtE. gen T1. gen G1. gen Hwfe. gen T2.
    induction m as [m IHm] using (well_founded_induction lt_wf).
    intros T2 Hwfe G1 T1 HwftBoxA HlsT1 HtE. introv Hwft Hd Hrig.
    inverts Hd.
    { (* eq_eqr *)
      forwards~ HrB0: rigid_lookt Hrig H;
      assert (HwB0: wft T3 B0) by (eapply lookt_wft; [ eapply wft_wfe; exact Hwft | exact H ]);
      assert (HltS: n < S n) by lia;
      lets IHa0: (IHm n HltS T2 Hwfe G1 T1 HwftBoxA HlsT1 HtE B0 T3 HwB0); lets IHa: IHa0 H0 d HrB0;
      destruct IHa as (Dv&HtDv&HteqDv&HwftDv&HlsDv);
      exists Dv; splits; [ exact HtDv | eapply eq_eqr; [ exact H | exact HteqDv ] | exact HwftDv | intro Hls; inverts Hls ]. }
    { (* eq_boxr (~rbox-free) : box target.  Re-box via eq_boxr. *)
      forwards~ (HwB0 & ? & ?): boxt_wft_inv H0;
      forwards~ Hr0: wft_box_rigid H0;
      assert (HltS: n < S n) by lia;
      lets IHa0: (IHm n HltS T2 Hwfe G1 T1 HwftBoxA HlsT1 HtE B0 T5 HwB0); lets IHa: IHa0 H 0 Hr0;
      destruct IHa as (Dv&HtDv&HteqDv&HwftDv&HlsDv);
      exists Dv; splits;
      [ exact HtDv
      | eapply eq_boxr; [ exact HteqDv | exact H0 ]
      | exact HwftDv
      | intro Hls; inverts Hls ]. }
    { (* eq_manir : mani target -- source padded (G1 &s), recurse, de-insert via vd_e *)
      inverts Hrig as HrC;
      assert (HwftC: wft (T3 &= A) C) by (unfold wft; inverts Hwft as HwC; exact HwC);
      assert (HltS: n < S n) by lia;
      assert (Hwfe1: wfe (G1 &s)) by (eapply we_tvar; eapply typ_wfe; exact HtE);
      forwards~ HtE': (value_insert HtE Hval (@itv_here2 G1) Hwfe1);
      assert (Hwfe1': wfe ((G1 &s) +++ tshift 0 T1)) by (eapply wfe_to_mcon_all; eapply typ_ans_wft; exact HtE');
      forwards~ HwftBoxA': (insert_tvar_wft (insert_tvar_env (@itv_here2 G1) T1) Hwfe1' HwftBoxA);
      assert (HlssT1: lshape (tshift 0 T1)) by (eapply lshape_tshift; exact HlsT1);
      assert (Hwfe2: wfe (T2 &s)) by (eapply we_tvar; exact Hwfe);
      lets IHa0: (IHm n HltS (T2 &s) Hwfe2 (G1 &s) (tshift 0 T1) HwftBoxA' HlssT1 HtE' C (T3 &= A) HwftC);
      lets IHa: IHa0 H (S d) HrC;
      destruct IHa as (Dv&HtDv&HteqDv&HwftDv&HlsDv);
      forwards~ (Aw&HtAw&HteqAw&HlsAw): (vd_e (T2 &s) Dv HtDv (@lvconst E T A0 Hval) 0 T2 (isl_here_s T2) Hwfe);
      exists Aw; splits;
        [ exact HtAw
        | eapply eq_manir; eapply teq_trans; [ exact HteqAw | exact HteqDv ]
        | eapply typ_ans_wft; exact HtAw
        | intro Hls; inverts Hls ]. }
    { (* eq_and : STRUCTURAL -- head E via exp-size IH; element is a
         self-contained box re-framed by teq_swap_left_box (left-ambient swap) *)
      inverts Hrig as HrHead HrElt;
      inverts Hwft as HwHead HwElt HlsT6;
      forwards~ HheadTeq: teqd_teq H2;
      forwards~ HeltTeq: teqd_teq H9;
      assert (HwftT3T6: wft T3 T6) by (unfold wft; exact HwHead);
      assert (HltE: ltof exp exp_size E (E;; boxt T A0)) by (unfold ltof; simpl; lia);
      lets IHE1: IHB E HltE Hval HtE HheadTeq; lets IHE2: IHE1 HrHead HwftT3T6 Hwfe;
      destruct IHE2 as (DE&HtDE&HteqDE&HwftDE&HlsDE0);
      forwards~ HlsDE: HlsDE0 H8;
      assert (HwfeT2DE: wfe (T2 +++ DE)) by (eapply wfe_to_mcon_all; exact HwftDE);
      forwards~ HwBel: teq_wft_right HeltTeq;
      assert (HeltSwap: teq (T2 +++ DE) (boxt T A0) B0 (T3 +++ T6)) by
        (eapply teq_swap_left_box; [ exact HeltTeq | exact HwfeT2DE ]);
      assert (HwftT2DEbox: wft (T2 +++ DE) (boxt T A0)) by
        (eapply teq_wft_left; exact HeltSwap);
      exists (DE &= boxt T A0); splits;
      [ eapply lt_const; [ exact HtDE | exact HlsDE | exact HwftT2DEbox ]
      | eapply eq_and; [ exact HteqDE | exact HlsDE | exact H8 | exact HeltSwap ]
      | unfold wft; eapply we_and; [ unfold wft in HwftDE; exact HwftDE | unfold wft in HwftT2DEbox; exact HwftT2DEbox | exact HlsDE ]
      | intro Hls2; econstructor; exact HlsDE ]. }
  }
  assert (vrt_e : forall G1 A B G2,
     has_type G1 e A -> value e -> teq G1 A B G2 -> wfe G2 -> has_type G2 e B).
  {
    introv Ht Hval Hteq Hwfe.

  destruct Hval.
  { (* lit i : leaf, int *)
    remember (lit i) as ei eqn:Hei.
    induction Ht; try solve [inverts Hei].
    - inverts Hei. eapply t_eq with (A := int).
      + eapply t_int; eauto.
      + eapply teq_swap_left_int; eauto.
    - eapply IHHt; eauto. eapply teq_trans; eauto. }
  { (* clos E e : box source *)
    remember (clos E e) as ec eqn:Hec.
    induction Ht; try solve [inverts Hec].
    - inverts Hec. eapply t_eq with (A := boxt T1 (arr A B0)).
      + eapply t_clos; eauto.
      + eapply teq_swap_left_box; eauto.
    - eapply IHHt; eauto. eapply teq_trans; eauto. }
  { (* bclos E e : box source *)
    remember (bclos E e) as ec eqn:Hec.
    induction Ht; try solve [inverts Hec].
    - inverts Hec. eapply t_eq with (A := boxt T1 (all A)).
      + eapply t_bclos; eauto.
      + eapply teq_swap_left_box; eauto.
    - eapply IHHt; eauto. eapply teq_trans; eauto. }
  - (* rec l v *)
    remember (rec l v) as er eqn:Her.
    induction Ht; try solve [inverts Her].
    + (* t_eq *) eapply IHHt; eauto. eapply teq_trans; eauto.
    + (* t_rec *)
      inverts Her.
      remember (rcd l A) as RA eqn:HRA.
      induction Hteq; try solve [inverts HRA].
      * (* eq_eqr : concrete tvar target -- retype via br_e then t_eq *)
        subst A0.
        assert (Htrec: has_type T1 (rec l v) (rcd l A)) by (eapply t_rec; exact Ht).
        assert (Hvrec: value (rec l v)) by (eapply vrec; exact Hval).
        forwards~ HwftC: teq_wft_right Hteq.
        forwards~ HrigC: rigid_of_wft_keyLen HwftC.
        lets HRB0: br_e Hvrec Htrec Hteq HrigC. lets HRB: HRB0 HwftC Hwfe.
        destruct HRB as (D & HtD & HteqD & HwftD & HlsD).
        eapply t_eq; [ exact HtD | eapply eq_eqr; [ exact H | exact HteqD ] ].
      * (* eq_boxr (~rbox-free) : box target on a record value -- via
           br_e, then re-box on the right via eq_boxr. *)
        subst A0.
        assert (Htrec: has_type T1 (rec l v) (rcd l A)) by (eapply t_rec; exact Ht).
        assert (Hvrec: value (rec l v)) by (eapply vrec; exact Hval).
        (* eq_boxr (new): box-wft [H : wft G2 (boxt T5 B0)] is the inverted premise.
           Recover the body wft + rigidity from it, retype the record at G2 via the
           bridge, then re-box on the right via eq_boxr supplying H. *)
        match goal with H: wft _ (boxt ?T5 ?B0) |- has_type _ _ (boxt ?T5 ?B0) =>
          forwards~ Hr0: wft_box_rigid H;
          forwards~ (Hwb0 & ? & ?): boxt_wft_inv H;
          lets HRB0: br_e Hvrec Htrec Hteq Hr0; lets HRB: HRB0 Hwb0 Hwfe;
          destruct HRB as (D & HtD & HteqD & HwftD & HlsD);
          eapply t_eq with (A := D); [ exact HtD | ];
          eapply eq_boxr; [ exact HteqD | exact H ] end.
      * (* eq_manir : mani target on a record value -- repackage via eq_manir,
           then retype the record at T2 via br_e at depth keyLen *)
        subst B.
        assert (Htrec: has_type T1 (rec l v) (rcd l A)) by (eapply t_rec; exact Ht).
        assert (Hvrec: value (rec l v)) by (eapply vrec; exact Hval).
        assert (Hmani: teq T1 (rcd l A) (mani A0 C) T2) by (eapply eq_manir; exact Hteq).
        forwards~ HwftM: teq_wft_right Hmani.
        forwards~ HrigM: rigid_of_wft_keyLen HwftM.
        lets HRB0: br_e Hvrec Htrec Hmani HrigM. lets HRB: HRB0 HwftM Hwfe.
        destruct HRB as (D & HtD & HteqD & HwftD & HlsD).
        eapply t_eq with (A := D); [ exact HtD | exact HteqD ].
      * (* eq_rcd : structural recursion on body via exp-size IH *)
        inverts HRA. eapply t_rec.
        eapply IHV; [ unfold ltof; simpl; lia | exact Ht | exact Hval | exact Hteq | exact Hwfe ].
  - (* unit : leaf, top *)
    remember unit as eu eqn:Heu.
    induction Ht; try solve [inverts Heu].
    + (* t_eq *) eapply IHHt; eauto. eapply teq_trans; eauto.
    + (* lt_nil *) inverts Heu. eapply t_eq with (A := top).
      eapply lt_nil; eauto.
      eapply teq_swap_left_top with (T1' := G2); [ exact Hteq | exact Hwfe ].
  - (* E ,, v : list cons (bare element value) *)
    remember (E,,v) as ec eqn:Hec.
    induction Ht; try solve [inverts Hec].
    + (* t_eq *) eapply IHHt; eauto. eapply teq_trans; eauto.
    + (* lt_conse *)
      inverts Hec.
      remember (T1 & A) as SA eqn:HSA.
      induction Hteq; try solve [inverts HSA].
      * (* eq_eqr : concrete tvar target -- retype via br_e then t_eq/eq_eqr *)
        subst A0.
        assert (Htlist: has_type T0 (E,, v) (T1 & A)) by (eapply lt_conse; [ exact Ht1 | exact H | exact Ht2 ]).
        assert (Hvlist: value (E,, v)) by (eapply lvconsv; [ exact Hval1 | exact Hval2 ]).
        forwards~ HwftC: teq_wft_right Hteq.
        forwards~ HrigC: rigid_of_wft_keyLen HwftC.
        lets HRB0: br_e Hvlist Htlist Hteq HrigC. lets HRB: HRB0 HwftC Hwfe.
        destruct HRB as (D & HtD & HteqD & HwftD & HlsD).
        eapply t_eq; [ exact HtD | eapply eq_eqr; [ exact H0 | exact HteqD ] ].
      * (* eq_boxr (~rbox-free) : box target on a bare-list value -- via
           br_e, then re-box on the right via eq_boxr. *)
        subst A0.
        assert (Htlist: has_type T0 (E,, v) (T1 & A)) by (eapply lt_conse; [ exact Ht1 | exact H | exact Ht2 ]).
        assert (Hvlist: value (E,, v)) by (eapply lvconsv; [ exact Hval1 | exact Hval2 ]).
        match goal with H': wft _ (boxt ?T5 ?B0) |- has_type _ _ (boxt ?T5 ?B0) =>
          forwards~ Hr0: wft_box_rigid H';
          forwards~ (Hwb0 & ? & ?): boxt_wft_inv H';
          lets HRB0: br_e Hvlist Htlist Hteq Hr0; lets HRB: HRB0 Hwb0 Hwfe;
          destruct HRB as (D & HtD & HteqD & HwftD & HlsD);
          eapply t_eq with (A := D); [ exact HtD | ];
          eapply eq_boxr; [ exact HteqD | exact H' ] end.
      * (* eq_manir : mani target on a bare-list value -- repackage via eq_manir
           then retype via br_e at depth keyLen *)
        subst B.
        assert (Htlist: has_type T0 (E,, v) (T1 & A)) by (eapply lt_conse; [ exact Ht1 | exact H | exact Ht2 ]).
        assert (Hvlist: value (E,, v)) by (eapply lvconsv; [ exact Hval1 | exact Hval2 ]).
        assert (Hmani: teq T0 (T1 & A) (mani A0 C) T2) by (eapply eq_manir; exact Hteq).
        forwards~ HwftM: teq_wft_right Hmani.
        forwards~ HrigM: rigid_of_wft_keyLen HwftM.
        lets HRB0: br_e Hvlist Htlist Hmani HrigM. lets HRB: HRB0 HwftM Hwfe.
        destruct HRB as (D & HtD & HteqD & HwftD & HlsD).
        eapply t_eq with (A := D); [ exact HtD | exact HteqD ].
      * (* eq_and : STRUCTURAL -- head and element via exp-size IH (head teq lands at T2) *)
        inverts HSA.
        forwards~ HwBel: teq_wft_right Hteq2.
        forwards~ HwfeT2T4: wft_wfe HwBel.
        eapply lt_conse.
        eapply IHV; [ unfold ltof; simpl; lia | exact Ht1 | exact Hval1 | exact Hteq1 | exact Hwfe ].
        exact H1.
        eapply IHV; [ unfold ltof; simpl; lia | exact Ht2 | exact Hval2 | exact Hteq2 | exact HwfeT2T4 ].
  - (* E ;; boxt T A0 : list cons (box element) *)
    remember (E;; boxt T A0) as ec eqn:Hec.
    induction Ht; try solve [inverts Hec].
    + (* t_eq *) eapply IHHt; eauto. eapply teq_trans; eauto.
    + (* lt_const *)
      inverts Hec.
      remember (T1 &= boxt T A0) as SA eqn:HSA.
      induction Hteq; try solve [inverts HSA].
      * (* eq_eqr : concrete tvar target -- retype via br_e then t_eq/eq_eqr *)
        subst A.
        assert (Htlist: has_type T0 (E;; boxt T A0) (T1 &= boxt T A0)) by (eapply lt_const; [ exact Ht | exact H | exact H0 ]).
        assert (Hvlist: value (E;; boxt T A0)) by (eapply lvconst; exact Hval).
        forwards~ HwftC: teq_wft_right Hteq.
        forwards~ HrigC: rigid_of_wft_keyLen HwftC.
        lets HRB0: br_e Hvlist Htlist Hteq HrigC. lets HRB: HRB0 HwftC Hwfe.
        destruct HRB as (D & HtD & HteqD & HwftD & HlsD).
        eapply t_eq; [ exact HtD | eapply eq_eqr; [ exact H1 | exact HteqD ] ].
      * (* eq_boxr (~rbox-free) : box target on a box-tail list value -- via
           br_e, then re-box on the right via eq_boxr. *)
        subst A.
        assert (Htlist: has_type T0 (E;; boxt T A0) (T1 &= boxt T A0)) by (eapply lt_const; [ exact Ht | exact H | exact H0 ]).
        assert (Hvlist: value (E;; boxt T A0)) by (eapply lvconst; exact Hval).
        match goal with H': wft _ (boxt ?T5 ?Bb) |- has_type _ _ (boxt ?T5 ?Bb) =>
          forwards~ Hr0: wft_box_rigid H';
          forwards~ (Hwb0 & ? & ?): boxt_wft_inv H';
          lets HRB0: br_e Hvlist Htlist Hteq Hr0; lets HRB: HRB0 Hwb0 Hwfe;
          destruct HRB as (D & HtD & HteqD & HwftD & HlsD);
          eapply t_eq with (A := D); [ exact HtD | ];
          eapply eq_boxr; [ exact HteqD | exact H' ] end.
      * (* eq_manir : mani target on a box-tail list value -- repackage via eq_manir
           then retype via br_e at depth keyLen *)
        subst B.
        assert (Htlist: has_type T0 (E;; boxt T A0) (T1 &= boxt T A0)) by (eapply lt_const; [ exact Ht | exact H | exact H0 ]).
        assert (Hvlist: value (E;; boxt T A0)) by (eapply lvconst; exact Hval).
        assert (Hmani: teq T0 (T1 &= boxt T A0) (mani A C) T2) by (eapply eq_manir; exact Hteq).
        forwards~ HwftM: teq_wft_right Hmani.
        forwards~ HrigM: rigid_of_wft_keyLen HwftM.
        lets HRB0: br_e Hvlist Htlist Hmani HrigM. lets HRB: HRB0 HwftM Hwfe.
        destruct HRB as (D & HtD & HteqD & HwftD & HlsD).
        eapply t_eq with (A := D); [ exact HtD | exact HteqD ].
      * (* eq_and : STRUCTURAL; element is a self-contained box -- via teq_swap_left_box *)
        inverts HSA.
        forwards~ HwBel: teq_wft_right Hteq2.
        forwards~ HwfeT2T4: wft_wfe HwBel.
        forwards~ HrigA0: wft_box_rigid H0.
        forwards~ (HwT & HwA0 & HwfeT0T1): boxt_wft_inv H0.
        assert (HheadT4: has_type T2 E T4).
        { eapply IHV; [ unfold ltof; simpl; lia | exact Ht | exact Hval | exact Hteq1 | exact Hwfe ]. }
        forwards~ HwftT2T4: typ_ans_wft HheadT4.
        forwards~ HwfeT2T4all: wfe_to_mcon_all HwftT2T4.
        assert (Helt: teq (T2 +++ T4) (boxt T A0) B (T2 +++ T4)).
        { eapply teq_swap_left_box; [ exact Hteq2 | exact HwfeT2T4all ]. }
        assert (HwftT2T4Box: wft (T2 +++ T4) (boxt T A0)).
        { unfold wft. eapply we_box; [ eauto | exact HrigA0 | exact HwfeT2T4all ]. }
        eapply t_eq with (A := T4 &= boxt T A0).
        eapply lt_const; [ exact HheadT4 | exact H2 | exact HwftT2T4Box ].
        eapply eq_and; [ eapply teq_refl; exact HwftT2T4 | exact H2 | exact H2 | exact Helt ].
  }
  splits; [ exact vd_e | exact br_e | exact vrt_e ].
Qed.

(* Project the three corollaries with their EXACT original statements. *)

Lemma vrt: forall e G1 A B G2,
  has_type G1 e A -> value e -> teq G1 A B G2 -> wfe G2 ->
  has_type G2 e B.
Proof. intro e. exact (proj2 (proj2 (vrt_bridge e))). Qed.

(* Value de-insertion corollary (projected from vrt_bridge). *)
Lemma vd: forall e T' D',
  has_type T' e D' -> value e -> forall X T, insl X T T' -> wfe T ->
  exists A, has_type T e A /\ teq T' (tshift X A) D' T' /\ (lshape D' -> lshape A).
Proof. intro e. exact (proj1 (vrt_bridge e)). Qed.


Lemma lt_closed_gen: forall T E A,
  has_type T E A -> forall T1,
  teq T A T1 T ->
  wfe T1 ->
  lshape T1 ->
  value E -> forall T2,
  wfe T2 ->
  has_type T2 E T1.
Proof.
  introv Ht. inductions Ht; introv Hteq Hwfe Hlsh Hval Hwfe2;
    try solve [ inverts Hval ];
    try solve [ exfalso; eapply lshape_int; eauto ].
  - (* t_clos: boxt T1 (arr A B) is not list-shaped; contradiction with lshape target *)
    exfalso.
    assert (Hc: has_type T (clos E1 e2) (boxt T1 (arr A B)))
      by (eapply t_clos; eauto).
    forwards Hc2: t_eq Hc Hteq.
    eapply typ_shape_clos; eauto.
  - (* t_bclos: boxt T1 (all A) is not list-shaped; contradiction *)
    exfalso.
    assert (Hc: has_type T (bclos E1 e2) (boxt T1 (all A)))
      by (eapply t_bclos; eauto).
    forwards Hc2: t_eq Hc Hteq.
    eapply typ_shape_bclos; eauto.
  - (* t_eq: chain the conversion through the induction hypothesis *)
    eapply IHHt; eauto. eapply teq_trans; eauto.
  - (* lt_nil: A = top, so the lshape target must be top as well *)
    forwards~ Heq: typ_shape_nil_aux (lt_nil H) Hteq.
    subst. eauto.
  - (* lt_conse. *)
    inverts Hteq; try solve [ inverts Hlsh ].
    inverts Hval.
    forwards~ HwfeT6: wfe_inv Hwfe.
    forwards~ Hsub: ambient_tail_subst H9 H3 H5 H8.
    eapply lt_conse.
    + eapply IHHt1; [ exact H3 | exact HwfeT6 | exact H8 | assumption | exact Hwfe2 ].
    + exact H8.
    + (* BARE-VALUE re-ambient of element e from [T+++T1] to [T2+++T6] at type B.
         Closed via the value-re-ambient keystone vrt: change the right-ambient
         PREFIX of the element teq from T to T2 (shared wft tail T6, via teq_old),
         then re-type e along the resulting bridge. *)
      assert (HwB6: wft T6 B) by (unfold wft; eapply wfe_evar_eteq; exact Hwfe).
      assert (HwfeT2T6: wfe (T2 +++ T6)) by (eapply wfe_app; [ exact HwfeT6 | exact Hwfe2 ]).
      forwards Hbridge: teq_old H9 HwB6 HwfeT2T6.
      eapply vrt; [ exact Ht2 | exact H4 | exact Hbridge | exact HwfeT2T6 ].
  - (* lt_const.  Symmetric to lt_conse: inverting eq_and gives the spine teq and the
       element wft mismatch; ambient_tail_subst aligns the tail.  Same value-concreteness
       re-ambient residual (here for the manifest element value). *)
    inverts Hteq; try solve [ inverts Hlsh ].
    inverts Hval.
    forwards~ HwfeT6: wfe_inv Hwfe.
    forwards~ Hsub: ambient_tail_subst H10 H4 H6 H9.
    forwards~ HheadT6: IHHt H4 HwfeT6 H9 H2 Hwfe2.
    forwards~ HwftT2T6: typ_ans_wft HheadT6.
    forwards~ HwfeT2T6: wfe_to_mcon_all HwftT2T6.
    assert (HwfeBox: wfe (T0 &= A0)) by (inverts H0; assumption).
    eapply t_eq with (A := T6 &= boxt T0 A0).
    + eapply lt_const; [ exact HheadT6 | exact H9
                       | unfold wft; eapply we_box;
                         [ eauto
                         | eapply wft_box_rigid; eapply teq_wft_left; exact Hsub
                         | eauto ] ].
    + eapply eq_and; [ eapply teq_refl; exact HwftT2T6
                     | exact H9 | exact H9 | ].
      (* goal : teq (T2+++T6) (boxt T0 A0) B (T2+++T6) ; we have
         Hsub : teq (T+++T1) (boxt T0 A0) B (T+++T1) and
         H10 : teq (T+++T1) (boxt T0 A0) B (T+++T6).  The element is ALREADY a box
         [boxt T0 A0] whose frame T0 is rigid (wft_box_rigid) and ambient-independent,
         and the box-removed type B is wft over the BARE spine T6 (prefix-free).
         teq_box_inv strips the box; teq_old changes the right ambient prefix T->T2
         (shared wft tail T6); ~rbox-free eq_boxl re-boxes the left. *)
      forwards~ HrigA0: wft_box_rigid H0.
      forwards~ (HwT0 & HwA0 & HwfeT0A0): boxt_wft_inv H0.
      forwards~ Hbi6: teq_box_inv H10.
      assert (HwB6: wft T6 B) by (unfold wft; exact Hwfe).
      forwards Hbi6t: teq_old Hbi6 HwB6 T2; [ exact HwfeT2T6 | ].
      forwards HwBT26: teq_wft_right Hbi6t.
      (* re-box the left via eq_boxl; the box-wft on ambient (T2+++T6) is rebuilt
         via we_box from the body wft (HwT0), rigidity (HrigA0), ambient (HwfeT2T6). *)
      eapply eq_boxl; [ exact Hbi6t | unfold wft; eapply we_box; [ exact HwT0 | exact HrigA0 | exact HwfeT2T6 ] ].
  - (* t_rec: rcd l A is not list-shaped; contradiction *)
    exfalso.
    forwards Hc: t_rec Ht.
    forwards Hc2: t_eq Hc Hteq.
    eapply typ_shape_rec; eauto.
Qed. 

Lemma lt_closed: forall T E T1,
  has_type T E T1 ->
  wfe T1 ->
  lshape T1 ->
  value E -> forall T2,
  wfe T2 ->
  has_type T2 E T1.
Proof.
  intros.
  eapply lt_closed_gen; eauto.
  eapply teq_refl; eauto.
  eapply typ_ans_wft; eauto.
Qed.


Lemma typ_concat: forall E1 T T1,
  has_type T E1 T1 ->
  lshape T1 ->
  value E1 -> forall E2 T2,
  has_type (T +++ T1) E2 T2 ->
  value E2 ->
  lshape T2 ->
  has_type T (E1 ++- E2) (T1 +++ T2).
Proof.
  intros E1 T T1 Ht1 Hl1 Hv1 E2.
  induction E2; introv Ht2 Hv2 Hl2;
    try solve [ inverts Hv2 ];
    try solve [ inverts Hl2 ];
    try solve [ exfalso; eapply typ_shape_lit;   eauto ];
    try solve [ exfalso; eapply typ_shape_clos;  eauto ];
    try solve [ exfalso; eapply typ_shape_bclos; eauto ];
    try solve [ exfalso; eapply typ_shape_rec;   eauto ].
  - (* E2 = unit: T2 must be top, and both econcat and (T1 +++ top) collapse *)
    forwards~ Heq: typ_shape_nil Ht2. subst.
    simpl. exact Ht1.
  - (* E2 = _ ,, _ : the last element is a BARE value; re-ambient it from the
       spine-Tq ambient to the spine-T4 ambient via the keystone vrt (the element
       teq from merge_inv directly bridges the two ambients).  Spine re-types via IH. *)
    inverts Hv2.
    forwards~ (B1 & T4 & HeqT2): merge_inv2 Ht2 Hl2. subst T2.
    forwards~ (v1 & ve & C & Tq & Heqv & Hv1' & Hve & Htv1 & Htve & Hspine & Helt): merge_inv Ht2.
    inverts Heqv.
    rewrite <- econ_cons.
    rewrite <- mcon_cons.
    inverts Helt.
    forwards~ Hhead: IHE2_1 Htve Hve.
    forwards~ HwBel: teq_wft_right H11.
    forwards~ HwfeElt: wft_wfe HwBel.
    forwards~ Helt2: vrt Htv1 Hv1' H11 HwfeElt.
    assert (HlsT1T4: lshape (T1 +++ T4)) by (eapply lshape_app; exact Hl1).
    rewrite mapp_ass in Helt2.
    eapply lt_conse. exact Hhead. exact HlsT1T4. exact Helt2.
  - (* E2 = _ ;; _ : the last element is a BOX [boxt T0 A] (self-contained rigid frame),
       so -- exactly like the lt_const case of lt_closed_gen -- it re-ambients via
       teq_box_inv + teq_old (here folded into the eq_and element re-box) + rbox_dec.
       The spine re-types via the IH; lt_const rebuilds the tlist. *)
    rewrite <- econ_cons_typ. inverts Hv2.
    forwards~ (B1&T4&HeqT2): tmerge_inv2 Ht2 Hl2. subst.
    forwards~ (B2&ve0&T5&Heqv&Hbx&Hve&Hwf&Hte&Hteq1&Hteq2): tmerge_inv Ht2.
    inverts Heqv.
    assert (Hls4: lshape T4) by (inverts Hl2; assumption).
    forwards~ Hhead: IHE2 Hte H0 Hls4.
    rewrite <- mcon_cons.
    inverts Hteq2.
    forwards~ HwfBox: typ_ans_wft Hhead.
    forwards~ (HwT0 & HwfA & Hwfe0): boxt_wft_inv Hwf.
    forwards~ HrigA: wft_box_rigid Hwf.
    assert (HwftBoxNew: wft (T +++ (T1 +++ T4)) (boxt T0 A)).
    { unfold wft. eapply we_box; eauto. eapply wfe_to_mcon_all; eauto. }
    eapply t_eq with (A := (T1 +++ T4) &= boxt T0 A).
    + eapply lt_const; [ exact Hhead | eapply lshape_app; eauto | exact HwftBoxNew ].
    + eapply eq_and.
      * eapply teq_refl; exact HwfBox.
      * eapply lshape_app; eauto.
      * eapply lshape_app; eauto.
      * rewrite mapp_ass in H10. rewrite mapp_ass in H10.
        forwards Hbi: teq_box_inv H10.
        (* box-left intro via eq_boxl; the box-wft on the ambient is HwftBoxNew. *)
        eapply eq_boxl; [ exact Hbi | exact HwftBoxNew ].
Qed. (* Both recursive cases CLOSED: the bare-value last element (E2 = _ ,, _) re-ambients
   via the keystone vrt; the box last element (E2 = _ ;; _) via teq_box_inv + rbox_dec. *)

Lemma canonical_list_aux: forall T A0 v,
  has_type T v A0 -> forall T1 B,
  teq T A0 (T1 & B) T -> 
  value v -> exists v1 ve,
  v = (ve ,, v1).
Proof.
  introv Ht. inductions Ht; introv Heq Hv;
  try solve [inverts* Hv];
  try solve [inverts* Heq];
  try solve [match goal with H: teq _ (boxt _ _) (and _ _ _) _ |- _ =>
               inverts H; match goal with Hb: teq _ _ (and _ _ _) _ |- _ => inverts Hb end end];
  try solve [inverts* Heq; inverts H4];
  try solve [forwards~ Hc: teq_trans H Heq; forwards~: IHHt Hc].
Qed.

Lemma canonical_list: forall T v T1 B,
  has_type T v (T1 & B) -> 
  value v -> exists v1 ve,
  v = (ve ,, v1).
Proof.
  introv Ht Hv.
  forwards~: typ_ans_wft Ht. forwards~: teq_refl H.
  eapply canonical_list_aux; eauto.
Qed.

Lemma rcd_inv_aux2: forall T v A',
  has_type T v A' -> forall l A T1,
  teq T A' (rcd l A) T1 ->
  value v -> exists v1,
  v = (rec l v1).
Proof.
  introv Ht. inductions Ht; introv Heq Hv;
  try solve [inverts Hv];
  try solve [inductions Heq].
  - inductions Heq. inductions Heq.
  - inductions Heq. inductions Heq.
  - forwards~: IHHt.
    eapply teq_trans; eauto.
    eauto.
  - inverts* Heq. 
Qed.

Lemma canonical_tlist_aux: forall A1 T v,
  has_type T v A1 -> forall A T1,
  teq T A1 (T1 &= A) T ->
  value v -> exists B ve,
  v = (ve ;; B).
Proof.
  introv Ht. inductions Ht; introv Heq Hv;
  try solve [inverts* Hv];
  try solve [inverts* Heq];
  try solve [match goal with H: teq _ (boxt _ _) (and _ _ _) _ |- _ =>
               inverts H; match goal with Hb: teq _ _ (and _ _ _) _ |- _ => inverts Hb end end];
  try solve [inverts* Heq; inverts H4];
  try solve [forwards~ Hc: teq_trans H Heq; forwards~: IHHt Hc].
Qed.

Lemma canonical_tlist: forall A T1 T v,
  has_type T v (T1 &= A) -> 
  value v -> exists B ve,
  v = (ve ;; B).
Proof.
  introv Ht Hv.
  forwards~: typ_ans_wft Ht. forwards~: teq_refl H.
  eapply canonical_tlist_aux; eauto.
Qed.

Lemma rlookup_prog_ori: forall l T1 A,
  rlk T1 l A -> forall T dv,
  has_type T dv T1 ->
  value dv ->
  exists v', rlookupv dv l v'.
Proof.
  introv Hr. inductions Hr; introv Ht Hv.
  - (* rlk_hit: subject = T0 & rcd l A *)
    forwards~ (v1&ve0&C&T2&Heqv&Hv1&Hve&Ht1&Hte&Hteq1&Hteq2): merge_inv Ht Hv.
    subst.
    inverts Hteq2.
    match goal with Hc: teq (mconcat T (?Tx)) C (rcd _ _) _ |- _ =>
      forwards~ (v1'&?): rcd_inv_aux2 Ht1 Hc end.
    subst. eexists. eapply rvlzero.
  - (* rlk_left: subject = T0 & rcd l1 A, l <> l1 *)
    forwards~ (v1&ve0&C&T2&Heqv&Hv1&Hve&Ht1&Hte&Hteq1&Hteq2): merge_inv Ht Hv.
    subst.
    forwards~ (v'&?): IHHr Hte.
    inverts Hteq2.
    match goal with Hc: teq (mconcat T (?Tx)) C (rcd _ _) _ |- _ =>
      forwards~ (v1'&?): rcd_inv_aux2 Ht1 Hc end.
    subst. eexists. eapply rvl_left; eauto.
  - (* rlk_right: subject = T1 & T2; look up in the right component v1 via ambient_tail_subst *)
    forwards~ (v1&ve0&Cq&Tq&Heqv&Hv1&Hve&Ht1&Hte&Hteq1&Hteq2): merge_inv Ht Hv.
    subst.
    inverts Hteq2.
    forwards~ Hsub: ambient_tail_subst H11 H7 H9 H10.
    forwards~ Hv1T2: t_eq Ht1 Hsub.
    forwards~ (v'&Hrlk): IHHr Hv1T2 Hv1.
    exists v'. eapply rvl_right. exact Hrlk.
  - (* rlk_left_t: subject = T0 &= A *)
    forwards~ (A0&ve0&T2&Heqv&Hbx&Hve&Hwf&Hte&Hteq1&Hteq2): tmerge_inv Ht Hv.
    subst.
    forwards~ (v'&?): IHHr Hte.
    eexists. eapply rvl_left_t; eauto.
Qed.

Lemma rlookup_prog: forall l T1 A,
  rlk T1 l A -> forall dv0 T dv,
  has_type top dv0 T ->
  value dv0 ->
  lshape T ->
  has_type T dv T1 ->
  value dv ->
  exists v', rlookupv dv l v'.
Proof.
  intros. eapply rlookup_prog_ori; try eapply H3; eauto.
Qed.



Lemma gprogress: forall T e A, 
  has_type T e A ->
  lshape T -> forall ve, 
  value ve -> 
  has_type top ve T -> 
  value e \/ exists e', step ve e e'.
Proof.
  introv Ht; inductions Ht; introv Hs Hv Hve; try solve [eauto].
  (* var *)
  - right. 
    forwards~ (?&?): lookupv_prog H0 Hve.
    econstructor; eauto.
  (* app *)
  - right.
    forwards~ [?|?]: IHHt1 Hv;
    forwards~ [?|?]: IHHt2 Hv;
    try solve [inverts* H].
    + forwards~: canonical_clos Ht1.
      forwards~: typ_wfe Ht1. 
      destruct H1 as (ve'&e&Tq&?). subst. exists*.
  (* all *)
  - right.
    forwards~ [?|?]: IHHt Hve.
    + forwards~: canonical_bclos Ht.
      forwards~: typ_wfe Ht. 
      destruct H1 as (ve'&e0&Tq&?). subst. exists*.
    + inverts* H0.
  (* box *)
  - right.
    forwards~ [Hv1|?]: IHHt1 Hve.
    + assert (has_type top e1 T1) as Hc.
      {
        eapply lt_closed; eauto;
          try (eapply wfe_lshape; eapply typ_wfe; eauto);
          try (eapply typ_wfe; eauto).
      }

      forwards~ Hr: IHHt2 Hc. eapply wfe_lshape; eapply typ_wfe; eauto. destruct* Hr.
    + destruct* H. 
  (*  *)
  - forwards~ [?|?]: IHHt1 Hve.
    + assert (has_type top (ve ++- E) (T +++ T1)) as Hc. 
      { 
        eapply typ_concat; eauto.
        rewrite <-add_top_lshape; eauto.
      }
      forwards~: IHHt2 Hc. 
      eapply lshape_app; eauto.
      eapply value_app; eauto. 
      destruct* H1.
    + destruct* H. 
  - forwards~ [?|?]: IHHt Hve.
    + forwards~ [?|?]: is_box_dec A.
      * inverts* H2.
      * right. eauto.
    + destruct* H0. 
  (* rec *)
  - forwards~ [?|?]: IHHt Hve. destruct* H.
  (* proj *)
  - forwards~: IHHt Hve. destruct* H0.
    right. 
    forwards~: rlookup_prog H Hve Ht.
    destruct* H1.
Qed.


Lemma progress: forall e A, 
  has_type top e A -> 
  value e \/ exists e', step unit e e'.
Proof.
  intros. forwards~: gprogress H lsh_nil unit. 
Qed.



(* -------------------------//-------------------------- *)
(* proving preservation *)
(* -------------------------//-------------------------- *)
Lemma clos_inv_aux: forall T v A',
  has_type T v A' -> forall A B,
  teq T A' (arr A B) T ->
  value v -> exists ve C e T1 D,
  v = clos ve e /\
  has_type top ve T1 /\
  wfe T /\
  has_type (T1 & C) e D /\
  teq T (boxt T1 (arr C D)) (arr A B) T.
Proof.
  introv Ht. inductions Ht; introv Heq Hv;
  try solve [inverts Hv];
  try solve [inductions Heq];
  try solve [match goal with H: teq _ (boxt _ (all _)) (arr _ _) _ |- _ =>
               inverts H; match goal with Hb: teq _ (all _) (arr _ _) _ |- _ => inverts Hb end end];
  try solve [do 5 eexists; repeat split; eauto];
  try solve [
    match goal with
    | Hab: teq ?Tc ?Aa ?Bb ?Tc, Hbarr: teq ?Tc ?Bb (arr _ _) ?Tc |- _ =>
      forwards Hc: teq_trans Hab Hbarr;
      forwards~ (vv & CC & ee & TT1 & DD & ? & ? & ? & ? & ?): IHHt Hc;
      exists vv CC ee TT1 DD; repeat split; eauto
    end ].
Qed.


Lemma clos_inv: forall T v A B,
  has_type T v (arr A B) -> 
  value v -> exists ve C e T1 D,
  v = clos ve e /\
  has_type top ve T1 /\
  wfe T /\
  has_type (T1 & C) e D /\
  teq T (boxt T1 (arr C D)) (arr A B) T.
Proof.
  introv Ht Hv. eapply clos_inv_aux; eauto.
  eapply teq_refl. eapply typ_ans_wft; eauto.
Qed.

Lemma bclos_inv_aux: forall T v A',
  has_type T v A' ->
  value v -> forall B,
  teq T A' (all B) T -> 
  exists ve e T1 D,
  v = bclos ve e /\
  (has_type top ve T1 /\
  wfe T /\
  has_type (T1 &s) e D /\
  teq T (boxt T1 (all D)) (all B) T).
Proof.
  introv Ht. inductions Ht; introv Hv Heq;
  try solve [inverts Hv];
  try solve [inductions Heq];
  try solve [match goal with H: teq _ (boxt _ (arr _ _)) (all _) _ |- _ =>
               inverts H; match goal with Hb: teq _ (arr _ _) (all _) _ |- _ => inverts Hb end end];
  try solve [do 4 eexists; repeat split; eauto];
  try solve [
    match goal with
    | Hab: teq ?Tc ?Aa ?Bb ?Tc, Hball: teq ?Tc ?Bb (all _) ?Tc |- _ =>
      forwards Hc: teq_trans Hab Hball;
      forwards~ (vv & ee & TT1 & DD & ? & ? & ? & ? & ?): IHHt Hc;
      exists vv ee TT1 DD; repeat split; eauto
    end ].
Qed.

Lemma bclos_inv: forall T v B,
  has_type T v (all B) -> 
  value v -> exists ve e T1 D,
  v = bclos ve e /\
  (has_type top ve T1 /\
  wfe T /\
  has_type (T1 &s) e D /\
  teq T (boxt T1 (all D)) (all B) T).
Proof.
  introv Ht Hv. eapply bclos_inv_aux; eauto.
  eapply teq_refl. eapply typ_ans_wft; eauto.
Qed.

Lemma lookupv_pres: forall ve n v,
  lookupv ve n v ->
  value ve -> forall T A,
  lshape T ->
  get_var T n A ->
  has_type top ve T ->
  has_type T v A.
Proof.
  introv Hl. inductions Hl; introv Hve Hs Hg Htv.
  - (* lvzero: env [ve0 ,, v1], looked-up value v1 typed at the looked-up slot. *)
    inverts Hve. forwards~ (B&T2&HeqT): merge_inv2 Htv. subst. inverts Hg.
    forwards~ (v1&ve0&C&T3&Heqv&Hvv1&Hvve0&Htv1&Htve0&Hteqsp&Hteqand): merge_inv Htv.
    inverts Heqv. inverts Hteqand.
    rewrite <-(add_top_lshape H9) in Htv1, H11.
    rewrite <-(add_top_lshape H10) in H11.
    forwards~ HwftA: teq_wft_right H11. forwards~ Hwfe2: wfe_eteq_evar HwftA.
    eapply vrt; [ exact Htv1 | exact Hvv1 | | exact Hwfe2 ].
    eapply adde_teq_sp_r; [exact H11 | eapply adde_wft_sp; eauto].
  - inverts Hve. forwards~ (B&T2&HeqT): merge_inv2 Htv. subst. inverts Hg. inverts Hs.
    forwards~ (v1&ve0&C&T3&Heqv&Hvv1&Hvve0&Htv1&Htve0&Hteqsp&Hteqand): merge_inv Htv.
    inverts Heqv.
    forwards~ Hihv: IHHl H1 H0 H5 Htve0.
    inverts Hteqand. rewrite <-(add_top_lshape H0) in *.
    forwards~ HwftB: teq_wft_right H13. forwards~ Hwfe2: wfe_eteq_evar HwftB.
    forwards~ Hvv': lookupv_value Hl. forwards~ HwftA: typ_ans_wft Hihv.
    eapply vrt; [ exact Hihv | exact Hvv' | | exact Hwfe2 ].
    eapply adde_teq_sp_r; [ eapply teq_refl; exact HwftA | eapply adde_wft_sp; eauto ].
  - inverts Hve. forwards~ (B&T2&HeqT): tmerge_inv2 Htv. subst. inverts Hg. inverts Hs.
    assert (value (ve ;; boxt T0 A1)) as Hvm by (econstructor; eauto).
    forwards~ (A1'&ve0&T3&Heqv&Hbox&Hvve0&Hwft&Htve0&Hteqsp&Hteqeq): tmerge_inv Htv Hvm.
    inverts Heqv.
    forwards~ Hihv: IHHl H0 H1 H4 Htve0.
    inverts Hteqeq. rewrite <-(add_top_lshape H11) in H12.
    forwards~ HwftB: teq_wft_right H12.
    forwards~ HwftA: typ_ans_wft Hihv.
    forwards~ Hvv': lookupv_value Hl.
    eapply vrt; [ exact Hihv | exact Hvv' | | exact HwftB ].
    assert (Hna: num_of_abs T2 = 0) by (eapply value_num0; [ exact Htve0 | exact Hvve0 | reflexivity ]).
    assert (HrigA: rigid 0 T2 A) by (eapply rigid_of_wft; [ exact Hna | exact HwftA ]).
    eapply teq_sym.
    eapply dead_star_l with (p := top) (T1 := T2) (C := B);
      [ eapply teq_shift_tvar_l_rigid with (X := 0) (T1 := T2);
          [ eapply teq_refl; exact HwftA
          | exact HrigA
          | eapply itv_here2
          | eapply we_tvar; eapply wft_wfe; exact HwftA ]
      | eapply lsh_nil
      | exact HrigA
      | exact HwftB
      | exact HwftB ].
Qed.




(* -------------------------------------- *)
(* inst: typing *)
(* -------------------------------------- *)
Lemma orel_getv: forall T T1, 
  orel T T1 -> forall n A,
  get_var T n A ->
  get_var T1 n A.
Proof.
  intros T T1 He. inductions He; introv Hl; try solve [inverts* Hl].
Qed.  


Lemma wft_earlier: forall T3 B T4,
  wfe ((T4 &= B) +++ T3) ->
  wft T4 B.
Proof.
  intros. forwards~: wfe_cut H. 
Qed.

Lemma inst_typ: forall T3 T4 e A,
  has_type (T4 &s +++ T3) e A -> lshape T3 -> forall B,
  wfe ((T4 &= B) +++ T3) ->
  has_type ((T4 &= B) +++ T3) e A.
Proof.
  introv Ht. inductions Ht ; introv Hls Hw; try solve [eauto].
  (* var *)
  - econstructor; eauto.
    eapply orel_getv; eauto.
    eapply inst_orel; eauto.
    eapply wft_earlier; eauto.
  (* lam *)
  - econstructor; eauto.
    assert (Hrec: has_type (T4 &= B0 +++ (T3 & A)) e B).
    { eapply IHHt.
      - rewrite <- mcon_cons. eauto.
      - eapply lsh_evar; exact Hls.
      - forwards~ HwA: typ_ans_wft Ht. forwards~ HwfeA: wft_wfe HwA.
        eapply orel_wfe; eauto.
        rewrite <- mcon_cons. eauto.
        econstructor. eapply inst_orel. eapply wfe_inv; eauto. eapply wft_earlier; eauto. }
    rewrite mcon_cons. exact Hrec.
  (* blam *)
  - econstructor; eauto.
    assert (Hrec: has_type (T4 &= B0 +++ (T3 &s)) e B).
    { eapply IHHt.
      - rewrite <- mcon_cons_st. eauto.
      - eapply lsh_ands; exact Hls.
      - rewrite <- mcon_cons_st. eauto. }
    rewrite mcon_cons_st. exact Hrec.
  (* tapp *)
  - econstructor; eauto. unfold wft in *.
    eapply orel_wfe; try eapply H; eauto.
    econstructor.  eapply inst_orel. eapply wfe_inv; eauto. eapply wft_earlier; eauto.
  (* eq *)
  - forwards~ Hrec: IHHt T3 T4 B0.
    eapply t_eq; [ exact Hrec | ].
    eapply inst_teq_gen; [ exact H | exact Hls | exact Hls | reflexivity | ].
    eapply teq_refl.
    eapply wft_earlier; eauto.
  (* lt_conse *)
  - eapply lt_conse; eauto.
    assert (Hrec: has_type (T4 &= B +++ (T3 +++ T1)) e A).
    { eapply IHHt2.
      - rewrite mapp_ass. eauto.
      - eapply mcon_lshape; [ exact H | exact Hls ].
      - rewrite <-mapp_ass.
        forwards~ Hwt: typ_wfe Ht2.
        eapply orel_wfe; try eapply H; eauto.
        eapply orel_app. eapply orel_app. econstructor.
        eapply orel_refl; eauto.
        forwards~: wfe_cut Hw. }
    rewrite <-mapp_ass in Hrec. eauto.
  (* lt_const *)
  - eapply lt_const; eauto.
    eapply orel_wfe; try eapply H0; eauto.
    econstructor.
    eapply orel_app. eapply orel_app. econstructor.
    eapply orel_refl; eauto.
    forwards~: wfe_cut Hw.
Qed.

Lemma inst_typ_sp: forall T4 e A,
  has_type (T4 &s) e A -> forall B,
  wfe (T4 &= B) ->
  has_type (T4 &= B) e A.
Proof.
  intros T4 e A H B H0.
  eapply inst_typ with (T3 := top); [ exact H | eapply lsh_nil | exact H0 ].
Qed.


Lemma rcd_inv_aux3: forall T v A',
  has_type T v A' -> forall T1 l A,
  teq T A' (rcd l A) T1 ->
  value v -> exists v1 C,
  v = (rec l v1) /\
  has_type T v1 C /\
  teq T (rcd l C) (rcd l A) T1.
Proof.
  introv Ht. inductions Ht; introv Heq Hv;
  try solve [inverts Hv];
  try solve [inductions Heq].
  - inductions Heq. inductions Heq.
  - inductions Heq. inductions Heq.
  - forwards~: IHHt.
    eapply teq_trans; eauto.
    eauto.
  - inverts* Heq. 
Qed.

Lemma merge_inv3_aux: forall T v A',
  has_type T v A' -> forall T1 l B,
  teq T A' (T1 & (rcd l B)) T ->
  value v -> exists v1 ve C T2,
  v = (ve ,, rec l v1) /\
  value v1 /\
  value ve /\
  has_type (T +++ T2) v1 C /\
  has_type T ve T1 /\
  teq T T2 T1 T /\
  teq T (T2 & (rcd l C)) (T1 & (rcd l B)) T.
Proof.
  introv Ht. inductions Ht; introv Heq Hv;
  try solve [inverts Hv];
  try solve [inductions Heq].
  - inverts Heq;
      try solve [repeat match goal with
        H: teq _ (arr _ _) _ _ |- _ => inverts H
      | H: teq _ _ (arr _ _) _ |- _ => inverts H end].
  - inverts Heq;
      try solve [repeat match goal with
        H: teq _ (all _) _ _ |- _ => inverts H
      | H: teq _ _ (all _) _ |- _ => inverts H end].
  - forwards~: IHHt.
    eapply teq_trans; eauto.
    eauto.
  - inverts Hv. inverts* Heq.
    forwards~: rcd_inv_aux3 Ht2 H12.
    destruct H0 as (v1&C&?&?&?). subst. inverts H3.
    exists* v1 E C T1.
Qed.


Lemma merge_inv3: forall T v T1 l B,
  has_type T v (T1 & (rcd l B)) -> 
  value v -> exists v1 ve C T2,
  v = (ve ,, rec l v1) /\
  value v1 /\
  value ve /\
  has_type (T +++ T2) v1 C /\
  has_type T ve T1 /\
  teq T T2 T1 T /\
  teq T (T2 & (rcd l C)) (T1 & (rcd l B)) T.
Proof.
  introv Ht Hv.
  forwards~: typ_ans_wft Ht. forwards~: teq_refl H.
  eapply merge_inv3_aux; eauto.
Qed.


(* number of manifest (&=) binders in the spine T1 *)
Fixpoint nmani (T1: typ) : nat :=
  match T1 with
  | and A rt _ => S (nmani A)
  | and A non _ => nmani A
  | ands A => nmani A
  | _ => 0
  end.

(* &s-tower: append n abstract binders *)
Fixpoint sands (n: nat) (T: typ) : typ :=
  match n with
  | 0 => T
  | S k => (sands k T) &s
  end.

(* iterated tshift 0 *)
Fixpoint itsh (n: nat) (A: typ) : typ :=
  match n with
  | 0 => A
  | S k => tshift 0 (itsh k A)
  end.

Lemma sands_wfe: forall n T, wfe T -> wfe (sands n T).
Proof. induction n; intros; simpl; eauto. Qed.

(* strip the n &s padding from a VALUE typing, de-shifting the type *)
Lemma vstrip_sands: forall n T v A,
  value v -> has_type (sands n T) v (itsh n A) -> wfe T ->
  has_type T v A.
Proof.
  induction n; introv Hval Ht Hw.
  - simpl in *. exact Ht.
  - simpl in Ht.
    forwards (A0 & Ht0 & Hteq & _): vd Ht Hval (isl_here_s (sands n T)).
    eapply sands_wfe; eauto.
    forwards Hu: teq_unpad_s Hteq; try (eapply sands_wfe; eauto).
    forwards Ht1: vrt Ht0 Hval Hu; try (eapply sands_wfe; eauto).
    eapply IHn; eauto.
Qed.

Lemma mopen_eq: forall T1 A B,
  mopen T1 A B -> forall T,
  wft (T +++ T1) A ->
  teq (T +++ T1) A (itsh (nmani T1) B) (sands (nmani T1) T).
Proof.
  introv Hm. inductions Hm; introv Hw.
  - simpl in *. eapply teq_refl; eauto.
  - rewrite <- mcon_cons in *. cbn [nmani].
    forwards Hwd: del_wft Hw (T0 +++ T).
    econstructor. eapply del_refl; eauto.
    forwards HIH: IHHm Hwd.
    eapply adde_teq_sp; eauto.
  - rewrite <- mcon_cons in *. cbn [nmani sands itsh].
    forwards HIH: IHHm T0.
    { unfold wft. eapply we_mani; eauto. eapply wft_wfe; eauto. }
    eapply teq_mani_inv_l. exact HIH.
Qed.


Lemma elist_rcd: forall T d A,
  has_type T d A -> forall l1 v,
  rlookupv d l1 v ->
  value d -> forall T1 l B,
  teq T A (rcd l B) T1 ->
  False.
Proof.
  introv Ht. inductions Ht; introv Hr Hv He;
  try solve [inverts He];
  try solve [inverts Hv];
  try solve [match goal with H: teq _ (boxt _ _) (rcd _ _) _ |- _ =>
               inverts H; match goal with Hb: teq _ _ (rcd _ _) _ |- _ => inverts Hb end end];
  try solve [inverts He; inverts H4];
  try solve [forwards~: teq_trans H He; eauto];
  try solve [inverts He; inverts Hr].
Qed.

Lemma rcd_elist: forall T v A l,
  has_type T (rec l v) A ->
  value (rec l v) -> forall T1 T2,
  teq T A T2 T1 -> forall l1 B,
  rlk T2 l1 B ->
  False.
Proof.
  introv Ht. inductions Ht; introv Hv He Hr; try solve [inverts He].
  - forwards~: teq_trans H He. eauto.
  - inverts He; inverts* Hr. 
Qed.

Lemma rlookup_pres_ori: forall T1 l A,
  rlk T1 l A -> forall T, forall dv v',
  rlookupv dv l v' ->
  value dv ->
  has_type T dv T1 ->
  has_type T v' A.
Proof.
  introv Hl. inductions Hl; introv Hlv Hv Ht.
  - forwards~ (v1&ve&?): canonical_list Ht. inverts H1.
    inverts Hv.
    forwards~ (v2&ve1&C&T2&?&?&?&?&?&?&?): merge_inv3 Ht.
    inverts H1. inverts H9. inverts H19.
    inverts Hlv.
    + forwards~ HwA: teq_wft_right H13.
      forwards Hmo: mopen_eq H0 HwA.
      forwards Htr: teq_trans H13 Hmo.
      forwards Hvs: vrt H6 H2 Htr.
      { eapply sands_wfe. eapply typ_wfe; eauto. }
      eapply vstrip_sands; [ exact H2 | exact Hvs | eapply typ_wfe; eauto ].
    + contradiction.
    + inverts H12.
  - forwards~ (v1&ve&?): canonical_list Ht. inverts H0.
    inverts Hv.
    forwards~ (v2&ve1&C&T2&?&?&?&?&?&?&?): merge_inv Ht.
    inverts H0. inverts H8.
    inverts Hlv.
    + forwards~: rcd_inv_aux2 H5 H18.
      destruct H0. inverts H0. inverts H1. contradiction.
    + eapply IHHl; eauto.
    + exfalso. eapply elist_rcd; try eapply H18; eauto.
  - forwards~ (v1&ve&?): canonical_list Ht. inverts H1.
    inverts Hv.
    forwards~ (v3&ve1&D&T3&?&?&?&?&?&?&?): merge_inv Ht.
    inverts H1. inverts H9.
    inverts Hlv.
    + exfalso. eapply rcd_elist; eauto.
    + exfalso. eapply rcd_elist; eauto.
    + forwards~ He: typ_wfe H7.
      forwards~ He1: teq_wfe_right H19.
      assert (Ht2: has_type (T +++ T1) v3 T2).
      { eapply vrt; eauto. }
      forwards~ Htv': IHHl H12 Ht2.
      forwards~ Hvv': rl_value H12 H2.
      forwards~ HwB: typ_ans_wft Htv'.
      forwards Hmo: mopen_eq H0 HwB.
      forwards Hvs: vrt Htv' Hvv' Hmo.
      { eapply sands_wfe; eauto. }
      eapply vstrip_sands; [ exact Hvv' | exact Hvs | exact He ].
  - forwards~ (v1&ve&?): canonical_tlist Ht. inverts H.
    inverts Hv.
    forwards~ (C&ve1&T3&?&?&?&?&?&?&?): tmerge_inv Ht.
    inverts H. inverts H1. inverts H6.
    inverts Hlv.
    eapply IHHl; eauto.
Qed.


Lemma value_boxing: forall dv G v A G1,
  has_type top dv G ->
  value dv ->
  has_type G v A ->
  value v ->
  wfe G1 ->
  has_type G1 v (boxt G A).
Proof.
  introv Htdv Hvdv Htv Hvv Hwf1.
  assert (Hna: num_of_abs G = 0)
    by (eapply value_num0; [ exact Htdv | exact Hvdv | reflexivity ]).
  forwards~ HwftA: typ_ans_wft Htv.
  forwards~ Hrig: rigid_of_wft Hna HwftA.
  assert (HwftBox: wft G1 (boxt G A))
    by (unfold wft; eapply we_box; [ exact HwftA | exact Hrig | exact Hwf1 ]).
  eapply vrt;
    [ exact Htv | exact Hvv
    | eapply eq_boxr; [ eapply teq_refl; exact HwftA | exact HwftBox ]
    | exact Hwf1 ].
Qed.

(* -------------------------//-------------------------- *)
Lemma gpreservation: forall T e A,
  has_type T e A -> forall ve e',
  step ve e e' ->
  has_type top ve T ->
  lshape T ->
  has_type T e' A.
Proof.
  introv Ht.
  inductions Ht; introv Red Htv Hs;
  try solve [inverts* Red].
  (* lookup *)
  - inverts Red.
    eapply lookupv_pres with (n := n); eauto.
  - inverts Red.
    forwards~ HnT: value_num0 Htv H1.
    forwards~ Hwft: typ_ans_wft (t_lam Ht).
    assert (Hrig: rigid 0 T (arr A B)) by (eapply rigid_of_wft; eauto).
    assert (HwfeT: wfe T) by (eapply wft_wfe; exact Hwft).
    eapply t_eq with (A := boxt T (arr A B)).
    + eapply t_clos with (T1 := T); eauto.
    + assert (Hrefl: teq T (arr A B) (arr A B) T) by (eapply teq_refl; eauto).
      (* box-left intro via eq_boxl; box-wft via we_box (body wft + rigidity + ambient). *)
      eapply eq_boxl; [ exact Hrefl | unfold wft; eapply we_box; [ exact Hwft | exact Hrig | exact HwfeT ] ].
 (* app *)
  - inverts Red.
    + (* sappl: e1 steps -- structural, via IH1 *)
      eapply t_app; eauto.
    + (* sappr: e2 steps -- structural, via IH2 *)
      eapply t_app; eauto.
    + forwards~ (ve1&C&e0&T2&D&?&?&?&?&?): clos_inv Ht1.
      inverts H.
      forwards~ HnT2: value_num0 H0 H1.
      forwards~ HwfeT2C: typ_wfe H4.
      forwards~ HwftD: typ_ans_wft H4.
      forwards~ HrigD: rigid_of_wft (T2 & C) D.
      forwards~ Hbteq: teq_box_inv H6.
      inverts Hbteq.
      assert (HwfeT2: wfe T2) by (eapply wfe_inv; eauto).
      forwards~ HlsT2: wfe_lshape HwfeT2.
      assert (HwfeTT2: wfe (T +++ T2)) by (eapply wfe_app; eauto).
      assert (Harg: has_type (T +++ T2) e2 C).
      { eapply vrt with (G1:=T)(A:=A); eauto. eapply teq_weaken; eauto. eapply teq_sym; eauto. }
      eapply t_eq with (A := boxt (T2 & C) D).
      * eapply t_box with (T1 := T2 & C).
        -- eapply lt_conse with (T1 := T2).
           ++ eapply lt_closed; eauto.
           ++ exact HlsT2.
           ++ exact Harg.
        -- exact H4.
        -- exact HrigD.
      * assert (HbodyD: teq (T2 & C) D B T) by (eapply adde_teq_sp; eauto).
        forwards HwftB: teq_wft_right H13.
        (* box-left intro via eq_boxl; box-wft via we_box (body wft HwftD +
           rigidity HrigD + ambient wfe T from HwftB). *)
        eapply eq_boxl;
          [ exact HbodyD
          | unfold wft; eapply we_box; [ exact HwftD | exact HrigD | eapply wft_wfe; exact HwftB ] ].
  - inverts Red.
    forwards~ HnT: value_num0 Htv H1.
    forwards~ Hwft: typ_ans_wft (t_blam Ht).
    assert (Hrig: rigid 0 T (all B)) by (eapply rigid_of_wft; eauto).
    assert (HwfeT: wfe T) by (eapply wft_wfe; exact Hwft).
    eapply t_eq with (A := boxt T (all B)).
    + eapply t_bclos with (T1 := T); eauto.
    + assert (Hrefl: teq T (all B) (all B) T) by (eapply teq_refl; eauto).
      (* box-left intro via eq_boxl; box-wft via we_box (body wft + rigidity + ambient). *)
      eapply eq_boxl; [ exact Hrefl | unfold wft; eapply we_box; [ exact Hwft | exact Hrig | exact HwfeT ] ].
  (* tapp *)
  - inverts Red.
    + (* stappl: e1 steps -- structural, via IH *)
      eapply t_tapp; eauto.
    + (* stapp: tapp (bclos v1 e1) A -> box (v1 ;; boxt (c2g ve) A) e1. *)
      clear IHHt.
      forwards~: typ_wfe Ht.
      forwards~ Hwt: typ_ans_wft Ht.
      forwards~: bclos_inv Ht.
      destruct H1 as (ve1&e1&?T1&D&?&?&?&?&?). inverts H1.
      assert (HwfT1: wfe T1) by (forwards~: typ_wfe H6; eapply wfe_sinv; eauto).
      assert (HlsT1: lshape T1) by (eapply wfe_lshape; eauto).
      forwards~ HnT1: value_num0 H2 H5.
      assert (Hwbox: wft T1 (boxt (c2g ve) A)) by (eapply vtyp_wft_c; eauto).
      assert (Hbody: has_type (T1 &= (boxt (c2g ve) A)) e1 D)
        by (eapply inst_typ_sp; eauto; unfold wft in Hwbox; eauto).
      eapply t_eq with (A := boxt (T1 &= boxt (c2g ve) A) D).
      * eapply t_box.
        -- eapply lt_const; eauto.
           eapply lt_closed; eauto.
           eapply vtyp_wft_c; eauto. eapply wfe_app; eauto.
        -- exact Hbody.
        -- eapply rigid_of_wft; eauto. eapply typ_ans_wft; eauto.
      * inverts H7.
        (* the body teq [H10 : teq T1 (all D) (all B) T] inverts (eq_all) to the
           under-binder body teq [teq (T1 &s) D B (T &s)]. *)
        assert (Hbteq: teq (T1 &s) D B (T &s)) by (match goal with Hh: teq _ (all _) (all _) _ |- _ => inverts Hh; eauto end).
        assert (Hrm: teq T1 (boxt (c2g ve) A) A T) by (eapply vtyp_eq_c; eauto).
        forwards~ Hinst: inst_teq Hbteq Hrm.
        assert (HrigD: rigid 0 (T1 &= boxt (c2g ve) A) D)
          by (eapply rigid_of_wft; eauto; eapply typ_ans_wft; eauto).
        assert (HwftB: wft (T &= A) B) by (eapply teq_wft_right; eauto).
        (* box-removal of [boxt (T1 &= boxt (c2g ve) A) D] against [B] (the eq_manir
           body): ~rbox-free, so just eq_boxl on the body teq [Hinst] (rigidity
           [HrigD], the frame-body wft from typ_ans_wft, [HwftB] for the right). *)
        eapply eq_manir.
        assert (HwftFD: wft (T1 &= boxt (c2g ve) A) D)
          by (eapply typ_ans_wft; eauto).
        eapply eq_boxl;
          [ exact Hinst
          | unfold wft; eapply we_box; [ exact HwftFD | exact HrigD | eapply we_tvar; eapply teq_wfe_right; exact Hrm ] ].
  (* box *)
  - assert (Hs1: lshape T1) by (eapply wfe_lshape; eapply typ_wfe; eauto).
    inverts Red.
    + (* sboxl: e1 steps -- structural, via IH1 *)
      eapply t_box; eauto.
    + (* sbox: e2 steps inside the box frame e1 -- structural, via IH2 retyped to
         the ambient frame T1 (e1 is a value, so lt_closed retypes it). *)
      eapply t_box; eauto. eapply IHHt2; eauto.
      eapply lt_closed; eauto. eapply typ_wfe; eauto.
    + (* sboxv: box v1 v2 -> v2, with result type [boxt T1 A].  The body value
         [v2 : A] (ambient T1) is re-typed at the box type [boxt T1 A] under the
         ambient T directly by [value_boxing].  Its value-environment witness is
         the box env [v1], re-ambiented from T to top via [lt_closed]; this shows
         that the local context T1 is the type of a value environment. *)
      eapply value_boxing;
        [ eapply lt_closed;
            [ exact Ht1 | eapply typ_wfe; exact Ht2
            | eapply wfe_lshape; eapply typ_wfe; exact Ht2
            | assumption | apply we_nil ]
        | assumption | exact Ht2 | assumption | eapply typ_wfe; exact Ht1 ].
  (* list exp *)
  - inverts* Red.
    + eapply lt_conse; eauto.
      eapply IHHt2; eauto.
      * eapply typ_concat; eauto.
        rewrite <-add_top_lshape; eauto.
      * eapply lshape_app; eauto.
  (* list typ *)
  - inverts* Red.
    + forwards~: typ_concat Htv E T1.
      rewrite <-add_top_lshape; eauto.
      forwards~: value_app H5 H3.
      forwards~: wft_wfe H0.
      econstructor.
      * eapply lt_const; eauto.
        eapply vtyp_wft_c; eauto.
        eapply lshape_app; eauto.
      * econstructor; eauto.
        eapply teq_refl; eauto. eapply typ_ans_wft; eauto.
        eapply vtyp_eq_c; eauto.
        eapply lshape_app; eauto.
  (* proj *)
  - inverts* Red.
    eapply rlookup_pres_ori; eauto.
Qed.

Lemma preservation: forall e A,
  has_type top e A -> forall e',
  step unit e e' ->
  has_type top e' A.
Proof.
  intros. forwards~: gpreservation H H0. 
Qed.
