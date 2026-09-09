Require Import LibTactics.
From Stdlib Require Import Arith Lia.
From Stdlib Require Import Strings.String.
Require Import Top.source.Syntax.
Require Import Top.source.Elaboration.
Set Implicit Arguments.

(* -------------------------//-------------------------- *)
(* Foundations. *)

Lemma mopen_total : forall T, sig_shape T -> forall A, exists B, mopen T A B.
Proof.
  introv Hs. inductions Hs; intros.
  - exists A. eauto.
  - forwards~ (B&HB): IHHs A0. exists B. eauto.
  - forwards~ (B&HB): IHHs (mani A A0). exists B. eauto.
Qed.

(* companion of check_lt_keyLen *)
Lemma lookt_lt_keyLen : forall T X A, lookt T X A -> X < keyLen T.
Proof. introv Hl. induction Hl; simpl; lia. Qed.

(* sig_shape rules out rlk_right; unique_labels supplies rlk_hit's ~ lb_in.
   Nothing elsewhere in the development constructs an rlk derivation. *)
Lemma rlk_exists : forall G l A,
  has_lbl G l A -> sig_shape G -> unique_labels G ->
  exists B, rlk G l B.
Proof.
  introv Hl. induction Hl; introv Hs Hu; inverts Hs; inverts Hu.
  - match goal with Hs' : sig_shape ?G0 |- _ =>
      forwards~ (B&HB): mopen_total Hs' A end.
    exists B. eauto.
  - assert (exists B, rlk G l B) as (B&HB) by (apply IHHl; eauto).
    exists B. eauto.
  - assert (exists B0, rlk G l B0) as (B0&HB0) by (apply IHHl; eauto).
    exists B0. eauto.
Qed.

(* tshift is the identity on a type well formed in T, at any offset at or
   above keyLen T. *)
Lemma wft_tshift_id : forall A T X, wft T A -> tshift (keyLen T + X) A = A.
Proof.
  induction A; introv Hw; unfold wft in Hw; inverts Hw; simpl; eauto.
  all: try solve [ match goal with H : check ?T0 ?n0 |- _ =>
                     forwards~ Hlt: check_lt_keyLen H end;
                   destruct (le_gt_dec (keyLen T + X) n); solve [ lia | eauto ] ].
  all: try solve [ match goal with H : lookt ?T0 ?n0 ?A0 |- _ =>
                     forwards~ Hlt: lookt_lt_keyLen H end;
                   destruct (le_gt_dec (keyLen T + X) n); solve [ lia | eauto ] ].
  all: try solve [ forwards~ E1: IHA1 T X; forwards~ E2: IHA2 T X;
                   rewrite E1; rewrite E2; eauto ].
  all: try solve [ forwards~ E: IHA (T &s) X;
                   replace (S (keyLen T + X)) with (keyLen (T &s) + X) by (simpl; lia);
                   rewrite E; eauto ].
  all: try solve [ forwards~ E1: IHA1 T X; forwards~ E2: IHA2 (T &= A1) X; rewrite E1;
                   replace (S (keyLen T + X)) with (keyLen (T &= A1) + X) by (simpl; lia);
                   rewrite E2; eauto ].
  (* and: tshift matches on the mode, so destruct it *)
  all: try solve [ destruct m;
                   forwards~ E1: IHA1 T X; forwards~ E2: IHA2 (T +++ A1) X; rewrite E1;
                   replace (keyLen A1 + (keyLen T + X)) with (keyLen (T +++ A1) + X)
                     by (rewrite keyLen_app; lia);
                   rewrite E2; eauto ].
  all: try solve [ forwards~ E1: IHA T X; rewrite E1; eauto ].
Qed.

(* at T = top: a closed signature is fixed by every shift.  This is what
   removes the need for a shifting lemma on rlk. *)
Lemma closed_tshift_id : forall G X, wft top G -> tshift X G = G.
Proof. introv Hw. forwards~ E: wft_tshift_id G top X. Qed.

(* -------------------------//-------------------------- *)
(* Well-formedness helpers. *)

Lemma wft_top_weaken : forall A, wft top A -> forall T, wfe T -> wft T A.
Proof. introv Ha Hw. forwards~ H: wft_prepend Ha T. Qed.

Lemma wfe_snoc : forall T A, wft T A -> wfe (T & A).
Proof. introv H. eapply wfe_eteq_evar; eauto. Qed.

Lemma wfe_body : forall T D, wft T D -> wfe (T +++ D).
Proof. introv Hw. eapply wfe_to_mcon_all; exact Hw. Qed.

(* the ambient under an environment term being built *)
Lemma wfe_under : forall T d Gd, has_type T d Gd -> wfe (T +++ Gd).
Proof. introv Ht. eapply wfe_body. eapply typ_ans_wft; exact Ht. Qed.

(* discharges the lshape premise of lt_conse / lt_const *)
Lemma sig_shape_lshape : forall G, sig_shape G -> lshape G.
Proof. introv H. induction H; eauto. Qed.

(* num_of_abs top = 0, so this is the whole sandbox side condition *)
Lemma rigid_top : forall A, wft top A -> rigid 0 top A.
Proof. introv Hw. eapply rigid_of_wft; eauto. Qed.

(* -------------------------//-------------------------- *)
(* Merge infrastructure. *)

(* Growing the ambient by D moves a variable's index by numv D and puts
   mshift D on its type.  No side condition. *)
Lemma get_var_grow_gen : forall D T n A,
  get_var T n A ->
  get_var (T +++ D) (numv D + n) (mshift D A).
Proof.
  induction D; introv Hg; try solve [simpl; exact Hg].
  - (* and: mconcat, mshift and numv all match on the mode *)
    destruct m.
    + rewrite <- mcon_cons. simpl. eapply get_var_evar. eapply IHD1; exact Hg.
    + rewrite <- mcon_cons. simpl. eapply get_var_eteq. eapply IHD1; exact Hg.
  - (* ands *)
    rewrite <- mcon_cons_st. simpl. eapply get_var_etvar. eapply IHD; exact Hg.
Qed.

Lemma mshift_id : forall D A,
  (forall X, tshift X A = A) -> mshift D A = A.
Proof.
  induction D; introv Hid; try solve [simpl; reflexivity].
  - destruct m; simpl.
    + eapply IHD1; exact Hid.
    + rewrite (IHD1 A Hid). eapply Hid.
  - simpl. rewrite (IHD A Hid). eapply Hid.
Qed.

Lemma mshift_closed : forall D A, wft top A -> mshift D A = A.
Proof.
  introv Hw. eapply mshift_id. introv. eapply closed_tshift_id; exact Hw.
Qed.

(* on a closed signature the shifts collapse and only the index moves *)
Lemma get_var_grow : forall D T n A,
  wft top A -> get_var T n A ->
  get_var (T +++ D) (numv D + n) A.
Proof.
  introv Hw Hg. forwards~ H: get_var_grow_gen D Hg.
  rewrite (mshift_closed D Hw) in H. exact H.
Qed.

Lemma expands_lshape : forall Amb k Gsrc Gtodo dIn GIn dOut GOut,
  expands Amb k Gsrc Gtodo dIn GIn dOut GOut ->
  lshape GIn -> lshape GOut.
Proof. introv He. induction He; introv Hl; eauto. Qed.

Lemma expands_sound : forall Amb k Gsrc Gtodo dIn GIn dOut GOut,
  expands Amb k Gsrc Gtodo dIn GIn dOut GOut ->
  wft top Gsrc ->
  get_var Amb k Gsrc ->
  lshape GIn ->
  has_type Amb dIn GIn ->
  has_type Amb dOut GOut.
Proof.
  introv He. induction He; introv Hc Hg Hl Ht.
  - (* ex_nil *) exact Ht.
  - (* ex_lbl *)
    forwards Hd1: IHHe Hc Hg Hl Ht.
    forwards Hl1: expands_lshape He Hl.
    eapply lt_conse; [ exact Hd1 | exact Hl1 | ].
    eapply t_rec. eapply trproj.
    + eapply t_var.
      * eapply wfe_under; exact Hd1.
      * eapply get_var_grow; [ exact Hc | exact Hg ].
    + eassumption.
  - (* ex_typ *)
    forwards Hd1: IHHe Hc Hg Hl Ht.
    forwards Hl1: expands_lshape He Hl.
    eapply lt_const; [ exact Hd1 | exact Hl1 | eassumption ].
Qed.

(* -------------------------//-------------------------- *)
(* One compatibility lemma per elaboration rule, stated in has_type with
   its premises already in has_type form.  Same organization as LogRel.v's
   comp_eq / comp_proj. *)

Lemma comp_var : forall G n l A B,
  wfe G -> get_var G n A -> rlk A l B ->
  has_type G (rproj (var n) l) B.
Proof. introv Hw Hg Hr. eapply trproj; [ eapply t_var; eauto | exact Hr ]. Qed.

Lemma comp_fun : forall G A e B,
  has_type (G & A) e B -> has_type G (lam e) (arr A B).
Proof. introv H. eapply t_lam; exact H. Qed.

Lemma comp_tfun : forall G e B,
  has_type (G &s) e B -> has_type G (blam e) (all B).
Proof. introv H. eapply t_blam; exact H. Qed.

Lemma comp_app : forall G e1 e2 A B,
  has_type G e1 (arr A B) -> has_type G e2 A -> has_type G (app e1 e2) B.
Proof. introv H1 H2. eapply t_app; eassumption. Qed.

Lemma comp_tapp : forall G e A B,
  has_type G e (all B) -> wft G A -> has_type G (tapp e A) (mani A B).
Proof. introv H Hw. eapply t_tapp; eassumption. Qed.

Lemma comp_eq : forall G e A B,
  has_type G e A -> teq G A B G -> has_type G e B.
Proof. introv H Hq. eapply t_eq; eassumption. Qed.

Lemma comp_box : forall G e A,
  has_type top e A -> wfe G -> has_type G (box unit e) (boxt top A).
Proof.
  introv Ht Hw. eapply t_box.
  - eapply lt_nil; exact Hw.
  - exact Ht.
  - eapply rigid_top. eapply typ_ans_wft; exact Ht.
Qed.

Lemma comp_dnil : forall G, wfe G -> has_type G unit top.
Proof. introv H. eapply lt_nil; exact H. Qed.

Lemma comp_dval : forall G d Gd l e A,
  has_type G d Gd -> lshape Gd -> has_type (G +++ Gd) e A ->
  has_type G (d ,, rec l e) (Gd & (rcd l A)).
Proof.
  introv Hd Hl He. eapply lt_conse; [ exact Hd | exact Hl | eapply t_rec; exact He ].
Qed.

Lemma comp_dtyp : forall G d Gd A,
  has_type G d Gd -> lshape Gd -> wft (G +++ Gd) A ->
  has_type G (d ;; A) (Gd &= A).
Proof. introv Hd Hl Hw. eapply lt_const; eassumption. Qed.

(* a module member is a labelled component, as a value member is *)
Lemma comp_dmod : forall G d Gd l e A,
  has_type G d Gd -> lshape Gd -> has_type (G +++ Gd) e A ->
  has_type G (d ,, rec l e) (Gd & (rcd l A)).
Proof. introv Hd Hl He. eapply comp_dval; eassumption. Qed.

Lemma elabd_lshape : forall G D d Gd, elabd G D d Gd -> lshape Gd.
Proof. introv H. induction H; eauto. Qed.

Lemma comp_merge : forall G e1 e2 G1 G2 d1 Gd1 body Gout,
  has_type G e1 G1 ->
  has_type G e2 G2 ->
  wft top G1 -> wft top G2 ->
  expands ((G & G1) & G2) 1 G1 G1 unit top d1 Gd1 ->
  expands ((G & G1) & G2) 0 G2 G2 d1 Gd1 body Gout ->
  has_type G (app (app (lam (lam body)) e1) e2) Gout.
Proof.
  introv Ht1 Ht2 Hc1 Hc2 Hx1 Hx2.
  forwards HwG: typ_wfe Ht1.
  forwards Hw1: wft_top_weaken Hc1 HwG.
  forwards HwG1: wfe_snoc Hw1.
  forwards Hw2: wft_top_weaken Hc2 HwG1.
  forwards HwG2: wfe_snoc Hw2.
  (* operand 1 at index 1, operand 2 at index 0 *)
  assert (Hg1 : get_var ((G & G1) & G2) 1 G1) by eauto.
  assert (Hg2 : get_var ((G & G1) & G2) 0 G2) by eauto.
  assert (Hnil : has_type ((G & G1) & G2) unit top) by (eapply lt_nil; exact HwG2).
  (* operand 1's entries first, then operand 2's on the same base *)
  forwards Hd1: expands_sound Hx1 Hc1 Hg1 lsh_nil Hnil.
  forwards Hl1: expands_lshape Hx1 lsh_nil.
  forwards Hbody: expands_sound Hx2 Hc2 Hg2 Hl1 Hd1.
  eapply t_app; [ eapply t_app | exact Ht2 ].
  - eapply t_lam. eapply t_lam. exact Hbody.
  - exact Ht1.
Qed.

#[export] Hint Resolve elabd_lshape sig_shape_lshape : core.
