Require Import LibTactics. 
From Stdlib Require Import Arith.
From Stdlib Require Import Lia. 
Require Import Stdlib.Lists.List. 
Require Import Stdlib.Classes.EquivDec. 
Import ListNotations.
From Stdlib Require Import Strings.String.

Require Export Teq.
Set Implicit Arguments.


Lemma not_wf_teq: forall T1 A B T2,
  ~ wfe T1 ->
  ~ teq T1 A B T2.
Proof.
  introv Hnwf Hteq. forwards~: teq_wfe_left Hteq.
Qed.

Lemma not_wf_teq_r: forall T1 A B T2,
  ~ wfe T2 ->
  ~ teq T1 A B T2.
Proof.
  introv Hnwf Hteq. forwards~: teq_wfe_right Hteq.
Qed.

Ltac solve_left := left; introv Hb; 
  match goal with 
     | [ Hb : _ |- _ ] => inverts* Hb
  end.

Ltac solve_right := right; introv Hb; 
  match goal with 
     | [ Hb : _ |- _ ] => inverts* Hb
  end. 

Lemma lookt_dec: forall T i,
  {exists A, lookt T i A} + {~ exists A, lookt T i A}.
Proof.
  intros T. inductions T; intros i; eauto;
  try solve [solve_right; inverts* H].
- destruct* m.
  + forwards~ [?|?]: IHT1 i. 
    * left. destruct* e.
    * solve_right. inverts* H.
  + destruct* i.
    forwards~[?|?]: IHT1 i.
    * left. destruct* e.
    * solve_right. inverts* H.
- destruct* i. 
  + solve_right. inverts* H.
  + forwards~ [?|?]: IHT i.
    * left. destruct* e.
    * solve_right. inverts* H.
Qed.

Lemma check_dec: forall T i,
  {check T i} + {~ check T i}.
Proof.
  intros T. inductions T; intros i; eauto;
  try solve [solve_right].
  - destruct* m.
    + forwards~ [?|?]: IHT1 i.
      solve_right.
    + destruct* i.
      * solve_right.
      * forwards~[?|?]: IHT1 i.
        solve_right.
  - destruct* i. forwards~ [?|?]: IHT i.
    solve_right.
Qed.

Fixpoint lsize (A : typ) : nat :=
  match A with
    | int => 1
    | tvar _ => 1
    | arr A1 A2 => 1 + lsize A1 + lsize A2
    | all A1 => 2 + lsize A1
    | boxt T A1 => 1 + lsize T + lsize A1    
    | mani A1 A2 => 2 + lsize A1 + lsize A2
    | top => 1
    | and A m B => 1 + lsize A + lsize B
    | A&s => 1 + lsize A
    | rcd l A => 1 + lsize A
  end.

Lemma lsize_min: forall A,
  1 <= lsize A.
Proof.
  intros A. inductions A; simpl; lia.
Qed.

Lemma lshape_dec: forall A,
  {~ lshape A} + {lshape A}.
Proof. 
  intros A. inductions A; eauto;
  try solve [left; introv Hb; inverts Hb].
  - destruct* IHA1. 
    left. introv Hb. inverts* Hb.
  - destruct* IHA. 
    left. introv Hb. inverts* Hb.
Qed.

Lemma ls_ass: forall T1 T2 T3 m1 m2,
  lsize (and T1 m1 (and T2 m2 T3)) = lsize (and (and T1 m1 T2) m2 T3).
Proof.
  intros T1 T2 T3 m1 m2. simpl. lia.  
Qed.

Lemma ls_ass_st: forall T1 T2 m1,
  lsize (and T1 m1 (T2 &s)) = lsize ((and T1 m1 T2) &s).
Proof.
  intros. simpl. lia.  
Qed.


Lemma ls_size: forall T2 T1 m,
  lsize (T1 +++ T2) < lsize (and T1 m T2).
Proof.
  intros T2. inductions T2; intros; 
  try solve [simpl; try lia].
  - rewrite <-mcon_cons. rewrite ls_ass. 
    forwards~: IHT2_1 T1 m. simpl.
    lia.
  - rewrite <-mcon_cons_st. rewrite ls_ass_st.
    forwards~: IHT2 T1 m. simpl. lia.
Qed.

Lemma ls_size_2: forall T1 T2 A m m0,
  lsize ((T1 +++ T2) &= A) < lsize (and T1 m (and T2 m0 A)).
Proof.
  intros. simpl.
  forwards~: ls_size T2 T1 m. lia.
Qed. 


Lemma mode_dec: forall (a b : mode), {a = b} + {a <> b}.
Proof. decide equality. Qed.

Lemma lookt_get: forall T i, {B | lookt T i B} + {forall B, ~ lookt T i B}.
Proof.
  intros T. inductions T; intros i;
  try solve [right; introv Hb; inverts Hb].
  - destruct m.
    + forwards~ [ [B HB] |Hno]: IHT1 i.
      * left. exists B. eauto.
      * right. introv Hb. inverts Hb. eapply Hno; eauto.
    + destruct i.
      * left. eexists. eapply lookt_zero.
      * forwards~ [ [B HB] |Hno]: IHT1 i.
        ** left. eexists. eapply lookt_eteq; eauto.
        ** right. introv Hb. inverts Hb. eapply Hno; eauto.
  - destruct i.
    + right. introv Hb. inverts Hb.
    + forwards~ [ [B HB] |Hno]: IHT i.
      * left. eexists. eapply lookt_etvar; eauto.
      * right. introv Hb. inverts Hb. eapply Hno; eauto.
Qed.

(* Decidability of [rigid] *)
Lemma rigid_dec: forall k d T A,
  bindings T A <= k ->
  wft T A ->
  {rigid d T A} + {~ rigid d T A}.
Proof.
  intros k. induction k as [|k IH]; introv Hb Hwf.
  - forwards: bindings_min A T; lia.
  - assert (Hwfe: wfe T) by (eapply wft_wfe; eauto).
    assert (Hmani: forall A1 A2, bindings T (mani A1 A2) = 1 + bindings T A1 + bindings (T &= A1) A2)
      by (intros; unfold bindings; simpl; fold mkb; reflexivity).
    assert (Hand: forall A1 m A2, bindings T (and A1 m A2) = 1 + bindings T A1 + bindings (T +++ A1) A2)
      by (intros; unfold bindings; destruct m; simpl; fold mkb_list; rewrite mkb_eq; reflexivity).
    destruct A.
    + (* int *) left. eapply rigid_int.
    + (* tvar *)
      forwards [ [B Hlk] | Hnlk]: lookt_get T n.
      * forwards Hbb: var_decr Hwfe Hlk.
        forwards HwfB: lookt_wft Hwfe Hlk.
        forwards [Hr | Hnr]: IH d T B; [ lia | eauto | | ].
        ** left. eapply rigid_cvar; eauto.
        ** right. intro Hc. inverts Hc.
           *** eapply lookt_check_false; eauto.
           *** forwards Heq: lookt_det Hlk H0. subst. eauto.
      * forwards [Hck | Hnck]: check_dec T n.
        ** forwards [Hlt | Hnlt]: lt_dec n d.
           *** left. eapply rigid_bvar; eauto.
           *** right. intro Hc. inverts Hc; [ eauto | eapply Hnlk; eauto ].
        ** right. intro Hc. inverts Hc; [ eauto | eapply Hnlk; eauto ].
    + (* arr *)
      assert (Hwf1: wft T A1) by (unfold wft in *; inverts Hwf; eauto).
      assert (Hwf2: wft T A2) by (unfold wft in *; inverts Hwf; eauto).
      assert (Hba: bindings T (arr A1 A2) = 1 + bindings T A1 + bindings T A2)
        by (unfold bindings; simpl; lia).
      forwards [Hr1|Hn1]: IH d T A1; [ lia | eauto | | ].
      * forwards [Hr2|Hn2]: IH d T A2; [ lia | eauto | | ].
        ** left. eapply rigid_arr; eauto.
        ** right. intro Hc. inverts Hc. eauto.
      * right. intro Hc. inverts Hc. eauto.
    + (* all *)
      assert (Hwfa: wft (T &s) A) by (unfold wft in *; inverts Hwf; eauto).
      assert (Hba: bindings T (all A) = 1 + bindings (T &s) A) by (unfold bindings; simpl; lia).
      forwards [Hr|Hn]: IH (S d) (T &s) A; [ lia | eauto | | ].
      * left. eapply rigid_all; eauto.
      * right. intro Hc. inverts Hc. eauto.
    + (* boxt *)
      left. unfold wft in Hwf. inverts Hwf. eapply rigid_box; eauto.
    + (* mani *)
      assert (Hwfa: wft (T &= A1) A2) by (unfold wft in *; inverts Hwf; eauto).
      rewrite Hmani in Hb.
      forwards [Hr|Hn]: IH (S d) (T &= A1) A2; [ lia | eauto | | ].
      * left. eapply rigid_mani; eauto.
      * right. intro Hc. inverts Hc. eauto.
    + (* rcd *)
      assert (Hwfa: wft T A) by (unfold wft in *; inverts Hwf; eauto).
      assert (Hba: bindings T (rcd s A) = 1 + bindings T A) by (unfold bindings; simpl; lia).
      forwards [Hr|Hn]: IH d T A; [ lia | eauto | | ].
      * left. eapply rigid_rcd; eauto.
      * right. intro Hc. inverts Hc. eauto.
    + (* top *) left. eapply rigid_top.
    + (* and *)
      assert (Hwf1: wft T A1) by (unfold wft in *; inverts Hwf; eauto).
      assert (Hwf2: wft (T +++ A1) A2) by (unfold wft in *; inverts Hwf; eauto).
      rewrite Hand in Hb.
      forwards [Hr1|Hn1]: IH d T A1; [ lia | eauto | | ].
      * forwards [Hr2|Hn2]: IH (d + keyLen A1) (T +++ A1) A2; [ lia | eauto | | ].
        ** left. eapply rigid_and; eauto.
        ** right. intro Hc. inverts Hc. eauto.
      * right. intro Hc. inverts Hc. eauto.
    + (* ands *)
      assert (Hwfa: wft T A) by (unfold wft in *; inverts Hwf; eauto).
      assert (Hba: bindings T (A &s) = 1 + bindings T A) by (unfold bindings; simpl; lia).
      forwards [Hr|Hn]: IH d T A; [ lia | eauto | | ].
      * left. eapply rigid_ands; eauto.
      * right. intro Hc. inverts Hc. eauto.
Qed.

Lemma rigid_dec_sp: forall d T A,
  wft T A ->
  {rigid d T A} + {~ rigid d T A}.
Proof.
  intros. eapply rigid_dec; eauto.
Qed.

Lemma wf_dec_size: forall n T,
  lsize T <= n ->
  {~ wfe T} + {wfe T}.
Proof.
  intros n. inductions n; introv Hl.
  forwards~: lsize_min T. lia.

  destruct* T; try solve [solve_left].
  - destruct* T2.
    + forwards~: IHn T1. solve_size.
      destruct* H. solve_left. 
    + forwards~: IHn T1. solve_size.
      destruct* H. solve_left.
      forwards~: lookt_dec T1 n0.
      destruct* H.
      * right. destruct* e.
      * forwards~: check_dec T1 n0.
        destruct* H. solve_left.
    + forwards~: IHn (T1 &= T2_1).
      simpl in Hl. simpl. solve_size.  
      destruct* H.
      * solve_left.
      * forwards~: IHn (T1 &= T2_2). 
        simpl in Hl. simpl. solve_size.
        destruct* H. solve_left.
    + forwards~: IHn T1. solve_size.
      destruct* H. solve_left.
      forwards~: IHn (T1 &s &= T2).
      simpl in Hl. simpl. solve_size.
      destruct* H. solve_left.
    + forwards~: IHn T1. solve_size.
      forwards~: IHn (T2_1 &= T2_2). solve_size.
      destruct* H. solve_left.
      destruct* H0; [ solve_left | ].
      (* wfe T1 and wfe (T2_1 &= T2_2) (= wft T2_1 T2_2) both hold; decide rigidity *)
      forwards [Hr | Hnr]: rigid_dec_sp 0 w0.
      * right. eapply we_box; eauto.
      * left. intro Hc. inverts Hc. eauto.
    + forwards~: IHn (T1 &= T2_1). solve_size.
      forwards~: IHn (T1 &= T2_1 &= T2_2). solve_size.
      destruct* H. solve_left.
      destruct* H0. solve_left.
    + forwards~: IHn (T1 &= T2). solve_size.
      destruct* H. solve_left.
    + forwards~: IHn T1. solve_size.
      destruct* H. solve_left.
    + forwards~: lshape_dec T2_1. destruct H. solve_left.
      forwards~: IHn (T1 &= T2_1). solve_size.
      forwards~: IHn ((T1 +++ T2_1) &= T2_2).
      forwards: ls_size_2 T1 T2_1 T2_2 m m0. simpl in *. lia.
      destruct* H. solve_left.
      destruct* H0. solve_left.
    + forwards~: lshape_dec T2. destruct H. solve_left.
      forwards~: IHn (T1 &= T2). solve_size.
      destruct* H. solve_left.
  - forwards~ :IHn T. solve_size.
    destruct* H. solve_left.
Qed.
      
Lemma wf_dec: forall T,
  {~ wfe T} + {wfe T}.
Proof.
  intros. eapply wf_dec_size; eauto. 
Qed. 


Lemma wft_Sn: forall T n, 
  wft (T &s) (tvar (S n)) ->
  wft T (tvar n).
Proof.
  introv Hw. inverts Hw.
  - eapply we_check; eauto.
    eapply wfe_sinv; eauto.
    inverts H3. eauto.
  - inverts* H3.
    eapply we_get; eauto.
    eapply wfe_sinv; eauto.
Qed.

Lemma wft_Sn_teq: forall T A n, 
  wft (T &= A) (tvar (S n)) ->
  wft T (tvar n).
Proof.
  introv Hw. inverts* Hw.
  - inverts* H3. forwards~: wfe_inv H1. 
    eapply we_check; eauto.
  - inverts* H3. forwards~: wfe_inv H1. 
    eapply we_get; eauto.
Qed.


Lemma wft_or: forall T n,
  wft T (tvar n) ->
  (check T n) + {A | lookt T n A}.
Proof.
  introv Hw. unfold wft in *.
  inductions T; simpl in Hw.
  - right. exfalso. inverts* Hw; inverts H3.
  - right. exfalso. inverts* Hw; inverts H3.
  - right. exfalso. inverts* Hw; inverts H3.
  - right. exfalso. inverts* Hw; inverts H3.
  - right. exfalso. inverts* Hw; inverts H3.
  - right. exfalso. inverts* Hw; inverts H3.
  - right. exfalso. inverts* Hw; inverts H3.
  - right. exfalso. inverts* Hw; inverts H3.
  - destruct m.
    + forwards~ Hwd: del_wft Hw T1.
      { econstructor; eauto. eapply del_refl; eauto. }
      forwards~ Hor: IHT1 Hwd. destruct Hor as [Hck | [A0 Hlk]].
      * left. eapply check_evar; exact Hck.
      * right. exists A0. eapply lookt_evar; exact Hlk.
    + destruct n.
      { right. eexists. eapply lookt_zero. }
      forwards~ Hwd: IHT1 n. { eapply wft_Sn_teq. eauto. }
      destruct Hwd as [Hck | [A0 Hlk]].
      * left. eapply check_eteq; exact Hck.
      * right. exists (tshift 0 A0). eapply lookt_eteq; exact Hlk.
  - destruct n. { left. eapply check_zero. }
    forwards~ Hwd: IHT. { eapply wft_Sn; exact Hw. }
    destruct Hwd as [Hck | [A0 Hlk]].
    * left. eapply check_etvar; exact Hck.
    * right. exists (tshift 0 A0). eapply lookt_etvar; exact Hlk.
Qed.


Ltac solve_look := eapply lookt_check_false; eauto.

Lemma tvar_inv: forall T1 n n1 T2,
  teq T1 (tvar n) (tvar n1) T2 ->
  check T1 n -> check T2 n1 ->
  n = n1.
Proof.
  introv Ht. inductions Ht; introv Hi Hj.
  - reflexivity.
  - exfalso. solve_look.
  - exfalso. solve_look.
Qed.

Lemma tvar_inv_l: forall T1 A n1 T2,
  teq T1 A (tvar n1) T2 -> forall B,
  lookt T2 n1 B -> 
  teq T1 A B T2.
Proof.
  introv Ht. inductions Ht; introv Hl; eauto;
  try solve [exfalso; solve_look];
  try solve [forwards~: lookt_det Hl H; subst; eauto];
  (* eq_boxl: RHS tvar n1 resolves to B via Hl.  New design: eq_boxl has no ~ rbox
     premise; just recurse on the body and carry rigid/wft/wfe. *)
  try solve [eapply eq_boxl;
    [ eapply IHHt; [ reflexivity | exact Hl ]
    | eauto
    | eauto
    | eapply lookt_wft; eauto using wft_wfe, wfe_inv
    | eauto ]].
  (* eq_tvar is discharged by the [exfalso; solve_look] solve above (check vs lookt). *)
  (* eq_manil: padded premise carries tvar (S n1); rebuild via lookt_etvar + eq_manil. *)
  - eapply eq_manil. eapply IHHt;
    [ simpl; reflexivity | eapply lookt_etvar; exact Hl ].
Qed.

Lemma tvar_inv_l2: forall T1 A n1 T2,
  teq T2 (tvar n1) A T1-> forall B,
  lookt T2 n1 B -> 
  teq T2 B A T1.
Proof.
  introv Ht Hl. eapply teq_sym.
  eapply tvar_inv_l; eauto.
  eapply teq_sym; eauto.
Qed.

(* B = boxt: for a non-box / non-var / non-mani left operand A, the only rule that can
   relate [A] to a box on the right is [eq_boxr]; decide its side conditions. *)
Lemma boxr_dec: forall T1 A Tb Bb T2,
  ~ is_box A -> (forall X, A <> tvar X) -> (forall C D, A <> mani C D) ->
  wfe T2 -> wfe T1 ->
  {teq T1 A Bb Tb} + {~ teq T1 A Bb Tb} ->
  {teq T1 A (boxt Tb Bb) T2} + {~ teq T1 A (boxt Tb Bb) T2}.
Proof.
  introv Hnb Hntv Hnm Hw2 Hw1 Hsub. destruct Hsub as [Hsub | Hnsub].
  - (* new eq_boxr side condition is the single box-wft [wft T2 (boxt Tb Bb)];
       decide it directly via [wf_dec]. *)
    destruct (wf_dec (T2 &= (boxt Tb Bb))) as [Hnwft | Hwft].
    + right. intro Hc. inverts Hc; try solve [ apply Hnb; econstructor ]; try solve [ eapply Hntv; reflexivity ]; try solve [ eapply Hnm; reflexivity ].
      apply Hnwft. assumption.
    + left. eapply eq_boxr; eauto.
  - right. intro Hc. inverts Hc; try solve [ apply Hnb; econstructor ]; try solve [ eapply Hntv; reflexivity ]; try solve [ eapply Hnm; reflexivity ].
    eauto.
Qed.

(* A = boxt against a non-box / non-var / non-mani right operand B: only [eq_boxl]. *)
Lemma boxl_dec: forall T1 Ta Ab B T2,
  ~ is_box B -> (forall Y, B <> tvar Y) -> (forall C D, B <> mani C D) ->
  wfe T2 -> wfe T1 ->
  {teq Ta Ab B T2} + {~ teq Ta Ab B T2} ->
  {teq T1 (boxt Ta Ab) B T2} + {~ teq T1 (boxt Ta Ab) B T2}.
Proof.
  introv Hnb Hntv Hnm Hw2 Hw1 Hsub. destruct Hsub as [Hsub | Hnsub].
  - (* new eq_boxl side condition is the single box-wft [wft T1 (boxt Ta Ab)];
       decide it directly via [wf_dec]. *)
    destruct (wf_dec (T1 &= (boxt Ta Ab))) as [Hnwft | Hwft].
    + right. intro Hc. inverts Hc; try solve [ apply Hnb; econstructor ]; try solve [ eapply Hntv; reflexivity ]; try solve [ eapply Hnm; reflexivity ].
      apply Hnwft. assumption.
    + left. eapply eq_boxl; eauto.
  - right. intro Hc. inverts Hc; try solve [ apply Hnb; econstructor ]; try solve [ eapply Hntv; reflexivity ]; try solve [ eapply Hnm; reflexivity ].
    eauto.
Qed.


Lemma boxbox_dec: forall T1 Ta Ab Tb Bb T2,
  wfe T1 -> wfe T2 ->
  {teq T1 (boxt Ta Ab) (boxt Tb Bb) T2} +
  {~ (teq Ta Ab (boxt Tb Bb) T2 /\ rigid 0 Ta Ab)} ->
  {teq T1 (boxt Ta Ab) Bb Tb} + {~ teq T1 (boxt Ta Ab) Bb Tb} ->
  {teq T1 (boxt Ta Ab) (boxt Tb Bb) T2} + {~ teq T1 (boxt Ta Ab) (boxt Tb Bb) T2}.
Proof.
  introv Hw1 Hw2 Hroute Hsubr. destruct Hroute as [Hbl | Hnbl].
  - left. exact Hbl.
  - destruct Hsubr as [Hsr | Hnsr].
    + (* eq_boxr side condition is the single box-wft [wft T2 (boxt Tb Bb)]. *)
      destruct (wf_dec (T2 &= (boxt Tb Bb))) as [Hnwft | Hwft].
      * right. intro Hc. inverts Hc.
        ** (* eq_boxl: rigid 0 Ta Ab recovered from the box-wft hyp *)
           apply Hnbl; splits; eauto using wft_box_rigid.
        ** (* eq_boxr: box-wft hyp [wft T2 (boxt Tb Bb)] contradicts Hnwft *)
           apply Hnwft. assumption.
      * left. eapply eq_boxr; eauto.
    + right. intro Hc. inverts Hc.
      ** apply Hnbl; splits; eauto using wft_box_rigid.
      ** eauto.
Qed.

Lemma eqr_dec2: forall T1 A n0 T2,
  ~ is_box A -> (forall X, A <> tvar X) -> (forall C D, A <> mani C D) ->
  wfe T1 -> wfe T2 ->
  (forall B', lookt T2 n0 B' -> {teq T1 A B' T2} + {~ teq T1 A B' T2}) ->
  {teq T1 A (tvar n0) T2} + {~ teq T1 A (tvar n0) T2}.
Proof.
  introv Hnb Hntv Hnm Hw1 Hw2 Hrec.
  forwards~ [Hnwf | Hwf]: wf_dec (T2 &= (tvar n0)).
  - right. intro Hc. forwards~: teq_wft_right Hc.
  - forwards [ Hi | [B' Hl] ]: wft_or Hwf.
    + right. intro Hc. inverts Hc;
        try solve [ apply Hnb; econstructor ]; try solve [ eapply Hntv; reflexivity ]; try solve [ eapply Hnm; reflexivity ];
        try solve [ exfalso; eauto using lookt_check_false ].
    + forwards [Hr | Hnr]: Hrec B' Hl.
      * left. eapply eq_eqr; eauto.
      * right. intro Hc. inverts Hc;
          try solve [ apply Hnb; econstructor ]; try solve [ eapply Hntv; reflexivity ]; try solve [ eapply Hnm; reflexivity ].
        forwards Heq: lookt_det Hl H0. subst. eauto.
Qed.

Lemma boxl_route_dec: forall T1 Ta Ab B T2,
  wfe T1 ->
  {teq Ta Ab B T2} + {~ teq Ta Ab B T2} ->
  {teq T1 (boxt Ta Ab) B T2} +
  {~ (teq Ta Ab B T2 /\ rigid 0 Ta Ab)}.
Proof.
  introv Hw1 Hsub. destruct Hsub as [Hsub | Hnsub].
  - forwards Hwfa: teq_wft_left Hsub. forwards Hwfb: teq_wft_right Hsub.
    forwards [Hrig | Hnrig]: rigid_dec_sp 0 Hwfa.
    + left. eapply eq_boxl; [ exact Hsub | unfold wft; eapply we_box; eauto ].
    + right. intro Hc. destruct Hc as (? & Hrigc). eauto.
  - right. intro Hc. destruct Hc as (Hsubc & ?). eauto.
Qed.

(* Size-neutral padded recursion helpers.  *)
Lemma manil_padR: forall n,
  (forall T A B T', bindings T A + bindings T' B <= n -> {teq T A B T'} + {~ teq T A B T'}) ->
  forall T1 A1 A2 B T2, bindings (T1 &= A1) A2 + bindings T2 B <= n ->
  {teq (T1 &= A1) A2 (tshift 0 B) (T2 &s)} + {~ teq (T1 &= A1) A2 (tshift 0 B) (T2 &s)}.
Proof.
  introv IH Hb. apply IH. rewrite <- (bindings_zero2 B T2). exact Hb.
Qed.

Lemma manir_padL: forall n,
  (forall T A B T', bindings T A + bindings T' B <= n -> {teq T A B T'} + {~ teq T A B T'}) ->
  forall T1 A B1 B2 T2, bindings T1 A + bindings (T2 &= B1) B2 <= n ->
  {teq (T1 &s) (tshift 0 A) B2 (T2 &= B1)} + {~ teq (T1 &s) (tshift 0 A) B2 (T2 &= B1)}.
Proof.
  introv IH Hb. apply IH. rewrite <- (bindings_zero2 A T1). exact Hb.
Qed.

Lemma manir_dec: forall T1 A B1 B2 T2,
  (forall X, A <> tvar X) -> (forall Tb Bb, A <> boxt Tb Bb) -> (forall C D, A <> mani C D) ->
  {teq (T1 &s) (tshift 0 A) B2 (T2 &= B1)} + {~ teq (T1 &s) (tshift 0 A) B2 (T2 &= B1)} ->
  {teq T1 A (mani B1 B2) T2} + {~ teq T1 A (mani B1 B2) T2}.
Proof.
  introv Hntv Hnb Hnm Hsub. destruct Hsub as [Hr | Hnr].
  - left. eapply eq_manir; eauto.
  - right. intro Hb. inverts Hb;
      try solve [ eapply Hntv; reflexivity ];
      try solve [ eapply Hnb; reflexivity ];
      try solve [ eapply Hnm; reflexivity ].
    eauto.
Qed.

Lemma manil_dec: forall T1 A1 A2 B T2,
  (forall X, B <> tvar X) -> (forall Tb Bb, B <> boxt Tb Bb) -> (forall C D, B <> mani C D) ->
  {teq (T1 &= A1) A2 (tshift 0 B) (T2 &s)} + {~ teq (T1 &= A1) A2 (tshift 0 B) (T2 &s)} ->
  {teq T1 (mani A1 A2) B T2} + {~ teq T1 (mani A1 A2) B T2}.
Proof.
  introv Hntv Hnb Hnm Hsub. destruct Hsub as [Hr | Hnr].
  - left. eapply eq_manil; eauto.
  - right. intro Hb. inverts Hb;
      try solve [ eapply Hntv; reflexivity ];
      try solve [ eapply Hnb; reflexivity ];
      try solve [ eapply Hnm; reflexivity ].
    eauto.
Qed.

Lemma manilr_dec: forall T1 A1 A2 B1 B2 T2,
  {teq (T1 &= A1) A2 (tshift 0 (mani B1 B2)) (T2 &s)} + {~ teq (T1 &= A1) A2 (tshift 0 (mani B1 B2)) (T2 &s)} ->
  {teq (T1 &s) (tshift 0 (mani A1 A2)) B2 (T2 &= B1)} + {~ teq (T1 &s) (tshift 0 (mani A1 A2)) B2 (T2 &= B1)} ->
  {teq T1 (mani A1 A2) (mani B1 B2) T2} + {~ teq T1 (mani A1 A2) (mani B1 B2) T2}.
Proof.
  introv Hl Hr. destruct Hl as [Hl | Hnl].
  - left. eapply eq_manil; eauto.
  - destruct Hr as [Hr | Hnr].
    + left. eapply eq_manir; eauto.
    + right. intro Hb. inverts Hb; eauto.
Qed.


Lemma manil_box_dec: forall T1 A1 A2 Tb Bb T2,
  wfe T2 ->
  {teq (T1 &= A1) A2 (tshift 0 (boxt Tb Bb)) (T2 &s)} + {~ teq (T1 &= A1) A2 (tshift 0 (boxt Tb Bb)) (T2 &s)} ->
  {teq T1 (mani A1 A2) Bb Tb} + {~ teq T1 (mani A1 A2) Bb Tb} ->
  {teq T1 (mani A1 A2) (boxt Tb Bb) T2} + {~ teq T1 (mani A1 A2) (boxt Tb Bb) T2}.
Proof.
  introv Hw2 Hl Hr. destruct Hl as [Hl | Hnl].
  - left. eapply eq_manil; eauto.
  - destruct Hr as [Hr | Hnr].
    + destruct (wf_dec (T2 &= (boxt Tb Bb))) as [Hnwft | Hwft].
      * right. intro Hb. inverts Hb; eauto.
      * left. eapply eq_boxr; eauto.
    + right. intro Hb. inverts Hb; eauto.
Qed.

Lemma manil_var_dec: forall T1 A1 A2 X T2,
  wfe T1 -> wfe T2 ->
  {teq (T1 &= A1) A2 (tshift 0 (tvar X)) (T2 &s)} + {~ teq (T1 &= A1) A2 (tshift 0 (tvar X)) (T2 &s)} ->
  (forall B', lookt T2 X B' -> {teq T1 (mani A1 A2) B' T2} + {~ teq T1 (mani A1 A2) B' T2}) ->
  {teq T1 (mani A1 A2) (tvar X) T2} + {~ teq T1 (mani A1 A2) (tvar X) T2}.
Proof.
  introv Hw1 Hw2 Hl Hrec. destruct Hl as [Hl | Hnl].
  - left. eapply eq_manil; eauto.
  - forwards~ [Hnwf | Hwf]: wf_dec (T2 &= (tvar X)).
    + right. intro Hc. forwards~: teq_wft_right Hc.
    + forwards [ Hi | [B' Hlk] ]: wft_or Hwf.
      * right. intro Hb. inverts Hb;
          try solve [ exfalso; eauto using lookt_check_false ].
      * forwards [Hr | Hnr]: Hrec B' Hlk.
        ** left. eapply eq_eqr; eauto.
        ** right. intro Hb. inverts Hb; eauto.
           forwards Heq: lookt_det Hlk H0. subst. eauto.
Qed.

(* Decidability of [teq]. *)
Lemma teq_dec_size: forall n T1 A B T2,
  bindings T1 A + bindings T2 B <= n ->
  {teq T1 A B T2} + {~ teq T1 A B T2}.
Proof.
  intros n. inductions n; introv Hl.
  - forwards~: bindings_min A T1. lia.
  - forwards~ [Hnw1|Hw1]: wf_dec T1.
    + right. eapply not_wf_teq; eauto.
    + forwards~ [Hnw2|Hw2]: wf_dec T2.
      * right. eapply not_wf_teq_r; eauto.
      * destruct A.
{ (* int *)
  assert (Hmani2: forall B1 B2, bindings T2 (mani B1 B2) = 1 + bindings T2 B1 + bindings (T2 &= B1) B2)
       by (intros; unfold bindings; simpl; fold mkb; reflexivity).
  assert (Hbox2: forall Tb Bb, bindings T2 (boxt Tb Bb) = S (bindings Tb Bb))
       by (intros; unfold bindings; reflexivity).
  destruct B;
    try solve [ right; intro Hb; inverts Hb ].
  - left. eapply eq_int; eauto.
  - eapply eqr_dec2; eauto;
      try solve [ intro Hc; inverts Hc ]; try solve [ intros; discriminate ].
    intros B' Hl0. forwards Hbb: var_decr Hw2 Hl0. eapply IHn. lia.
  - rewrite Hbox2 in Hl. eapply boxr_dec; eauto;
      try solve [ intro Hc; inverts Hc ]; try solve [ intros; discriminate ].
    eapply IHn. assert (1 <= bindings T1 int) by eapply bindings_min. lia.
  - rewrite Hmani2 in Hl.
    eapply manir_dec;
      try solve [ intro Hc; inverts Hc ]; try solve [ intros; discriminate ].
    eapply (manir_padL IHn). lia. }
{ (* tvar n0 *)
  assert (Hmani2: forall B1 B2, bindings T2 (mani B1 B2) = 1 + bindings T2 B1 + bindings (T2 &= B1) B2)
       by (intros; unfold bindings; simpl; fold mkb; reflexivity).
  assert (Hbox2: forall Tb Bb, bindings T2 (boxt Tb Bb) = S (bindings Tb Bb))
       by (intros; unfold bindings; reflexivity).
  forwards~ [Hnwf1 | Hwf1]: wf_dec (T1 &= (tvar n0)).
  { right. intro Hc. forwards~: teq_wft_left Hc. }
  forwards [ Hi | [A' Hla] ]: wft_or Hwf1.
  - destruct B;
      try solve [ right; intro Hb; inverts Hb; try solve [exfalso; solve_look] ].
    + forwards~ [Hnwf2 | Hwf2]: wf_dec (T2 &= (tvar n1)).
      { right. intro Hc. forwards~: teq_wft_right Hc. }
      forwards [ Hj | [B' Hlb] ]: wft_or Hwf2.
      * forwards~ [Heq|Hne]: eq_nat_dec n0 n1.
        ** subst. left. eapply eq_tvar; eauto.
        ** right. intro Hb. forwards~: tvar_inv Hb Hi Hj.
      * forwards Hbb: var_decr Hw2 Hlb.
        forwards [Hr|Hnr]: IHn T1 (tvar n0) B' T2; [ lia | | ].
        ** left. eapply eq_eqr; eauto.
        ** right. intro Hb. eapply Hnr. eapply tvar_inv_l; eauto.
    + rewrite Hbox2 in Hl.
      forwards [Hr|Hnr]: IHn T1 (tvar n0) B2 B1; [ lia | | ].
      * forwards Hwfb: teq_wft_right Hr.
        forwards [Hrig|Hnrig]: rigid_dec_sp 0 Hwfb.
        ** left. eapply eq_boxr; [ exact Hr | unfold wft; eapply we_box; eauto ].
        ** right. intro Hb. inverts Hb;
             try solve [ exfalso; solve_look ].
           apply Hnrig. eapply wft_box_rigid; eauto.
      * right. intro Hb. inverts Hb;
          try solve [ exfalso; solve_look ].
        eauto.
    + rewrite Hmani2 in Hl.
      forwards [Hr|Hnr]: (manir_padL IHn) T1 (tvar n0) B1 B2 T2; [ lia | | ].
      * left. eapply eq_manir; eauto.
      * right. intro Hb. inverts Hb;
          try solve [ exfalso; solve_look ].
        eauto.
  - forwards Hbb: var_decr Hw1 Hla.
    forwards [Hr|Hnr]: IHn T1 A' B T2; [ lia | | ].
    + left. eapply eq_eql; eauto.
    + right. intro Hb. eapply Hnr. eapply tvar_inv_l2; eauto. }
{ (* arr *)
  assert (Hmani2: forall B1 B2, bindings T2 (mani B1 B2) = 1 + bindings T2 B1 + bindings (T2 &= B1) B2)
       by (intros; unfold bindings; simpl; fold mkb; reflexivity).
  assert (Hbox2: forall Tb Bb, bindings T2 (boxt Tb Bb) = S (bindings Tb Bb))
       by (intros; unfold bindings; reflexivity).
  assert (Harr1: bindings T1 (arr A1 A2) = 1 + bindings T1 A1 + bindings T1 A2)
       by (unfold bindings; simpl; lia).
  assert (Harr2: forall B1 B2, bindings T2 (arr B1 B2) = 1 + bindings T2 B1 + bindings T2 B2)
       by (intros; unfold bindings; simpl; lia).
  destruct B;
    try solve [ right; intro Hb; inverts Hb ].
  - eapply eqr_dec2; eauto;
      try solve [ intro Hc; inverts Hc ]; try solve [ intros; discriminate ].
    intros B' Hl0. forwards Hbb: var_decr Hw2 Hl0. eapply IHn. lia.
  - rewrite Harr1 in Hl. rewrite Harr2 in Hl.
    forwards [Hr1|Hn1]: IHn T1 A1 B1 T2; [ lia | | ].
    + forwards [Hr2|Hn2]: IHn T1 A2 B2 T2; [ lia | | ].
      * left. eapply eq_arr; eauto.
      * right. intro Hb. inverts Hb. eauto.
    + right. intro Hb. inverts Hb. eauto.
  - rewrite Hbox2 in Hl. eapply boxr_dec; eauto;
      try solve [ intro Hc; inverts Hc ]; try solve [ intros; discriminate ].
    eapply IHn. lia.
  - rewrite Hmani2 in Hl.
    eapply manir_dec;
      try solve [ intro Hc; inverts Hc ]; try solve [ intros; discriminate ].
    eapply (manir_padL IHn). lia. }
{ (* all *)
  assert (Hmani2: forall B1 B2, bindings T2 (mani B1 B2) = 1 + bindings T2 B1 + bindings (T2 &= B1) B2)
       by (intros; unfold bindings; simpl; fold mkb; reflexivity).
  assert (Hbox2: forall Tb Bb, bindings T2 (boxt Tb Bb) = S (bindings Tb Bb))
       by (intros; unfold bindings; reflexivity).
  assert (Hall1: bindings T1 (all A) = 1 + bindings (T1 &s) A)
       by (unfold bindings; simpl; lia).
  assert (Hall2: forall C, bindings T2 (all C) = 1 + bindings (T2 &s) C)
       by (intros; unfold bindings; simpl; lia).
  destruct B;
    try solve [ right; intro Hb; inverts Hb ].
  - eapply eqr_dec2; eauto;
      try solve [ intro Hc; inverts Hc ]; try solve [ intros; discriminate ].
    intros B' Hl0. forwards Hbb: var_decr Hw2 Hl0. eapply IHn. lia.
  - rewrite Hall1 in Hl. rewrite Hall2 in Hl.
    forwards [Hr|Hnr]: IHn (T1 &s) A B (T2 &s); [ lia | | ].
    + left. eapply eq_all; eauto.
    + right. intro Hb. inverts Hb. eauto.
  - rewrite Hbox2 in Hl. eapply boxr_dec; eauto;
      try solve [ intro Hc; inverts Hc ]; try solve [ intros; discriminate ].
    eapply IHn. lia.
  - rewrite Hmani2 in Hl.
    eapply manir_dec;
      try solve [ intro Hc; inverts Hc ]; try solve [ intros; discriminate ].
    eapply (manir_padL IHn). lia. }
{ (* boxt A1 A2 *)
  assert (Hbox1: bindings T1 (boxt A1 A2) = S (bindings A1 A2)) by (unfold bindings; reflexivity).
  assert (Hmani2: forall C1 C2, bindings T2 (mani C1 C2) = 1 + bindings T2 C1 + bindings (T2 &= C1) C2)
       by (intros; unfold bindings; simpl; fold mkb; reflexivity).
  assert (Hbox2: forall Tb Bb, bindings T2 (boxt Tb Bb) = S (bindings Tb Bb))
       by (intros; unfold bindings; reflexivity).
  destruct B.
  - rewrite Hbox1 in Hl. eapply boxl_dec; eauto;
      try solve [ intro Hc; inverts Hc ]; try solve [ intros; discriminate ].
    eapply IHn. lia.
  - forwards Hsub: IHn A1 A2 (tvar n0) T2; [ rewrite Hbox1 in Hl; lia | ].
    destruct (boxl_route_dec Hw1 Hsub) as [Hbl|Hnbl].
    + left. exact Hbl.
    + forwards~ [Hnwf2 | Hwf2]: wf_dec (T2 &= (tvar n0)).
      { right. intro Hc. forwards~: teq_wft_right Hc. }
      forwards [ Hj | [B' Hlb] ]: wft_or Hwf2.
      * right. intro Hb. inverts Hb;
          try solve [ exfalso; eauto using lookt_check_false ];
          try solve [ apply Hnbl; splits; eauto using wft_box_rigid ].
      * forwards Hbb: var_decr Hw2 Hlb.
        forwards [Hr|Hnr]: IHn T1 (boxt A1 A2) B' T2; [ rewrite Hbox1; rewrite Hbox1 in Hl; lia | | ].
        ** left. eapply eq_eqr; eauto.
        ** right. intro Hb. inverts Hb;
             try solve [ apply Hnbl; splits; eauto using wft_box_rigid ];
             try solve [ match goal with Ha: lookt T2 n0 ?x, Hbb2: lookt T2 n0 ?y |- _ =>
                           forwards Heq: lookt_det Ha Hbb2; subst end; eauto ].
  - rewrite Hbox1 in Hl. eapply boxl_dec; eauto;
      try solve [ intro Hc; inverts Hc ]; try solve [ intros; discriminate ].
    eapply IHn. lia.
  - rewrite Hbox1 in Hl. eapply boxl_dec; eauto;
      try solve [ intro Hc; inverts Hc ]; try solve [ intros; discriminate ].
    eapply IHn. lia.
  - (* boxt B1 B2 : box-vs-box.  Try the eq_boxl route for RHS (boxt B1 B2); on
       failure fall back to eq_boxr via the smaller subproblem teq T1 (boxt A1 A2) B2 B1. *)
    forwards Hsub: IHn A1 A2 (boxt B1 B2) T2; [ rewrite Hbox1 in Hl; rewrite Hbox2; rewrite Hbox2 in Hl; lia | ].
    eapply boxbox_dec; eauto.
    + eapply boxl_route_dec; eauto.
    + eapply IHn. rewrite Hbox1; rewrite Hbox1 in Hl; rewrite Hbox2 in Hl. lia.
  - forwards Hsub: IHn A1 A2 (mani B1 B2) T2; [ rewrite Hbox1 in Hl; lia | ].
    destruct (boxl_route_dec Hw1 Hsub) as [Hbl|Hnbl].
    + left. exact Hbl.
    + rewrite Hmani2 in Hl.
      forwards [Hr|Hnr]: (manir_padL IHn) T1 (boxt A1 A2) B1 B2 T2;
        [ rewrite Hbox1 in Hl; rewrite Hbox1; lia | | ].
      * left. eapply eq_manir; eauto.
      * right. intro Hb. inverts Hb;
          try solve [ apply Hnbl; splits; eauto using wft_box_rigid ];
          try solve [ eauto ].
  - rewrite Hbox1 in Hl. eapply boxl_dec; eauto;
      try solve [ intro Hc; inverts Hc ]; try solve [ intros; discriminate ].
    eapply IHn. lia.
  - rewrite Hbox1 in Hl. eapply boxl_dec; eauto;
      try solve [ intro Hc; inverts Hc ]; try solve [ intros; discriminate ].
    eapply IHn. lia.
  - rewrite Hbox1 in Hl. eapply boxl_dec; eauto;
      try solve [ intro Hc; inverts Hc ]; try solve [ intros; discriminate ].
    eapply IHn. lia.
  - rewrite Hbox1 in Hl. eapply boxl_dec; eauto;
      try solve [ intro Hc; inverts Hc ]; try solve [ intros; discriminate ].
    eapply IHn. lia. }
{ (* mani A1 A2 *)
  assert (Hmani1: forall A0 A3, bindings T1 (mani A0 A3) = 1 + bindings T1 A0 + bindings (T1 &= A0) A3)
       by (intros; unfold bindings; simpl; fold mkb; reflexivity).
  assert (Hmani2: forall B1 B2, bindings T2 (mani B1 B2) = 1 + bindings T2 B1 + bindings (T2 &= B1) B2)
       by (intros; unfold bindings; simpl; fold mkb; reflexivity).
  assert (Hbox2: forall Tb Bb, bindings T2 (boxt Tb Bb) = S (bindings Tb Bb))
       by (intros; unfold bindings; reflexivity).
  rewrite Hmani1 in Hl.
  (* eq_manil fires for every B; the [tshift 0 B] / [&s] padding keeps the subproblem
     size-neutral (bindings_zero2).  For B = tvar / box / mani an alternative rule
     (eq_eqr / eq_boxr / eq_manir) may also fire, so try eq_manil first then the
     B-specific route. *)
  destruct B;
    try solve [ eapply manil_dec;
      try solve [ intro Hc; inverts Hc ]; try solve [ intros; discriminate ];
      eapply (manil_padR IHn); lia ].
  - (* B = tvar n0 *)
    eapply manil_var_dec; eauto.
    + eapply (manil_padR IHn). lia.
    + intros B' Hl0. forwards Hbb: var_decr Hw2 Hl0. eapply IHn. rewrite Hmani1. lia.
  - (* B = boxt Tb Bb : eq_manil OR eq_boxr *)
    rewrite Hbox2 in Hl.
    eapply manil_box_dec; eauto.
    + eapply (manil_padR IHn). rewrite Hbox2. lia.
    + eapply IHn. rewrite Hmani1. lia.
  - (* B = mani B1 B2 : eq_manil OR eq_manir *)
    rewrite Hmani2 in Hl.
    eapply manilr_dec.
    + eapply (manil_padR IHn). rewrite Hmani2. lia.
    + eapply (manir_padL IHn). rewrite Hmani1. lia. }
{ (* rcd s A *)
  assert (Hmani2: forall B1 B2, bindings T2 (mani B1 B2) = 1 + bindings T2 B1 + bindings (T2 &= B1) B2)
       by (intros; unfold bindings; simpl; fold mkb; reflexivity).
  assert (Hbox2: forall Tb Bb, bindings T2 (boxt Tb Bb) = S (bindings Tb Bb))
       by (intros; unfold bindings; reflexivity).
  assert (Hrcd1: bindings T1 (rcd s A) = 1 + bindings T1 A) by (unfold bindings; simpl; lia).
  assert (Hrcd2: forall l C, bindings T2 (rcd l C) = 1 + bindings T2 C) by (intros; unfold bindings; simpl; lia).
  destruct B;
    try solve [ right; intro Hb; inverts Hb ].
  - eapply eqr_dec2; eauto;
      try solve [ intro Hc; inverts Hc ]; try solve [ intros; discriminate ].
    intros B' Hl0. forwards Hbb: var_decr Hw2 Hl0. eapply IHn. lia.
  - rewrite Hbox2 in Hl. eapply boxr_dec; eauto;
      try solve [ intro Hc; inverts Hc ]; try solve [ intros; discriminate ].
    eapply IHn. lia.
  - rewrite Hmani2 in Hl.
    eapply manir_dec;
      try solve [ intro Hc; inverts Hc ]; try solve [ intros; discriminate ].
    eapply (manir_padL IHn). lia.
  - forwards~ [Heq|Hne]: string_dec s s0.
    + subst. rewrite Hrcd1 in Hl. rewrite Hrcd2 in Hl.
      forwards [Hr|Hnr]: IHn T1 A B T2; [ lia | | ].
      * left. eapply eq_rcd; eauto.
      * right. intro Hb. inverts Hb. eauto.
    + right. intro Hb. inverts Hb. eauto. }
{ (* top *)
  assert (Hmani2: forall B1 B2, bindings T2 (mani B1 B2) = 1 + bindings T2 B1 + bindings (T2 &= B1) B2)
       by (intros; unfold bindings; simpl; fold mkb; reflexivity).
  assert (Hbox2: forall Tb Bb, bindings T2 (boxt Tb Bb) = S (bindings Tb Bb))
       by (intros; unfold bindings; reflexivity).
  destruct B;
    try solve [ right; intro Hb; inverts Hb ].
  - eapply eqr_dec2; eauto;
      try solve [ intro Hc; inverts Hc ]; try solve [ intros; discriminate ].
    intros B' Hl0. forwards Hbb: var_decr Hw2 Hl0. eapply IHn. lia.
  - rewrite Hbox2 in Hl. eapply boxr_dec; eauto;
      try solve [ intro Hc; inverts Hc ]; try solve [ intros; discriminate ].
    eapply IHn. assert (1 <= bindings T1 top) by eapply bindings_min. lia.
  - rewrite Hmani2 in Hl.
    eapply manir_dec;
      try solve [ intro Hc; inverts Hc ]; try solve [ intros; discriminate ].
    eapply (manir_padL IHn). lia.
  - left. eapply eq_top; eauto. }
{ (* and A1 m A2 *)
  assert (Hmani2: forall C1 C2, bindings T2 (mani C1 C2) = 1 + bindings T2 C1 + bindings (T2 &= C1) C2)
       by (intros; unfold bindings; simpl; fold mkb; reflexivity).
  assert (Hbox2: forall Tb Bb, bindings T2 (boxt Tb Bb) = S (bindings Tb Bb))
       by (intros; unfold bindings; reflexivity).
  assert (Hand1: bindings T1 (and A1 m A2) = 1 + bindings T1 A1 + bindings (T1 +++ A1) A2)
       by (unfold bindings; destruct m; simpl; fold mkb_list; rewrite mkb_eq; reflexivity).
  assert (Hand2: forall C1 m0 C2, bindings T2 (and C1 m0 C2) = 1 + bindings T2 C1 + bindings (T2 +++ C1) C2)
       by (intros; unfold bindings; destruct m0; simpl; fold mkb_list; rewrite mkb_eq; reflexivity).
  destruct B;
    try solve [ right; intro Hb; inverts Hb ].
  - eapply eqr_dec2; eauto;
      try solve [ intro Hc; inverts Hc ]; try solve [ intros; discriminate ].
    intros B' Hl0. forwards Hbb: var_decr Hw2 Hl0. eapply IHn. lia.
  - rewrite Hbox2 in Hl. eapply boxr_dec; eauto;
      try solve [ intro Hc; inverts Hc ]; try solve [ intros; discriminate ].
    eapply IHn. lia.
  - rewrite Hmani2 in Hl.
    eapply manir_dec;
      try solve [ intro Hc; inverts Hc ]; try solve [ intros; discriminate ].
    eapply (manir_padL IHn). lia.
  - (* and B1 m0 B2 *)
    destruct (mode_dec m m0) as [Hmeq | Hmne];
      [ subst | right; intro Hb; inverts Hb; eauto ].
    forwards~ [Hnlsa | Hlsa]: lshape_dec A1;
      [ right; intro Hb; inverts Hb; eauto | ].
    forwards~ [Hnlsb | Hlsb]: lshape_dec B1;
      [ right; intro Hb; inverts Hb; eauto | ].
    rewrite Hand1 in Hl. rewrite Hand2 in Hl.
    forwards [Hr1|Hn1]: IHn T1 A1 B1 T2; [ lia | | ].
    + forwards [Hr2|Hn2]: IHn (T1 +++ A1) A2 B2 (T2 +++ B1); [ lia | | ].
      * left. eapply eq_and; eauto.
      * right. intro Hb. inverts Hb. eauto.
    + right. intro Hb. inverts Hb. eauto. }
{ (* A &s *)
  assert (Hmani2: forall C1 C2, bindings T2 (mani C1 C2) = 1 + bindings T2 C1 + bindings (T2 &= C1) C2)
       by (intros; unfold bindings; simpl; fold mkb; reflexivity).
  assert (Hbox2: forall Tb Bb, bindings T2 (boxt Tb Bb) = S (bindings Tb Bb))
       by (intros; unfold bindings; reflexivity).
  assert (Hands1: bindings T1 (A &s) = 1 + bindings T1 A) by (unfold bindings; simpl; lia).
  assert (Hands2: forall C, bindings T2 (C &s) = 1 + bindings T2 C) by (intros; unfold bindings; simpl; lia).
  destruct B;
    try solve [ right; intro Hb; inverts Hb ].
  - eapply eqr_dec2; eauto;
      try solve [ intro Hc; inverts Hc ]; try solve [ intros; discriminate ].
    intros B' Hl0. forwards Hbb: var_decr Hw2 Hl0. eapply IHn. lia.
  - rewrite Hbox2 in Hl. eapply boxr_dec; eauto;
      try solve [ intro Hc; inverts Hc ]; try solve [ intros; discriminate ].
    eapply IHn. lia.
  - rewrite Hmani2 in Hl.
    eapply manir_dec;
      try solve [ intro Hc; inverts Hc ]; try solve [ intros; discriminate ].
    eapply (manir_padL IHn). lia.
  - forwards~ [Hnlsa | Hlsa]: lshape_dec A.
    + right. intro Hb. inverts Hb. eauto.
    + forwards~ [Hnlsb | Hlsb]: lshape_dec B.
      * right. intro Hb. inverts Hb. eauto.
      * rewrite Hands1 in Hl. rewrite Hands2 in Hl.
        forwards [Hr|Hnr]: IHn T1 A B T2; [ lia | | ].
        ** left. eapply eq_ands; eauto.
        ** right. intro Hb. inverts Hb. eauto. }
Qed.

Lemma teq_dec: forall T1 A B T2,
  {teq T1 A B T2} + {~ teq T1 A B T2}.
Proof.
  intros. eapply teq_dec_size; eauto.
Qed.