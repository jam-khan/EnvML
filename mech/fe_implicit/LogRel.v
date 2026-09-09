Require Import LibTactics.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
Require Export Teq ExpSyntax Semantics Typing.
Set Implicit Arguments.



Lemma value_irred : forall v ve e, value v -> ~ step ve v e.
Proof.
  introv Hv. gen ve e. induction Hv; introv Hs; inverts Hs; eauto.
  eapply IHHv; eauto. eapply IHHv1; eauto. eapply IHHv2; eauto.
Qed.

Lemma lookupv_det : forall ve n v1 v2,
  lookupv ve n v1 -> lookupv ve n v2 -> v1 = v2.
Proof. introv H1. gen v2. induction H1; introv H2; inverts H2; eauto. Qed.

Lemma rl_rec_false : forall l v l' v', ~ rlookupv (rec l v) l' v'.
Proof. introv H. inverts H. Qed.

Lemma rlookupv_det : forall dv l v1 v2,
  rlookupv dv l v1 -> rlookupv dv l v2 -> v1 = v2.
Proof.
  introv H1. gen v2. induction H1; introv H2; inverts H2.
  all: try solve [ auto | congruence | false; eauto using rl_rec_false | eauto ].
  all: exfalso; match goal with
    | H : rlookupv (rec _ _) _ _ |- _ => eapply rl_rec_false; exact H
    end.
Qed.

Lemma step_det : forall ve e e1 e2,
  step ve e e1 -> step ve e e2 -> e1 = e2.
Proof.
  introv H1. gen e2. induction H1; introv H2; inverts H2;
    try solve
      [ f_equal; eauto
      | eauto using lookupv_det, rlookupv_det
      | exfalso; match goal with
          | H : step _ ?t _ |- _ =>
              assert (Hvv: value t) by eauto; eapply (value_irred Hvv); eauto
          end ].
Qed.

(* The value a term reduces to is UNIQUE -- the lemma t_gen consumes. *)
Lemma mstep_val_det : forall g e v1 v2,
  mstep g e v1 -> value v1 -> mstep g e v2 -> value v2 -> v1 = v2.
Proof.
  introv M1. gen v2. induction M1; introv Hv1 M2 Hv2.
  - inverts M2.
    + auto.
    + exfalso. eapply (value_irred Hv1); eauto.
  - inverts M2.
    + exfalso. eapply (value_irred Hv2); eauto.
    + assert (e' = e'0) by (eapply step_det; eauto). subst. eapply IHM1; eauto.
Qed.

(* ====================== the logical relation ======================= *)

Definition cand := exp -> Prop.
Definition senv := nat -> cand.
Definition scons (R:cand) (r:senv) : senv :=
  fun n => match n with 0 => R | S m => r m end.
Definition stail (r:senv) : senv := fun n => r (S n).
Definition sdrop (k:nat) (r:senv) : senv := fun n => r (n + k).
Definition goodr (r:senv) := forall n w, r n w -> value w.

Fixpoint V (r:senv) (A:typ) (v:exp) {struct A} : Prop :=
  match A with
  | int          => exists i, v = lit i
  | tvar n       => r n v
  | arr A1 B     => exists E e, v = clos E e /\ value E /\
                    (forall v2, V r A1 v2 ->
                       exists v', mstep (E ,, v2) e v' /\ value v' /\ V r B v')
  | all B        => forall (R:cand), (forall w, R w -> value w) ->
                       V (scons R r) B v                  (* reducibility candidate *)
  | boxt T0 A1   => exists rE, goodr rE /\ Vp rE T0 /\ V rE A1 v   (* realizer-free *)
  | mani C B     => exists R:cand, (forall w, R w <-> V r C w) /\ V (scons R r) B v
  | rcd l A1     => exists v', v = rec l v' /\ V r A1 v'
  | top          => v = unit
  | and T1 non A1 => exists E w r', v = (E ,, w) /\ goodr r' /\ Vc r' T1 E /\
                      (forall n w0, r' (n + keyLen T1) w0 <-> r n w0) /\ V r' A1 w
  | and T1 rt  A1 => exists r', goodr r' /\ Vc r' T1 v /\
                      (forall n w0, r' (n + keyLen T1) w0 <-> r n w0)
  | ands T1       => exists r', goodr r' /\ Vc r' T1 v /\
                      (forall n w0, r' (n + keyLen T1) w0 <-> r n w0)
  end
with Vc (r:senv) (T:typ) (g:exp) {struct T} : Prop :=
  match T with
  | top          => g = unit
  | and T1 non A1 => exists E w, g = (E ,, w) /\ Vc r T1 E /\ V r A1 w
  | and T1 rt  A1 => Vc (stail r) T1 g /\ (forall w, r 0 w <-> V (stail r) A1 w)
  | ands T1       => Vc (stail r) T1 g
  | _             => False
  end
with Vp (r:senv) (T:typ) {struct T} : Prop :=
  match T with
  | and T1 non A1 => Vp r T1
  | and T1 rt  A1 => Vp (stail r) T1 /\ (forall w, r 0 w <-> V (stail r) A1 w)
  | ands T1       => Vp (stail r) T1
  | _             => True
  end.

Definition sem (T:typ) (e:exp) (A:typ) : Prop :=
  forall r g, goodr r -> Vc r T g -> exists v', mstep g e v' /\ value v' /\ V r A v'.

(* ---------- basic structural facts ---------- *)

Lemma goodr_stail : forall r, goodr r -> goodr (stail r).
Proof. unfold goodr, stail. eauto. Qed.

Lemma goodr_scons : forall R r,
  (forall w, R w -> value w) -> goodr r -> goodr (scons R r).
Proof. unfold goodr, scons. introv HR Hr. destruct n; eauto. Qed.

Lemma stail_scons : forall R r n, stail (scons R r) n = r n.
Proof. intros. unfold stail, scons. destruct n; reflexivity. Qed.

(* every value in the relation is a syntactic value (mutual over V/Vc). *)
Lemma V_value_mut : forall A,
  (forall r v, goodr r -> V r A v -> value v) /\
  (forall r g, goodr r -> Vc r A g -> value g).
Proof.
  induction A as [ | n | A1 IHA1 A2 IHA2 | A1 IHA1 | A1 IHA1 A2 IHA2
                 | A1 IHA1 A2 IHA2 | s A1 IHA1 | | A1 IHA1 m A2 IHA2 | A1 IHA1 ];
    (split; introv Hg HV; simpl in HV).
  - destruct HV as [i Heq]; subst; auto.
  - destruct HV.
  - eauto.
  - destruct HV.
  - destruct HV as (E&e&Heq&HvE&_); subst; auto.
  - destruct HV.
  - assert (Hg0: forall w, (fun _:exp => False) w -> value w) by (intros ? []).
    eapply (proj1 IHA1); [ exact (@goodr_scons (fun _ => False) r Hg0 Hg) | apply HV; exact Hg0 ].
  - destruct HV.
  - destruct HV as (rE & HgE & _ & HA). eapply (proj1 IHA2); [ exact HgE | exact HA ].
  - destruct HV.
  - destruct HV as (R&Hiff&HB).
    eapply (proj1 IHA2); [ apply goodr_scons; [ | exact Hg ] | exact HB ].
    introv HR. apply Hiff in HR. eapply (proj1 IHA1); eauto.
  - destruct HV.
  - destruct HV as (v'&Heq&HA); subst. constructor. eapply (proj1 IHA1); eauto.
  - destruct HV.
  - subst; auto.
  - subst; auto.
  - destruct m.
    + destruct HV as (E&w&r'&Heq&Hgr'&HE&Hcond&Hw); subst.
      constructor; [ eapply (proj2 IHA1); [exact Hgr'|exact HE]
                   | eapply (proj1 IHA2); [exact Hgr'|exact Hw] ].
    + destruct HV as (r'&Hgr'&HE&Hcond).
      eapply (proj2 IHA1); [ exact Hgr' | exact HE ].
  - destruct m.
    + destruct HV as (E&w&Heq&HE&Hw); subst.
      constructor; [ eapply (proj2 IHA1); [exact Hg|exact HE]
                   | eapply (proj1 IHA2); [exact Hg|exact Hw] ].
    + destruct HV as (HE&Hpin).
      eapply (proj2 IHA1); [ apply goodr_stail; exact Hg | exact HE ].
  - destruct HV as (r'&Hgr'&HE&Hcond).
    eapply (proj2 IHA1); [ exact Hgr' | exact HE ].
  - eapply (proj2 IHA1); [ apply goodr_stail; exact Hg | exact HV ].
Qed.

Lemma V_value : forall A r v, goodr r -> V r A v -> value v.
Proof. intro A. exact (proj1 (V_value_mut A)). Qed.

Lemma Vc_value : forall A r g, goodr r -> Vc r A g -> value g.
Proof. intro A. exact (proj2 (V_value_mut A)). Qed.

(* ---- V respects pointwise senv equality (axiom-free; no funext) ---------- *)
Lemma scons_ext : forall R r1 r2,
  (forall n, r1 n = r2 n) -> forall n, scons R r1 n = scons R r2 n.
Proof. introv Heq. destruct n; simpl; auto. Qed.

Lemma stail_ext : forall r1 r2,
  (forall n, r1 n = r2 n) -> forall n, stail r1 n = stail r2 n.
Proof. introv Heq. unfold stail. auto. Qed.

Lemma V_ext_imp_mut : forall A,
  (forall r1 r2 v, (forall n, r1 n = r2 n) -> V r1 A v -> V r2 A v) /\
  (forall r1 r2 g, (forall n, r1 n = r2 n) -> Vc r1 A g -> Vc r2 A g).
Proof.
  induction A as [ | n | A1 IHA1 A2 IHA2 | A1 IHA1 | A1 IHA1 A2 IHA2
                 | A1 IHA1 A2 IHA2 | s A1 IHA1 | | A1 IHA1 m A2 IHA2 | A1 IHA1 ];
    (split; introv Heq HV; simpl in *).
  - assumption.
  - destruct HV.
  - rewrite <- Heq. assumption.
  - destruct HV.
  - destruct HV as (E&e&Hv&HvE&Hf). exists E e. splits; auto. introv HV2.
    apply (proj1 IHA1 r2 r1 v2) in HV2; [ | intro k; symmetry; apply Heq ].
    destruct (Hf _ HV2) as (v'&Hm&Hvv&HA2). exists v'. splits; auto. eapply (proj1 IHA2); eauto.
  - destruct HV.
  - intros R HR. eapply (proj1 IHA1); [ apply scons_ext; exact Heq | ]. apply HV; exact HR.
  - destruct HV.
  - assumption.
  - destruct HV.
  - destruct HV as (R&Hiff&HB). exists R. split.
    + intro w. rewrite Hiff. split; intro Hw.
      * eapply (proj1 IHA1); eauto.
      * apply (proj1 IHA1 r2 r1 w); [ intro k; symmetry; apply Heq | exact Hw ].
    + eapply (proj1 IHA2); [ apply scons_ext; exact Heq | exact HB ].
  - destruct HV.
  - destruct HV as (v'&Hv&HA). exists v'. split; auto. eapply (proj1 IHA1); eauto.
  - destruct HV.
  - assumption.
  - assumption.
  - destruct m.
    + destruct HV as (E&w&r'&Hv&Hgr'&HE&Hcond&Hw). exists E w r'. splits; auto.
      intros n w0. rewrite (Hcond n w0). rewrite (Heq n). tauto.
    + destruct HV as (r'&Hgr'&HE&Hcond). exists r'. splits; auto.
      intros n w0. rewrite (Hcond n w0). rewrite (Heq n). tauto.
  - destruct m.
    + destruct HV as (E&w&Hv&HE&Hw). exists E w. splits; auto.
      * eapply (proj2 IHA1); [ exact Heq | exact HE ].
      * eapply (proj1 IHA2); [ exact Heq | exact Hw ].
    + destruct HV as (HE&Hpin). split.
      * eapply (proj2 IHA1); [ apply stail_ext; exact Heq | exact HE ].
      * intro w. rewrite <- (Heq 0). rewrite Hpin. split; intro Hw.
        ** eapply (proj1 IHA2); [ apply stail_ext; exact Heq | exact Hw ].
        ** apply (proj1 IHA2 (stail r2) (stail r1) w);
             [ apply stail_ext; intro k; symmetry; apply Heq | exact Hw ].
  - destruct HV as (r'&Hgr'&HE&Hcond). exists r'. splits; auto.
    intros n w0. rewrite (Hcond n w0). rewrite (Heq n). tauto.
  - eapply (proj2 IHA1); [ apply stail_ext; exact Heq | exact HV ].
Qed.

Lemma V_ext_imp : forall A r1 r2 v,
  (forall n, r1 n = r2 n) -> V r1 A v -> V r2 A v.
Proof. intro A. exact (proj1 (V_ext_imp_mut A)). Qed.

Lemma Vc_ext_imp : forall A r1 r2 g,
  (forall n, r1 n = r2 n) -> Vc r1 A g -> Vc r2 A g.
Proof. intro A. exact (proj2 (V_ext_imp_mut A)). Qed.

Lemma V_ext : forall A r1 r2 v,
  (forall n, r1 n = r2 n) -> (V r1 A v <-> V r2 A v).
Proof.
  introv Heq. split; intro H.
  - eapply V_ext_imp; [ exact Heq | exact H ].
  - eapply V_ext_imp; [ | exact H ]. intro n; symmetry; apply Heq.
Qed.

(* ---- V respects pointwise IFF of candidates ------------------------------ *)
Lemma scons_ext_iff : forall R r1 r2,
  (forall n w, r1 n w <-> r2 n w) -> forall n w, scons R r1 n w <-> scons R r2 n w.
Proof. introv Heq. destruct n; simpl; [ tauto | apply Heq ]. Qed.

Lemma stail_ext_iff : forall r1 r2,
  (forall n w, r1 n w <-> r2 n w) -> forall n w, stail r1 n w <-> stail r2 n w.
Proof. intros r1 r2 Heq n w. unfold stail. apply Heq. Qed.

Lemma V_ext_iff_imp_mut : forall A,
  (forall r1 r2 v, (forall n w, r1 n w <-> r2 n w) -> V r1 A v -> V r2 A v) /\
  (forall r1 r2 g, (forall n w, r1 n w <-> r2 n w) -> Vc r1 A g -> Vc r2 A g).
Proof.
  induction A as [ | n | A1 IHA1 A2 IHA2 | A1 IHA1 | A1 IHA1 A2 IHA2
                 | A1 IHA1 A2 IHA2 | s A1 IHA1 | | A1 IHA1 m A2 IHA2 | A1 IHA1 ];
    (split; introv Heq HV; simpl in *).
  - assumption.
  - destruct HV.
  - apply (proj1 (Heq n v)); assumption.
  - destruct HV.
  - destruct HV as (E&e&Hv&HvE&Hf). exists E e. splits; auto. introv HV2.
    apply (proj1 IHA1 r2 r1 v2) in HV2; [ | intros k z; symmetry; apply Heq ].
    destruct (Hf _ HV2) as (v'&Hm&Hvv&HA2). exists v'. splits; auto. eapply (proj1 IHA2); eauto.
  - destruct HV.
  - intros R HR. eapply (proj1 IHA1); [ apply scons_ext_iff; exact Heq | ]. apply HV; exact HR.
  - destruct HV.
  - assumption.
  - destruct HV.
  - destruct HV as (R&Hiff&HB). exists R. split.
    + intro w. rewrite Hiff. split; intro Hw.
      * eapply (proj1 IHA1); eauto.
      * apply (proj1 IHA1 r2 r1 w); [ intros k z; symmetry; apply Heq | exact Hw ].
    + eapply (proj1 IHA2); [ apply scons_ext_iff; exact Heq | exact HB ].
  - destruct HV.
  - destruct HV as (v'&Hv&HA). exists v'. split; auto. eapply (proj1 IHA1); eauto.
  - destruct HV.
  - assumption.
  - assumption.
  - destruct m.
    + destruct HV as (E&w&r'&Hv&Hgr'&HE&Hcond&Hw). exists E w r'. splits; auto.
      intros n w0. rewrite (Hcond n w0). exact (Heq n w0).
    + destruct HV as (r'&Hgr'&HE&Hcond). exists r'. splits; auto.
      intros n w0. rewrite (Hcond n w0). exact (Heq n w0).
  - destruct m.
    + destruct HV as (E&w&Hv&HE&Hw). exists E w. splits; auto.
      * eapply (proj2 IHA1); [ exact Heq | exact HE ].
      * eapply (proj1 IHA2); [ exact Heq | exact Hw ].
    + destruct HV as (HE&Hpin). split.
      * eapply (proj2 IHA1); [ apply stail_ext_iff; exact Heq | exact HE ].
      * intro w. rewrite <- (Heq 0 w). rewrite (Hpin w). split; intro Hw.
        ** eapply (proj1 IHA2); [ apply stail_ext_iff; exact Heq | exact Hw ].
        ** apply (proj1 IHA2 (stail r2) (stail r1) w);
             [ apply stail_ext_iff; intros k z; symmetry; apply Heq | exact Hw ].
  - destruct HV as (r'&Hgr'&HE&Hcond). exists r'. splits; auto.
    intros n w0. rewrite (Hcond n w0). exact (Heq n w0).
  - eapply (proj2 IHA1); [ apply stail_ext_iff; exact Heq | exact HV ].
Qed.

Lemma V_ext_iff_imp : forall A r1 r2 v,
  (forall n w, r1 n w <-> r2 n w) -> V r1 A v -> V r2 A v.
Proof. intro A. exact (proj1 (V_ext_iff_imp_mut A)). Qed.

Lemma Vc_ext_iff_imp : forall A r1 r2 g,
  (forall n w, r1 n w <-> r2 n w) -> Vc r1 A g -> Vc r2 A g.
Proof. intro A. exact (proj2 (V_ext_iff_imp_mut A)). Qed.

(* ---- Vp (pin respect) infrastructure ------------------------------------- *)
Lemma Vp_ext_iff_imp : forall T r1 r2,
  (forall n w, r1 n w <-> r2 n w) -> Vp r1 T -> Vp r2 T.
Proof.
  induction T as [ | n | A1 IHA1 A2 IHA2 | A1 IHA1 | A1 IHA1 A2 IHA2
                 | A1 IHA1 A2 IHA2 | s A1 IHA1 | | A1 IHA1 m A2 IHA2 | A1 IHA1 ];
    intros r1 r2 Heq HP; simpl in *; auto.
  - destruct m.
    + exact (IHA1 r1 r2 Heq HP).
    + destruct HP as (HP1 & Hpin). split.
      * exact (IHA1 (stail r1) (stail r2) (stail_ext_iff _ _ Heq) HP1).
      * intro w. rewrite <- (Heq 0 w). rewrite (Hpin w). split; intro Hw.
        -- eapply V_ext_iff_imp; [ apply stail_ext_iff; exact Heq | exact Hw ].
        -- eapply V_ext_iff_imp;
             [ apply stail_ext_iff; intros k z; symmetry; apply Heq | exact Hw ].
  - exact (IHA1 (stail r1) (stail r2) (stail_ext_iff _ _ Heq) HP).
Qed.

Lemma Vp_ext_imp : forall T r1 r2,
  (forall n, r1 n = r2 n) -> Vp r1 T -> Vp r2 T.
Proof.
  intros T r1 r2 Heq. apply Vp_ext_iff_imp. intros n w. rewrite (Heq n). tauto.
Qed.

(* full context realization respects the pins (witness-erasure). *)
Lemma Vc_Vp : forall T r g, Vc r T g -> Vp r T.
Proof.
  induction T as [ | n | A1 IHA1 A2 IHA2 | A1 IHA1 | A1 IHA1 A2 IHA2
                 | A1 IHA1 A2 IHA2 | s A1 IHA1 | | A1 IHA1 m A2 IHA2 | A1 IHA1 ];
    intros r g HV; simpl in *; auto.
  - destruct m.
    + destruct HV as (E & w & _ & HE & _). exact (IHA1 r E HE).
    + destruct HV as (HE & Hpin).
      split; [ exact (IHA1 (stail r) g HE) | exact Hpin ].
  - exact (IHA1 (stail r) g HV).
Qed.

(* canonical pin environment. *)
Fixpoint penv (T:typ) : senv :=
  match T with
  | and T1 non A1 => penv T1
  | and T1 rt  A1 => scons (fun w => V (penv T1) A1 w) (penv T1)
  | ands T1       => scons (fun _ => False) (penv T1)
  | _             => fun _ _ => False
  end.

Lemma goodr_penv : forall T, goodr (penv T).
Proof.
  induction T as [ | n | A1 IHA1 A2 IHA2 | A1 IHA1 | A1 IHA1 A2 IHA2
                 | A1 IHA1 A2 IHA2 | s A1 IHA1 | | A1 IHA1 m A2 IHA2 | A1 IHA1 ];
    simpl; try (intros n0 w Hf; destruct Hf).
  - destruct m.
    + exact IHA1.
    + apply goodr_scons; [ | exact IHA1 ].
      intros w Hw. eapply V_value; [ exact IHA1 | exact Hw ].
  - apply goodr_scons; [ intros w Hf; destruct Hf | exact IHA1 ].
Qed.

Lemma Vp_penv : forall T, Vp (penv T) T.
Proof.
  induction T as [ | n | A1 IHA1 A2 IHA2 | A1 IHA1 | A1 IHA1 A2 IHA2
                 | A1 IHA1 A2 IHA2 | s A1 IHA1 | | A1 IHA1 m A2 IHA2 | A1 IHA1 ];
    simpl; auto.
  - destruct m.
    + exact IHA1.
    + split.
      * eapply Vp_ext_imp; [ | exact IHA1 ]. intro k; reflexivity.
      * intro w. simpl. apply V_ext. intro k; reflexivity.
Qed.

(* ---- weakening: inserting an unused candidate at depth d cancels tshift d -- *)
Definition sins (d:nat) (R:cand) (r:senv) : senv :=
  fun n => match lt_eq_lt_dec n d with
           | inleft (left _)  => r n        (* n < d *)
           | inleft (right _) => R          (* n = d *)
           | inright _        => r (pred n) (* n > d *)
           end.

Lemma sins_scons_eq : forall d R R' r n,
  scons R' (sins d R r) n = sins (S d) R (scons R' r) n.
Proof.
  intros. destruct n; unfold sins, scons; simpl;
    repeat match goal with
           | [ |- context[lt_eq_lt_dec ?a ?b] ] => destruct (lt_eq_lt_dec a b) as [[?|?]|?]
           end; try lia; auto.
  destruct n; simpl; auto; lia.
Qed.

Lemma goodr_sins : forall d R r,
  (forall w, R w -> value w) -> goodr r -> goodr (sins d R r).
Proof.
  introv HR Hg. intros n w Hw. unfold sins in Hw.
  destruct (lt_eq_lt_dec n d) as [[?|?]|?]; eauto.
Qed.

Definition sdel (k:nat) (r:senv) : senv :=
  fun m => if lt_dec m k then r m else r (S m).

Lemma goodr_sdel : forall k r, goodr r -> goodr (sdel k r).
Proof.
  introv Hg. intros n w Hw. unfold sdel in Hw. destruct (lt_dec n k); eauto.
Qed.

Lemma stail_sins : forall d R r n, stail (sins (S d) R r) n = sins d R (stail r) n.
Proof.
  intros. unfold stail, sins.
  destruct (lt_eq_lt_dec (S n) (S d)) as [[?|?]|?];
    destruct (lt_eq_lt_dec n d) as [[?|?]|?]; try lia; auto.
  destruct n; [ lia | simpl; auto ].
Qed.

Lemma sins_cond : forall k d R r r',
  (forall n w0, r' (n + k) w0 <-> r n w0) ->
  forall n w0, sins (k + d) R r' (n + k) w0 <-> sins d R r n w0.
Proof.
  introv Hcond. intros n w0. unfold sins.
  destruct (lt_eq_lt_dec (n + k) (k + d)) as [[?|?]|?];
    destruct (lt_eq_lt_dec n d) as [[?|?]|?]; try lia.
  - apply Hcond.
  - tauto.
  - replace (pred (n + k)) with (pred n + k) by lia. apply Hcond.
Qed.

Lemma unins_cond : forall k d R r r'',
  (forall n w0, r'' (n + k) w0 <-> sins d R r n w0) ->
  forall n w0, sdel (k + d) r'' (n + k) w0 <-> r n w0.
Proof.
  introv Hcond. intros n w0. unfold sdel.
  destruct (lt_dec (n + k) (k + d)).
  - rewrite (Hcond n w0). unfold sins.
    destruct (lt_eq_lt_dec n d) as [[?|?]|?]; try lia. tauto.
  - replace (S (n + k)) with (S n + k) by lia.
    rewrite (Hcond (S n) w0). unfold sins.
    destruct (lt_eq_lt_dec (S n) d) as [[?|?]|?]; try lia. simpl. tauto.
Qed.

Lemma unins_iff : forall k d R r r'',
  (forall n w0, r'' (n + k) w0 <-> sins d R r n w0) ->
  forall p w0, r'' p w0 <-> sins (k + d) R (sdel (k + d) r'') p w0.
Proof.
  introv Hcond. intros p w0. unfold sins, sdel.
  destruct (lt_eq_lt_dec p (k + d)) as [[Hlt|Heq]|Hgt].
  - destruct (lt_dec p (k + d)); [ tauto | lia ].
  - subst p. replace (k + d) with (d + k) by lia. rewrite (Hcond d w0).
    unfold sins. destruct (lt_eq_lt_dec d d) as [[?|?]|?]; try lia. tauto.
  - destruct (lt_dec (pred p) (k + d)); [ lia | ].
    replace (S (pred p)) with p by lia. tauto.
Qed.

(* ==================== THE WEAKENING LEMMA (mutual) ==================== *)
Lemma V_tshift_mut : forall A,
  (forall d r R v, (forall w, R w -> value w) ->
     (V (sins d R r) (tshift d A) v <-> V r A v)) /\
  (forall d r R g, (forall w, R w -> value w) ->
     (Vc (sins (keyLen A + d) R r) (tshift d A) g <-> Vc r A g)).
Proof.
  induction A as [ | n | A1 IHA1 A2 IHA2 | A1 IHA1 | A1 IHA1 A2 IHA2
                 | A1 IHA1 A2 IHA2 | s A1 IHA1 | | A1 IHA1 m A2 IHA2 | A1 IHA1 ].
  all: swap 1 9. all: swap 2 10.
  (* ---- and T1 m A2 (the env-type case; the heart of the lemma) ---- *)
  destruct IHA1 as (IH1V & IH1C). destruct IHA2 as (IH2V & IH2C).
  split.
  - intros d r R v HRval. destruct m; simpl.
    + assert (Hk : keyLen (tshift d A1) = keyLen A1) by (symmetry; apply keyLen_same).
      rewrite Hk. split.
      * intros (E & w & r'' & Heqv & Hg'' & HE & Hcond & HA).
        exists E, w, (sdel (keyLen A1 + d) r''). splits;
        [ exact Heqv
        | apply goodr_sdel; exact Hg''
        | apply (proj1 (IH1C d (sdel (keyLen A1 + d) r'') R E HRval));
          eapply Vc_ext_iff_imp; [ intros p w0; exact (unins_iff _ _ _ _ _ Hcond p w0) | exact HE ]
        | intros n w0; exact (unins_cond _ _ _ _ _ Hcond n w0)
        | apply (proj1 (IH2V (keyLen A1 + d) (sdel (keyLen A1 + d) r'') R w HRval));
          eapply V_ext_iff_imp; [ intros p w0; exact (unins_iff _ _ _ _ _ Hcond p w0) | exact HA ] ].
      * intros (E & w & r' & Heqv & Hg' & HE & Hcond & HA).
        exists E, w, (sins (keyLen A1 + d) R r'). splits;
        [ exact Heqv
        | apply goodr_sins; assumption
        | exact (proj2 (IH1C d r' R E HRval) HE)
        | intros n w0; exact (sins_cond _ _ _ _ _ Hcond n w0)
        | exact (proj2 (IH2V (keyLen A1 + d) r' R w HRval) HA) ].
    + assert (Hk : keyLen (tshift d A1) = keyLen A1) by (symmetry; apply keyLen_same).
      rewrite Hk. split.
      * intros (r'' & Hg'' & HE & Hcond).
        exists (sdel (keyLen A1 + d) r''). splits;
        [ apply goodr_sdel; exact Hg''
        | apply (proj1 (IH1C d (sdel (keyLen A1 + d) r'') R v HRval));
          eapply Vc_ext_iff_imp; [ intros p w0; exact (unins_iff _ _ _ _ _ Hcond p w0) | exact HE ]
        | intros n w0; exact (unins_cond _ _ _ _ _ Hcond n w0) ].
      * intros (r' & Hg' & HE & Hcond).
        exists (sins (keyLen A1 + d) R r'). splits;
        [ apply goodr_sins; assumption
        | exact (proj2 (IH1C d r' R v HRval) HE)
        | intros n w0; exact (sins_cond _ _ _ _ _ Hcond n w0) ].
  - intros d r R g HRval. destruct m; simpl.
    + split.
      * intros (E & w & Heq & HE & HA). exists E, w. splits;
        [ exact Heq
        | exact (proj1 (IH1C d r R E HRval) HE)
        | exact (proj1 (IH2V (keyLen A1 + d) r R w HRval) HA) ].
      * intros (E & w & Heq & HE & HA). exists E, w. splits;
        [ exact Heq
        | exact (proj2 (IH1C d r R E HRval) HE)
        | exact (proj2 (IH2V (keyLen A1 + d) r R w HRval) HA) ].
    + split.
      * intros (HE & Hpin).
        split;
        [ apply (proj1 (IH1C d (stail r) R g HRval));
          eapply Vc_ext_imp; [ intro k; apply stail_sins | exact HE ]
        | ].
        intros w.
        assert (H0 : sins (S (keyLen A1 + d)) R r 0 w <-> r 0 w)
          by (unfold sins; destruct (lt_eq_lt_dec 0 (S (keyLen A1 + d))) as [[?|?]|?]; try lia; tauto).
        rewrite <- H0. rewrite (Hpin w). split; intro HX;
        [ apply (proj1 (IH2V (keyLen A1 + d) (stail r) R w HRval));
          eapply V_ext_imp; [ intro k; apply stail_sins | exact HX ]
        | eapply V_ext_imp; [ intro k; symmetry; apply stail_sins | ];
          apply (proj2 (IH2V (keyLen A1 + d) (stail r) R w HRval)); exact HX ].
      * intros (HE & Hpin).
        split;
        [ eapply Vc_ext_imp; [ intro k; symmetry; apply stail_sins | ];
          apply (proj2 (IH1C d (stail r) R g HRval)); exact HE
        | ].
        intros w.
        assert (H0 : sins (S (keyLen A1 + d)) R r 0 w <-> r 0 w)
          by (unfold sins; destruct (lt_eq_lt_dec 0 (S (keyLen A1 + d))) as [[?|?]|?]; try lia; tauto).
        rewrite H0. rewrite (Hpin w). split; intro HX;
        [ eapply V_ext_imp; [ intro k; symmetry; apply stail_sins | ];
          apply (proj2 (IH2V (keyLen A1 + d) (stail r) R w HRval)); exact HX
        | apply (proj1 (IH2V (keyLen A1 + d) (stail r) R w HRval));
          eapply V_ext_imp; [ intro k; apply stail_sins | exact HX ] ].
  (* ---- ands T1 (&s) ---- *)
  - destruct IHA1 as (IH1V & IH1C).
    split.
    + intros d r R v HRval. simpl.
      assert (Hk : keyLen (tshift d A1) = keyLen A1) by (symmetry; apply keyLen_same).
      rewrite Hk. split.
      * intros (r'' & Hg'' & HE & Hcond).
        exists (sdel (keyLen A1 + d) r''). splits;
        [ apply goodr_sdel; exact Hg''
        | apply (proj1 (IH1C d (sdel (keyLen A1 + d) r'') R v HRval));
          eapply Vc_ext_iff_imp; [ intros p w0; exact (unins_iff _ _ _ _ _ Hcond p w0) | exact HE ]
        | intros n w0; exact (unins_cond _ _ _ _ _ Hcond n w0) ].
      * intros (r' & Hg' & HE & Hcond).
        exists (sins (keyLen A1 + d) R r'). splits;
        [ apply goodr_sins; assumption
        | exact (proj2 (IH1C d r' R v HRval) HE)
        | intros n w0; exact (sins_cond _ _ _ _ _ Hcond n w0) ].
    + intros d r R g HRval. simpl. split.
      * intros HE. apply (proj1 (IH1C d (stail r) R g HRval));
          eapply Vc_ext_imp; [ intro k; apply stail_sins | exact HE ].
      * intros HE. eapply Vc_ext_imp; [ intro k; symmetry; apply stail_sins | ];
          apply (proj2 (IH1C d (stail r) R g HRval)); exact HE.
  (* ---- non-env constructors: Vc coincides with V and keyLen = 0 ---- *)
  - assert (HV : forall d r R v, (forall w : exp, R w -> value w) ->
        (V (sins d R r) (tshift d (arr A1 A2)) v <-> V r (arr A1 A2) v)).
    + intros d r R v HRval. simpl. split.
      * intros (E&e&Hv&HvE&Hf). exists E e. splits; auto. introv HV2.
        apply (proj2 (proj1 IHA1 d r R v2 HRval)) in HV2.
        destruct (Hf _ HV2) as (v'&Hm&Hvv&HA). exists v'. splits; auto.
        apply (proj1 (proj1 IHA2 d r R v' HRval)); exact HA.
      * intros (E&e&Hv&HvE&Hf). exists E e. splits; auto. introv HV2.
        apply (proj1 (proj1 IHA1 d r R v2 HRval)) in HV2.
        destruct (Hf _ HV2) as (v'&Hm&Hvv&HA). exists v'. splits; auto.
        apply (proj2 (proj1 IHA2 d r R v' HRval)); exact HA.
    + split; [ exact HV | intros d r R g HRval; simpl; tauto ].
  - assert (HV : forall d r R v, (forall w : exp, R w -> value w) ->
        (V (sins d R r) (tshift d (all A1)) v <-> V r (all A1) v)).
    + intros d r R v HRval. simpl. split.
      * intros Hf R0 HR0val.
        apply (proj1 (proj1 IHA1 (S d) (scons R0 r) R v HRval)).
        eapply V_ext_imp; [ apply sins_scons_eq | apply Hf; exact HR0val ].
      * intros Hf R0 HR0val.
        eapply V_ext_imp; [ intro n; symmetry; apply sins_scons_eq | ].
        apply (proj2 (proj1 IHA1 (S d) (scons R0 r) R v HRval)). apply Hf; exact HR0val.
    + split; [ exact HV | intros d r R g HRval; simpl; tauto ].
  - split; intros d r R v HRval; simpl; reflexivity.
  - assert (HV : forall d r R v, (forall w : exp, R w -> value w) ->
        (V (sins d R r) (tshift d (mani A1 A2)) v <-> V r (mani A1 A2) v)).
    + intros d r R v HRval. simpl. split.
      * intros (R0&Hiff&HB). exists R0. split.
        ** intro w. rewrite Hiff. exact (proj1 IHA1 d r R w HRval).
        ** apply (proj1 (proj1 IHA2 (S d) (scons R0 r) R v HRval)).
           eapply V_ext_imp; [ apply sins_scons_eq | exact HB ].
      * intros (R0&Hiff&HB). exists R0. split.
        ** intro w. rewrite Hiff. symmetry. exact (proj1 IHA1 d r R w HRval).
        ** eapply V_ext_imp; [ intro n; symmetry; apply sins_scons_eq | ].
           apply (proj2 (proj1 IHA2 (S d) (scons R0 r) R v HRval)); exact HB.
    + split; [ exact HV | intros d r R g HRval; simpl; tauto ].
  - assert (HV : forall d r R v, (forall w : exp, R w -> value w) ->
        (V (sins d R r) (tshift d (rcd s A1)) v <-> V r (rcd s A1) v)).
    + intros d r R v HRval. simpl. split.
      * intros (w&Hv&HA); subst. exists w. split; auto.
        apply (proj1 (proj1 IHA1 d r R w HRval)); exact HA.
      * intros (w&Hv&HA); subst. exists w. split; auto.
        apply (proj2 (proj1 IHA1 d r R w HRval)); exact HA.
    + split; [ exact HV | intros d r R g HRval; simpl; tauto ].
  - split; intros d r R v HRval; simpl; reflexivity.
  - split; intros d r R v HRval; simpl; reflexivity.
  - assert (HV : forall d r R v, (forall w : exp, R w -> value w) ->
        (V (sins d R r) (tshift d (tvar n)) v <-> V r (tvar n) v)).
    + intros d r R v HRval. simpl. unfold sins. destruct (le_gt_dec d n).
      * destruct (lt_eq_lt_dec (S n) d) as [[?|?]|?]; try lia. simpl. reflexivity.
      * destruct (lt_eq_lt_dec n d) as [[?|?]|?]; try lia; reflexivity.
    + split; [ exact HV | intros d r R g HRval; simpl; tauto ].
Qed.

Lemma V_tshift : forall A d r R v, (forall w, R w -> value w) ->
  (V (sins d R r) (tshift d A) v <-> V r A v).
Proof. intro A. exact (proj1 (V_tshift_mut A)). Qed.

(* d=0 instance of weakening: crossing one type binding. *)
Lemma V_tshift0 : forall A r v, goodr r -> (V r (tshift 0 A) v <-> V (stail r) A v).
Proof.
  introv Hg.
  rewrite <- (V_tshift A 0 (stail r) (r 0) v (fun w Hw => Hg 0 w Hw)).
  apply V_ext. intro n. unfold sins.
  destruct (lt_eq_lt_dec n 0) as [[H|H]|H]; try lia.
  - subst; auto.
  - destruct n; [ lia | ]. unfold stail; simpl. auto.
Qed.

(* A type-level realization induces a context realization under a combined env. *)
Lemma V_to_Vc : forall T r v, lshape T -> goodr r -> V r T v ->
  exists r', goodr r' /\ (forall n w, r' (n + keyLen T) w <-> r n w) /\ Vc r' T v.
Proof.
  intros T r v Hlsh Hg HV.
  destruct T as [ | n | T1 T2 | T1 | T1 T2 | T1 T2 | s T1 | | T1 m T2 | T1 ];
    try (inverts Hlsh).
  - (* top *) exists r; splits;
      [ exact Hg
      | intros n0 w; simpl; replace (n0 + 0) with n0 by lia; tauto
      | exact HV ].
  - (* and T1 m T2 *) destruct m; simpl in HV.
    + destruct HV as (E & w & r' & Heq & Hgr' & HE & Hcond & Hw). subst.
      exists r'. splits; [ exact Hgr' | exact Hcond | ].
      simpl. exists E, w. splits; auto.
    + destruct HV as (r' & Hgr' & HE & Hcond).
      exists (scons (fun w => V r' T2 w) r'). splits.
      * apply goodr_scons; [ introv Hw; eapply V_value; eauto | exact Hgr' ].
      * intros n w. simpl. replace (n + S (keyLen T1)) with (S (n + keyLen T1)) by lia.
        simpl. exact (Hcond n w).
      * simpl. split.
        -- eapply Vc_ext_imp; [ intro k; reflexivity | exact HE ].
        -- intro w. simpl. split; intro Hw.
           ++ eapply V_ext_imp; [ intro k; reflexivity | exact Hw ].
           ++ eapply V_ext_imp; [ intro k; reflexivity | exact Hw ].
  - (* ands T1 *) simpl in HV.
    destruct HV as (r' & Hgr' & HE & Hcond).
    exists (scons (fun _ => False) r'). splits.
    + apply goodr_scons; [ intros w Hw; destruct Hw | exact Hgr' ].
    + intros n w. simpl. replace (n + S (keyLen T1)) with (S (n + keyLen T1)) by lia.
      simpl. exact (Hcond n w).
    + simpl. eapply Vc_ext_imp; [ intro k; reflexivity | exact HE ].
Qed.

(* =================== mstep congruences =================== *)

Lemma mstep_trans : forall ve e1 e2 e3,
  mstep ve e1 e2 -> mstep ve e2 e3 -> mstep ve e1 e3.
Proof.
  introv H1. induction H1; introv H2; auto.
  eapply mstep_step; [ exact H | ]. apply IHmstep; exact H2.
Qed.

Lemma mstep_appl : forall ve e1 e1' e2,
  value ve -> mstep ve e1 e1' -> mstep ve (app e1 e2) (app e1' e2).
Proof.
  introv Hv H. induction H. apply mstep_base; auto.
  eapply mstep_step; [ apply sappl; eauto | eauto ].
Qed.

Lemma mstep_appr : forall ve v1 e2 e2',
  value ve -> value v1 -> mstep ve e2 e2' -> mstep ve (app v1 e2) (app v1 e2').
Proof.
  introv Hv Hv1 H. induction H. apply mstep_base; auto.
  eapply mstep_step; [ apply sappr; eauto | eauto ].
Qed.

Lemma mstep_boxl : forall ve e1 e1' e2,
  value ve -> mstep ve e1 e1' -> mstep ve (box e1 e2) (box e1' e2).
Proof.
  introv Hv H. induction H. apply mstep_base; auto.
  eapply mstep_step; [ apply sboxl; eauto | eauto ].
Qed.

Lemma mstep_boxbody : forall ve v1 e2 e2',
  value ve -> value v1 -> mstep v1 e2 e2' -> mstep ve (box v1 e2) (box v1 e2').
Proof.
  introv Hv Hv1 H. induction H. apply mstep_base; auto.
  eapply mstep_step; [ apply sbox; eauto | eauto ].
Qed.

Lemma mstep_rec : forall ve l e e',
  value ve -> mstep ve e e' -> mstep ve (rec l e) (rec l e').
Proof.
  introv Hv H. induction H. apply mstep_base; auto.
  eapply mstep_step; [ apply s_rec; eauto | eauto ].
Qed.

Lemma mstep_proj : forall ve l e e',
  value ve -> mstep ve e e' -> mstep ve (rproj e l) (rproj e' l).
Proof.
  introv Hv H. induction H. apply mstep_base; auto.
  eapply mstep_step; [ apply s_proj; eauto | eauto ].
Qed.

Lemma mstep_mrgl : forall g E E' e, value g -> mstep g E E' -> mstep g (E ,, e) (E' ,, e).
Proof. introv Hv H. induction H; auto. eapply mstep_step; [ apply ls_mrgl; eauto | eauto ]. Qed.

Lemma mstep_mrgr : forall g E e e', value g -> value E -> mstep (g ++- E) e e' -> mstep g (E ,, e) (E ,, e').
Proof.
  introv Hv HE H. remember (g ++- E) as ge eqn:Hge. induction H; subst.
  - apply mstep_base. auto.
  - eapply mstep_step; [ apply ls_mrgr; [ exact Hv | exact HE | exact H ] | ]. apply IHmstep; auto.
Qed.

(* ===================== compatibility lemmas ===================== *)

Lemma comp_int : forall T i, sem T (lit i) int.
Proof.
  unfold sem. introv Hg HV. exists (lit i). splits.
  - apply mstep_base. eapply Vc_value; eauto.
  - auto.
  - simpl. eauto.
Qed.

Lemma comp_unit : forall T, sem T unit top.
Proof.
  unfold sem. introv Hg HV. exists unit. splits.
  - apply mstep_base. eapply Vc_value; eauto.
  - auto.
  - simpl. auto.
Qed.

(* context lookup respects Vc *)
Lemma var_lookup : forall T n A, get_var T n A ->
  forall r g, goodr r -> Vc r T g -> exists v', lookupv g n v' /\ V r A v'.
Proof.
  induction 1; introv Hg HV; simpl in HV.
  - edestruct (IHget_var (stail r) g) as (v'&Hl&HA);
      [ apply goodr_stail; auto | exact HV | ].
    exists v'. split; [ exact Hl | apply (proj2 (V_tshift0 A v' Hg)); exact HA ].
  - destruct HV as (HE & _).
    edestruct (IHget_var (stail r) g) as (v'&Hl&HA);
      [ apply goodr_stail; auto | exact HE | ].
    exists v'. split; [ exact Hl | apply (proj2 (V_tshift0 A v' Hg)); exact HA ].
  - destruct HV as (E&w&Heqg&HE&Hw); subst.
    exists w. split; [ apply lvzero | exact Hw ].
  - destruct HV as (E&w&Heqg&HE&Hw); subst.
    edestruct (IHget_var r E) as (v'&Hl&HA); [ auto | exact HE | ].
    exists v'. split; [ apply lvsuccv; exact Hl | exact HA ].
Qed.

Lemma comp_var : forall T n A, get_var T n A -> sem T (var n) A.
Proof.
  introv Hgv. unfold sem. introv Hg HV.
  assert (value g) as Hvg by (eapply Vc_value; eauto).
  assert (exists v', lookupv g n v' /\ V r A v') as (v'&Hl&HA)
    by (eapply var_lookup; eauto).
  exists v'. splits.
  - eapply mstep_step; [ apply svar | apply mstep_base ]; eauto.
  - eapply V_value; eauto.
  - exact HA.
Qed.

Lemma comp_lam : forall T A e B, sem (T & A) e B -> sem T (lam e) (arr A B).
Proof.
  unfold sem. introv Hs Hg HV.
  assert (value g) as Hvg by (eapply Vc_value; eauto).
  exists (clos g e). splits.
  - eapply mstep_step; [ apply sclos; auto | apply mstep_base; auto ].
  - auto.
  - simpl. exists g e. splits; auto. introv HVA.
    apply Hs; auto. simpl. exists g v2. splits; auto.
Qed.

Lemma comp_app : forall T A B e1 e2,
  sem T e1 (arr A B) -> sem T e2 A -> sem T (app e1 e2) B.
Proof.
  unfold sem. introv Hs1 Hs2 Hg HV.
  assert (value g) as Hvg by (eapply Vc_value; eauto).
  destruct (Hs1 r g Hg HV) as (v1 & Hm1 & Hvv1 & HVf).
  destruct (Hs2 r g Hg HV) as (v2 & Hm2 & Hvv2 & HVa).
  simpl in HVf. destruct HVf as (E&e&Heq&HvE&Hf). subst v1.
  destruct (Hf v2 HVa) as (v' & Hmb & Hvv' & HVb).
  assert (value (E ,, v2)) as Hvev by (constructor; auto).
  exists v'. splits; auto.
  eapply mstep_trans; [ apply mstep_appl; eauto | ].
  eapply mstep_trans; [ apply mstep_appr; eauto | ].
  eapply mstep_step; [ apply sbeta; eauto | ].
  eapply mstep_trans; [ apply mstep_boxbody; eauto | ].
  eapply mstep_step; [ apply sboxv; eauto | apply mstep_base; auto ].
Qed.

Lemma comp_rec : forall T l e A, sem T e A -> sem T (rec l e) (rcd l A).
Proof.
  unfold sem. introv Hs Hg HV.
  destruct (Hs r g Hg HV) as (v & Hm & Hvv & HVA).
  assert (value g) as Hvg by (eapply Vc_value; eauto).
  exists (rec l v). splits.
  - apply mstep_rec; auto.
  - auto.
  - simpl. exists v. splits; auto.
Qed.

(* phantom &s : realizing T under r  <->  realizing (T &s) under (R::r) -- via Vc *)
Lemma Vc_ands_scons : forall T r R g,
  Vc (scons R r) (ands T) g <-> Vc r T g.
Proof.
  intros. simpl. split; intro H.
  - eapply Vc_ext_imp; [ | exact H ]. intro n. apply stail_scons.
  - eapply Vc_ext_imp; [ | exact H ]. intro n. symmetry; apply stail_scons.
Qed.

(* ---- t_gen ---- *)
Lemma comp_gen : forall T e A, sem (T &s) e A -> sem T e (all A).
Proof.
  unfold sem. introv IH Hr Hg.
  assert (Hg0 : forall w : exp, (fun _ : exp => False) w -> value w)
    by (intros w Hf; destruct Hf).
  destruct (IH (scons (fun _ => False) r) g (@goodr_scons (fun _ => False) r Hg0 Hr)
              (proj2 (Vc_ands_scons T r (fun _ => False) g) Hg))
    as (v0 & Hm0 & Hv0 & _).
  exists v0. splits; auto.
  simpl. intros R HvalR.
  destruct (IH (scons R r) g (@goodr_scons R r HvalR Hr)
              (proj2 (Vc_ands_scons T r R g) Hg))
    as (vR & HmR & HvR & HVR).
  assert (vR = v0) by (eapply mstep_val_det; eauto). subst vR. exact HVR.
Qed.

(* ---- t_tapp ---- *)
Lemma comp_tapp : forall T e A B, sem T e (all B) -> sem T e (mani A B).
Proof.
  unfold sem. introv Hs Hr Hg.
  destruct (Hs r g Hr Hg) as (vf & Hmf & Hvf & HVall).
  exists vf. splits; auto.
  simpl. exists (V r A). split.
  - intro w; tauto.
  - simpl in HVall. apply HVall. intros w Hw. eapply V_value; eauto.
Qed.

(* a closed value typed at top:T1 realizes V[[T1]] under every good env *)
Lemma sem_top_value : forall E1 T1 r,
  sem top E1 T1 -> value E1 -> goodr r -> V r T1 E1.
Proof.
  introv Hs HvE1 Hg.
  destruct (Hs r unit Hg eq_refl) as (v' & Hm & Hvv & HV).
  assert (v' = E1) as ->.
  { inverts Hm; auto. exfalso. eapply (value_irred HvE1); eauto. }
  exact HV.
Qed.

Lemma comp_box : forall T e1 T1 A e2,
  sem T e1 T1 -> sem T1 e2 A -> lshape T1 -> sem T (box e1 e2) (boxt T1 A).
Proof.
  unfold sem. introv Hs1 Hs2 Hl Hg HV.
  assert (value g) as Hvg by (eapply Vc_value; eauto).
  destruct (Hs1 r g Hg HV) as (v1 & Hm1 & Hvv1 & HVT1).
  destruct (@V_to_Vc T1 r v1 Hl Hg HVT1) as (r' & Hgr' & Hcond & HVc1).
  destruct (Hs2 r' v1 Hgr' HVc1) as (v' & Hm2 & Hvv' & HVA).
  exists v'. splits.
  - eapply mstep_trans; [ apply mstep_boxl; eauto | ].
    eapply mstep_trans; [ apply mstep_boxbody; eauto | ].
    eapply mstep_step; [ apply sboxv; eauto | apply mstep_base; auto ].
  - auto.
  - simpl. exists r'. splits; [ exact Hgr' | exact (Vc_Vp _ _ _ HVc1) | exact HVA ].
Qed.

Lemma comp_clos : forall T E1 T1 A B e2,
  sem top E1 T1 -> sem (T1 & A) e2 B -> value E1 -> lshape T1 ->
  sem T (clos E1 e2) (boxt T1 (arr A B)).
Proof.
  unfold sem. introv Hs1 Hs2 HvE1 Hl Hg HV.
  assert (V r T1 E1) as HVT1 by (eapply sem_top_value; eauto).
  destruct (@V_to_Vc T1 r E1 Hl Hg HVT1) as (r' & Hgr' & Hcond & HVc1).
  exists (clos E1 e2). splits.
  - apply mstep_base. exact (@Vc_value T r g Hg HV).
  - auto.
  - simpl. exists r'. splits; [ exact Hgr' | exact (Vc_Vp _ _ _ HVc1) | ].
    simpl. exists E1 e2. splits; auto. introv HVA.
    apply Hs2; auto. simpl. exists E1 v2. splits; auto.
Qed.

(* ===================== teq compatibility ===================== *)

(* manifest pinning: a lookt-resolvable var X is interpreted exactly as its def B. *)
(* manifest pinning needs only PIN respect (Vp). *)
Lemma Vp_lookt_pin : forall T X B, lookt T X B ->
  forall r, goodr r -> Vp r T -> forall w, r X w <-> V r B w.
Proof.
  intros T X B Hl. induction Hl; intros r Hg HP w; simpl in HP.
  - exact (IHHl r Hg HP w).
  - destruct HP as (HP1 & Hpin). rewrite (Hpin w). symmetry. apply V_tshift0; exact Hg.
  - destruct HP as (HP1 & Hpin).
    specialize (IHHl (stail r) (goodr_stail Hg) HP1 w). unfold stail in IHHl. rewrite IHHl.
    symmetry. apply V_tshift0; exact Hg.
  - specialize (IHHl (stail r) (goodr_stail Hg) HP w). unfold stail in IHHl. rewrite IHHl.
    symmetry. apply V_tshift0; exact Hg.
Qed.

(* pin respect over +++ : T3 low, T1 high (shifted by keyLen T3). *)
Lemma Vp_concat : forall T3, lshape T3 -> forall r T1,
  Vp (sdrop (keyLen T3) r) T1 -> Vp r T3 -> Vp r (T1 +++ T3).
Proof.
  induction 1; intros r T1 HP1 HP3.
  - simpl. eapply Vp_ext_imp; [ | exact HP1 ].
    intro n. unfold sdrop. f_equal. simpl. lia.
  - assert (Hmc: (T1 +++ (and T m A)) = (and (T1 +++ T) m A)) by (destruct T; reflexivity).
    rewrite Hmc. destruct m; simpl in HP3 |- *.
    + exact (IHlshape r T1 HP1 HP3).
    + destruct HP3 as (HP3' & Hpin). split; [ | exact Hpin ].
      apply (IHlshape (stail r) T1); [ | exact HP3' ].
      eapply Vp_ext_imp; [ | exact HP1 ]. intro n. unfold sdrop, stail. f_equal. simpl. lia.
  - assert (Hmc: (T1 +++ (T &s)) = ((T1 +++ T) &s)) by (destruct T; reflexivity).
    rewrite Hmc. simpl in HP3 |- *.
    apply (IHlshape (stail r) T1); [ | exact HP3 ].
    eapply Vp_ext_imp; [ | exact HP1 ]. intro n. unfold sdrop, stail. f_equal. simpl. lia.
Qed.

(* type vars X interpreted at the SAME positional index in T1 and T2 agree. *)
Definition Ralign (r1 r2 : senv) (T1 T2 : typ) : Prop :=
  forall X, check T1 X -> check T2 X -> forall w, r1 X w <-> r2 X w.

(* teqd is symmetric (the _l/_r constructors mirror; the rest self-symmetric). *)
Lemma teqd_sym : forall n T1 A B T2, teqd n T1 A B T2 -> teqd n T2 B A T1.
Proof.
  intros n T1 A B T2 H. induction H;
    eauto using dq_int, dq_tvar, dq_eql, dq_eqr, dq_boxl, dq_boxr, dq_arr,
                dq_all, dq_manil, dq_manir, dq_top, dq_and, dq_ands, dq_rcd.
Qed.

Lemma teqd_rigid_l : forall n T1 A B T2, teqd n T1 A B T2 -> rigid 0 T2 B -> rigid 0 T1 A.
Proof. intros n T1 A B T2 H Hr. exact (teqd_rigid_r (teqd_sym H) Hr). Qed.

(* === RIGID teq-compatibility (realizer-free) ===
   The box rules now condition on `wft .. (boxt T3 A)`, i.e. a RIGID box body.
   For rigid types the value relation reads only manifest pins (Vp) and BOUND
   vars (< d, vacuous at d=0); the box body never consults the ambient alignment
   beyond its bound.  So a depth-BOUNDED alignment suffices, and the box cases
   reset the bound to 0 (extract: IH at the box's pin env; provide: canonical
   penv).   *)
Lemma comp_eq_rigid_combined : forall n T1 A B T2, teqd n T1 A B T2 ->
  (forall d1 d2, rigid d1 T1 A -> rigid d2 T2 B ->
   forall r1 r2, goodr r1 -> goodr r2 -> Vp r1 T1 -> Vp r2 T2 ->
   (forall X, check T1 X -> check T2 X -> X < d1 -> X < d2 -> forall w, r1 X w <-> r2 X w) ->
   forall v, V r1 A v <-> V r2 B v)
  /\ (lshape A -> lshape B ->
      forall d1 d2, rigid d1 T1 A -> rigid d2 T2 B ->
      forall r1 r2, goodr r1 -> goodr r2 -> Vp r1 T1 -> Vp r2 T2 ->
      (forall X, check T1 X -> check T2 X -> X < d1 -> X < d2 -> forall w, r1 X w <-> r2 X w) ->
      forall r1' E, goodr r1' -> Vc r1' A E ->
        (forall k w, r1' (k + keyLen A) w <-> r1 k w) ->
      exists r2', goodr r2' /\ Vc r2' B E /\
        (forall k w, r2' (k + keyLen B) w <-> r2 k w) /\
        (forall X, check (T1 +++ A) X -> check (T2 +++ B) X ->
           X < d1 + keyLen A -> X < d2 + keyLen B -> forall w, r1' X w <-> r2' X w))
  /\ (lshape A -> lshape B ->
      forall d1 d2, rigid d1 T1 A -> rigid d2 T2 B ->
      forall r1 r2, goodr r1 -> goodr r2 -> Vp r1 T1 -> Vp r2 T2 ->
      (forall X, check T1 X -> check T2 X -> X < d1 -> X < d2 -> forall w, r1 X w <-> r2 X w) ->
      forall r2' E, goodr r2' -> Vc r2' B E ->
        (forall k w, r2' (k + keyLen B) w <-> r2 k w) ->
      exists r1', goodr r1' /\ Vc r1' A E /\
        (forall k w, r1' (k + keyLen A) w <-> r1 k w) /\
        (forall X, check (T1 +++ A) X -> check (T2 +++ B) X ->
           X < d1 + keyLen A -> X < d2 + keyLen B -> forall w, r1' X w <-> r2' X w)).
Proof.
  intros n T1 A B T2 H. induction H.
  (* dq_int *)
  - split; [ | split ].
    + intros d1 d2 HrA HrB r1 r2 Hg1 Hg2 HV1 HV2 Hbnd v. simpl. tauto.
    + intros HlA HlB; solve [ inversion HlA | inversion HlB ].
    + intros HlA HlB; solve [ inversion HlA | inversion HlB ].
  (* dq_tvar *)
  - split; [ | split ].
    + intros d1 d2 HrA HrB r1 r2 Hg1 Hg2 HV1 HV2 Hbnd v.
      simpl. inversion HrA; subst.
      * (* HrA = bvar : check T1 X, X < d1 *)
        inversion HrB; subst.
        -- (* HrB = bvar *) apply (Hbnd X H1 H2 ltac:(assumption) ltac:(assumption) v).
        -- (* HrB = cvar *) exfalso. eapply lookt_check_false; eassumption.
      * (* HrA = cvar : lookt T1 X _ *)
        exfalso. eapply lookt_check_false; eassumption.
    + intros HlA HlB; solve [ inversion HlA | inversion HlB ].
    + intros HlA HlB; solve [ inversion HlA | inversion HlB ].
  (* dq_eql *)
  - split; [ | split ].
    + intros d1 d2 HrA HrB r1 r2 Hg1 Hg2 HV1 HV2 Hbnd v.
      simpl. inversion HrA; subst.
      * exfalso. exact (lookt_check_false H H2).
      * assert (A = B0) by (eapply lookt_det; eauto). subst.
        rewrite (Vp_lookt_pin H Hg1 HV1 v).
        exact (proj1 IHteqd d1 d2 ltac:(assumption) HrB r1 r2 Hg1 Hg2 HV1 HV2 Hbnd v).
    + intros HlA HlB; solve [ inversion HlA | inversion HlB ].
    + intros HlA HlB; solve [ inversion HlA | inversion HlB ].
  (* dq_eqr *)
  - split; [ | split ].
    + intros d1 d2 HrA HrB r1 r2 Hg1 Hg2 HV1 HV2 Hbnd v.
      simpl. inversion HrB; subst.
      * exfalso. exact (lookt_check_false H H2).
      * assert (B = B0) by (eapply lookt_det; eauto). subst.
        rewrite (Vp_lookt_pin H Hg2 HV2 v).
        exact (proj1 IHteqd d1 d2 HrA ltac:(assumption) r1 r2 Hg1 Hg2 HV1 HV2 Hbnd v).
    + intros HlA HlB; solve [ inversion HlA | inversion HlB ].
    + intros HlA HlB; solve [ inversion HlA | inversion HlB ].
  (* dq_boxl *)
  - split; [ | split ].
    + intros d1 d2 HrA HrB r1 r2 Hg1 Hg2 HV1 HV2 Hbnd v.
      assert (HrT3 : rigid 0 T3 A) by (eapply wft_box_rigid; exact H0).
      simpl. split.
      * (* box-EXTRACT: IH at the box's pin env, depth 0 *)
        intros (rE & HgE & HpE & HrEA').
        assert (Hbnd0 : forall X, check T3 X -> check T2 X -> X < 0 -> X < d2 -> forall w, rE X w <-> r2 X w) by (intros ? ? ? Hlt ?; exfalso; lia).
        apply (proj1 (proj1 IHteqd 0 d2 HrT3 HrB rE r2 HgE Hg2 HpE HV2 Hbnd0 v)). exact HrEA'.
      * (* box-PROVIDE: canonical pin env penv T3 *)
        intros HB. exists (penv T3). split; [ apply goodr_penv | split; [ apply Vp_penv | ] ].
        assert (Hbnd0 : forall X, check T3 X -> check T2 X -> X < 0 -> X < d2 -> forall w, penv T3 X w <-> r2 X w) by (intros ? ? ? Hlt ?; exfalso; lia).
        apply (proj2 (proj1 IHteqd 0 d2 HrT3 HrB (penv T3) r2 (goodr_penv T3) Hg2 (Vp_penv T3) HV2 Hbnd0 v)). exact HB.
    + intros HlA HlB; solve [ inversion HlA | inversion HlB ].
    + intros HlA HlB; solve [ inversion HlA | inversion HlB ].
  (* dq_boxr *)
  - split; [ | split ].
    + intros d1 d2 HrA HrB r1 r2 Hg1 Hg2 HV1 HV2 Hbnd v.
      assert (HrT3 : rigid 0 T3 B) by (eapply wft_box_rigid; exact H0).
      simpl. split.
      * (* box-PROVIDE *)
        intros HA. exists (penv T3). split; [ apply goodr_penv | split; [ apply Vp_penv | ] ].
        assert (Hbnd0 : forall X, check T1 X -> check T3 X -> X < d1 -> X < 0 -> forall w, r1 X w <-> penv T3 X w) by (intros ? ? ? ? HltY; exfalso; lia).
        apply (proj1 (proj1 IHteqd d1 0 HrA HrT3 r1 (penv T3) Hg1 (goodr_penv T3) HV1 (Vp_penv T3) Hbnd0 v)). exact HA.
      * (* box-EXTRACT *)
        intros (rE & HgE & HpE & HrEB').
        assert (Hbnd0 : forall X, check T1 X -> check T3 X -> X < d1 -> X < 0 -> forall w, r1 X w <-> rE X w) by (intros ? ? ? ? HltY; exfalso; lia).
        apply (proj2 (proj1 IHteqd d1 0 HrA HrT3 r1 rE Hg1 HgE HV1 HpE Hbnd0 v)). exact HrEB'.
    + intros HlA HlB; solve [ inversion HlA | inversion HlB ].
    + intros HlA HlB; solve [ inversion HlA | inversion HlB ].
  (* dq_arr *)
  - split; [ | split ].
    + intros d1 d2 HrA HrB r1 r2 Hg1 Hg2 HV1 HV2 Hbnd v.
      simpl. inversion HrA; subst. inversion HrB; subst. split.
      * intros (E&e&Heq&Hval&Hbody). exists E, e. split; [exact Heq | split; [exact Hval | intros v2 Hv2]].
        apply (proj2 (proj1 IHteqd1 d1 d2 ltac:(assumption) ltac:(assumption) r1 r2 Hg1 Hg2 HV1 HV2 Hbnd v2)) in Hv2.
        destruct (Hbody v2 Hv2) as (v'&Hms&Hvv&HB). exists v'. split; [exact Hms | split; [exact Hvv | apply (proj1 (proj1 IHteqd2 d1 d2 ltac:(assumption) ltac:(assumption) r1 r2 Hg1 Hg2 HV1 HV2 Hbnd v')); exact HB]].
      * intros (E&e&Heq&Hval&Hbody). exists E, e. split; [exact Heq | split; [exact Hval | intros v2 Hv2]].
        apply (proj1 (proj1 IHteqd1 d1 d2 ltac:(assumption) ltac:(assumption) r1 r2 Hg1 Hg2 HV1 HV2 Hbnd v2)) in Hv2.
        destruct (Hbody v2 Hv2) as (v'&Hms&Hvv&HB). exists v'. split; [exact Hms | split; [exact Hvv | apply (proj2 (proj1 IHteqd2 d1 d2 ltac:(assumption) ltac:(assumption) r1 r2 Hg1 Hg2 HV1 HV2 Hbnd v')); exact HB]].
    + intros HlA HlB; solve [ inversion HlA | inversion HlB ].
    + intros HlA HlB; solve [ inversion HlA | inversion HlB ].
  (* dq_all *)
  - split; [ | split ].
    + intros d1 d2 HrA HrB r1 r2 Hg1 Hg2 HV1 HV2 Hbnd v.
      simpl. inversion HrA; subst. inversion HrB; subst. split.
      * intros Hf R HRval.
        assert (HgR1: goodr (scons R r1)) by (apply goodr_scons; auto).
        assert (HgR2: goodr (scons R r2)) by (apply goodr_scons; auto).
        assert (HW: Vp (scons R r1) (T1 &s)). { simpl. eapply Vp_ext_imp; [ | exact HV1 ]. intro k; reflexivity. }
        assert (HW': Vp (scons R r2) (T2 &s)). { simpl. eapply Vp_ext_imp; [ | exact HV2 ]. intro k; reflexivity. }
        assert (Hbnd': forall X, check (T1 &s) X -> check (T2 &s) X -> X < S d1 -> X < S d2 -> forall w, scons R r1 X w <-> scons R r2 X w).
        { intros X HcX HcY HltX HltY w. inversion HcX; subst; inversion HcY; subst; simpl; try tauto;
          match goal with Ha : check T1 ?a, Hb : check T2 ?a |- _ => apply (Hbnd a Ha Hb); lia end. }
        apply (proj1 (proj1 IHteqd (S d1) (S d2) ltac:(assumption) ltac:(assumption) (scons R r1) (scons R r2) HgR1 HgR2 HW HW' Hbnd' v)). apply Hf; exact HRval.
      * intros Hf R HRval.
        assert (HgR1: goodr (scons R r1)) by (apply goodr_scons; auto).
        assert (HgR2: goodr (scons R r2)) by (apply goodr_scons; auto).
        assert (HW: Vp (scons R r1) (T1 &s)). { simpl. eapply Vp_ext_imp; [ | exact HV1 ]. intro k; reflexivity. }
        assert (HW': Vp (scons R r2) (T2 &s)). { simpl. eapply Vp_ext_imp; [ | exact HV2 ]. intro k; reflexivity. }
        assert (Hbnd': forall X, check (T1 &s) X -> check (T2 &s) X -> X < S d1 -> X < S d2 -> forall w, scons R r1 X w <-> scons R r2 X w).
        { intros X HcX HcY HltX HltY w. inversion HcX; subst; inversion HcY; subst; simpl; try tauto;
          match goal with Ha : check T1 ?a, Hb : check T2 ?a |- _ => apply (Hbnd a Ha Hb); lia end. }
        apply (proj2 (proj1 IHteqd (S d1) (S d2) ltac:(assumption) ltac:(assumption) (scons R r1) (scons R r2) HgR1 HgR2 HW HW' Hbnd' v)). apply Hf; exact HRval.
    + intros HlA HlB; solve [ inversion HlA | inversion HlB ].
    + intros HlA HlB; solve [ inversion HlA | inversion HlB ].
  (* dq_manil *)
  - split; [ | split ].
    + intros d1 d2 HrA HrB r1 r2 Hg1 Hg2 HV1 HV2 Hbnd v.
      simpl. inversion HrA; subst. split.
      * intros (R & HReq & HB).
        assert (HgR1: goodr (scons R r1)). { intros [|n0] w0 Hw0; simpl in Hw0; [exact (@V_value A r1 w0 Hg1 (proj1 (HReq w0) Hw0)) | apply (Hg1 n0 w0 Hw0)]. }
        assert (HW: Vp (scons R r1) (T1 &= A)).
        { simpl. split.
          - eapply Vp_ext_imp; [ | exact HV1 ]. intro k; reflexivity.
          - intro w. simpl. rewrite (HReq w). apply V_ext. intro k; reflexivity. }
        assert (HgR2: goodr (scons (fun w => V r1 A w) r2)).
        { intros [|n0] w0 Hw0; simpl in Hw0; [exact (@V_value A r1 w0 Hg1 Hw0) | apply (Hg2 n0 w0 Hw0)]. }
        assert (HW2: Vp (scons (fun w => V r1 A w) r2) (T2 &s)).
        { simpl. eapply Vp_ext_imp; [ intro k; unfold stail, scons; reflexivity | exact HV2 ]. }
        assert (Hbnd': forall X, check (T1 &= A) X -> check (T2 &s) X -> X < S d1 -> X < S d2 -> forall w, (scons R r1) X w <-> (scons (fun w => V r1 A w) r2) X w).
        { intros X HcX HcY HltX HltY w. inversion HcX; subst; inversion HcY; subst; simpl;
          match goal with Ha : check T1 ?a, Hb : check T2 ?a |- _ => apply (Hbnd a Ha Hb); lia end. }
        apply (proj1 (V_tshift0 C v HgR2)).
        apply (proj1 (proj1 IHteqd (S d1) (S d2) ltac:(eassumption) (rigid_pad_s HrB) (scons R r1) (scons (fun w => V r1 A w) r2) HgR1 HgR2 HW HW2 Hbnd' v)). exact HB.
      * intros HC. exists (fun w => V r1 A w). split; [intro w; reflexivity | ].
        assert (HgR1: goodr (scons (fun w => V r1 A w) r1)). { intros [|n0] w0 Hw0; simpl in Hw0; [exact (@V_value A r1 w0 Hg1 Hw0) | apply (Hg1 n0 w0 Hw0)]. }
        assert (HW: Vp (scons (fun w => V r1 A w) r1) (T1 &= A)).
        { simpl. split.
          - eapply Vp_ext_imp; [ | exact HV1 ]. intro k; reflexivity.
          - intro w. simpl. apply V_ext. intro k; reflexivity. }
        assert (HgR2: goodr (scons (fun w => V r1 A w) r2)).
        { intros [|n0] w0 Hw0; simpl in Hw0; [exact (@V_value A r1 w0 Hg1 Hw0) | apply (Hg2 n0 w0 Hw0)]. }
        assert (HW2: Vp (scons (fun w => V r1 A w) r2) (T2 &s)).
        { simpl. eapply Vp_ext_imp; [ intro k; unfold stail, scons; reflexivity | exact HV2 ]. }
        assert (Hbnd': forall X, check (T1 &= A) X -> check (T2 &s) X -> X < S d1 -> X < S d2 -> forall w, (scons (fun w => V r1 A w) r1) X w <-> (scons (fun w => V r1 A w) r2) X w).
        { intros X HcX HcY HltX HltY w. inversion HcX; subst; inversion HcY; subst; simpl;
          match goal with Ha : check T1 ?a, Hb : check T2 ?a |- _ => apply (Hbnd a Ha Hb); lia end. }
        apply (proj2 (proj1 IHteqd (S d1) (S d2) ltac:(eassumption) (rigid_pad_s HrB) (scons (fun w => V r1 A w) r1) (scons (fun w => V r1 A w) r2) HgR1 HgR2 HW HW2 Hbnd' v)).
        apply (proj2 (V_tshift0 C v HgR2)). exact HC.
    + intros HlA HlB; solve [ inversion HlA | inversion HlB ].
    + intros HlA HlB; solve [ inversion HlA | inversion HlB ].
  (* dq_manir *)
  - split; [ | split ].
    + intros d1 d2 HrA HrB r1 r2 Hg1 Hg2 HV1 HV2 Hbnd v.
      simpl. inversion HrB; subst. split.
      * intros HB. exists (fun w => V r2 A w). split; [intro w; reflexivity | ].
        assert (HgR2: goodr (scons (fun w => V r2 A w) r2)). { intros [|n0] w0 Hw0; simpl in Hw0; [exact (@V_value A r2 w0 Hg2 Hw0) | apply (Hg2 n0 w0 Hw0)]. }
        assert (HgR1: goodr (scons (fun w => V r2 A w) r1)). { intros [|n0] w0 Hw0; simpl in Hw0; [exact (@V_value A r2 w0 Hg2 Hw0) | apply (Hg1 n0 w0 Hw0)]. }
        assert (HW: Vp (scons (fun w => V r2 A w) r2) (T2 &= A)).
        { simpl. split.
          - eapply Vp_ext_imp; [ | exact HV2 ]. intro k; reflexivity.
          - intro w. simpl. apply V_ext. intro k; reflexivity. }
        assert (HW1: Vp (scons (fun w => V r2 A w) r1) (T1 &s)).
        { simpl. eapply Vp_ext_imp; [ intro k; unfold stail, scons; reflexivity | exact HV1 ]. }
        assert (Hbnd': forall X, check (T1 &s) X -> check (T2 &= A) X -> X < S d1 -> X < S d2 -> forall w, (scons (fun w => V r2 A w) r1) X w <-> (scons (fun w => V r2 A w) r2) X w).
        { intros X HcX HcY HltX HltY w. inversion HcX; subst; inversion HcY; subst; simpl;
          match goal with Ha : check T1 ?a, Hb : check T2 ?a |- _ => apply (Hbnd a Ha Hb); lia end. }
        apply (proj1 (proj1 IHteqd (S d1) (S d2) (rigid_pad_s HrA) ltac:(eassumption) (scons (fun w => V r2 A w) r1) (scons (fun w => V r2 A w) r2) HgR1 HgR2 HW1 HW Hbnd' v)).
        apply (proj2 (V_tshift0 B v HgR1)). exact HB.
      * intros (R & HReq & HC).
        assert (HgR2: goodr (scons R r2)). { intros [|n0] w0 Hw0; simpl in Hw0; [exact (@V_value A r2 w0 Hg2 (proj1 (HReq w0) Hw0)) | apply (Hg2 n0 w0 Hw0)]. }
        assert (HgR1: goodr (scons R r1)). { intros [|n0] w0 Hw0; simpl in Hw0; [exact (@V_value A r2 w0 Hg2 (proj1 (HReq w0) Hw0)) | apply (Hg1 n0 w0 Hw0)]. }
        assert (HW: Vp (scons R r2) (T2 &= A)).
        { simpl. split.
          - eapply Vp_ext_imp; [ | exact HV2 ]. intro k; reflexivity.
          - intro w. simpl. rewrite (HReq w). apply V_ext. intro k; reflexivity. }
        assert (HW1: Vp (scons R r1) (T1 &s)).
        { simpl. eapply Vp_ext_imp; [ intro k; unfold stail, scons; reflexivity | exact HV1 ]. }
        assert (Hbnd': forall X, check (T1 &s) X -> check (T2 &= A) X -> X < S d1 -> X < S d2 -> forall w, (scons R r1) X w <-> (scons R r2) X w).
        { intros X HcX HcY HltX HltY w. inversion HcX; subst; inversion HcY; subst; simpl;
          match goal with Ha : check T1 ?a, Hb : check T2 ?a |- _ => apply (Hbnd a Ha Hb); lia end. }
        apply (proj1 (V_tshift0 B v HgR1)).
        apply (proj2 (proj1 IHteqd (S d1) (S d2) (rigid_pad_s HrA) ltac:(eassumption) (scons R r1) (scons R r2) HgR1 HgR2 HW1 HW Hbnd' v)). exact HC.
    + intros HlA HlB; solve [ inversion HlA | inversion HlB ].
    + intros HlA HlB; solve [ inversion HlA | inversion HlB ].
  (* dq_top *)
  - split; [ | split ].
    + intros d1 d2 HrA HrB r1 r2 Hg1 Hg2 HV1 HV2 Hbnd v. simpl. tauto.
    + intros _ _ d1 d2 HrA HrB r1 r2 Hg1 Hg2 HV1 HV2 Hbnd r1' E Hgr1' HE Hcond.
      exists r2. simpl in HE; subst E. splits.
      * exact Hg2.
      * reflexivity.
      * intros k w. rewrite Nat.add_0_r. tauto.
      * intros X HcX HcY HltX HltY w. specialize (Hcond X w). rewrite Nat.add_0_r in Hcond.
        rewrite Hcond. rewrite Nat.add_0_r in HltX, HltY. apply (Hbnd X HcX HcY); lia.
    + intros _ _ d1 d2 HrA HrB r1 r2 Hg1 Hg2 HV1 HV2 Hbnd r2' E Hgr2' HE Hcond.
      exists r1. simpl in HE; subst E. splits.
      * exact Hg1.
      * reflexivity.
      * intros k w. rewrite Nat.add_0_r. tauto.
      * intros X HcX HcY HltX HltY w. specialize (Hcond X w). rewrite Nat.add_0_r in Hcond.
        rewrite Hcond. rewrite Nat.add_0_r in HltX, HltY. apply (Hbnd X HcX HcY); lia.
  (* dq_and *)
  - split; [ | split ].
    + intros d1 d2 HrA HrB r1 r2 Hg1 Hg2 HV1 HV2 Hbnd v.
      inversion HrA; subst. inversion HrB; subst.
      destruct m.
      * simpl. split.
        -- intros (E & w & r1' & Heqv & Hgr1' & HE & Hcond1 & HA).
           destruct (proj1 (proj2 IHteqd1) H0 H1 d1 d2 ltac:(eassumption) ltac:(eassumption) r1 r2 Hg1 Hg2 HV1 HV2 Hbnd r1' E Hgr1' HE Hcond1)
             as (r2' & Hgr2' & HE2 & Hcond2 & Hbnd').
           assert (HP1 : Vp r1' (T1 +++ T3)).
           { apply Vp_concat; [ exact H0 | | exact (Vc_Vp _ _ _ HE) ].
             eapply Vp_ext_iff_imp; [ | exact HV1 ]. intros k z. unfold sdrop. symmetry. apply Hcond1. }
           assert (HP2 : Vp r2' (T2 +++ T4)).
           { apply Vp_concat; [ exact H1 | | exact (Vc_Vp _ _ _ HE2) ].
             eapply Vp_ext_iff_imp; [ | exact HV2 ]. intros k z. unfold sdrop. symmetry. apply Hcond2. }
           exists E, w, r2'. splits; [ exact Heqv | exact Hgr2' | exact HE2 | exact Hcond2 | ].
           apply (proj1 (proj1 IHteqd2 (d1 + keyLen T3) (d2 + keyLen T4) ltac:(eassumption) ltac:(eassumption) r1' r2' Hgr1' Hgr2' HP1 HP2 Hbnd' w)). exact HA.
        -- intros (E & w & r2' & Heqv & Hgr2' & HE2 & Hcond2 & HB).
           destruct (proj2 (proj2 IHteqd1) H0 H1 d1 d2 ltac:(eassumption) ltac:(eassumption) r1 r2 Hg1 Hg2 HV1 HV2 Hbnd r2' E Hgr2' HE2 Hcond2)
             as (r1' & Hgr1' & HE1 & Hcond1 & Hbnd').
           assert (HP1 : Vp r1' (T1 +++ T3)).
           { apply Vp_concat; [ exact H0 | | exact (Vc_Vp _ _ _ HE1) ].
             eapply Vp_ext_iff_imp; [ | exact HV1 ]. intros k z. unfold sdrop. symmetry. apply Hcond1. }
           assert (HP2 : Vp r2' (T2 +++ T4)).
           { apply Vp_concat; [ exact H1 | | exact (Vc_Vp _ _ _ HE2) ].
             eapply Vp_ext_iff_imp; [ | exact HV2 ]. intros k z. unfold sdrop. symmetry. apply Hcond2. }
           exists E, w, r1'. splits; [ exact Heqv | exact Hgr1' | exact HE1 | exact Hcond1 | ].
           apply (proj2 (proj1 IHteqd2 (d1 + keyLen T3) (d2 + keyLen T4) ltac:(eassumption) ltac:(eassumption) r1' r2' Hgr1' Hgr2' HP1 HP2 Hbnd' w)). exact HB.
      * simpl. split.
        -- intros (r1' & Hgr1' & HE & Hcond1).
           destruct (proj1 (proj2 IHteqd1) H0 H1 d1 d2 ltac:(eassumption) ltac:(eassumption) r1 r2 Hg1 Hg2 HV1 HV2 Hbnd r1' v Hgr1' HE Hcond1)
             as (r2' & Hgr2' & HE2 & Hcond2 & Hbnd').
           exists r2'. splits; [ exact Hgr2' | exact HE2 | exact Hcond2 ].
        -- intros (r2' & Hgr2' & HE2 & Hcond2).
           destruct (proj2 (proj2 IHteqd1) H0 H1 d1 d2 ltac:(eassumption) ltac:(eassumption) r1 r2 Hg1 Hg2 HV1 HV2 Hbnd r2' v Hgr2' HE2 Hcond2)
             as (r1' & Hgr1' & HE1 & Hcond1 & Hbnd').
           exists r1'. splits; [ exact Hgr1' | exact HE1 | exact Hcond1 ].
    + intros HlA HlB d1 d2 HrA HrB r1 r2 Hg1 Hg2 HV1 HV2 Hbnd r1' E Hgr1' HE Hcond.
      assert (HlT3 : lshape T3) by exact H0.
      assert (HlT4 : lshape T4) by exact H1.
      inversion HrA; subst. inversion HrB; subst.
      destruct m.
      * (* non *)
        assert (HkA : keyLen (T3 & A) = keyLen T3) by reflexivity.
        assert (HkB : keyLen (T4 & B) = keyLen T4) by reflexivity.
        assert (Hcat3 : (T1 +++ (T3 & A)) = ((T1 +++ T3) & A)) by (destruct T3; reflexivity).
        assert (Hcat4 : (T2 +++ (T4 & B)) = ((T2 +++ T4) & B)) by (destruct T4; reflexivity).
        simpl in HE. destruct HE as (E0 & w & HEeq & HET3 & HAw).
        rewrite HkA in Hcond.
        destruct (proj1 (proj2 IHteqd1) HlT3 HlT4 d1 d2 ltac:(eassumption) ltac:(eassumption) r1 r2 Hg1 Hg2 HV1 HV2 Hbnd r1' E0 Hgr1' HET3 Hcond)
          as (r2' & Hgr2' & HET4 & Hcond2 & Hbnd').
        assert (HP1 : Vp r1' (T1 +++ T3)).
        { apply Vp_concat; [ exact HlT3 | | exact (Vc_Vp _ _ _ HET3) ].
          eapply Vp_ext_iff_imp; [ | exact HV1 ]. intros k z. unfold sdrop. symmetry. apply Hcond. }
        assert (HP2 : Vp r2' (T2 +++ T4)).
        { apply Vp_concat; [ exact HlT4 | | exact (Vc_Vp _ _ _ HET4) ].
          eapply Vp_ext_iff_imp; [ | exact HV2 ]. intros k z. unfold sdrop. symmetry. apply Hcond2. }
        assert (HBw : V r2' B w).
        { apply (proj1 (proj1 IHteqd2 (d1 + keyLen T3) (d2 + keyLen T4) ltac:(eassumption) ltac:(eassumption) r1' r2' Hgr1' Hgr2' HP1 HP2 Hbnd' w)). exact HAw. }
        exists r2'. splits.
        -- exact Hgr2'.
        -- simpl. exists E0, w. split; [ exact HEeq | split; [exact HET4 | exact HBw] ].
        -- rewrite HkB. exact Hcond2.
        -- rewrite Hcat3, Hcat4. intros X HcX HcY HltX HltY w0.
           rewrite HkA in HltX. rewrite HkB in HltY.
           inversion HcX; subst. inversion HcY; subst.
           match goal with HX : check (T1 +++ T3) ?a, HY : check (T2 +++ T4) ?a |- _ =>
             apply (Hbnd' a HX HY); lia end.
      * (* rt: T3 &= A *)
        assert (HkA : keyLen (T3 &= A) = S (keyLen T3)) by reflexivity.
        assert (HkB : keyLen (T4 &= B) = S (keyLen T4)) by reflexivity.
        assert (Hcat3 : (T1 +++ (T3 &= A)) = ((T1 +++ T3) &= A)) by (destruct T3; reflexivity).
        assert (Hcat4 : (T2 +++ (T4 &= B)) = ((T2 +++ T4) &= B)) by (destruct T4; reflexivity).
        simpl in HE. destruct HE as (HET3 & Hpin).
        assert (Hcih : forall k w, (stail r1') (k + keyLen T3) w <-> r1 k w).
        { intros k w. unfold stail. specialize (Hcond k w). rewrite HkA in Hcond.
          rewrite <- Nat.add_succ_r. exact Hcond. }
        destruct (proj1 (proj2 IHteqd1) HlT3 HlT4 d1 d2 ltac:(eassumption) ltac:(eassumption) r1 r2 Hg1 Hg2 HV1 HV2 Hbnd (stail r1') E
                    (goodr_stail Hgr1') HET3 Hcih)
          as (r2'0 & Hgr2'0 & HET4 & Hcond2'0 & Hbnd'0).
        exists (scons (fun w => V r2'0 B w) r2'0). splits.
        -- apply goodr_scons; [ intros w Hw; exact (@V_value B r2'0 w Hgr2'0 Hw) | exact Hgr2'0 ].
        -- simpl. split.
           ++ eapply Vc_ext_imp; [ intro k; unfold stail, scons; reflexivity | exact HET4 ].
           ++ intro w. unfold scons, stail. reflexivity.
        -- intros k w. rewrite HkB. simpl. rewrite Nat.add_succ_r. exact (Hcond2'0 k w).
        -- rewrite Hcat3, Hcat4. intros X HcX HcY HltX HltY w0.
           rewrite HkA in HltX. rewrite HkB in HltY.
           inversion HcX; subst. inversion HcY; subst. simpl.
           match goal with HX : check (T1 +++ T3) ?a, HY : check (T2 +++ T4) ?a |- _ =>
             generalize (Hbnd'0 a HX HY ltac:(lia) ltac:(lia) w0) end.
           unfold stail, scons; simpl; tauto.
    + intros HlA HlB d1 d2 HrA HrB r1 r2 Hg1 Hg2 HV1 HV2 Hbnd r2' E Hgr2' HE Hcond.
      assert (HlT3 : lshape T3) by exact H0.
      assert (HlT4 : lshape T4) by exact H1.
      inversion HrA; subst. inversion HrB; subst.
      destruct m.
      * (* non *)
        assert (HkA : keyLen (T3 & A) = keyLen T3) by reflexivity.
        assert (HkB : keyLen (T4 & B) = keyLen T4) by reflexivity.
        assert (Hcat3 : (T1 +++ (T3 & A)) = ((T1 +++ T3) & A)) by (destruct T3; reflexivity).
        assert (Hcat4 : (T2 +++ (T4 & B)) = ((T2 +++ T4) & B)) by (destruct T4; reflexivity).
        simpl in HE. destruct HE as (E0 & w & HEeq & HET4 & HBw).
        rewrite HkB in Hcond.
        destruct (proj2 (proj2 IHteqd1) HlT3 HlT4 d1 d2 ltac:(eassumption) ltac:(eassumption) r1 r2 Hg1 Hg2 HV1 HV2 Hbnd r2' E0 Hgr2' HET4 Hcond)
          as (r1' & Hgr1' & HET3 & Hcond1 & Hbnd').
        assert (HP1 : Vp r1' (T1 +++ T3)).
        { apply Vp_concat; [ exact HlT3 | | exact (Vc_Vp _ _ _ HET3) ].
          eapply Vp_ext_iff_imp; [ | exact HV1 ]. intros k z. unfold sdrop. symmetry. apply Hcond1. }
        assert (HP2 : Vp r2' (T2 +++ T4)).
        { apply Vp_concat; [ exact HlT4 | | exact (Vc_Vp _ _ _ HET4) ].
          eapply Vp_ext_iff_imp; [ | exact HV2 ]. intros k z. unfold sdrop. symmetry. apply Hcond. }
        assert (HAw : V r1' A w).
        { apply (proj2 (proj1 IHteqd2 (d1 + keyLen T3) (d2 + keyLen T4) ltac:(eassumption) ltac:(eassumption) r1' r2' Hgr1' Hgr2' HP1 HP2 Hbnd' w)). exact HBw. }
        exists r1'. splits.
        -- exact Hgr1'.
        -- simpl. exists E0, w. split; [ exact HEeq | split; [exact HET3 | exact HAw] ].
        -- rewrite HkA. exact Hcond1.
        -- rewrite Hcat3, Hcat4. intros X HcX HcY HltX HltY w0.
           rewrite HkA in HltX. rewrite HkB in HltY.
           inversion HcX; subst. inversion HcY; subst.
           match goal with HX : check (T1 +++ T3) ?a, HY : check (T2 +++ T4) ?a |- _ =>
             apply (Hbnd' a HX HY); lia end.
      * (* rt: T4 &= B *)
        assert (HkA : keyLen (T3 &= A) = S (keyLen T3)) by reflexivity.
        assert (HkB : keyLen (T4 &= B) = S (keyLen T4)) by reflexivity.
        assert (Hcat3 : (T1 +++ (T3 &= A)) = ((T1 +++ T3) &= A)) by (destruct T3; reflexivity).
        assert (Hcat4 : (T2 +++ (T4 &= B)) = ((T2 +++ T4) &= B)) by (destruct T4; reflexivity).
        simpl in HE. destruct HE as (HET4 & Hpin).
        assert (Hcih : forall k w, (stail r2') (k + keyLen T4) w <-> r2 k w).
        { intros k w. unfold stail. specialize (Hcond k w). rewrite HkB in Hcond.
          rewrite <- Nat.add_succ_r. exact Hcond. }
        destruct (proj2 (proj2 IHteqd1) HlT3 HlT4 d1 d2 ltac:(eassumption) ltac:(eassumption) r1 r2 Hg1 Hg2 HV1 HV2 Hbnd (stail r2') E
                    (goodr_stail Hgr2') HET4 Hcih)
          as (r1'0 & Hgr1'0 & HET3 & Hcond1'0 & Hbnd'0).
        exists (scons (fun w => V r1'0 A w) r1'0). splits.
        -- apply goodr_scons; [ intros w Hw; exact (@V_value A r1'0 w Hgr1'0 Hw) | exact Hgr1'0 ].
        -- simpl. split.
           ++ eapply Vc_ext_imp; [ intro k; unfold stail, scons; reflexivity | exact HET3 ].
           ++ intro w. unfold scons, stail. reflexivity.
        -- intros k w. rewrite HkA. simpl. rewrite Nat.add_succ_r. exact (Hcond1'0 k w).
        -- rewrite Hcat3, Hcat4. intros X HcX HcY HltX HltY w0.
           rewrite HkA in HltX. rewrite HkB in HltY.
           inversion HcX; subst. inversion HcY; subst. simpl.
           match goal with HX : check (T1 +++ T3) ?a, HY : check (T2 +++ T4) ?a |- _ =>
             generalize (Hbnd'0 a HX HY ltac:(lia) ltac:(lia) w0) end.
           unfold stail, scons; simpl; tauto.
  (* dq_ands *)
  - split; [ | split ].
    + intros d1 d2 HrA HrB r1 r2 Hg1 Hg2 HV1 HV2 Hbnd v.
      inversion HrA; subst. inversion HrB; subst.
      simpl. split.
      * intros (r1' & Hgr1' & HET3 & Hcond1).
        destruct (proj1 (proj2 IHteqd) H0 H1 d1 d2 ltac:(eassumption) ltac:(eassumption) r1 r2 Hg1 Hg2 HV1 HV2 Hbnd r1' v Hgr1' HET3 Hcond1)
          as (r2' & Hgr2' & HET4 & Hcond2 & Hbnd').
        exists r2'. splits; [ exact Hgr2' | exact HET4 | exact Hcond2 ].
      * intros (r2' & Hgr2' & HET4 & Hcond2).
        destruct (proj2 (proj2 IHteqd) H0 H1 d1 d2 ltac:(eassumption) ltac:(eassumption) r1 r2 Hg1 Hg2 HV1 HV2 Hbnd r2' v Hgr2' HET4 Hcond2)
          as (r1' & Hgr1' & HET3 & Hcond1 & Hbnd').
        exists r1'. splits; [ exact Hgr1' | exact HET3 | exact Hcond1 ].
    + intros _ _ d1 d2 HrA HrB r1 r2 Hg1 Hg2 HV1 HV2 Hbnd r1' E Hgr1' HE Hcond.
      inversion HrA; subst. inversion HrB; subst.
      simpl in HE.
      assert (Hcih : forall k w, (stail r1') (k + keyLen T3) w <-> r1 k w).
      { intros k w. unfold stail. specialize (Hcond k w). simpl in Hcond.
        rewrite <- Nat.add_succ_r. exact Hcond. }
      destruct (proj1 (proj2 IHteqd) H0 H1 d1 d2 ltac:(eassumption) ltac:(eassumption) r1 r2 Hg1 Hg2 HV1 HV2 Hbnd (stail r1') E
                  (goodr_stail Hgr1') HE Hcih)
        as (r2'0 & Hgr2'0 & HET4 & Hcond2'0 & Hbnd'0).
      exists (scons (r1' 0) r2'0). splits.
      * apply goodr_scons; [ intros w Hw; exact (Hgr1' 0 w Hw) | exact Hgr2'0 ].
      * simpl. eapply Vc_ext_imp; [ intro k; unfold stail, scons; reflexivity | exact HET4 ].
      * intros k w. simpl. rewrite Nat.add_succ_r. exact (Hcond2'0 k w).
      * assert (Hcat3 : (T1 +++ (T3 &s)) = ((T1 +++ T3) &s)) by (destruct T3; reflexivity).
        assert (Hcat4 : (T2 +++ (T4 &s)) = ((T2 +++ T4) &s)) by (destruct T4; reflexivity).
        rewrite Hcat3, Hcat4.
        intros X HcX HcY HltX HltY w.
        simpl in HltX, HltY.
        inversion HcX; subst; inversion HcY; subst; simpl;
          try (unfold scons; tauto);
          match goal with
          | HX : check (T1 +++ T3) ?a, HY : check (T2 +++ T4) ?a |- _ =>
              generalize (Hbnd'0 a HX HY ltac:(lia) ltac:(lia) w); unfold stail, scons; simpl; tauto
          end.
    + intros _ _ d1 d2 HrA HrB r1 r2 Hg1 Hg2 HV1 HV2 Hbnd r2' E Hgr2' HE Hcond.
      inversion HrA; subst. inversion HrB; subst.
      simpl in HE.
      assert (Hcih : forall k w, (stail r2') (k + keyLen T4) w <-> r2 k w).
      { intros k w. unfold stail. specialize (Hcond k w). simpl in Hcond.
        rewrite <- Nat.add_succ_r. exact Hcond. }
      destruct (proj2 (proj2 IHteqd) H0 H1 d1 d2 ltac:(eassumption) ltac:(eassumption) r1 r2 Hg1 Hg2 HV1 HV2 Hbnd (stail r2') E
                  (goodr_stail Hgr2') HE Hcih)
        as (r1'0 & Hgr1'0 & HET3 & Hcond1'0 & Hbnd'0).
      exists (scons (r2' 0) r1'0). splits.
      * apply goodr_scons; [ intros w Hw; exact (Hgr2' 0 w Hw) | exact Hgr1'0 ].
      * simpl. eapply Vc_ext_imp; [ intro k; unfold stail, scons; reflexivity | exact HET3 ].
      * intros k w. simpl. rewrite Nat.add_succ_r. exact (Hcond1'0 k w).
      * assert (Hcat3 : (T1 +++ (T3 &s)) = ((T1 +++ T3) &s)) by (destruct T3; reflexivity).
        assert (Hcat4 : (T2 +++ (T4 &s)) = ((T2 +++ T4) &s)) by (destruct T4; reflexivity).
        rewrite Hcat3, Hcat4.
        intros X HcX HcY HltX HltY w.
        simpl in HltX, HltY.
        inversion HcX; subst; inversion HcY; subst; simpl;
          try (unfold scons; tauto);
          match goal with
          | HX : check (T1 +++ T3) ?a, HY : check (T2 +++ T4) ?a |- _ =>
              generalize (Hbnd'0 a HX HY ltac:(lia) ltac:(lia) w); unfold stail, scons; simpl; tauto
          end.
  (* dq_rcd *)
  - split; [ | split ].
    + intros d1 d2 HrA HrB r1 r2 Hg1 Hg2 HV1 HV2 Hbnd v.
      simpl. inversion HrA; subst. inversion HrB; subst. split.
      * intros (v'&Heq&HA). exists v'. split; [exact Heq | apply (proj1 (proj1 IHteqd d1 d2 ltac:(eassumption) ltac:(eassumption) r1 r2 Hg1 Hg2 HV1 HV2 Hbnd v')); exact HA].
      * intros (v'&Heq&HA). exists v'. split; [exact Heq | apply (proj2 (proj1 IHteqd d1 d2 ltac:(eassumption) ltac:(eassumption) r1 r2 Hg1 Hg2 HV1 HV2 Hbnd v')); exact HA].
    + intros HlA HlB; solve [ inversion HlA | inversion HlB ].
    + intros HlA HlB; solve [ inversion HlA | inversion HlB ].
Qed.

Lemma comp_eq_rigid : forall n T1 A B T2, teqd n T1 A B T2 ->
  forall d1 d2, rigid d1 T1 A -> rigid d2 T2 B ->
  forall r1 r2, goodr r1 -> goodr r2 -> Vp r1 T1 -> Vp r2 T2 ->
  (forall X, check T1 X -> check T2 X -> X < d1 -> X < d2 -> forall w, r1 X w <-> r2 X w) ->
  forall v, V r1 A v <-> V r2 B v.
Proof. intros n T1 A B T2 H. exact (proj1 (comp_eq_rigid_combined H)). Qed.

(* === Combined teq-compatibility + prefix-transport, Vp-premised ===
   Boxes are entered with only PIN respect (Vp); concreteness of the box's
   context makes the (full) inner-alignment vacuous there, and the canonical
   pin env penv witnesses the PROVIDE direction (no realizer needed). *)
Lemma comp_eq_combined : forall T1 A B T2, teq T1 A B T2 ->
  (forall r1 r2, goodr r1 -> goodr r2 -> Vp r1 T1 -> Vp r2 T2 ->
     Ralign r1 r2 T1 T2 -> forall v, V r1 A v <-> V r2 B v)
  /\ (lshape A -> lshape B ->
      forall r1 r2, goodr r1 -> goodr r2 -> Vp r1 T1 -> Vp r2 T2 -> Ralign r1 r2 T1 T2 ->
      forall r1' E, goodr r1' -> Vc r1' A E ->
        (forall k w, r1' (k + keyLen A) w <-> r1 k w) ->
      exists r2', goodr r2' /\ Vc r2' B E /\
        (forall k w, r2' (k + keyLen B) w <-> r2 k w) /\
        Ralign r1' r2' (T1 +++ A) (T2 +++ B))
  /\ (lshape A -> lshape B ->
      forall r1 r2, goodr r1 -> goodr r2 -> Vp r1 T1 -> Vp r2 T2 -> Ralign r1 r2 T1 T2 ->
      forall r2' E, goodr r2' -> Vc r2' B E ->
        (forall k w, r2' (k + keyLen B) w <-> r2 k w) ->
      exists r1', goodr r1' /\ Vc r1' A E /\
        (forall k w, r1' (k + keyLen A) w <-> r1 k w) /\
        Ralign r1' r2' (T1 +++ A) (T2 +++ B)).
Proof.
  intros T1 A B T2 H. induction H.
  (* eq_int *)
  - split; [| split].
    + intros r1 r2 Hg1 Hg2 HV1 HV2 Hal v. simpl. tauto.
    + intros HlA HlB; solve [ inversion HlA | inversion HlB ].
    + intros HlA HlB; solve [ inversion HlA | inversion HlB ].
  (* eq_tvar *)
  - split; [| split].
    + intros r1 r2 Hg1 Hg2 HV1 HV2 Hal v. simpl. exact (Hal X H1 H2 v).
    + intros HlA HlB; solve [ inversion HlA | inversion HlB ].
    + intros HlA HlB; solve [ inversion HlA | inversion HlB ].
  (* eq_eql *)
  - split; [| split].
    + intros r1 r2 Hg1 Hg2 HV1 HV2 Hal v. simpl.
      rewrite (Vp_lookt_pin H Hg1 HV1 v). exact (proj1 IHteq r1 r2 Hg1 Hg2 HV1 HV2 Hal v).
    + intros HlA HlB; solve [ inversion HlA | inversion HlB ].
    + intros HlA HlB; solve [ inversion HlA | inversion HlB ].
  (* eq_eqr *)
  - split; [| split].
    + intros r1 r2 Hg1 Hg2 HV1 HV2 Hal v. simpl.
      rewrite (Vp_lookt_pin H Hg2 HV2 v). exact (proj1 IHteq r1 r2 Hg1 Hg2 HV1 HV2 Hal v).
    + intros HlA HlB; solve [ inversion HlA | inversion HlB ].
    + intros HlA HlB; solve [ inversion HlA | inversion HlB ].
  (* eq_boxl: teq T3 A B T2, wft T1 (boxt T3 A) -- the box body is RIGID
     (wft_box_rigid), so delegate to the rigid-bounded compatibility at
     d1 = d2 = 0 (bounded alignment vacuous). *)
  - split; [| split].
    + intros r1 r2 Hg1 Hg2 HV1 HV2 Hal v.
      destruct (teq_teqd H) as (n & Hd).
      assert (Hbox : teqd (S n) T1 (boxt T3 A) B T2) by (eapply dq_boxl; eassumption).
      assert (HrA : rigid 0 T1 (boxt T3 A)) by (eapply rigid_box; eapply wft_box_rigid; eassumption).
      assert (HrB : rigid 0 T2 B) by (eapply teqd_rigid_r; eassumption).
      assert (Hbnd0 : forall X, check T1 X -> check T2 X -> X < 0 -> X < 0 -> forall w, r1 X w <-> r2 X w)
        by (intros ? ? ? Hlt ?; exfalso; lia).
      exact (comp_eq_rigid Hbox HrA HrB Hg1 Hg2 HV1 HV2 Hbnd0 v).
    + intros HlA HlB; solve [ inversion HlA | inversion HlB ].
    + intros HlA HlB; solve [ inversion HlA | inversion HlB ].
  (* eq_boxr: teq T1 A B T3, wft T2 (boxt T3 B) -- symmetric. *)
  - split; [| split].
    + intros r1 r2 Hg1 Hg2 HV1 HV2 Hal v.
      destruct (teq_teqd H) as (n & Hd).
      assert (Hbox : teqd (S n) T1 A (boxt T3 B) T2) by (eapply dq_boxr; eassumption).
      assert (HrB : rigid 0 T2 (boxt T3 B)) by (eapply rigid_box; eapply wft_box_rigid; eassumption).
      assert (HrA : rigid 0 T1 A) by (eapply teqd_rigid_l; eassumption).
      assert (Hbnd0 : forall X, check T1 X -> check T2 X -> X < 0 -> X < 0 -> forall w, r1 X w <-> r2 X w)
        by (intros ? ? ? Hlt ?; exfalso; lia).
      exact (comp_eq_rigid Hbox HrA HrB Hg1 Hg2 HV1 HV2 Hbnd0 v).
    + intros HlA HlB; solve [ inversion HlA | inversion HlB ].
    + intros HlA HlB; solve [ inversion HlA | inversion HlB ].
  (* eq_arr *)
  - split; [| split].
    + intros r1 r2 Hg1 Hg2 HV1 HV2 Hal v. simpl. split.
      * intros (E&e&Heq&Hval&Hbody). exists E, e. split; [exact Heq | split; [exact Hval | intros v2 Hv2]].
        apply (proj2 (proj1 IHteq1 r1 r2 Hg1 Hg2 HV1 HV2 Hal v2)) in Hv2.
        destruct (Hbody v2 Hv2) as (v'&Hms&Hvv&HB). exists v'. split; [exact Hms | split; [exact Hvv | apply (proj1 (proj1 IHteq2 r1 r2 Hg1 Hg2 HV1 HV2 Hal v')); exact HB]].
      * intros (E&e&Heq&Hval&Hbody). exists E, e. split; [exact Heq | split; [exact Hval | intros v2 Hv2]].
        apply (proj1 (proj1 IHteq1 r1 r2 Hg1 Hg2 HV1 HV2 Hal v2)) in Hv2.
        destruct (Hbody v2 Hv2) as (v'&Hms&Hvv&HB). exists v'. split; [exact Hms | split; [exact Hvv | apply (proj2 (proj1 IHteq2 r1 r2 Hg1 Hg2 HV1 HV2 Hal v')); exact HB]].
    + intros HlA HlB; solve [ inversion HlA | inversion HlB ].
    + intros HlA HlB; solve [ inversion HlA | inversion HlB ].
  (* eq_all *)
  - split; [| split].
    + intros r1 r2 Hg1 Hg2 HV1 HV2 Hal v. simpl. split.
      * intros Hf R HRval.
        assert (HgR1: goodr (scons R r1)) by (apply goodr_scons; auto).
        assert (HgR2: goodr (scons R r2)) by (apply goodr_scons; auto).
        assert (HW: Vp (scons R r1) (T1 &s)). { simpl. eapply Vp_ext_imp; [ | exact HV1 ]. intro k; reflexivity. }
        assert (HW': Vp (scons R r2) (T2 &s)). { simpl. eapply Vp_ext_imp; [ | exact HV2 ]. intro k; reflexivity. }
        assert (Hal': Ralign (scons R r1) (scons R r2) (T1 &s) (T2 &s)).
        { intros X HcX HcY w. inversion HcX; subst; inversion HcY; subst; simpl; try tauto;
          match goal with Ha : check T1 ?a, Hb : check T2 ?a |- _ => apply (Hal a Ha Hb w) end. }
        apply (proj1 (proj1 IHteq (scons R r1) (scons R r2) HgR1 HgR2 HW HW' Hal' v)). apply Hf; exact HRval.
      * intros Hf R HRval.
        assert (HgR1: goodr (scons R r1)) by (apply goodr_scons; auto).
        assert (HgR2: goodr (scons R r2)) by (apply goodr_scons; auto).
        assert (HW: Vp (scons R r1) (T1 &s)). { simpl. eapply Vp_ext_imp; [ | exact HV1 ]. intro k; reflexivity. }
        assert (HW': Vp (scons R r2) (T2 &s)). { simpl. eapply Vp_ext_imp; [ | exact HV2 ]. intro k; reflexivity. }
        assert (Hal': Ralign (scons R r1) (scons R r2) (T1 &s) (T2 &s)).
        { intros X HcX HcY w. inversion HcX; subst; inversion HcY; subst; simpl; try tauto;
          match goal with Ha : check T1 ?a, Hb : check T2 ?a |- _ => apply (Hal a Ha Hb w) end. }
        apply (proj2 (proj1 IHteq (scons R r1) (scons R r2) HgR1 HgR2 HW HW' Hal' v)). apply Hf; exact HRval.
    + intros HlA HlB; solve [ inversion HlA | inversion HlB ].
    + intros HlA HlB; solve [ inversion HlA | inversion HlB ].
  (* eq_manil *)
  - split; [| split].
    + intros r1 r2 Hg1 Hg2 HV1 HV2 Hal v. simpl. split.
      * intros (R & HReq & HB).
        assert (HgR1: goodr (scons R r1)). { intros [|n0] w0 Hw0; simpl in Hw0; [exact (@V_value A r1 w0 Hg1 (proj1 (HReq w0) Hw0)) | apply (Hg1 n0 w0 Hw0)]. }
        assert (HW: Vp (scons R r1) (T1 &= A)).
        { simpl. split.
          - eapply Vp_ext_imp; [ | exact HV1 ]. intro k; reflexivity.
          - intro w. simpl. rewrite (HReq w). apply V_ext. intro k; reflexivity. }
        assert (HgR2: goodr (scons (fun w => V r1 A w) r2)).
        { intros [|n0] w0 Hw0; simpl in Hw0; [exact (@V_value A r1 w0 Hg1 Hw0) | apply (Hg2 n0 w0 Hw0)]. }
        assert (HW2: Vp (scons (fun w => V r1 A w) r2) (T2 &s)).
        { simpl. eapply Vp_ext_imp; [ intro k; unfold stail, scons; reflexivity | exact HV2 ]. }
        assert (Hal': Ralign (scons R r1) (scons (fun w => V r1 A w) r2) (T1 &= A) (T2 &s)).
        { intros X HcX HcY w. inversion HcX; subst; inversion HcY; subst; simpl. match goal with HX : check T1 ?a, HY : check T2 ?a |- _ => apply (Hal a HX HY w) end. }
        apply (proj1 (V_tshift0 C v HgR2)).
        apply (proj1 (proj1 IHteq (scons R r1) (scons (fun w => V r1 A w) r2) HgR1 HgR2 HW HW2 Hal' v)). exact HB.
      * intros HC. exists (fun w => V r1 A w). split; [intro w; reflexivity | ].
        assert (HgR1: goodr (scons (fun w => V r1 A w) r1)). { intros [|n0] w0 Hw0; simpl in Hw0; [exact (@V_value A r1 w0 Hg1 Hw0) | apply (Hg1 n0 w0 Hw0)]. }
        assert (HW: Vp (scons (fun w => V r1 A w) r1) (T1 &= A)).
        { simpl. split.
          - eapply Vp_ext_imp; [ | exact HV1 ]. intro k; reflexivity.
          - intro w. simpl. apply V_ext. intro k; reflexivity. }
        assert (HgR2: goodr (scons (fun w => V r1 A w) r2)).
        { intros [|n0] w0 Hw0; simpl in Hw0; [exact (@V_value A r1 w0 Hg1 Hw0) | apply (Hg2 n0 w0 Hw0)]. }
        assert (HW2: Vp (scons (fun w => V r1 A w) r2) (T2 &s)).
        { simpl. eapply Vp_ext_imp; [ intro k; unfold stail, scons; reflexivity | exact HV2 ]. }
        assert (Hal': Ralign (scons (fun w => V r1 A w) r1) (scons (fun w => V r1 A w) r2) (T1 &= A) (T2 &s)).
        { intros X HcX HcY w. inversion HcX; subst; inversion HcY; subst; simpl. match goal with HX : check T1 ?a, HY : check T2 ?a |- _ => apply (Hal a HX HY w) end. }
        apply (proj2 (proj1 IHteq (scons (fun w => V r1 A w) r1) (scons (fun w => V r1 A w) r2) HgR1 HgR2 HW HW2 Hal' v)).
        apply (proj2 (V_tshift0 C v HgR2)). exact HC.
    + intros HlA HlB; solve [ inversion HlA | inversion HlB ].
    + intros HlA HlB; solve [ inversion HlA | inversion HlB ].
  (* eq_manir *)
  - split; [| split].
    + intros r1 r2 Hg1 Hg2 HV1 HV2 Hal v. simpl. split.
      * intros HB. exists (fun w => V r2 A w). split; [intro w; reflexivity | ].
        assert (HgR2: goodr (scons (fun w => V r2 A w) r2)). { intros [|n0] w0 Hw0; simpl in Hw0; [exact (@V_value A r2 w0 Hg2 Hw0) | apply (Hg2 n0 w0 Hw0)]. }
        assert (HgR1: goodr (scons (fun w => V r2 A w) r1)). { intros [|n0] w0 Hw0; simpl in Hw0; [exact (@V_value A r2 w0 Hg2 Hw0) | apply (Hg1 n0 w0 Hw0)]. }
        assert (HW: Vp (scons (fun w => V r2 A w) r2) (T2 &= A)).
        { simpl. split.
          - eapply Vp_ext_imp; [ | exact HV2 ]. intro k; reflexivity.
          - intro w. simpl. apply V_ext. intro k; reflexivity. }
        assert (HW1: Vp (scons (fun w => V r2 A w) r1) (T1 &s)).
        { simpl. eapply Vp_ext_imp; [ intro k; unfold stail, scons; reflexivity | exact HV1 ]. }
        assert (Hal': Ralign (scons (fun w => V r2 A w) r1) (scons (fun w => V r2 A w) r2) (T1 &s) (T2 &= A)).
        { intros X HcX HcY w. inversion HcX; subst; inversion HcY; subst; simpl. match goal with HX : check T1 ?a, HY : check T2 ?a |- _ => apply (Hal a HX HY w) end. }
        apply (proj1 (proj1 IHteq (scons (fun w => V r2 A w) r1) (scons (fun w => V r2 A w) r2) HgR1 HgR2 HW1 HW Hal' v)).
        apply (proj2 (V_tshift0 B v HgR1)). exact HB.
      * intros (R & HReq & HC).
        assert (HgR2: goodr (scons R r2)). { intros [|n0] w0 Hw0; simpl in Hw0; [exact (@V_value A r2 w0 Hg2 (proj1 (HReq w0) Hw0)) | apply (Hg2 n0 w0 Hw0)]. }
        assert (HgR1: goodr (scons R r1)). { intros [|n0] w0 Hw0; simpl in Hw0; [exact (@V_value A r2 w0 Hg2 (proj1 (HReq w0) Hw0)) | apply (Hg1 n0 w0 Hw0)]. }
        assert (HW: Vp (scons R r2) (T2 &= A)).
        { simpl. split.
          - eapply Vp_ext_imp; [ | exact HV2 ]. intro k; reflexivity.
          - intro w. simpl. rewrite (HReq w). apply V_ext. intro k; reflexivity. }
        assert (HW1: Vp (scons R r1) (T1 &s)).
        { simpl. eapply Vp_ext_imp; [ intro k; unfold stail, scons; reflexivity | exact HV1 ]. }
        assert (Hal': Ralign (scons R r1) (scons R r2) (T1 &s) (T2 &= A)).
        { intros X HcX HcY w. inversion HcX; subst; inversion HcY; subst; simpl. match goal with HX : check T1 ?a, HY : check T2 ?a |- _ => apply (Hal a HX HY w) end. }
        apply (proj1 (V_tshift0 B v HgR1)).
        apply (proj2 (proj1 IHteq (scons R r1) (scons R r2) HgR1 HgR2 HW1 HW Hal' v)). exact HC.
    + intros HlA HlB; solve [ inversion HlA | inversion HlB ].
    + intros HlA HlB; solve [ inversion HlA | inversion HlB ].
  (* eq_top *)
  - split; [| split].
    + intros r1 r2 Hg1 Hg2 HV1 HV2 Hal v. simpl. tauto.
    + intros _ _ r1 r2 Hg1 Hg2 HV1 HV2 Hal r1' E Hgr1' HE Hcond.
      exists r2. simpl in HE; subst E. splits.
      * exact Hg2.
      * reflexivity.
      * intros k w. rewrite Nat.add_0_r. tauto.
      * intros X HcX HcY w. specialize (Hcond X w). rewrite Nat.add_0_r in Hcond.
        rewrite Hcond. exact (Hal X HcX HcY w).
    + intros _ _ r1 r2 Hg1 Hg2 HV1 HV2 Hal r2' E Hgr2' HE Hcond.
      exists r1. simpl in HE; subst E. splits.
      * exact Hg1.
      * reflexivity.
      * intros k w. rewrite Nat.add_0_r. tauto.
      * intros X HcX HcY w. specialize (Hcond X w). rewrite Nat.add_0_r in Hcond.
        rewrite Hcond. exact (Hal X HcX HcY w).
  (* eq_and *)
  - split; [| split].
    + intros r1 r2 Hg1 Hg2 HV1 HV2 Hal v. destruct m.
      * simpl. split.
        -- intros (E & w & r1' & Heqv & Hgr1' & HE & Hcond1 & HA).
           destruct (proj1 (proj2 IHteq1) H0 H1 r1 r2 Hg1 Hg2 HV1 HV2 Hal r1' E Hgr1' HE Hcond1)
             as (r2' & Hgr2' & HE2 & Hcond2 & Hal').
           assert (HP1 : Vp r1' (T1 +++ T3)).
           { apply Vp_concat; [ exact H0 | | exact (Vc_Vp _ _ _ HE) ].
             eapply Vp_ext_iff_imp; [ | exact HV1 ]. intros k z. unfold sdrop. symmetry. apply Hcond1. }
           assert (HP2 : Vp r2' (T2 +++ T4)).
           { apply Vp_concat; [ exact H1 | | exact (Vc_Vp _ _ _ HE2) ].
             eapply Vp_ext_iff_imp; [ | exact HV2 ]. intros k z. unfold sdrop. symmetry. apply Hcond2. }
           exists E, w, r2'. splits; [ exact Heqv | exact Hgr2' | exact HE2 | exact Hcond2 | ].
           apply (proj1 (proj1 IHteq2 r1' r2' Hgr1' Hgr2' HP1 HP2 Hal' w)). exact HA.
        -- intros (E & w & r2' & Heqv & Hgr2' & HE2 & Hcond2 & HB).
           destruct (proj2 (proj2 IHteq1) H0 H1 r1 r2 Hg1 Hg2 HV1 HV2 Hal r2' E Hgr2' HE2 Hcond2)
             as (r1' & Hgr1' & HE1 & Hcond1 & Hal').
           assert (HP1 : Vp r1' (T1 +++ T3)).
           { apply Vp_concat; [ exact H0 | | exact (Vc_Vp _ _ _ HE1) ].
             eapply Vp_ext_iff_imp; [ | exact HV1 ]. intros k z. unfold sdrop. symmetry. apply Hcond1. }
           assert (HP2 : Vp r2' (T2 +++ T4)).
           { apply Vp_concat; [ exact H1 | | exact (Vc_Vp _ _ _ HE2) ].
             eapply Vp_ext_iff_imp; [ | exact HV2 ]. intros k z. unfold sdrop. symmetry. apply Hcond2. }
           exists E, w, r1'. splits; [ exact Heqv | exact Hgr1' | exact HE1 | exact Hcond1 | ].
           apply (proj2 (proj1 IHteq2 r1' r2' Hgr1' Hgr2' HP1 HP2 Hal' w)). exact HB.
      * simpl. split.
        -- intros (r1' & Hgr1' & HE & Hcond1).
           destruct (proj1 (proj2 IHteq1) H0 H1 r1 r2 Hg1 Hg2 HV1 HV2 Hal r1' v Hgr1' HE Hcond1)
             as (r2' & Hgr2' & HE2 & Hcond2 & Hal').
           exists r2'. splits; [ exact Hgr2' | exact HE2 | exact Hcond2 ].
        -- intros (r2' & Hgr2' & HE2 & Hcond2).
           destruct (proj2 (proj2 IHteq1) H0 H1 r1 r2 Hg1 Hg2 HV1 HV2 Hal r2' v Hgr2' HE2 Hcond2)
             as (r1' & Hgr1' & HE1 & Hcond1 & Hal').
           exists r1'. splits; [ exact Hgr1' | exact HE1 | exact Hcond1 ].
    + intros HlA HlB r1 r2 Hg1 Hg2 HV1 HV2 Hal r1' E Hgr1' HE Hcond.
      assert (HlT3 : lshape T3) by (inversion HlA; subst; assumption).
      assert (HlT4 : lshape T4) by (inversion HlB; subst; assumption).
      destruct m.
      * (* non *)
        assert (HkA : keyLen (T3 & A) = keyLen T3) by reflexivity.
        assert (HkB : keyLen (T4 & B) = keyLen T4) by reflexivity.
        assert (Hcat3 : (T1 +++ (T3 & A)) = ((T1 +++ T3) & A)) by (destruct T3; reflexivity).
        assert (Hcat4 : (T2 +++ (T4 & B)) = ((T2 +++ T4) & B)) by (destruct T4; reflexivity).
        simpl in HE. destruct HE as (E0 & w & HEeq & HET3 & HAw).
        rewrite HkA in Hcond.
        destruct (proj1 (proj2 IHteq1) HlT3 HlT4 r1 r2 Hg1 Hg2 HV1 HV2 Hal r1' E0 Hgr1' HET3 Hcond)
          as (r2' & Hgr2' & HET4 & Hcond2 & Hal').
        assert (HP1 : Vp r1' (T1 +++ T3)).
        { apply Vp_concat; [ exact HlT3 | | exact (Vc_Vp _ _ _ HET3) ].
          eapply Vp_ext_iff_imp; [ | exact HV1 ]. intros k z. unfold sdrop. symmetry. apply Hcond. }
        assert (HP2 : Vp r2' (T2 +++ T4)).
        { apply Vp_concat; [ exact HlT4 | | exact (Vc_Vp _ _ _ HET4) ].
          eapply Vp_ext_iff_imp; [ | exact HV2 ]. intros k z. unfold sdrop. symmetry. apply Hcond2. }
        assert (HBw : V r2' B w).
        { apply (proj1 (proj1 IHteq2 r1' r2' Hgr1' Hgr2' HP1 HP2 Hal' w)). exact HAw. }
        exists r2'. splits.
        -- exact Hgr2'.
        -- simpl. exists E0, w. split; [ exact HEeq | split; [exact HET4 | exact HBw] ].
        -- rewrite HkB. exact Hcond2.
        -- rewrite Hcat3, Hcat4. intros X HcX HcY w0.
           inversion HcX; subst. inversion HcY; subst.
           match goal with HX : check (T1 +++ T3) ?a, HY : check (T2 +++ T4) ?a |- _ =>
             exact (Hal' a HX HY w0) end.
      * (* rt: T3 &= A *)
        assert (HkA : keyLen (T3 &= A) = S (keyLen T3)) by reflexivity.
        assert (HkB : keyLen (T4 &= B) = S (keyLen T4)) by reflexivity.
        assert (Hcat3 : (T1 +++ (T3 &= A)) = ((T1 +++ T3) &= A)) by (destruct T3; reflexivity).
        assert (Hcat4 : (T2 +++ (T4 &= B)) = ((T2 +++ T4) &= B)) by (destruct T4; reflexivity).
        simpl in HE. destruct HE as (HET3 & Hpin).
        assert (Hcih : forall k w, (stail r1') (k + keyLen T3) w <-> r1 k w).
        { intros k w. unfold stail. specialize (Hcond k w). rewrite HkA in Hcond.
          rewrite <- Nat.add_succ_r. exact Hcond. }
        destruct (proj1 (proj2 IHteq1) HlT3 HlT4 r1 r2 Hg1 Hg2 HV1 HV2 Hal (stail r1') E
                    (goodr_stail Hgr1') HET3 Hcih)
          as (r2'0 & Hgr2'0 & HET4 & Hcond2'0 & Hal'0).
        exists (scons (fun w => V r2'0 B w) r2'0). splits.
        -- apply goodr_scons; [ intros w Hw; exact (@V_value B r2'0 w Hgr2'0 Hw) | exact Hgr2'0 ].
        -- simpl. split.
           ++ eapply Vc_ext_imp; [ intro k; unfold stail, scons; reflexivity | exact HET4 ].
           ++ intro w. unfold scons, stail. reflexivity.
        -- intros k w. rewrite HkB. simpl. rewrite Nat.add_succ_r. exact (Hcond2'0 k w).
        -- rewrite Hcat3, Hcat4. intros X HcX HcY w0.
           inversion HcX; subst. inversion HcY; subst.
           match goal with HX : check (T1 +++ T3) ?a, HY : check (T2 +++ T4) ?a |- _ =>
             generalize (Hal'0 a HX HY w0) end. unfold stail, scons. simpl. tauto.
    + intros HlA HlB r1 r2 Hg1 Hg2 HV1 HV2 Hal r2' E Hgr2' HE Hcond.
      assert (HlT3 : lshape T3) by (inversion HlA; subst; assumption).
      assert (HlT4 : lshape T4) by (inversion HlB; subst; assumption).
      destruct m.
      * (* non *)
        assert (HkA : keyLen (T3 & A) = keyLen T3) by reflexivity.
        assert (HkB : keyLen (T4 & B) = keyLen T4) by reflexivity.
        assert (Hcat3 : (T1 +++ (T3 & A)) = ((T1 +++ T3) & A)) by (destruct T3; reflexivity).
        assert (Hcat4 : (T2 +++ (T4 & B)) = ((T2 +++ T4) & B)) by (destruct T4; reflexivity).
        simpl in HE. destruct HE as (E0 & w & HEeq & HET4 & HBw).
        rewrite HkB in Hcond.
        destruct (proj2 (proj2 IHteq1) HlT3 HlT4 r1 r2 Hg1 Hg2 HV1 HV2 Hal r2' E0 Hgr2' HET4 Hcond)
          as (r1' & Hgr1' & HET3 & Hcond1 & Hal').
        assert (HP1 : Vp r1' (T1 +++ T3)).
        { apply Vp_concat; [ exact HlT3 | | exact (Vc_Vp _ _ _ HET3) ].
          eapply Vp_ext_iff_imp; [ | exact HV1 ]. intros k z. unfold sdrop. symmetry. apply Hcond1. }
        assert (HP2 : Vp r2' (T2 +++ T4)).
        { apply Vp_concat; [ exact HlT4 | | exact (Vc_Vp _ _ _ HET4) ].
          eapply Vp_ext_iff_imp; [ | exact HV2 ]. intros k z. unfold sdrop. symmetry. apply Hcond. }
        assert (HAw : V r1' A w).
        { apply (proj2 (proj1 IHteq2 r1' r2' Hgr1' Hgr2' HP1 HP2 Hal' w)). exact HBw. }
        exists r1'. splits.
        -- exact Hgr1'.
        -- simpl. exists E0, w. split; [ exact HEeq | split; [exact HET3 | exact HAw] ].
        -- rewrite HkA. exact Hcond1.
        -- rewrite Hcat3, Hcat4. intros X HcX HcY w0.
           inversion HcX; subst. inversion HcY; subst.
           match goal with HX : check (T1 +++ T3) ?a, HY : check (T2 +++ T4) ?a |- _ =>
             exact (Hal' a HX HY w0) end.
      * (* rt: T4 &= B *)
        assert (HkA : keyLen (T3 &= A) = S (keyLen T3)) by reflexivity.
        assert (HkB : keyLen (T4 &= B) = S (keyLen T4)) by reflexivity.
        assert (Hcat3 : (T1 +++ (T3 &= A)) = ((T1 +++ T3) &= A)) by (destruct T3; reflexivity).
        assert (Hcat4 : (T2 +++ (T4 &= B)) = ((T2 +++ T4) &= B)) by (destruct T4; reflexivity).
        simpl in HE. destruct HE as (HET4 & Hpin).
        assert (Hcih : forall k w, (stail r2') (k + keyLen T4) w <-> r2 k w).
        { intros k w. unfold stail. specialize (Hcond k w). rewrite HkB in Hcond.
          rewrite <- Nat.add_succ_r. exact Hcond. }
        destruct (proj2 (proj2 IHteq1) HlT3 HlT4 r1 r2 Hg1 Hg2 HV1 HV2 Hal (stail r2') E
                    (goodr_stail Hgr2') HET4 Hcih)
          as (r1'0 & Hgr1'0 & HET3 & Hcond1'0 & Hal'0).
        exists (scons (fun w => V r1'0 A w) r1'0). splits.
        -- apply goodr_scons; [ intros w Hw; exact (@V_value A r1'0 w Hgr1'0 Hw) | exact Hgr1'0 ].
        -- simpl. split.
           ++ eapply Vc_ext_imp; [ intro k; unfold stail, scons; reflexivity | exact HET3 ].
           ++ intro w. unfold scons, stail. reflexivity.
        -- intros k w. rewrite HkA. simpl. rewrite Nat.add_succ_r. exact (Hcond1'0 k w).
        -- rewrite Hcat3, Hcat4. intros X HcX HcY w0.
           inversion HcX; subst. inversion HcY; subst.
           match goal with HX : check (T1 +++ T3) ?a, HY : check (T2 +++ T4) ?a |- _ =>
             generalize (Hal'0 a HX HY w0) end. unfold stail, scons. simpl. tauto.
  (* eq_ands *)
  - split; [| split].
    + intros r1 r2 Hg1 Hg2 HV1 HV2 Hal v. simpl. split.
      * intros (r1' & Hgr1' & HET3 & Hcond1).
        destruct (proj1 (proj2 IHteq) H0 H1 r1 r2 Hg1 Hg2 HV1 HV2 Hal r1' v Hgr1' HET3 Hcond1)
          as (r2' & Hgr2' & HET4 & Hcond2 & Hal').
        exists r2'. splits; [ exact Hgr2' | exact HET4 | exact Hcond2 ].
      * intros (r2' & Hgr2' & HET4 & Hcond2).
        destruct (proj2 (proj2 IHteq) H0 H1 r1 r2 Hg1 Hg2 HV1 HV2 Hal r2' v Hgr2' HET4 Hcond2)
          as (r1' & Hgr1' & HET3 & Hcond1 & Hal').
        exists r1'. splits; [ exact Hgr1' | exact HET3 | exact Hcond1 ].
    + intros _ _ r1 r2 Hg1 Hg2 HV1 HV2 Hal r1' E Hgr1' HE Hcond.
      simpl in HE.
      assert (Hcih : forall k w, (stail r1') (k + keyLen T3) w <-> r1 k w).
      { intros k w. unfold stail. specialize (Hcond k w). simpl in Hcond.
        rewrite <- Nat.add_succ_r. exact Hcond. }
      destruct (proj1 (proj2 IHteq) H0 H1 r1 r2 Hg1 Hg2 HV1 HV2 Hal (stail r1') E
                  (goodr_stail Hgr1') HE Hcih)
        as (r2'0 & Hgr2'0 & HET4 & Hcond2'0 & Hal'0).
      exists (scons (r1' 0) r2'0). splits.
      * apply goodr_scons; [ intros w Hw; exact (Hgr1' 0 w Hw) | exact Hgr2'0 ].
      * simpl. eapply Vc_ext_imp; [ intro k; unfold stail, scons; reflexivity | exact HET4 ].
      * intros k w. simpl. rewrite Nat.add_succ_r. exact (Hcond2'0 k w).
      * assert (Hcat3 : (T1 +++ (T3 &s)) = ((T1 +++ T3) &s)) by (destruct T3; reflexivity).
        assert (Hcat4 : (T2 +++ (T4 &s)) = ((T2 +++ T4) &s)) by (destruct T4; reflexivity).
        rewrite Hcat3, Hcat4.
        intros X HcX HcY w.
        inversion HcX; subst; inversion HcY; subst; simpl;
          try (unfold scons; tauto);
          match goal with
          | HX : check (T1 +++ T3) ?a, HY : check (T2 +++ T4) ?a |- _ =>
              generalize (Hal'0 a HX HY w); unfold stail, scons; simpl; tauto
          end.
    + intros _ _ r1 r2 Hg1 Hg2 HV1 HV2 Hal r2' E Hgr2' HE Hcond.
      simpl in HE.
      assert (Hcih : forall k w, (stail r2') (k + keyLen T4) w <-> r2 k w).
      { intros k w. unfold stail. specialize (Hcond k w). simpl in Hcond.
        rewrite <- Nat.add_succ_r. exact Hcond. }
      destruct (proj2 (proj2 IHteq) H0 H1 r1 r2 Hg1 Hg2 HV1 HV2 Hal (stail r2') E
                  (goodr_stail Hgr2') HE Hcih)
        as (r1'0 & Hgr1'0 & HET3 & Hcond1'0 & Hal'0).
      exists (scons (r2' 0) r1'0). splits.
      * apply goodr_scons; [ intros w Hw; exact (Hgr2' 0 w Hw) | exact Hgr1'0 ].
      * simpl. eapply Vc_ext_imp; [ intro k; unfold stail, scons; reflexivity | exact HET3 ].
      * intros k w. simpl. rewrite Nat.add_succ_r. exact (Hcond1'0 k w).
      * assert (Hcat3 : (T1 +++ (T3 &s)) = ((T1 +++ T3) &s)) by (destruct T3; reflexivity).
        assert (Hcat4 : (T2 +++ (T4 &s)) = ((T2 +++ T4) &s)) by (destruct T4; reflexivity).
        rewrite Hcat3, Hcat4.
        intros X HcX HcY w.
        inversion HcX; subst; inversion HcY; subst; simpl;
          try (unfold scons; tauto);
          match goal with
          | HX : check (T1 +++ T3) ?a, HY : check (T2 +++ T4) ?a |- _ =>
              generalize (Hal'0 a HX HY w); unfold stail, scons; simpl; tauto
          end.
  (* eq_rcd *)
  - split; [| split].
    + intros r1 r2 Hg1 Hg2 HV1 HV2 Hal v. simpl. split.
      * intros (v'&Heq&HA). exists v'. split; [exact Heq | apply (proj1 (proj1 IHteq r1 r2 Hg1 Hg2 HV1 HV2 Hal v')); exact HA].
      * intros (v'&Heq&HA). exists v'. split; [exact Heq | apply (proj2 (proj1 IHteq r1 r2 Hg1 Hg2 HV1 HV2 Hal v')); exact HA].
    + intros HlA HlB; solve [ inversion HlA | inversion HlB ].
    + intros HlA HlB; solve [ inversion HlA | inversion HlB ].
Qed.

Lemma comp_eq_gen : forall T1 A B T2, teq T1 A B T2 ->
  forall r1 r2, goodr r1 -> goodr r2 -> Vp r1 T1 -> Vp r2 T2 ->
  Ralign r1 r2 T1 T2 -> forall v, V r1 A v <-> V r2 B v.
Proof. intros T1 A B T2 H. exact (proj1 (comp_eq_combined H)). Qed.

Lemma comp_eq : forall T e A B, sem T e A -> teq T A B T -> sem T e B.
Proof.
  intros T e A B Hsem Hteq r g Hg HV.
  destruct (Hsem r g Hg HV) as (v' & Hms & Hvv & HVA).
  exists v'. split; [exact Hms | split; [exact Hvv | ]].

  assert (HRal : Ralign r r T T).
  { intros X HcX HcY w. tauto. }
  apply (proj1 (comp_eq_gen Hteq Hg Hg (Vc_Vp _ _ _ HV) (Vc_Vp _ _ _ HV) HRal v')). exact HVA.
Qed.

(* ===================== env-type intro / projection ===================== *)

(* combine realizations over +++ : T3 is low, T1 is high (shifted by keyLen T3). *)
Lemma V_concat_realize : forall T3, lshape T3 -> forall r T1 g1 E,
  Vc (sdrop (keyLen T3) r) T1 g1 -> Vc r T3 E -> Vc r (T1 +++ T3) (g1 ++- E).
Proof.
  induction 1; intros r T1 g1 E HV1 HE; simpl in HE.
  - subst E. simpl. eapply Vc_ext_imp; [ | exact HV1]. intro n. unfold sdrop. f_equal. simpl. lia.
  - assert (Hmc: (T1 +++ (and T m A)) = (and (T1 +++ T) m A)) by (destruct T; reflexivity).
    rewrite Hmc. destruct m.
    + destruct HE as (E0 & w & Heq & HET & HW); subst E. simpl.
      exists (g1 ++- E0), w.
      split; [destruct E0; reflexivity | split; [apply (IHlshape r T1 g1 E0 HV1 HET) | exact HW]].
    + destruct HE as (HET & Hpin).
      assert (HV1' : Vc (sdrop (keyLen T) (stail r)) T1 g1).
      { eapply Vc_ext_imp; [ | exact HV1]. intro n. unfold sdrop, stail. f_equal. simpl. lia. }
      split; [ apply (IHlshape (stail r) T1 g1 E HV1' HET) | exact Hpin ].
  - assert (Hmc: (T1 +++ (T &s)) = ((T1 +++ T) &s)) by (destruct T; reflexivity).
    rewrite Hmc.
    assert (HV1' : Vc (sdrop (keyLen T) (stail r)) T1 g1).
    { eapply Vc_ext_imp; [ | exact HV1]. intro n. unfold sdrop, stail. f_equal. simpl. lia. }
    apply (IHlshape (stail r) T1 g1 E HV1' HE).
Qed.

(* env-type value intro: appending a value binding realizes T1 & A. *)
Lemma comp_conse : forall T E T1 e A,
  sem T E T1 -> lshape T1 -> sem (T +++ T1) e A -> sem T (E ,, e) (T1 & A).
Proof.
  unfold sem. introv Hs1 Hl Hs2 Hg HV.
  assert (value g) as Hvg by (eapply Vc_value; eauto).
  destruct (Hs1 r g Hg HV) as (E0 & HmE & HvE0 & HVT1).
  destruct (@V_to_Vc T1 r E0 Hl Hg HVT1) as (r1' & Hgr1' & Hcond1 & HVc1).
  assert (HVcT : Vc (sdrop (keyLen T1) r1') T g).
  { apply (Vc_ext_iff_imp T r (sdrop (keyLen T1) r1') g);
      [ intros k z; unfold sdrop; symmetry; apply Hcond1 | exact HV ]. }
  assert (HVcat : Vc r1' (T +++ T1) (g ++- E0)).
  { apply V_concat_realize; [ exact Hl | exact HVcT | exact HVc1 ]. }
  destruct (Hs2 r1' (g ++- E0) Hgr1' HVcat) as (w & Hmw & Hvw & HVAw).
  exists (E0 ,, w). splits.
  - eapply mstep_trans; [ apply mstep_mrgl; [ exact Hvg | exact HmE ] | ].
    apply mstep_mrgr; [ exact Hvg | exact HvE0 | exact Hmw ].
  - constructor; [ exact HvE0 | exact Hvw ].
  - simpl. exists E0, w, r1'. splits; [ reflexivity | exact Hgr1' | exact HVc1 | exact Hcond1 | exact HVAw ].
Qed.

(* opening a field type over its prefix preserves V *)
Lemma V_mopen : forall T A B, mopen T A B ->
  forall r g v, Vc r T g -> (V r A v <-> V (sdrop (keyLen T) r) B v).
Proof.
  intros T A B Hm. induction Hm; intros r g v HVT; simpl.
  - apply V_ext. intro n. unfold sdrop. f_equal. lia.
  - simpl in HVT. destruct HVT as (E&w&Heq&HET&Hw). exact (IHHm r E v HET).
  - simpl in HVT. destruct HVT as (HET & Hpin).
    specialize (IHHm (stail r) g v HET) as IH.
    assert (Henv : V (sdrop (keyLen T) (stail r)) B v <-> V (sdrop (S (keyLen T)) r) B v).
    { apply V_ext. intro n. unfold sdrop, stail. f_equal. lia. }
    assert (Hb : V r A v <-> V (stail r) (mani C A) v).
    { simpl. split.
      - intro Hv. exists (r 0). split.
        + exact Hpin.
        + eapply V_ext_imp; [ | exact Hv ]. intro n. destruct n; unfold scons, stail; reflexivity.
      - intros (R & Hiff & HA). eapply V_ext_iff_imp; [ | exact HA ].
        intros n w. destruct n.
        + split; intro H; [ apply (proj2 (Hpin w)); apply (proj1 (Hiff w)); exact H
                          | apply (proj2 (Hiff w)); apply (proj1 (Hpin w)); exact H ].
        + unfold scons, stail. tauto. }
    rewrite Hb. rewrite IH. exact Henv.
Qed.

(* a projectable env type, well-formed under some context, is an lshape. *)
Lemma rlk_wft_lshape : forall T1 l A, rlk T1 l A ->
  forall T0, wft T0 T1 -> lshape T1.
Proof.
  introv Hr. induction Hr; introv Hw; unfold wft in Hw; inverts Hw;
    match goal with H : lshape _ |- _ => apply lsh_evar; exact H end.
Qed.

(* Vc-based record projection. *)
Lemma rproj_lookup_c : forall T1 l A, rlk T1 l A ->
  forall T0, wft T0 T1 ->
  forall r g, goodr r -> Vc r T1 g -> exists v2, rlookupv g l v2 /\ V (sdrop (keyLen T1) r) A v2.
Proof.
  intros T1 l A Hrlk. induction Hrlk; introv Hw; unfold wft in Hw; introv Hg HV.
  - simpl in HV. destruct HV as (E & w & Heq & HET1 & Hw'). subst g.
    simpl in Hw'. destruct Hw' as (w' & Heqw & HAw'). subst w.
    exists w'. split.
    + apply rvlzero.
    + assert (Hk : keyLen (T1 & rcd l A) = keyLen T1) by reflexivity. rewrite Hk.
      apply (proj1 (V_mopen H0 r E w' HET1)). exact HAw'.
  - simpl in HV. destruct HV as (E & w & Heq & HET1 & Hw'). subst g.
    destruct Hw' as (v' & Heqw & HAv'). subst w.
    inverts Hw. destruct (IHHrlk T0 ltac:(unfold wft; eassumption) r E Hg HET1) as (v2 & Hlk & HBv2).
    exists v2. split.
    + apply rvl_left; [ exact Hlk | exact H ].
    + assert (Hk : keyLen (T1 & rcd l1 A) = keyLen T1) by reflexivity. rewrite Hk. exact HBv2.
  - simpl in HV. destruct HV as (E & w & Heq & HET1 & Hw'). subst g.
    inverts Hw.
    assert (HwftT2 : wft (T0 +++ T1) T2) by (unfold wft; eassumption).
    assert (Hsh2 : lshape T2) by (eapply rlk_wft_lshape; eauto).
    destruct (@V_to_Vc T2 r w Hsh2 Hg Hw') as (r'' & Hgr'' & Hcond'' & HVc2).
    destruct (IHHrlk (T0 +++ T1) HwftT2 r'' w Hgr'' HVc2) as (v2 & Hlk & HBv2).
    exists v2. split.
    + apply rvl_right. exact Hlk.
    + assert (HBr : V r B v2).
      { eapply V_ext_iff_imp; [ | exact HBv2 ]. intros n z. unfold sdrop. apply Hcond''. }
      assert (Hk : keyLen (T1 & T2) = keyLen T1) by reflexivity. rewrite Hk.
      apply (proj1 (V_mopen H0 r E v2 HET1)). exact HBr.
  - simpl in HV. destruct HV as (HET1 & Hpin).
    inverts Hw. destruct (IHHrlk T0 ltac:(unfold wft; eassumption) (stail r) g (goodr_stail Hg) HET1) as (v2 & Hlk & HBv2).
    exists v2. split.
    + exact Hlk.
    + assert (Hk : keyLen (T1 &= A) = S (keyLen T1)) by reflexivity. rewrite Hk.
      eapply V_ext_imp; [ | exact HBv2 ]. intro n. unfold sdrop, stail. f_equal. lia.
Qed.

Lemma rproj_lookup : forall T1 l A, rlk T1 l A -> forall T0, wft T0 T1 ->
  forall r g, goodr r -> V r T1 g -> exists v2, rlookupv g l v2 /\ V r A v2.
Proof.
  intros T1 l A Hrlk T0 Hwft r g Hg HV.
  assert (Hsh : lshape T1) by (eapply rlk_wft_lshape; eauto).
  destruct (@V_to_Vc T1 r g Hsh Hg HV) as (r' & Hgr' & Hcond' & HVc).
  destruct (@rproj_lookup_c T1 l A Hrlk T0 Hwft r' g Hgr' HVc) as (v2 & Hlk & HAv2).
  exists v2. split; [ exact Hlk | ].
  eapply V_ext_iff_imp; [ | exact HAv2 ]. intros n z. unfold sdrop. apply Hcond'.
Qed.

Lemma comp_proj : forall T e T1 l A, sem T e T1 -> rlk T1 l A -> wft T T1 -> sem T (rproj e l) A.
Proof.
  unfold sem. introv Hs Hrlk Hwft Hg HV.
  assert (value g) as Hvg by (eapply Vc_value; eauto).
  destruct (Hs r g Hg HV) as (dv&Hm&Hvdv&HVT1).
  assert (exists v2, rlookupv dv l v2 /\ V r A v2) as (v2&Hl&HA)
    by (eapply rproj_lookup; eauto).
  exists v2. splits.
  - eapply mstep_trans; [ apply mstep_proj; eauto | ].
    eapply mstep_step; [ apply srprojv; eauto | apply mstep_base; auto ].
  - eapply V_value; eauto.
  - exact HA.
Qed.

(* ---- t_star : phantom &s intro ---- *)
Lemma comp_star : forall T e A, sem T e A -> lshape A -> sem T e (A &s).
Proof.
  unfold sem. introv Hs Hl Hg HV.
  destruct (Hs r g Hg HV) as (v' & Hm & Hvv & HVA).
  exists v'. splits; auto.
  simpl. destruct (@V_to_Vc A r v' Hl Hg HVA) as (r' & Hgr' & Hcond & HVc).
  exists r'. splits; [ exact Hgr' | exact HVc | exact Hcond ].
Qed.

(* ---- t_mani : phantom &= intro ---- *)
Lemma comp_mani : forall T e A B, sem T e A -> lshape A -> sem T e (A &= B).
Proof.
  unfold sem. introv Hs Hl Hg HV.
  destruct (Hs r g Hg HV) as (v' & Hm & Hvv & HVA).
  exists v'. splits; auto.
  simpl. destruct (@V_to_Vc A r v' Hl Hg HVA) as (r' & Hgr' & Hcond & HVc).
  exists r'. splits; [ exact Hgr' | exact HVc | exact Hcond ].
Qed.

(* ---- The fundamental theorem. --- *)
Theorem sem_sound : forall T e A, has_type T e A -> sem T e A.
Proof.
  induction 1;
    eauto using comp_int, comp_var, comp_lam, comp_app, comp_gen, comp_tapp,
                comp_eq, comp_unit, comp_rec, comp_star, comp_mani.
  - (* t_box *) eapply comp_box; eauto.
    eapply wfe_lshape, (typ_wfe H0).
  - (* t_clos *) eapply comp_clos; eauto.
    eapply wfe_lshape, wfe_inv, (typ_wfe H0).
  - (* lt_conse *) eapply comp_conse; eauto.
  - (* trproj *) eapply comp_proj; eauto.
    eapply typ_ans_wft; eauto.
Qed.

Corollary normalization : forall e A,
  has_type top e A -> exists v', mstep unit e v' /\ value v'.
Proof.
  introv Ht. apply sem_sound in Ht.
  destruct (Ht (fun _ _ => False) unit) as (v'&Hm&Hvv&_).
  - unfold goodr. intros n w HF. destruct HF.
  - simpl. reflexivity.
  - exists v'. auto.
Qed.
