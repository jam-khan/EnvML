Require Import LibTactics.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
Require Import Stdlib.Lists.List.
From Stdlib Require Import Strings.String.
Require Import Setoid.
Require Export Safety.
Import ListNotations.
Set Implicit Arguments.

(* A semantic type = a predicate on (closed) values: a reducibility candidate. *)
Definition cand := exp -> Prop.
(* Semantic environment: one candidate per type variable (de Bruijn). *)
Definition senv := nat -> cand.
Definition scons (R:cand) (r:senv) : senv :=
  fun n => match n with 0 => R | S m => r m end.
Definition stail (r:senv) : senv := fun n => r (S n).
Definition sdrop (k:nat) (r:senv) : senv := fun n => r (n + k).

(* r is "value-valued": a genuine reducibility-candidate environment. *)
Definition goodr (r:senv) := forall n w, r n w -> value w.

(* THREE mutually-defined relations (all structurally recursive on the type):

   V  r A v  -- TYPE interpretation: A is a type formed in a context whose
               realization is the AMBIENT env r.  For env types (and/&=/&s),
               A's own internal type bindings are NOT slots of r: the clause
               existentially provides a COMBINED env r' whose low keyLen
               slots are the prefix's exported bindings and whose high part
               is r (the cond).  The prefix is realized by Vc r' (role-1),
               so the binding A1's low de Bruijn refs hit EXACTLY the
               prefix's exported slots (no duplication) -- this is what makes
               weakening (V_tshift, sins at ambient depth d) provable.

   Vc r T g  -- CONTEXT realization (role-1): r's low slots [0,keyLen T) ARE
               T's own type bindings (slot 0 = innermost/rightmost), peeled
               via stail exactly as in the original flat clauses; a type
               formed in context T is then read by V at the SAME r.
               Vc is a relation on ENVIRONMENTS ONLY: its four cases mirror
               lshape exactly, and every non-environment constructor maps to
               False.  The bridge V_to_Vc therefore carries an [lshape T]
               precondition -- always available at its call sites, since a
               box's frame type is well-formed (typ_wfe -> wfe_lshape).

   Vp r T   -- PIN respect (witness-free); True off environments.  See the
               comment at its definition below.                            *)
Fixpoint V (r:senv) (A:typ) (v:exp) {struct A} : Prop :=
  match A with
  | int          => exists i, v = lit i
  | tvar n       => r n v
  | arr A1 B     => exists E e, v = clos E e /\ value E /\
                    (forall v2, V r A1 v2 ->
                       exists v', mstep (E ,, v2) e v' /\ value v' /\ V r B v')
  | all B        => exists E e, v = bclos E e /\ value E /\
                    (forall (R:cand) (C F:typ), (forall w, R w -> value w) -> exists v',
                       mstep (E ;; boxt F C) e v' /\ value v' /\ V (scons R r) B v')
  | boxt T0 A1   => exists rE, goodr rE /\ Vp rE T0 /\ V rE A1 v
                    (* realizer-FREE: the body is read under SOME good env that respects
                       the frame's manifest pins (Vp); no frame inhabitation is demanded.
                       Box bodies are rigid (wft_box_rigid), so pins + boundedness are
                       all they consume; r-independent by construction (tshift-stable). *)
  | mani C B     => exists R:cand,           (* manifest [C]B: type var pinned to V[[C]] *)
                      (forall w, R w <-> V r C w) /\ V (scons R r) B v
  | rcd l A1     => exists v', v = rec l v' /\ V r A1 v'
  | top          => v = unit
  | and T1 non A1 => exists E w r', v = (E ,, w) /\ goodr r' /\ Vc r' T1 E /\
                      (forall n w0, r' (n + keyLen T1) w0 <-> r n w0) /\ V r' A1 w
  | and T1 rt  A1 => exists E T0 B0 r', v = (E ;; boxt T0 B0) /\ goodr r' /\ Vc r' T1 E /\
                      (forall n w0, r' (n + keyLen T1) w0 <-> r n w0)
  | ands T1       => exists E T0 B0 r', v = (E ;; boxt T0 B0) /\ goodr r' /\ Vc r' T1 E /\
                      (forall n w0, r' (n + keyLen T1) w0 <-> r n w0)
  end
with Vc (r:senv) (T:typ) (g:exp) {struct T} : Prop :=
  match T with
  | top           => g = unit
  | and T1 non A1 => exists E w, g = (E ,, w) /\ Vc r T1 E /\ V r A1 w
  | and T1 rt  A1 => exists E T0 B0, g = (E ;; boxt T0 B0) /\ Vc (stail r) T1 E /\
                       (forall w, r 0 w <-> V (stail r) A1 w)        (* &= pins r 0 to A1 *)
  | ands T1       => exists E T0 B0, g = (E ;; boxt T0 B0) /\ Vc (stail r) T1 E  (* &s: r 0 free *)
  | _             => False
  end
(* Vp r T -- PIN respect (role-1, witness-free): r's low slots satisfy exactly the
   manifest (&=) pin equations of T; value-binding inhabitation and abstract slots
   are NOT constrained.  This is the part of context realization that a RIGID type
   formed in T actually reads (rigid tvars are lookt-manifest or forall-bound), and
   unlike full realization it is ALWAYS satisfiable (penv below) -- which is what
   makes the box clause realizer-free.                                            *)
with Vp (r:senv) (T:typ) {struct T} : Prop :=
  match T with
  | and T1 non A1 => Vp r T1
  | and T1 rt  A1 => Vp (stail r) T1 /\ (forall w, r 0 w <-> V (stail r) A1 w)
  | ands T1       => Vp (stail r) T1
  | _             => True
  end.

Lemma goodr_stail : forall r, goodr r -> goodr (stail r).
Proof. unfold goodr, stail. eauto. Qed.

Lemma goodr_scons : forall (R:cand) r,
  (forall w, R w -> value w) -> goodr r -> goodr (scons R r).
Proof. unfold goodr, scons. introv HR Hr. destruct n; eauto. Qed.

(* Every value in the relation is a syntactic value (mutual over V/Vc). *)
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
  - destruct HV as (E&e&Heq&HvE&_); subst; auto.
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
    + destruct HV as (E&T0&B0&r'&Heq&Hgr'&HE&Hcond); subst.
      constructor. eapply (proj2 IHA1); [ exact Hgr' | exact HE ].
  - destruct m.
    + destruct HV as (E&w&Heq&HE&Hw); subst.
      constructor; [ eapply (proj2 IHA1); [exact Hg|exact HE]
                   | eapply (proj1 IHA2); [exact Hg|exact Hw] ].
    + destruct HV as (E&T0&B0&Heq&HE&Hiff); subst.
      constructor. eapply (proj2 IHA1); [ apply goodr_stail; exact Hg | exact HE ].
  - destruct HV as (E&T0&B0&r'&Heq&Hgr'&HE&Hcond); subst.
    constructor. eapply (proj2 IHA1); [ exact Hgr' | exact HE ].
  - destruct HV as (E&T0&B0&Heq&HE); subst.
    constructor. eapply (proj2 IHA1); [ apply goodr_stail; exact Hg | exact HE ].
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
  - destruct HV as (E&e&Hv&HvE&Hf). exists E e. splits; auto. introv HRval.
    destruct (Hf R C F HRval) as (v'&Hm&Hvv&HA1). exists v'. splits; auto.
    eapply (proj1 IHA1); [ apply scons_ext; exact Heq | exact HA1 ].
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
    + destruct HV as (E&T0&B0&r'&Hv&Hgr'&HE&Hcond). exists E T0 B0 r'. splits; auto.
      intros n w0. rewrite (Hcond n w0). rewrite (Heq n). tauto.
  - destruct m.
    + destruct HV as (E&w&Hv&HE&Hw). exists E w. splits; auto.
      * eapply (proj2 IHA1); [ exact Heq | exact HE ].
      * eapply (proj1 IHA2); [ exact Heq | exact Hw ].
    + destruct HV as (E&T0&B0&Hv&HE&Hpin). exists E T0 B0. splits; auto.
      * eapply (proj2 IHA1); [ apply stail_ext; exact Heq | exact HE ].
      * intro w. rewrite <- (Heq 0). rewrite Hpin. split; intro Hw.
        ** eapply (proj1 IHA2); [ apply stail_ext; exact Heq | exact Hw ].
        ** apply (proj1 IHA2 (stail r2) (stail r1) w);
             [ apply stail_ext; intro k; symmetry; apply Heq | exact Hw ].
  - destruct HV as (E&T0&B0&r'&Hv&Hgr'&HE&Hcond). exists E T0 B0 r'. splits; auto.
    intros n w0. rewrite (Hcond n w0). rewrite (Heq n). tauto.
  - destruct HV as (E&T0&B0&Hv&HE). exists E T0 B0. splits; auto.
    eapply (proj2 IHA1); [ apply stail_ext; exact Heq | exact HE ].
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

(* ---- V respects pointwise IFF of candidates (needed for manifest pinning) -- *)
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
  - destruct HV as (E&e&Hv&HvE&Hf). exists E e. splits; auto. introv HRval.
    destruct (Hf R C F HRval) as (v'&Hm&Hvv&HA1). exists v'. splits; auto.
    eapply (proj1 IHA1); [ apply scons_ext_iff; exact Heq | exact HA1 ].
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
    + destruct HV as (E&T0&B0&r'&Hv&Hgr'&HE&Hcond). exists E T0 B0 r'. splits; auto.
      intros n w0. rewrite (Hcond n w0). exact (Heq n w0).
  - destruct m.
    + destruct HV as (E&w&Hv&HE&Hw). exists E w. splits; auto.
      * eapply (proj2 IHA1); [ exact Heq | exact HE ].
      * eapply (proj1 IHA2); [ exact Heq | exact Hw ].
    + destruct HV as (E&T0&B0&Hv&HE&Hpin). exists E T0 B0. splits; auto.
      * eapply (proj2 IHA1); [ apply stail_ext_iff; exact Heq | exact HE ].
      * intro w. rewrite <- (Heq 0 w). rewrite (Hpin w). split; intro Hw.
        ** eapply (proj1 IHA2); [ apply stail_ext_iff; exact Heq | exact Hw ].
        ** apply (proj1 IHA2 (stail r2) (stail r1) w);
             [ apply stail_ext_iff; intros k z; symmetry; apply Heq | exact Hw ].
  - destruct HV as (E&T0&B0&r'&Hv&Hgr'&HE&Hcond). exists E T0 B0 r'. splits; auto.
    intros n w0. rewrite (Hcond n w0). exact (Heq n w0).
  - destruct HV as (E&T0&B0&Hv&HE). exists E T0 B0. splits; auto.
    eapply (proj2 IHA1); [ apply stail_ext_iff; exact Heq | exact HE ].
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
    + destruct HV as (E & T0 & B0 & _ & HE & Hpin).
      split; [ exact (IHA1 (stail r) E HE) | exact Hpin ].
  - destruct HV as (E & T0 & B0 & _ & HE). exact (IHA1 (stail r) E HE).
Qed.

(* canonical pin environment: satisfies exactly T's manifest pins; abstract and
   ambient slots are the empty candidate.  Witnesses that Vp is ALWAYS satisfiable
   (unlike full realization) -- the key to the realizer-free box clause.        *)
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

Lemma sins_scons_eq : forall d (R R':cand) r n,
  scons R' (sins d R r) n = sins (S d) R (scons R' r) n.
Proof.
  intros. destruct n; unfold sins, scons; simpl;
    repeat match goal with
           | [ |- context[lt_eq_lt_dec ?a ?b] ] => destruct (lt_eq_lt_dec a b) as [[?|?]|?]
           end; try lia; auto.
  destruct n; simpl; auto; lia.
Qed.

(* good candidates are preserved by insertion/deletion *)
Lemma goodr_sins : forall d (R:cand) r,
  (forall w, R w -> value w) -> goodr r -> goodr (sins d R r).
Proof.
  introv HR Hg. intros n w Hw. unfold sins in Hw.
  destruct (lt_eq_lt_dec n d) as [[?|?]|?]; eauto.
Qed.

(* deleting a slot (inverse of sins on the env side) *)
Definition sdel (k:nat) (r:senv) : senv :=
  fun m => if lt_dec m k then r m else r (S m).

Lemma goodr_sdel : forall k r, goodr r -> goodr (sdel k r).
Proof.
  introv Hg. intros n w Hw. unfold sdel in Hw. destruct (lt_dec n k); eauto.
Qed.

(* peeling one slot commutes with insertion at a positive depth *)
Lemma stail_sins : forall d (R:cand) r n, stail (sins (S d) R r) n = sins d R (stail r) n.
Proof.
  intros. unfold stail, sins.
  destruct (lt_eq_lt_dec (S n) (S d)) as [[?|?]|?];
    destruct (lt_eq_lt_dec n d) as [[?|?]|?]; try lia; auto.
  destruct n; [ lia | simpl; auto ].
Qed.

(* a combined env r' whose high-(above k) part is r, after inserting R at
   k+d, has high part = the d-insertion of R into r.                        *)
Lemma sins_cond : forall k d (R:cand) r r',
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

(* un-insertion: if r''-high (above k) is the d-insertion of R into r, then
   deleting slot k+d recovers an env whose high part is r ...               *)
Lemma unins_cond : forall k d (R:cand) r r'',
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

(* ... and r'' itself is pointwise-iff the (k+d)-insertion of R into it.    *)
Lemma unins_iff : forall k d (R:cand) r r'',
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

(* ==================== THE WEAKENING LEMMA (mutual) ====================
   V : inserting a (value-valued) candidate at ambient depth d cancels
       tshift d -- including for env types (the and/&=/&s clauses place
       the inserted R at slot keyLen T1 + d of the combined env, exactly
       where tshift's keyLen-offset convention expects it).
   Vc: for context realization the insertion happens at slot keyLen A + d
       (the context's own bindings occupy the low slots).                 *)
Lemma V_tshift_mut : forall A,
  (forall d r (R:cand) v, (forall w, R w -> value w) ->
     (V (sins d R r) (tshift d A) v <-> V r A v)) /\
  (forall d r (R:cand) g, (forall w, R w -> value w) ->
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
      * intros (E & T0 & B0 & r'' & Heqv & Hg'' & HE & Hcond).
        exists E, T0, B0, (sdel (keyLen A1 + d) r''). splits;
        [ exact Heqv
        | apply goodr_sdel; exact Hg''
        | apply (proj1 (IH1C d (sdel (keyLen A1 + d) r'') R E HRval));
          eapply Vc_ext_iff_imp; [ intros p w0; exact (unins_iff _ _ _ _ _ Hcond p w0) | exact HE ]
        | intros n w0; exact (unins_cond _ _ _ _ _ Hcond n w0) ].
      * intros (E & T0 & B0 & r' & Heqv & Hg' & HE & Hcond).
        exists E, T0, B0, (sins (keyLen A1 + d) R r'). splits;
        [ exact Heqv
        | apply goodr_sins; assumption
        | exact (proj2 (IH1C d r' R E HRval) HE)
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
      * intros (E & T0 & B0 & Heq & HE & Hpin).
        exists E, T0, B0. splits;
        [ exact Heq
        | apply (proj1 (IH1C d (stail r) R E HRval));
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
      * intros (E & T0 & B0 & Heq & HE & Hpin).
        exists E, T0, B0. splits;
        [ exact Heq
        | eapply Vc_ext_imp; [ intro k; symmetry; apply stail_sins | ];
          apply (proj2 (IH1C d (stail r) R E HRval)); exact HE
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
      * intros (E & T0 & B0 & r'' & Heqv & Hg'' & HE & Hcond).
        exists E, T0, B0, (sdel (keyLen A1 + d) r''). splits;
        [ exact Heqv
        | apply goodr_sdel; exact Hg''
        | apply (proj1 (IH1C d (sdel (keyLen A1 + d) r'') R E HRval));
          eapply Vc_ext_iff_imp; [ intros p w0; exact (unins_iff _ _ _ _ _ Hcond p w0) | exact HE ]
        | intros n w0; exact (unins_cond _ _ _ _ _ Hcond n w0) ].
      * intros (E & T0 & B0 & r' & Heqv & Hg' & HE & Hcond).
        exists E, T0, B0, (sins (keyLen A1 + d) R r'). splits;
        [ exact Heqv
        | apply goodr_sins; assumption
        | exact (proj2 (IH1C d r' R E HRval) HE)
        | intros n w0; exact (sins_cond _ _ _ _ _ Hcond n w0) ].
    + intros d r R g HRval. simpl. split.
      * intros (E & T0 & B0 & Heq & HE). exists E, T0, B0. split;
        [ exact Heq
        | apply (proj1 (IH1C d (stail r) R E HRval));
          eapply Vc_ext_imp; [ intro k; apply stail_sins | exact HE ] ].
      * intros (E & T0 & B0 & Heq & HE). exists E, T0, B0. split;
        [ exact Heq
        | eapply Vc_ext_imp; [ intro k; symmetry; apply stail_sins | ];
          apply (proj2 (IH1C d (stail r) R E HRval)); exact HE ].
  (* ---- non-env constructors: Vc coincides with V and keyLen = 0 ---- *)
  - assert (HV : forall d r (R:cand) v, (forall w : exp, R w -> value w) ->
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
    + split; [ exact HV | intros d r R g HRval; simpl; reflexivity ].
  - assert (HV : forall d r (R:cand) v, (forall w : exp, R w -> value w) ->
        (V (sins d R r) (tshift d (all A1)) v <-> V r (all A1) v)).
    + intros d r R v HRval. simpl. split.
      * intros (E&e&Hv&HvE&Hf). exists E e. splits; auto. introv HRval0.
        destruct (Hf R0 C F HRval0) as (v'&Hm&Hvv&HA). exists v'. splits; auto.
        apply (proj1 (proj1 IHA1 (S d) (scons R0 r) R v' HRval)).
        eapply V_ext_imp; [ apply sins_scons_eq | exact HA ].
      * intros (E&e&Hv&HvE&Hf). exists E e. splits; auto. introv HRval0.
        destruct (Hf R0 C F HRval0) as (v'&Hm&Hvv&HA). exists v'. splits; auto.
        eapply V_ext_imp; [ intro n; symmetry; apply sins_scons_eq | ].
        apply (proj2 (proj1 IHA1 (S d) (scons R0 r) R v' HRval)); exact HA.
    + split; [ exact HV | intros d r R g HRval; simpl; reflexivity ].
  - split; intros d r R v HRval; simpl; reflexivity.
  - assert (HV : forall d r (R:cand) v, (forall w : exp, R w -> value w) ->
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
    + split; [ exact HV | intros d r R g HRval; simpl; reflexivity ].
  - assert (HV : forall d r (R:cand) v, (forall w : exp, R w -> value w) ->
        (V (sins d R r) (tshift d (rcd s A1)) v <-> V r (rcd s A1) v)).
    + intros d r R v HRval. simpl. split.
      * intros (w&Hv&HA); subst. exists w. split; auto.
        apply (proj1 (proj1 IHA1 d r R w HRval)); exact HA.
      * intros (w&Hv&HA); subst. exists w. split; auto.
        apply (proj2 (proj1 IHA1 d r R w HRval)); exact HA.
    + split; [ exact HV | intros d r R g HRval; simpl; reflexivity ].
  - split; intros d r R v HRval; simpl; reflexivity.
  - split; intros d r R v HRval; simpl; reflexivity.
  - assert (HV : forall d r (R:cand) v, (forall w : exp, R w -> value w) ->
        (V (sins d R r) (tshift d (tvar n)) v <-> V r (tvar n) v)).
    + intros d r R v HRval. simpl. unfold sins. destruct (le_gt_dec d n).
      * destruct (lt_eq_lt_dec (S n) d) as [[?|?]|?]; try lia. simpl. reflexivity.
      * destruct (lt_eq_lt_dec n d) as [[?|?]|?]; try lia; reflexivity.
    + split; [ exact HV | intros d r R g HRval; simpl; reflexivity ].
Qed.

Lemma V_tshift : forall A d r (R:cand) v, (forall w, R w -> value w) ->
  (V (sins d R r) (tshift d A) v <-> V r A v).
Proof. intro A. exact (proj1 (V_tshift_mut A)). Qed.

(* A type-level realization (ambient r) induces a context realization under
   a combined env r' whose high part is r.  For non-env types r' = r; for env
   types the V clause already carries the combined env, we just re-expose it
   (consing the pinned/abstract slot for &= / &s).                            *)
Lemma V_to_Vc : forall T r v, lshape T -> goodr r -> V r T v ->
  exists r', goodr r' /\ (forall n w, r' (n + keyLen T) w <-> r n w) /\ Vc r' T v.
Proof.
  intros T r v Hsh Hg HV.
  destruct T as [ | n | T1 T2 | T1 | T1 T2 | T1 T2 | s T1 | | T1 m T2 | T1 ];
    try solve [ inverts Hsh ].
  - (* top *) exists r. splits;
      [ exact Hg
      | intros n0 w; simpl; replace (n0 + 0) with n0 by lia; tauto
      | exact HV ].
  - (* and T1 m T2 *) destruct m; simpl in HV.
    + destruct HV as (E & w & r' & Heq & Hgr' & HE & Hcond & Hw). subst.
      exists r'. splits; [ exact Hgr' | exact Hcond | ].
      simpl. exists E, w. splits; auto.
    + destruct HV as (E & T0 & B0 & r' & Heq & Hgr' & HE & Hcond). subst.
      exists (scons (fun w => V r' T2 w) r'). splits.
      * apply goodr_scons; [ introv Hw; eapply V_value; eauto | exact Hgr' ].
      * intros n w. simpl. replace (n + S (keyLen T1)) with (S (n + keyLen T1)) by lia.
        simpl. exact (Hcond n w).
      * simpl. exists E, T0, B0. splits.
        -- reflexivity.
        -- eapply Vc_ext_imp; [ intro k; reflexivity | exact HE ].
        -- intro w. simpl. split; intro Hw.
           ++ eapply V_ext_imp; [ intro k; reflexivity | exact Hw ].
           ++ eapply V_ext_imp; [ intro k; reflexivity | exact Hw ].
  - (* ands T1 *) simpl in HV.
    destruct HV as (E & T0 & B0 & r' & Heq & Hgr' & HE & Hcond). subst.
    exists (scons (fun _ => False) r'). splits.
    + apply goodr_scons; [ intros w Hw; destruct Hw | exact Hgr' ].
    + intros n w. simpl. replace (n + S (keyLen T1)) with (S (n + keyLen T1)) by lia.
      simpl. exact (Hcond n w).
    + simpl. exists E, T0, B0. split.
      * reflexivity.
      * eapply Vc_ext_imp; [ intro k; reflexivity | exact HE ].
Qed.

(* ---- multistep infrastructure (transitivity + evaluation-context congruence) *)
Lemma mstep_trans : forall ve e1 e2 e3,
  mstep ve e1 e2 -> mstep ve e2 e3 -> mstep ve e1 e3.
Proof. introv H1 H2. induction H1; auto. eapply mstep_step; eauto. Qed.

Lemma mstep_appl : forall ve e2 e1 e1',
  value ve -> mstep ve e1 e1' -> mstep ve (app e1 e2) (app e1' e2).
Proof. introv Hv H. induction H; auto. eapply mstep_step; [ apply sappl | ]; eauto. Qed.

Lemma mstep_appr : forall ve v1 e2 e2',
  value ve -> value v1 -> mstep ve e2 e2' -> mstep ve (app v1 e2) (app v1 e2').
Proof. introv Hv Hv1 H. induction H; auto. eapply mstep_step; [ apply sappr | ]; eauto. Qed.

Lemma mstep_boxbody : forall ve e1 e2 e2',
  value ve -> value e1 -> mstep e1 e2 e2' -> mstep ve (box e1 e2) (box e1 e2').
Proof. introv Hv Hv1 H. induction H; auto. eapply mstep_step; [ apply sbox | ]; eauto. Qed.

Lemma mstep_boxl : forall ve e1 e1' e2,
  value ve -> mstep ve e1 e1' -> mstep ve (box e1 e2) (box e1' e2).
Proof. introv Hv H. induction H; auto. eapply mstep_step; [ apply sboxl | ]; eauto. Qed.

(* values are irreducible, so a value multisteps only to itself. *)
Lemma value_irred : forall v, value v -> forall ve e', ~ step ve v e'.
Proof.
  induction 1; introv Hs; try solve [ inverts Hs ].
  - inverts Hs. eapply IHvalue; eauto.
  - inverts Hs; [ eapply IHvalue1 | eapply IHvalue2 ]; eauto.
  - inverts Hs.
    + eapply IHvalue; eauto.
    + match goal with H : ~ is_box _ |- _ => apply H; constructor end.
Qed.

Lemma mstep_value : forall ve v v', value v -> mstep ve v v' -> v' = v.
Proof.
  introv Hv H. inverts H; auto. exfalso. eapply value_irred; eauto.
Qed.

(* Semantic typing:  under any value-valued r and env g realizing T (as a
   CONTEXT, i.e. Vc: r's low slots are T's own type bindings),
   e evaluates to a value in V[[A]] -- A is formed in T, so it reads the
   same r.                                                                    *)
Definition sem (T:typ) (e:exp) (A:typ) : Prop :=
  forall r g, goodr r -> Vc r T g -> exists v', mstep g e v' /\ value v' /\ V r A v'.

(* ===== compatibility lemmas (one per typing rule) ======================== *)

Lemma comp_int : forall T i, sem T (lit i) int.
Proof.
  unfold sem. introv Hg HV. exists (lit i). splits.
  - apply mstep_base. eapply Vc_value; eauto.
  - auto.
  - simpl. eauto.
Qed.

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

(* context lookup respects Vc (de Bruijn: value bindings keep r, type bindings stail+weaken) *)
Lemma var_lookup : forall T n A, get_var T n A ->
  forall r g, goodr r -> Vc r T g -> exists v', lookupv g n v' /\ V r A v'.
Proof.
  induction 1; introv Hg HV; simpl in HV.
  - destruct HV as (E&T0&B0&Heqg&HE); subst.
    edestruct (IHget_var (stail r) E) as (v'&Hl&HA);
      [ apply goodr_stail; auto | exact HE | ].
    exists v'. split; [ apply lvsucct; exact Hl | apply (proj2 (V_tshift0 A v' Hg)); exact HA ].
  - destruct HV as (E&T0&B0&Heqg&HE&Hpin); subst.
    edestruct (IHget_var (stail r) E) as (v'&Hl&HA);
      [ apply goodr_stail; auto | exact HE | ].
    exists v'. split; [ apply lvsucct; exact Hl | apply (proj2 (V_tshift0 A v' Hg)); exact HA ].
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

(* box: e1 -> v1 in V[[T1]], then e2 under v1 -> v' in V[[A]]; boxes transparent *)
Lemma comp_box : forall T e1 T1 A e2,
  sem T e1 T1 -> sem T1 e2 A -> lshape T1 -> sem T (box e1 e2) (boxt T1 A).
Proof.
  unfold sem. introv Hs1 Hs2 Hsh1 Hg HV.
  assert (value g) as Hvg by (eapply Vc_value; eauto).
  destruct (Hs1 r g Hg HV) as (v1 & Hm1 & Hvv1 & HVT1).
  destruct (@V_to_Vc T1 r v1 Hsh1 Hg HVT1) as (r' & Hgr' & Hcond & HVc1).
  destruct (Hs2 r' v1 Hgr' HVc1) as (v' & Hm2 & Hvv' & HVA).
  exists v'. splits.
  - eapply mstep_trans; [ apply mstep_boxl; eauto | ].
    eapply mstep_trans; [ apply mstep_boxbody; eauto | ].
    eapply mstep_step; [ apply sboxv; eauto | apply mstep_base; auto ].
  - auto.
  - simpl. exists r'. splits; [ exact Hgr' | exact (Vc_Vp _ _ _ HVc1) | exact HVA ].
Qed.

(* a closed value env E1 typed under top realizes V[[T1]] *)
Lemma sem_top_value : forall E1 T1 r,
  sem top E1 T1 -> value E1 -> goodr r -> V r T1 E1.
Proof.
  introv Hs Hv Hg.
  destruct (Hs r unit Hg eq_refl) as (v1 & Hm & Hvv & HVT1).
  apply mstep_value in Hm; auto. subst; auto.
Qed.

(* bclos: System-F intro; exercises the &s-context and the all clause *)
Lemma comp_bclos : forall T E1 T1 A e2,
  sem top E1 T1 -> sem (T1 &s) e2 A -> value E1 -> lshape T1 ->
  sem T (bclos E1 e2) (boxt T1 (all A)).
Proof.
  unfold sem. introv Hs1 Hs2 HvE1 Hsh1 Hg HV.
  assert (V r T1 E1) as HVT1 by (eapply sem_top_value; eauto).
  destruct (@V_to_Vc T1 r E1 Hsh1 Hg HVT1) as (r' & Hgr' & Hcond & HVc1).
  exists (bclos E1 e2). splits.
  - apply mstep_base. exact (@Vc_value T r g Hg HV).
  - auto.
  - simpl. exists r'. splits; [ exact Hgr' | exact (Vc_Vp _ _ _ HVc1) | ].
    simpl. exists E1 e2. splits; auto.
    introv HRval.
    assert (goodr (scons R r')) as Hg' by (apply goodr_scons; auto).
    assert (Vc (scons R r') (T1 &s) (E1 ;; boxt F C)) as HVctx.
    { simpl. exists E1 F C. split; [ reflexivity | ].
      eapply Vc_ext_imp; [ intro k; reflexivity | exact HVc1 ]. }
    destruct (Hs2 (scons R r') _ Hg' HVctx) as (v' & Hm & Hvv & HVA).
    exists v'. splits; auto.
Qed.

(* clos: runtime lambda-closure (already a value); like comp_lam over E1 *)
Lemma comp_clos : forall T E1 T1 A B e2,
  sem top E1 T1 -> sem (T1 & A) e2 B -> value E1 -> lshape T1 ->
  sem T (clos E1 e2) (boxt T1 (arr A B)).
Proof.
  unfold sem. introv Hs1 Hs2 HvE1 Hsh1 Hg HV.
  assert (V r T1 E1) as HVT1 by (eapply sem_top_value; eauto).
  destruct (@V_to_Vc T1 r E1 Hsh1 Hg HVT1) as (r' & Hgr' & Hcond & HVc1).
  exists (clos E1 e2). splits.
  - apply mstep_base. exact (@Vc_value T r g Hg HV).
  - auto.
  - simpl. exists r'. splits; [ exact Hgr' | exact (Vc_Vp _ _ _ HVc1) | ].
    simpl. exists E1 e2. splits; auto. introv HVA.
    apply Hs2; auto. simpl. exists E1 v2. splits; auto.
Qed.

Lemma mstep_rec : forall ve l e e',
  value ve -> mstep ve e e' -> mstep ve (rec l e) (rec l e').
Proof. introv Hv H. induction H; auto. eapply mstep_step; [ apply s_rec | ]; eauto. Qed.

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

Lemma comp_unit : forall T, sem T unit top.
Proof.
  unfold sem. introv Hg HV. exists unit. splits.
  - apply mstep_base. eapply Vc_value; eauto.
  - auto.
  - simpl. auto.
Qed.

Lemma mstep_tappl : forall ve e e' A,
  mstep ve e e' -> mstep ve (tapp e A) (tapp e' A).
Proof. introv H. induction H; auto. eapply mstep_step; [ apply stappl | ]; eauto. Qed.

(* tapp: System-F elim; instantiate the all-clause candidate R := V[[A]] -> mani A B *)
Lemma comp_tapp : forall T e A B, sem T e (all B) -> sem T (tapp e A) (mani A B).
Proof.
  unfold sem. introv Hs Hg HV.
  assert (value g) as Hvg by (eapply Vc_value; eauto).
  destruct (Hs r g Hg HV) as (vf & Hmf & Hvvf & HVall).
  simpl in HVall. destruct HVall as (E0&e0&Heq&HvE0&Hall). subst vf.
  assert (forall w, (V r A) w -> value w) as HRval by (introv HH; eapply V_value; eauto).
  destruct (Hall (V r A) A (c2g g) HRval) as (v' & Hmb & Hvv' & HVB).
  assert (value (E0 ;; boxt (c2g g) A)) as Hvbind by (constructor; auto).
  exists v'. splits.
  - eapply mstep_trans; [ apply mstep_tappl; exact Hmf | ].
    eapply mstep_step; [ apply stapp; eauto | ].
    eapply mstep_trans; [ apply mstep_boxbody; eauto | ].
    eapply mstep_step; [ apply sboxv; eauto | apply mstep_base; auto ].
  - auto.
  - simpl. exists (V r A). split; [ intro w; tauto | exact HVB ].
Qed.

(* blam: source forall-intro; blam e -> bclos g e (sbclos); result type (all B) *)
Lemma comp_blam : forall T e B, sem (T &s) e B -> sem T (blam e) (all B).
Proof.
  unfold sem. introv Hs Hg HV.
  assert (value g) as Hvg by (eapply Vc_value; eauto).
  exists (bclos g e). splits.
  - eapply mstep_step; [ apply sbclos; auto | apply mstep_base; auto ].
  - auto.
  - simpl. exists g e. splits; auto. introv HRval.
    assert (Vc (scons R r) (T &s) (g ;; boxt F C)) as HVctx.
    { simpl. exists g F C. split; [ reflexivity | ].
      eapply Vc_ext_imp; [ intro k; reflexivity | exact HV ]. }
    apply (Hs (scons R r) (g ;; boxt F C)); [ apply goodr_scons; auto | exact HVctx ].
Qed.

(* ---- remaining compatibility lemmas (stubs to be discharged) ------------- *)
(* manifest pinning: a lookt-resolvable (manifest &=) var X is interpreted exactly
   as its definition B.  B is already tshift'd, so the def env is r itself. *)
Lemma V_lookt_pin : forall T X B, lookt T X B ->
  forall r g, goodr r -> Vc r T g -> forall w, r X w <-> V r B w.
Proof.
  intros T X B Hl. induction Hl; intros r g Hg HV w.
  - simpl in HV. destruct HV as (E&w'&Heq&HET&Hw'). exact (IHHl r E Hg HET w).
  - simpl in HV. destruct HV as (E&T0&B0&Heq&HET&Hpin). rewrite (Hpin w). symmetry. apply V_tshift0; exact Hg.
  - simpl in HV. destruct HV as (E&T0&B0&Heq&HET&Hpin).
    specialize (IHHl (stail r) E (goodr_stail Hg) HET w). unfold stail in IHHl. rewrite IHHl.
    symmetry. apply V_tshift0; exact Hg.
  - simpl in HV. destruct HV as (E&T0&B0&Heq&HET).
    specialize (IHHl (stail r) E (goodr_stail Hg) HET w). unfold stail in IHHl. rewrite IHHl.
    symmetry. apply V_tshift0; exact Hg.
Qed.

(* manifest pinning needs only PIN respect (Vp), not full realization: lookt
   paths traverse only env constructors, and the equations they read are
   exactly Vp's pin conjuncts.  This is what lets a box body (rigid, hence
   lookt-or-bound vars only) be interpreted under ANY pin-respecting env.    *)
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
(* type vars X (in T1) and Y (in T2) with the same inner index are interpreted
   identically -- the alignment needed for eq_tvar. *)
Definition Ralign (r1 r2 : senv) (T1 T2 : typ) : Prop :=
  forall X, check T1 X -> check T2 X -> forall w, r1 X w <-> r2 X w.

(* rigid teq-compatibility, REALIZER-FREE: both sides rigid (box bodies) => the
   envs need only respect the manifest PINS (Vp -- always satisfiable) and agree
   on BOUND vars (< d, vacuous at d=0).  Rigid types read nothing else (their
   tvars are lookt-manifest or forall-bound), so:
   - box-EXTRACT applies the IH at the box's existential pin env (d resets to 0);
   - box-PROVIDE conjures the canonical pin env (penv) -- no inhabitation needed.
   Combined with two prefix-transport conjuncts (mirroring comp_combined below)
   so the env-type (and/ands) cases close under the bounded alignment.          *)
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
        exact (proj1 IHteqd d1 d2 H5 HrB r1 r2 Hg1 Hg2 HV1 HV2 Hbnd v).
    + intros HlA HlB; solve [ inversion HlA | inversion HlB ].
    + intros HlA HlB; solve [ inversion HlA | inversion HlB ].
  (* dq_eqr *)
  - split; [ | split ].
    + intros d1 d2 HrA HrB r1 r2 Hg1 Hg2 HV1 HV2 Hbnd v.
      simpl. inversion HrB; subst.
      * exfalso. exact (lookt_check_false H H2).
      * assert (B = B0) by (eapply lookt_det; eauto). subst.
        rewrite (Vp_lookt_pin H Hg2 HV2 v).
        exact (proj1 IHteqd d1 d2 HrA H5 r1 r2 Hg1 Hg2 HV1 HV2 Hbnd v).
    + intros HlA HlB; solve [ inversion HlA | inversion HlB ].
    + intros HlA HlB; solve [ inversion HlA | inversion HlB ].
  (* dq_boxl *)
  - split; [ | split ].
    + intros d1 d2 HrA HrB r1 r2 Hg1 Hg2 HV1 HV2 Hbnd v.
      simpl. split.
      * (* box-EXTRACT: IH at the box's pin env, depth 0 *)
        intros (rE & HgE & HpE & HrEA'). inversion HrA; subst.
        assert (forall X, check T3 X -> check T2 X -> X < 0 -> X < d2 -> forall w, rE X w <-> r2 X w) as Hbnd0 by (intros ? ? ? Hlt ?; exfalso; lia).
        apply (proj1 (proj1 IHteqd 0 d2 H4 HrB rE r2 HgE Hg2 HpE HV2 Hbnd0 v)). exact HrEA'.
      * (* box-PROVIDE: canonical pin env penv T3 *)
        intros HB. inversion HrA; subst.
        exists (penv T3). split; [ apply goodr_penv | split; [ apply Vp_penv | ] ].
        assert (forall X, check T3 X -> check T2 X -> X < 0 -> X < d2 -> forall w, penv T3 X w <-> r2 X w) as Hbnd0 by (intros ? ? ? Hlt ?; exfalso; lia).
        apply (proj2 (proj1 IHteqd 0 d2 H4 HrB (penv T3) r2 (goodr_penv T3) Hg2 (Vp_penv T3) HV2 Hbnd0 v)). exact HB.
    + intros HlA HlB; solve [ inversion HlA | inversion HlB ].
    + intros HlA HlB; solve [ inversion HlA | inversion HlB ].
  (* dq_boxr *)
  - split; [ | split ].
    + intros d1 d2 HrA HrB r1 r2 Hg1 Hg2 HV1 HV2 Hbnd v.
      simpl. split.
      * (* box-PROVIDE *)
        intros HA. inversion HrB; subst.
        exists (penv T3). split; [ apply goodr_penv | split; [ apply Vp_penv | ] ].
        assert (forall X, check T1 X -> check T3 X -> X < d1 -> X < 0 -> forall w, r1 X w <-> penv T3 X w) as Hbnd0 by (intros ? ? ? ? HltY; exfalso; lia).
        apply (proj1 (proj1 IHteqd d1 0 HrA H4 r1 (penv T3) Hg1 (goodr_penv T3) HV1 (Vp_penv T3) Hbnd0 v)). exact HA.
      * (* box-EXTRACT *)
        intros (rE & HgE & HpE & HrEB'). inversion HrB; subst.
        assert (forall X, check T1 X -> check T3 X -> X < d1 -> X < 0 -> forall w, r1 X w <-> rE X w) as Hbnd0 by (intros ? ? ? ? HltY; exfalso; lia).
        apply (proj2 (proj1 IHteqd d1 0 HrA H4 r1 rE Hg1 HgE HV1 HpE Hbnd0 v)). exact HrEB'.
    + intros HlA HlB; solve [ inversion HlA | inversion HlB ].
    + intros HlA HlB; solve [ inversion HlA | inversion HlB ].
  (* dq_arr *)
  - split; [ | split ].
    + intros d1 d2 HrA HrB r1 r2 Hg1 Hg2 HV1 HV2 Hbnd v.
      simpl. inversion HrA; subst. inversion HrB; subst. split.
      * intros (E&e&Heq&Hval&Hbody). exists E, e. split; [exact Heq | split; [exact Hval | intros v2 Hv2]].
        apply (proj2 (proj1 IHteqd1 d1 d2 H5 H7 r1 r2 Hg1 Hg2 HV1 HV2 Hbnd v2)) in Hv2.
        destruct (Hbody v2 Hv2) as (v'&Hms&Hvv&HB). exists v'. split; [exact Hms | split; [exact Hvv | apply (proj1 (proj1 IHteqd2 d1 d2 H6 H8 r1 r2 Hg1 Hg2 HV1 HV2 Hbnd v')); exact HB]].
      * intros (E&e&Heq&Hval&Hbody). exists E, e. split; [exact Heq | split; [exact Hval | intros v2 Hv2]].
        apply (proj1 (proj1 IHteqd1 d1 d2 H5 H7 r1 r2 Hg1 Hg2 HV1 HV2 Hbnd v2)) in Hv2.
        destruct (Hbody v2 Hv2) as (v'&Hms&Hvv&HB). exists v'. split; [exact Hms | split; [exact Hvv | apply (proj2 (proj1 IHteqd2 d1 d2 H6 H8 r1 r2 Hg1 Hg2 HV1 HV2 Hbnd v')); exact HB]].
    + intros HlA HlB; solve [ inversion HlA | inversion HlB ].
    + intros HlA HlB; solve [ inversion HlA | inversion HlB ].
  (* dq_all *)
  - split; [ | split ].
    + intros d1 d2 HrA HrB r1 r2 Hg1 Hg2 HV1 HV2 Hbnd v.
      simpl. inversion HrA; subst. inversion HrB; subst. split.
      * intros (E&e&Heq&Hval&Hbody). exists E, e. split; [exact Heq | split; [exact Hval | intros R C0 F0 HRval]].
        destruct (Hbody R C0 F0 HRval) as (v'&Hms&Hvv&HA). exists v'. split; [exact Hms | split; [exact Hvv | ]].
        assert (HgR1: goodr (scons R r1)). { intros [|n0] w0 Hw0; simpl in Hw0; [apply (HRval w0 Hw0) | apply (Hg1 n0 w0 Hw0)]. }
        assert (HgR2: goodr (scons R r2)). { intros [|n0] w0 Hw0; simpl in Hw0; [apply (HRval w0 Hw0) | apply (Hg2 n0 w0 Hw0)]. }
        assert (HW: Vp (scons R r1) (T1 &s)). { simpl. eapply Vp_ext_imp; [ | exact HV1 ]. intro k; reflexivity. }
        assert (HW': Vp (scons R r2) (T2 &s)). { simpl. eapply Vp_ext_imp; [ | exact HV2 ]. intro k; reflexivity. }
        assert (Hbnd': forall X, check (T1 &s) X -> check (T2 &s) X -> X < S d1 -> X < S d2 -> forall w, (scons R r1) X w <-> (scons R r2) X w).
        { intros X HcX HcY HltX HltY w. inversion HcX as [ | | | X0 ? Hc1]; subst; inversion HcY as [ | | | ? ? Hc2]; subst; simpl; [tauto | apply (Hbnd X0 Hc1 Hc2); lia]. }
        apply (proj1 (proj1 IHteqd (S d1) (S d2) H3 H4 (scons R r1) (scons R r2) HgR1 HgR2 HW HW' Hbnd' v')). exact HA.
      * intros (E&e&Heq&Hval&Hbody). exists E, e. split; [exact Heq | split; [exact Hval | intros R C0 F0 HRval]].
        destruct (Hbody R C0 F0 HRval) as (v'&Hms&Hvv&HA). exists v'. split; [exact Hms | split; [exact Hvv | ]].
        assert (HgR1: goodr (scons R r1)). { intros [|n0] w0 Hw0; simpl in Hw0; [apply (HRval w0 Hw0) | apply (Hg1 n0 w0 Hw0)]. }
        assert (HgR2: goodr (scons R r2)). { intros [|n0] w0 Hw0; simpl in Hw0; [apply (HRval w0 Hw0) | apply (Hg2 n0 w0 Hw0)]. }
        assert (HW: Vp (scons R r1) (T1 &s)). { simpl. eapply Vp_ext_imp; [ | exact HV1 ]. intro k; reflexivity. }
        assert (HW': Vp (scons R r2) (T2 &s)). { simpl. eapply Vp_ext_imp; [ | exact HV2 ]. intro k; reflexivity. }
        assert (Hbnd': forall X, check (T1 &s) X -> check (T2 &s) X -> X < S d1 -> X < S d2 -> forall w, (scons R r1) X w <-> (scons R r2) X w).
        { intros X HcX HcY HltX HltY w. inversion HcX as [ | | | X0 ? Hc1]; subst; inversion HcY as [ | | | ? ? Hc2]; subst; simpl; [tauto | apply (Hbnd X0 Hc1 Hc2); lia]. }
        apply (proj2 (proj1 IHteqd (S d1) (S d2) H3 H4 (scons R r1) (scons R r2) HgR1 HgR2 HW HW' Hbnd' v')). exact HA.
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
        -- intros (E & T0 & B0 & r1' & Heqv & Hgr1' & HE & Hcond1).
           destruct (proj1 (proj2 IHteqd1) H0 H1 d1 d2 ltac:(eassumption) ltac:(eassumption) r1 r2 Hg1 Hg2 HV1 HV2 Hbnd r1' E Hgr1' HE Hcond1)
             as (r2' & Hgr2' & HE2 & Hcond2 & Hbnd').
           exists E, T0, B0, r2'. splits; [ exact Heqv | exact Hgr2' | exact HE2 | exact Hcond2 ].
        -- intros (E & T0 & B0 & r2' & Heqv & Hgr2' & HE2 & Hcond2).
           destruct (proj2 (proj2 IHteqd1) H0 H1 d1 d2 ltac:(eassumption) ltac:(eassumption) r1 r2 Hg1 Hg2 HV1 HV2 Hbnd r2' E Hgr2' HE2 Hcond2)
             as (r1' & Hgr1' & HE1 & Hcond1 & Hbnd').
           exists E, T0, B0, r1'. splits; [ exact Heqv | exact Hgr1' | exact HE1 | exact Hcond1 ].
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
        simpl in HE. destruct HE as (E0 & T0 & B0 & HEeq & HET3 & Hpin).
        assert (Hcih : forall k w, (stail r1') (k + keyLen T3) w <-> r1 k w).
        { intros k w. unfold stail. specialize (Hcond k w). rewrite HkA in Hcond.
          rewrite <- Nat.add_succ_r. exact Hcond. }
        destruct (proj1 (proj2 IHteqd1) HlT3 HlT4 d1 d2 ltac:(eassumption) ltac:(eassumption) r1 r2 Hg1 Hg2 HV1 HV2 Hbnd (stail r1') E0
                    (goodr_stail Hgr1') HET3 Hcih)
          as (r2'0 & Hgr2'0 & HET4 & Hcond2'0 & Hbnd'0).
        exists (scons (fun w => V r2'0 B w) r2'0). splits.
        -- apply goodr_scons; [ intros w Hw; exact (@V_value B r2'0 w Hgr2'0 Hw) | exact Hgr2'0 ].
        -- simpl. exists E0, T0, B0. split; [ exact HEeq | split ].
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
        simpl in HE. destruct HE as (E0 & T0 & B0 & HEeq & HET4 & Hpin).
        assert (Hcih : forall k w, (stail r2') (k + keyLen T4) w <-> r2 k w).
        { intros k w. unfold stail. specialize (Hcond k w). rewrite HkB in Hcond.
          rewrite <- Nat.add_succ_r. exact Hcond. }
        destruct (proj2 (proj2 IHteqd1) HlT3 HlT4 d1 d2 ltac:(eassumption) ltac:(eassumption) r1 r2 Hg1 Hg2 HV1 HV2 Hbnd (stail r2') E0
                    (goodr_stail Hgr2') HET4 Hcih)
          as (r1'0 & Hgr1'0 & HET3 & Hcond1'0 & Hbnd'0).
        exists (scons (fun w => V r1'0 A w) r1'0). splits.
        -- apply goodr_scons; [ intros w Hw; exact (@V_value A r1'0 w Hgr1'0 Hw) | exact Hgr1'0 ].
        -- simpl. exists E0, T0, B0. split; [ exact HEeq | split ].
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
      * intros (E & T0 & B0 & r1' & Heqv & Hgr1' & HET3 & Hcond1).
        destruct (proj1 (proj2 IHteqd) H0 H1 d1 d2 ltac:(eassumption) ltac:(eassumption) r1 r2 Hg1 Hg2 HV1 HV2 Hbnd r1' E Hgr1' HET3 Hcond1)
          as (r2' & Hgr2' & HET4 & Hcond2 & Hbnd').
        exists E, T0, B0, r2'. splits; [ exact Heqv | exact Hgr2' | exact HET4 | exact Hcond2 ].
      * intros (E & T0 & B0 & r2' & Heqv & Hgr2' & HET4 & Hcond2).
        destruct (proj2 (proj2 IHteqd) H0 H1 d1 d2 ltac:(eassumption) ltac:(eassumption) r1 r2 Hg1 Hg2 HV1 HV2 Hbnd r2' E Hgr2' HET4 Hcond2)
          as (r1' & Hgr1' & HET3 & Hcond1 & Hbnd').
        exists E, T0, B0, r1'. splits; [ exact Heqv | exact Hgr1' | exact HET3 | exact Hcond1 ].
    + intros _ _ d1 d2 HrA HrB r1 r2 Hg1 Hg2 HV1 HV2 Hbnd r1' E Hgr1' HE Hcond.
      inversion HrA; subst. inversion HrB; subst.
      simpl in HE. destruct HE as (E0 & T0 & B0 & HEeq & HET3).
      assert (Hcih : forall k w, (stail r1') (k + keyLen T3) w <-> r1 k w).
      { intros k w. unfold stail. specialize (Hcond k w). simpl in Hcond.
        rewrite <- Nat.add_succ_r. exact Hcond. }
      destruct (proj1 (proj2 IHteqd) H0 H1 d1 d2 ltac:(eassumption) ltac:(eassumption) r1 r2 Hg1 Hg2 HV1 HV2 Hbnd (stail r1') E0
                  (goodr_stail Hgr1') HET3 Hcih)
        as (r2'0 & Hgr2'0 & HET4 & Hcond2'0 & Hbnd'0).
      exists (scons (r1' 0) r2'0). splits.
      * apply goodr_scons; [ intros w Hw; exact (Hgr1' 0 w Hw) | exact Hgr2'0 ].
      * simpl. exists E0, T0, B0. split; [ exact HEeq | ].
        eapply Vc_ext_imp; [ intro k; unfold stail, scons; reflexivity | exact HET4 ].
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
      simpl in HE. destruct HE as (E0 & T0 & B0 & HEeq & HET4).
      assert (Hcih : forall k w, (stail r2') (k + keyLen T4) w <-> r2 k w).
      { intros k w. unfold stail. specialize (Hcond k w). simpl in Hcond.
        rewrite <- Nat.add_succ_r. exact Hcond. }
      destruct (proj2 (proj2 IHteqd) H0 H1 d1 d2 ltac:(eassumption) ltac:(eassumption) r1 r2 Hg1 Hg2 HV1 HV2 Hbnd (stail r2') E0
                  (goodr_stail Hgr2') HET4 Hcih)
        as (r1'0 & Hgr1'0 & HET3 & Hcond1'0 & Hbnd'0).
      exists (scons (r2' 0) r1'0). splits.
      * apply goodr_scons; [ intros w Hw; exact (Hgr2' 0 w Hw) | exact Hgr1'0 ].
      * simpl. exists E0, T0, B0. split; [ exact HEeq | ].
        eapply Vc_ext_imp; [ intro k; unfold stail, scons; reflexivity | exact HET3 ].
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
    + destruct HE as (E0 & T0 & B0 & Heq & HET & Hpin); subst E.
      exists (g1 ++- E0), T0, B0.
      split; [destruct E0; reflexivity | split].
      * assert (HV1' : Vc (sdrop (keyLen T) (stail r)) T1 g1).
        { eapply Vc_ext_imp; [ | exact HV1]. intro n. unfold sdrop, stail. f_equal. simpl. lia. }
        apply (IHlshape (stail r) T1 g1 E0 HV1' HET).
      * exact Hpin.
  - assert (Hmc: (T1 +++ (T &s)) = ((T1 +++ T) &s)) by (destruct T; reflexivity).
    rewrite Hmc. destruct HE as (E0 & T0 & B0 & Heq & HET); subst E.
    exists (g1 ++- E0), T0, B0. split; [destruct E0; reflexivity | ].
    assert (HV1' : Vc (sdrop (keyLen T) (stail r)) T1 g1).
    { eapply Vc_ext_imp; [ | exact HV1]. intro n. unfold sdrop, stail. f_equal. simpl. lia. }
    apply (IHlshape (stail r) T1 g1 E0 HV1' HET).
Qed.

(* teqd is symmetric (the _l/_r constructors mirror; the rest are self-symmetric). *)
Lemma teqd_sym : forall n T1 A B T2, teqd n T1 A B T2 -> teqd n T2 B A T1.
Proof.
  intros n T1 A B T2 H. induction H;
    eauto using dq_int, dq_tvar, dq_eql, dq_eqr, dq_boxl, dq_boxr, dq_arr, dq_all, dq_manil, dq_manir, dq_top, dq_and, dq_ands, dq_rcd.
Qed.

Lemma teqd_rigid_l : forall n T1 A B T2, teqd n T1 A B T2 -> rigid 0 T2 B -> rigid 0 T1 A.
Proof. intros n T1 A B T2 H Hr. exact (teqd_rigid_r (teqd_sym H) Hr). Qed.

(* === Combined teq-compatibility + prefix-transport ===
   Two conjuncts proven simultaneously by structural induction on teqd:
   (1) comp_eq_gen-style type compatibility;
   (2) prefix-transport (guarded by lshape) -- the SAME value-env E that realizes A
       (over r1) also realizes B (over a constructed r2'), threading the prefix's
       abstract candidates.  dq_and is mutually recursive: its prefix uses (2), its
       binding uses (1); both available as the structural IHs of the same derivation. *)
Lemma comp_combined : forall n T1 A B T2, teqd n T1 A B T2 ->
  (forall r1 r2 g1 g2, goodr r1 -> goodr r2 -> Vc r1 T1 g1 -> Vc r2 T2 g2 ->
     Ralign r1 r2 T1 T2 -> forall v, V r1 A v <-> V r2 B v)
  /\ (lshape A -> lshape B ->
      forall r1 r2 g1 g2, goodr r1 -> goodr r2 -> Vc r1 T1 g1 -> Vc r2 T2 g2 -> Ralign r1 r2 T1 T2 ->
      forall r1' E, goodr r1' -> Vc r1' A E ->
        (forall k w, r1' (k + keyLen A) w <-> r1 k w) ->
      exists r2', goodr r2' /\ Vc r2' B E /\
        (forall k w, r2' (k + keyLen B) w <-> r2 k w) /\
        Ralign r1' r2' (T1 +++ A) (T2 +++ B))
  /\ (lshape A -> lshape B ->
      forall r1 r2 g1 g2, goodr r1 -> goodr r2 -> Vc r1 T1 g1 -> Vc r2 T2 g2 -> Ralign r1 r2 T1 T2 ->
      forall r2' E, goodr r2' -> Vc r2' B E ->
        (forall k w, r2' (k + keyLen B) w <-> r2 k w) ->
      exists r1', goodr r1' /\ Vc r1' A E /\
        (forall k w, r1' (k + keyLen A) w <-> r1 k w) /\
        Ralign r1' r2' (T1 +++ A) (T2 +++ B)).
Proof.
  intros n T1 A B T2 H. induction H.
  (* dq_int *)
  - split; [| split].
    + intros r1 r2 g1 g2 Hg1 Hg2 HV1 HV2 Hal v. simpl. tauto.
    + intros HlA HlB; solve [ inversion HlA | inversion HlB ].
    + intros HlA HlB; solve [ inversion HlA | inversion HlB ].
  (* dq_tvar *)
  - split; [| split].
    + intros r1 r2 g1 g2 Hg1 Hg2 HV1 HV2 Hal v. simpl. exact (Hal X H1 H2 v).
    + intros HlA HlB; solve [ inversion HlA | inversion HlB ].
    + intros HlA HlB; solve [ inversion HlA | inversion HlB ].
  (* dq_eql *)
  - split; [| split].
    + intros r1 r2 g1 g2 Hg1 Hg2 HV1 HV2 Hal v. simpl.
      rewrite (V_lookt_pin H g1 Hg1 HV1 v). exact (proj1 IHteqd r1 r2 g1 g2 Hg1 Hg2 HV1 HV2 Hal v).
    + intros HlA HlB; solve [ inversion HlA | inversion HlB ].
    + intros HlA HlB; solve [ inversion HlA | inversion HlB ].
  (* dq_eqr *)
  - split; [| split].
    + intros r1 r2 g1 g2 Hg1 Hg2 HV1 HV2 Hal v. simpl.
      rewrite (V_lookt_pin H g2 Hg2 HV2 v). exact (proj1 IHteqd r1 r2 g1 g2 Hg1 Hg2 HV1 HV2 Hal v).
    + intros HlA HlB; solve [ inversion HlA | inversion HlB ].
    + intros HlA HlB; solve [ inversion HlA | inversion HlB ].
  (* dq_boxl *)
  - split; [| split].
    + intros r1 r2 g1 g2 Hg1 Hg2 HV1 HV2 Hal v.
      exact (comp_eq_rigid (dq_boxl H H0) (rigid_box 0 T1 (wft_box_rigid H0))
               (teqd_rigid_r H (wft_box_rigid H0)) Hg1 Hg2 (Vc_Vp _ _ _ HV1) (Vc_Vp _ _ _ HV2)
               ltac:(intros ? ? ? Hlt ?; exfalso; lia) v).
    + intros HlA HlB; solve [ inversion HlA | inversion HlB ].
    + intros HlA HlB; solve [ inversion HlA | inversion HlB ].
  (* dq_boxr *)
  - split; [| split].
    + intros r1 r2 g1 g2 Hg1 Hg2 HV1 HV2 Hal v.
      exact (comp_eq_rigid (dq_boxr H H0) (teqd_rigid_l (dq_boxr H H0) (rigid_box 0 T2 (wft_box_rigid H0)))
               (rigid_box 0 T2 (wft_box_rigid H0)) Hg1 Hg2 (Vc_Vp _ _ _ HV1) (Vc_Vp _ _ _ HV2)
               ltac:(intros ? ? ? Hlt ?; exfalso; lia) v).
    + intros HlA HlB; solve [ inversion HlA | inversion HlB ].
    + intros HlA HlB; solve [ inversion HlA | inversion HlB ].
  (* dq_arr *)
  - split; [| split].
    + intros r1 r2 g1 g2 Hg1 Hg2 HV1 HV2 Hal v. simpl. split.
      * intros (E&e&Heq&Hval&Hbody). exists E, e. split; [exact Heq | split; [exact Hval | intros v2 Hv2]].
        apply (proj2 (proj1 IHteqd1 r1 r2 g1 g2 Hg1 Hg2 HV1 HV2 Hal v2)) in Hv2.
        destruct (Hbody v2 Hv2) as (v'&Hms&Hvv&HB). exists v'. split; [exact Hms | split; [exact Hvv | apply (proj1 (proj1 IHteqd2 r1 r2 g1 g2 Hg1 Hg2 HV1 HV2 Hal v')); exact HB]].
      * intros (E&e&Heq&Hval&Hbody). exists E, e. split; [exact Heq | split; [exact Hval | intros v2 Hv2]].
        apply (proj1 (proj1 IHteqd1 r1 r2 g1 g2 Hg1 Hg2 HV1 HV2 Hal v2)) in Hv2.
        destruct (Hbody v2 Hv2) as (v'&Hms&Hvv&HB). exists v'. split; [exact Hms | split; [exact Hvv | apply (proj2 (proj1 IHteqd2 r1 r2 g1 g2 Hg1 Hg2 HV1 HV2 Hal v')); exact HB]].
    + intros HlA HlB; solve [ inversion HlA | inversion HlB ].
    + intros HlA HlB; solve [ inversion HlA | inversion HlB ].
  (* dq_all *)
  - split; [| split].
    + intros r1 r2 g1 g2 Hg1 Hg2 HV1 HV2 Hal v. simpl. split.
      * intros (E&e&Heq&Hval&Hbody). exists E, e. split; [exact Heq | split; [exact Hval | intros R C0 F0 HRval]].
        destruct (Hbody R C0 F0 HRval) as (v'&Hms&Hvv&HA). exists v'. split; [exact Hms | split; [exact Hvv | ]].
        assert (HgR1: goodr (scons R r1)). { intros [|n0] w0 Hw0; simpl in Hw0; [apply (HRval w0 Hw0) | apply (Hg1 n0 w0 Hw0)]. }
        assert (HgR2: goodr (scons R r2)). { intros [|n0] w0 Hw0; simpl in Hw0; [apply (HRval w0 Hw0) | apply (Hg2 n0 w0 Hw0)]. }
        assert (HW: Vc (scons R r1) (T1 &s) (g1;; boxt top top)). { simpl. exists g1, top, top. split; [reflexivity | exact HV1]. }
        assert (HW': Vc (scons R r2) (T2 &s) (g2;; boxt top top)). { simpl. exists g2, top, top. split; [reflexivity | exact HV2]. }
        assert (Hal': Ralign (scons R r1) (scons R r2) (T1 &s) (T2 &s)). { intros X HcX HcY w. inversion HcX; subst; inversion HcY; subst; simpl; [tauto | match goal with HX : check T1 ?a, HY : check T2 ?a |- _ => apply (Hal a HX HY w) end]. }
        apply (proj1 (proj1 IHteqd (scons R r1) (scons R r2) (g1;; boxt top top) (g2;; boxt top top) HgR1 HgR2 HW HW' Hal' v')). exact HA.
      * intros (E&e&Heq&Hval&Hbody). exists E, e. split; [exact Heq | split; [exact Hval | intros R C0 F0 HRval]].
        destruct (Hbody R C0 F0 HRval) as (v'&Hms&Hvv&HA). exists v'. split; [exact Hms | split; [exact Hvv | ]].
        assert (HgR1: goodr (scons R r1)). { intros [|n0] w0 Hw0; simpl in Hw0; [apply (HRval w0 Hw0) | apply (Hg1 n0 w0 Hw0)]. }
        assert (HgR2: goodr (scons R r2)). { intros [|n0] w0 Hw0; simpl in Hw0; [apply (HRval w0 Hw0) | apply (Hg2 n0 w0 Hw0)]. }
        assert (HW: Vc (scons R r1) (T1 &s) (g1;; boxt top top)). { simpl. exists g1, top, top. split; [reflexivity | exact HV1]. }
        assert (HW': Vc (scons R r2) (T2 &s) (g2;; boxt top top)). { simpl. exists g2, top, top. split; [reflexivity | exact HV2]. }
        assert (Hal': Ralign (scons R r1) (scons R r2) (T1 &s) (T2 &s)). { intros X HcX HcY w. inversion HcX; subst; inversion HcY; subst; simpl; [tauto | match goal with HX : check T1 ?a, HY : check T2 ?a |- _ => apply (Hal a HX HY w) end]. }
        apply (proj2 (proj1 IHteqd (scons R r1) (scons R r2) (g1;; boxt top top) (g2;; boxt top top) HgR1 HgR2 HW HW' Hal' v')). exact HA.
    + intros HlA HlB; solve [ inversion HlA | inversion HlB ].
    + intros HlA HlB; solve [ inversion HlA | inversion HlB ].
  (* dq_manil *)
  - split; [| split].
    + intros r1 r2 g1 g2 Hg1 Hg2 HV1 HV2 Hal v. simpl. split.
      * intros (R & HReq & HB).
        assert (HgR1: goodr (scons R r1)). { intros [|n0] w0 Hw0; simpl in Hw0; [exact (@V_value A r1 w0 Hg1 (proj1 (HReq w0) Hw0)) | apply (Hg1 n0 w0 Hw0)]. }
        assert (HgR2: goodr (scons (fun w => V r1 A w) r2)). { intros [|n0] w0 Hw0; simpl in Hw0; [exact (@V_value A r1 w0 Hg1 Hw0) | apply (Hg2 n0 w0 Hw0)]. }
        assert (HW: Vc (scons R r1) (T1 &= A) (g1;; boxt top top)). { simpl. exists g1, top, top. split; [reflexivity | split; [exact HV1 | exact HReq]]. }
        assert (HW2: Vc (scons (fun w => V r1 A w) r2) (T2 &s) (g2;; boxt top top)). { simpl. exists g2, top, top. split; [reflexivity | eapply Vc_ext_imp; [ intro k; unfold stail, scons; reflexivity | exact HV2 ] ]. }
        assert (Hal': Ralign (scons R r1) (scons (fun w => V r1 A w) r2) (T1 &= A) (T2 &s)). { intros X HcX HcY w. inversion HcX; subst; inversion HcY; subst; simpl. match goal with HX : check T1 ?a, HY : check T2 ?a |- _ => apply (Hal a HX HY w) end. }
        apply (proj1 (V_tshift0 C v HgR2)).
        apply (proj1 (proj1 IHteqd (scons R r1) (scons (fun w => V r1 A w) r2) (g1;; boxt top top) (g2;; boxt top top) HgR1 HgR2 HW HW2 Hal' v)). exact HB.
      * intros HC. exists (fun w => V r1 A w). split; [intro w; reflexivity | ].
        assert (HgR1: goodr (scons (fun w => V r1 A w) r1)). { intros [|n0] w0 Hw0; simpl in Hw0; [exact (@V_value A r1 w0 Hg1 Hw0) | apply (Hg1 n0 w0 Hw0)]. }
        assert (HgR2: goodr (scons (fun w => V r1 A w) r2)). { intros [|n0] w0 Hw0; simpl in Hw0; [exact (@V_value A r1 w0 Hg1 Hw0) | apply (Hg2 n0 w0 Hw0)]. }
        assert (HW: Vc (scons (fun w => V r1 A w) r1) (T1 &= A) (g1;; boxt top top)). { simpl. exists g1, top, top. split; [reflexivity | split; [exact HV1 | intro w; reflexivity]]. }
        assert (HW2: Vc (scons (fun w => V r1 A w) r2) (T2 &s) (g2;; boxt top top)). { simpl. exists g2, top, top. split; [reflexivity | eapply Vc_ext_imp; [ intro k; unfold stail, scons; reflexivity | exact HV2 ] ]. }
        assert (Hal': Ralign (scons (fun w => V r1 A w) r1) (scons (fun w => V r1 A w) r2) (T1 &= A) (T2 &s)). { intros X HcX HcY w. inversion HcX; subst; inversion HcY; subst; simpl. match goal with HX : check T1 ?a, HY : check T2 ?a |- _ => apply (Hal a HX HY w) end. }
        apply (proj2 (proj1 IHteqd (scons (fun w => V r1 A w) r1) (scons (fun w => V r1 A w) r2) (g1;; boxt top top) (g2;; boxt top top) HgR1 HgR2 HW HW2 Hal' v)).
        apply (proj2 (V_tshift0 C v HgR2)). exact HC.
    + intros HlA HlB; solve [ inversion HlA | inversion HlB ].
    + intros HlA HlB; solve [ inversion HlA | inversion HlB ].
  (* dq_manir *)
  - split; [| split].
    + intros r1 r2 g1 g2 Hg1 Hg2 HV1 HV2 Hal v. simpl. split.
      * intros HB. exists (fun w => V r2 A w). split; [intro w; reflexivity | ].
        assert (HgR2: goodr (scons (fun w => V r2 A w) r2)). { intros [|n0] w0 Hw0; simpl in Hw0; [exact (@V_value A r2 w0 Hg2 Hw0) | apply (Hg2 n0 w0 Hw0)]. }
        assert (HgR1: goodr (scons (fun w => V r2 A w) r1)). { intros [|n0] w0 Hw0; simpl in Hw0; [exact (@V_value A r2 w0 Hg2 Hw0) | apply (Hg1 n0 w0 Hw0)]. }
        assert (HW: Vc (scons (fun w => V r2 A w) r2) (T2 &= A) (g2;; boxt top top)). { simpl. exists g2, top, top. split; [reflexivity | split; [exact HV2 | intro w; reflexivity]]. }
        assert (HW1: Vc (scons (fun w => V r2 A w) r1) (T1 &s) (g1;; boxt top top)). { simpl. exists g1, top, top. split; [reflexivity | eapply Vc_ext_imp; [ intro k; unfold stail, scons; reflexivity | exact HV1 ] ]. }
        assert (Hal': Ralign (scons (fun w => V r2 A w) r1) (scons (fun w => V r2 A w) r2) (T1 &s) (T2 &= A)). { intros X HcX HcY w. inversion HcX; subst; inversion HcY; subst; simpl. match goal with HX : check T1 ?a, HY : check T2 ?a |- _ => apply (Hal a HX HY w) end. }
        apply (proj1 (proj1 IHteqd (scons (fun w => V r2 A w) r1) (scons (fun w => V r2 A w) r2) (g1;; boxt top top) (g2;; boxt top top) HgR1 HgR2 HW1 HW Hal' v)).
        apply (proj2 (V_tshift0 B v HgR1)). exact HB.
      * intros (R & HReq & HC).
        assert (HgR2: goodr (scons R r2)). { intros [|n0] w0 Hw0; simpl in Hw0; [exact (@V_value A r2 w0 Hg2 (proj1 (HReq w0) Hw0)) | apply (Hg2 n0 w0 Hw0)]. }
        assert (HgR1: goodr (scons R r1)). { intros [|n0] w0 Hw0; simpl in Hw0; [exact (@V_value A r2 w0 Hg2 (proj1 (HReq w0) Hw0)) | apply (Hg1 n0 w0 Hw0)]. }
        assert (HW: Vc (scons R r2) (T2 &= A) (g2;; boxt top top)). { simpl. exists g2, top, top. split; [reflexivity | split; [exact HV2 | exact HReq]]. }
        assert (HW1: Vc (scons R r1) (T1 &s) (g1;; boxt top top)). { simpl. exists g1, top, top. split; [reflexivity | eapply Vc_ext_imp; [ intro k; unfold stail, scons; reflexivity | exact HV1 ] ]. }
        assert (Hal': Ralign (scons R r1) (scons R r2) (T1 &s) (T2 &= A)). { intros X HcX HcY w. inversion HcX; subst; inversion HcY; subst; simpl. match goal with HX : check T1 ?a, HY : check T2 ?a |- _ => apply (Hal a HX HY w) end. }
        apply (proj1 (V_tshift0 B v HgR1)).
        apply (proj2 (proj1 IHteqd (scons R r1) (scons R r2) (g1;; boxt top top) (g2;; boxt top top) HgR1 HgR2 HW1 HW Hal' v)). exact HC.
    + intros HlA HlB; solve [ inversion HlA | inversion HlB ].
    + intros HlA HlB; solve [ inversion HlA | inversion HlB ].
  (* dq_top *)
  - split; [| split].
    + intros r1 r2 g1 g2 Hg1 Hg2 HV1 HV2 Hal v. simpl. tauto.
    + intros _ _ r1 r2 g1 g2 Hg1 Hg2 HV1 HV2 Hal r1' E Hgr1' HE Hcond.
      exists r2. simpl in HE; subst E. splits.
      * exact Hg2.
      * reflexivity.
      * intros k w. rewrite Nat.add_0_r. tauto.
      * intros X HcX HcY w. specialize (Hcond X w). rewrite Nat.add_0_r in Hcond.
        rewrite Hcond. exact (Hal X HcX HcY w).
    + intros _ _ r1 r2 g1 g2 Hg1 Hg2 HV1 HV2 Hal r2' E Hgr2' HE Hcond.
      exists r1. simpl in HE; subst E. splits.
      * exact Hg1.
      * reflexivity.
      * intros k w. rewrite Nat.add_0_r. tauto.
      * intros X HcX HcY w. specialize (Hcond X w). rewrite Nat.add_0_r in Hcond.
        rewrite Hcond. exact (Hal X HcX HcY w).
  (* dq_and *)
  - split; [| split].
    + intros r1 r2 g1 g2 Hg1 Hg2 HV1 HV2 Hal v. destruct m.
      * simpl. split.
        -- intros (E & w & r1' & Heqv & Hgr1' & HE & Hcond1 & HA).
           assert (Hsd1 : Vc (sdrop (keyLen T3) r1') T1 g1).
           { apply (Vc_ext_iff_imp T1 r1 (sdrop (keyLen T3) r1') g1);
               [ intros k z; unfold sdrop; symmetry; apply Hcond1 | exact HV1 ]. }
           assert (HVcat1 : Vc r1' (T1 +++ T3) (g1 ++- E)).
           { apply V_concat_realize; [ exact H0 | exact Hsd1 | exact HE ]. }
           destruct (proj1 (proj2 IHteqd1) H0 H1 r1 r2 g1 g2 Hg1 Hg2 HV1 HV2 Hal r1' E Hgr1' HE Hcond1)
             as (r2' & Hgr2' & HE2 & Hcond2 & Hal').
           assert (Hsd2 : Vc (sdrop (keyLen T4) r2') T2 g2).
           { apply (Vc_ext_iff_imp T2 r2 (sdrop (keyLen T4) r2') g2);
               [ intros k z; unfold sdrop; symmetry; apply Hcond2 | exact HV2 ]. }
           assert (HVcat2 : Vc r2' (T2 +++ T4) (g2 ++- E)).
           { apply V_concat_realize; [ exact H1 | exact Hsd2 | exact HE2 ]. }
           exists E, w, r2'. splits;
             [ exact Heqv | exact Hgr2' | exact HE2 | exact Hcond2 | ].
           apply (proj1 IHteqd2 r1' r2' (g1 ++- E) (g2 ++- E) Hgr1' Hgr2' HVcat1 HVcat2 Hal' w).
           exact HA.
        -- intros (E & w & r2' & Heqv & Hgr2' & HE2 & Hcond2 & HB).
           assert (Hsd2 : Vc (sdrop (keyLen T4) r2') T2 g2).
           { apply (Vc_ext_iff_imp T2 r2 (sdrop (keyLen T4) r2') g2);
               [ intros k z; unfold sdrop; symmetry; apply Hcond2 | exact HV2 ]. }
           assert (HVcat2 : Vc r2' (T2 +++ T4) (g2 ++- E)).
           { apply V_concat_realize; [ exact H1 | exact Hsd2 | exact HE2 ]. }
           destruct (proj2 (proj2 IHteqd1) H0 H1 r1 r2 g1 g2 Hg1 Hg2 HV1 HV2 Hal r2' E Hgr2' HE2 Hcond2)
             as (r1' & Hgr1' & HE1 & Hcond1 & Hal').
           assert (Hsd1 : Vc (sdrop (keyLen T3) r1') T1 g1).
           { apply (Vc_ext_iff_imp T1 r1 (sdrop (keyLen T3) r1') g1);
               [ intros k z; unfold sdrop; symmetry; apply Hcond1 | exact HV1 ]. }
           assert (HVcat1 : Vc r1' (T1 +++ T3) (g1 ++- E)).
           { apply V_concat_realize; [ exact H0 | exact Hsd1 | exact HE1 ]. }
           exists E, w, r1'. splits;
             [ exact Heqv | exact Hgr1' | exact HE1 | exact Hcond1 | ].
           apply (proj2 (proj1 IHteqd2 r1' r2' (g1 ++- E) (g2 ++- E) Hgr1' Hgr2' HVcat1 HVcat2 Hal' w)).
           exact HB.
      * simpl. split.
        -- intros (E & T0 & B0 & r1' & Heqv & Hgr1' & HE & Hcond1).
           destruct (proj1 (proj2 IHteqd1) H0 H1 r1 r2 g1 g2 Hg1 Hg2 HV1 HV2 Hal r1' E Hgr1' HE Hcond1)
             as (r2' & Hgr2' & HE2 & Hcond2 & Hal').
           exists E, T0, B0, r2'. splits;
             [ exact Heqv | exact Hgr2' | exact HE2 | exact Hcond2 ].
        -- intros (E & T0 & B0 & r2' & Heqv & Hgr2' & HE2 & Hcond2).
           destruct (proj2 (proj2 IHteqd1) H0 H1 r1 r2 g1 g2 Hg1 Hg2 HV1 HV2 Hal r2' E Hgr2' HE2 Hcond2)
             as (r1' & Hgr1' & HE1 & Hcond1 & Hal').
           exists E, T0, B0, r1'. splits;
             [ exact Heqv | exact Hgr1' | exact HE1 | exact Hcond1 ].
    + intros HlA HlB r1 r2 g1 g2 Hg1 Hg2 HV1 HV2 Hal r1' E Hgr1' HE Hcond.
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
        destruct (proj1 (proj2 IHteqd1) HlT3 HlT4 r1 r2 g1 g2 Hg1 Hg2 HV1 HV2 Hal r1' E0 Hgr1' HET3 Hcond)
          as (r2' & Hgr2' & HET4 & Hcond2 & Hal').
        assert (Hsd1 : Vc (sdrop (keyLen T3) r1') T1 g1).
        { apply (Vc_ext_iff_imp T1 r1 (sdrop (keyLen T3) r1') g1);
            [ intros k z; unfold sdrop; symmetry; apply Hcond | exact HV1 ]. }
        assert (HVcat1 : Vc r1' (T1 +++ T3) (g1 ++- E0)).
        { apply V_concat_realize; [ exact HlT3 | exact Hsd1 | exact HET3 ]. }
        assert (Hsd2 : Vc (sdrop (keyLen T4) r2') T2 g2).
        { apply (Vc_ext_iff_imp T2 r2 (sdrop (keyLen T4) r2') g2);
            [ intros k z; unfold sdrop; symmetry; apply Hcond2 | exact HV2 ]. }
        assert (HVcat2 : Vc r2' (T2 +++ T4) (g2 ++- E0)).
        { apply V_concat_realize; [ exact HlT4 | exact Hsd2 | exact HET4 ]. }
        assert (HBw : V r2' B w).
        { apply (proj1 IHteqd2 r1' r2' (g1 ++- E0) (g2 ++- E0) Hgr1' Hgr2' HVcat1 HVcat2 Hal' w). exact HAw. }
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
        simpl in HE. destruct HE as (E0 & T0 & B0 & HEeq & HET3 & Hpin).
        assert (Hcih : forall k w, (stail r1') (k + keyLen T3) w <-> r1 k w).
        { intros k w. unfold stail. specialize (Hcond k w). rewrite HkA in Hcond.
          rewrite <- Nat.add_succ_r. exact Hcond. }
        destruct (proj1 (proj2 IHteqd1) HlT3 HlT4 r1 r2 g1 g2 Hg1 Hg2 HV1 HV2 Hal (stail r1') E0
                    (goodr_stail Hgr1') HET3 Hcih)
          as (r2'0 & Hgr2'0 & HET4 & Hcond2'0 & Hal'0).
        exists (scons (fun w => V r2'0 B w) r2'0). splits.
        -- apply goodr_scons; [ intros w Hw; exact (@V_value B r2'0 w Hgr2'0 Hw) | exact Hgr2'0 ].
        -- simpl. exists E0, T0, B0. split; [ exact HEeq | split ].
           ++ eapply Vc_ext_imp; [ intro k; unfold stail, scons; reflexivity | exact HET4 ].
           ++ intro w. unfold scons, stail. reflexivity.
        -- intros k w. rewrite HkB. simpl. rewrite Nat.add_succ_r. exact (Hcond2'0 k w).
        -- rewrite Hcat3, Hcat4. intros X HcX HcY w0.
           inversion HcX; subst. inversion HcY; subst.
           match goal with HX : check (T1 +++ T3) ?a, HY : check (T2 +++ T4) ?a |- _ =>
             generalize (Hal'0 a HX HY w0) end. unfold stail, scons. simpl. tauto.
    + intros HlA HlB r1 r2 g1 g2 Hg1 Hg2 HV1 HV2 Hal r2' E Hgr2' HE Hcond.
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
        destruct (proj2 (proj2 IHteqd1) HlT3 HlT4 r1 r2 g1 g2 Hg1 Hg2 HV1 HV2 Hal r2' E0 Hgr2' HET4 Hcond)
          as (r1' & Hgr1' & HET3 & Hcond1 & Hal').
        assert (Hsd1 : Vc (sdrop (keyLen T3) r1') T1 g1).
        { apply (Vc_ext_iff_imp T1 r1 (sdrop (keyLen T3) r1') g1);
            [ intros k z; unfold sdrop; symmetry; apply Hcond1 | exact HV1 ]. }
        assert (HVcat1 : Vc r1' (T1 +++ T3) (g1 ++- E0)).
        { apply V_concat_realize; [ exact HlT3 | exact Hsd1 | exact HET3 ]. }
        assert (Hsd2 : Vc (sdrop (keyLen T4) r2') T2 g2).
        { apply (Vc_ext_iff_imp T2 r2 (sdrop (keyLen T4) r2') g2);
            [ intros k z; unfold sdrop; symmetry; apply Hcond | exact HV2 ]. }
        assert (HVcat2 : Vc r2' (T2 +++ T4) (g2 ++- E0)).
        { apply V_concat_realize; [ exact HlT4 | exact Hsd2 | exact HET4 ]. }
        assert (HAw : V r1' A w).
        { apply (proj2 (proj1 IHteqd2 r1' r2' (g1 ++- E0) (g2 ++- E0) Hgr1' Hgr2' HVcat1 HVcat2 Hal' w)). exact HBw. }
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
        simpl in HE. destruct HE as (E0 & T0 & B0 & HEeq & HET4 & Hpin).
        assert (Hcih : forall k w, (stail r2') (k + keyLen T4) w <-> r2 k w).
        { intros k w. unfold stail. specialize (Hcond k w). rewrite HkB in Hcond.
          rewrite <- Nat.add_succ_r. exact Hcond. }
        destruct (proj2 (proj2 IHteqd1) HlT3 HlT4 r1 r2 g1 g2 Hg1 Hg2 HV1 HV2 Hal (stail r2') E0
                    (goodr_stail Hgr2') HET4 Hcih)
          as (r1'0 & Hgr1'0 & HET3 & Hcond1'0 & Hal'0).
        exists (scons (fun w => V r1'0 A w) r1'0). splits.
        -- apply goodr_scons; [ intros w Hw; exact (@V_value A r1'0 w Hgr1'0 Hw) | exact Hgr1'0 ].
        -- simpl. exists E0, T0, B0. split; [ exact HEeq | split ].
           ++ eapply Vc_ext_imp; [ intro k; unfold stail, scons; reflexivity | exact HET3 ].
           ++ intro w. unfold scons, stail. reflexivity.
        -- intros k w. rewrite HkA. simpl. rewrite Nat.add_succ_r. exact (Hcond1'0 k w).
        -- rewrite Hcat3, Hcat4. intros X HcX HcY w0.
           inversion HcX; subst. inversion HcY; subst.
           match goal with HX : check (T1 +++ T3) ?a, HY : check (T2 +++ T4) ?a |- _ =>
             generalize (Hal'0 a HX HY w0) end. unfold stail, scons. simpl. tauto.
  (* dq_ands *)
  - split; [| split].
    + intros r1 r2 g1 g2 Hg1 Hg2 HV1 HV2 Hal v. simpl. split.
      * intros (E & T0 & B0 & r1' & Heqv & Hgr1' & HET3 & Hcond1).
        destruct (proj1 (proj2 IHteqd) H0 H1 r1 r2 g1 g2 Hg1 Hg2 HV1 HV2 Hal r1' E Hgr1' HET3 Hcond1)
          as (r2' & Hgr2' & HET4 & Hcond2 & Hal').
        exists E, T0, B0, r2'. splits;
          [ exact Heqv | exact Hgr2' | exact HET4 | exact Hcond2 ].
      * intros (E & T0 & B0 & r2' & Heqv & Hgr2' & HET4 & Hcond2).
        destruct (proj2 (proj2 IHteqd) H0 H1 r1 r2 g1 g2 Hg1 Hg2 HV1 HV2 Hal r2' E Hgr2' HET4 Hcond2)
          as (r1' & Hgr1' & HET3 & Hcond1 & Hal').
        exists E, T0, B0, r1'. splits;
          [ exact Heqv | exact Hgr1' | exact HET3 | exact Hcond1 ].
    + intros _ _ r1 r2 g1 g2 Hg1 Hg2 HV1 HV2 Hal r1' E Hgr1' HE Hcond.
      simpl in HE. destruct HE as (E0 & T0 & B0 & HEeq & HET3).
      assert (Hcih : forall k w, (stail r1') (k + keyLen T3) w <-> r1 k w).
      { intros k w. unfold stail. specialize (Hcond k w). simpl in Hcond.
        rewrite <- Nat.add_succ_r. exact Hcond. }
      destruct (proj1 (proj2 IHteqd) H0 H1 r1 r2 g1 g2 Hg1 Hg2 HV1 HV2 Hal (stail r1') E0
                  (goodr_stail Hgr1') HET3 Hcih)
        as (r2'0 & Hgr2'0 & HET4 & Hcond2'0 & Hal'0).
      exists (scons (r1' 0) r2'0). splits.
      * apply goodr_scons; [ intros w Hw; exact (Hgr1' 0 w Hw) | exact Hgr2'0 ].
      * simpl. exists E0, T0, B0. split; [ exact HEeq | ].
        eapply Vc_ext_imp; [ intro k; unfold stail, scons; reflexivity | exact HET4 ].
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
    + intros _ _ r1 r2 g1 g2 Hg1 Hg2 HV1 HV2 Hal r2' E Hgr2' HE Hcond.
      simpl in HE. destruct HE as (E0 & T0 & B0 & HEeq & HET4).
      assert (Hcih : forall k w, (stail r2') (k + keyLen T4) w <-> r2 k w).
      { intros k w. unfold stail. specialize (Hcond k w). simpl in Hcond.
        rewrite <- Nat.add_succ_r. exact Hcond. }
      destruct (proj2 (proj2 IHteqd) H0 H1 r1 r2 g1 g2 Hg1 Hg2 HV1 HV2 Hal (stail r2') E0
                  (goodr_stail Hgr2') HET4 Hcih)
        as (r1'0 & Hgr1'0 & HET3 & Hcond1'0 & Hal'0).
      exists (scons (r2' 0) r1'0). splits.
      * apply goodr_scons; [ intros w Hw; exact (Hgr2' 0 w Hw) | exact Hgr1'0 ].
      * simpl. exists E0, T0, B0. split; [ exact HEeq | ].
        eapply Vc_ext_imp; [ intro k; unfold stail, scons; reflexivity | exact HET3 ].
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
  (* dq_rcd *)
  - split; [| split].
    + intros r1 r2 g1 g2 Hg1 Hg2 HV1 HV2 Hal v. simpl. split.
      * intros (v'&Heq&HA). exists v'. split; [exact Heq | apply (proj1 (proj1 IHteqd r1 r2 g1 g2 Hg1 Hg2 HV1 HV2 Hal v')); exact HA].
      * intros (v'&Heq&HA). exists v'. split; [exact Heq | apply (proj2 (proj1 IHteqd r1 r2 g1 g2 Hg1 Hg2 HV1 HV2 Hal v')); exact HA].
    + intros HlA HlB; solve [ inversion HlA | inversion HlB ].
    + intros HlA HlB; solve [ inversion HlA | inversion HlB ].
Qed.

(* generalized teq-compatibility over two contexts. *)
Lemma comp_eq_gen : forall n T1 A B T2, teqd n T1 A B T2 ->
  forall r1 r2 g1 g2, goodr r1 -> goodr r2 ->
  Vc r1 T1 g1 -> Vc r2 T2 g2 -> Ralign r1 r2 T1 T2 ->
  forall v, V r1 A v <-> V r2 B v.
Proof. intros n T1 A B T2 H. exact (proj1 (comp_combined H)). Qed.

Lemma comp_eq : forall T e A B, sem T e A -> teq T A B T -> sem T e B.
Proof.
  intros T e A B Hsem Hteq r g Hg HV.
  destruct (Hsem r g Hg HV) as (v' & Hms & Hvv & HVA).
  exists v'. split; [exact Hms | split; [exact Hvv | ]].
  destruct (teq_teqd Hteq) as (n & Hteqd).
  assert (HRal : Ralign r r T T).
  { intros X HcX HcY w. tauto. }
  apply (proj1 (comp_eq_gen Hteqd g g Hg Hg HV HV HRal v')). exact HVA.
Qed.

Lemma mstep_proj : forall ve l e e',
  value ve -> mstep ve e e' -> mstep ve (rproj e l) (rproj e' l).
Proof. introv Hv H. induction H; auto. eapply mstep_step; [ apply s_proj | ]; eauto. Qed.

(* opening a field type over its prefix preserves V (given r realizes the prefix) *)
(* mopen drops the manifest bindings it inlines, so B is read under r with
   keyLen T positions dropped (NOT the same r). *)
Lemma V_mopen : forall T A B, mopen T A B ->
  forall r g v, Vc r T g -> (V r A v <-> V (sdrop (keyLen T) r) B v).
Proof.
  intros T A B Hm. induction Hm; intros r g v HVT; simpl.
  - apply V_ext. intro n. unfold sdrop. f_equal. lia.
  - simpl in HVT. destruct HVT as (E&w&Heq&HET&Hw). exact (IHHm r E v HET).
  - simpl in HVT. destruct HVT as (E & T0 & B0 & Heq & HET & Hpin).
    specialize (IHHm (stail r) E v HET) as IH.
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

(* Vc-based record projection: under a CONTEXT realization, field lookup yields a
   value in V of the (mopen-corrected) field type read at the sdrop'd env. *)
(* The subject of an rlk derivation is lshape whenever it is well-formed.
   (The left spine bottoms out env-shaped, and we_and / we_ands / we_rcd
   each expose the lshape of the left component.) *)
Lemma rlk_wft_lshape : forall T1 l A, rlk T1 l A ->
  forall T0, wft T0 T1 -> lshape T1.
Proof.
  introv Hr. induction Hr; introv Hw; unfold wft in Hw; inverts Hw;
    match goal with H : lshape _ |- _ => apply lsh_evar; exact H end.
Qed.

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
  - simpl in HV. destruct HV as (E & T0' & B0 & Heq & HET1 & Hpin). subst g.
    inverts Hw. destruct (IHHrlk T0 ltac:(unfold wft; eassumption) (stail r) E (goodr_stail Hg) HET1) as (v2 & Hlk & HBv2).
    exists v2. split.
    + apply rvl_left_t. exact Hlk.
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

(* multistep congruences for the env-extension forms ,, and ;; *)
Lemma mstep_mrgl : forall g E E' e, value g -> mstep g E E' -> mstep g (E ,, e) (E' ,, e).
Proof. introv Hv H. induction H; auto. eapply mstep_step; [ apply ls_mrgl; eauto | eauto ]. Qed.

Lemma mstep_mrgr : forall g E e e', value g -> value E -> mstep (g ++- E) e e' -> mstep g (E ,, e) (E ,, e').
Proof.
  introv Hv HE H. remember (g ++- E) as ge eqn:Hge. induction H; subst.
  - apply mstep_base. auto.
  - eapply mstep_step; [ apply ls_mrgr; [ exact Hv | exact HE | exact H ] | ]. apply IHmstep; auto.
Qed.

Lemma mstep_t_mrgl : forall g E E' A, value g -> mstep g E E' -> mstep g (E ;; A) (E' ;; A).
Proof. introv Hv H. induction H; auto. eapply mstep_step; [ apply ls_t_mrgl; eauto | eauto ]. Qed.

(* env-type value intro: appending a value binding realizes the combined env-type T1 & A. *)
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

(* env-type manifest intro: appending a type binding A realizes T1 &= A. *)
Lemma comp_const : forall T T1 E A,
  sem T E T1 -> lshape T1 -> wft (T +++ T1) A -> sem T (E ;; A) (T1 &= A).
Proof.
  unfold sem. introv Hs1 Hl Hwft Hg HV.
  assert (value g) as Hvg by (eapply Vc_value; eauto).
  destruct (Hs1 r g Hg HV) as (E0 & HmE & HvE0 & HVT1).
  destruct (@V_to_Vc T1 r E0 Hl Hg HVT1) as (r1' & Hgr1' & Hcond1 & HVc1).
  destruct (is_box_dec A) as [Hib | Hnib].
  - destruct Hib as [T0 B0].
    exists (E0 ;; boxt T0 B0). splits.
    + apply (mstep_t_mrgl (boxt T0 B0) Hvg HmE).
    + apply lvconst; exact HvE0.
    + simpl. exists E0, T0, B0, r1'. splits;
        [ reflexivity | exact Hgr1' | exact HVc1 | exact Hcond1 ].
  - exists (E0 ;; boxt (c2g (g ++- E0)) A). splits.
    + eapply mstep_trans; [ apply (mstep_t_mrgl A Hvg HmE) | ].
      eapply mstep_step; [ apply ls_t_mrgr; [ exact Hvg | exact HvE0 | exact Hnib ] | apply mstep_base; exact Hvg ].
    + apply lvconst; exact HvE0.
    + simpl. exists E0, (c2g (g ++- E0)), A, r1'. splits;
        [ reflexivity | exact Hgr1' | exact HVc1 | exact Hcond1 ].
Qed.

(* ---- The fundamental theorem: syntactic typing entails semantic typing. --- *)
Theorem sem_sound : forall T e A, has_type T e A -> sem T e A.
Proof.
  induction 1;
    try solve [ eauto using comp_int, comp_var, comp_lam, comp_app, comp_blam,
                comp_tapp, comp_eq, comp_unit, comp_conse, comp_const, comp_rec ].
  - (* t_box *) eapply comp_box; [ exact IHhas_type1 | exact IHhas_type2 | ].
    eapply wfe_lshape; eapply typ_wfe; eauto.
  - (* t_clos *) eapply comp_clos; [ exact IHhas_type1 | exact IHhas_type2 | exact H1 | ].
    eapply wfe_lshape; eapply wfe_inv; eapply typ_wfe; eauto.
  - (* t_bclos *) eapply comp_bclos; [ exact IHhas_type1 | exact IHhas_type2 | exact H1 | ].
    eapply wfe_lshape; eapply wfe_sinv; eapply typ_wfe; eauto.
  - (* trproj *) eapply comp_proj; [ exact IHhas_type | exact H0 | ].
    eapply typ_ans_wft; eauto.
Qed.

(* ---- Corollary: semantic type safety / normalization. -------------------- *)
Corollary normalization : forall e A,
  has_type top e A -> exists v', mstep unit e v' /\ value v'.
Proof.
  introv Ht. apply sem_sound in Ht.
  destruct (Ht (fun _ _ => False) unit) as (v'&Hm&Hvv&_).
  - unfold goodr. intros n w HF. destruct HF.
  - simpl. reflexivity.
  - exists v'. auto.
Qed.
