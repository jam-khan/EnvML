Require Import Arith.
From Coq Require Import Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.EquivDec.


Inductive styp :=
  | Sint : styp
  | Stop : styp
  | Sarr : styp -> styp -> styp
  | Sand : styp -> styp -> styp
  | Srcd : string -> styp -> styp
  | Ssig : styp -> styp -> styp.

Inductive sop := Sapp | Swith | SDmrg | SNmrg | SMapp.

Inductive sexp :=
  | Sctx        : sexp  
  | Sunit       : sexp
  | Slit        : nat   -> sexp
  | Sbinop      : sop   -> sexp -> sexp -> sexp
  | Slam        : styp  -> sexp -> sexp
  | Sproj       : sexp  -> nat  -> sexp
  | SClos       : sexp  -> styp -> sexp -> sexp
  | SStruct     : styp  -> sexp -> sexp
  | Srec        : string -> sexp -> sexp
  | Srproj      : sexp -> string -> sexp
  | Slet        : sexp -> styp -> sexp -> sexp
  | Sopen       : sexp -> sexp -> sexp.

Inductive typ :=
  | int : typ
  | top : typ
  | arr : typ -> typ -> typ
  | and : typ -> typ -> typ
  | rcd : string -> typ -> typ.

Inductive op := app | box | mrg.

Inductive exp :=
  | ctx         : exp
  | lit         : nat -> exp
  | unit        : exp
  | binop       : op -> exp -> exp -> exp
  | lam         : typ -> exp -> exp
  | proj        : exp -> nat -> exp
  | clos        : exp -> typ -> exp -> exp
  | rec         : string -> exp -> exp
  | rproj       : exp -> string -> exp.

Fixpoint elaborate_typ (s : styp) : typ :=
  match s with
  | Sint       => int
  | Stop       => top
  | Sarr A B   => arr (elaborate_typ A) (elaborate_typ B)
  | Sand A B   => and (elaborate_typ A) (elaborate_typ B)
  | Srcd l A   => rcd l (elaborate_typ A)
  | Ssig A B   => arr (elaborate_typ A) (elaborate_typ B)
  end.

Inductive Slookup : styp -> nat -> styp -> Prop :=
  | Slzero : forall A B, 
      Slookup (Sand A B) 0 B
  | Slsucc : forall A B n C, 
      Slookup A n C -> 
      Slookup (Sand A B) (S n) C.


Inductive Slin: string -> styp -> Prop :=
  | Slin_rcd: forall A l, Slin l (Srcd l A)
  | Slin_andl: forall A B l,
      Slin l A ->
      Slin l (Sand A B)
  | Slin_andr: forall A B l,
     Slin l B ->
     Slin l (Sand A B).

Inductive Srlookup : styp -> string -> styp -> Prop :=
  | Srlzero : forall l B, 
      Srlookup (Srcd l B) l B
  | Slandl : forall A B C l, 
      Srlookup A l C ->
      Slin l A /\ ~ Slin l B ->
      Srlookup (Sand A B) l C
  | Slandr : forall A B C l, 
      Srlookup B l C ->
      ~ Slin l A /\ Slin l B ->
      Srlookup (Sand A B) l C.

Inductive elaborate_sexp : styp -> sexp -> styp -> exp -> Prop :=
  | infctx: forall E,
        elaborate_sexp E Sctx E ctx
  | infint: forall E n,
        elaborate_sexp E (Slit n) Sint (lit n)
  | infunit: forall E,
        elaborate_sexp E Sunit Stop unit
  | infproj: forall E n Se e A B,
      elaborate_sexp E Se B e ->
      Slookup B n A ->
      elaborate_sexp E (Sproj Se n) A (proj e n)
  | inflam: forall E A Se e B,
      elaborate_sexp (Sand E A) Se B e ->
      elaborate_sexp E (Slam A Se) (Sarr A B) (lam (elaborate_typ A) e)
  | infbox: forall E E' A Se1 Se2 e1 e2,
      elaborate_sexp E Se1 E' e1 ->
      elaborate_sexp E' Se2 A e2 ->
      elaborate_sexp E (Sbinop Swith Se1 Se2) A (binop box e1 e2)
  | infclos: forall E E' A B Se1 Se2 e1 e2,
      elaborate_sexp E Se1 E' e1 ->
      elaborate_sexp (Sand E' A) Se2 B e2 ->
      elaborate_sexp E (SClos Se1 A Se2) (Sarr A B) (binop box e1 (lam (elaborate_typ A) e2))
  | infapp: forall E A B sE1 sE2 cE1 cE2,
      elaborate_sexp E sE1 (Sarr A B) cE1 ->
      elaborate_sexp E sE2 A cE2 ->
      elaborate_sexp E (Sbinop Sapp sE1 sE2) B (binop app cE1 cE2)
  | infdmrg: forall E A1 A2 sE1 sE2 e1 e2, 
      elaborate_sexp E sE1 A1 e1 ->
      elaborate_sexp (Sand E A1) sE2 A2 e2 ->
      elaborate_sexp E (Sbinop SDmrg sE1 sE2) (Sand A1 A2) (binop mrg e1 e2)
  | infnmrg: forall E A1 A2 sE1 sE2 e1 e2,
      elaborate_sexp E sE1 A1 e1 ->
      elaborate_sexp E sE2 A2 e2 ->
      elaborate_sexp E  (Sbinop SNmrg sE1 sE2)
                        (Sand A1 A2)
                        (binop app (lam (elaborate_typ E)
                                        (binop mrg 
                                               (binop box (proj ctx 0) e1)
                                               (binop box (proj ctx 1) e2))) ctx)
  | infstruct: forall E A B sE cE,
      elaborate_sexp (Sand Stop A) sE B cE ->
      elaborate_sexp E (SStruct A sE) (Ssig A B) (binop box unit (lam (elaborate_typ A) cE))
  | infmodapp: forall E A B sE1 sE2 e1 e2,
      elaborate_sexp E sE1 (Ssig A B) e1  ->
      elaborate_sexp E sE2 A e2           ->
      elaborate_sexp E (Sbinop SMapp sE1 sE2) B (binop app e1 e2)
  | infrcd: forall E A Se l e,
      elaborate_sexp E Se A e ->
      elaborate_sexp E (Srec l Se) (Srcd l A) (rec l e)
  | infrproj: forall E A B Se e l,
      elaborate_sexp E Se B e ->
      Srlookup B l A ->
      elaborate_sexp E (Srproj Se l) A (rproj e l)
  | inflet: forall E A B Se1 Se2 e1 e2,
      elaborate_sexp E Se1 A e1 ->
      elaborate_sexp (Sand E A) Se2 B e2 ->
      elaborate_sexp E (Slet Se1 A Se2) B (binop app (lam (elaborate_typ A) e2) e1)
  | infopen: forall E A B l Se1 e1 Se2 e2,
      Srlookup (Srcd l A) l A ->
      elaborate_sexp E Se1 (Srcd l A) e1 ->
      elaborate_sexp E (Srproj Se1 l) A (rproj e1 l) ->
      elaborate_sexp (Sand E A) Se2 B e2 ->
      elaborate_sexp E 
          (Sopen Se1 Se2) B 
          (binop app (lam (elaborate_typ A) e2) (rproj e1 l)).

Inductive lookup : typ -> nat -> typ -> Prop :=
  | lzero : forall A B, 
      lookup (and A B) 0 B
  | lsucc : forall A B n C, 
      lookup A n C -> 
      lookup (and A B) (S n) C.

Inductive value : exp -> Prop :=
  | vint    : forall n, value (lit n)
  | vunit   : value unit
  | vclos   : forall v A e, value v -> value (clos v A e)
  | vrcd    : forall l v, value v -> value (rec l v)
  | vmrg    : forall v1 v2, value v1 -> value v2 -> value (binop mrg v1 v2).

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
  | sbeta : forall v v1 v2 A e, 
      value v -> 
      value v1 ->
      value v2 -> 
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
Hint Constructors typ op exp lookup lookupv lin rlookup Slookup styp sop sexp elaborate_sexp has_type value rlookupv step : core.


Require Import Program.Equality.

Lemma type_elaboration_unique : forall E E' E'',
  elaborate_typ E = E' ->
  elaborate_typ E = E'' ->
  E' = E''.
Proof.
  intros E E' E'' H1 H2.
  generalize dependent E''.
  induction H1; intros E'' H2; try inversion H2; subst; try reflexivity;
    try ( apply IHelaborate_typ1 in H1;
          apply IHelaborate_typ2 in H4;
          rewrite H1; rewrite H4; reflexivity).
Qed.

Lemma type_safe_lookup : forall A n B,
  Slookup A n B ->
  lookup (elaborate_typ A) n (elaborate_typ B).
Proof.
  intros.
  induction H.
  + apply lzero.
  + simpl. apply lsucc.
    assumption.
Qed.

Lemma type_safe_lin : forall l B,
    Slin l B ->
    lin l (elaborate_typ B).
Proof.
  intros l B H.
  induction H.
  ++ simpl. apply lin_rcd.
  ++ simpl. apply lin_andl; assumption.
  ++ simpl. apply lin_andr; assumption.
Qed.

Lemma type_safe_lin1 : forall l B,
  lin l (elaborate_typ B) -> 
    Slin l B.
Proof.
  intros l B H.
  induction B.
  + simpl in H. inversion H.
  + simpl in H. inversion H.
  + simpl in H. inversion H.
  + simpl in H. inversion H; subst.
    ++ apply Slin_andl. apply IHB1. assumption.
    ++ apply Slin_andr. apply IHB2. assumption.
  + simpl in H. inversion H; subst.
    apply Slin_rcd.
  + simpl in H. inversion H; subst.
Qed.

Lemma type_safe_lin_equivalence : forall l B,
  Slin l B <-> lin l (elaborate_typ B).
Proof.
  split.
  apply type_safe_lin.
  apply type_safe_lin1.
Qed.

Lemma neg_type_safe_lin : forall l B,
    ~ Slin l B ->
    ~ lin l (elaborate_typ B).
Proof.
  intros l B H.
  unfold not.
  unfold not in H.
  intros.
  apply type_safe_lin1 in H0.
  apply H; assumption.
Qed.

Lemma type_safe_rlookup : forall A l B,
  Srlookup A l B ->
  rlookup (elaborate_typ A) l (elaborate_typ B).
Proof.
  intros.
  induction H.
  + simpl.
    apply rlzero.
  + simpl.
    apply landl.
    ++ assumption.
    ++ apply neg_type_safe_lin. destruct H0. assumption.
  + simpl.
    apply landr.
    ++ assumption.
    ++ apply neg_type_safe_lin. destruct H0. assumption.
Qed.

(* -------------------------Elaboration--------------------------- *)
(*  Type Preservation *)
Theorem type_preservation : forall E SE A CE,
  elaborate_sexp E SE A CE ->
  has_type (elaborate_typ E) CE (elaborate_typ A).
Proof.
  intros E SE A CE H.
  induction H.
  + apply tctx.
  + apply tint.
  + apply tunit.
  + apply tproj with (A := (elaborate_typ B)).
    - assumption.
    - apply type_safe_lookup in H0. assumption.
  + simpl.
    apply tlam.
    simpl in IHelaborate_sexp. assumption.
  + simpl in IHelaborate_sexp1.
    simpl in IHelaborate_sexp2.
    apply tbox with (E1 := (elaborate_typ E')); try assumption.
  + simpl. 
    apply tbox with (E1 := (elaborate_typ E')).
    ++ assumption.
    ++ simpl in IHelaborate_sexp2. apply tlam. assumption.
  + simpl in IHelaborate_sexp1.
    simpl in IHelaborate_sexp2.
    apply tapp with (A := (elaborate_typ A)).
    ++ assumption.
    ++ assumption.
  + simpl in IHelaborate_sexp1.
    simpl in IHelaborate_sexp2.
    apply tmrg; try assumption.
  + simpl.
    apply tapp with (A := (elaborate_typ E)).
    ++ apply tlam.
       apply tmrg.
       - apply tbox with (E1 := (elaborate_typ E)).
         -- apply tproj with (A := and (elaborate_typ E) (elaborate_typ E)).
            * apply tctx.
            * apply lzero.
         -- assumption.
      - apply tbox with (E1 := (elaborate_typ E)).
        -- apply tproj with (A := (and (and (elaborate_typ E) (elaborate_typ E)) (elaborate_typ A1))).
            * apply tctx.
            * apply lsucc. apply lzero.
        -- assumption.
    ++ apply tctx.
  + simpl.
    simpl in IHelaborate_sexp.
    apply tbox with (E1:= top).
    - apply tunit.
    - apply tlam; assumption.
  + simpl.
    simpl in IHelaborate_sexp1.
    simpl in IHelaborate_sexp2.
    apply tapp with (A := elaborate_typ A); try assumption.
  + simpl.
    apply trcd. assumption.
  + simpl.
    apply trproj with (elaborate_typ B). 
    ++ assumption.
    ++ apply type_safe_rlookup in H0; assumption.
  + simpl.
    simpl in IHelaborate_sexp2.
    apply tapp with (A := elaborate_typ A); try assumption.
    apply tlam; try assumption.
  + simpl in IHelaborate_sexp2.
    apply type_safe_rlookup in H.
    apply tapp with (elaborate_typ A).
    ++ apply tlam. simpl in IHelaborate_sexp3.
       assumption.
    ++ assumption.
Qed.


(* Uniqueness of look-up *)
Lemma uniqueness_of_Slookup : forall E n A1 A2,
  Slookup E n A1 ->
  Slookup E n A2 ->
  A1 = A2.
Proof.
  intros E n A1 A2 H1 H2.
  generalize dependent A2.
  induction H1; intros; inversion H2; subst; eauto.
Qed.

Lemma uniqueness_of_Srlookup : forall E l A1 A2,
  Srlookup E l A1 ->
  Srlookup E l A2 ->
  A1 = A2.
Proof.
  intros E l A1 A2 H1 H2.
  generalize dependent A2.
  induction H1; intros.
  + inversion H2; subst; reflexivity.
  + inversion H2; subst. 
    - apply IHSrlookup; assumption.
    - destruct H. destruct H7.
      exfalso. apply H0. assumption.
  + inversion H2; subst.
    - apply IHSrlookup.
      destruct H7; destruct H.
      exfalso. apply H3. assumption.
    - apply IHSrlookup; assumption.
Qed.

(* Uniqueness of type-inference *)
Theorem uniqueness_of_inference : forall E SE A1 A2 CE1 CE2,
  elaborate_sexp E SE A1 CE1 ->
  elaborate_sexp E SE A2 CE2 ->
  A1 = A2.
Proof.
  intros E SE A1 A2 CE1 CE2 H1 H2.
  generalize dependent A2.
  generalize dependent CE2.
  induction H1; intros; inversion H2; subst; eauto.
  + apply IHelaborate_sexp in H5.
    rewrite H5 in H.
    apply uniqueness_of_Slookup with B0 n; try assumption.
  + apply IHelaborate_sexp in H6. rewrite H6; reflexivity.
  + apply IHelaborate_sexp1 in H3.
    symmetry in H3. rewrite H3 in H6.
    apply IHelaborate_sexp2 in H6; assumption.
  + apply IHelaborate_sexp1 in H6. symmetry in H6. rewrite H6 in H7.
    apply IHelaborate_sexp2 in H7. rewrite H7. reflexivity.
  + apply IHelaborate_sexp2 in H6. symmetry in H6. rewrite H6 in H3.
    apply IHelaborate_sexp1 in H3. inversion H3; subst; reflexivity.
  + apply IHelaborate_sexp1 in H3.
    symmetry in H3. rewrite H3 in H6.
    apply IHelaborate_sexp2 in H6.
    rewrite H3. rewrite H6. reflexivity.
  + apply IHelaborate_sexp1 in H3. rewrite H3.
    rewrite H3 in IHelaborate_sexp1.
    inversion H3; subst.
    inversion H2; subst. apply IHelaborate_sexp2 in H10. rewrite H10.
    reflexivity.
  + apply IHelaborate_sexp in H6. rewrite H6. reflexivity.
  + apply IHelaborate_sexp2 in H6.
    apply IHelaborate_sexp1 in H3.
    subst. inversion H3; subst; eauto.
  + apply IHelaborate_sexp in H6; subst; eauto.
  + apply IHelaborate_sexp in H5; subst; eauto.
    apply uniqueness_of_Srlookup with B0 l; try assumption.
  + apply IHelaborate_sexp1 in H4; subst.
    inversion H4; subst.
    apply IHelaborate_sexp3 in H9. assumption.
Qed.

(* Uniqueness of Elaboration *)
Theorem uniqueness_of_elaboration : forall E SE A1 A2 CE1 CE2,
  elaborate_sexp E SE A1 CE1 ->
  elaborate_sexp E SE A2 CE2 ->
  CE1 = CE2.
Proof.
  intros E SE A1 A2 CE1 CE2 H1 H2.
  generalize dependent A2.
  generalize dependent CE2.
  induction H1; intros; inversion H2; subst; eauto; 
  try ( apply IHelaborate_sexp in H6; subst; reflexivity );
  try ( apply IHelaborate_sexp in H5; subst; reflexivity );
  try ( apply IHelaborate_sexp1 in H3; subst;
        apply IHelaborate_sexp2 in H6; subst; reflexivity ).
  + assert ( Eq : E' = E'0 ). 
    {
     apply uniqueness_of_inference with (E := E) (SE := Se1) (CE1 := e1) (CE2 := e0); 
     try assumption; 
     subst. 
    }
    apply IHelaborate_sexp1 in H3; subst.
    apply IHelaborate_sexp2 in H6; subst; reflexivity.
  + assert ( Eq : E' = E'0 ). 
    {apply uniqueness_of_inference with (E := E) (SE := Se1) (CE1 := e1) (CE2 := e0); 
     try assumption; 
     subst. }
    apply IHelaborate_sexp1 in H6; subst.
    apply IHelaborate_sexp2 in H7; subst; reflexivity.
  + assert ( Eq : A1 = A3 ).
    { apply uniqueness_of_inference with E sE1 e1 e0; try assumption; subst. }
    apply IHelaborate_sexp1 in H3; subst.
    apply IHelaborate_sexp2 in H6; subst; reflexivity.
  + apply IHelaborate_sexp1 in H6; subst.
    apply IHelaborate_sexp2 in H7; subst.
    reflexivity.
  + assert (Eq : (Srcd l0 A0) = (Srcd l A)).
    { apply uniqueness_of_inference with (E := E) (SE := Se1) (CE1 := e0) (CE2 := e1).
      - assumption.
      - assumption. }
    inversion Eq; subst.
    apply IHelaborate_sexp2 in H6; inversion H6; subst.
    apply IHelaborate_sexp3 in H9; subst.
    reflexivity.
Qed.
