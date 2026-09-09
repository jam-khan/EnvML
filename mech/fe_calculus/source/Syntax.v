Require Import LibTactics.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
Require Import Stdlib.Lists.List.
From Stdlib Require Import Strings.String.
Import ListNotations.
Require Export Teq ExpSyntax Semantics Safety.
Set Implicit Arguments.

(* Nameless EnvML: only the module layer is new.  A signature IS an FE type
   (typ) and a declaration body IS an FE term (exp), so there is no separate
   signature syntax and no signature equivalence. *)

Inductive smod :=
  | s_var    : nat -> string -> smod      (* module variable, reached by label *)
  | s_fun    : typ -> smod -> smod        (* functor (x : A) -> M *)
  | s_tfun   : smod -> smod               (* functor (type t) -> M *)
  | s_app    : smod -> smod -> smod
  | s_tapp   : smod -> typ -> smod
  | s_struct : sdecl -> smod
  | s_box    : smod -> smod               (* sandbox *)
  | s_merge  : smod -> smod -> smod
with sdecl :=
  | d_nil : sdecl
  | d_val : sdecl -> string -> exp -> sdecl
  | d_typ : sdecl -> typ -> sdecl
  | d_mod : sdecl -> string -> smod -> sdecl.

#[export] Hint Constructors smod sdecl : core.

(* ------------------------------------------------------------------ *)
(* Signature shape.                                                     *)
(*                                                                      *)
(* A merge operand's signature must be manifest: every entry is either a *)
(* labelled component (rcd l A) or a transparent type component (&= A).  *)
(* An abstract entry (&s) cannot be rebuilt by projection, and a nested  *)
(* environment entry would need rlk_right; the prototype already forbids *)
(* both, so neither arises.                                             *)

Inductive sig_shape : typ -> Prop :=
  | ss_nil : sig_shape top
  | ss_lbl : forall G l A, sig_shape G -> sig_shape (G & (rcd l A))
  | ss_typ : forall G A, sig_shape G -> sig_shape (G &= A).

#[export] Hint Constructors sig_shape : core.

(* The labels a signature binds, and its type entries, as predicates. *)

Inductive has_lbl : typ -> string -> typ -> Prop :=
  | hl_here  : forall G l A, has_lbl (G & (rcd l A)) l A
  | hl_lbl   : forall G l A l1 A1,
      has_lbl G l A -> l <> l1 -> has_lbl (G & (rcd l1 A1)) l A
  | hl_typ   : forall G l A B, has_lbl G l A -> has_lbl (G &= B) l A.

#[export] Hint Constructors has_lbl : core.

(* Disjointness: no label is bound twice.  This is what makes every labelled
   component of a merge operand recoverable, and it is exactly the condition
   checkComposable enforces in the implementation. *)

Inductive unique_labels : typ -> Prop :=
  | ul_nil : unique_labels top
  | ul_lbl : forall G l A,
      unique_labels G -> ~ lb_in l G -> unique_labels (G & (rcd l A))
  | ul_typ : forall G A, unique_labels G -> unique_labels (G &= A).

#[export] Hint Constructors unique_labels : core.
