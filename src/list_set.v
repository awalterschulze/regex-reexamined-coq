(* This file contains some definitions and lemmas on using lists as sets. Mainly
   we want to know whether two lists have the same set of elements (see the
   definition of `list_set_eq`).
 *)

(* TODO: Help Wanted: isn't there some library that more or less does this?
   The ones I found don't seem to have a notation of equality of sets. *)

Set Implicit Arguments.
Set Asymmetric Patterns.

Require Import List.
Import ListNotations.

Section list_set_eq.
  Context {A: Type}.

  Definition list_set_eq (xs ys : list A): Prop :=
    forall (a : A), (In a xs) <-> (In a ys).

  Hint Unfold list_set_eq: list_set_db.

  (* Hint Extern extends an auto database with a tactic.
   You can specify a cost (the natural number 0 in this case) and a
   pattern to apply the tactic to.
   See https://coq.inria.fr/refman/proof-engine/tactics.html#coq:cmdv.hint-extern *)
  Hint Extern 0 (_ <-> _) => split : list_set_db.

  Lemma list_set_eq_refl (xs: list A):
    list_set_eq xs xs.
  Proof.
    auto with list_set_db.
  Qed.

  Hint Resolve list_set_eq_refl: list_set_db.

  Lemma list_set_eq_symm (xs ys: list A):
    list_set_eq xs ys <-> list_set_eq ys xs.
  Proof.
    easy.
    (* Interesting note: auto doesn't solve this (even auto 10), but easy does. *)
  Qed.

  Lemma list_set_eq_step (a : A) (xs: list A):
    list_set_eq (a::xs) (a::(a::xs)).
  Proof.
(* From the manual: "This tactic unfolds constants that were declared through a
   Hint Unfold in the given databases."
   https://coq.inria.fr/distrib/current/refman/proof-engine/tactics.html#coq:tacn.autounfold

   In this case, I wanted to unfold list_set_eq. (We did `Hint Unfold list_set_eq:
   list_set_db.` before.)
 *)
    autounfold with list_set_db.
    intros.
    split.
    - intro H.
      unfold In.
      auto.
    - intro H.
      unfold In in *.
      destruct H; auto.
      (* TODO: Help Wanted
         Is there a way to do this entire proof in an automatised way?
         We're only introducing, unfolding and destructing the logical disjunction H.
       *)
  Qed.

  Lemma list_set_eq_trans (xs ys zs : list A):
    list_set_eq xs ys
    -> list_set_eq ys zs
    -> list_set_eq xs zs.
  Proof.
    intros.
    unfold list_set_eq in *.
    intro.
    split.
    - intro.
      auto using H, H0 with list_set_db.
      (* TODO: Help Wanted
         How can the above auto statement fail to just apply the hints
         I told it to apply?
         The Coq manual does say (https://coq.inria.fr/distrib/current/refman/proof-engine/tactics.html#automation):

         "auto uses a weaker version of apply that is closer to simple apply so it
         is expected that sometimes auto will fail even if applying manually one
         of the hints would succeed."

         And indeed, `simple apply H0` does not work. So maybe that is the reason?

         But then that raises the question: how do we get it to work? Should be
         possible.
       *)
      apply H0.
      apply H.
      assumption.
    - intro.
      apply H.
      apply H0.
      assumption.
  Qed.

  Lemma list_set_eq_ind_step (xs ys: list A) (x : A):
    list_set_eq xs ys ->
    list_set_eq (x::xs) (x::ys).
  Proof.
    intros.
    unfold list_set_eq.
    intros.
    split.
    - intros H0.
      destruct H0.
      + subst. cbn. auto.
      + subst. cbn. right.
        apply H. assumption.
    - intros H0.
      destruct H0.
      + subst. cbn. auto.
      + subst. cbn. right.
        apply H. assumption.
  Qed.
End list_set_eq.
