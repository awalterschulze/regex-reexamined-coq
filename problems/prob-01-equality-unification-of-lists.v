(* Coq works in mysterious ways, Episode 1.

Some questions:

- how does Coq determine that the two different ways of writing the list

      x :: xs ++ ys = (x :: xs) ++ ys.

  are actually the same?

  In what sense is it the same?

  1. You can prove they are the same with eq_refl.
  2. It seems that they are the same for the unification tests.

 *)

Require Import List.

Section example_of_rewrite_problem.
  Context (X : Set).
  Parameter (xs ys : list X).
  Parameter (x : X).
  Parameter (get: (* this gets an element from a list *)
               forall (xs : list X),
                 {n : nat | n < length xs} -> X).

  Search (_ :: _ ++ _).
  Print app_comm_cons.
  (* We have the obvious lemma:

      app_comm_cons =
      fun (A : Type) (x y : list A) (a : A) => eq_refl
          : forall (A : Type) (x y : list A) (a : A), a :: x ++ y = (a :: x) ++ y

    And Coq seems capable of doing that rewrite under the hood, it seems,
    because this lemma below doesn't call anything else except just eq_refl.

    (So maybe my question is: how does eq_refl determine whether two things are equal?)
  *)

  Lemma trivial_or_not:
    forall (x : X) (xs ys : list X),
      x :: xs ++ ys = (x :: xs) ++ ys.
  Proof.
    intros.
    exact eq_refl.
  Defined.

  (* It also seems that unification works with both. *)
  Hypothesis P Q: Prop.
  Hypothesis (owiejf:
                forall (x : X) (xs ys : list X),
                  P -> ((x :: xs ++ ys) = nil)).
  Hypothesis (some_impl: Q -> P).

  Lemma just_try_to_apply_the_above:
    forall (x : X) (xs ys : list X),
      Q -> (x :: (xs ++ ys) = nil).
  Proof.
    intros.
    apply owiejf.
    apply some_impl. assumption.
  Qed.

  Lemma just_try_to_apply_the_above':
    forall (x : X) (xs ys : list X),
      Q -> (x :: xs ++ ys = nil).
  Proof.
    intros.
    apply owiejf.
    apply some_impl. assumption.
  Qed.

(* Coq seems to think this is trivially true...
   But then why was it having unification problems?
   And how does it know the two lists are the same?

   It think you would need to rely on the lemma

   *)
  Lemma what_I_want_to_prove:
    forall
      (x0 : X)
      (i : nat)
      (pf: i < length ((x :: xs) ++ ys)),
      (get ((x :: xs) ++ ys) (exist _ i pf))
      = (get (x :: xs ++ ys) (exist _ i pf)).
  Proof.
    intros.
    reflexivity.
  Qed.


  (* This lemma is obviously not true, but it demonstrates the difficulty. *)
  Lemma asdf:
    forall
      (x0 : X)
      (i : nat)
      (pf: i < length ((x :: xs) ++ ys)),
      x0 = (get ((x :: xs) ++ ys) (exist _ i pf)).
  Proof.
    assert ( (x :: xs) ++ ys = (x :: (xs ++ ys))) as Eqrewrite.
    apply app_comm_cons.

    (* No problem: rewrite, then intros *)
    rewrite Eqrewrite.
    intros.

  Abort. (* had to abort, because restart doesn't undo the rewrite! *)

  (* Same lemma as above, but now I try to rewrite after intros, which fails. *)
  Lemma asdf:
    forall
      (x0 : X)
      (i : nat)
      (pf: i < length ((x :: xs) ++ ys)),
      x0 = (get ((x :: xs) ++ ys) (exist _ i pf)).
  Proof.
    assert ( (x :: xs) ++ ys = (x :: (xs ++ ys))) as Eqrewrite.
    apply app_comm_cons.

    (* Big problem: intros, then rewrite; failes with an error that I found unintelligible. *)
    intros.
    Fail rewrite Eqrewrite.

    (* Can generalize to undo the intros *)
    generalize pf.
    rewrite Eqrewrite.

  Abort. (* had to abort, because restart doesn't undo the rewrite! *)

  (* TODO: in the original situation, I couldn't even generalize! I don't know why. *)

  (* But they are actually different! How can Coq sometimes seem to act as if
   they are in fact the same?
   Is Coq smart enough to use an assertion that two things are the same? I thought not. *)
  Unset Printing Notations.
  Check (x :: xs ++ ys). (* cons x (app xs ys) *)
  Check ((x :: xs) ++ ys). (* app (cons x xs) ys *)
  Set Printing Notations.


  (* Thought: maybe the reason is that List is implemented in some specific way?
   Let's try creating our own inductive list type. *)

  Inductive mylist: Type :=
  | nil : mylist
  | cons: X -> mylist -> mylist.

  Fixpoint mylist_app (xs ys: mylist): mylist :=
    match xs with
    | nil => ys
    | cons x0 xs' => cons x0 (mylist_app xs' ys)
    end.

  (* Lemma mylist_app_induction_step: *)
  (*   forall (ws: mylist) (w: X), *)
  (*     cons *)


  Proposition mylist_app_cons_comm:
    forall (ws zs: mylist) (w: X),
      mylist_app (cons w ws) zs
      = cons w (mylist_app ws zs).
  Proof. intros. exact eq_refl. Qed.

  Print mylist_app_cons_comm.

(* Strange, it's also true here. It does follow immediately from the definition.
 So maybe eq_refl automatically does some reductions? *)

  (* Suppose that we had an opaque definition,
  and a lemma that said that we had the property we want.
  Can we then just immediately use eq_refl? Probably not. *)
  Parameter (mylist_app':  mylist -> mylist -> mylist).
  Hypothesis (mylist_app_cons_comm':
               forall (ws zs: mylist) (w: X),
                 mylist_app' (cons w ws) zs
                 = cons w (mylist_app' ws zs)).

  Proposition asdfasodfij:
    forall (ws zs: mylist) (w: X),
      mylist_app' (cons w ws) zs
      = cons w (mylist_app' ws zs).
  Proof.
    intros.
    Fail exact eq_refl.

    apply mylist_app_cons_comm'.
  Qed.


End example_of_rewrite_problem.