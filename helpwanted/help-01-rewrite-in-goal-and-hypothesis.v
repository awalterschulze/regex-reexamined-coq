(* I want to do a very simple rewrite, but for some reason, I'm getting a very
difficult error message. Search for "HELP WANTED" to find the exact location. *)

Require Import List.
Import ListNotations.

Section trivial_rewrite.
  (* Setup the same as before. *)
  Print All.
  Context (A : Set).
  Parameter (get: (* this gets an element from a list *)
               forall (xs : list A),
                 {n : nat | n < length xs} -> A).

  (* This lemma is not true, but is an example of what I wanted to do. *)
  Lemma help_wanted:
    forall (xs ys: list A) (x: A)
           (i : nat)
           (pf: i < length (xs ++ ys))
           (pf': (S i) < length ((x :: xs) ++ ys)),
      get ((x::xs) ++ ys) (exist _ (S i) pf')
          = get (xs ++ ys) (exist _ i pf).
  Proof.
    intros.
    (* HELP WANTED here:

       How do I replace

          ((x::xs) ++ ys)

      with

          (x :: (xs ++ ys)) ?
    *)

    (* First attempt: doesn't do anything. *)
    replace ((x::xs) ++ ys) with (x :: (xs ++ ys)). (* This doesn't replace anything! *)

    (* Second attempt: fails with difficult error message *)
    assert (((x::xs) ++ ys) = (x :: (xs ++ ys))) as Heq.
    exact eq_refl.
    Fail rewrite Heq.
  Abort.
End trivial_rewrite.