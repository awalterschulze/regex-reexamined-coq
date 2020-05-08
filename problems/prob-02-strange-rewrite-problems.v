(*

Two problems:

1. Strange error message, that seems to say I cannot apply something,
   while I actually can if I just provide enough withs.

2. In some situations, it seems impossible to do a rewrite.
   This cause seems to be that there is some hypothesis that's being used in the goal, and you can't just rewrite the hypothesis.

 *)


(* TODO:

- example of erewrite for those who are not familiar with it
- intro better

*)

Require Import List.
Import ListNotations.

Section example_of_rewrite_problem.
  Context (X : Set).
  Parameter (get: (* this gets an element from a list *)
               forall (xs : list X),
                 {n : nat | n < length xs} -> X).

  (* With eq_refl, you can see that these two things are the same: *)
  Lemma list_cons_app_commute:
    forall (xs ys: list X) (x: X),
      (x :: (xs ++ ys)) = ((x::xs) ++ ys).
  Proof.
    intros.
    exact eq_refl.
  Qed.

  (* There is also a built-in lemma that shows this. (I included the lemma above
   to show that you can simply prove it with eq_refl.) *)
  Print app_comm_cons.


  (* Assume we have proven the following lemma: *)
  Lemma get_from_tail:
    forall (xs : list X) (x: X)
           (i : nat)
           (pf: i < length xs)
           (pf': (S i) < length (x::xs)),
      (get (x::xs) (exist _ (S i) pf')) =
      (get xs (exist _ i pf)).
  Proof. Admitted.

  (* This corollary shows the first problem: a misleading error message. *)
  Corollary get_from_tail_corollary:
    forall (xs ys: list X) (x: X)
           (i : nat)
           (pf: i < length (xs ++ ys))
           (pf': (S i) < length ((x :: xs) ++ ys)),
      get ((x::xs) ++ ys) (exist _ (S i) pf')
          = get (xs ++ ys) (exist _ i pf).
  Proof.
    (* Then this follows directly. *)
    intros.
    apply get_from_tail.

    (* But suppose we were a bit stupid and wanted to first rewrite with
    get_from_tail, and then just use reflexivity. *)
    Restart.
    intros.
    (* It's maybe not so strange that this next tactic fails, but what does
    surprise me is the error message: "Found no subterm matching ...." *)
    Fail rewrite get_from_tail.
    (* It doesn't even work if you ask it to get evars for you. *)
    Fail unshelve erewrite get_from_tail.
    (* But this does succeed: *)
    rewrite get_from_tail with (x := x) (xs := (xs ++ ys)) (pf := pf).

    (* This I find very strange: if the erewrite fails, then rewrite ... with
    ... shouldn't be able to succeed! *)

    (* We can now finish the proof with reflexivity. *)
    reflexivity.
  Qed.


  (* On the rewriting issues: *)
  (* Below are two lemmas, that I don't want to prove (they are false),
     but that provide just enough context to show the problem I was having.

They are here for historical context: they were similar to the situation that
I was in when I encountered the above problems

The problem I had, was that I wanted to rewrite the goal with get_from_tail,
but for some reason, I couldn't.

The lemmas differ in only one aspect: one uses

    (x :: (xs ++ ys))

whereas the other uses

    ((x :: xs) ++ ys)

However, as we've seen, these two terms are equal by eq_refl,
so that shouldn't be too much of a problem.
   *)

  (* This lemma is only there to be compared with the next. *)
  Lemma get_from_tail_test:
    forall (xs ys: list X) (x: X)
           (i : nat)
           (pfdec: i < length (xs ++ ys))
           (pf: (S i) < length (x :: (xs ++ ys))),
      get (x::(xs ++ ys)) (exist _ (S i) pf)
          = x.
  Proof.
    intros.
    Fail rewrite get_from_tail.
    (* This failed because it couldn't find an instance for the variable pf.
    So let's just give it. *)
    rewrite get_from_tail with (pf := pfdec).

    (* That worked. If we had wanted to use the proof assistant to help us find
    pfdec, we could have done that like this: *)
    Undo.
    unshelve erewrite get_from_tail.
    exact pfdec. (* <- this could have been much more difficult, of course *)
  Abort.

  (* This shows the first issue: why can't I replace? *)
  Lemma get_from_tail_test':
    forall (xs ys: list X) (x: X)
           (i : nat)
           (pfdec: i < length (xs ++ ys))
           (pf: (S i) < length ((x :: xs) ++ ys)),
      get ((x::xs) ++ ys) (exist _ (S i) pf)
          = x.
  Proof.
    intros.

    (* Suppose I wanted to rewrite all occurences of ((x::xs) ++ ys) with (x ::
    (xs ++ ys)). Why doesn't this work? *)
    replace ((x::xs) ++ ys) with (x :: (xs ++ ys)). (* This doesn't replace anything! *)
    replace ((x::xs) ++ ys) with (x :: (xs ++ ys)) in pf. (* This doesn't replace anything either! But neither of them shows an error... *)

    (* Why doesn't this work? *)
    Fail rewrite <- list_cons_app_commute.
    (* "A metavariable has several occurences." *)


    (* ----------- *)
    (* But as before, we can just apply get_from_tail by giving enough
    arguments. *)
    (* This fails, as we saw in the corollary. *)
    Fail rewrite get_from_tail.

    (* And as in the corollary, if we give it some hints, it works. *)
    rewrite get_from_tail with
        (x := x)
        (xs := (xs ++ ys))
        (pf := pfdec).

    (* Unfortunately, . *)
    Undo.
    Fail unshelve erewrite get_from_tail.
  Abort.
End example_of_rewrite_problem.

Section simple_rewrite_example.
  (* TODO: not yet complete. *)
  Context (A: Type).

  Parameter (a b : A).
  Hypothesis (EqRewrite : a = b).
  Parameter (P: A -> Prop).

  Parameter (Q: forall a: A,
            P a -> Prop).

  Lemma plz:
    forall (pf : P a),
      P b -> (Q a pf).
  Proof.
    intros.

    (* Cannot change; used in conclusion *)
    Fail rewrite EqRewrite in pf.

    (* Quite difficult error message... *)
    Fail rewrite EqRewrite.

    (* This doesn't do anything, but doesn't fail. *)
    replace a with b.
  Abort.
End simple_rewrite_example.


Section github_issue.
  (* Maybe I've just encountered this bug (?): *)
  (* https://github.com/coq/coq/issues/7744 *)
  Parameters A B : Prop.
  Goal A /\ B.
    Fail apply (fun a b => conj a (b a)).
    (* Gives the same error message as I've been getting. *)
  Abort.
End github_issue.
