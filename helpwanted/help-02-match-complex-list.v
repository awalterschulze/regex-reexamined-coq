Require Import List.
Import ListNotations.

Parameter (A : Type).
Variable (x : A).
Variables (xs ys : list A).

Goal x = x. (* this is just to enter proof mode *)
  remember ((x :: xs) ++ ys) as foo.

  (* QUESTION: why do these matches fail? *)
  Fail match foo with
  | ((?x :: ?xs0) ++ ?xs1) => idtac "Yep" x xs0 xs1
  end.

  Fail match foo with
  | (?xs0 ++ ?xs1) => idtac "Yep" xs0 xs1
  end.

  (* I was mostly trying to do this to troubleshoot some tactics. Specifically, I wanted to match something
     of type

          S i < length ((x::xs) ++ ys)

   *)

  (* It looks like it just matches "foo"... *)
  match foo with
  | ?x =>  idtac x
  end.

Abort.


(* The motivation: *)
Lemma bar: forall (i: nat)
              (pf: (S i < length((x::xs) ++ ys))),
    1 = 1.
Proof.
  intros.

  match type of pf with
  | (S ?n < length(?xs ++ ?ys)) => idtac "Found" n xs ys
  end.

  match type of pf with
  | (S ?n < length((?x :: ?xs) ++ ?ys)) => idtac "Found" n x xs ys
  end.

  (* I don't want this to fail, because (in my situation) I can't rewrite the hypothesis. *)
  Fail match type of pf with
       | S ?n < length (?x :: ?xs) => idtac "Found" n x xs
       end.

  match type of pf with
  | (S ?n < length(?xs ++ ?ys)) => idtac "Found" n xs ys
  end.

  match type of pf with
  | (S ?n < length((?x :: ?xs) ++ ?ys)) => idtac "Found" n x xs ys
  end.

  Fail match type of pf with
       | S ?n < length (?x :: ?xs) => idtac "Found" n x xs
       end.
Abort.