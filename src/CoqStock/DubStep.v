(* DubStep
   "Beware of the drop!"

   Essentially the dubstep tactic folds and unfolds a targeted function.
   It sounds like this would not really do much,
   but if used correctly it makes the targeted function take a step forward.
   Unlike the cbn and simpl tactics, which would make all functions calculate as much as they can.

   If you are unfamiliar with dubstep, here is a tutorial:
   [UKF Dubstep Tutorial - Dubba Jonny](https://www.youtube.com/watch?v=CJzfTZlEl40)
*)

Ltac dubstep_goal F :=
  unfold F; fold F.

Ltac dubstep_in F H :=
  unfold F in H; fold F in H.

Tactic Notation "dubstep" constr(F)  := (dubstep_goal F).
Tactic Notation "dubstep" constr(F) "in" hyp(H) := (dubstep_in F H).

Require Import Nat.
Require Import Arith.

Fixpoint sum_n (n: nat): nat :=
  match n with
  | O => 0
  | (S n') => n + sum_n n'
  end.

Example example_sum_n_is_n_mul_sn: forall (n: nat),
  2 * sum_n n = n * (n + 1).
Proof.
induction n.
- simpl.
  reflexivity.
- (* 2 * sum_n (S n) = S n * (S n + 1) *)
  dubstep sum_n.
  (* 2 * (S n + sum_n n) = S n * (S n + 1) *)
  rewrite Nat.mul_add_distr_l.
  rewrite IHn.
  ring.
Qed.
   