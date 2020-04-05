(* orb_simple is a module specifically created for the orb_simple tactic,
   which simplifies orb expressions.
*)

Set Implicit Arguments.
Set Asymmetric Patterns.

Require Import Bool.

(* orb_reorder_and_remove_duplicates matches specific instances of orb combinators
   it then reorders then and remove duplicates with the hope that this would
   make proving equality easier.
*)
Ltac orb_reorder_and_remove_duplicates :=
  match goal with
    | [ |- ?A || (?A || ?B) = _ ] => rewrite orb_assoc; rewrite orb_diag
      (* a || (a || b) = _ => a || b = _ *)
    | [ |- ?A || ?B = ?B || ?A ] => rewrite orb_comm
      (* a || b = b || a => b || a = b || a *)
    | [ |- ?A || ?B || ?A = ?A || ?B ] =>
      (* a || (a || b) = a || b => a || b = a || b *)
      rewrite orb_comm;
      rewrite orb_assoc;
      rewrite orb_diag
    | [ |- ?A || ?B || ?C = ?A || (?B || ?C) ] => rewrite orb_assoc
      (* a || b || c = a || (b || c) => a || b || c = a || b || c *)
    | [ |- ?A || (?B || ?C) = ?B || (?A || ?C) ] =>
      (* a || (b || c) = b || (a || c) => b || (c || a) = b || (c || a) *)
      rewrite orb_comm;
      rewrite <- orb_assoc;
      rewrite orb_comm with (b1 := (A))
    | [ |- ?A || ?B || (?A || ?C) = _ ] =>
      (* a || b || (a || c) =_ => c || b || a = _ *)
      rewrite orb_assoc;
      rewrite orb_comm;
      rewrite orb_assoc;
      rewrite orb_comm with (b1 := A);
      rewrite orb_assoc;
      rewrite <- orb_assoc;
      rewrite orb_diag
    | [ |- ?C || ?B || ?A = ?A || (?B || ?C) ] =>
      (* c || b || a = a || (b || c) => a || (c || b) = a || (c || b) *)
      rewrite orb_comm;
      rewrite orb_comm with (b1 := B)
    | [ |- _ = ?A || ?D || (?B  || (?C  || ?D )) ] =>
      (* _ = a || d || (b || (c || d )) => _ = a || b || c || d *)
      rewrite orb_comm with (b1 := A) (b2 := D);
      repeat rewrite <- orb_assoc;
      rewrite orb_comm with (b1 := D);
      repeat rewrite <- orb_assoc;
      rewrite orb_diag;
      repeat rewrite orb_assoc
  end.

(* orb_simple combines a lot of orb tactics to simplify orb expressions. *)
Ltac orb_simple := repeat
  (  rewrite orb_diag
  || rewrite orb_false_r
  || rewrite orb_false_l
  || orb_reorder_and_remove_duplicates
).

Theorem test_tactic_or_cases_commutativity: forall (a b: bool),
  a || b = b || a.
Proof.
intros.
orb_reorder_and_remove_duplicates.
reflexivity.
Qed.

Theorem test_tactic_or_cases_idempotency_1: forall (a b: bool),
  a || (a || b) = a || b.
Proof.
intros.
orb_reorder_and_remove_duplicates.
reflexivity.
Qed.

Theorem test_tactic_or_cases_idempotency_2: forall (a b: bool),
  a || b || a = a || b.
Proof.
intros.
orb_reorder_and_remove_duplicates.
reflexivity.
Qed.

Theorem test_tactic_or_cases_associativity_1: forall (a b c: bool),
  a || b || c = a || (b || c).
Proof.
intros.
orb_reorder_and_remove_duplicates.
reflexivity.
Qed.

Theorem test_tactic_or_cases_associativity_2: forall (a b c: bool),
  a || (b || c) = b || (a || c).
Proof.
intros.
orb_reorder_and_remove_duplicates.
reflexivity.
Qed.

Theorem test_tactic_or_cases_3: forall (a b c: bool),
  a || b || (a || c) = a || (b || c).
Proof.
intros.
repeat orb_reorder_and_remove_duplicates.
reflexivity.
Qed.

Theorem test_tactic_or_cases_4: forall (a b c d: bool),
  a  || b  || (c || d ) =
  a  || d || (b || (c || d )).
Proof.
intros.
orb_reorder_and_remove_duplicates.
reflexivity.
Qed.
