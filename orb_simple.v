Set Implicit Arguments.
Set Asymmetric Patterns.

Require Import Bool.

Ltac orb_reorder_and_remove_duplicates :=
  match goal with
    | [ |- ?A || (?A || ?B) = _ ] => rewrite orb_assoc; rewrite orb_diag
    | [ |- ?A || ?B = ?B || ?A ] => rewrite orb_comm
    | [ |- ?A || ?B || ?C = ?A || (?B || ?C) ] => rewrite orb_assoc
    | [ |- ?A || (?B || ?C) = ?B || (?A || ?C) ] =>
      rewrite orb_comm;
      rewrite <- orb_assoc;
      rewrite orb_comm with (b1 := (A))
    | [ |- ?A || ?B || ?A = ?A || ?B ] =>
      rewrite orb_comm;
      rewrite orb_assoc;
      rewrite orb_diag
    | [ |- ?A || ?B || (?A || ?C) = ?A || (?B || ?C) ] =>
      rewrite orb_assoc;
      rewrite orb_comm;
      rewrite orb_assoc;
      rewrite orb_comm with (b1 := A);
      rewrite orb_assoc;
      rewrite <- orb_assoc;
      rewrite orb_diag
    | [ |- ?C || ?B || ?A = ?A || (?B || ?C) ] =>
      rewrite orb_comm;
      rewrite orb_comm with (b1 := B)
    | [ |- _ = ?A || ?D || (?B  || (?C  || ?D )) ] =>
      rewrite orb_comm with (b1 := A) (b2 := D);
      repeat rewrite <- orb_assoc;
      rewrite orb_comm with (b1 := D);
      repeat rewrite <- orb_assoc;
      rewrite orb_diag;
      repeat rewrite orb_assoc
  end.

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
orb_simple.
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
