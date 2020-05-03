(* orb_simple is a module specifically created for the orb_simple tactic,
   which simplifies orb expressions.
*)

Set Implicit Arguments.
Set Asymmetric Patterns.

From Coq Require Import Ring.
Require Import Bool.

Lemma bool_semi_ring:
  semi_ring_theory false true orb andb (@eq bool).
Proof.
constructor.
exact Bool.orb_false_l.
exact Bool.orb_comm.
exact Bool.orb_assoc.
exact Bool.andb_true_l.
exact Bool.andb_false_l.
exact Bool.andb_comm.
exact Bool.andb_assoc.
exact Bool.andb_orb_distrib_l.
Qed.

Add Ring bool_semi_ring: bool_semi_ring
  (decidable bool_eq_ok, constants [bool_cst]).

(*
orb_simple is a tactic that repeatedly applies:
  - the semi ring with orb tactic
  - removes duplicates in or expressions
  - removes all false values in or expressions
*)
Ltac orb_simple := repeat
  ( ring
  || rewrite orb_diag
  || rewrite orb_false_r
  || rewrite orb_false_l
  ).

Theorem test_tactic_or_cases_commutativity: forall (a b: bool),
  a || b = b || a.
Proof.
intros.
orb_simple.
Qed.

Theorem test_tactic_or_cases_idempotency_1: forall (a b: bool),
  a || (a || b) = a || b.
Proof.
intros.
orb_simple.
Qed.

Theorem test_tactic_or_cases_idempotency_2: forall (a b: bool),
  a || b || a = a || b.
Proof.
intros.
orb_simple.
Qed.

Theorem test_tactic_or_cases_associativity_1: forall (a b c: bool),
  a || b || c = a || (b || c).
Proof.
intros.
orb_simple.
Qed.

Theorem test_tactic_or_cases_associativity_2: forall (a b c: bool),
  a || (b || c) = b || (a || c).
Proof.
intros.
orb_simple.
Qed.

Theorem test_tactic_or_cases_3: forall (a b c: bool),
  a || b || (a || c) = a || (b || c).
Proof.
intros.
orb_simple.
Qed.

Theorem test_tactic_or_cases_4: forall (a b c d: bool),
  a  || b || (c || d ) =
  a  || d || (b || (c || d )).
Proof.
intros.
orb_simple.
Qed.
