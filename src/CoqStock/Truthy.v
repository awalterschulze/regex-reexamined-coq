(* truthy is a module specifically created for the truthy tactic,
   which simplifies orb and andb expressions.
*)

Set Implicit Arguments.
Set Asymmetric Patterns.

Require Import Coq.Bool.Bool.
Require Import Coq.setoid_ring.Ring.

(* bool_semi_ring creates a semi ring 
   , using `or` and `and` boolean expressions 
   that can be used with the `ring` tactic
*)
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
truthy is a tactic that repeatedly applies:
  - the semi ring with orb tactic
  - removes duplicates in or expressions
  - removes all false values in or expressions
  - returns true, if a true is found in an or expression
*)
Ltac truthy := repeat
  ( ring
  || rewrite orb_diag
  || rewrite orb_false_r
  || rewrite orb_false_l
  || rewrite orb_true_r
  || rewrite orb_true_l
  ).

Example example_or_commutativity: forall (a b: bool),
  a || b = b || a.
Proof.
intros.
truthy.
Qed.

Example example_or_idempotency_1: forall (a b: bool),
  a || (a || b) = a || b.
Proof.
intros.
truthy.
Qed.

Example example_or_idempotency_2: forall (a b: bool),
  a || b || a = a || b.
Proof.
intros.
truthy.
Qed.

Example example_or_associativity_1: forall (a b c: bool),
  a || b || c = a || (b || c).
Proof.
intros.
truthy.
Qed.

Example example_or_associativity_2: forall (a b c: bool),
  a || (b || c) = b || (a || c).
Proof.
intros.
truthy.
Qed.

Example example_or_3: forall (a b c: bool),
  a || b || (a || c) = a || (b || c).
Proof.
intros.
truthy.
Qed.

Example example_or_4: forall (a b c d: bool),
  a  || b || (c || d ) =
  a  || d || (b || (c || d )).
Proof.
intros.
truthy.
Qed.

Example example_or_false: forall (a: bool),
  a || false = a.
Proof.
intros.
truthy.
Qed.

Example example_or_true: forall (a: bool),
  true || a = true.
Proof.
intros.
truthy.
Qed.
