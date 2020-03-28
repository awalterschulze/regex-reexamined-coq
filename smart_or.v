Set Implicit Arguments.
Set Asymmetric Patterns.

Require Import List.

Require Import comparable.
Require Import compare_regex.
Require Import derive.
Require Import nullable.
Require Import regex.

(* TODO: add associativity, waiting for reorder proofs *)
Definition smart_or {X: Set} {tc: comparable X} (r s: regex X) : regex X :=
  match compare_regex r s with
  | Eq => s
  | Lt => or r s
  | Gt => or s r
  end.
