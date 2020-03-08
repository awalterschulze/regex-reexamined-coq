Set Implicit Arguments.
Set Asymmetric Patterns.

Require Import comparable.

Section Regex.

(* A character for a regular expression is generic,
   but it needs to implement an interface.
   It needs to be comparable.
*)

Variable X: Set.
Parameter TC: comparable X.

Inductive regex :=
  nothing : regex (* matches no strings *)
  | empty : regex (* matches the empty string *)
  | char : X -> regex (* matches a single character *)
  | or : regex -> regex -> regex
  | and : regex -> regex -> regex
  | concat : regex -> regex -> regex
  | not : regex -> regex
  | zero_or_more : regex -> regex
  .

End Regex.