Require Import comparable.

(* A character for a regular expression is generic,
   but it needs to implement an interface.
   It needs to be comparable.
*)

Inductive regex (X: Type) {C: comparable X} : Type :=
  fail : regex X (* matchesb no strings *)
  | empty : regex X (* matchesb the empty string *)
  | char : X -> regex X (* matchesb a single character *)
  | or : regex X -> regex X -> regex X
  | and : regex X -> regex X -> regex X
  | concat : regex X -> regex X -> regex X
  | not : regex X -> regex X
  | star : regex X -> regex X
  .

(*
We set arguments for fail and empty so that X is implicit when constructing a regex.
For fail: Arguments X, C are implicit and maximally inserted
For empty: Arguments X, C are implicit and maximally inserted
*)

Arguments fail {X} {C}.
Arguments empty {X} {C}.
Arguments char {X} {C} _.
Arguments or {X} {C} _ _.
Arguments and {X} {C} _ _.
Arguments concat {X} {C} _ _.
Arguments not {X} {C} _.
Arguments star {X} {C} _.
