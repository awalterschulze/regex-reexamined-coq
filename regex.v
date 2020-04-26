Require Import comparable.

(* A character for a regular expression is generic,
   but it needs to implement an interface.
   It needs to be comparable.
*)

Inductive regex (A: Type) {C: comparable A} : Type :=
  fail : regex A (* matchesb no strings *)
  | empty : regex A (* matchesb the empty string *)
  | char : A -> regex A (* matchesb a single character *)
  | or : regex A -> regex A -> regex A
  | and : regex A -> regex A -> regex A
  | concat : regex A -> regex A -> regex A
  | not : regex A -> regex A
  | star : regex A -> regex A
  .

(*
We set arguments for fail and empty so that A is implicit when constructing a regex.
For fail: Arguments A, C are implicit and maximally inserted
For empty: Arguments A, C are implicit and maximally inserted
*)

Arguments fail {A} {C}.
Arguments empty {A} {C}.
Arguments char {A} {C} _.
Arguments or {A} {C} _ _.
Arguments and {A} {C} _ _.
Arguments concat {A} {C} _ _.
Arguments not {A} {C} _.
Arguments star {A} {C} _.
