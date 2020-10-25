Require Import CoqStock.comparable.
Require Import CoqStock.List.

(* A character for a regular expression is generic,
   but it needs to implement an interface.
   It needs to be comparable.
*)

Inductive regex (A: Type) {cmp: comparable A} : Type :=
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
For fail: Arguments A, cmp are implicit and maximally inserted
For empty: Arguments A, cmp are implicit and maximally inserted
*)

Arguments fail {A} {cmp}.
Arguments empty {A} {cmp}.
Arguments char {A} {cmp} _.
Arguments or {A} {cmp} _ _.
Arguments and {A} {cmp} _ _.
Arguments concat {A} {cmp} _ _.
Arguments not {A} {cmp} _.
Arguments star {A} {cmp} _.
