Require Import Coq.Lists.List.

Require Import CoqStock.comparable.

Require Import Reexamined.regex.

(* nullable returns whether the regular expression matchesb the
   empty string, for example:
   nullable (ab)*        = true
   nullable a(ab)*       = false
   nullable a            = false
   nullable (abc)*|ab    = true
   nullable a(abc)*|ab   = false
   nullable !(a)         = true
*)
Fixpoint nullable {A: Type} {cmp: comparable A} (r: regex A) : bool :=
  match r with
  | fail => false
  | empty => true
  | char _ => false
  | or s t => nullable s || nullable t
  | and s t => nullable s && nullable t
  | concat s t => nullable s && nullable t
  | not s => negb (nullable s)
  | star _ => true
  end.