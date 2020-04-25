Set Implicit Arguments.
Set Asymmetric Patterns.

Require Import List.

Require Import comparable.
Require Import regex.

(* nullable returns whether the regular expression matches the
   empty string, for example:
   nullable (ab)*        = true
   nullable a(ab)*       = false
   nullable a            = false
   nullable (abc)*|ab    = true
   nullable a(abc)*|ab   = false
   nullable !(a)         = true
*)
Fixpoint nullable {X: Set} {tc: comparable X} (r: regex X) : bool :=
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