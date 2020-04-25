Set Implicit Arguments.
Set Asymmetric Patterns.

Require Import List.

Require Import comparable.
Require Import regex.

Fixpoint size {X: Set} (r: regex X) := 
  match r with
  | fail => 1
  | empty => 1
  | char _ => 1
  | (or s t) => 1 + size s + size t
  | (and s t) => 1 + size s + size t
  | (concat s t) => 1 + size s + size t
  | (not s) => 1 + size s
  | (star s) => 1 + size s
  end.
