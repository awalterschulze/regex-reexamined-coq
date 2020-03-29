Set Implicit Arguments.
Set Asymmetric Patterns.

Require Import List.

Require Import comparable.
Require Import regex.

Fixpoint size {X: Set} (r: regex X) := 
  match r with
  | nothing => 1
  | empty => 2
  | char _ => 3
  | (or s t) => 1 + size s + size t
  | (and s t) => 1 + size s + size t
  | (concat s t) => 1 + size s + size t
  | (not s) => 1 + size s
  | (zero_or_more s) => 1 + size s
  end.
