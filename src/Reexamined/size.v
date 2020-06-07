Set Implicit Arguments.
Set Asymmetric Patterns.

Require Import List.

Require Import CoqStock.comparable.
Require Import Reexamined.regex.

Fixpoint size {A: Type} {cmp: comparable A} (r: regex A) := 
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
