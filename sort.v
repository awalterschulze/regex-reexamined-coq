Set Implicit Arguments.
Set Asymmetric Patterns.

Require Import List.

Require Import comparable.

(* insert is a helper function for sort *)
Fixpoint insert {X: Set} {tc: comparable X} (x: X) (xs: list X) : list X :=
  match xs with
  | nil => x :: nil
  | (x'::xs') => match compare x x' with
    | Eq => x::x'::xs'
    | Lt => x::x'::xs'
    | Gt => x'::(insert x xs')
    end
  end.

(* sort is a helper function for eval_list_sort *)
Fixpoint sort {X: Set} {tc: comparable X} (xs: list X) : list X :=
  match xs with
  | nil => nil
  | (x'::xs') => insert x' (sort xs')
  end.

Fixpoint is_sorted {X: Set} {tc: comparable X} (xs: list X) : Prop :=
  match xs with
  | nil => True
  | (x'::xs') => match xs' with
    | nil => True
    | (x''::xs'') => match compare x' x'' with
      | Gt => False
      | _ => is_sorted xs'
      end
    end
  end.