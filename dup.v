Set Implicit Arguments.
Set Asymmetric Patterns.

Require Import List.

Require Import comparable.
Require Import sort.

(* remove_duplicates_from_sorted removes duplicates from a sorted list *)
Fixpoint remove_duplicates_from_sorted {X: Type} {tc: comparable X} (xs: list X): list X :=
  match xs with
  | nil => nil
  | (x'::xs') => match xs' with
    | nil => xs
    | (x''::xs'') =>
      match compare x' x'' with
      | Eq => remove_duplicates_from_sorted xs'
      | _ => x'::(remove_duplicates_from_sorted xs')
      end
    end
  end.

(* remove_duplicates_from_sorted_is_sorted shows that a sorted list with its duplicates removed is still sorted *)
Theorem remove_duplicates_from_sorted_is_sorted:
  forall {X: Type} {tc: comparable X} (xs: list X) {s: is_sorted xs},
  is_sorted (remove_duplicates_from_sorted xs).
Proof.
(* TODO: Good First Issue *)
Admitted.

(* TODO: Help Wanted
Define more theorems to prove that remove_duplicates is correct 
*)

