Set Implicit Arguments.
Set Asymmetric Patterns.

Require Import List.
Import ListNotations.

Require Import comparable.
Require Import sort.

Section inductive_predicate_strictly_sorted.
  (* Being strictly sorted can be defined in two equivalent ways:
1. being sorted and having no duplicates; or
2. every element in the list is strictly smaller than the next.
   *)

  Context {A: Type}.
  Context {cmp: comparable A}.

  Inductive is_strictly_sorted : list A -> Prop :=
  | empty_strictly_sorted : is_strictly_sorted nil
  | singleton_strictly_sorted (x : A) : is_strictly_sorted [x]
  | tail_strictly_sorted (x y : A) (xs : list A):
      (compare x y = Lt)
      -> is_strictly_sorted (y :: xs)
      -> is_strictly_sorted (x :: y :: xs).

  Hint Constructors is_strictly_sorted : strictly_sorted.

  Lemma is_strictly_sorted_tail: forall (ls : list A),
      is_strictly_sorted ls -> is_strictly_sorted (tl ls).
  Proof.
    intro ls. intro H.
    destruct H; auto with strictly_sorted.
  Qed.
End inductive_predicate_strictly_sorted.

Section remove_duplicates_from_sorted.
  Context {A: Type}.
  Context {cmp: comparable A}.

  (* The type of this function does not entirely specify the function: the
     result may be a strictly sorted list, but there is nothing that says it is
     the same as ls, but with duplicates removed. *)
  Fixpoint remove_duplicates_from_sorted (ls : list A):
      is_sorted ls -> {ls' : list A | is_strictly_sorted ls'}.
    intro.
    (* Probably need to do convoy trick here again. *)
    refine (match ls with
              | nil => (exist _ nil empty_strictly_sorted)
              | (x0 :: xs')
                => match xs' with
                   | nil => (exist _ [x0] (singleton_strictly_sorted x0))
                   | (x1 :: xs'') =>
                     match compare x0 x1 with
                     | Eq => remove_duplicates_from_sorted xs' (tail_of_is_sorted_is_sorted H)
                     | _ => x0 :: (remove_duplicates_from_sorted xs' (tail_of_is_sorted_is_sorted H))
                     end
                   end
            end).
  Abort.
End remove_duplicates_from_sorted.

(* remove_duplicates_from_sorted removes duplicates from a sorted list *)
Fixpoint remove_duplicates_from_sorted {A: Type} {cmp: comparable A} (xs: list A): list A :=
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
  forall {A: Type} {cmp: comparable A} (xs: list A) {s: is_sorted xs},
  is_sorted (remove_duplicates_from_sorted xs).
Proof.
(* TODO: Good First Issue *)
Abort.

(* TODO: Help Wanted
Define more theorems to prove that remove_duplicates is correct 
*)

