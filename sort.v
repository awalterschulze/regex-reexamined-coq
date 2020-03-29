Set Implicit Arguments.
Set Asymmetric Patterns.

Require Import List.

Require Import comparable.

(* TODO: Help Wanted
Use /\ and \/ to define a more compact property
*)
(* sorted is a property that says whether a list is sorted *)
Fixpoint sorted {X: Set} {tc: comparable X} (xs: list X) : Prop :=
  match xs with
  | nil => True
  | (x'::xs') => match xs' with
    | nil => True
    | (x''::xs'') => match compare x' x'' with
      | Gt => False
      | _ => sorted xs'
      end
    end
  end.

Theorem sort_incremental: forall {X: Set} {tc: comparable X} (xs: list X)  (x: X) {s : sorted (x :: xs)},
  sorted xs.
Proof.
(* TODO: Good First Issue *)
Admitted.

(* insert_sort is a helper function for sort *)
Fixpoint insert_sort {X: Set} {tc: comparable X} (xs: list X) (x: X) : list X :=
  match xs with
  | nil => x :: nil
  | (x'::xs') => match compare x x' with
    | Eq => x::x'::xs'
    | Lt => x::x'::xs'
    | Gt => x'::(insert_sort xs' x)
    end
  end.

(* insert_sort_sorts is a helper lemma for sort_sorts *)
Lemma insert_sort_sorts: forall {X: Set} {tc: comparable X} (xs: list X) (x: X) {s: sorted xs},
  sorted (insert_sort xs x).
Proof.
(* TODO: Good First Issue *)
Admitted.

(* sort is a helper function for eval_list_sort *)
Fixpoint sort {X: Set} {tc: comparable X} (xs: list X) : list X :=
  match xs with
  | nil => nil
  | (x'::xs') => insert_sort (sort xs') x'
  end.

Theorem sort_sorts: forall {X: Set} {tc: comparable X} (xs: list X),
  sorted (sort xs).
Proof.
induction xs.
- simpl. trivial.
- simpl. apply insert_sort_sorts. assumption.
Qed.
