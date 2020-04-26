Set Implicit Arguments.
Set Asymmetric Patterns.

Require Import List.

Require Import comparable.

(* is_sorted is a property that says whether a list is sorted *)
Fixpoint is_sorted {A: Type} {cmp: comparable A} (xs: list A) : Prop :=
  match xs with
  | nil => True
  | (x'::xs') => match xs' with
    | nil => True
    | (x''::xs'') => match compare x' x'' with
      | Eq => True
      | Lt => True
      | Gt => False
      end
    end
  end.

Lemma is_sorted_sufficient_cond
  {A: Type}
  {cmp: comparable A}
  (x x' : A)
  (xs: list A):
  ((compare x x' = Lt) \/ (compare x x' = Eq)) ->
  (is_sorted (x'::xs)) ->
  is_sorted (x::x'::xs).
Proof.
intros.
unfold is_sorted.
destruct H; rewrite H; trivial.
Qed.

Inductive is_sorted' {A: Type} {cmp: comparable A} : list A -> Prop :=
  | empty_sorted' : is_sorted' nil
  | singleton_sorted' (x: A) : is_sorted' (x :: nil)
  | lessthan_sorted'
    (x: A)
    (y: A)
    (c : compare x y = Lt)
    (xs: list A)
    (s: is_sorted' (y :: xs))
    : is_sorted' (x :: y :: xs)
  | equal_sorted'
    (x: A)
    (y: A)
    (c : compare x y = Eq)
    (xs: list A)
    (s: is_sorted' (y :: xs))
    : is_sorted' (x :: y :: xs)
.

Inductive is_sorted'' {A: Type} {cmp: comparable A} : list A -> Prop :=
  | empty_sorted'' : is_sorted'' nil
  | singleton_sorted'' : forall x, is_sorted'' (x :: nil)
  | lessthan_sorted''
    : forall (x: A) (xs: list A),
      (exists (y: A) (ys: list A),
      xs = (y :: ys)
      /\ compare x y = Lt)
      /\ is_sorted'' xs
      -> is_sorted'' (x :: xs)
  | equal_sorted''
    : forall (x: A) (xs: list A),
      (exists (y: A) (ys: list A),
      xs = (y :: ys)
      /\ compare x y = Eq)
      /\ is_sorted'' xs
      -> is_sorted'' (x :: xs)
.

Lemma tail_of_is_sorted_is_sorted:
  forall {A: Type}
  {cmp: comparable A}
  (x: A)
  (xs: list A),
  is_sorted (x :: xs) -> is_sorted xs.
Proof.
(* TODO: Good First Issue *)
Admitted.

Lemma tail_of_is_sorted'_is_sorted':
  forall {A: Type}
  {cmp: comparable A}
  (x: A)
  (xs: list A),
  is_sorted' (x :: xs) -> is_sorted' xs.
Proof.
(* TODO: Good First Issue *)
Admitted.

Lemma tail_of_is_sorted''_is_sorted'':
  forall {A: Type}
  {cmp: comparable A}
  (x: A)
  (xs: list A),
  is_sorted'' (x :: xs) -> is_sorted'' xs.
Proof.
(* TODO: Good First Issue *)
Admitted.

Theorem is_sorted_and_is_sorted'_are_equivalent : forall {A: Type} {cmp: comparable A} (xs: list A),
  is_sorted xs <-> is_sorted' xs.
Proof.
intros.
split.
- induction xs as [(*nil*)| x0 xs' IH].
  + simpl.
    intros.
    exact empty_sorted'.
  + induction xs' as [(*nil*)| x1 xs''].
    * simpl.
      intros.
      exact (singleton_sorted' x0).
    * intros.
      assert (is_sorted (x1 :: xs'')).
      -- apply tail_of_is_sorted_is_sorted with (x := x0) (xs := (x1 :: xs'')).
         assumption.
      -- apply IH in H0.
         simpl in H.
         destruct (compare x0 x1) eqn:c.
         ++ refine (equal_sorted' _ _ _).
            ** exact c.
            ** exact H0.
         ++ exact (lessthan_sorted' _ c H0).
         ++ contradiction.
- induction xs as [(*nil*)| x0 xs' IH].
  + simpl.
    intros.
    trivial.
  + intros.
    inversion H.
    * simpl. trivial.
    * simpl. rewrite c. trivial.
    * simpl. rewrite c. trivial.
Qed.

Theorem is_sorted'_and_is_sorted''_are_equivalent : forall {A: Type} {cmp: comparable A} (xs: list A),
  is_sorted' xs <-> is_sorted'' xs.
Proof.
(* TODO: Good First Issue *)
Admitted.

(* insert_sort is a helper function for sort *)
Fixpoint insert_sort {A: Type} {cmp: comparable A} (xs: list A) (x: A) : list A :=
  match xs with
  | nil => x :: nil
  | (x'::xs') => match compare x x' with
    | Eq => x::x'::xs'
    | Lt => x::x'::xs'
    | Gt => x'::(insert_sort xs' x)
    end
  end.

(* insert_sort_sorts is a helper lemma for sort_sorts *)
Lemma insert_sort_sorts: forall {A: Type} {cmp: comparable A} (xs: list A) (x: A) {s: is_sorted xs},
  is_sorted (insert_sort xs x).
Proof.
(* TODO: Good First Issue *)
Admitted.

(* sort is a helper function for eval_list_sort *)
Fixpoint sort {A: Type} {cmp: comparable A} (xs: list A) : list A :=
  match xs with
  | nil => nil
  | (x'::xs') => insert_sort (sort xs') x'
  end.

Theorem sort_sorts: forall {A: Type} {cmp: comparable A} (xs: list A),
  is_sorted (sort xs).
Proof.
induction xs.
- simpl. trivial.
- simpl. apply insert_sort_sorts. assumption.
Qed.
