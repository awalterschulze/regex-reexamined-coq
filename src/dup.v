Set Implicit Arguments.
Set Asymmetric Patterns.

Require Import List.
Import ListNotations.

Require Import CoqStock.comparable.
Require Import sort.
Require Import CoqStock.list_set.

Section inductive_predicate_strictly_sorted.
  (* The following two properties of lists are equivalent:
     1. being sorted and having no duplicates; and
     2. being strictly sorted, i.e., every element is strictly smaller than the next.

     I think the second is easier to capture in an inductive predicate (it's
     almost the same as our definition of is_sorted), so that's what I'll use.
   *)

  Context {A: Type}.
  Context {cmp: comparable A}.

  Inductive is_strictly_sorted: list A -> Prop :=
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

  Local Ltac extract_info_from_strictly_sorted :=
    unfold not; intros; subst;
    match goal with
    | [ H: is_strictly_sorted (?x0 :: ?xs) |- _ ]
      => inversion H; subst;
         try discriminate (* this eliminates some impossible cases *)
    end;
    destruct_list_equality.

  Lemma is_strictly_sorted_implies_sorted: forall (ls : list A),
      is_strictly_sorted ls -> is_sorted ls.
  Proof.
    induction ls.
    - constructor.
    - extract_info_from_strictly_sorted.
      + constructor.
      + constructor. right. assumption.
        apply IHls. assumption.
  Qed.

  (* If (x :: xs) is strictly sorted, then xs is also strictly sorted.
     This tactic uses that fact to derive a contradiction if possible.
   *)
  Local Ltac is_strictly_sorted_contradiction_via_tail :=
    match goal with
    | [ H: is_strictly_sorted (?x0 :: ?xs),
           Hcon: ~(is_strictly_sorted ?xs)
        |- False ]
      => apply Hcon;
         apply is_strictly_sorted_tail;
         exact H
    | [ H: ~(is_strictly_sorted ?xs)
        |- ~(is_strictly_sorted (?x0 :: ?xs))]
        (* in this case, just apply the contrapositive of is_strictly_sorted_tail *)
      => contradict H;
         apply is_strictly_sorted_tail with (ls := (x0 :: xs));
         assumption
    end.
  (* TODO: Good First Issue *)
  (* Change this tactic so that it also works with sorted lists,
     not only strictly sorted lists. *)

  Definition is_strictly_sorted_dec: forall (ls :list A),
      {is_strictly_sorted ls} + {~(is_strictly_sorted ls)}.


    refine (
        fix F (ls: list A) : {is_strictly_sorted ls} + {~(is_strictly_sorted ls)} :=
          (match ls
                 return {is_strictly_sorted ls} +
                        {~(is_strictly_sorted ls)}
           with
             | nil => left _
             | (x0::ls') =>
               (match ls' as l
                      return (ls' = l) ->
                             {is_strictly_sorted (x0::ls')} +
                             {~(is_strictly_sorted (x0::ls'))}
                with
                | nil => (fun _ => left _)
                | (x1::ls'') =>
                  (fun ls0 =>
                     (match (compare x0 x1) as cmp
                            return (compare x0 x1 = cmp) ->
                                   {is_strictly_sorted (x0::ls')} +
                                   {~(is_strictly_sorted (x0::ls'))}
                      with
                      | Lt =>
                        (fun Hcmp => if (F ls')
                                     then left _
                                     else right _)
                      | _ =>
                        (fun Hcmp => right _)
                      end) eq_refl)
                end) eq_refl
           end));
      try (subst; constructor; assumption);
      try is_strictly_sorted_contradiction_via_tail;
      try (extract_info_from_strictly_sorted; contradiction_from_compares).
    Defined.
End inductive_predicate_strictly_sorted.

Section remove_duplicates_from_sorted.
  (*
    The main definition of this section is remove_duplicates_from_sorted, which
    is a verified decision procedure that removes all duplicates from a sorted
    list.

    To fully specify this in the type system, we first define list_set_eq, which
    is a type that represents the proposition that two lists are equal as sets
    (i.e., they have exactly the same elements).
  *)
  Context {A: Type}.
  Context {cmp: comparable A}.

  (* This lemma solves the bulk of oen of the cases of remove_duplicates_from_sorted.
     Short description:
     - we know x < y (with x, y of type A)
     - ls is a strictly sorted list that starts with y (b/c as a set, it is
       equal to something of the form (y :: ls'))
     Therefore, (x :: ls) is strictly sorted.
   *)
  Lemma consing_smaller_than_smallest_to_strictly_sorted (ls ls' : list A) (x y : A):
    compare x y = Lt ->
    is_strictly_sorted ls ->
    is_sorted (y :: ls') ->
    list_set_eq (y :: ls') ls ->
    is_strictly_sorted (x :: ls).
  Proof.
    intros Hcomp Hssortls Hsort Hseteq.
    destruct ls eqn:?.
    - constructor.
    - constructor.
      apply compare_lt_leq_trans with (y0 := y).
      assumption.

      apply is_sorted_first_element_smallest with (xs := (y :: ls')) (default := y).
      assumption.
      apply Hseteq.
      unfold In. auto.
      assumption.
  Qed.

  (* A verified decision procedure to remove all duplicate elements from a list
   that is sorted. The type tells you: given an input list ls, it returns a
   strictly sorted list (hence, without any duplicates) that is equal to the
   original list ls as set. *)
  Definition remove_duplicates_from_sorted: forall (ls : list A),
    is_sorted ls -> { lres : list A | is_strictly_sorted lres & list_set_eq ls lres }.
    intros ls0 Hsort0.

    refine
      ((fix F (ls : list A) (Hsort : is_sorted ls) :
          { lres : list A | is_strictly_sorted lres & list_set_eq ls lres } :=
          let
            restype := ({ lres : list A | is_strictly_sorted lres & list_set_eq ls lres })
          in
          match ls as l return ((ls = l) -> restype) with
          | nil =>
            (fun H => (exist2 _ _ (* These two holes correspond to the two propositions about (ls : list A)
                                     that are part of the sigma type: the first proposition is is_strictly_sorted,
                                     the second is the list_eq.
                                     Even though they are not implicit arguments, Coq can infer them
                                     from the context. *)
                              nil (* the actual element *)
                              empty_strictly_sorted (* proof for the first proposition (strictly sorted) *)
                              _ (* proof for the second proposition (equal as lists) *)
            ))
          | (x :: ls') =>
            (fun H =>
               (match ls' as l return (ls' = l) -> restype with
                | nil => (fun H' => (exist2 _ _ (x::nil) _ _))
                | (y :: ls'') =>
                  (fun H' =>
                     (match (compare x y) as cmp
                            return (compare x y = cmp -> restype) with
                      | Gt => (fun Hcomp => False_rect _ _)
                      | Eq =>
                        let recres := (F ls' _) in
                        let (recres_list, recres_sorted, recres_listeq) := recres in
                        (fun Hcomp =>
                           (exist2 _ _
                                   recres_list
                                   recres_sorted
                                   _))
                      | Lt =>
                        let recres := (F ls' _) in
                        let (recres_list, recres_sorted, recres_listeq) := recres in
                        (fun Hcomp =>
                           (exist2 _ _
                                   (x :: recres_list)
                                   _
                                   _))
                      end) eq_refl)
                end) eq_refl)
          end eq_refl (* this eq_refl provides the proof for (ls = l) (see match statement) *)
       ) ls0 Hsort0).
    - subst. apply list_set_eq_refl.
    - constructor.
    - subst. apply list_set_eq_refl.

    - (* Case Eq *)
      Unshelve.
      2: {
        subst. apply (tail_of_is_sorted_is_sorted Hsort).
      }
      apply list_set_eq_trans with (ys := ls').
      subst.
      compare_to_eq.
      apply list_set_eq_symm.
      apply list_set_eq_step.

      assumption.
      subst. apply (tail_of_is_sorted_is_sorted Hsort).

    - (* Case Lt, proof of strictly *)
      (* This proof is actually quite elaborate to prove in Coq.
       The idea is:
       - recres_list has the same elements as ls'
       - x is smaller than everything in ls'
         (because it is smaller than the first element fo ls', and ls' is sorted)
       - hence, x is smaller than everything in recres_list
       *)

      apply consing_smaller_than_smallest_to_strictly_sorted with (y := y) (ls' := ls''); try assumption.
      apply tail_of_is_sorted_is_sorted with (x0 := x). subst. assumption.
      subst. assumption.

    - (* Case Lt, proof of list equality *)
      subst.
      apply list_set_eq_ind_step.
      assumption.

    - (* Case Gt, proof of contradiction *)
      subst.
      remember (first_two_of_is_sorted_are_sorted Hsort).
      contradiction_from_compares.
  Qed.

  (* A convenience function that extracts the list from the above sigma type. *)
  Definition remove_duplicates_from_sorted_list (ls : list A) (Hsort: is_sorted ls): list A
    := (proj1_sig (sig_of_sig2 (remove_duplicates_from_sorted Hsort))).


  (* remove_duplicates_from_sorted removes duplicates from a sorted list *)
  (* This is an alternative to remove_duplicates_from_sorted.
   The basic structure is the same, except that here the case
      compare x' x'' = Gt
   is treated differently: here we treat it the same as Lt, whereas
   in the other we show that that case is contradictory.
   *)
  Fixpoint remove_duplicates_from_sorted' (xs: list A): list A :=
    match xs with
    | nil => nil
    | (x'::xs') => match xs' with
                   | nil => xs
                   | (x''::xs'') =>
                     match compare x' x'' with
                     | Eq => remove_duplicates_from_sorted' xs'
                     | _ => x'::(remove_duplicates_from_sorted' xs')
                     end
                   end
    end.

  Lemma remove_duplicates_from_sorted_both_are_same (xs: list A) (Hsort: is_sorted xs):
    remove_duplicates_from_sorted' xs = remove_duplicates_from_sorted_list Hsort.
    Proof.
    (* TODO: Good First Issue *)
    Abort.
End remove_duplicates_from_sorted.
