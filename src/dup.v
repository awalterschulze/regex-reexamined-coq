Set Implicit Arguments.
Set Asymmetric Patterns.

Require Import List.
Import ListNotations.

Require Import comparable.
Require Import sort.

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

  (* HELP WANTED: isn't there some library that more or less does this?
   The ones I found don't seem to have a notation of equality of sets. *)
  Definition list_set_eq (xs ys : list A): Prop :=
    forall (a : A), (In a xs) <-> (In a ys).

  Hint Unfold list_set_eq: list_set_db.
  Hint Extern 0 (_ <-> _) => split : list_set_db.

  Lemma list_set_eq_refl (xs: list A):
    list_set_eq xs xs.
  Proof.
    auto with list_set_db.
  Qed.

  Hint Resolve list_set_eq_refl: list_set_db.

  Lemma list_set_eq_symm (xs ys: list A):
    list_set_eq xs ys <-> list_set_eq ys xs.
  Proof.
    (* QUESTION: why can't auto do this? *)
    split;
      intro H;
      unfold list_set_eq in *;
      intro;
      split; apply H.
  Qed.

  Lemma list_set_eq_step (a : A) (xs: list A):
    list_set_eq (a::xs) (a::(a::xs)).
  Proof.
    autounfold with list_set_db.
    intros.
    split.
    - intro H.
      unfold In.
      destruct (compare_eq_dec a a0); auto.
    - intro H.
      unfold In.
      (* Here auto doesn't work, because we need to destruct H twice
       (one time we do it manually; one time, it happens in auto).
       Is there some way we can add that as a kind of hint? *)
      destruct (compare_eq_dec a a0).
      + auto.
      + unfold In in H.
        destruct H; auto.
  Qed.

  Lemma list_set_eq_trans (xs ys zs : list A):
    list_set_eq xs ys
    -> list_set_eq ys zs
    -> list_set_eq xs zs.
  Proof.
    intros.
    unfold list_set_eq in *.
    intro.
    split.
    - intro.
      auto using H, H0 with list_set_db.
      (* QUESTION: how can the above auto statement fail to just apply the hints
      I told it to apply? *)
      apply H0.
      apply H.
      assumption.
    - intro.
      apply H.
      apply H0.
      assumption.
  Qed.

  Lemma list_set_eq_ind_step (xs ys: list A) (x : A):
    list_set_eq xs ys ->
    list_set_eq (x::xs) (x::ys).
  Proof.
    intros.
    unfold list_set_eq.
    intros.
    split.
    - intros H0.
      destruct H0.
      + subst. cbn. auto.
      + subst. cbn. right.
        apply H. assumption.
    - intros H0.
      destruct H0.
      + subst. cbn. auto.
      + subst. cbn. right.
        apply H. assumption.
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
            (fun H => (exist2 _ _ (* these two arguments are the propositions on A; they are not implicit
                                  arguments, but I think Coq can infer it from the context*)
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
      destruct recres_list as [| x1 reclist'] eqn:?; constructor.
      apply compare_lt_leq_trans with (y0 := y).
      assumption.
      replace y with (hd y ls').
      apply is_sorted_first_element_smallest.
      subst. apply tail_of_is_sorted_is_sorted with (x0 := x).
      assumption.
      apply recres_listeq.
      cbn. auto.
      subst. cbn. reflexivity.
      assumption.

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
End remove_duplicates_from_sorted.
