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
      + constructor. left. assumption.
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
      (* QUESTION: how can the above auto statement fail to just apply the hints I told it to apply? *)
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

  (* The result has to satisfy two properties:
1. It is strictly sorted.
2. As a set, it is equal to the input.
   *)
  Fixpoint remove_duplicates_from_sorted (ls : list A):
    is_sorted ls ->
    { lres : list A | is_strictly_sorted lres & list_set_eq ls lres }.
    intros.
    destruct ls as [| a0 ls'] eqn:?.
    - subst.
      refine (exist2 _ _ [] _ _).
      + constructor.
      + apply list_set_eq_refl.
    - assert (is_sorted ls') as Hls'sorted.
      apply tail_of_is_sorted_is_sorted with (x := a0).
      assumption.

      pose (remove_duplicates_from_sorted ls' Hls'sorted) as res.

      destruct ls' as [| a1 ls''] eqn:?.

      + refine (exist2 _ _ ls _ _).
        subst. constructor. subst.
        apply list_set_eq_refl.
      + destruct (compare a0 a1) eqn:?.
        * (* Case: a0 = a1 *)
          refine (exist2 _ _
                         (proj1_sig (sig_of_sig2 res))
                         (proj2_sig (sig_of_sig2 res))
                         _).

          apply list_set_eq_trans with
              (xs := (a0 :: a1 :: ls''))
              (ys := ls')
              (zs := (proj1_sig (sig_of_sig2 res))).
          subst. compare_to_eq. subst.
          apply list_set_eq_symm.
          apply list_set_eq_step with (a := a1)
                                      (xs := (ls'')).

          subst.
          exact (proj3_sig res).

        * (* Case: a0 < a1 *)
          set (res_list :=
                 (proj1_sig (sig_of_sig2 res))).

          refine (exist2 _ _
                         (a0 :: res_list)
                         _ _).

          -- (* proof of strictly sorted *)
             destruct res_list as [| res0 res_list' ] eqn:?; try constructor.
             subst.

             assert (compare_leq a1 res0).
             (* Will use: a1 in  (a1 :: ls''), which is sorted;
              res0 is also in there *)
             assert (In res0 (a1 :: ls'')).
             apply (proj3_sig res).
             replace (proj1_sig (sig_of_sig2 res)) with res_list.
             rewrite Heql1.
             cbn. auto. auto.

             replace a1 with (hd a1 (a1 :: ls'')).
             apply is_sorted_first_element_smallest.
             apply tail_of_is_sorted_is_sorted with (x := a0).
             assumption.

             assumption.
             auto.

             (* now use transitivity *)
             apply compare_lt_leq_trans with (y := a1);
             assumption.

             subst.
             rewrite <- Heql1.
             exact (proj2_sig (sig_of_sig2 res)).

          -- (* proof of list equality *)
            (* idea of proof: both have a0; and the rest
            of the list is equal by recursion. *)
            apply list_set_eq_ind_step.
            unfold res_list.
            subst.
            exact (proj3_sig res).

        * (* Case a0 > a1; contradiction *)
          exfalso.
          remember (first_two_of_is_sorted_are_sorted H) as Hcontrad.
          destruct Hcontrad; contradiction_from_compares.
  Defined.





  (* The type of this function does not entirely specify the function: the
     result may be a strictly sorted list, but there is nothing that says it is
     the same as ls, but with duplicates removed. *)
  Fixpoint remove_duplicates_from_sorted (ls : list A):
      is_sorted ls -> {ls' : list A | is_strictly_sorted ls'}.
    intro.
    (* Probably need to do convoy trick here again. *)
    (* refine (match ls with *)
    (*           | nil => (exist _ nil empty_strictly_sorted) *)
    (*           | (x0 :: xs') *)
    (*             => match xs' with *)
    (*                | nil => (exist _ [x0] (singleton_strictly_sorted x0)) *)
    (*                | (x1 :: xs'') => *)
    (*                  match compare x0 x1 with *)
    (*                  | Eq => remove_duplicates_from_sorted xs' (tail_of_is_sorted_is_sorted H) *)
    (*                  | _ => x0 :: (remove_duplicates_from_sorted xs' (tail_of_is_sorted_is_sorted H)) *)
    (*                  end *)
    (*                end *)
    (*         end). *)
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

