Set Implicit Arguments.
Set Asymmetric Patterns.

Require Import List.

Require Import Psatz.
Require Import Lia.

Require Import comparable.

(* is_sorted is a property that says whether a list is sorted *)
Inductive is_sorted {A: Type} {cmp: comparable A} : list A -> Prop :=
  | empty_sorted : is_sorted nil
  | singleton_sorted (x: A) : is_sorted (x :: nil)
  | tail_sorted
    (x: A)
    (y: A)
    (c : compare_leq x y)
    (xs: list A)
    (s: is_sorted (y :: xs))
    : is_sorted (x :: y :: xs)
.

(* This is not really a bool... should it be? *)
Fixpoint is_sortedb {A: Type} {cmp: comparable A} (xs: list A) : Prop :=
  match xs with
  | nil => True
  | (x'::xs') => match xs' with
    | nil => True
    | (x''::xs'') => match compare x' x'' with
      | Eq => is_sortedb xs'
      | Lt => is_sortedb xs'
      | Gt => False
      end
    end
  end.

Lemma is_sortedb_induction_step
  {A: Type}
  {cmp: comparable A}
  (x x' : A)
  (xs: list A):
  (compare_leq x x') ->
  (is_sortedb (x'::xs)) ->
  is_sortedb (x::x'::xs).
Proof.
  intros.
  unfold is_sortedb.
  destruct H; rewrite H; trivial.
Qed.

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
  intros.
  inversion H; subst; (constructor || assumption).
Qed.

Lemma first_two_of_is_sorted_are_sorted:
  forall {A: Type}
  {cmp: comparable A}
  (x y: A)
  (xs: list A),
  is_sorted (x :: y :: xs) -> compare_leq x y.
Proof.
  intros.
  inversion H.
  assumption.
Qed.

Lemma tail_of_is_sortedb_is_sortedb:
  forall {A: Type}
  {cmp: comparable A}
  (x: A)
  (xs: list A),
  is_sortedb (x :: xs) -> is_sortedb xs.
Proof.
(* TODO: Good First Issue
By Admitting this we previously let a bug slip through
 *)
Abort.

Lemma tail_of_is_sorted''_is_sorted'':
  forall {A: Type}
  {cmp: comparable A}
  (x: A)
  (xs: list A),
  is_sorted'' (x :: xs) -> is_sorted'' xs.
Proof.
(* TODO: Good First Issue *)
Abort.

Lemma list_inductive_equality: forall {A: Type} {cmp: comparable A} (x y: A) (xs ys: list A),
    ( (x::xs) = (y::ys)) <-> (x = y /\ (xs = ys)).
Proof.
  intros. split.
  - split.
    + assert (x = (hd x (x :: xs))) as Heq.
      trivial.
      rewrite H in Heq.
      unfold hd in Heq.
      assumption.
    + assert (xs = (tl (x::xs))) as Heq.
      trivial.
      rewrite H in Heq.
      unfold tl in Heq.
      assumption.
  - intros.
    destruct H. subst. trivial.
Qed.

(* This tactic turns a hypothesis of the form
        (?x :: ?xs) = (?y :: ?ys)
   into two hypotheses
         x = y     and     xs = ys
*)
(* TODO: should this be moved somewhere else? Maybe make a library of tactics? *)
Ltac destruct_list_equality :=
  repeat match goal with
         | [H: (?x :: ?xs) = (?y :: ?ys) |- _] => rewrite list_inductive_equality in H; destruct H
         end.


(* If there is a pair of hypotheses
          compare ?x0 ?x1 = Gt   and   compare ?x0 ?x1 = Lt (or = Eq)
       then this tactic derives a contradiction.
 *)
(* TODO: move to library? *)
Ltac contradiction_from_compares :=
  match goal with
  | [ H1: compare ?x0 ?x1 = Gt , H2: compare ?x0 ?x1 = Lt |- _ ]
    => exfalso; assert (Gt = Lt); try (rewrite <- H1; rewrite <- H2; reflexivity); discriminate
  | [ H1: compare ?x0 ?x1 = Gt , H2: compare ?x0 ?x1 = Eq |- _ ]
    => exfalso; assert (Gt = Eq); try (rewrite <- H1; rewrite <- H2; reflexivity); discriminate
  | [ H1: compare ?x0 ?x1 = Eq , H2: compare ?x0 ?x1 = Lt |- _ ]
    => exfalso; assert (Eq = Lt); try (rewrite <- H1; rewrite <- H2; reflexivity); discriminate
  | [ H1: compare_leq ?x0 ?x1, H2: compare ?x0 ?x1 = Gt |- _ ]
    => destruct H1; contradiction_from_compares
  end.


Section certified_decision_procedure.
  Context {A: Type}.
  Context {cmp: comparable A}.

  (* This is a certified decision procedure (as in Ch. 15 in [CPDT]). It is
   essentially the same as our definition of is_sortedb, except that instead of
   giving True or False as the end result, the end result is a dependent type,
   which shows that it is correct. *)

  Definition is_sorted_dec:
    forall (xs: list A), {is_sorted xs} + {~(is_sorted xs)}.
    Hint Constructors is_sorted: sorted_db.

    (* This tactic derives a contradiction of we know that the tail of a sorted
     list is not sorted. *)
    Local Ltac is_sorted_contradiction_via_tail :=
      match goal with
      | [H: is_sorted (?x0 :: ?xs) , Hcon: ~(is_sorted ?xs)  |- False ]
        => apply Hcon; apply tail_of_is_sorted_is_sorted with (x := x0); exact H
      end.



    Hint Unfold compare_leq: sorted_db.

    (*
The essence of the statement below is as simple as is_sortedb, but there are two
complicating factors:

1. We need to use the "convoy trick" (see [CPDT]) twice, to carry over data from
the match statements.

2. We need to supply a proof.
     *)
    refine (fix F (xs : list A): {is_sorted xs} + {~(is_sorted xs)} :=
              match xs return {is_sorted xs} + {~(is_sorted xs)} with
              | nil => left _
              | (x0::xs') =>
                (match xs' as l return (xs' = l) -> {is_sorted (x0::xs')} + {~(is_sorted (x0::xs'))}  with
                  | nil => (fun _ => left _)
                  | (x1::xs'') =>
                    (fun l0 =>
                    (let comp := (compare x0 x1) in
                     (match comp as H return (compare x0 x1 = H) -> {is_sorted (x0::xs')} + {~(is_sorted (x0::xs'))} with
                      | Gt => (fun _ => right _)
                      | _ => (fun Hcomp =>
                                if (F xs')
                                then left _
                                else right _)
                      end) _))
                  end) _
              end);
      try (subst; constructor; auto with sorted_db);
      try (intro; is_sorted_contradiction_via_tail).
    - intro H. inversion H; subst.
      + discriminate.
      + destruct c; subst; destruct_list_equality; subst; contradiction_from_compares.
  Defined.
End certified_decision_procedure.

Section lemmas.
  Context {A: Type}.
  Context {cmp: comparable A}.

  Lemma is_sortedb_reverse_direction (x y : A) (xs : list A):
    is_sortedb (x::y::xs) ->
    (compare_leq x y) /\ (is_sortedb (y::xs)).
  Proof.
    intros.
    unfold is_sortedb in H.
    split.
    - destruct (compare x y) eqn:Hcomp.
      + apply or_introl. assumption.
      + apply or_intror. assumption.
      + contradiction.
    - fold (is_sortedb (y::xs)) in H.
      destruct (compare x y); (assumption || contradiction).
  Qed.

  Lemma is_sorted_first_element_smallest (xs: list A) (default: A):
    is_sorted (xs) ->
    (forall (a: A),
        In a xs -> compare_leq (hd default xs) a).
  Proof.
    induction xs as [| x0 xs'].
    - intros Hsort a Hin.
      unfold In in Hin. contradiction.
    - intros Hsort a Hin.

      destruct xs' as [| x1 xs''].
      + cbn.
        cbn in Hin.
        destruct Hin.
        * subst. unfold compare_leq.
          left. apply proof_compare_eq_reflex.
        * contradiction.

      + cbn.
        cbn in Hin.

        destruct Hin as [Hin | [Hin | Hin]]; try subst.
        * apply compare_leq_reflex.
        * apply first_two_of_is_sorted_are_sorted with (xs := xs'').
          assumption.
        * (* proof is going to be: x0 leq x1, x1 leq x2 *)
          apply compare_leq_trans with (y := x1).
          -- apply first_two_of_is_sorted_are_sorted with (xs := xs'').
             assumption.
          -- apply IHxs'.
             apply tail_of_is_sorted_is_sorted with (x := x0).
             assumption.
             unfold In in *.
             right. assumption.
  Qed.
End lemmas.

Theorem is_sorted_and_is_sortedb_are_equivalent : forall {A: Type} {cmp: comparable A} (xs: list A),
  is_sorted xs <-> is_sortedb xs.
Proof.
Hint Unfold is_sortedb: sorted_db. (* TODO: deprecated *)
Hint Resolve is_sortedb_induction_step: sorted_db.

split.
- induction xs as [(*nil*)| x0 xs' IH]; auto with sorted_db.
  intros.
  try (match goal with
       | [ H: is_sorted ?xs |- _] => inversion H
       end); subst; auto with sorted_db.

- induction xs as [| x0 xs'].
  + intros.
    constructor.
  + intros.
    destruct xs' eqn:?.
    * constructor.
    * set (Hsort := is_sortedb_reverse_direction _ _ _ H).
      destruct Hsort as [Hcomp Hsublist].
      constructor; auto with sorted_db.
Qed.

Theorem is_sortedb_and_is_sorted''_are_equivalent : forall {A: Type} {cmp: comparable A} (xs: list A),
  is_sortedb xs <-> is_sorted'' xs.
Proof.
(* TODO: Good First Issue *)
Abort.

Section indices.
  Context {A: Type}.
  Context {cmp: comparable A}.

  Lemma get_recursion_helper (n : nat) (x : A) (xs : list A):
    (S n < length (x :: xs)) <-> (n < length xs).
  Proof.
    intros. split; (apply Lt.lt_S_n || apply Lt.lt_n_S); auto.
  Defined.

  (* The two lemmas below are sometimes useful in functional contexts *)

  (* What I want:

      a map {k : nat | k < length xs} -> {k : nat | k < length xs}

    but I somehow want to say that this is just the map

      k => (S k)

    but with additional proofs attached
   *)

  Definition get_recursion_helper_dec (n : nat) (x : A) (xs : list A):
    (S n < length (x :: xs)) -> (n < length xs) :=
    fun (H : S n < length (x :: xs)) => Lt.lt_S_n n (length xs) H.

  Definition get_recursion_helper_inc (n : nat) (x : A) (xs : list A):
    (n < length xs) -> (S n < length (x :: xs)) :=
    fun (H : n < length (xs)) => Lt.lt_n_S n (length xs) H.

  (* This tactic adds the hypothesis t only if there is not already a hypothesis
  of type t in the context. Copied from
  https://github.com/coq/coq/wiki/TacticExts#assert-if-necessary *)
  Local Ltac not_exist_hyp t :=
    match goal with
    | H1:t |- _ => fail 2
    end || idtac.

  Local Ltac assert_if_not_exist H :=
    not_exist_hyp H; assert H.

  Local Ltac get_proof_recursion_helpers :=
    match goal with
    | H: (S ?n < length (?x :: ?xs)) |- _
      => assert_if_not_exist (n < length(xs)); try exact (@get_recursion_helper_dec n x xs H)
    end.

  Lemma length_nil {Y: Set}:
    (@length Y nil) = 0.
  Proof. cbn. reflexivity. Qed.

  Lemma reduce_list_lengths_by_one:
    forall (x: A) (xs: list A),
      length (x :: xs) = S (length xs).
  Proof. cbn. reflexivity. Qed.

  Local Ltac nat_smaller_than_length_nil :=
        (* This tactic derives a contradiction when there is a nat n with n < length nil *)
        repeat (match goal with
                | [ P : {n : nat | n < length nil } |- _] => destruct P
                | [ P : _ < length nil |- _ ] => cbn in P
                | [ P : ?x < 0 |- _ ] => apply PeanoNat.Nat.nlt_0_r with (n := x)
        end); assumption.

  Local Ltac reduce_list_lengths :=
    match goal with
    | P: context [length (?x :: ?xs)]  |- _ => rewrite reduce_list_lengths_by_one in P
    | P: context [length nil]  |- _ => rewrite length_nil in P
    | |- context [length (?x :: ?xs)] => rewrite reduce_list_lengths_by_one
    | |- context [length nil] => rewrite length_nil
    end.

  Local Ltac resolve_compare_leq :=
    unfold compare_leq in *; try assumption; try apply or_comm; try assumption.

  Fixpoint get (xs: list A): { n: nat | n < (length xs)} -> A.
    intros. destruct H as [n pf].
    destruct xs as [| x0 xs'] eqn:?.
    - (* xs cannot be empty *)
      exfalso.
      nat_smaller_than_length_nil.
    - destruct n.
      + (* if n = 0, return the first element *)
        exact x0.
      + (* otherwise, recurse *)
        exact (get xs' (exist _ n (get_recursion_helper_dec pf))).
  Defined.

  (* Alternative definition, using std lib *)
  Definition get' (xs: list A): { n: nat | n < (length xs)} -> A.
    intro H. destruct H as [n pf].
    destruct (nth_error xs n) eqn:?.
    - exact a.
    - exfalso.
      (* This is basically an application of nth_error_nth', except that we
       somehow need to get a default element... we can get this from the fact
       that n < length xs, which implies that xs has at least one elemnt.

       So I can imagine this could be automated with some appropriate hints. *)
      destruct xs as [| x0 xs'] eqn:Hxs.
      * replace (length nil) with 0 in pf.
        apply (PeanoNat.Nat.nlt_0_r n). assumption.
        auto.
      * set (@nth_error_nth' A (x0::xs') n x0).
        rewrite e in Heqo.
        discriminate Heqo.
        assumption.
  Defined.

  (* Maybe it would have been better to just use nth_error together
  with some tactics that prove that the bounds are correct. *)

  Lemma get_from_tail:
    forall (xs : list A) (x: A)
           (i : nat)
           (pf: i < length xs)
           (pf': (S i) < length (x::xs)),
      (get (x::xs) (exist _ (S i) pf')) =
      (get xs (exist _ i pf)).
  Proof.
    induction xs as [| x0 xs'].

    - intros. exfalso.
      nat_smaller_than_length_nil.

    - destruct i as [| iminus1].
      + unfold get. reflexivity.
      + intros.
        unfold get.
        fold (get xs' (exist _ iminus1 (get_recursion_helper_dec pf))).
        fold (get (x0::xs') (exist _ (S iminus1) (get_recursion_helper_dec pf'))).
        apply IHxs'.
  Qed.

  Local Ltac get_proof_recursion_helpers_rewrite :=
    repeat get_proof_recursion_helpers;
    repeat (unshelve erewrite get_from_tail; try assumption).


  Lemma get_proof_irrelevance:
    forall (xs: list A)
           (i: nat)
           (pf: i < length xs)
           (pf': i < length xs),
      get xs (exist _ i pf) =
      get xs (exist _ i pf').
  Proof.
    induction xs.
    - intros. exfalso. nat_smaller_than_length_nil.
    - destruct i.
      + unfold get. reflexivity.
      + intros.
        get_proof_recursion_helpers_rewrite.
        apply IHxs.
  Qed.

  Lemma get_app:
    forall (xs ys : list A)
           (i : nat)
           (pf: i < length xs)
           (pf': i < length (xs ++ ys)),
      (get (xs ++ ys) (exist _ i pf'))
      = (get xs (exist _ i pf)).
  Proof.
    induction xs as [| x0 xs'].
    - intros. exfalso.
      nat_smaller_than_length_nil.
    - destruct i as [| iminus1].
      + unfold get. trivial.
      +
        replace ((x0 :: xs') ++ ys) with (x0 :: (xs' ++ ys)).
        2: { exact eq_refl. }
        intros.

        (* All you need to do here is rewrite get_from_tail in two places, and
        then apply the induction hypothesis. *)
        get_proof_recursion_helpers_rewrite.
        apply IHxs'.
  Qed.

  Lemma get_app':
    forall (xs ys : list A)
           (i : nat)
           (assum: i >= length xs)
           (pf: (i - length xs) < length ys)
           (pf': i < length (xs ++ ys)),
      (get (xs ++ ys) (exist _ i pf'))
      = (get ys (exist _ (i - length xs) pf)).
  Proof.
    induction xs as [| x0 xs'].
    - cbn.
      intro.
      intro.
      replace (i - 0) with i.
      2: { lia. }

      intros.
      apply get_proof_irrelevance.

    -
      intros ys i.
      replace ((x0 :: xs') ++ ys) with (x0 :: (xs' ++ ys)).
      2: { exact eq_refl. }

      intros.

      destruct i.
      + exfalso.
        cbn in assum.
        lia.

      + get_proof_recursion_helpers_rewrite.

        cbn.
        apply IHxs'.
        cbn in assum.
        lia.
  Qed.

  Theorem is_sorted_via_indices (xs: list A):
    (is_sorted xs) <->
    (forall (i j: {n : nat | n < (length xs)}),
        let (i0, _) := i in
        let (j0, _) := j in
        (i0 < j0) ->
        (compare_leq
           (get xs i)
           (get xs j))).
  Proof.
    split.
    - induction xs as [|x0 xs'].
      + intros.
        exfalso.
        nat_smaller_than_length_nil.

      + intros.
        destruct i as [i0 pfi].
        destruct j as [j0 pfj].
        intros.

        match goal with
          | [ H: is_sorted (?x :: ?xs) |- _ ] => set (tail_of_is_sorted_is_sorted H)
        end.


        set (xj := get (x0 :: xs') (exist _ j0 pfj)).
        set (xi := get (x0 :: xs') (exist _ i0 pfi)).

        destruct i0 as [| i0minus1].
        * (* base case: use that x0 is leq the next element,
           an by the induction hypothesis, that next element is leq the j-th element *)

          destruct xs' as [| x1 xs''].
          -- exfalso. (* xs' cannot be nil, bc 0 = i < j < length xs *)
             repeat (reduce_list_lengths).
             assert (j0 = 0) as Hj0.
             apply PeanoNat.Nat.lt_1_r.
             assumption.
             subst.
             apply (PeanoNat.Nat.lt_irrefl 0).
             assumption.
          -- assert (compare_leq xi x1).
             apply first_two_of_is_sorted_are_sorted with (xs := xs'').
             assumption.

             Print pred.
             assert (j0 = S (pred j0)).
             destruct j0; lia.

             destruct (pred j0) as [| j0minus2].

             ++ assert (xj = x1).
                unfold xj.
                subst.
                unfold get.
                reflexivity.

                rewrite H3.
                resolve_compare_leq.

             ++ assert (compare_leq x1 xj).

                (* this follows from induction hypothesis, but it is a bit of work to set up *)
                assert (0 < length (x1 :: xs'')) as pf0.
                reduce_list_lengths. lia.

                subst.
                specialize IHxs' with
                            (i := (exist (fun n => n < length (x1 :: xs'')) 0 pf0))
                            (j := (exist (fun n => n < length (x1 :: xs''))(S j0minus2)
                                         (get_recursion_helper_dec pfj))).

                assert (0 < (S j0minus2)) as Hlt.
                lia.

                Check (tail_of_is_sorted_is_sorted H).
                apply (IHxs' (tail_of_is_sorted_is_sorted H) Hlt).

                apply compare_leq_trans with (y := x1); assumption.

        * destruct j0 as [| j0minus1 ].
          lia. (* deals with the case j0 = 0 (contradiction) *)

          destruct j0minus1 as [| j0minus2 ].
          lia. (* deals with the case j0 = 1 (contradiction) *)

          set (pfiminus1 := get_recursion_helper_dec pfi).
          set (pfjminus1 := get_recursion_helper_dec pfj).

          assert (i0minus1 < S j0minus2) as Hlt.
          lia.

          set (IH := IHxs'
                 (tail_of_is_sorted_is_sorted H)
                 (exist _ i0minus1 pfiminus1)
                 (exist _ (S j0minus2) pfjminus1)
              Hlt).

          assert (xi = get xs' (exist (fun n : nat => n < length xs') i0minus1 pfiminus1)) as xi_from_tail.
          subst xi.
          apply get_from_tail.


          assert (xj = get xs' (exist (fun n : nat => n < length xs') (S j0minus2) pfjminus1)) as xj_from_tail.
          subst xj.
          apply get_from_tail.

          rewrite xi_from_tail.
          rewrite xj_from_tail.
          assumption.

    - intros.
      induction xs as [| x0 xs'].
      + constructor.
      + destruct xs' as [| x1 xs''].
        * constructor.
        * assert (0 < length (x0 :: x1 :: xs'')) as pf0.
          reduce_list_lengths. lia.

          assert (1 < length (x0 :: x1 :: xs'')) as pf1.
          repeat reduce_list_lengths. lia.

          assert (x0 = get (x0 :: x1 :: xs'') (exist _ 0 pf0)) as Eqx0.
          unfold get. reflexivity.

          assert (x1 = get (x0 :: x1 :: xs'') (exist _ 1 pf1)) as Eqx1.
          unfold get. reflexivity.

          assert (compare_leq x0 x1) as Hfirsttwo.
          rewrite Eqx0.
          rewrite Eqx1.
          assert (0 < 1) as zerosmallerone. lia.
          set (H (exist _ 0 pf0) (exist _ 1 pf1) zerosmallerone).
          assumption.

          (* now we need to use the induction hypothesis, so we need to prove the hypothesis about indices *)
          assert (is_sorted (x1::xs'')).
          apply IHxs'.
          intros.
          destruct i as [i0 pfi].
          destruct j as [j0 pfj].
          intro Hlt.
          (* this follows from H *)
          Check Lt.lt_S_n.

          pose (H
                 (exist _ (S i0) (get_recursion_helper_inc x0 (x1 :: xs'') pfi))
                 (exist _ (S j0) (get_recursion_helper_inc x0 (x1 :: xs'') pfj))
                 (Lt.lt_n_S i0 j0 Hlt)) as Hasdfasdf.

          rewrite <- (get_from_tail (* (x1::xs'') x0 i0 *)
                                 pfi (get_recursion_helper_inc x0 (x1::xs'') pfi)).
          rewrite <- (get_from_tail (* (x1::xs'') x0 i0 *)
                                 pfj (get_recursion_helper_inc x0 (x1::xs'') pfj)).
          assumption.

          constructor.
          resolve_compare_leq.
          assumption.
  Qed.

End indices.

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
Abort.

(* sort is a helper function for eval_list_sort *)
Fixpoint sort {A: Type} {cmp: comparable A} (xs: list A) : list A :=
  match xs with
  | nil => nil
  | (x'::xs') => insert_sort (sort xs') x'
  end.

Theorem sort_sorts: forall {A: Type} {cmp: comparable A} (xs: list A),
  is_sorted (sort xs).
Proof.
Abort.
