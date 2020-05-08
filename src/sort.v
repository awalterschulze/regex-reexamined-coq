Set Implicit Arguments.
Set Asymmetric Patterns.

Require Import List.

Require Import Psatz.
Require Import Lia.

Require Import comparable.

(* TODO:
  - change Admitted to Abort
  - rename X to A and tc to cmp
  *)

(* is_sorted is a property that says whether a list is sorted *)
Inductive is_sorted {X: Set} {tc: comparable X} : list X -> Prop :=
  | empty_sorted : is_sorted nil
  | singleton_sorted (x: X) : is_sorted (x :: nil)
  | tail_sorted
    (x: X)
    (y: X)
    (c : compare x y = Lt \/ compare x y = Eq)
    (xs: list X)
    (s: is_sorted (y :: xs))
    : is_sorted (x :: y :: xs)
.

(* This is not really a bool... *)
Fixpoint is_sortedb {X: Set} {tc: comparable X} (xs: list X) : Prop :=
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
  {X: Set}
  {tc: comparable X}
  (x x' : X)
  (xs: list X):
  ((compare x x' = Lt) \/ (compare x x' = Eq)) ->
  (is_sortedb (x'::xs)) ->
  is_sortedb (x::x'::xs).
Proof.
  intros.
  unfold is_sortedb.
  destruct H; rewrite H; trivial.
Qed.

Inductive is_sorted'' {X: Set} {tc: comparable X} : list X -> Prop :=
  | empty_sorted'' : is_sorted'' nil
  | singleton_sorted'' : forall x, is_sorted'' (x :: nil)
  | lessthan_sorted''
    : forall (x: X) (xs: list X),
      (exists (y: X) (ys: list X),
      xs = (y :: ys)
      /\ compare x y = Lt)
      /\ is_sorted'' xs
      -> is_sorted'' (x :: xs)
  | equal_sorted''
    : forall (x: X) (xs: list X),
      (exists (y: X) (ys: list X),
      xs = (y :: ys)
      /\ compare x y = Eq)
      /\ is_sorted'' xs
      -> is_sorted'' (x :: xs)
.


Lemma tail_of_is_sorted_is_sorted:
  forall {X: Set}
  {tc: comparable X}
  (x: X)
  (xs: list X),
  is_sorted (x :: xs) -> is_sorted xs.
Proof.
  intros.
  inversion H; subst; (constructor || assumption).
Qed.

Lemma first_two_of_is_sorted_are_sorted:
  forall {X: Set}
  {tc: comparable X}
  (x y: X)
  (xs: list X),
  is_sorted (x :: y :: xs) -> compare_leq x y.
Proof.
  intros.
  unfold compare_leq.
  inversion H.
  apply or_comm.
  assumption.
Qed.

Lemma tail_of_is_sortedb_is_sortedb:
  forall {X: Set}
  {tc: comparable X}
  (x: X)
  (xs: list X),
  is_sortedb (x :: xs) -> is_sortedb xs.
Proof.
(* TODO: Good First Issue *)
Admitted.

Lemma tail_of_is_sorted''_is_sorted'':
  forall {X: Set}
  {tc: comparable X}
  (x: X)
  (xs: list X),
  is_sorted'' (x :: xs) -> is_sorted'' xs.
Proof.
(* TODO: Good First Issue *)
Admitted.

Lemma list_inductive_equality: forall {X: Set} {tc: comparable X} (x y: X) (xs ys: list X),
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


(* I don't know if we can use the definition of is_sortedb in this way. *)

(* This follows the ideas (and some of the notation) from Ch. 15 of CPDT *)
Inductive partial (P: Prop) : Set :=
| Proved : P -> partial P
| Uncertain : partial P.

Notation "[ P ]" := (partial P).

(* comparison -> [is_sorted xs] *)

Section reflection.
  Context {X: Set}.
  Context {tc: comparable X}.


  (* This is a certified decision procedure (as in Ch. 15 in [CPDT]). It is essentially
   the same as our definition of is_sortedb, except that instead of giving True or False
   as the end result, the end result is a dependent type, which shows that it is correct. *)
  Definition check_is_sorted: forall (xs: list X), [is_sorted xs].
    Hint Constructors is_sorted. (* TODO: deprecated *)

    (* The essence of the statement below is as simple as is_sortedb. The only thing that makes it look
     more complicated is that we need to use the "convoy trick" (see [CPDT]) twice. *)
    refine (fix F (xs : list X): [is_sorted xs] :=
              match xs return [is_sorted xs] with
              | nil => Proved _
              | (x0::xs') =>
                (match xs' as l return (xs' = l) -> [is_sorted (x0::xs')] with
                  | nil => (fun _ => Proved _)
                  | (x1::xs'') =>
                    (fun l0 =>
                    (let comp := (compare x0 x1) in
                     (match comp as H return (compare x0 x1 = H) -> [is_sorted (x0::xs')] with
                      | Gt => (fun _ => Uncertain _)
                      | _ => (fun Hcomp =>
                                if (F xs')
                                then Proved _
                                else Uncertain _)
                      end) _))
                  end) _
              end); subst; constructor; auto.
  Defined.
End reflection.

Section lemmas.
  Context {X: Set}.
  Context {tc: comparable X}.

  Lemma is_sortedb_reverse_direction (x y : X) (xs : list X):
    is_sortedb (x::y::xs) ->
    (compare x y = Lt \/ compare x y = Eq) /\ (is_sortedb (y::xs)).
  Proof.
    intros.
    unfold is_sortedb in H.
    split.
    - destruct (compare x y) eqn:Hcomp.
      + apply or_intror. reflexivity.
      + apply or_introl. reflexivity.
      + contradiction.
    - fold (is_sortedb (y::xs)) in H.
      destruct (compare x y); (assumption || contradiction).
  Qed.
End lemmas.

Theorem is_sorted_and_is_sortedb_are_equivalent : forall {X: Set} {tc: comparable X} (xs: list X),
  is_sorted xs <-> is_sortedb xs.
Proof.
Hint Unfold is_sortedb. (* TODO: deprecated *)
Hint Resolve is_sortedb_induction_step.

split.
- induction xs as [(*nil*)| x0 xs' IH]; auto.
  intros.
  try (match goal with
       | [ H: is_sorted ?xs |- _] => inversion H
       end); subst; auto.

- induction xs as [| x0 xs'].
  + intros.
    constructor.
  + intros.
    destruct xs' eqn:?.
    * constructor.
    * set (Hsort := is_sortedb_reverse_direction _ _ _ H).
      destruct Hsort as [Hcomp Hsublist].
      constructor; auto.
Qed.

Theorem is_sortedb_and_is_sorted''_are_equivalent : forall {X: Set} {tc: comparable X} (xs: list X),
  is_sortedb xs <-> is_sorted'' xs.
Proof.
(* TODO: Good First Issue *)
Admitted.

Section indices.
  Context {X: Set}.
  Context {tc: comparable X}.

  Lemma get_recursion_helper (n : nat) (x : X) (xs : list X):
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

  Definition get_recursion_helper_dec (n : nat) (x : X) (xs : list X):
    (S n < length (x :: xs)) -> (n < length xs) :=
    fun (H : S n < length (x :: xs)) => Lt.lt_S_n n (length xs) H.

  Definition get_recursion_helper_inc (n : nat) (x : X) (xs : list X):
    (n < length xs) -> (S n < length (x :: xs)) :=
    fun (H : n < length (xs)) => Lt.lt_n_S n (length xs) H.

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
  Proof.
    auto.
  Qed.


  Lemma reduce_list_lengths_by_one:
    forall (x: X) (xs: list X),
      length (x :: xs) = S (length xs).
  Proof. auto. Qed.

  Local Ltac nat_smaller_than_length_nil :=
        (* The below just derives a contradiction when there is a nat n with n < length nil *)
        repeat (match goal with
                | [ P : {n : nat | n < length nil } |- _] => destruct P
                | [ P : _ < length nil |- _ ] => rewrite (length_nil) in P
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

  (* Definition get_recursion_helper_dec_exist {x : X} {xs : list X}: *)
  (*   { n : nat | S n < length (x :: xs)} -> { n : nat | n < length xs }. *)
  (* Proof. *)
  (*   intro ipf. *)
  (*   destruct ipf as [i pf]. *)
  (*   apply get_recursion_helper in pf. *)
  (*   exact (exist _ i pf). *)
  (* Defined. *)

  (* Print get_recursion_helper_dec_exist. *)

  (* (* This just says that the map *) *)
  (* Lemma get_recursion_helper_dec_proj (ipf : {n : nat | S n < length (x :: xs)}): *)
  (*   proj1_sig ipf *)

  (* apply get_recursion_helper. Qed. *)


  Fixpoint get (xs: list X): { n: nat | n < (length xs)} -> X.
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
  Definition get' (xs: list X): { n: nat | n < (length xs)} -> X.
    intro H. destruct H as [n pf].
    destruct (nth_error xs n) eqn:?.
    - exact x.
    - exfalso.
      (* This is basically an application of nth_error_nth', except that we
       somehow need to get a default element... we can get this from the fact
       that n < length xs, which implies that xs has at least one elemnt.

       So I can imagine this could be automated with some appropriate hints. *)
      destruct xs as [| x0 xs'] eqn:Hxs.
      * replace (length nil) with 0 in pf.
        apply (PeanoNat.Nat.nlt_0_r n). assumption.
        auto.
      * set (@nth_error_nth' X (x0::xs') n x0).
        rewrite e in Heqo.
        discriminate Heqo.
        assumption.
  Defined.

  (* Maybe it would have been better to just use nth_error together
  with some tactics that prove that the bounds are correct. *)

  Lemma get_from_tail:
    forall (xs : list X) (x: X)
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
    forall (xs: list X)
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
    forall (xs ys : list X)
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
    forall (xs ys : list X)
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


  (*     erewrite get_from_tail with (x := x0) (xs := (xs' ++ ys)). *)


  (*     get_proof_recursion_helpers_rewrite. *)
  (*     Check (i - length xs'). *)

  (*     intros. *)
  (*     cbn in *. *)
  (*     assert (i - 0 = i). *)
  (*     lia. *)
  (*     unfold get. *)
  (*     cbn. *)
  (*     trivial. *)
  (*     reflexivity. *)
  (*     exfalso. *)
  (*     nat_smaller_than_length_nil. *)
  (*   - destruct i as [| iminus1]. *)
  (*     + unfold get. trivial. *)
  (*     + *)
  (*       replace ((x0 :: xs') ++ ys) with (x0 :: (xs' ++ ys)). *)
  (*       2: { exact eq_refl. } *)
  (*       intros. *)

  (*       Local Ltac get_proof_recursion_helpers := *)
  (*         match goal with *)
  (*         | H: (S ?n < length (?x :: ?xs)) |- _ *)
  (*           => assert_if_not_exist (n < length(xs)); try exact (@get_recursion_helper_dec n x xs H) *)
  (*         end. *)

  (*       (* All you need to do here is rewrite get_from_tail in two places, and *)
  (*       then apply the induction hypothesis. *) *)

  (*       repeat get_proof_recursion_helpers. *)
  (*       unshelve erewrite get_from_tail. assumption. *)
  (*       unshelve erewrite get_from_tail. assumption. *)

  (*       apply IHxs'. *)
  (* Qed. *)


  Theorem is_sorted_via_indices (xs: list X):
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
Lemma insert_sort_sorts: forall {X: Set} {tc: comparable X} (xs: list X) (x: X) {s: is_sorted xs},
  is_sorted (insert_sort xs x).
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
  is_sorted (sort xs).
Proof.
  Abort.
