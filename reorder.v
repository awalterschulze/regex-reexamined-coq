(*
Practice scenarios for proving reordering ORs in a regex.

Given an expression tree.
If the operators are:
  - associative
  - commutative
  - identity is present
Then reordering the tree should result in the same answer.
*)

Set Implicit Arguments.
Set Asymmetric Patterns.

Require Import List.
Require Import comparable.

Section Reorder.

(* A is an generic value *)
Variable A: Set.

(* A has a compare function which returns comparison *)
Variable HasCompareFunction: comparable A.

(* A has an operator
   Examples of the operator are:
   - addition
   - multiplication
   - and
   - or
*)
Variable Op: A -> A -> A.

(* A has an identity value *)
Variable Identity: A.
Parameter proof_id
    : forall (x: A)
    , Op x Identity = x.

(* The operator is associative *)
Parameter proof_assoc
    : forall (x y z: A)
    , (Op (Op x y) z) = (Op x (Op y z)).

(* The operator is commutative *)
Parameter proof_comm
    : forall (x y: A)
    , Op x y = Op y x.

(* eval_list evaluates the list using Op *)
Fixpoint eval_list (xs: list A) : A :=
    match xs with
    | nil => Identity
    | (x' :: xs') => Op x' (eval_list xs')
    end.

(* eval_list_swap swaps the evaluation order *)
Fixpoint eval_list_swap (xs: list A) : A :=
    match xs with
    | nil => Identity
    | (x' :: xs') => Op (eval_list_swap xs') x'
    end.

(* insert is a helper function for sort *)
Fixpoint insert (x: A) (xs: list A) : list A :=
    match xs with
    | nil => x :: nil
    | y::ys => match compare x y with
        | Eq => x::y::ys
        | Lt => x::y::ys
        | Gt => y::(insert x ys)
        end
    end.

(* sort is a helper function for eval_list_sort *)
Fixpoint sort (xs: list A) : list A :=
    match xs with
    | nil => nil
    | (x'::xs') => insert x' (sort xs')
    end.

(* eval_list_sort first sorts a list before evaluating it *)
Definition eval_list_sort (xs: list A) : A :=
    eval_list (sort xs).

(* eval_list_swap_is_correct shows that
   eval_list_swap is equivalent to eval_list
*)
Theorem eval_list_swap_is_correct
    : forall (xs: list A)
    , eval_list xs = eval_list_swap xs.
Proof.
intros.
induction xs.
- simpl.
  reflexivity.
- simpl.
  rewrite <- IHxs.
  rewrite proof_comm.
  reflexivity.
Qed.

(* eval_list_and_insert is an incremental lemma for eval_list_sort_is_correct *)
Lemma eval_list_and_insert
  : forall (x: A) (xs: list A)
  , eval_list (x::xs) = eval_list (insert x xs).
Proof.
  induction xs as [| y ys IH].
  - unfold insert. reflexivity.
  - unfold insert.
    case (compare x y).
    + reflexivity.
    + reflexivity.
    + fold insert.
      assert (eval_list (x :: y :: ys) = Op y (eval_list (x::ys))) as lem.
      simpl (eval_list (x :: _)).
      Check proof_assoc.
      rewrite <- (proof_assoc x y (eval_list ys)).
      rewrite -> (proof_comm x y).
      rewrite -> (proof_assoc y x (eval_list ys)).
      reflexivity.
      rewrite -> lem.
      simpl (eval_list (y :: _)).
      rewrite -> IH.
      reflexivity.
Qed.

(* eval_list_sort_is_correct shows that
   eval_list_sort is equivalent to eval_list
*)
Theorem eval_list_sort_is_correct
  : forall (xs: list A)
  , eval_list xs = eval_list_sort xs.
Proof.
  induction xs.
  - reflexivity.
  - unfold eval_list_sort.
    simpl (sort (a :: xs)).
    rewrite <- eval_list_and_insert.
    simpl (eval_list _).
    replace (eval_list (sort xs)) with (eval_list_sort xs).
    rewrite <- IHxs.
    reflexivity.
    unfold eval_list_sort.
    reflexivity.
Qed.

(* eval_list_and_insert' is an alternative proof for eval_list_and_insert,
   which an incremental lemma for eval_list_sort_is_correct' *)
Lemma eval_list_and_insert'
  : forall (x: A) (xs: list A)
  , eval_list (x::xs) = eval_list (insert x xs).
Proof.
induction xs.
(* inserting into a single element into an empty list is always the same *)
- reflexivity.
- (* unfold the insert function, to get to the compare function *)
  simpl.
  (* where an element will be inserted depends on the compare function,
     so lets do induction on that compare
  *)
  induction (compare x a).
  (* when the compare is LT
     then it is the same as prepending the element.
  *)
  + reflexivity.
  (* when the compare is EQ
     then it is the same as prepending the element.
  *)
  + reflexivity.
  (* when the compare is GT
     this is the case where the order changes.
  *)
  + simpl.
  (* rewriting with the induction hypothesis, removes insert *)
    rewrite <- IHxs.
    simpl.
  (* now we are left with:
     `Op x (Op a (eval_list xs)) = Op a (Op x (eval_list xs))`
     Lets group `(Op x a)` and `(Op a x)` together using associativity.
  *)
    rewrite <- proof_assoc.
    rewrite <- proof_assoc.
  (* Now we can swap `Op x a` to `Op a x` for one case using commutativity. *)
    rewrite proof_comm with (x := x) (y := a).
  (* And we get:
     `Op (Op a x) (eval_list xs) = Op (Op a x) (eval_list xs)`
  *)
    reflexivity.
Qed.

(* eval_list_sort_is_correct' is an alternative proof for eval_list_sort_is_correct,
   which shows that eval_list_sort is equivalent to eval_list
*)
Theorem eval_list_sort_is_correct'
  : forall (xs: list A)
  , eval_list xs = eval_list_sort xs.
Proof.
induction xs.
(* evaluating an empty list is always the same *)
- reflexivity.
(* We want to get to a pointer where we can rewrite using our incremental helper: 
   `eval_list (insert x xs)` into `eval_list (x::xs)`,
   but we have `eval_list (a :: xs) = eval_list_sort (a :: xs)`
*)
- unfold eval_list_sort; simpl sort.
  (* unfolding and evaluating sort a bit gives us:
     `eval_list (a :: xs) = eval_list (insert a (sort xs))` 
     We can now rewrite using our incremental helper,
     where: `xs` is `sort xs`*)
  rewrite <- eval_list_and_insert'.
  (* Now we get: `eval_list (a :: xs) = eval_list (a :: sort xs)`*)
  simpl.
  (* Now we can use our induction hypothesis:
     `eval_list xs = eval_list_sort xs`
  *)
  rewrite IHxs.
  (* This gives us:
     `Op a (eval_list_sort xs) = Op a (eval_list (sort xs))`
     And from the definition we know:
     `eval_list_sort xs = eval_list (sort xs)`.
  *)
  unfold eval_list_sort.
  reflexivity.
Qed.

(* tree is a generic tree with values *)
Inductive tree (A: Set) :=
    | value : A -> tree A
    | bin : tree A -> tree A -> tree A.
   
(* eval_tree evaluates the tree using Op *)
Fixpoint eval_tree (tx: tree A) : A :=
    match tx with
    | value v => v
    | bin l r => Op (eval_tree l) (eval_tree r)
    end.

(* eval_tree_swap swaps the evaluation order *)
Fixpoint eval_tree_swap (tx: tree A) : A :=
    match tx with
    | value v => v
    | bin l r => Op (eval_tree_swap r) (eval_tree_swap l)
    end.

(* to_list converts a tree to a list *)
Fixpoint to_list (tx: tree A) : list A :=
    match tx with
    | value v => v :: nil
    | bin l r => to_list l ++ to_list r
    end.

(* to_tree converts a list to a tree.
   The empty list results in a tree with an identity element.
*)
Fixpoint to_tree (xs: list A) : tree A :=
    match xs with
    | nil => value Identity
    | (x::nil) => value x
    | (x'::xs') => bin (value x') (to_tree xs')
    end.

(* eval_tree_sort first sorts a tree before evaluating it *)
Definition eval_tree_sort (tx: tree A) : A :=
    eval_tree (to_tree (sort (to_list tx))).

(* eval_list_concatenation is a helper lemma for
   eval_tree_factorizes_through_eval_list, which is a helper lemma for
   eval_tree_sort_is_correct
*)
Lemma eval_list_concatenation
  : forall (xs ys : list A)
  , eval_list (xs ++ ys) = Op (eval_list xs) (eval_list ys).
Proof.
  induction xs.
  - intros ys.
    simpl.
    rewrite proof_comm.
    rewrite proof_id.
    reflexivity.
  - intros ys.
    simpl eval_list at 2.
    simpl eval_list at 1.
    rewrite (IHxs ys).
    rewrite proof_assoc.
    reflexivity.
Qed.

(* eval_tree_factorizes_through_eval_list is a helper lemma for
   eval_tree_sort_is_correct
*)
Lemma eval_tree_factorizes_through_eval_list
  : forall (xs: tree A)
  , eval_tree xs = eval_list (to_list xs).
Proof.
  induction xs.
  - unfold to_list.
    unfold eval_list.
    unfold eval_tree.
    rewrite proof_id.
    reflexivity.
  - simpl (eval_tree (bin _ _)).
    simpl (to_list _).
    simpl (eval_list _).
    rewrite eval_list_concatenation.
    rewrite IHxs1.
    rewrite IHxs2.
    reflexivity.
Qed.

(* to_list_to_tree is a helper lemma for eval_tree_sort_is_correct *)
Lemma to_list_to_tree
  : forall (xs : list A)
  , eval_list (to_list (to_tree xs)) = eval_list xs.
Proof.
  induction xs.
  - unfold to_tree.
    unfold to_list.
    unfold eval_list.
    rewrite proof_id.
    reflexivity.
  - induction xs.
    + unfold to_tree.
      unfold to_list.
      simpl.
      repeat (rewrite proof_id); reflexivity.
    + induction xs.
      -- unfold to_tree, to_list, app; reflexivity.
         (* the below is not so nice, but I can't get Coq to find the replacements itself *)
      -- replace (to_list (to_tree (a :: a0 :: a1 :: xs)))
           with (a :: (to_list (to_tree (a0 :: a1 :: xs)))).
         replace (eval_list (a :: a0 :: a1 :: xs))
                 with (Op a (eval_list (a0 :: a1 :: xs))).
         unfold eval_list at 1.
         fold eval_list.
         rewrite IHxs; reflexivity.
         unfold eval_list; reflexivity.
         unfold to_tree, to_list; reflexivity.
Qed.

(* eval_tree_swap_is_correct shows that
   eval_tree_swap is equivalent to eval_tree
*)
Theorem eval_tree_swap_is_correct
    : forall (xs: tree A)
    , eval_tree xs = eval_tree_swap xs.
Proof.
intros.
induction xs.
- simpl.
  reflexivity.
- simpl.
  rewrite proof_comm.
  rewrite IHxs1.
  rewrite IHxs2.
  reflexivity.
Qed.

(* eval_tree_sort_is_correct shows that
   eval_tree_sort is equivalent to eval_tree
*)
Theorem eval_tree_sort_is_correct
    : forall (xs: tree A)
    , eval_tree xs = eval_tree_sort xs.
Proof.
  intros xs.
  unfold eval_tree_sort.
  repeat rewrite eval_tree_factorizes_through_eval_list.
  rewrite to_list_to_tree.
  (* the following replace also seems like it shouldn't be necessary *)
  replace (eval_list (sort (to_list xs)))
    with (eval_list_sort (to_list xs)).
  apply eval_list_sort_is_correct.
  unfold eval_list_sort; reflexivity.
Qed.

(* eval_list_concatenation' is a helper lemma for
   eval_tree_factorizes_through_eval_list', which is a helper lemma for
   eval_tree_sort_is_correct'
*)
Lemma eval_list_concatenation'
  : forall (xs ys : list A)
  , eval_list (xs ++ ys) = Op (eval_list xs) (eval_list ys).
Proof.
induction xs.
- simpl.
  intros ys.
  rewrite proof_comm.
  rewrite proof_id.
  reflexivity.
- simpl.
  intros.
  rewrite IHxs.
  rewrite proof_assoc.
  reflexivity.
Qed.

(* eval_tree_factorizes_through_eval_list' is a helper lemma for
   eval_tree_sort_is_correct'
*)
Lemma eval_tree_factorizes_through_eval_list'
  : forall (xs: tree A)
  , eval_tree xs = eval_list (to_list xs).
Proof.
induction xs.
- simpl.
  rewrite proof_id.
  reflexivity.
- simpl.
  rewrite eval_list_concatenation'.
  rewrite IHxs1.
  rewrite IHxs2.
  reflexivity.
Qed.

(* to_list_to_tree' is a helper lemma for eval_tree_sort_is_correct' *)
Lemma to_list_to_tree'
  : forall (xs : list A)
  , eval_list (to_list (to_tree xs)) = eval_list xs.
Proof.
induction xs.
- simpl. rewrite proof_id. reflexivity.
- induction xs.
  + simpl. rewrite proof_id. reflexivity.
  + (* We are two levels into induction:
    `eval_list (to_list (to_tree (a :: a0 :: xs))) = eval_list (a :: a0 :: xs)`
    We want to pull `a` to the front of the expression and get:
    `Op a (eval_list (to_list (to_tree (a0 :: xs))))`
    So we can use our induction hypothesis:
    `eval_list (to_list (to_tree (a0 :: xs))) = eval_list (a0 :: xs)`
    To do this, we want to restrict the unfolding of to_tree to only unfold when it can resolve a match.
    We use: `Arguments to_tree: simpl nomatch.` to do this, see the docs here:
    https://coq.inria.fr/distrib/current/refman/proof-engine/tactics.html?highlight=simpl%20nomatch#coq:tacn.simpl
    *)
    Arguments to_tree: simpl nomatch.
    simpl to_tree.
    (* We have now moved `a` out of to_tree:
    `eval_list (to_list (bin (value a) (to_tree (a0 :: xs)))) = eval_list (a :: a0 :: xs)`
    Now we want to move `a` out of to_list.
    To do this we use the same trick to restrict the simplification of to_list.
    *)
    Arguments to_list: simpl nomatch.
    simpl to_list.
    (* We have now moved `a` out of to_list:
    `eval_list (a :: to_list (to_tree (a0 :: xs))) = eval_list (a :: a0 :: xs)`
    Now we want to move the `a` out of eval_list.
    To do this we use the same trick again to limit the reductions applied to eval_list.
    *)
    Arguments eval_list: simpl nomatch.
    simpl eval_list.
    (* We have moved `a` all the way out of the eval_list expression:
    `Op a (eval_list (to_list (to_tree (a0 :: xs)))) = Op a (Op a0 (eval_list xs))`
    Now we can apply our hypothesis.
    *)
    rewrite IHxs.
    simpl.
    reflexivity.
Qed.

(* eval_tree_sort_is_correct' shows that
   eval_tree_sort is equivalent to eval_tree
*)
Theorem eval_tree_sort_is_correct'
    : forall (xs: tree A)
    , eval_tree xs = eval_tree_sort xs.
Proof.
intros.
unfold eval_tree_sort.
(* 
We have to prove:
`eval_tree xs = eval_tree (to_tree (sort (to_list xs)))`
We can rewrite eval_tree to get to eval_list:
`eval_tree xs = eval_list (to_list xs)`
*)
rewrite eval_tree_factorizes_through_eval_list'.
rewrite eval_tree_factorizes_through_eval_list'.
(*
Now we can forget about eval_tree and focus on eval_list.
`eval_list (to_list xs) = eval_list (to_list (to_tree (sort (to_list xs))))`
We know that `to_list . to_tree = id`:
`eval_list (to_list (to_tree xs)) = eval_list xs.`
*)
rewrite to_list_to_tree'.
(*
So we can remove `to_list (to_tree` from the equation:
`eval_list (to_list xs) = eval_list (sort (to_list xs))`
We have already proven that evaluation is not effected by sorting:
`eval_list xs = eval_list_sort xs`
*)
rewrite eval_list_sort_is_correct.
(*
And from definition we know that:
`eval_list_sort = eval_list . sort`
*)
unfold eval_list_sort.
reflexivity.
Qed.


(* to_tree_id converts a list to a tree.
   The final element in the tree is always the Identity element.
*)
Fixpoint to_tree_id (xs: list A) : tree A :=
  match xs with
  | nil => value Identity
  | (x'::xs') => bin (value x') (to_tree xs')
  end.

(* eval_tree_sort_id first sorts a tree before evaluating it *)
Definition eval_tree_sort_id (tx: tree A) : A :=
    eval_tree (to_tree_id (sort (to_list tx))).

(* eval_tree_sort_id_is_correct shows that
   eval_tree_sort is equivalent to eval_tree
*)
Theorem eval_tree_sort_id_is_correct
    : forall (xs: tree A)
    , eval_tree xs = eval_tree_sort_id xs.
Proof.
(* TODO: Good First Issue *)
Admitted.

End Reorder.