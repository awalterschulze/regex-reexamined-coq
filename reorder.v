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

(* X is an generic value *)
Variable X: Set.

(* X has a compare function which returns comparison *)
Variable HasCompareFunction: comparable X.

(* X has an operator
   Examples of the operator are:
   - addition
   - multiplication
   - and
   - or
*)
Variable Op: X -> X -> X.

(* X has an identity value *)
Variable Identity: X.
Parameter proof_id
    : forall (x: X)
    , Op x Identity = x.

(* The operator is associative *)
Parameter proof_assoc
    : forall (x y z: X)
    , (Op (Op x y) z) = (Op x (Op y z)).

(* The operator is commutative *)
Parameter proof_comm
    : forall (x y: X)
    , Op x y = Op y x.

(* eval_list evaluates the list using Op *)
Fixpoint eval_list (xs: list X) : X :=
    match xs with
    | nil => Identity
    | (x' :: xs') => Op x' (eval_list xs')
    end.

(* eval_list_swap swaps the evaluation order *)
Fixpoint eval_list_swap (xs: list X) : X :=
    match xs with
    | nil => Identity
    | (x' :: xs') => Op (eval_list_swap xs') x'
    end.

(* insert is a helper function for sort *)
Fixpoint insert (x: X) (xs: list X) : list X :=
    match xs with
    | nil => x :: nil
    | y::ys => match compare x y with
        | Eq => x::y::ys
        | Lt => x::y::ys
        | Gt => y::(insert x ys)
        end
    end.

(* sort is a helper function for eval_list_sort *)
Fixpoint sort (xs: list X) : list X :=
    match xs with
    | nil => nil
    | (x'::xs') => insert x' (sort xs')
    end.

(* eval_list_sort first sorts a list before evaluating it *)
Definition eval_list_sort (xs: list X) : X :=
    eval_list (sort xs).

(* eval_list_swap_is_correct shows that
   eval_list_swap is equivalent to eval_list
*)
Theorem eval_list_swap_is_correct
    : forall (xs: list X)
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

Lemma eval_list_and_insert
  : forall (x: X) (xs: list X)
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


Theorem eval_list_sort_is_correct
  : forall (xs: list X)
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


(* tree is a generic tree with values *)
Inductive tree (A: Set) :=
    | value : A -> tree A
    | bin : tree A -> tree A -> tree A.
   
(* eval_tree evaluates the tree using Op *)
Fixpoint eval_tree (tx: tree X) : X :=
    match tx with
    | value v => v
    | bin l r => Op (eval_tree l) (eval_tree r)
    end.

(* eval_tree_swap swaps the evaluation order *)
Fixpoint eval_tree_swap (tx: tree X) : X :=
    match tx with
    | value v => v
    | bin l r => Op (eval_tree_swap r) (eval_tree_swap l)
    end.

(* to_list converts a tree to a list *)
Fixpoint to_list (tx: tree X) : list X :=
    match tx with
    | value v => v :: nil
    | bin l r => to_list l ++ to_list r
    end.


(* to_tree converts a list to a tree.
   The empty list results in a tree with an identity element.
*)
Fixpoint to_tree (xs: list X) : tree X :=
    match xs with
    | nil => value Identity
    | (x'::x''::nil) => bin (value x') (value x'')
    | (x'::xs') => bin (value x') (to_tree xs')
    end.

(* eval_tree_sort first sorts a tree before evaluating it *)
Definition eval_tree_sort (tx: tree X) : X :=
    eval_tree (to_tree (sort (to_list tx))).



Lemma eval_list_concatenation
  : forall (xs ys : list X)
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


(* eval_tree factorizes through eval_list *)
Proposition eval_tree_factorizes_through_eval_list
  : forall (xs: tree X)
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

Lemma to_list_to_tree
  : forall (xs : list X)
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
    : forall (xs: tree X)
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
    : forall (xs: tree X)
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

End Reorder.