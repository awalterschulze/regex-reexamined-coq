Set Implicit Arguments.
Set Asymmetric Patterns.

Require Import Bool.
Require Import List.
Require Import Omega.

Require Import Coq.Program.Program.

Require Import comparable.
Require Import compare_regex.
Require Import dup.
Require Import derive.
Require Import nullable.
Require Import orb_simple.
Require Import regex.
Require Import size.
Require Import sort.

(*
Here we define smart_or and smart_or'.
These are smart constructors which apply simplification rules during construction to normalize the expression.
This is useful for minimizing the state space.
These smart constructors assume that the regular expressions provided as input has also been smart constructed.

 - smart_or: applies the minimal simplification rules: idempotency, associativity and commutativity.
 - smart_or': applies more simplification rules.
*)

(* TODO: Help Wanted
Define a property `is_merge_or` that expresses the type the `merge_or` function returns.
`is_merge_or {X: Set} {tc: comparable X} (r: regex X) : Prop`
It should express that the tree is sorted and duplicates have been removed.
*)

(* TODO: Help Wanted
Use the previous defined property `is_merge_or` to prove:
```
merge_or_is_correct: forall {X: Set} {tc: comparable X} 
  (r s: regex X) (is_merge_or r) (is_merge_or s),
  is_merge_or (merge_or r s)
```
*)

(* TODO: Help Wanted
Call merge_or, instead of this naive smart_or function, that doesn't reorder recursively.
It will break proofs in other files, so this todo is more about fixing those proofs.
*)
Definition smart_or {X: Set} {tc: comparable X} (r s: regex X) : regex X :=
  match compare_regex r s with
  | Eq => s
  | Lt => or r s
  | Gt => or s r
  end.

(* merge_or merges two regexes.
It applies a merge sort on the root ors, while removing duplicates.
It can do this because of the following properties:
  idempotency: r + r = r
  commutativity: r + s = s + r
  associativity: (r + s) + t = r + (s + t)
It does this to normalize the regular expression.
It assumes the two regexes that is provided as input is already sorted with duplicates removed.

For a Fixpoint function Coq always needs to know which argument is decreasing.
For merge_or either `r` or `s` is decreasing, which is confusing to the termination checker, we need to be consistent.
We introduce a closure fixpoint `merge_or_r` inside of our fixpoint `merge_or`.
merge_or's descreasing argument is always `r` and
merge_or_r's decreasing argument is always `s`, while `r` is not decreasing and is the original `r`, hence `_or_r`.

For another example for a closure fixpoint inside a fixpoint, see the merge function in:
https://coq.inria.fr/library/Coq.Sorting.Mergesort.html 
*)
Fixpoint merge_or {X: Set} {tc: comparable X} (r s: regex X) : regex X :=
  let fix merge_or_r s :=
    match r with
    | or r_1 r_next =>
      match s with
      | or s_1 s_next =>
        match compare r_1 s_1 with
        | Lt => or r_1 (merge_or r_next s)
        | Eq => or r_1 (merge_or r_next s_next)
        | Gt => or s_1 (merge_or_r s_next)
        end
      | _ =>
        match compare r_1 s with
        | Lt => or r_1 (merge_or r_next s)
        | Eq => r
        | Gt => or s r
        end
      end
    | _ =>
      match s with
      | or s_1 s_next =>
        match compare r s_1 with
        | Lt => or r s
        | Eq => s
        | Gt => or s_1 (merge_or_r s_next)
        end
      | _ =>
        match compare r s with
        | Lt => or r s
        | Eq => s
        | Gt => or s r
        end
      end
    end
  in merge_or_r s.

(* merge_or_step rewrite merge_or without an fix closure,
   which was just there so Coq can see that the function is terminating.
   This way the function is easier to read and smaller steps can be taken inside proofs.
*)
Theorem merge_or_step: forall {X: Set} {tc: comparable X} (r s: regex X),
  merge_or r s = match r with
  | or r_1 r_next =>
    match s with
    | or s_1 s_next =>
      match compare r_1 s_1 with
      | Lt => or r_1 (merge_or r_next s)
      | Eq => or r_1 (merge_or r_next s_next)
      | Gt => or s_1 (merge_or r s_next)
      end
    | _ =>
      match compare r_1 s with
      | Lt => or r_1 (merge_or r_next s)
      | Eq => r
      | Gt => or s r
      end
    end
  | _ =>
    match s with
    | or s_1 s_next =>
      match compare r s_1 with
      | Lt => or r s
      | Eq => s
      | Gt => or s_1 (merge_or r s_next)
      end
    | _ =>
      match compare r s with
      | Lt => or r s
      | Eq => s
      | Gt => or s r
      end
    end
  end.
Proof.
induction r, s; simpl; trivial.
Qed.

(* merged_or is a property that specifies whether a regex was merged with merge_or *)
Fixpoint merged_or {X: Set} {tc: comparable X} (r: regex X) : Prop :=
  match r with
  | or s t =>
    match s with
    | or _ _ => False
    | _ => match t with
      | or t_1 _ =>
        match compare s t_1 with
        | Lt => merged_or t
        | _ => False
        end
      | _ => match compare s t with
        | Lt => True
        | _ => False
        end
      end
    end
  | _ => True
  end.

Theorem merged_or_upholds: forall {X: Set} {tc: comparable X} (r s: regex X) (mr: merged_or r) (ms: merged_or s),
  merged_or (merge_or r s).
(* TODO: Help Wanted *)
Admitted.

Theorem merged_or_is_recursive: forall
  {X: Set}
  {tc: comparable X}
  (r s: regex X),
merged_or (or r s) -> merged_or r /\ merged_or s.
(* TODO: Good First Issue *)
Admitted.

(* nothing|r = r *)
Theorem merge_or_id: forall
  {X: Set}
  {tc: comparable X}
  (r: regex X)
  (xs: list X),
  matches (merge_or (nothing _) r) xs = matches r xs.
Proof.
intros.
induction r; try (simpl; or_simple; fail).
- induction r1; try (simpl; or_simple; fail).
Qed.

(* merge_or_empty is a helper Lemma for merge_or_is_or *)
Lemma merge_or_empty: forall
  {X: Set}
  {tc: comparable X}
  (r: regex X)
  (xs: list X),
  matches (or (empty _) r) xs = matches (merge_or (empty _) r) xs.
Proof.
intros.
induction r; try (simpl; or_simple; fail).
- induction r1; try (simpl; or_simple; fail).
  + assert (merge_or (empty X) (or (nothing X) r2) =
            or (nothing X) (merge_or (empty X) r2)).
    * simpl; or_simple. trivial.
    * rewrite H.  
      or_simple.
      rewrite <- or_is_logical_or.
      rewrite IHr2.
      reflexivity.
Qed.

(* merge_or_char is a helper Lemma for merge_or_is_or *)
Lemma merge_or_char: forall
  {X: Set}
  {tc: comparable X}
  (r: regex X)
  (xs: list X)
  (x: X),
  matches (or (char x) r) xs = matches (merge_or (char x) r) xs.
Proof.
intros.
induction r; try (simpl; or_simple; fail).
- simpl; or_simple.
  induction_on_compare; (simpl; or_simple).
- induction r1; try (simpl; or_simple; fail).
  + assert ((merge_or (char x) (or (nothing X) r2)) =
            (or (nothing X) (merge_or (char x) r2))
           ).
    * simpl; or_simple; trivial.
    * rewrite H.
      or_simple.
      rewrite <- or_is_logical_or.
      rewrite IHr2.
      reflexivity.
  + assert ((merge_or (char x) (or (empty X) r2)) =
            (or (empty X) (merge_or (char x) r2))
            ).
    * simpl; or_simple; trivial.
    * rewrite H.
      or_simple.
      rewrite <- IHr2.
      or_simple.
  + rewrite merge_or_step.
    induction_on_compare.
    * or_simple.
    * reflexivity.
    * or_simple.
      rewrite <- IHr2.
      or_simple.
Qed.

Theorem merge_or_is_or: forall
  {X: Set}
  {tc: comparable X}
  (xs: list X)
  (r: regex X)
  (s: regex X),
  matches (or r s) xs = matches (merge_or r s) xs.
Proof.
induction r.
- intros.
  induction s; try (simpl; or_simple; fail).
  + or_simple.
    rewrite merge_or_id.
    or_simple.
- intros.
  induction s; try (simpl; or_simple; fail).
  + rewrite merge_or_empty.
    reflexivity.
- intros.
  induction s; try (simpl; or_simple; fail).
  + simpl; or_simple.
    induction_on_compare; (simpl; or_simple).
  + rewrite merge_or_char. reflexivity.
- induction s.
  + simpl. or_simple.
    induction_on_compare_regex.
    * or_simple.
    * or_simple.
      rewrite <- IHr2.
      or_simple.
    * or_simple.
  + simpl; or_simple.
    induction_on_compare_regex.
    * or_simple.
    * or_simple.
      rewrite <- IHr2.
      or_simple.
    * or_simple.
  + simpl; or_simple.
    induction_on_compare_regex.
    * or_simple.
    * or_simple.
      rewrite <- IHr2.
      or_simple.
    * or_simple.
  + (* IHs1: matches (or (or r1 r2) s1) xs = matches (merge_or (or r1 r2) s1) xs *)
    (* IHs2: matches (or (or r1 r2) s2) xs = matches (merge_or (or r1 r2) s2) xs*)
    (* IHr1: forall s, matches (or r1 s) xs = matches (merge_or r1 s) xs *)
    (* IHr2: forall s, matches (or r2 s) xs = matches (merge_or r2 s) xs *)
    rewrite merge_or_step.
    induction_on_compare.
    * or_simple.
      rewrite <- IHr2.
      or_simple.
    * or_simple.
      rewrite <- IHr2.
      or_simple.
    * or_simple.
      rewrite <- IHs2.
      or_simple.
  + simpl; or_simple.
    induction_on_compare_regex.
    * or_simple.
    * or_simple. 
      rewrite <- IHr2.
      or_simple.
    * simpl; or_simple.
  + simpl; or_simple. 
    induction_on_compare_regex.
    * or_simple.
    * or_simple. 
      rewrite <- IHr2.
      or_simple.
    * simpl; or_simple.
  + simpl; or_simple.
    induction_on_compare_regex.
    * or_simple.
    * or_simple. 
      rewrite <- IHr2.
      or_simple.
    * simpl; or_simple.
  + simpl; or_simple.
    induction_on_compare_regex.
    * or_simple.
    * or_simple. 
      rewrite <- IHr2.
      or_simple.
    * simpl; or_simple.
- intros.
  induction s; try (simpl; or_simple; fail).
  + assert (merge_or (and r1 r2) (or s1 s2) =
      match compare (and r1 r2) s1 with
      | Lt => or (and r1 r2) (or s1 s2)
      | Eq => (or s1 s2)
      | Gt => or s1 (merge_or (and r1 r2) s2)
      end
    ) as step1. simpl; or_simple; trivial. rewrite step1.
    induction_on_compare.
    * or_simple.
    * reflexivity.
    * or_simple.
      rewrite <- IHs2.
      or_simple.
  + simpl; or_simple.
    induction_on_compare_regex; simpl; or_simple.
    * induction_on_compare_regex; simpl; or_simple.
- intros.
  induction s; try (simpl; or_simple; fail).
  + assert (merge_or (concat r1 r2) (or s1 s2) =
      match compare (concat r1 r2) s1 with
      | Lt => or (concat r1 r2) (or s1 s2)
      | Eq => (or s1 s2)
      | Gt => or s1 (merge_or (concat r1 r2) s2)
      end
    ) as step1. simpl; or_simple; trivial. rewrite step1.
    induction_on_compare.
    * or_simple.
    * reflexivity.
    * or_simple.
      rewrite <- IHs2.
      or_simple.
  + simpl; or_simple.
    induction_on_compare_regex; simpl; or_simple.
    * induction_on_compare_regex; simpl; or_simple.
- intros.
  induction s; try (simpl; or_simple; fail).
  + assert (merge_or (not r) (or s1 s2) =
      match compare (not r) s1 with
      | Lt => or (not r) (or s1 s2)
      | Eq => (or s1 s2)
      | Gt => or s1 (merge_or (not r) s2)
      end
    ) as step1. simpl; or_simple; trivial. rewrite step1.
    induction_on_compare.
    * or_simple.
    * reflexivity.
    * or_simple.
      rewrite <- IHs2.
      or_simple.
  + simpl; or_simple.
    induction_on_compare_regex; simpl; or_simple.
- intros.
  induction s; try (simpl; or_simple; fail).
  + assert (merge_or (zero_or_more r) (or s1 s2) =
      match compare (zero_or_more r) s1 with
      | Lt => or (zero_or_more r) (or s1 s2)
      | Eq => (or s1 s2)
      | Gt => or s1 (merge_or (zero_or_more r) s2)
      end
    ) as step1. simpl; or_simple; trivial. rewrite step1.
    induction_on_compare.
    * or_simple.
    * reflexivity.
    * or_simple.
      rewrite <- IHs2.
      or_simple.
  + simpl; or_simple.
    induction_on_compare_regex; simpl; or_simple.
Qed.

(* to_list_or is a helper function for smart_or'
It turns a regex into a list of ors, for example:
```
to_list_or (or nothing empty) = [nothing, empty]
to_list_or (or nothing (or empty (char x))) = [nothing, empty, char x]
```
It only turns the top level into ors and doesn't recurse past other operators:
```
to_list_or (or (and (or a b) c) (or empty (char x))) = [and (or a b) c, empty, char x]
```
It also doesn't recurse down the left side into or operators, 
since it expects the previous construction into a tree was done in a way that satifies this property:
```
to_list_or (or (or empty nothing) (or empty (or nothing empty))) = [or empty nothing, empty, nothing, empty]
```
*)
Fixpoint to_list_or {X: Set} {tc: comparable X} (r: regex X) : list (regex X) :=
  match r with
  | or s t => s :: to_list_or t
  | _ => r :: nil
  end.

(* to_tree_or creates a regex from a list of regexes by combining them with an `or` operator.
   At the end of the list a `nothing` expression is insert as this is the identity expression for `or.`
*)
Fixpoint to_tree_or {X: Set} (xs: list (regex X)) : regex X :=
  match xs with
  | nil => nothing _
  | (x'::xs') => or x' (to_tree_or xs')
  end.

(* TODO: Help Wanted
Define the property described in the comments of to_tree_or
Also find the appropriate/official name for this property.
I am pretty sure this tree of this form have a name:
  x
 / \
a   x
   / \
  b   x
     / \
    c   id
*)

(* to_list_or__to_tree_or__is_id shows that:
`to_tree_or . to_list_or = id`
*)
Theorem to_list_or__to_tree_or__is_id: forall {X: Set} {tc: comparable X} (r: regex X) (xs: list X),
  matches r xs = matches (to_tree_or (to_list_or r)) xs.
Proof.
induction r; try (simpl; intros xs; rewrite or_id; reflexivity).
- simpl.
  intros xs.
  rewrite or_is_logical_or.
  rewrite or_is_logical_or.
  rewrite IHr2.
  reflexivity.
Qed.

(*
  smart_or' applies all the following rules
  r + r = r
  r + s = s + r
  (r + s) + t = r + (s + t)
  r + nothing = r
*)
Definition smart_or' {X: Set} {tc: comparable X} (r s: regex X) : regex X :=
  to_tree_or (remove_duplicates_from_sorted (fold_left insert_sort (to_list_or r) (to_list_or s))).

(*
merge_or_program merges two regexes.
It applies a merge sort on the root ors, while removing duplicates.
It can do this because of the following properties:
  idempotency: r + r = r
  commutativity: r + s = s + r
  associativity: (r + s) + t = r + (s + t)
It does this to normalize the regular expression.
It assumes the two regexes that is provided as input is already sorted with duplicates removed.

Program Fixpoint is used to we can set `measure` as the fixpoint's descreasing argument.
For more details, see:
https://stackoverflow.com/questions/47816742/decreasing-argument-and-what-is-a-program-fixpoint
https://coq.inria.fr/refman/addendum/program.html

We use Section here to make sure we solve the obligations generated by Program,
before moving onto proving or defining something else.
*)
Section merge_or_section.

Set Transparent Obligations.

Program Fixpoint merge_or_program {X: Set} {tc: comparable X} (r s: regex X) {measure ((size r)+(size s))} : regex X :=
  match r with
  | or r_1 r_next =>
    match s with
    | or s_1 s_next =>
      match compare r_1 s_1 with
      | Lt => or r_1 (merge_or_program r_next s)
      | Eq => or r_1 (merge_or_program r_next s_next)
      | Gt => or s_1 (merge_or_program r s_next)
      end
    | _ =>
      match compare r_1 s with
      | Lt => or r_1 (merge_or_program r_next s)
      | Eq => r
      | Gt => or s r
      end
    end
  | _ =>
    match s with
    | or s_1 s_next =>
      match compare r s_1 with
      | Lt => or r s
      | Eq => s
      | Gt => or s_1 (merge_or_program r s_next)
      end
    | _ =>
      match compare r s with
      | Lt => or r s
      | Eq => s
      | Gt => or s r
      end
    end
  end.

(*
Program has now generated obligations for several branches that need to be proved.
They all look quite similar, for example:
`size r_next + size (or s_1 s_next) < size (or r_1 r_next) + size (or s_1 s_next)`
which when simplified, look like:
`size r_next + S (size s_1 + size s_next) < S (size r_1 + size r_next + S (size s_1 + size s_next))`
which is the same as:
`x + S (y + z) < S (w + x + S (y + z))`
This is true, but probably a large proof to do manually,
so we use tactic omega to prove it for us.
*)

Next Obligation.
simpl.
omega.
Qed.

Next Obligation.
simpl.
omega.
Qed.

Next Obligation.
simpl.
omega.
Qed.

Next Obligation.
simpl.
omega.
Qed.

Next Obligation.
simpl.
omega.
Qed.

End merge_or_section.