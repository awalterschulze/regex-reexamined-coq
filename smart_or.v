Set Implicit Arguments.
Set Asymmetric Patterns.

Require Import List.

Require Import comparable.
Require Import compare_regex.
Require Import derive.
Require Import nullable.
Require Import regex.

Definition type_or {X: Set} (r: regex X) : Prop :=
  match r with
  | or _ _ => True
  | _ => False
  end.

(* TODO: Help Wanted
Define a property `is_smart_or` that expresses the type the `smart_or` function returns.
`smart_or {X: Set} {tc: comparable X} (r: regex X) : Prop`
*)

(* TODO: Help Wanted
Use the previous defined property `is_smart_or` to prove:
```
smart_or_is_correct: forall {X: Set} {tc: comparable X} 
  (r s: regex X) (is_smart_or r) (is_smart_or s),
  is_smart_or (smart_or r s)
```
*)

(* TODO: add associativity, waiting for reorder proofs *)
Definition smart_or {X: Set} {tc: comparable X} (r s: regex X) : regex X :=
  match compare_regex r s with
  | Eq => s
  | Lt => or r s
  | Gt => or s r
  end.

(* to_list_or turns a regex into a list of ors, for example:
to_list_or (or nothing empty) = [nothing, empty]
to_list_or (or nothing (or empty (char x))) = [nothing, empty, char x]
It only turns the top level into ors and doesn't recurse past other operators:
to_list_or (or (and (or a b) c) (or empty (char x))) = [and (or a b) c, empty, char x]
It also doesn't recurse down the left side into or operators, 
since it expects the previous construction into a tree was done in a way that satifies this property:
to_list_or (or (or empty nothing) (or empty (or nothing empty))) = [or empty nothing, empty, nothing, empty]
*)
Fixpoint to_list_or {X: Set} {tc: comparable X} (r: regex X) : list (regex X) :=
  match r with
  | or s t => s :: to_list_or t
  | _ => r :: nil
  end.

(* TODO: Help Wanted
Define the property described in the comments of to_list_or
Also find the appropriate/official name for this property.
I am pretty sure this already has a name, but I can't find or remember it.
*)

(* to_tree_or creates a regex from a list of regexes by combining them with an `or` operator.
   At the end of the list a `nothing` expression is insert as this is the identity expression for `or.`
*)
Fixpoint to_tree_or {X: Set} (xs: list (regex X)) : regex X :=
  match xs with
  | nil => nothing _
  | (x'::xs') => or x' (to_tree_or xs')
  end.

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

