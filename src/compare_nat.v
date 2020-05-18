(*
compare_nat contains comparable_nat,
which is a instance of comparable for nat.
*)

Set Implicit Arguments.
Set Asymmetric Patterns.

Require Import List.

Require Import comparable.

Definition nat_compare := Nat.compare.

Lemma nat_proof_compare_eq_is_equal:
  forall (x y: nat)
         (p: nat_compare x y = Eq),
    x = y.
Proof.
induction x, y.
- compute. trivial.
- compute. intros. discriminate.
- compute. intros. discriminate.
- simpl.
  intros.
  remember (IHx y p).
  rewrite e.
  reflexivity.
Qed.

Lemma nat_proof_compare_eq_is_equal' x y:
  nat_compare x y = Eq ->
  x = y.
Proof.
(* Because of how the lemma is stated, `x' and `y' are already introduced into
   the context, causing our inductive hypothesis to become too weak to solve the
   goal. `generalize dependent y' returns `y' to the goal and makes sure any
   dependent terms are updated. *)
generalize dependent y.
induction x, y.
- compute. trivial.
- compute. intros. discriminate.
- compute. intros. discriminate.
- simpl.
  intros.
  remember (IHx y H).
  rewrite e.
  reflexivity.
Qed.

Lemma nat_proof_compare_eq_reflex
  : forall (x: nat)
  , nat_compare x x = Eq.
Proof.
(* TODO *)
Admitted.

Lemma nat_proof_compare_eq_trans
  : forall (x y z: nat)
           (p: nat_compare x y = Eq)
           (q: nat_compare y z = Eq)
  , nat_compare x z = Eq.
Proof.
(* TODO *)
Admitted.

Lemma nat_proof_compare_lt_trans
  : forall (x y z: nat)
           (p: nat_compare x y = Lt)
           (q: nat_compare y z = Lt)
  , nat_compare x z = Lt.
Proof.
(* TODO *)
Admitted.

Lemma nat_proof_compare_gt_trans
  : forall (x y z: nat)
           (p: nat_compare x y = Gt)
           (q: nat_compare y z = Gt)
  , nat_compare x z = Gt.
Proof.
(* TODO *)
Admitted.

Instance comparable_nat : comparable nat :=
  { compare := nat_compare
  ; proof_compare_eq_is_equal := nat_proof_compare_eq_is_equal
  ; proof_compare_eq_reflex := nat_proof_compare_eq_reflex
  ; proof_compare_eq_trans := nat_proof_compare_eq_trans
  ; proof_compare_lt_trans := nat_proof_compare_lt_trans
  ; proof_compare_gt_trans := nat_proof_compare_gt_trans
  }.

(* test_compare_list simply tests whether nat can be used
   with a function that expects a comparable instance.
   compare_list is defined in comparable, 
   specifically for this use case.
*)
Definition test_compare_list : Prop :=
  comparable_list (1 :: 2 :: nil) (1 :: 3 :: nil) = Lt.

