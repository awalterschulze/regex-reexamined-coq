Require Import OrderedType.

Lemma compare_nat_eq x y:
  Nat.compare x y = Eq ->
  x = y.
Proof.
  generalize dependent y.
  induction x, y; intros; try inversion H; auto.
Qed.

Lemma compare_nat_lt x y:
  Nat.compare x y = Lt ->
  x < y.
Proof.
  generalize dependent y.
  induction x, y; intros; try inversion H; auto with arith.
Qed.

Lemma compare_nat_gt x y:
  Nat.compare x y = Gt ->
  y < x.
Proof.
  generalize dependent y.
  induction x, y; intros; try inversion H; auto with arith.
Qed.

Definition compare_nat : forall x y : nat, Compare lt eq x y.
Proof.
  intros.
  destruct (Nat.compare x y) eqn:?.
  - apply EQ; apply compare_nat_eq; assumption.
  - apply LT; apply compare_nat_lt; assumption.
  - apply GT; apply compare_nat_gt; assumption.
Qed.

Lemma lt_not_eq x y:
  lt x y ->
  ~ eq x y.
Proof.
  generalize dependent y.
  induction x, y; intros.
  - inversion H.
  - auto with arith.
  - auto with arith.
  - auto with arith.
Qed.

Module NatOrd <: OrderedType.
  Definition t := nat.
  Definition eq := @eq nat.
  Definition lt := lt.
  Definition eq_refl := @eq_refl nat.
  Definition eq_trans := @eq_trans nat.
  Definition eq_sym := @eq_sym nat.
  Definition lt_trans := PeanoNat.Nat.lt_trans.
  Definition lt_not_eq := lt_not_eq.

  Definition compare := compare_nat.

  Definition eq_dec := PeanoNat.Nat.eq_dec.
End NatOrd.
