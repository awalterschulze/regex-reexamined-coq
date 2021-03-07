(* LEM: Law of excluded middle
   This module contains Theorems that are surprising to see
   requires LEM: `P /\ ~ P`
   or does not require LEM.
*)

Require Import CoqStock.WreckIt.

Theorem move_forall_inside_orl: forall (A: Type) (P: A -> Prop) (Q: Prop) (a : A),
  (forall x, P x) \/ Q
  -> (forall x, P x \/ Q).
Proof.
intros.
wreckit.
- specialize H with x.
  left.
  assumption.
- right.
  assumption.
Qed.

Theorem move_forall_outside_orl: forall (A: Type) (P: A -> Prop) (Q: Prop) (a : A),
  Q \/ ~ Q
  -> (
      (forall x, P x \/ Q)
      -> (forall x, P x) \/ Q
  ).
Proof.
intros.
wreckit.
- right.
  assumption.
- left.
  intros.
  specialize H0 with x.
  wreckit.
  + assumption.
  + contradiction.
Qed.
