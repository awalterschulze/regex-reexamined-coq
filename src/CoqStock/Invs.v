(*
invs tactic is like inversion, but cleans up after itself and is shorter to type.
*)

Ltac invs H :=
  inversion H;
  clear H;
  subst.

Example example_invs_exists: forall (x: nat) (e: exists (y: nat), x = S y /\ y = O),
  x = S O.
Proof.
intros.
invs e.
invs H.
reflexivity.
Qed.