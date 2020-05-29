Require Import Bool.

Ltac reduce_orb_step :=
  match goal with
  | [ |- context [?X || ?Y || (?Z || ?Y)]] =>
    rewrite orb_comm with Z Y
  | [ |- context [?X || ?Y || (?Y || ?Z)]] =>
    rewrite orb_assoc with (X||Y) Y Z
  | [ |- context [?X || ?Y || ?Y]] =>
    rewrite <- orb_assoc with X Y Y
  | [ |- context [?Y || ?Y]] =>
    rewrite orb_diag
  | [|- context [?X || ?Y || ?Z = ?X || ?Z || ?Y]] =>
    rewrite <- orb_assoc with X Z Y;
    rewrite orb_comm with Z Y;
    rewrite orb_assoc with X Y Z
  end.

Ltac reduce_orb := repeat (try reduce_orb_step).

Example example_reduce_orb_step: forall (a b c: bool),
  a || b || (c || b) = a || b || c.
Proof.
intros.
reduce_orb_step.
reduce_orb_step.
reduce_orb_step.
reduce_orb_step.
reflexivity.
Qed.

Example example_reduce_orb: forall (a b c: bool),
  a || b || (c || b) = a || b || c.
Proof.
intros.
reduce_orb.
reflexivity.
Qed.

(* TODO: Good First Issue
   Add more examples of using reduce_orb_step, 
   by creating theorems that are proved using reduce_orb_step
   The theorem names should start with example_
*)