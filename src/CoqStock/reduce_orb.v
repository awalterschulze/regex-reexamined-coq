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

(* TODO: Good First Issue
   Add some examples of using reduce_orb_step, 
   by creating theorems that are proved using reduce_orb_step
   The theorem names should start with test_
*)