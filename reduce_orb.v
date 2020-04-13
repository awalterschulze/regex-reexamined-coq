Require Import Bool.

Ltac reduce_orb_step :=
  match goal with
  | [ |- context [?A || ?B || (?C || ?B)]] =>
    rewrite orb_comm with C B
  | [ |- context [?A || ?B || (?B || ?C)]] =>
    rewrite orb_assoc with (A||B) B C
  | [ |- context [?A || ?B || ?B]] =>
    rewrite <- orb_assoc with A B B
  | [ |- context [?B || ?B]] =>
    rewrite orb_diag
  | [|- context [?A || ?B || ?C = ?A || ?C || ?B]] =>
    rewrite <- orb_assoc with A C B;
    rewrite orb_comm with C B;
    rewrite orb_assoc with A B C
  end.

Ltac reduce_orb := repeat (try reduce_orb_step).
