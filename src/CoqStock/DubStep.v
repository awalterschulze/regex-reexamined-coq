(* TODO: Good First Issue
    Create examples that requires unfold and folding to take a step.
    This should help to document: https://stackoverflow.com/a/63210415/2482570
*)

Ltac dubstep_goal F :=
  unfold F; fold F.

Ltac dubstep_in F H :=
  unfold F in H; fold F in H.

Tactic Notation "dubstep" constr(F)  := (dubstep_goal F).
Tactic Notation "dubstep" constr(F) "in" hyp(H) := (dubstep_in F H).
