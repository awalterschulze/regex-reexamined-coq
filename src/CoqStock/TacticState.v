(*
TacticState is a tactic helper.
It is used to avoid infinitely loops in your tactic
by marking that a hypothesis has already been visited by your tactic.
The API features 3 tactics:
  - add_state: adds a state to the hypothesis as `H -> True`
  - has_state: fails if the state has not been added yet
  - clear_states: removes all states from the hypothesis
*)

Ltac add_state H :=
  let T := type of H in
  let S := fresh "state_" H in
    assert (T -> True) as S by constructor.

Ltac has_state H :=
  let T := type of H in
    match goal with
    | [ _: T -> True |- _ ] => idtac
    | _ => fail "State doesn't contain the hypothesis:" T
    end .

Ltac clear_states :=
  repeat (
    match goal with
    | [H : _ -> True |- _] => clear H
    end
  ).

Example example_state_api:
  forall (P Q : Prop),
    (P /\ Q) -> P.
Proof.
  intros.
  Fail (has_state H).
  add_state H.
  has_state H.
  clear_states.
  Fail (has_state H).
  destruct H.
  assumption.
Qed.