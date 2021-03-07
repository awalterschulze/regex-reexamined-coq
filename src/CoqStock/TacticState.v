(*
TacticState is a tactic helper.
It is used to avoid infinitely loops in your tactic
by marking that a hypothesis has already been visited by your tactic.
*)

Ltac add_state H :=
  let T := type of H in
    assert (T -> True) by constructor.

Ltac has_state H :=
  let T := type of H in
    match goal with
    | [ _: T -> True |- _ ] => idtac
    | _ => fail "State doesn't contain the hypothesis:" T
    end .

Ltac clear_state :=
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
  clear_state.
  Fail (has_state H).
  destruct H.
  assumption.
Qed.