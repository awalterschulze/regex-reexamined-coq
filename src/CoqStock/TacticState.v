(*
TacticState is a tactic helper.
It is used to avoid infinitely loops in your tactic
by marking that a hypothesis has already been visited by your tactic.
The API features 3 tactics:
  - add_state: adds a state to the hypothesis as `mk_state (type of H) H`
  - has_state: fails if the state has not been added yet
  - clear_states: removes all states from the hypothesis
*)

Inductive state (T: Type) (x: T): Prop :=
  | mk_state: state T x.

Ltac is_hyp H :=
  let T := type of H in
  match goal with
  | [ HName: T |- _ ] => idtac
  | _ => fail
  end.

Ltac add_state E :=
  tryif is_hyp E
  then
    let T := type of E in
    pose (mk_state _ T)
  else
    pose (mk_state _ E).

Ltac has_state E :=
  tryif is_hyp E
  then
    let T := type of E in
    match goal with
    | [ S : state _ T |- _ ] => idtac
    | _ => fail "State doesn't contain hypothesis:" E
    end
  else
    match goal with
    | [ S : state _ E |- _ ] => idtac
    | _ => fail "State doesn't contain:" E
    end.

Ltac clear_states :=
repeat (
  match goal with
  | [H : state _ _ |- _] => clear H
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

Theorem example_state_api_2: 1 = 1.
Proof.
  add_state False.
  add_state 2.
  add_state (3 = 2).
  assert True by constructor.
  add_state nat.
  has_state 2.
  Fail has_state 3.
  has_state nat.
  Fail has_state Set.
  add_state Set.
  has_state Set.
  clear_states.
  Fail has_state 2.
  reflexivity.
Qed.

(* This example resulted in endless loop in previous version of wreck_one *)
Example example_one_is_one:
  forall (x: nat), x = 1 -> 1 = 1.
Proof.
intros.
inversion H as [H0].
add_state H.
(* This failed before.
   We now use Tactic Notation to detect the type of expression
   and call the appropriate add_state and has_state
*)
has_state H0.
inversion H0 as [H1].
add_state H1.
inversion s.
has_state H.
Fail has_state nat.
reflexivity.
Qed.