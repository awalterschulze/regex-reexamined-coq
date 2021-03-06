(*
WreckIt Ralph

████████████████████████████████
██████▓▓▓▓█████▓▓▓▓████▓▓▓▓█████
████████▓▓▓▓▓▓▓▓▓▓▓██▓▓▓▓███████
███▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓███
█████▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓█████
█▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓█
███▓▓▓▓▓▓▓▓░░░░░░░░░░▓▓▓▓▓▓▓▓███
█████▓▓▓▓▒▒██░░░░░░██▒▒▓▓▓▓█████
███▓▓▓▓▓▓▒▒▒▒██▓▓██▒▒▒▒▓▓▓▓▓▓███
█▓▓▒▒▒▒▓▓▒▒────▒▒────▒▒▓▓▒▒▒▒▓▓█
███░░▒▒▓▓░░──██░▒██──░░▓▓▒▒░░███
███░░░░▓▓░░░░▓▓▓▓▓▓░░░░▓▓░░░░███
███████░░░░░░▓▓▓▓▓▓░░░░░░███████
███████░░░░░░░░░░░░░░░░░░███████
█████░░░░██▀▀▀▀▀▀▀▀▀▀██░░░░█████
█████░░████▄▄▄▄▄▄▄▄▄▄████░░█████
█████░░██████████████████░░█████
█████░░██▒▒██▓▓▓▓▓▓██▒▒██░░█████
█████░░██▓█▀▀▀▀▀▀▀▀▀▀█▓██░░█████
█████░░████▄▄▄▄▄▄▄▄▄▄████░░█████
███████░░░░░░░░░░░░░░░░░░███████
█████████▒▒▒▒▒▒▒▒▒▒▒▒▒▒█████████
████████████████████████████████

"I'm Gonna Wreck It!"

wreckit is a tactic to break down:
  - exists in hypotheses
  - conjuction in hypotheses
  - disjunction in hypotheses
  - conjuction in the goal
*)

(* wreck_exists:
  - finds an exists in the hypotheses 
  - inverts that hypothesis
  - removes that hypothesis and 
  - substitutes all variables
  ```
  H: exists x : ?X, ?Y
  ->
  x: ?X
  H: ?Y
  ```
*)
Ltac wreck_exists :=
match goal with
| [ H: exists _, _ = _ |- _ ] => 
  let E := fresh "E"
  in let B := fresh "B"
  in destruct H as [E B];
  try rewrite B in *
| [ H: exists _, _ |- _ ] => 
  destruct H
end.

Example example_wreck_exists: forall (x: nat) (e: exists (y: nat), x = S y /\ y = O),
  x = S O.
Proof.
intros.
wreck_exists.
inversion_clear H.
subst.
reflexivity.
Qed.

Example example_wreck_exists_neq: forall (x: nat) (e: exists (y: nat), x = S y),
  x <> O.
Proof.
intros.
wreck_exists.
discriminate.
Qed.

(* wreck_conj:
  - finds a conjunction in the hypotheses
  - inverts that hypothesis
  - clears that hypothesis
  - substitutes all variables
  ```
  H: ?X /\ ?Y ->
  H0: ?X
  H1: ?Y
  ```
*)
Ltac wreck_conj :=
match goal with
| [ H: _ /\ _ |- _ ] =>
  let L := fresh "L"
  in let R := fresh "R"
  in destruct H as [L R];
  try rewrite L in *;
  try rewrite R in *
end.

Example example_wreck_conj: forall (x: nat) (e: exists (y: nat), x = S y /\ y = O),
  x = S O.
Proof.
intros.
wreck_exists.
wreck_conj.
reflexivity.
Qed.

(* inversion_disj:
  - finds a disjunction in the hypotheses
  - inverts that hypothesis
  - clears that hypothesis
  ```
  H: ?X \/ ?Y ->
     2 goals
     - H1: ?X
     - H2: ?Y
  ```
*)
Ltac wreck_disj :=
match goal with
| [ H: _ \/ _ |- _ ] =>
  let B := fresh "B"
  in destruct H as [B | B];
     try rewrite B in *
end.

Example example_wreck_disj: forall (x: nat) (p: x = 0 \/ x = 1),
  x < 2.
Proof.
intros.
wreck_disj; auto.
Qed.

Theorem conj2: forall (P: Prop),
  P -> P /\ P.
Proof.
intros.
constructor; assumption.
Qed.

(* constructor_conj
   If the goal is a conjuction,
   then deconstruct it into two goals.
   ```
   ?X /\ ?Y ->
   2 goals
   - ?X
   - ?Y
   ```
   or one goal if possible
   ```
   ?X /\ ?X -> ?X
   ```
*)
Ltac constructor_conj :=
match goal with
| [ |- ?X /\ ?X ] =>
  apply conj2
| [ |- _ /\ _ ] =>
  apply conj
end.

Example example_constructor_conj: forall (x: nat) (p: x = 0),
  x < 2 /\ x < 3.
Proof.
intros.
constructor_conj.
- rewrite p.
  auto.
- rewrite p.
  auto.
Qed.

Example example_duplicate_conj: forall (x: nat) (p: x = 0),
  x < 2 /\ x < 2.
Proof.
intros.
constructor_conj.
rewrite p.
auto.
Qed.

(* State is used to avoid infinitely loops in wreckit_invert_one. It marks that a hypothesis
 has already been inverted. *)
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
      end).

Example example_state_set_api:
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

Ltac wreckit_invert_one :=
  match goal with
    | [ H: _ |- _ ] => tryif has_state H then fail else (inversion H; [idtac]; add_state H)
  end.
(* Question: why didn't has_state H || (inversion H; [idtac]; add_state H) work? *)

Example example_invert_one:
  forall (P Q : Prop),
    (P /\ Q) -> P.
Proof.
  intros.
  wreckit_invert_one.
  assumption.
Qed.

Example example_invert_one_noop_because_two_goals:
  forall (P Q : Prop),
    (P \/ Q) -> Q \/ P.
Proof.
  intros.
  Fail wreckit_invert_one.
Abort.

Example example_invert_one_multiple_hypotheses:
  forall (P Q R : Prop),
    (P /\ Q) -> P /\ R -> P.
Proof.
  intros.
  wreckit_invert_one.
  wreckit_invert_one.
  has_state H0.
  Fail wreckit_invert_one.
  assumption.
Qed.


(* wreckit_step is helpful for seeing what wreckit does step by step *)
Ltac wreckit_step :=
     wreck_exists
  || wreck_conj
  || wreck_disj
  || constructor_conj
  || wreckit_invert_one
  .

Ltac wreckit := repeat wreckit_step ; clear_state.

Example example_wreckit: forall (x: nat) (e: exists (y: nat), x = S y /\ y = O),
  x = S O /\ S O = x.
Proof.
intros.
wreckit; reflexivity.
Qed.

Example example_wreckit_disj: forall (x: nat) (e: exists (y: nat), (x = S y \/ S y = x) /\ y = O),
  x = S O \/ S O = x.
Proof.
intros.
wreckit; auto.
Qed.

Inductive example_type_for_inversion (T: Type) :=
  | example_constructor: T -> example_type_for_inversion T.

Example example_wreckit_inversion: example_type_for_inversion (example_type_for_inversion (2 = 3)) -> False.
Proof.
  intros.
  wreckit.
  discriminate.
Qed.
