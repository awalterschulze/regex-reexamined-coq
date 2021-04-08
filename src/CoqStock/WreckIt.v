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
  - constructors in the goal that solve the goal.
  - inductive predicates that when inverted do not create more goals.
*)

Require Import CoqStock.TacticState.

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
Ltac wreck_exists H :=
  match type of H with
  | exists E, _ = _ =>
    destruct H as [E H];
    try rewrite H in *;
    try wreck_exists H
  | exists E, _ =>
    destruct H as [E H];
    try wreck_exists H
  end.

Tactic Notation "wreck_exists" "in" hyp(H) :=
  wreck_exists H.

Tactic Notation "wreck_exists" "in" "*" :=
  match goal with
  | [ H: exists _, _ = _ |- _ ] =>
    wreck_exists in H
  | [ H: exists _, _ |- _ ] =>
    wreck_exists in H
  end.

Example example_wreck_exists: forall (x: nat) (e: exists (y: nat) (z: nat), x = S y /\ y = O),
  x = S O.
Proof.
intros.
wreck_exists in e.
inversion_clear e.
subst.
reflexivity.
Qed.

Example example_wreck_exists_neq: forall (x: nat) (e: exists (y: nat), x = S y),
  x <> O.
Proof.
intros.
wreck_exists in *.
discriminate.
Qed.

(* wreck_conj:
  - finds a conjunction in the hypotheses
  - inverts that hypothesis
  - clears that hypothesis
  - substitutes all variables
  ```
  H: ?X /\ ?Y ->
  H_left: ?X
  H_right: ?Y
  ```
*)
Ltac wreck_conj H :=
  match type of H with
  | _ /\ _ =>
    let L := fresh H in
    destruct H as [L H];
    try rewrite L in *;
    try rewrite H in *;
    try wreck_conj H
  end.

Tactic Notation "wreck_conj" "in" hyp(H) :=
  wreck_conj H.

Tactic Notation "wreck_conj" "in" "*" :=
  match goal with
  | [ H: _ /\ _ |- _ ] =>
    wreck_conj in H
  end.

Example example_wreck_conj: forall (x: nat) (e: exists (y: nat), x = S y /\ y = O),
  x = S O.
Proof.
intros.
wreck_exists in *.
wreck_conj in e.
reflexivity.
Qed.

Example example_wreck_conj2: forall (P Q R :Prop),
  P /\ Q /\ R -> R.
Proof.
intros.
wreck_conj in H.
assumption.
Qed.

Ltac wreck_conj_as H I :=
  match type of H with
  | _ /\ _ =>
    destruct H as I
  end.

Tactic Notation "wreck_conj" "in" hyp(H) "as" simple_intropattern(I) :=
  wreck_conj_as H I.

Example example_wreck_conj2_as: forall (P Q R :Prop),
  P /\ Q /\ R -> R.
Proof.
intros.
wreck_conj in H as [Hone [Htwo Hthree]].
assumption.
Qed.

(* wreck_disj:
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
Ltac wreck_disj H :=
  match type of H with
  | _ \/ _ =>
    let L := fresh H
    in destruct H as [H | H];
    try rewrite H in *;
    try wreck_disj H
  end.

Tactic Notation "wreck_disj" "in" hyp(H) :=
  wreck_disj H.

Tactic Notation "wreck_disj" "in" "*" :=
  match goal with
  | [ H: _ \/ _ |- _ ] =>
    wreck_disj in H
  end.

Example example_wreck_disj: forall (x: nat) (p: x = 0 \/ x = 1),
  x < 2.
Proof.
intros.
wreck_disj in p.
- auto.
- auto.
Qed.

Example example_wreck_disj2: forall (x: nat) (p: x = 0 \/ x = 1 \/ x = 2),
  x < 3.
Proof.
intros.
wreck_disj in p.
- auto.
- auto.
- auto.
Qed.

Ltac wreck_disj_as H I :=
  match type of H with
  | _ \/ _ =>
    destruct H as I
  end.

Tactic Notation "wreck_disj" "in" hyp(H) "as" simple_intropattern(I) :=
  wreck_disj_as H I.

Example example_wreck_disj2_as: forall (x: nat) (p: x = 0 \/ x = 1 \/ x = 2),
  x < 3.
Proof.
intros.
wreck_disj in p as [p | [p | p]].
- subst. auto.
- subst. auto.
- subst. auto.
Qed.

Local Theorem conj2: forall (P: Prop),
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

(* constructor_zero
   apply constructor only if it solves the goal
*)
Ltac constructor_zero :=
  constructor; fail.

Example example_constructor_zero:
  True -> True.
Proof.
intros.
constructor_zero.
Qed.

Example example_constructor_zero_fail:
  True -> True /\ True.
Proof.
intros.
Fail constructor_zero.
Abort.

(* wreck_one
   If the goal is an inductive predicate,
   then deconstruct it only if it does not create extra goals.
   ```
   H: ?X /\ ?Y ->
   H0: ?X
   H1: ?Y
   ```
   or given the following inductive type,
   which simply boxes a type:
   ```
   Inductive box (T: Type) :=
    | mk_box: T -> box T.
   ```
   inverts the box:
   ```
   box False ->
   False
   ```
*)
Ltac wreck_one H :=
  tryif has_state H
  then
    fail
  else
    (
      (* inversion completes the proof *)
      inversion H; fail
    ) || (
      (* inversion doesn't create an extra goal *)
      let Hi := fresh H in
      inversion H as [Hi];
      add_state H;
      try wreck_one Hi
    ).
(* TODO: Help Wanted
   Question:
     We found that `tryif has_state H then fail` is necessary,
     but we would think that `has_state H ||` would have worked.
     Why is tryif necessary in this case?
*)

Tactic Notation "wreck_one" "in" hyp(H) :=
  wreck_one H.

Tactic Notation "wreck_one" "in" "*" :=
  match goal with
  | [ H: _ |- _ ] =>
    wreck_one H
  end.

Inductive example_type_for_inversion (T: Type) :=
  | example_constructor: T -> example_type_for_inversion T.

Example example_invert_one:
  example_type_for_inversion (example_type_for_inversion (2 = 3)) -> False.
Proof.
intros.
wreck_one in H.
Qed.

Example example_invert_one_conj:
  forall (P Q : Prop),
    (P /\ Q) -> P.
Proof.
  intros.
  wreck_one in H.
  assumption.
Qed.

Example example_invert_zero:
  forall (P: Prop),
    False -> P.
Proof.
  intros.
  wreck_one in H.
Qed.

Example example_invert_one_disj_fail:
  forall (P Q : Prop),
    (P \/ Q) -> Q \/ P.
Proof.
  intros.
  Fail wreck_one in H.
Abort.

Example example_invert_one_noop_because_two_goals:
  forall (P Q : Prop),
    (P \/ Q) -> Q \/ P.
Proof.
  intros.
  Fail wreck_one in H.
Abort.

Example example_invert_one_multiple_hypotheses:
  forall (P Q R : Prop),
    (P /\ Q) -> P /\ R -> P.
Proof.
  intros.
  wreck_one in *.
  wreck_one in *.
  has_state H0.
  Fail wreck_one.
  assumption.
Qed.

Ltac wreck_one_as H I :=
  inversion H as I.

Tactic Notation "wreck_one" "in" hyp(H) "as" simple_intropattern(I) :=
  wreck_one_as H I.

Example example_wreck_one_as:
  forall (P Q : Prop),
    (P /\ Q) -> P.
Proof.
  intros.
  wreck_one in H as [H1 H2].
  exact H1.
Qed.

(* wreckit_step is helpful for seeing what wreckit does step by step *)
Ltac wreckit_step :=
     wreck_exists in *
  || wreck_conj in *
  || wreck_disj in *
  || constructor_conj
  || constructor_zero
  || wreck_one in *
  .

Ltac wreckit := repeat wreckit_step ; clear_states.

Tactic Notation "wreckit" "in" hyp(H) :=
     wreck_exists in H
  || wreck_conj in H
  || wreck_disj in H
  || wreck_one in H
  .

Example example_wreckit: forall (x: nat) (e: exists (y: nat), x = S y /\ y = O),
  x = S O /\ S O = x.
Proof.
intros.
wreckit; reflexivity.
Qed.

(* This example resulted in endless loop in previous version of wreck_one *)
Example example_one_is_one:
  forall (x: nat), x = 1 -> 1 = 1.
Proof.
intros.
wreckit; auto.
Qed.

Example example_wreckit_disj: forall (x: nat) (e: exists (y: nat), (x = S y \/ S y = x) /\ y = O),
  x = S O \/ S O = x.
Proof.
intros.
wreckit; auto.
Qed.

Example example_wreckit_inversion: example_type_for_inversion (example_type_for_inversion (2 = 3)) -> False.
Proof.
  intros.
  wreckit in H.
Qed.

Tactic Notation "wreckit" "in" hyp(H) "as" simple_intropattern(I) :=
     wreck_conj in H as I
  || wreck_disj in H as I
  || wreck_one in H as I
  .

Example example_wreckit_as: example_type_for_inversion (example_type_for_inversion (2 = 3)) -> False.
Proof.
  intros.
  wreckit in H as [H1].
  wreckit in H1 as [H2].
  discriminate.
Qed.