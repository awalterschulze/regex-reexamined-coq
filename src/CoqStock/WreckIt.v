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

(* destruct_exists:
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
Ltac destruct_exists :=
match goal with
| [ H: exists _, _ = _ |- _ ] => 
  let E := fresh "E"
  in let B := fresh "B"
  in destruct H as [E B];
  try rewrite B in *
| [ H: exists _, _ |- _ ] => 
  destruct H
end.

Example example_destruct_exists: forall (x: nat) (e: exists (y: nat), x = S y /\ y = O),
  x = S O.
Proof.
intros.
destruct_exists.
inversion_clear H.
subst.
reflexivity.
Qed.

Example example_destruct_exists_neq: forall (x: nat) (e: exists (y: nat), x = S y),
  x <> O.
Proof.
intros.
destruct_exists.
discriminate.
Qed.

(* destruct_conj:
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
Ltac destruct_conj :=
match goal with
| [ H: _ /\ _ |- _ ] =>
  let L := fresh "L"
  in let R := fresh "R"
  in destruct H as [L R];
  try rewrite L in *;
  try rewrite R in *
end.

Example example_destruct_conj: forall (x: nat) (e: exists (y: nat), x = S y /\ y = O),
  x = S O.
Proof.
intros.
destruct_exists.
destruct_conj.
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
Ltac destruct_disj :=
match goal with
| [ H: _ \/ _ |- _ ] =>
  let B := fresh "B"
  in destruct H as [B | B];
     try rewrite B in *
end.

Example example_destruct_disj: forall (x: nat) (p: x = 0 \/ x = 1),
  x < 2.
Proof.
intros.
destruct_disj; auto.
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

(* wreckit_step is helpful for seeing what wreckit does step by step *)
Ltac wreckit_step :=
     destruct_exists
  || destruct_conj
  || destruct_disj
  || constructor_conj
  .

Ltac wreckit := repeat wreckit_step.

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