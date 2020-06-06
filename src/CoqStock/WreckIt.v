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

(* inversion_exists:
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
Ltac inversion_exists :=
match goal with
| [ H: exists _, _ = _ |- _ ] => 
  let E := fresh "E"
  in let B := fresh "B"
  in inversion_clear H as [E B];
  try rewrite B in *
| [ H: exists _, _ |- _ ] => 
  inversion_clear H
end.

Example example_inversion_exists: forall (x: nat) (e: exists (y: nat), x = S y /\ y = O),
  x = S O.
Proof.
intros.
inversion_exists.
inversion_clear H.
subst.
reflexivity.
Qed.

Example example_inversion_exists_neq: forall (x: nat) (e: exists (y: nat), x = S y),
  x <> O.
Proof.
intros.
inversion_exists.
discriminate.
Qed.

(* inversion_conj:
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
Ltac inversion_conj :=
match goal with
| [ H: _ /\ _ |- _ ] =>
  let L := fresh "L"
  in let R := fresh "R"
  in inversion_clear H as [L R];
  try rewrite L in *;
  try rewrite R in *
end.

Example example_inversion_conj: forall (x: nat) (e: exists (y: nat), x = S y /\ y = O),
  x = S O.
Proof.
intros.
inversion_exists.
inversion_conj.
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
Ltac inversion_disj :=
match goal with
| [ H: _ \/ _ |- _ ] =>
  let B := fresh "B"
  in inversion_clear H as [B | B];
     try rewrite B in *
end.

Example example_inversion_disj: forall (x: nat) (p: x = 0 \/ x = 1),
  x < 2.
Proof.
intros.
inversion_disj; auto.
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
*)
Ltac constructor_conj :=
match goal with
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

(* wreckit_step is helpful for seeing what wreckit does step by step *)
Ltac wreckit_step :=
     inversion_exists
  || inversion_conj
  || inversion_disj
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