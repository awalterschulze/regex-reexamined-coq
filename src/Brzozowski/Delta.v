Require Import List.
Import ListNotations.

Require Import CoqStock.Listerine.

Require Import Brzozowski.Alphabet.
Require Import Brzozowski.Regex.
Require Import Brzozowski.Sequences.

(*
    **Definition 3.2.** Given any set $R$ of sequences we define $\delta(R)$ to be

    $$
    \begin{aligned}
    \delta(R) & = \lambda\ \text{if}\ \lambda \in R \\
              & = \emptyset\ \text{if}\ \lambda \notin R \\
    \end{aligned}
    $$
*)

Inductive delta: regex -> regex -> Prop :=
    | delta_lambda (r: regex):
        [] `elem` {{r}} ->
        delta r lambda
    | delta_emptyset (r: regex):
        [] `notelem` {{r}} ->
        delta r emptyset
    .

(*
    It is clear that:

    $$
    \begin{aligned}
    \delta(a) & = \emptyset\ \text{for any}\ a \in \Sigma_k, \\
    \delta(\lambda) & = \lambda, \text{and} \\
    \delta(\emptyset) & = \emptyset . \\
    \end{aligned}
    $$
*)

Theorem delta_lambda_is_lambda: delta lambda lambda.
Proof.
apply delta_lambda.
constructor.
reflexivity.
Qed.

Theorem delta_emptyset_is_emptyset: delta emptyset emptyset.
Proof.
apply delta_emptyset.
unfold not.
intros.
inversion H.
Qed.

Theorem delta_symbol_is_emptyset: forall (a: alphabet),
    delta (symbol a) emptyset.
Proof.
intros.
apply delta_emptyset.
unfold not.
intros.
inversion H.
listerine.
Qed.

(*
    Furthermore

    $$
    \begin{aligned}
    \delta(P* ) &= \lambda\ \text{(by definition of * ), and} \\
    \delta(P.Q) &= \delta(P)\ \&\ \delta(Q).
    \end{aligned}
    $$
*)

Theorem delta_star_is_lambda: forall (r: regex),
    delta (star r) lambda.
Proof.
intros.
apply delta_lambda.
constructor.
reflexivity.
Qed.

Theorem delta_concat_is_and_lambda: forall (p q: regex),
    delta p lambda ->
    delta q lambda ->
    delta (concat p q) lambda.
Proof.
intros.
constructor.
constructor.
exists [].
exists [].
assert ([] ++ [] = (@nil alphabet)). cbn. reflexivity.
exists H1.
split.
- inversion H.
  exact H2.
- inversion H0.
  exact  H2.
Qed.

Theorem delta_concat_is_and_emptyset_r: forall (p q: regex),
    delta p emptyset ->
    delta q lambda ->
    delta (concat p q) emptyset.
Proof.
(*TODO: Good First Issue *)
Abort.

Theorem delta_concat_is_and_emptyset_l: forall (p q: regex),
    delta p lambda ->
    delta q emptyset ->
    delta (concat p q) emptyset.
Proof.
(* TODO: Good First Issue *)
Abort.

Theorem delta_concat_is_and_emptyset: forall (p q: regex),
    delta p emptyset ->
    delta q emptyset ->
    delta (concat p q) emptyset.
Proof.
(* TODO: Good First Issue *)
Abort.

(*
    If $R = f(P, Q)$ it is also easy to determine $\delta(R)$. For example,

    $$
    \begin{aligned}
    \text{(3.1)}&\ \delta(P + Q)    &= \delta(P) + \delta(Q). \\
    \text{(3.2)}&\ \delta(P\ \&\ Q) &= \delta(P)\ \&\ \delta(Q). \\
    \text{(3.3)}&\ \delta(P')       &= \lambda\ \text{if}\ \delta(P) = \emptyset \\
                &                   &= \emptyset\ \text{if}\ \delta(P) = \lambda \\
    \end{aligned}
    $$
*)

Theorem delta_or_lambda: forall (p q: regex),
    delta p lambda ->
    delta q lambda ->
    delta (or p q) lambda.
Proof.
(* TODO: Good First Issue *)
Abort.

Theorem delta_or_lambda_l: forall (p q: regex),
    delta p lambda ->
    delta q emptyset ->
    delta (or p q) lambda.
Proof.
(* TODO: Good First Issue *)
Abort.

Theorem delta_or_lambda_r: forall (p q: regex),
    delta p emptyset ->
    delta q lambda ->
    delta (or p q) lambda.
Proof.
(* TODO: Good First Issue *)
Abort.

Theorem delta_or_emptyset: forall (p q: regex),
    delta p emptyset ->
    delta q emptyset ->
    delta (or p q) emptyset.
Proof.
(* TODO: Good First Issue *)
Abort.

Theorem delta_and_lambda: forall (p q: regex),
    delta p lambda ->
    delta q lambda ->
    delta (and p q) lambda.
Proof.
(* TODO: Good First Issue *)
Abort.

Theorem delta_and_emptyset_r: forall (p q: regex),
    delta p emptyset ->
    delta q lambda ->
    delta (and p q) emptyset.
Proof.
(* TODO: Good First Issue *)
Abort.

Theorem delta_and_emptyset_l: forall (p q: regex),
    delta p lambda ->
    delta q emptyset ->
    delta (and p q) emptyset.
Proof.
(* TODO: Good First Issue *)
Abort.

Theorem delta_and_emptyset: forall (p q: regex),
    delta p emptyset ->
    delta q emptyset ->
    delta (and p q) emptyset.
Proof.
(* TODO: Good First Issue *)
Abort.

Theorem delta_not_emptyset: forall (r: regex),
    delta r lambda ->
    delta (complement r) emptyset.
Proof.
intros.
constructor.
inversion H.
unfold not.
intros.
inversion H2.
clear H2.
subst.
inversion H3.
contradiction.
Qed.

Theorem delta_not_lambda: forall (r: regex),
    delta r emptyset ->
    delta (complement r) lambda.
Proof.
intros.
constructor.
inversion H.
constructor.
constructor; assumption.
Qed.