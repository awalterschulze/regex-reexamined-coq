Require Import List.
Import ListNotations.

Require Import CoqStock.Invs.
Require Import CoqStock.Listerine.
Require Import CoqStock.Untie.
Require Import CoqStock.WreckIt.

Require Import Brzozowski.Alphabet.
Require Import Brzozowski.Regex.
Require Import Brzozowski.Sequences.

(*
    **Definition 3.2.**
    Given any set $R$ of sequences we define $\delta(R)$ to be

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
delta_and is only true when both regexes are true, where
true = lambda
false = emptyset
*)
Fixpoint delta_and (p q: regex): regex :=
  match (p, q) with
  | (lambda, lambda) => lambda
  | _ => emptyset
  end.

(*
delta_nor is only true when both regexes are false, where
true = lambda
false = emptyset
*)
Fixpoint delta_nor (p q: regex): regex :=
  match (p, q) with
  | (emptyset, emptyset) => lambda
  | _ => emptyset
  end.

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

(* \delta(P* ) = \lambda\ *)
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

(* \delta(P.Q) = \delta(P)\ \&\ \delta(Q) *)
Theorem delta_concat_is_and:
  forall (p q: regex)
         (dp dq: regex)
         (dc: regex)
         (delta_p: delta p dp)
         (delta_q: delta q dq),
  delta (concat p q) (delta_and dp dq).
Proof.
intros.
invs delta_p; invs delta_q; cbn; constructor; try untie.
- constructor.
  exists []. exists []. exists eq_refl.
  split; assumption.
- invs H1. wreckit. listerine. subst.
  apply H0. assumption.
- invs H1. wreckit. listerine. subst.
  apply H. assumption.
- invs H1. wreckit. listerine. subst.
  apply H. assumption.
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

  where $\&$ and $+$ is defined for $\delta$ similar to 
  $\lambda$ being True and $\emptyset$ being False in a boolean equation.

  $$
  \begin{aligned}
  A\ \&\ B = \lambda\ \text{if and only if}\ A = \lambda\ \text{and}\ B = \lambda \\
  A + B = \emptyset\ \text{if and only if}\ A = \emptyset\ \text{and}\ B = \emptyset
  \end{aligned}
  $$
*)

(*
delta_or is only true when one of the regexes are true, where
true = lambda
false = emptyset
*)
Fixpoint delta_or (p q: regex): regex :=
  match (p, q) with
  | (lambda, _) => lambda
  | (_, lambda) => lambda
  | _ => emptyset
  end.

(* \delta(P + Q) = \delta(P) + \delta(Q) *)
Theorem delta_or_is_or:
  forall
    (p q: regex)
    (dp dq: regex)
    (delta_p: delta p dp)
    (delta_q: delta q dq),
    delta (or p q) (delta_or dp dq).
Proof.
intros.
invs delta_p; invs delta_q; cbn; constructor;
  try (constructor; split); untie;
  invs H1; wreckit; try contradiction.
- apply L. constructor.
  split; assumption.
Qed.

(* \delta(P\ \&\ Q) = \delta(P)\ \&\ \delta(Q). *)
Theorem delta_and_is_and:
  forall
    (p q: regex)
    (dp dq: regex)
    (delta_p: delta p dp)
    (delta_q: delta q dq),
    delta (and p q) (delta_and dp dq).
Proof.
intros.
invs delta_p; invs delta_q; cbn; constructor;
  try (constructor; split); 
  untie;
  invs H1;
  wreckit;
  try contradiction.
- apply R. constructor. wreckit. assumption.
- apply L. constructor. wreckit. assumption.
- apply L. constructor. wreckit. assumption.
Qed.

(*
delta_not is only true if input is false and vice versa, where
true = lambda
false = emptyset
*)
Fixpoint delta_not (p: regex): regex :=
  match p with
  | lambda => emptyset
  | _ => lambda
  end.

(*
\delta(P') = \lambda\ \text{if}\ \delta(P) = \emptyset \\
\delta(P') = \emptyset\ \text{if}\ \delta(P) = \lambda
*)
Theorem delta_not_is_not:
  forall
    (p: regex)
    (dp: regex)
    (delta_p: delta p dp),
    delta (complement p) (delta_not dp).
Proof.
intros.
invs delta_p; cbn; constructor.
- untie.
  cbn in H0.
  invs H0.
  wreckit.
  apply L.
  assumption.
- cbn.
  constructor.
  wreckit.
  assumption.
Qed. 

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

Fixpoint delta_def (r: regex): regex :=
  match r with
  | emptyset => emptyset
  | lambda => lambda
  | symbol _ => emptyset
  | concat s t => delta_and (delta_def s) (delta_def t)
  | star s => lambda
  | nor s t => delta_nor (delta_def s) (delta_def t)
end.

Theorem delta_is_delta_def:
  forall (r: regex),
  delta r (delta_def r).
Proof.
intros.
induction r.
- cbn.
  apply delta_emptyset.
  untie.
- cbn.
  apply delta_lambda.
  constructor.
- cbn.
  apply delta_emptyset.
  untie.
  invs H.
- cbn.
  invs IHr1;
  invs IHr2.
  + apply delta_lambda.
    constructor.
    exists [].
    exists [].
    exists eq_refl.
    split; assumption.
  + apply delta_emptyset.
    untie.
    invs H2.
    wreckit.
    listerine.
    contradiction.
  + apply delta_emptyset.
    untie.
    invs H2.
    wreckit.
    listerine.
    contradiction.
  + apply delta_emptyset.
    untie.
    invs H2.
    wreckit.
    listerine.
    contradiction.
- cbn.
  apply delta_lambda.
  constructor.
  reflexivity.
- cbn.
  invs IHr1; invs IHr2.
  + apply delta_emptyset.
    untie.
    inversion H2.
    wreckit.
    contradiction.
  + apply delta_emptyset.
    untie.
    inversion H2.
    wreckit.
    contradiction.
  + apply delta_emptyset.
    untie.
    inversion H2.
    wreckit.
    contradiction.
  + apply delta_lambda.
    constructor.
    split; assumption.
Qed.

Theorem delta_def_implies_delta:
  forall (r s: regex),
  delta_def r = s -> delta r s.
Proof.
intros.
rewrite <- H.
apply delta_is_delta_def.
Qed.

Theorem delta_implies_delta_def:
  forall (r s: regex),
  delta r s -> delta_def r = s.
Proof.
intros.
inversion_clear H.
- induction r.
  + inversion H0.
  + cbn. reflexivity.
  + inversion H0.
  + invs H0. wreckit. listerine. subst.
    remember (IHr1 L).
    remember (IHr2 R).
    cbn.
    rewrite e.
    rewrite e0.
    reflexivity.
  + cbn. reflexivity.
  + invs H0. wreckit.
    cbn.
    remember (delta_def r1).
    remember (delta_def r2).
    induction r;
      symmetry in Heqr;
      apply delta_def_implies_delta in Heqr;
      symmetry in Heqr0;
      apply delta_def_implies_delta in Heqr0;
      inversion Heqr;
      inversion Heqr0.
    * remember (R H1).
      inversion f.
    * reflexivity.
    * remember (L H).
      inversion f.
    * remember (L H).
      inversion f.
- induction r.
  + cbn. reflexivity.
  + exfalso.
    apply H0.
    constructor.
  + cbn. reflexivity.
  + cbn.
    remember (delta_def r1) as dr1.
    remember (delta_def r2) as dr2.
    symmetry in Heqdr1.
    symmetry in Heqdr2.
    apply delta_def_implies_delta in Heqdr1.
    apply delta_def_implies_delta in Heqdr2.
    induction dr1; inversion_clear Heqdr1.
    * reflexivity.
    * induction dr2; inversion_clear Heqdr2.
      -- reflexivity.
      -- exfalso.
         apply H0.
         constructor.
         exists [].
         exists [].
         exists eq_refl.
         split; assumption.
  + exfalso.
    apply H0.
    constructor.
    reflexivity.
  + cbn.
    remember (delta_def r1) as dr1.
    remember (delta_def r2) as dr2.
    symmetry in Heqdr1.
    symmetry in Heqdr2.
    apply delta_def_implies_delta in Heqdr1.
    apply delta_def_implies_delta in Heqdr2.
    induction dr1; inversion_clear Heqdr1.
    * induction dr2; inversion_clear Heqdr2.
      -- exfalso. apply H0. constructor.
         split; assumption.
      -- reflexivity.
    * reflexivity.
Qed.
    
    