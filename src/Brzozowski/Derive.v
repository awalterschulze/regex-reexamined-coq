Require Import List.
Import ListNotations.

Require Import CoqStock.Listerine.
Require Import CoqStock.Invs.
Require Import CoqStock.Untie.
Require Import CoqStock.WreckIt.

Require Import Brzozowski.Alphabet.
Require Import Brzozowski.Delta.
Require Import Brzozowski.Regex.
Require Import Brzozowski.Sequences.

(* 
**Definition 3.1.**
Given a set $R$ of sequences and a finite sequence $s$, 
the derivative of $R$ with respect to $s$ is denoted by $D_s R$ and is 
$D_s R = \{t | s.t \in R \}$.
*)
Definition derive_seqs (R: seqs) (s: seq) (t: seq): Prop :=
  (s ++ t) `elem` R.

(*
D_a R = { t | a.t \in R} 
*)
Definition derive_seqs_a (R: seqs) (a: alphabet) (t: seq): Prop :=
  (a :: t) `elem` R.

(* Alternative inductive predicate for derive_seqs *)
Inductive derive_seqs_a' (R: seqs) (a: alphabet) (t: seq): Prop :=
  | mk_derive_seqs:
    (a :: t) `elem` R ->
    t `elem` (derive_seqs_a' R a)
  .

Theorem derive_seqs_a_star_a:
  forall (a: alphabet),
  derive_seqs_a {{ star (symbol a) }} a
  {<->}
  {{ star (symbol a) }}.
Proof.
split.
- intros.
  inversion_clear H.
  + inversion H0.
  + inversion H0.
    wreckit.
    inversion L.
    listerine.
    assumption.
- intros.
  inversion_clear H.
  + apply mk_star_more.
    subst.
    constructor.
    exists [a].
    exists [].
    exists eq_refl.
    split.
    * constructor.
    * apply mk_star_zero.
      reflexivity.
  + inversion_clear H0.
    wreckit.
    subst.
    unfold derive_seqs.
    cbn.
    apply mk_star_more.
    inversion L.
    subst.
    constructor.
    exists [a].
    exists (a :: x0).
    exists eq_refl.
    split.
    -- constructor.
    -- apply mk_star_more.
       constructor.
       exists [a].
       exists x0.
       exists eq_refl.
       split.
       ++ constructor.
       ++ cbn in R.
          exact R.
Qed.

Theorem emptyset_terminates_a: forall (a: alphabet),
  derive_seqs_a emptyset_seqs a
  {<->}
  emptyset_seqs.
Proof.
intros.
split.
- intros.
  inversion H.
- intros.
  inversion H.
Qed.

(*
**THEOREM 3.1.** If $R$ is a regular expression, 
the derivative of $R$ with respect to a character $a \in \Sigma_k$ is found 
recursively as follows:

$$
\begin{aligned}
\text{(3.4)}&\ D_a a &=&\ \lambda, \\
\text{(3.5)}&\ D_a b &=&\ \emptyset,\ \text{for}\ b = \lambda\ \text{or}\ b = \emptyset\ \text{or}\ b \in A_k\ \text{and}\ b \neq a, \\
\text{(3.6)}&\ D_a (P^* ) &=&\ (D_a P)P^*, \\
\text{(3.7)}&\ D_a (PQ) &=&\ (D_a P)Q + \delta(P)(D_a Q). \\
\text{(3.8)}&\ D_a (f(P, Q)) &=&\ f(D_a P, D_a Q). \\
\end{aligned}
$$
*)
Fixpoint derive_def (r: regex) (a: alphabet) : regex :=
  match r with
  | emptyset => emptyset
  | lambda => emptyset
  | symbol b => 
    if (eqa b a)
    then lambda
    else emptyset
  | concat s t =>
    or (concat (derive_def s a) t) 
       (concat (delta_def s) (derive_def t a))
  | star s => concat (derive_def s a) (star s)
  | nor s t => nor (derive_def s a) (derive_def t a)
  end.

Theorem commutes_a_emptyset: forall (a: alphabet),
  derive_seqs_a {{ emptyset }} a
  {<->}
  {{ derive_def emptyset a }}.
Proof.
intros.
cbn.
apply emptyset_terminates_a.
Qed.

Theorem commutes_a_lambda: forall (a: alphabet),
  derive_seqs_a {{ lambda }} a
  {<->}
  {{ derive_def lambda a }}.
Proof.
intros.
split.
- intros.
  inversion H.
- intros.
  inversion H.
Qed.

Theorem commutes_a_symbol: forall (a b: alphabet),
  derive_seqs_a {{ symbol b }} a
  {<->}
  {{ derive_def (symbol b) a }}.
Proof.
intros.
split; intros.
- inversion H.
  subst.
  destruct a; cbn.
  + constructor.
  + constructor.
- destruct a, b; cbn in H.
  + invs H. constructor.
  + inversion H.
  + inversion H.
  + invs H. constructor.
Qed.

Theorem concat_seqs_a_impl_def: forall (r1 r2: regex) (a: alphabet),
  derive_seqs_a {{r1}} a {->} {{derive_def r1 a}} ->
  derive_seqs_a {{r2}} a {->} {{derive_def r2 a}} ->
  (
    derive_seqs_a {{ concat r1 r2 }} a
    {->}
    {{ derive_def (concat r1 r2) a }}
  ).
Proof.
unfold seqs_impl.
intros r1 r2 a R1 R2 s C.
invs C. 
wreckit.
cbn.
constructor.
wreckit.
untie.
invs H.
wreckit.
listerine.
- apply delta_lambda in L.
  apply delta_implies_delta_def in L.
  apply R2 in R.
  apply R0.
  constructor.
  exists [].
  exists s.
  exists eq_refl.
  split.
  + rewrite L.
    constructor.
  + assumption.
- apply R1 in L.
  apply L0.
  constructor.
  exists L1.
  exists x0.
  exists eq_refl.
  split.
  * assumption.
  * assumption.
Qed.

Theorem concat_emptyset_l_def_impl_seqs_a:
  forall (r2: regex) (a: alphabet),
  (
    {{ derive_def (concat emptyset r2) a }}
    {->}
    derive_seqs_a {{ concat emptyset r2 }} a
  ).
Proof.
unfold "{->}".
intros r2 a s C.
cbn in C.
invs C.
wreckit.
exfalso.
apply R.
constructor.
split.
- untie.
  invs H.
  wreckit.
  invs L0.
- untie.
  invs H.
  wreckit.
  invs L0.
Qed.

Theorem concat_emptyset_r_def_impl_seqs_a:
  forall (r1: regex) (a: alphabet),
  (
    {{ derive_def (concat r1 emptyset) a }}
    {->}
    derive_seqs_a {{ concat r1 emptyset }} a
  ).
Proof.
unfold "{->}".
intros r1 a s C.
cbn in C.
invs C.
wreckit.
exfalso.
apply R.
constructor.
split.
- untie.
  invs H.
  wreckit.
  invs R0.
- untie.
  invs H.
  wreckit.
  invs R0.
Qed.

Theorem derive_commutes: forall (r: regex) (a: alphabet),
  derive_seqs_a {{ r }} a
  {<->}
  {{ derive_def r a }}.
Proof.
(* TODO: Help Wanted *)
Abort.