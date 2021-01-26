Require Import CoqStock.List.

Require Import Brzozowski.Alphabet.
Require Import Brzozowski.Null.
Require Import Brzozowski.Regex.
Require Import Brzozowski.Language.

(*
**Definition 3.1.**
Given a language $R$ of and a finite sequence $s$,
the derivative of $R$ with respect to $s$ is denoted by $D_s R$ and is
$D_s R = \{t | s.t \in R \}$.
*)
Definition derive_langs (s: str) (R: lang) (t: str): Prop :=
  (s ++ t) \in R.

(*
D_a R = { t | a.t \in R}
*)
Definition derive_lang (a: alphabet) (R: lang) (t: str): Prop :=
  (a :: t) \in R.

(* Alternative inductive predicate for derive_lang *)
Inductive derive_lang' (a: alphabet) (R: lang) (t: str): Prop :=
  | mk_derive_lang:
    (a :: t) \in R ->
    t \in (derive_lang' a R)
  .

(*
**THEOREM 3.1.** If $R$ is a regular expression,
the derivative of $R$ with respect to a character $a \in \Sigma_k$ is found
recursively as follows:

$$
\begin{aligned}
\text{(3.4)}&\ D_a a &=&\ \epsilon, \\
\text{(3.5)}&\ D_a b &=&\ \emptyset,\ \text{for}\ b = \epsilon\ \text{or}\ b = \emptyset\ \text{or}\ b \in A_k\ \text{and}\ b \neq a, \\
\text{(3.6)}&\ D_a (P^* ) &=&\ (D_a P)P^*, \\
\text{(3.7)}&\ D_a (PQ) &=&\ (D_a P)Q + \nu(P)(D_a Q). \\
\text{(3.8)}&\ D_a (f(P, Q)) &=&\ f(D_a P, D_a Q). \\
\end{aligned}
$$
*)
Fixpoint derive_def (r: regex) (a: alphabet) : regex :=
  match r with
  | emptyset => emptyset
  | emptystr => emptyset
  | symbol b =>
    if (eqa b a)
    then emptystr
    else emptyset
  | or s t => or (derive_def s a) (derive_def t a)
  | neg s => neg (derive_def s a)
  | concat s t =>
    or (concat (derive_def s a) t)
       (concat (null_def s) (derive_def t a))
  | star s => concat (derive_def s a) (star s)
  end.

Definition derive_defs (r: regex) (s: str) : regex :=
  fold_left derive_def s r.
