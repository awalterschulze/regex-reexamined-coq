Require Import CoqStock.List.

Require Import Brzozowski.Alphabet.
Require Import Brzozowski.Regex.
Require Import Brzozowski.Language.

(*
    **Definition 3.2.**
    Given any language $R$ we define $\nu(R)$ to be

    $$
    \begin{aligned}
    \nu(R) & = \epsilon\ \text{if}\ \epsilon \in R \\
              & = \emptyset\ \text{if}\ \epsilon \notin R \\
    \end{aligned}
    $$
*)

Inductive null: regex -> regex -> Prop :=
  | null_emptystr (r: regex):
    [] \in {{r}} ->
    null r emptystr
  | null_emptyset (r: regex):
    [] \notin {{r}} ->
    null r emptyset
    .

(*
null_and is only true when both regexes are true, where
true = emptystr
false = emptyset
*)
Definition null_and (p q: regex): regex :=
  match (p, q) with
  | (emptystr, emptystr) => emptystr
  | _ => emptyset
  end.

(*
null_nor is only true when both regexes are false, where
true = emptystr
false = emptyset
*)
Definition null_nor (p q: regex): regex :=
  match (p, q) with
  | (emptyset, emptyset) => emptystr
  | _ => emptyset
  end.

(*
  If $R = f(P, Q)$ it is also easy to determine $\nu(R)$. For example,

  $$
  \begin{aligned}
  \text{(3.1)}&\ \nu(P + Q)    &= \nu(P) + \nu(Q). \\
  \text{(3.2)}&\ \nu(P\ \&\ Q) &= \nu(P)\ \&\ \nu(Q). \\
  \text{(3.3)}&\ \nu(P')       &= \epsilon\ \text{if}\ \nu(P) = \emptyset \\
              &                   &= \emptyset\ \text{if}\ \nu(P) = \epsilon \\
  \end{aligned}
  $$

  where $\&$ and $+$ is defined for $\nu$ similar to
  $\epsilon$ being True and $\emptyset$ being False in a boolean equation.

  $$
  \begin{aligned}
  A\ \&\ B = \epsilon\ \text{if and only if}\ A = \epsilon\ \text{and}\ B = \epsilon \\
  A + B = \emptyset\ \text{if and only if}\ A = \emptyset\ \text{and}\ B = \emptyset
  \end{aligned}
  $$
*)

(*
null_or is only true when one of the regexes are true, where
true = emptystr
false = emptyset
*)
Definition null_or (p q: regex): regex :=
  match (p, q) with
  | (emptystr, _) => emptystr
  | (_, emptystr) => emptystr
  | _ => emptyset
  end.

(*
null_neg is only true if input is false and vice versa, where
true = emptystr
false = emptyset
*)
Definition null_neg (p: regex): regex :=
  match p with
  | emptystr => emptyset
  | _ => emptystr
  end.

Fixpoint null_def (r: regex): regex :=
  match r with
  | emptyset => emptyset
  | emptystr => emptystr
  | symbol _ => emptyset
  | or s t => null_or (null_def s) (null_def t)
  | neg s => null_neg (null_def s)
  | concat s t => null_and (null_def s) (null_def t)
  | star s => emptystr
end.