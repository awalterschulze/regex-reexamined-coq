Require Import List.
Import ListNotations.

Require Import CoqStock.DubStep.
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
Definition derive_lang (R: lang) (s: seq) (t: seq): Prop :=
  (s ++ t) `elem` R.

(* Part of THEOREM 3.2
   For completeness, if s = \lambda, then D_[] R = R
*)
Theorem derive_lang_empty: forall (R: lang),
  derive_lang R [] {<->} R.
Proof.
intros.
unfold derive_lang.
cbn.
unfold "`elem`".
unfold "{<->}".
intros.
unfold "`elem`".
easy.
Qed.

(* **THEOREM 3.2**.
The derivative of a regular expression $R$ with respect
to a finite sequence of input characters $s = a_1, a_2, ..., a_m$
is found recursively as follows:

$$
\begin{aligned}
D_{a_1 a_2} R &= D_{a_2} (D_{a_1} R), \\
D_{a_1 a_2 a_3} R &= D_{a_3} (D_{a_1 a_2} R), \\
D_s R = D_{a_1 a_2 ... a_m} R &= D_{a_m} (D_{a_1 a_2 ... a_{m-1}} R), \\
\end{aligned}
$$

For completeness, if $s = \lambda$, then $D_{\lambda} R = R$.
The proof follows from Definition 3.1.
*)
Theorem derive_lang_is_recursive:
  forall (R: lang) (init: seq) (last: alphabet),
  derive_lang R (init ++ [last]) {<->}
  derive_lang (derive_lang R init) [last].
Proof.
intros.
split.
- unfold derive_lang.
  unfold "`elem`".
  intros.
  rewrite app_assoc.
  assumption.
- unfold derive_lang.
  unfold "`elem`".
  intros.
  rewrite app_assoc in H.
  assumption.
Qed.

Theorem derive_lang_is_recursive':
  forall (R: lang) (head: alphabet) (tail: seq),
  derive_lang R (head :: tail) {<->}
  derive_lang (derive_lang R [head]) tail.
Proof.
intros.
split.
- unfold derive_lang.
  unfold "`elem`".
  intros.
  cbn in *.
  assumption.
- unfold derive_lang.
  unfold "`elem`".
  intros.
  cbn in *.
  assumption.
Qed.

(*
D_a R = { t | a.t \in R}
*)
Definition derive_lang_a (R: lang) (a: alphabet) (t: seq): Prop :=
  (a :: t) `elem` R.

Theorem derive_lang_a_single: forall (R: lang) (a: alphabet),
  derive_lang R [a] {<->} derive_lang_a R a.
Proof.
intros.
unfold derive_lang.
unfold derive_lang_a.
unfold "{<->}".
intros.
cbn.
easy.
Qed.

Theorem derive_lang_single: forall (R: lang) (a: alphabet) (s s0: seq),
  s0 `elem` derive_lang R (a :: s) <->
  (s ++ s0) `elem` derive_lang R (a :: []).
Proof.
intros.
split;
  intros;
  unfold derive_lang in *;
  unfold "`elem`" in *;
  listerine;
  assumption.
Qed.

Theorem derive_lang_double: forall (R: lang) (a a0: alphabet) (s s0: seq),
  s0 `elem` derive_lang R (a :: a0 :: s) <->
  (s ++ s0) `elem` derive_lang R (a :: a0 :: []).
Proof.
intros.
split;
  intros;
  unfold derive_lang in *;
  unfold "`elem`" in *;
  listerine;
  assumption.
Qed.

Theorem derive_lang_step: forall (R: lang) (a: alphabet) (s: seq),
  derive_lang R (a :: s) {<->} derive_lang (derive_lang_a R a) s.
Proof.
intros.
unfold derive_lang.
unfold derive_lang_a.
unfold "{<->}".
unfold "`elem`".
intros.
listerine.
easy.
Qed.

(* Alternative inductive predicate for derive_lang *)
Inductive derive_lang_a' (R: lang) (a: alphabet) (t: seq): Prop :=
  | mk_derive_lang:
    (a :: t) `elem` R ->
    t `elem` (derive_lang_a' R a)
  .

Theorem derive_lang_a_star_a:
  forall (a: alphabet),
  derive_lang_a {{ star (symbol a) }} a
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
    unfold derive_lang.
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
  derive_lang_a emptyset_lang a
  {<->}
  emptyset_lang.
Proof.
intros.
split.
- intros.
  inversion H.
- intros.
  inversion H.
Qed.

Theorem emptyset_terminates: forall (s: seq),
  derive_lang emptyset_lang s
  {<->}
  emptyset_lang.
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

(* A helper Lemma for derive_commutes_a *)
Lemma commutes_a_emptyset: forall (a: alphabet),
  derive_lang_a {{ emptyset }} a
  {<->}
  {{ derive_def emptyset a }}.
Proof.
intros.
cbn.
apply emptyset_terminates_a.
Qed.

(* A helper Lemma for derive_commutes_a *)
Lemma commutes_a_lambda: forall (a: alphabet),
  derive_lang_a {{ lambda }} a
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

(* A helper Lemma for derive_commutes_a *)
Lemma commutes_a_symbol: forall (a b: alphabet),
  derive_lang_a {{ symbol b }} a
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

(*
  Let us consider now (3.8).
  It is sufficient to prove this relation for $f(P, Q) = P + Q$ and
  for $f(P, Q) = P'$, for this is a complete set of Boolean connectives.
  Now

  $$
  \begin{aligned}
  D_a (P + Q) &= {t | a.t \in (P + Q)}
              &= {u | a.u \in P} + {v | a.v \in P}
              &= D_a P + D_a Q.
  \end{aligned}
  $$

  It is clear that this rule can be extended to any number of regular expressions,
  i.e. that $D_a (R_1 + R_2 + \ldots) = D_a R_1 + D_a R_2 + \ldots$
  even when the number of $R_j$ is countably infinite.
  Next, note that $a.D_a R + a.D_a R' = a.I$.
  Taking the derivative with respect to $a$ of both sides,
  we have $D_a R + D_a R' = I$. Also $(D_a R) \& (D_a R') = \emptyset$,
  and we have $D_a R' = (D_a R)'$.
  Thus rule (3.8) holds for union and complementation,
  and consequently for any Boolean function.
*)

(* A helper Lemma for commutes_a_nor *)
Lemma nor_lang_distributes: forall (p q: regex) (a: alphabet),
  derive_lang_a {{nor p q}} a {<->}
  nor_lang (derive_lang_a {{p}} a) (derive_lang_a {{q}} a).
Proof.
intros.
split; intros; invs H; constructor; wreckit; untie.
Qed.

(* A helper Lemma for derive_commutes_a *)
Lemma commutes_a_nor: forall (p q: regex) (a: alphabet)
  (IHp: derive_lang_a {{p}} a {<->} {{derive_def p a}})
  (IHq: derive_lang_a {{q}} a {<->} {{derive_def q a}}),
  derive_lang_a {{ nor p q }} a
  {<->}
  {{ derive_def (nor p q) a }}.
Proof.
intros.
rewrite nor_lang_distributes.
rewrite IHp.
rewrite IHq.
dubstep derive_def.
cbn.
reflexivity.
Qed.

(* A helper Lemma for commutes_a_concat *)
Lemma concat_lang_a_impl_def: forall (r1 r2: regex) (a: alphabet),
  derive_lang_a {{r1}} a {->} {{derive_def r1 a}} ->
  derive_lang_a {{r2}} a {->} {{derive_def r2 a}} ->
  (
    derive_lang_a {{ concat r1 r2 }} a
    {->}
    {{ derive_def (concat r1 r2) a }}
  ).
Proof.
unfold "{->}".
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

(* A helper Lemma for commutes_a_concat *)
Lemma concat_emptyset_l_def_impl_lang_a:
  forall (r2: regex) (a: alphabet),
  (
    {{ derive_def (concat emptyset r2) a }}
    {->}
    derive_lang_a {{ concat emptyset r2 }} a
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

(* A helper Lemma for commutes_a_concat *)
Lemma concat_emptyset_r_def_impl_lang_a:
  forall (r1: regex) (a: alphabet),
  (
    {{ derive_def (concat r1 emptyset) a }}
    {->}
    derive_lang_a {{ concat r1 emptyset }} a
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

(*
  Next consider:
  derive_lang_a (R: lang) (a: alphabet) (t: seq): Prop :=
  (a :: t) `elem` R.
  derive_lang_a (concat_lang P Q)
  Let:
  P = delta_def(P) or P_0
  where delta_def(P_0) = emptyset
  Then:
  derive_lang_a (concat_lang P Q) a
    {<->} {s | (a :: s) `elem` (concat_lang P Q)}
    {<->} {s | (a :: s) `elem` (concat_lang (or_lang {{delta_def(P)}} P_0) Q)}
    {<->} {u | (a :: u) `elem` (concat_lang {{delta_def(P)}} Q)}
          \/
          {v | (a :: v) `elem` (concat_lang P_0 Q)}
    {<->} concat_lang {{delta_def(P)}} (derive_lang_a Q a)
          \/
          {v_1 ++ v_2 | (a :: v_1) `elem` P_0, v_2 `elem` Q}
    {<->} concat_lang {{delta_def(P)}} (derive_lang_a Q a)
          \/
          concat_lang ({v_1 | (a :: v_1) `elem` P_0}) Q
    {<->} concat_lang {{delta_def(P)}} (derive_lang_a Q a)
          \/
          concat_lang (derive_lang_a P_0 a) Q.

  But:
  derive_lang_a P a
  {<->} derive_lang_a (or_lang P_0 lambda_lang) a
  {<->} derive_lang_a P_0 a
  ; hence:
  derive_lang_a (concat_lang P Q)
  {<->} concat_lang {{delta_def(P)}} (derive_lang_a Q a)
        \/
        concat_lang (derive_lang_a P a) Q
        concat_lang ((a :: s) \in P) Q
  which is rule (3.7).
*)
Lemma commutes_a_concat: forall (a : alphabet) (p q: regex)
  (IHp: derive_lang_a {{p}} a {<->} {{derive_def p a}})
  (IHq: derive_lang_a {{q}} a {<->} {{derive_def q a}}),
  (
    derive_lang_a {{concat p q}} a
    {<->}
    {{derive_def (concat p q) a}}
  ).
Proof.
intros.
split.
- apply concat_lang_a_impl_def;
    unfold "{<->}" in *;
    unfold "{->}" in *;
    intros s0.
  + apply (IHp s0).
  + apply (IHq s0).
- (* TODO: Help Wanted *)
Admitted.

(*
  Finally we have

  $$
  \begin{aligned}
  D_a P^* &= D_a (\lambda + P + PP + PPP + \ldots) \\
          &= D_a \lambda + D_a P + D_a P ^2 + \ldots D_a P^n \ldots. \\
  \end{aligned}
  $$

  But

  $$
  \begin{aligned}
  \sum^{\infty}_{n=1} D_a P^n &= \sum^{\infty}_{n=1} ((D_a P)P^{n-1} + \delta(P) (D_a P^{n-1})) \\
                              &= \sum^{\infty}_{n=1} (D_a P)P^{n-1}, \\
  \end{aligned}
  $$

  since $\delta(P) (D_a^{n-1})$ is either $\emptyset$ or it is $D_a P^{n-1}$,
  which is already included.
  Thus we have

  $D_a P* = \sum^{\infty}_{n=1} (D_a P)P^{n-1} = (D_a P) \sum^{\infty}_{n=1}P^{n-1} = (D_a P)P*$,

  which is rule (3.6).
*)

Lemma commutes_a_star: forall (a : alphabet) (r : regex)
  (IH: derive_lang_a {{r}} a {<->} {{derive_def r a}}),
  (
    derive_lang_a {{star r}} a
    {<->}
    {{derive_def (star r) a}}
  ).
Proof.
(* TODO: Help Wanted *)
Admitted.

Theorem derive_commutes_a: forall (r: regex) (a: alphabet),
  derive_lang_a {{ r }} a
  {<->}
  {{ derive_def r a }}.
Proof.
induction r; intros.
- apply commutes_a_emptyset.
- apply commutes_a_lambda.
- apply commutes_a_symbol.
- apply commutes_a_concat.
  + apply IHr1.
  + apply IHr2.
- apply commutes_a_star.
  + apply IHr.
- apply commutes_a_nor.
  + apply IHr1.
  + apply IHr2.
Qed.

Definition derive_defs (r: regex) (s: seq) : regex :=
  fold_left derive_def s r.

(* derive_defs = fold_left derive_def s r. *)
Theorem derive_defs_step: forall (r: regex) (a: alphabet) (s: seq),
  derive_defs r (a :: s) =
  derive_defs (derive_def r a) s.
Proof.
intros.
destruct r; try (cbn; reflexivity).
Qed.

(* derive_defs = fold_left derive_def s r. *)
Theorem derive_defs_empty: forall (r: regex),
  derive_defs r [] = r.
Proof.
intros.
destruct r; (cbn; reflexivity).
Qed.

(*
TODO: Help Wanted

Prove that the derive square commutes
Regex --denote_regex-{{}}-> Set Of Sequences
   |                            |
derive_defs                  derive_lang
   |                            |
  \ /                          \ /
   .                            .
Derived Regex---{{}}------> Derived Set Of Sequences
*)

Theorem derive_lang_commutes_empty: forall (r: regex),
  derive_lang {{r}} [] {<->} {{derive_defs r []}}.
Proof.
intros.
rewrite derive_defs_empty.
unfold "{<->}".
intro s.
remember (derive_lang_empty {{r}} s) as E; destruct E.
split.
- intros.
  apply e.
  assumption.
- intros.
  apply e0.
  assumption.
Qed.

Theorem derive_lang_commutes_single:
  forall (r: regex) (a: alphabet),
    (
      forall (r': regex) (a: alphabet),
      derive_lang_a {{r'}} a {<->} {{derive_def r' a}}
    )
  ->
    derive_lang {{r}} [a] {<->} {{derive_defs r [a]}}
  .
Proof.
intros.
remember (derive_lang_commutes_empty (derive_def r a)) as H0.
clear HeqH0.
rewrite <- derive_defs_step in H0.
remember derive_lang_step as S. clear HeqS.
unfold "{<->}" in *.
intros.
specialize H with (s := s).
specialize H0 with (s := s).
destruct H0.
split; intros.
- apply H0.
  remember (S {{r}} a [] s) as S0.
  clear HeqS0.
  destruct S0.
  apply H3 in H2.
  apply H in H2.
  apply derive_lang_empty.
  exact H2.
- remember (S {{r}} a [] s) as S0.
  clear HeqS0.
  destruct S0.
  apply H4.
  apply derive_lang_empty.
  apply H.
  rewrite derive_defs_step in H2.
  rewrite derive_defs_empty in H2.
  exact H2.
Qed.

(* Part of Theorem 3.2 *)
Theorem derive_lang_commutes_star:
  forall (r: regex) (s: seq),
    (
      forall (r': regex) (a: alphabet),
      derive_lang_a {{r'}} a {<->} {{derive_def r' a}}
    )
  ->
    derive_lang {{r}} s {<->} {{derive_defs r s}}
  .
Proof.
intros.
induction s.
- apply derive_lang_commutes_empty.
- intros.
  induction s.
  + apply derive_lang_commutes_single.
    apply H.
  + clear IHs0.
    rewrite derive_defs_step.
    unfold "{<->}" in *.
    intros.
    remember (derive_lang_step {{r}} a (a0 :: s) s0) as Dr.
      clear HeqDr.
      destruct Dr as [Dr0 Dr1].
    remember (derive_lang_step {{derive_def r a}} a0 s s0) as Dr2.
      clear HeqDr2.
      destruct Dr2 as [Dr2 Dr3].
    remember (H (derive_def r a) a0 (s ++ s0)) as H2.
      clear HeqH2.
      destruct H2 as [H0 H1].
    remember (derive_lang_double {{r}} a a0 s s0) as DD.
      clear HeqDD.
      destruct DD as [DD0 DD1].
    split; intros.
    * apply DD0 in H2.
Abort.

Theorem commutes_emptyset: forall (s: seq),
  derive_lang {{ emptyset }} s
  {<->}
  {{ derive_defs emptyset s }}.
Proof.
intros.
induction s.
- cbn. apply emptyset_terminates.
- split; intros.
  + invs H.
  + unfold "{<->}" in IHs.
    cbn in H.
    fold (derive_defs emptyset s) in H.
    remember (IHs s0).
    apply i in H.
    invs H.
Qed.

Theorem commutes_lambda: forall (s: seq),
  derive_lang {{ lambda }} s
  {<->}
  {{ derive_defs lambda s }}.
Proof.
intros.
split.
- intros.
  inversion H.
  listerine.
  constructor.
- intros.
  induction s, s0.
  + constructor.
  + cbn in H.
    invs H.
  + cbn in H.
    fold (derive_defs emptyset s) in H.
    apply commutes_emptyset in H.
    invs H.
  + cbn in H.
    fold (derive_defs emptyset s) in H.
    apply commutes_emptyset in H.
    invs H.
Qed.

Theorem commutes_symbol: forall (b: alphabet) (s: seq),
  derive_lang {{ symbol b }} s
  {<->}
  {{ derive_defs (symbol b) s }}.
Proof.
intros.
split.
- intros.
  inversion H.
  listerine.
  + cbn. constructor.
  + cbn. destruct b; constructor.
- intros.
  induction s0, s.
  + invs H.
  + rewrite derive_defs_step in H.
    cbn.
    listerine.
    induction s; destruct a, b;
    (constructor
      || invs H
      || (cbn in H;
         fold (derive_defs emptyset s) in H;
         apply commutes_emptyset in H;
         invs H)).
  + cbn in H.
    invs H.
    constructor.
  + rewrite derive_defs_step in H.
    cbn.
    destruct a0, b; induction s; cbn in H; (
      invs H
      || (
        fold (derive_defs emptyset s) in H;
        apply commutes_emptyset in H;
        invs H
      )
    ).
Qed.

Theorem commutes_nor_emptyset_emptyset: forall (s: seq),
  derive_lang {{ nor emptyset emptyset }} s
  {<->}
  {{ derive_defs (nor emptyset emptyset) s }}.
Proof.
intros.
split.
- intros.
  induction s; cbn.
  + constructor. wreckit. untie.
  + apply IHs. constructor. wreckit. untie.
- intros.
  constructor. wreckit. untie.
Qed.

Theorem commutes_nor_emptyset_lambda: forall (s: seq),
  derive_lang {{ nor emptyset lambda }} s
  {<->}
  {{ derive_defs (nor emptyset lambda) s }}.
Proof.
intros.
split.
- intros.
  invs H.
  wreckit.
  clear L.
  induction s.
  + cbn.
    constructor.
    wreckit.
    * untie.
    * untie.
  + clear R.
    cbn.
    fold (derive_defs (nor emptyset emptyset) s).
    apply commutes_nor_emptyset_emptyset.
    constructor.
    wreckit.
    untie.
- intros.
  constructor.
  wreckit.
  + untie.
  + induction s.
    * invs H.
      wreckit.
      listerine.
      assumption.
    * cbn.
      untie.
      invs H0.
Qed.

Theorem derive_commutes: forall (r: regex) (s: seq),
  derive_lang {{ r }} s
  {<->}
  {{ derive_defs r s }}.
Proof.
(* TODO: Help Wanted *)
Abort.
