Require Import CoqStock.DubStep.
Require Import CoqStock.Listerine.
Require Import CoqStock.Invs.
Require Import CoqStock.Untie.
Require Import CoqStock.WreckIt.
Require Import CoqStock.List.

Require Import Brzozowski.Alphabet.
Require Import Brzozowski.ConcatLang.
Require Import Brzozowski.Derive.
Require Import Brzozowski.SplitEmptyStr.
Require Import Brzozowski.Null.
Require Import Brzozowski.LogicOp.
Require Import Brzozowski.Regex.
Require Import Brzozowski.Setoid.
Require Import Brzozowski.Simplify.
Require Import Brzozowski.Language.


(* Part of THEOREM 3.2
   For completeness, if s = \epsilon, then D_[] R = R
*)
Theorem derive_langs_empty: forall (R: lang),
  derive_langs [] R {<->} R.
Proof.
intros.
unfold derive_langs.
cbn.
unfold "\in".
unfold "{<->}".
intros.
unfold "\in".
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

For completeness, if $s = \epsilon$, then $D_{\epsilon} R = R$.
The proof follows from Definition 3.1.
*)
Theorem derive_langs_is_recursive:
  forall (R: lang) (init: str) (last: alphabet),
  derive_langs (init ++ [last]) R {<->}
  derive_langs [last] (derive_langs init R).
Proof.
intros.
split.
- unfold derive_langs.
  unfold "\in".
  intros.
  rewrite app_assoc.
  assumption.
- unfold derive_langs.
  unfold "\in".
  intros.
  rewrite app_assoc in H.
  assumption.
Qed.

Theorem derive_langs_is_recursive':
  forall (R: lang) (head: alphabet) (tail: str),
  derive_langs (head :: tail) R {<->}
  derive_langs tail (derive_langs [head] R).
Proof.
intros.
split.
- unfold derive_langs.
  unfold "\in".
  intros.
  cbn in *.
  assumption.
- unfold derive_langs.
  unfold "\in".
  intros.
  cbn in *.
  assumption.
Qed.

Theorem derive_langs_a_single: forall (R: lang) (a: alphabet),
  derive_langs [a] R {<->} derive_lang a R.
Proof.
intros.
unfold derive_langs.
unfold derive_lang.
unfold "{<->}".
intros.
cbn.
easy.
Qed.

Theorem derive_langs_single: forall (R: lang) (a: alphabet) (s s0: str),
  s0 \in derive_langs (a :: s) R <->
  (s ++ s0) \in derive_langs (a :: []) R.
Proof.
intros.
split;
  intros;
  unfold derive_langs in *;
  unfold "\in" in *;
  listerine;
  assumption.
Qed.

Theorem derive_langs_double: forall (R: lang) (a a0: alphabet) (s s0: str),
  s0 \in derive_langs (a :: a0 :: s) R <->
  (s ++ s0) \in derive_langs (a :: a0 :: []) R.
Proof.
intros.
split;
  intros;
  unfold derive_langs in *;
  unfold "\in" in *;
  listerine;
  assumption.
Qed.

Theorem derive_langs_step: forall (R: lang) (a: alphabet) (s: str),
  derive_langs (a :: s) R {<->} derive_langs s (derive_lang a R).
Proof.
intros.
unfold derive_langs.
unfold derive_lang.
unfold "{<->}".
unfold "\in".
intros.
listerine.
easy.
Qed.

Theorem derive_lang_star_a:
  forall (a: alphabet),
  derive_lang a {{ star (symbol a) }}
  {<->}
  {{ star (symbol a) }}.
Proof.
split.
- intros.
  inversion_clear H.
  + cbn in *.
    inversion H2.
    subst. listerine. exact H3.
- intros.
  inversion_clear H.
  + apply mk_star_more with (p := [a]) (q := []).
    now listerine.
    listerine.
    constructor.
    constructor.
  + inversion H2.
    subst.
    unfold derive_langs.
    cbn.
    apply mk_star_more with (p := [a]) (q := (a :: q)).
    now listerine.
    listerine.
    constructor.
    apply mk_star_more with (p := [a]) (q := q).
    now listerine.
    listerine.
    constructor.
    assumption.
Qed.

Theorem emptyset_terminates_a: forall (a: alphabet),
  derive_lang a emptyset_lang
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

Theorem emptyset_terminates: forall (s: str),
  derive_langs s emptyset_lang
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

(* A helper Lemma for derive_commutes_a *)
Lemma commutes_a_emptyset: forall (a: alphabet),
  derive_lang a {{ emptyset }}
  {<->}
  {{ derive_def emptyset a }}.
Proof.
intros.
cbn.
apply emptyset_terminates_a.
Qed.

(* A helper Lemma for derive_commutes_a *)
Lemma commutes_a_emptystr: forall (a: alphabet),
  derive_lang a {{ emptystr }}
  {<->}
  {{ derive_def emptystr a }}.
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
  derive_lang a {{ symbol b }}
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

(* A helper Lemma for commutes_a_or *)
Lemma or_lang_distributes: forall (p q: regex) (a: alphabet),
  derive_lang a {{or p q}} {<->}
  or_lang (derive_lang a {{p}}) (derive_lang a {{q}}).
Proof.
intros.
split; intros; invs H; constructor; unfold derive_lang in *; unfold "\in" in *; auto.
Qed.

(* A helper Lemma for derive_commutes_a *)
Lemma commutes_a_or: forall (p q: regex) (a: alphabet)
  (IHp: derive_lang a {{p}} {<->} {{derive_def p a}})
  (IHq: derive_lang a {{q}} {<->} {{derive_def q a}}),
  derive_lang a {{ or p q }}
  {<->}
  {{ derive_def (or p q) a }}.
Proof.
intros.
rewrite or_lang_distributes.
rewrite IHp.
rewrite IHq.
dubstep derive_def.
cbn.
reflexivity.
Qed.

(* A helper Lemma for commutes_a_concat *)
Lemma concat_lang_a_impl_def: forall (r1 r2: regex) (a: alphabet),
  derive_lang a {{r1}} {->} {{derive_def r1 a}} ->
  derive_lang a {{r2}} {->} {{derive_def r2 a}} ->
  (
    derive_lang a {{ concat r1 r2 }}
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
listerine.
- apply null_emptystr in H0.
  apply null_implies_null_def in H0.
  apply R2 in H1.
  rewrite H0.
  right.
  destruct_concat_lang.
  exists [].
  exists s.
  exists eq_refl.
  split.
  + constructor.
  + assumption.
- apply R1 in H0.
  left.
  destruct_concat_lang.
  exists L.
  exists q.
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
    derive_lang a {{ concat emptyset r2 }}
  ).
Proof.
unfold "{->}".
intros r2 a s C.
cbn in C.
invs C.
wreckit.
- invs B.
  invs H0.
- invs B.
  invs H0.
Qed.

(* A helper Lemma for commutes_a_concat *)
Lemma concat_emptyset_r_def_impl_lang_a:
  forall (r1: regex) (a: alphabet),
  (
    {{ derive_def (concat r1 emptyset) a }}
    {->}
    derive_lang a {{ concat r1 emptyset }}
  ).
Proof.
unfold "{->}".
intros r1 a s C.
cbn in C.
invs C.
destruct H.
- invs H.
  invs H2.
- invs H.
  invs H2.
Qed.

Lemma commutes_a_concat_step_1:
  forall (p q: regex) (e p': regex)
    (np: null p e)
    (np': null p' emptyset)
    (splitp: {{p}} {<->} {{or e p'}}),
    (concat_lang {{p}} {{q}})
    {<->}
    (concat_lang (or_lang {{e}} {{p'}}) {{q}}).
Proof.
intros.
rewrite splitp.
reflexivity.
Qed.

(*
  Next consider:
  derive_lang (a: alphabet) (R: lang) (t: str): Prop :=
  (a :: t) \in R.
  derive_lang _ (concat_lang P Q)
  Let:
  P = null_def(P) or P_0
  where null_def(P_0) = emptyset
  Then:
  derive_lang a (concat_lang P Q)
    {<->} {s | (a :: s) \in (concat_lang P Q)}
    {<->} {s | (a :: s) \in (concat_lang (or_lang {{null_def(P)}} P_0) Q)}
    {<->} {u | (a :: u) \in (concat_lang {{null_def(P)}} Q)}
          \/
          {v | (a :: v) \in (concat_lang P_0 Q)}
    {<->} concat_lang {{null_def(P)}} (derive_langs a Q)
          \/
          {v_1 ++ v_2 | (a :: v_1) \in P_0, v_2 \in Q}
    {<->} concat_lang {{null_def(P)}} (derive_langs a Q)
          \/
          concat_lang ({v_1 | (a :: v_1) \in P_0}) Q
    {<->} concat_lang {{null_def(P)}} (derive_langs a Q)
          \/
          concat_lang (derive_lang a P_0) Q.

  But:
  derive_lang a P
  {<->} derive_lang a (or_lang P_0 emptystr_lang)
  {<->} derive_lang a P_0
  ; hence:
  derive_lang _ (concat_lang P Q)
  {<->} concat_lang {{null_def(P)}} (derive_lang a Q)
        \/
        concat_lang (derive_lang a P) Q
        concat_lang ((a :: s) \in P) Q
  which is rule (3.7).
*)
Lemma commutes_a_concat: forall (a : alphabet) (p q: regex)
  (IHp: derive_lang a {{p}} {<->} {{derive_def p a}})
  (IHq: derive_lang a {{q}} {<->} {{derive_def q a}}),
  (
    derive_lang a {{concat p q}}
    {<->}
    {{derive_def (concat p q) a}}
  ).
Proof.
unfold derive_lang.
intros a p q dp dq.
cbn.
specialize null_split_emptystr_or with (r := p) as Np.
destruct Np as [e [p' [np [np' splitp]]]].
set (commutes_a_concat_step_1 p q e p' np np' splitp) as step1.
unfold "{<->}".
unfold "\in".
intros s.
fold ((a :: s) \in (concat_lang {{p}} {{q}})).
rewrite step1.
(* specialize lift_or_lang_over_concat_lang_l {{e}} {{q0}} {{q}}. *)

(* specialize null_split_emptystr_or with (r := p) as splitp.
destruct splitp as []
rewrite lift_or_lang_over_concat_lang_l. *)


(* TODO: Help Wanted *)
Abort.

(*
  Finally we have

  $$
  \begin{aligned}
  D_a P^* &= D_a (\epsilon + P + PP + PPP + \ldots) \\
          &= D_a \epsilon + D_a P + D_a P ^2 + \ldots D_a P^n \ldots. \\
  \end{aligned}
  $$

  But

  $$
  \begin{aligned}
  \sum^{\infty}_{n=1} D_a P^n &= \sum^{\infty}_{n=1} ((D_a P)P^{n-1} + \nu(P) (D_a P^{n-1})) \\
                              &= \sum^{\infty}_{n=1} (D_a P)P^{n-1}, \\
  \end{aligned}
  $$

  since $\nu(P) (D_a^{n-1})$ is either $\emptyset$ or it is $D_a P^{n-1}$,
  which is already included.
  Thus we have

  $D_a P* = \sum^{\infty}_{n=1} (D_a P)P^{n-1} = (D_a P) \sum^{\infty}_{n=1}P^{n-1} = (D_a P)P*$,

  which is rule (3.6).
*)
Lemma commutes_a_star: forall (a : alphabet) (r : regex)
  (IH: derive_lang a {{r}} {<->} {{derive_def r a}}),
  (
    derive_lang a {{star r}}
    {<->}
    {{derive_def (star r) a}}
  ).
Proof.
(* TODO: Help Wanted *)
Abort.

Theorem derive_commutes_a: forall (r: regex) (a: alphabet),
  derive_lang a {{ r }}
  {<->}
  {{ derive_def r a }}.
Proof.
induction r; intros.
- apply commutes_a_emptyset.
- apply commutes_a_emptystr.
- apply commutes_a_symbol.
- apply commutes_a_or.
  + apply IHr1.
  + apply IHr2.
(* - apply commutes_a_neg.
  + apply IHr. *)
- (*TODO Help Wanted
    Proof theorem commutes_a_concat and then apply it.
  apply commutes_a_concat.
  + apply IHr1.
  + apply IHr2.
*) admit.
- (*TODO Help Wanted
Proof theorem commutes_a_concat and then apply it.
  apply commutes_a_star.
  + apply IHr.
*) admit.

Abort.



(* derive_defs = fold_left derive_def s r. *)
Theorem derive_defs_step: forall (r: regex) (a: alphabet) (s: str),
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
Regex --denote_regex-{{}}-> Language
   |                            |
derive_defs                  derive_langs
   |                            |
  \ /                          \ /
   .                            .
Derived Regex---{{}}------> Derived Language
*)

Theorem derive_langs_commutes_empty: forall (r: regex),
  derive_langs [] {{r}} {<->} {{derive_defs r []}}.
Proof.
intros.
rewrite derive_defs_empty.
unfold "{<->}".
intro s.
remember (derive_langs_empty {{r}} s) as E; destruct E.
split.
- intros.
  apply e.
  assumption.
- intros.
  apply e0.
  assumption.
Qed.

Theorem derive_langs_commutes_single:
  forall (r: regex) (a: alphabet),
    (
      forall (r': regex) (a: alphabet),
      derive_lang a {{r'}} {<->} {{derive_def r' a}}
    )
  ->
    derive_langs [a] {{r}} {<->} {{derive_defs r [a]}}
  .
Proof.
intros.
remember (derive_langs_commutes_empty (derive_def r a)) as H0.
clear HeqH0.
rewrite <- derive_defs_step in H0.
remember derive_langs_step as S. clear HeqS.
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
  apply derive_langs_empty.
  exact H2.
- remember (S {{r}} a [] s) as S0.
  clear HeqS0.
  destruct S0.
  apply H4.
  apply derive_langs_empty.
  apply H.
  rewrite derive_defs_step in H2.
  rewrite derive_defs_empty in H2.
  exact H2.
Qed.

(* Part of Theorem 3.2 *)
Theorem derive_langs_commutes_star:
  forall (r: regex) (s: str),
    (
      forall (r': regex) (a: alphabet),
      derive_lang a {{r'}} {<->} {{derive_def r' a}}
    )
  ->
    derive_langs s {{r}} {<->} {{derive_defs r s}}
  .
Proof.
intros.
induction s.
- apply derive_langs_commutes_empty.
- intros.
  induction s.
  + apply derive_langs_commutes_single.
    apply H.
  + clear IHs0.
    rewrite derive_defs_step.
    unfold "{<->}" in *.
    intros.
    remember (derive_langs_step {{r}} a (a0 :: s) s0) as Dr.
      clear HeqDr.
      destruct Dr as [Dr0 Dr1].
    remember (derive_langs_step {{derive_def r a}} a0 s s0) as Dr2.
      clear HeqDr2.
      destruct Dr2 as [Dr2 Dr3].
    remember (H (derive_def r a) a0 (s ++ s0)) as H2.
      clear HeqH2.
      destruct H2 as [H0 H1].
    remember (derive_langs_double {{r}} a a0 s s0) as DD.
      clear HeqDD.
      destruct DD as [DD0 DD1].
    split; intros.
    * apply DD0 in H2.
Abort.

Theorem commutes_emptyset: forall (s: str),
  derive_langs s {{ emptyset }}
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

Theorem commutes_emptystr: forall (s: str),
  derive_langs s {{ emptystr }}
  {<->}
  {{ derive_defs emptystr s }}.
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

Theorem commutes_symbol: forall (b: alphabet) (s: str),
  derive_langs s {{ symbol b }}
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

Theorem derive_commutes: forall (r: regex) (s: str),
  derive_langs s {{ r }}
  {<->}
  {{ derive_defs r s }}.
Proof.
(* TODO: Help Wanted
   Finish proving derive_commutes_a
   and apply the following proof script:
set derive_commutes_a as commutes.
intros.
generalize dependent r.
induction s.
- unfold derive_langs.
  cbn.
  intros.
  reflexivity.
- cbn.
  intros.
  fold (derive_defs (derive_def r a) s).
  specialize IHs with (r := (derive_def r a)).
  rewrite <- IHs.
  specialize commutes with (r := r) (a := a).
  unfold lang_iff in *.
  intros.
  unfold derive_langs in *.
  unfold elem.
  specialize commutes with (s ++ s0).
  rewrite commutes.
  reflexivity.
*)
Abort.
