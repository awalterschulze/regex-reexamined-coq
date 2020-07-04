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

(* Part of THEOREM 3.2
   For completeness, if s = \lambda, then D_[] R = R
*)
Theorem derive_seqs_empty: forall (R: seqs),
  derive_seqs R [] {<->} R.
Proof.
intros.
unfold derive_seqs.
cbn.
unfold "`elem`".
unfold "{<->}".
intros.
unfold "`elem`".
easy.
Qed.

(*
D_a R = { t | a.t \in R}
*)
Definition derive_seqs_a (R: seqs) (a: alphabet) (t: seq): Prop :=
  (a :: t) `elem` R.

Theorem derive_seqs_single: forall (R: seqs) (a: alphabet),
  derive_seqs R [a] {<->} derive_seqs_a R a.
Proof.
intros.
unfold derive_seqs.
unfold derive_seqs_a.
unfold "{<->}".
intros.
cbn.
easy.
Qed.

Theorem derive_seqs_step: forall (R: seqs) (a: alphabet) (s: seq),
  derive_seqs R (a :: s) {<->} derive_seqs (derive_seqs_a R a) s.
Proof.
intros.
unfold derive_seqs.
unfold derive_seqs_a.
unfold "{<->}".
unfold "`elem`".
intros.
listerine.
easy.
Qed.

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

Theorem emptyset_terminates: forall (s: seq),
  derive_seqs emptyset_seqs s
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

Fixpoint derive_defs (r: regex) (s: seq) : regex :=
  fold_left derive_def s r.

(* derive_defs = fold_left derive_def s r. *)
Theorem derive_defs_step: forall (r: regex) (a: alphabet) (s: seq),
  derive_defs r (a :: s) =
  derive_defs (derive_def r a) s.
Proof.
intros.
destruct r; try (cbn; reflexivity).
destruct a, a0; cbn; reflexivity.
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
derive_defs                  derive_seqs
   |                            |
  \ /                          \ /
   .                            .
Derived Regex---{{}}------> Derived Set Of Sequences
*)

(* Part of Theorem 3.2 *)
Theorem derive_seqs_commutes_star:
  forall (r: regex) (a: alphabet) (s: seq),
    derive_seqs_a {{r}} a {<->} {{derive_def r a}}
  ->
    derive_seqs {{r}} s {<->} {{derive_defs r s}}
  .
Proof.
intros.
induction s.
- rewrite derive_defs_empty.
  unfold seqs_eq.
  intro s. 
  remember (derive_seqs_empty {{r}} s) as E; destruct E.
  split.
  + intros. 
    apply e.
    assumption.
  + intros.
    apply e0.
    assumption.
- intros.
  rewrite derive_defs_step.  
  unfold seqs_eq.
  intros s1.
  remember (derive_seqs_step {{r}} a0 s s1) as E.
  destruct E.
  split.
  + intros.
    apply e in H0.
    unfold derive_seqs in *.
    unfold derive_seqs_a in *.
    unfold "`elem`" in *.
    
    
    invs H0.

    remember (H (derive_def r a0) s1) as A.
    destruct A as [A1 A2].
    apply A.
    apply (H ((derive_def r a0))).
    apply H.

     


  remember (derive_seqs_empty {{r}}) as E.
  destruct E.
  remember (seqs_eq_left [] (derive_seqs_empty {{r}})).
  destruct E.
  split in s.
  rewrite derive_defs_empty.
  split; intros.
  +  apply H0 in s.
  intros.
    
    cbn. 

Theorem commutes_a_emptyset: forall (a: alphabet),
  derive_seqs_a {{ emptyset }} a
  {<->}
  {{ derive_def emptyset a }}.
Proof.
intros.
cbn.
apply emptyset_terminates_a.
Qed.

Theorem commutes_emptyset: forall (s: seq),
  derive_seqs {{ emptyset }} s
  {<->}
  {{ derive_defs emptyset s }}.
Proof.
intros.
induction s.
- cbn. apply emptyset_terminates.
- split; intros.
  + invs H.
  + unfold seqs_eq in IHs.
    cbn in H.
    fold (derive_defs emptyset s) in H.
    remember (IHs s0).
    apply i in H.
    invs H.
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

Theorem commutes_lambda: forall (s: seq),
  derive_seqs {{ lambda }} s
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

Theorem commutes_symbol: forall (b: alphabet) (s: seq),
  derive_seqs {{ symbol b }} s
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

Theorem commutes_a_nor: forall (p q: regex) (a: alphabet),
  derive_seqs_a {{ nor p q }} a
  {<->}
  {{ derive_def (nor p q) a }}.
Proof.
intros.
split.
- intros.
   

Theorem commutes_nor_emptyset_emptyset: forall (s: seq),
  derive_seqs {{ nor emptyset emptyset }} s
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
  derive_seqs {{ nor emptyset lambda }} s
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




Theorem commutes_nor_emptyset_l: forall (p q: regex) (s: seq),
  derive_seqs {{ nor emptyset q }} s
  {<->}
  {{ derive_defs (nor emptyset q) s }}.
Proof.
intros.
split.
- intros.
  induction q; induction s; cbn; cbn in H; invs H; wreckit.
  + constructor.
    wreckit.
    untie.
  + assert (s0 `elem` derive_seqs {{nor emptyset emptyset}} s).
    * constructor; wreckit; untie.
    * apply IHs in H.
      exact H.
  + destruct s0.
    * exfalso.
      apply R.
      constructor.
    * constructor.
      split; untie.
  + induction s.
    * cbn.
      constructor; wreckit; untie.
    * cbn.
      apply IHs0.
      -- intros.
          
  
  invs H.
    constructor. 

  induction s.
  + 
    
    *   
  cbn.
  fold (derive_defs (nor emptyset q) s).


Theorem commutes_nor: forall (p q: regex) (s: seq),
  derive_seqs {{ nor p q }} s
  {<->}
  {{ derive_defs (nor p q) s }}.
Proof.
intros.
split.
- intros.
  

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

Theorem derive_commutes_a: forall (r: regex) (a: alphabet),
  derive_seqs_a {{ r }} a
  {<->}
  {{ derive_def r a }}.
Proof.
(* TODO: Help Wanted *)
Abort.

Theorem derive_commutes: forall (r: regex) (s: seq),
  derive_seqs {{ r }} s
  {<->}
  {{ derive_defs r s }}.
Proof.
(* TODO: Help Wanted *)
Abort.