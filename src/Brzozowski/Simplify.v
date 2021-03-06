(* Simplify contains theorems that show that
   Language definitions of regular expressions are equivalent.
*)

Require Import CoqStock.DubStep.
Require Import CoqStock.Invs.
Require Import CoqStock.List.
Require Import CoqStock.Listerine.
Require Import CoqStock.Untie.
Require Import CoqStock.WreckIt.

Require Import Brzozowski.Alphabet.
Require Import Brzozowski.ConcatLang.
Require Import Brzozowski.Decidable.
Require Import Brzozowski.Language.
Require Import Brzozowski.LogicOp.
Require Import Brzozowski.Regex.

(*
TODO: Good First Issue
Create a theorem for and prove a simplification rule below:

## Simplification rules mentioned in the Brzozowski paper.

R + R = R
P + Q = Q + P
(P + Q) + R = P + (Q + R)

R + ∅ = R
∅ + R = R
concat_lang_emptyset_r_is_emptyset: R,∅ = ∅
concat_lang_emptyset_l_is_emptyset: ∅,R = ∅
concat_lang_emptystr_r_is_r: R,λ = R
concat_lang_emptystr_l_is_l: λ,R = R

~∅+X = ~∅
~∅&X = X

~(P+Q) = ~P&~Q
~(P&Q) = ~P+~Q

Q&~λ = Q where nullable(Q) = false

## Extra simplification from the Scott Owen's regular expression re-examined paper

r&r = r
r&s = s&r
(r&s)&t = r&(s&t)
∅&r = ∅

(r,s),t = r,(s,t)

r** = r*
λ* = λ
∅* = λ
neg_lang_neg_lang_is_lang: ~~r = r
*)

Theorem neg_lang_neg_lang_is_lang: forall (r: regex),
  neg_lang (neg_lang {{r}})
  {<->}
  {{r}}.
Proof.
unfold lang_iff.
intros.
specialize denotation_is_decidable with (s := s) (r := r) as D.
destruct D.
- split.
  + auto.
  + intros.
    constructor.
    untie.
    invs H1.
    contradiction.
- split.
  + intros.
    invs H0.
    exfalso.
    apply H1.
    constructor.
    assumption.
  + intros.
    contradiction.
Qed.

Theorem concat_lang_emptyset_l_is_emptyset: forall (r: lang),
  concat_lang emptyset_lang r
  {<->}
  emptyset_lang.
Proof.
split.
- intros.
  invs H.
  invs H1.
- intros.
  invs H.
Qed.

Theorem concat_lang_emptyset_r_is_emptyset: forall (r: lang),
  concat_lang r emptyset_lang
  {<->}
  emptyset_lang.
Proof.
split.
- intros.
  invs H.
  invs H2.
- intros.
  invs H.
Qed.

Theorem concat_lang_emptystr_l_is_l: forall (r: lang),
  concat_lang emptystr_lang r
  {<->}
  r.
Proof.
split.
- intros.
  invs H.
  inversion_clear H1.
  cbn.
  assumption.
- intros.
  destruct_concat_lang.
  exists [].
  exists s.
  exists eq_refl.
  split.
  + constructor.
  + assumption.
Qed.

Theorem concat_lang_emptystr_r_is_r: forall (r: lang),
  concat_lang r emptystr_lang
  {<->}
  r.
Proof.
split.
- intros.
  invs H.
  wreckit.
  subst.
  inversion_clear H2.
  listerine.
  assumption.
- intros.
  destruct_concat_lang.
  exists s.
  exists [].
  assert (s ++ [] = s). listerine. reflexivity.
  exists H0.
  split.
  + assumption.
  + constructor.
Qed.

Theorem lift_or_lang_over_concat_lang_r: forall (p q r: lang),
  (concat_lang p (or_lang q r))
  {<->}
  or_lang (concat_lang p q) (concat_lang p r).
Proof.
split; intros.
- constructor.
  invs H.
  invs H2.
  destruct H.
  + left.
    destruct_concat_lang.
    exists p0.
    exists q0.
    exists eq_refl.
    auto.
  + right.
    destruct_concat_lang.
    exists p0.
    exists q0.
    exists eq_refl.
    auto.
- invs H.
  invs H0.
  + destruct_concat_lang.
    invs H.
    exists p0.
    exists q0.
    exists eq_refl.
    split.
    * assumption.
    * constructor.
      left.
      assumption.
  + destruct_concat_lang.
    invs H.
    exists p0.
    exists q0.
    exists eq_refl.
    split.
    * assumption.
    * constructor.
      right.
      assumption.
Qed.

Theorem lift_or_lang_over_concat_lang_l: forall (p q r: lang),
  (concat_lang (or_lang p q) r)
  {<->}
  or_lang (concat_lang p r) (concat_lang q r).
Proof.
split; intros.
- constructor.
  invs H.
  invs H1.
  destruct H.
  + left.
    destruct_concat_lang.
    exists p0.
    exists q0.
    exists eq_refl.
    auto.
  + right.
    destruct_concat_lang.
    exists p0.
    exists q0.
    exists eq_refl.
    auto.
- invs H.
  invs H0.
  + destruct_concat_lang.
    invs H.
    exists p0.
    exists q0.
    exists eq_refl.
    split.
    * constructor.
      left.
      assumption.
    * assumption.
  + destruct_concat_lang.
    invs H.
    exists p0.
    exists q0.
    exists eq_refl.
    split.
    * constructor.
      right.
      assumption.
    * assumption.
Qed.

Theorem or_lang_emptyset_r_is_l: forall (r: lang),
  or_lang r emptyset_lang
  {<->}
  r.
Proof.
intros.
split.
- intros.
  invs H.
  destruct H0.
  + assumption.
  + invs H.
- intros.
  constructor.
  left.
  assumption.
Qed.

Theorem or_lang_emptyset_l_is_r: forall (r: lang),
  or_lang emptyset_lang r
  {<->}
  r.
Proof.
intros.
split.
- intros.
  invs H.
  destruct H0.
  + invs H.
  + assumption.
- intros.
  constructor.
  right.
  assumption.
Qed.

Theorem or_lang_idemp: forall (R: lang),
  or_lang R R {<->} R.
Proof.
intros.
split; intros.
- invs H. invs H0; assumption.
- constructor. left. assumption.
Qed.

Theorem or_lang_comm: forall (P Q: lang),
  or_lang P Q {<->} or_lang Q P.
Proof.
intros.
split; intros; invs H; constructor; destruct H0; auto.
Qed.