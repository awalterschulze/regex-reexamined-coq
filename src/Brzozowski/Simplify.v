(* Simplify contains theorems that show that
   Language definitions of regular expressions are equivalent.
*)

Require Import Coq.Lists.List.
Import Coq.Lists.List.ListNotations.

Require Import CoqStock.DubStep.
Require Import CoqStock.Invs.
Require Import CoqStock.Listerine.
Require Import CoqStock.Untie.
Require Import CoqStock.WreckIt.

Require Import Brzozowski.Alphabet.
Require Import Brzozowski.Language.
Require Import Brzozowski.Regex.

Theorem not_lang_not_lang_is_lang: forall (r: regex),
  not_lang (not_lang {{r}})
  {<->}
  {{r}}.
Proof.
intros.
split.
- assert (s `elem` {{ r }} \/ s `notelem` {{ r }}).
  admit. (* TODO: apply denotation_is_decidable *)
  intros.
  wreckit.
  + assumption.
  + invs H0.
    wreckit.
    unfold not in L.
    exfalso.
    apply L.
    constructor.
    wreckit.
    assumption.
- assert (s `elem` {{ r }} \/ s `notelem` {{ r }}).
  admit. (* TODO: apply denotation_is_decidable *)
  intros.
  constructor.
  wreckit.
  + unfold not.
    intros.
    invs H.
    wreckit.
    contradiction.
  + contradiction.
Abort.

Theorem concat_lang_emptyset_l_is_emptyset: forall (r: lang),
  concat_lang emptyset_lang r
  {<->}
  emptyset_lang.
Proof.
split.
- intros.
  invs H.
  wreckit.
  invs L.
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
  wreckit.
  invs R.
- intros.
  invs H.
Qed.

Theorem concat_lang_emptyset_r: forall (r: lang) (s: str),
  s `notelem` concat_lang r emptyset_lang.
Proof.
intros.
untie.
invs H.
wreckit.
invs R.
Qed.

Theorem concat_lang_lambda_l_is_l: forall (r: lang),
  concat_lang lambda_lang r
  {<->}
  r.
Proof.
split.
- intros.
  invs H.
  wreckit.
  subst.
  inversion_clear L.
  cbn.
  assumption.
- intros.
  constructor.
  exists [].
  exists s.
  exists eq_refl.
  split.
  + constructor.
  + assumption.
Qed.

Theorem concat_lang_lambda_r_is_r: forall (r: lang),
  concat_lang r lambda_lang
  {<->}
  r.
Proof.
split.
- intros.
  invs H.
  wreckit.
  subst.
  inversion_clear R.
  listerine.
  assumption.
- intros.
  constructor.
  exists s.
  exists [].
  assert (s ++ [] = s). listerine. reflexivity.
  exists H0.
  split.
  + assumption.
  + constructor.
Qed.