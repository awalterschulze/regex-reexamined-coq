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

Theorem concat_lang_emptyset_r: forall (r: lang) (s: str),
  s `notelem` concat_lang r emptyset_lang.
Proof.
intros.
untie.
invs H.
invs H2.
Qed.

Theorem concat_lang_lambda_l_is_l: forall (r: lang),
  concat_lang lambda_lang r
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