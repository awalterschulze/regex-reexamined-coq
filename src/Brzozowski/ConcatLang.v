Require Import CoqStock.DubStep.
Require Import CoqStock.Invs.
Require Import CoqStock.List.
Require Import CoqStock.Listerine.
Require Import CoqStock.Untie.
Require Import CoqStock.WreckIt.

Require Import Brzozowski.Alphabet.
Require Import Brzozowski.Language.
Require Import Brzozowski.Regex.

Inductive concat_lang_ex (P Q: lang): lang :=
  | mk_concat_ex: forall (s: str),
    (exists
      (p: str)
      (q: str)
      (pqs: p ++ q = s),
      p `elem` P /\
      q `elem` Q
    ) ->
    concat_lang_ex P Q s
  .

Theorem concat_ex_equivalent (P Q: lang):
  concat_lang_ex P Q {<->} concat_lang P Q.
Proof.
split.
- intros.
  destruct H.
  destruct H as [p [q [H [Hp Hq]]]].
  apply (mk_concat P Q p q s); assumption.
- intros.
  destruct H.
  constructor.
  exists p.
  exists q.
  exists H.
  split; assumption.
Qed.

Ltac destruct_concat :=
  apply concat_ex_equivalent;
  fold denote_regex;
  apply mk_concat_ex.

Example deconstruct_concat:
  forall (p q: regex),
  [] `elem` {{p}} /\ [] `elem` {{q}} ->
  [] `elem` {{concat p q}}.
Proof.
intros.
destruct_concat.
exists [].
exists [].
listerine.
exists eq_refl.
assumption.
Qed.