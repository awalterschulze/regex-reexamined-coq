Require Import Coq.micromega.Lia.

Require Import CoqStock.Invs.
Require Import CoqStock.List.
Require Import CoqStock.Untie.

Require Import Brzozowski.Alphabet.
Require Import Brzozowski.Decidable.
Require Import Brzozowski.Derive.
Require Import Brzozowski.DeriveCommutes.
Require Import Brzozowski.Language.
Require Import Brzozowski.LogicOp.
Require Import Brzozowski.Regex.

Require Import Coinduction.Bisimilar.
Require Import Coinduction.Setoid.

Lemma or_emptyset_is_l_helper:
  forall (r: regex),
  [] \in or_lang {{r}} emptyset_lang <-> [] \in {{r}}.
Proof.
intros.
split; intros.
- invs H.
  invs H0.
  + assumption.
  + invs H.
- auto with lang.
Qed.


(* First example from the paper *)
Theorem or_emptyset_is_l: forall (r: regex),
  bisimilar
  (or_lang {{r}} emptyset_lang)
  {{r}}.
Proof.
cofix G.
intros.
constructor.
split.
- apply or_emptyset_is_l_helper.
- intros.
  specialize G with (r := (derive_def r a)).
  rewrite <- (derive_commutes_a r a) in G.
  specialize (derive_commutes_a (or r emptyset) a) as D.
  rewrite D.
  Fail Guarded.
  cbn.
  specialize (derive_commutes_a r a) as D1.
  rewrite <- D1.
  assumption.
(* TODO: Help Wanted *)
Abort.

Theorem star_star_bisimilar: forall (r: lang),
  bisimilar
  (star_lang r)
  (star_lang (star_lang r)).
Proof.
(* TODO: Help Wanted *)
Abort.

Theorem or_lang_commutativity_bisimilar: forall (a b: lang),
  bisimilar
  (or_lang a b)
  (or_lang b a).
Proof.
(* TODO: Help Wanted *)
Abort.

Theorem concat_lang_assoc_bisimilar: forall (a b c: lang),
  bisimilar
  (concat_lang a (concat_lang b c))
  (concat_lang (concat_lang a b) c).
Proof.
(* TODO: Help Wanted *)
Abort.

Theorem concat_lang_emptyset_l_bisimilar_emptyset: forall (r: lang),
    bisimilar
    (concat_lang emptyset_lang r)
    emptyset_lang.
Proof.
(* TODO: Help Wanted *)
Abort.