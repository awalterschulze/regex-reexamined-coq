Require Import Coq.Setoids.Setoid.

Require Import Brzozowski.Alphabet.
Require Import Brzozowski.Derive.
Require Import Brzozowski.Language.
Require Import Brzozowski.Setoid.

Require Import Coinduction.Bisimilar.

(* bisimilar_setoid makes it possible to use:
  - rewrite for proven bisimilar theorems
  - reflexivity for bisimilar relations where both sides are equal
*)

Section BisimilarSetoid.

Theorem bisimilar_refl : forall A:lang, A <<->> A.
  Proof.
    intros.
    rewrite bisimilar_is_equivalence.
    apply Brzozowski.Setoid.lang_iff_refl.
  Qed.

Theorem bisimilar_trans : forall A B C:lang, (A <<->> B) -> (B <<->> C) -> (A <<->> C).
  Proof.
    intros.
    rewrite bisimilar_is_equivalence in *.
    apply (Brzozowski.Setoid.lang_iff_trans A B C); assumption.
  Qed.

Theorem bisimilar_sym : forall A B:lang, (A <<->> B) -> (B <<->> A).
  Proof.
    intros.
    rewrite bisimilar_is_equivalence in *.
    apply (Brzozowski.Setoid.lang_iff_sym A B); assumption.
  Qed.

Add Parametric Relation: lang bisimilar
  reflexivity proved by bisimilar_refl
  symmetry proved by bisimilar_sym
  transitivity proved by bisimilar_trans as bisimilar_setoid.

End BisimilarSetoid.

Existing Instance bisimilar_setoid.

Add Parametric Morphism : bisimilar
  with signature lang_iff ==> lang_iff ==> iff as bisimilar_lang_morphism.
Proof.
  intros ?? H ?? H'.
  apply  bisimilar_is_equivalence in H, H'.
  split; intro H0.
  now rewrite <- H, H0.
  now rewrite H, H'.
Qed.

Example example_rewriting_using_lang_iff_in_bisimilar:
  forall (P Q: lang)
  (pq: P {<->} Q),
  bisimilar Q P.
Proof.
  intros.
  rewrite pq.
  reflexivity.
Qed.

Add Parametric Morphism: or_lang
  with signature bisimilar ==> bisimilar ==> bisimilar as or_bisim_morph.
Proof.
intros.
rewrite bisimilar_is_equivalence in *.
apply or_lang_morph; assumption.
Qed.

Add Parametric Morphism: neg_lang
  with signature bisimilar ==> bisimilar as neg_bisim_morph.
Proof.
intros.
rewrite bisimilar_is_equivalence in *.
apply neg_lang_morph; assumption.
Qed.

Add Parametric Morphism: concat_lang
  with signature bisimilar ==> bisimilar ==> bisimilar as concat_bisim_morph.
Proof.
intros.
rewrite bisimilar_is_equivalence in *.
apply concat_lang_morph; assumption.
Qed.

Add Parametric Morphism: star_lang
  with signature bisimilar ==> bisimilar as star_bisim_morph.
Proof.
intros.
rewrite bisimilar_is_equivalence in *.
apply star_lang_morph; assumption.
Qed.

Add Parametric Morphism {s: str}: (elem s)
  with signature bisimilar ==> iff
  as elem_bisim_morph.
Proof.
intros.
rewrite bisimilar_is_equivalence in *.
apply elem_morph; assumption.
Qed.

Add Parametric Morphism {s: str}: (derive_langs s)
  with signature bisimilar ==> bisimilar
  as derive_langs_bisim_morph.
Proof.
intros.
rewrite bisimilar_is_equivalence in *.
apply derive_langs_morph; assumption.
Qed.

Add Parametric Morphism {a: alphabet}: (derive_lang a)
  with signature bisimilar ==> bisimilar
  as derive_lang_bism_morph.
Proof.
intros.
rewrite bisimilar_is_equivalence in *.
apply derive_lang_morph; assumption.
Qed.
