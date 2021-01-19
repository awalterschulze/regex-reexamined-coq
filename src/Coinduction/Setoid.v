Require Import Coq.Setoids.Setoid.

Require Import Brzozowski.Alphabet.
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
