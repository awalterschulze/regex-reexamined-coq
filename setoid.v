Set Implicit Arguments.

Require Export Relations.
Require Export Setoid.

Require Import comparable.
Require Import derive.
Require Import nullable.
Require Import orb_simple.
Require Import regex.

Section RegexEq.

  Context {X: Set}.
  Context {tc: comparable X}.

  Definition bool_eq (b1 b2: bool) : Prop := b1 = b2.

  Definition char_eq (a b: X) : Prop := compare a b = Eq.

  Definition regex_eq (r s: regex X): Prop :=
      forall (xs: list X), matches r xs = matches s xs.

  Lemma regex_eq_refl : reflexive (regex X) regex_eq.
  Proof.
    unfold reflexive.
    unfold regex_eq.
    reflexivity.
  Qed.

  Lemma regex_eq_sym: symmetric (regex X) regex_eq.
  Proof.
    unfold symmetric.
    unfold regex_eq.
    symmetry.
    apply H.
  Qed.

  Lemma regex_eq_trans: transitive (regex X) regex_eq.
  Proof.
    unfold transitive.
    unfold regex_eq.
    intros.
    specialize H with xs.
    specialize H0 with xs.
    eapply eq_trans.
    - exact H.
    - exact H0.
  Qed.

  Add Parametric Relation: (regex X) regex_eq
      reflexivity proved by regex_eq_refl
      symmetry proved by regex_eq_sym
      transitivity proved by regex_eq_trans as regex_setoid.

  Add Parametric Morphism: nullable
      with signature regex_eq ==> bool_eq as nullable_morph.
  Proof.
    intros.
    unfold bool_eq.
    unfold regex_eq in H.
    specialize H with nil.
    cbn in H.
    assumption.
  Qed.

  Add Parametric Morphism: (@derive X tc)
      with signature regex_eq ==> char_eq ==> regex_eq as derive_morph.
  Proof.
    intros.
    unfold char_eq in H0.
    symmetry in H0.
    compare_to_eq.
    unfold regex_eq in *.
    unfold matches in H.
    intro.
    specialize H with (cons y0 xs).
    cbn in H.
    fold (matches (derive x y0) xs) in H.
    fold (matches (derive y y0) xs) in H.
    assumption.
  Qed.

  Add Parametric Morphism: (@or X)
      with signature regex_eq ==> regex_eq ==> regex_eq as or_morph.
  Proof.
    intros.
    unfold regex_eq in *.
    intros.
    repeat rewrite or_is_logical_or.
    rewrite H.
    rewrite H0.
    reflexivity.
  Qed.

  Add Parametric Morphism: (@and X)
    with signature regex_eq ==> regex_eq ==> regex_eq as and_morph.
  Proof.
    intros.
    unfold regex_eq in *.
    intros.
    repeat rewrite and_is_logical_and.
    rewrite H.
    rewrite H0.
    reflexivity.
  Qed.

  Add Parametric Morphism: (@not X)
    with signature regex_eq ==> regex_eq as not_morph.
  Proof.
    intros.
    unfold regex_eq in *.
    intro.
    repeat rewrite not_is_logical_not.
    rewrite H.
    reflexivity.
  Qed.

  Lemma concat_morph_specialized : forall
      (xs: list X)
      (x y x0 y0: regex X)
      (H0: (regex_eq x x0))
      (H1: (regex_eq y y0)),
      (matches (concat x y) xs) = (matches (concat x0 y0) xs).
  Proof.
    intro.
    induction xs.
    - intros.
      cbn.
      rewrite (nullable_morph H0).
      rewrite (nullable_morph H1).
      reflexivity.
    - intros.
      unfold matches.
      cbn.
      simpl_matches.
      rewrite (nullable_morph H0).
      destruct (nullable x0).
      + repeat rewrite or_is_logical_or.
        Check derive_morph.
        rewrite (derive_morph H1 (proof_compare_eq_reflex a)).
        replace (matches (concat (derive x0 a) y0) xs) with (matches (concat (derive x a) y) xs).
        * reflexivity.
        * eapply IHxs.
          ** rewrite (derive_morph H0 (proof_compare_eq_reflex a)).
            reflexivity.
          ** assumption.
      + eapply IHxs.
        * rewrite (derive_morph H0 (proof_compare_eq_reflex a)).
          reflexivity.
        * assumption.
  Qed.

  Add Parametric Morphism: (@concat X)
      with signature regex_eq ==> regex_eq ==> regex_eq as concat_morph.
  Proof.
    intros.
    unfold regex_eq.
    intro.
    eapply concat_morph_specialized.
    - assumption.
    - assumption.
  Qed.

  Add Parametric Morphism: (@zero_or_more X)
      with signature regex_eq ==> regex_eq as zero_or_more_morph.
  Proof.
    Admitted.

End RegexEq.
