Set Implicit Arguments.

Require Export Relation_Definitions.
Require Export Setoid.

Require Import comparable.
Require Import derive_def.
Require Import nullable.
Require Import orb_simple.
Require Import regex.

Section RegexEq.

  Context {A: Type}.
  Context {tc: comparable A}.

  Definition bool_eq (b1 b2: bool) : Prop := b1 = b2.

  Definition char_eq (a b: A) : Prop := compare a b = Eq.

  Definition regex_eq (r s: regex A): Prop :=
      forall (xs: list A), matchesb r xs = matchesb s xs.

  Lemma regex_eq_refl : reflexive (regex A) regex_eq.
  Proof.
    unfold reflexive.
    unfold regex_eq.
    reflexivity.
  Qed.

  Lemma regex_eq_sym: symmetric (regex A) regex_eq.
  Proof.
    unfold symmetric.
    unfold regex_eq.
    symmetry.
    apply H.
  Qed.

  Lemma regex_eq_trans: transitive (regex A) regex_eq.
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

  Add Parametric Relation: (regex A) regex_eq
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

  Add Parametric Morphism: (@derive A tc)
      with signature regex_eq ==> char_eq ==> regex_eq as derive_morph.
  Proof.
    intros.
    unfold char_eq in H0.
    symmetry in H0.
    compare_to_eq.
    unfold regex_eq in *.
    unfold matchesb in H.
    intro.
    specialize H with (cons y0 xs).
    cbn in H.
    fold (matchesb (derive x y0) xs) in H.
    fold (matchesb (derive y y0) xs) in H.
    assumption.
  Qed.

  Add Parametric Morphism: or
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

  Add Parametric Morphism: and
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

  Add Parametric Morphism: not
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
      (xs: list A)
      (x y x0 y0: regex A)
      (H0: (regex_eq x x0))
      (H1: (regex_eq y y0)),
      (matchesb (concat x y) xs) = (matchesb (concat x0 y0) xs).
  Proof.
    intro.
    induction xs.
    - intros.
      cbn.
      rewrite (nullable_morph H0).
      rewrite (nullable_morph H1).
      reflexivity.
    - intros.
      unfold matchesb.
      cbn.
      simpl_matchesb.
      rewrite (nullable_morph H0).
      destruct (nullable x0).
      + repeat rewrite or_is_logical_or.
        rewrite (derive_morph H1 (proof_compare_eq_reflex a)).
        replace (matchesb (concat (derive x0 a) y0) xs) with (matchesb (concat (derive x a) y) xs).
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

  Add Parametric Morphism: concat
      with signature regex_eq ==> regex_eq ==> regex_eq as concat_morph.
  Proof.
    intros.
    unfold regex_eq.
    intro.
    eapply concat_morph_specialized.
    - assumption.
    - assumption.
  Qed.

  Add Parametric Morphism: star
      with signature regex_eq ==> regex_eq as star_morph.
  Proof.
  (* TODO: Help Wanted *)
  Admitted.

End RegexEq.

Existing Instance regex_setoid.
Existing Instance and_morph_Proper.
Existing Instance or_morph_Proper.
Existing Instance not_morph_Proper.
Existing Instance concat_morph_Proper.
Existing Instance nullable_morph_Proper.
Existing Instance derive_morph_Proper.

