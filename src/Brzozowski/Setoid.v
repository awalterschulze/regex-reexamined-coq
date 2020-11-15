Require Import Coq.Setoids.Setoid.

Require Import CoqStock.DubStep.
Require Import CoqStock.Invs.
Require Import CoqStock.List.
Require Import CoqStock.Listerine.
Require Import CoqStock.Untie.
Require Import CoqStock.WreckIt.

Require Import Brzozowski.Alphabet.
Require Import Brzozowski.Language.
Require Import Brzozowski.Regex.

(* lang_setoid makes it possible to use:
  - rewrite for proven lang_iff theorems
  - reflexivity for lang_iff relations where both sides are equal
  see Example LangSetoidRewriteReflexivity
*)

Section LangSetoid.

Theorem lang_iff_refl : forall A:lang, A {<->} A.
  Proof.
    split; auto.
  Qed.

Theorem lang_iff_trans : forall A B C:lang, (A {<->} B) -> (B {<->} C) -> (A {<->} C).
  Proof.
    intros.
    unfold "{<->}" in *.
    intros.
    specialize H with s.
    specialize H0 with s.
    unfold "`elem`" in *.
    apply iff_trans with (A := A s) (B := B s); assumption.
  Qed.

Theorem lang_iff_sym : forall A B:lang, (A {<->} B) -> (B {<->} A).
  Proof.
    intros.
    unfold "{<->}" in *.
    intros.
    specialize H with s.
    unfold "`elem`" in *.
    apply iff_sym.
    assumption.
  Qed.

Add Parametric Relation: lang lang_iff
  reflexivity proved by lang_iff_refl
  symmetry proved by lang_iff_sym
  transitivity proved by lang_iff_trans as lang_setoid.

End LangSetoid.

Existing Instance lang_setoid.

(*
   nor_lang_morph allows rewrite to work inside nor_lang parameters
   see Example NorLangMorphSetoidRewrite
*)
Add Parametric Morphism: nor_lang
  with signature lang_iff ==> lang_iff ==> lang_iff as nor_lang_morph.
Proof.
intros.
unfold "{<->}" in *.
unfold "`elem`" in *.
intros.
specialize H with s.
specialize H0 with s.
constructor;
  intros;
  constructor;
  wreckit;
    untie;
    unfold "`elem`" in *;
    invs H1;
    wreckit.
- apply L.
  apply H.
  assumption.
- apply R.
  apply H0.
  assumption.
- apply L.
  apply H.
  assumption.
- apply R.
  apply H0.
  assumption.
Qed.

Existing Instance nor_lang_morph_Proper.

(*
   concat_lang_morph allows rewrite to work inside concat_lang parameters
*)
Add Parametric Morphism: concat_lang
  with signature lang_iff ==> lang_iff ==> lang_iff as concat_lang_morph.
Proof.
intros.
split.
- intros.
  destruct H1.
  apply (mk_concat _ _  p q s).
  + assumption.
  + apply H. assumption.
  + apply H0. assumption.
- intros.
  destruct H1.
  apply (mk_concat _ _  p q s).
  + assumption.
  + apply H. assumption.
  + apply H0. assumption.
Qed.

Lemma star_lang_morph_helper:
  forall (x y : lang) (s: str),
  (x {<->} y)
  -> (s `elem` star_lang x -> s `elem` star_lang y).
Proof.
  intros.
  induction H0.
  - constructor.
  - constructor 2 with (p := p) (q := q); try assumption.
    + apply H. assumption.
Qed.

Theorem star_lang_morph':
  forall (x y : lang) (s: str),
  (x {<->} y)
  -> (s `elem` star_lang x <-> s `elem` star_lang y).
Proof.
  intros.
  split.
  - apply star_lang_morph_helper. assumption.
  - apply star_lang_morph_helper.
    symmetry.
    assumption.
Qed.

(*
   star_lang_morph allows rewrite to work inside star_lang parameters
*)
Add Parametric Morphism: star_lang
  with signature lang_iff ==> lang_iff as star_lang_morph.
Proof.
intros R R' Riff.
unfold "{<->}" in *.
intro s.
apply star_lang_morph'.
assumption.
Qed.

(* This lemma is only here to show off the setoid rewrite example below. *)
Example lemma_for_setoid_example_concat_lang_emptyset_l_is_emptyset: forall (r: lang),
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

(*
  The implementation of Setoid for lang allows the use of rewrite and reflexivity.
*)
Example LangSetoidRewriteReflexivity: forall (r: lang),
  concat_lang emptyset_lang r
  {<->}
  emptyset_lang.
Proof.
intros.
rewrite lemma_for_setoid_example_concat_lang_emptyset_l_is_emptyset.
reflexivity.
Qed.

(*
  The implementation of not_lang_morph allows the use of rewrite inside nor_lang parameters.
*)
Example NorLangMorphSetoidRewrite: forall (r s: lang),
  nor_lang (concat_lang emptyset_lang r) s
  {<->}
  nor_lang emptyset_lang s.
Proof.
intros.
rewrite lemma_for_setoid_example_concat_lang_emptyset_l_is_emptyset.
reflexivity.
Qed.

Example StarLangNorLangMorphSetoidRewrite: forall (r s: lang),
  star_lang (nor_lang (concat_lang emptyset_lang r) s)
  {<->}
  star_lang (nor_lang emptyset_lang s).
Proof.
intros.
rewrite lemma_for_setoid_example_concat_lang_emptyset_l_is_emptyset.
reflexivity.
Qed.
