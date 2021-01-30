Require Import Coq.Setoids.Setoid.

Require Import CoqStock.DubStep.
Require Import CoqStock.Invs.
Require Import CoqStock.List.
Require Import CoqStock.Listerine.
Require Import CoqStock.Untie.
Require Import CoqStock.WreckIt.

Require Import Brzozowski.Alphabet.
Require Import Brzozowski.Derive.
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
    unfold "\in" in *.
    apply iff_trans with (A := A s) (B := B s); assumption.
  Qed.

Theorem lang_iff_sym : forall A B:lang, (A {<->} B) -> (B {<->} A).
  Proof.
    intros.
    unfold "{<->}" in *.
    intros.
    specialize H with s.
    unfold "\in" in *.
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
Add Parametric Morphism: or_lang
  with signature lang_iff ==> lang_iff ==> lang_iff as or_lang_morph.
Proof.
intros.
unfold "{<->}" in *.
unfold "\in" in *.
intros.
specialize H with s.
specialize H0 with s.
constructor.
- intros.
  constructor.
  invs H1.
  rewrite <- H.
  rewrite <- H0.
  assumption.
- intros.
  constructor.
  invs H1.
  rewrite H.
  rewrite H0.
  assumption.
Qed.

Add Parametric Morphism: neg_lang
  with signature lang_iff ==> lang_iff as neg_lang_morph.
Proof.
intros.
unfold "{<->}" in *.
intros.
specialize H with s.
split.
- intros.
  constructor.
  invs H0.
  rewrite <- H.
  assumption.
- intros.
  constructor.
  invs H0.
  rewrite H.
  assumption.
Qed.

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
  -> (s \in star_lang x -> s \in star_lang y).
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
  -> (s \in star_lang x <-> s \in star_lang y).
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
  The implementation of or_lang_morph allows the use of rewrite inside or_lang parameters.
*)
Example OrLangMorphSetoidRewrite: forall (r s: lang),
  or_lang (concat_lang emptyset_lang r) s
  {<->}
  or_lang emptyset_lang s.
Proof.
intros.
rewrite lemma_for_setoid_example_concat_lang_emptyset_l_is_emptyset.
reflexivity.
Qed.

Example StarLangOrLangMorphSetoidRewrite: forall (r s: lang),
  star_lang (or_lang (concat_lang emptyset_lang r) s)
  {<->}
  star_lang (or_lang emptyset_lang s).
Proof.
intros.
rewrite lemma_for_setoid_example_concat_lang_emptyset_l_is_emptyset.
reflexivity.
Qed.

(* Allow \in expressions to also be rewritten using lang_iff expressions: *)

Add Parametric Morphism {s: str}: (elem s)
  with signature lang_iff ==> iff
  as elem_morph.
Proof.
intros.
unfold elem.
unfold "{<->}" in H.
specialize H with (s := s).
unfold "\in" in H.
assumption.
Qed.

Example example_rewriting_using_lang_iff_in_iff:
  forall (p q: regex)
  (pq: {{p}} {<->} {{q}}),
  forall s: str,
  s \in {{q}} <-> s \in {{p}}.
Proof.
intros.
rewrite pq.
reflexivity.
Qed.

Example example_rewriting_using_lang_iff_in_iff':
  forall (P Q: lang)
  (pq: P {<->} Q),
  forall s: str,
  s \in Q <-> s \in P.
Proof.
intros.
rewrite pq.
reflexivity.
Qed.

Example example_rewriting_using_lang_iff_in_iff'':
  forall (P Q: lang)
  (pq: P {<->} Q),
  forall s: str,
  s \in neg_lang Q <-> s \in neg_lang P.
Proof.
intros.
rewrite pq.
reflexivity.
Qed.

Example example_rewriting_using_lang_iff_in_iff''':
  forall (R: lang)
  (nnr: R {<->} neg_lang (neg_lang R)),
  forall s: str,
  s \in neg_lang R <-> s \in neg_lang (neg_lang (neg_lang R)).
Proof.
intros.
rewrite <- nnr.
reflexivity.
Qed.

(* Allow derive_langs expressions to also be rewritten using lang_iff expressions: *)

Add Parametric Morphism {s: str}: (derive_langs s)
  with signature lang_iff ==> lang_iff
  as derive_langs_morph.
Proof.
unfold derive_langs.
unfold "{<->}" in *.
intros.
unfold "\in" in *.
specialize H with (s := (s ++ s0)).
assumption.
Qed.

Example example_rewriting_using_lang_iff_in_derive_langs:
  forall (p q: regex)
  (pq: {{p}} {<->} {{q}}),
  forall s: str,
  derive_langs s {{q}} {<->} derive_langs s {{p}}.
Proof.
intros.
rewrite pq.
reflexivity.
Qed.

(* Allow derive_lang expressions to also be rewritten using lang_iff expressions: *)

Add Parametric Morphism {a: alphabet}: (derive_lang a)
  with signature lang_iff ==> lang_iff
  as derive_lang_morph.
Proof.
unfold derive_lang.
unfold "{<->}" in *.
intros.
unfold "\in" in *.
specialize H with (s := (a :: s)).
assumption.
Qed.

Example example_rewriting_using_lang_iff_in_derive_lang:
  forall (p q: regex)
  (pq: {{p}} {<->} {{q}}),
  forall a: alphabet,
  derive_lang a {{q}} {<->} derive_lang a {{p}}.
Proof.
intros.
rewrite pq.
reflexivity.
Qed.