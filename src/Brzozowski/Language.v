Require Import Coq.Setoids.Setoid.

Require Import CoqStock.DubStep.
Require Import CoqStock.Invs.
Require Import CoqStock.List.
Require Import CoqStock.Listerine.
Require Import CoqStock.Untie.
Require Import CoqStock.WreckIt.

Require Import Brzozowski.Alphabet.
Require Import Brzozowski.Regex.

(* A string is a list of characters. *)
Definition str := list alphabet.
(* A regular expression denotes a set of strings called a _language_. *)
Definition lang := str -> Prop.
Definition elem (l: lang) (s: str): Prop := l s.
Notation "p `elem` P" := (elem P p) (at level 80).
Notation "p `notelem` P" := (~ (elem P p)) (at level 80).

Definition lang_if (s1 s2: lang): Prop :=
  forall (s: str),
  s `elem` s1 -> s `elem` s2.

Notation "s1 {->} s2" := (lang_if s1 s2) (at level 80).

Definition lang_iff (s1 s2: lang): Prop :=
  forall (s: str),
  s `elem` s1 <-> s `elem` s2.

Notation "s1 {<->} s2" := (lang_iff s1 s2) (at level 80).

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

(* Concatenation*. $(P.Q) = \{ s | s = p.q; p \in P, q \in Q \}$. *)
Inductive concat_lang (P Q: lang): lang :=
  | mk_concat: forall (p q s: str),
    p ++ q = s ->
    p `elem` P ->
    q `elem` Q ->
    concat_lang P Q s
  .

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

Inductive star_lang (R: lang): lang :=
  | mk_star_zero : star_lang R []
  | mk_star_more : forall (s p q: str),
      p ++ q = s ->
      p <> [] ->
      p `elem` R ->
      q `elem` (star_lang R) ->
      s `elem` star_lang R.

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

Theorem star_lang_morph:
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
set (n := length s).
(* TODO: apply star_lang_morph_helper, but first prove it *)
(* apply (star_lang_morph_helper R R' s (length s)).
- trivial.
- unfold "{<->}" in *.
  intro s0.
  specialize Riff with s0.
  assumption. *)
(* TODO: Good First Issue *)
Abort.

(*
    *Boolean function*. We shall denote any Boolean function of $P$ and $Q$ by $f(P, Q)$.
    Of course, all the laws of Boolean algebra apply.
    `nor` is used to emulate `f`, since nor can be used to emulate all boolean functions.
*)
Inductive nor_lang (P Q: lang): lang :=
  | mk_nor : forall s,
    s `notelem` P /\ s `notelem` Q ->
    nor_lang P Q s
  .

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

Inductive emptyset_lang: lang :=
  .
  (*
  This is equivalent to:
  ```
  | mk_emptyset: forall (s: str),
    False ->
    emptyset_lang s
  ```
  *)

Inductive lambda_lang: lang :=
  | mk_lambda: lambda_lang []
  .
  (*
  This is equivalent to:
  ```
  | mk_lambda:
    forall (s: str),
    s = [] ->
    lambda_lang s
  ```
  *)

Inductive symbol_lang (a: alphabet): lang :=
  | mk_symbol: symbol_lang a [a].
  (*
  This is equivalent to:
  ```
  | mk_symbol:
    forall (s: str),
    s = [a] ->
    symbol_lang a s
  ```
  *)

(*
  Here we use a mix of Fixpoint and Inductive predicates to define the denotation of regular expressions.
*)
Reserved Notation "{{ r }}" (r at level 60, no associativity).
Fixpoint denote_regex (r: regex): lang :=
  match r with
  | emptyset => emptyset_lang
  | lambda => lambda_lang
  | symbol y => symbol_lang y
  | concat r1 r2 => concat_lang {{r1}} {{r2}}
  | star r1 => star_lang {{r1}}
  | nor r1 r2 => nor_lang {{r1}} {{r2}}
  end
where "{{ r }}" := (denote_regex r).

Theorem notelem_emptyset: forall (s: str),
  s `notelem` emptyset_lang.
Proof.
intros.
untie.
Qed.

Definition not_lang (R: lang) : lang :=
  nor_lang R R.

Theorem not_not_regex_is_regex:
  forall (r: regex) (s: str),
  ((~ ~ (s `elem` {{ r }})) -> (s `elem` {{ r }})).
Proof.
  intros.
  assert (s `elem` {{ r }} \/ s `notelem` {{ r }}).
  - admit. (* TODO: apply denotation_is_decidable *)
  - intros.
  unfold not in *.
  destruct H0 as [x | not_x].
  + exact x.
  + apply H in not_x.
    induction not_x.
Abort.

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
