Require Import List.
Import ListNotations.
Require Import Setoid.

Require Import CoqStock.DubStep.
Require Import CoqStock.Invs.
Require Import CoqStock.Listerine.
Require Import CoqStock.Untie.
Require Import CoqStock.WreckIt.

Require Import Brzozowski.Alphabet.
Require Import Brzozowski.Regex.

(* A string is a list of characters. *)
Definition str := (list alphabet).
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
  | mk_concat: forall (s: str),
    (exists
      (p: str)
      (q: str)
      (pqs: p ++ q = s),
      p `elem` P /\
      q `elem` Q
    ) ->
    concat_lang P Q s
  .

(*
   concat_lang_morph allows rewrite to work inside concat_lang parameters
*)
Add Parametric Morphism: concat_lang
  with signature lang_iff ==> lang_iff ==> lang_iff as concat_lang_morph.
Proof.
intros.
constructor; constructor; invs H1; wreckit;
  exists x1;
  exists x2;
  exists x3;
  wreckit.
  + apply H.
    assumption.
  + apply H0.
    assumption.
  + apply H.
    assumption.
  + apply H0.
    assumption.
Qed.

(*
    *Star*. $P^{*} = \cup_{0}^{\infty} P^n$ , where $P^2 = P.P$, etc.
    and $P^0 = \lambda$, the set consisting of the string of zero length.
*)
Inductive star_lang (R: lang): lang :=
  | mk_star_zero : forall (s: str),
    s = [] -> star_lang R s
  | mk_star_more : forall (s: str),
    s `elem` (concat_lang R (star_lang R)) ->
    star_lang R s
  .

(*
   star_lang_morph allows rewrite to work inside star_lang parameters
*)
Add Parametric Morphism: star_lang
  with signature lang_iff ==> lang_iff as star_lang_morph.
Proof.
(* TODO: Help Wanted *)
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

Lemma denotation_emptyset_is_decidable (s: str):
  s `elem` {{ emptyset }} \/ s `notelem` {{ emptyset }}.
Proof.
right.
apply notelem_emptyset.
Qed.

Lemma denotation_lambda_is_decidable (s: str):
  s `elem` {{ lambda }} \/ s `notelem` {{ lambda }}.
Proof.
destruct s.
- left. constructor.
- right. untie. invs H.
Qed.

Lemma denotation_symbol_is_decidable (s: str) (a: alphabet):
  s `elem` {{ symbol a }} \/ s `notelem` {{ symbol a }}.
Proof.
destruct s.
- right. untie. invs H.
- destruct a, a0.
  + destruct s.
    * left.
      constructor.
    * right.
      untie.
      invs H.
  + right.
    untie.
    invs H.
  + right.
    untie.
    invs H.
  + destruct s.
    * left.
      constructor.
    * right.
      untie.
      invs H.
Qed.

Lemma denotation_nor_is_decidable (p q: regex) (s: str):
  s `elem` {{ p }} \/ s `notelem` {{ p }} ->
  s `elem` {{ q }} \/ s `notelem` {{ q }} ->
  s `elem` {{ nor p q }} \/ s `notelem` {{ nor p q }}.
Proof.
simpl.
intros.
wreckit.
- right.
  untie.
  invs H.
  wreckit.
  contradiction.
- right.
  untie.
  invs H.
  wreckit.
  contradiction.
- right.
  untie.
  invs H.
  wreckit.
  contradiction.
- left.
  constructor.
  wreckit.
  * assumption.
  * assumption.
Qed.

Lemma denotation_concat_is_decidable_for_empty_string (p q: regex):
  [] `elem` {{ p }} \/ [] `notelem` {{ p }} ->
  [] `elem` {{ q }} \/ [] `notelem` {{ q }} ->
  [] `elem` {{ concat p q }} \/ [] `notelem` {{ concat p q }}.
Proof.
intros.
wreckit.
- left.
  constructor.
  exists [].
  exists [].
  exists eq_refl.
  wreckit; assumption.
- right.
  untie.
  invs H.
  wreckit.
  listerine.
  contradiction.
- right.
  untie.
  invs H.
  wreckit.
  listerine.
  contradiction.
- right.
  untie.
  invs H.
  wreckit.
  listerine.
  contradiction.
Qed.

Definition regex_is_decidable (r: regex) :=
    (forall s: str, s `elem` {{r}} \/ s `notelem` {{r}}).

Require Import Lia.

Lemma length_zero_string_is_empty (s : str) :
  length s <= 0 -> s = [].
Proof.
  intros.
  assert (length s = 0).
  lia.
  rewrite length_zero_iff_nil in *.
  assumption.
Qed.


Lemma denotation_concat_is_decidable_helper (p q: regex):
  regex_is_decidable p ->
  regex_is_decidable q ->
  (forall (s: str) (n : nat),
      (* prove about only a subset of all splittings *)
      (forall (s1 s2: str),
          s = s1 ++ s2 ->
          length s1 <= n ->
          (* matches concat, or does not match concat pairwise *)
          (
            (s1 `elem` {{ p }} /\ s2 `elem` {{ q }}) (* matches pairwise *)
              \/ (s1 `notelem` {{ p }} \/ s2 `notelem` {{ q }}) (* does not match pairwise *)
  ))).
Proof.
  intros Hdecp Hdecq s n s1 s2 Hconc Hlen.
  induction n.
  - (* case that s1 is empty string *)
    apply length_zero_string_is_empty in Hlen.
    subst.
    (* Need to: desctruct decidability for p on emptystring, and q on s2 *)
    destruct (Hdecp []);
      destruct (Hdecq s2);
      auto. (* now just some lefts and rights *)
  - (* if length s1 <= n, we are done *)
    assert (length s1 <= n \/ length s1 = S n) as Hlen' by lia.
    destruct Hlen' as [Hlen' | Hlen'].
    exact (IHn Hlen').
    (* now the case where length s1 = S n *)
    destruct (Hdecp s1); destruct (Hdecq s2); auto.
Qed.
(* TODO: think about the above lemma again. It feels a bit like
 I wouldn't have needed to use induction... *)


Lemma denotation_concat_is_decidable_helper_plus (p q: regex):
  regex_is_decidable p ->
  regex_is_decidable q ->
  (forall (s: str),
      (* prove about only a subset of all splittings *)
      (forall (s1 s2: str),
          s = s1 ++ s2 ->
          (* matches concat, or does not match concat pairwise *)
          (
            (s1 `elem` {{ p }} /\ s2 `elem` {{ q }}) (* matches pairwise *)
              \/ (s1 `notelem` {{ p }} \/ s2 `notelem` {{ q }}) (* does not match pairwise *)
  ))).
Proof.
  intros Hdecp Hdecq s s1 s2 Hconc.
  cut (length s1 <= length s).
  intros.
  eapply (denotation_concat_is_decidable_helper p q Hdecp Hdecq s (length s)); try assumption.
  Admitted. (* TODO: this should be easy *)


Lemma split_string_lemma (s : str) (n : nat):
  forall (s1 s2: str),
    length s1 = n ->
    s = s1 ++ s2 ->
    s1 = firstn n s /\
    s2 = skipn n s.
Proof.
  intros.
  set (s1' := firstn n s).
  set (s2' := skipn n s).
  subst.

  set (firstn_app (length s1) s1 s2) as Hfirst.
  replace (length s1 - length s1) with 0 in * by lia.
  replace (firstn 0 s2) with (nil : str) in * by (symmetry; apply firstn_O).
  rewrite app_nil_r in Hfirst.
  replace (firstn (length s1) s1) with s1 in Hfirst by (symmetry; apply firstn_all).

  set (skipn_app (length s1) s1 s2) as Hlast.
  replace (length s1 - length s1) with 0 in * by lia.
  replace (skipn (length s1) s1) with (nil: str) in Hlast by (symmetry; apply skipn_all).
  rewrite app_nil_l in Hlast.
  replace (skipn 0 s2) with s2 in Hlast by (apply skipn_O).

  split; auto.
Qed.



Lemma denotation_concat_is_decidable_helper_attempt2 (p q: regex):
  regex_is_decidable p ->
  regex_is_decidable q ->
  (forall (s: str) (n : nat),
      (* prove that either all splittings don't match, or there is a match;
         but only consider a subset of all splttings
       *)
      (forall (s1 s2: str),
          s = s1 ++ s2 ->
          length s1 <= n ->
          (* does not match concat pairwise *)
          ((s1 `notelem` {{ p }} \/ s2 `notelem` {{ q }})))
      \/ (exists (s1 s2: str),
            s = s1 ++ s2 /\
            length s1 <= n /\
            (s1 `elem` {{ p }} /\ s2 `elem` {{ q }}))).
Proof.
  intros Hdecp Hdecq s n.
  induction n.
  - (* case that s1 is empty string *)
    destruct (Hdecp []) as [Hpmatches | Hpnomatch]; destruct (Hdecq s) as [Hqmatches | Hqnomatch].


    2,3,4: left; intros s1 s2 Hconcat Hlen';
      (* this could maybe use some refactoring.
         But in principle it is simple: I want to do exactly this
         for goals 2,3 and 4.
       *)
      (* now starts: we know what it is when it is split *)
      assert (s1 = []) by (apply length_zero_string_is_empty; assumption);
      assert (s2 = s) by (replace (s1 ++ s2) with s2 in Hconcat by (subst; auto);
                          symmetry;
                          assumption);
      clear Hconcat;
      clear Hlen';
      subst;
      try (now left);
      try (now right).

    + (* this is the case where in fact s matches q, [] matches p *)
      right.
      exists [].
      exists s.
      intros.
      auto.

  -
    set (l1 := firstn (S n) s).
    set (l2 := skipn (S n) s).

    (* lots of case distinctions: *)

    destruct IHn as [IHnAllNoMatch | IHnExistsMatch ].

    (* The case where there is already a match with a smaller split. *)
    Focus 2.
    right.
    destruct IHnExistsMatch as [s1 IHn1].
    destruct IHn1 as [s2 IHn].
    exists s1. exists s2.
    destruct IHn as [H0 [H1 [H2 H3]]].
    repeat split; try assumption.
    lia.


    (* If none of the earlier splits match. *)
    destruct (Hdecp l1) as [Hpmatch | Hpnomatch].
      destruct (Hdecq l2) as [Hqmatch | Hqnomatch ].

      2,3: left;
      intros s1 s2 Hconcat Hlen;
      assert (length s1 <= n \/ length s1 = S n) as Hlen' by lia;
      destruct Hlen' as [Hlen' | Hlen'];
      try (apply IHnAllNoMatch; assumption); (* case length s1 <= n *)
      try (
          destruct (split_string_lemma s (S n) s1 s2 Hlen' Hconcat) as [Hfoo Hbar];

          replace l1 with s1 in * by auto;
          replace l2 with s2 in * by auto;
          subst;
          try (left; assumption);
          try (right; assumption)).


    + right. exists l1. exists l2. intros.

      repeat split; try assumption.

      * symmetry. apply firstn_skipn.
      * apply firstn_le_length.


        (* The proof below is the proof for 2,3, but written with periods instead of semicolons...
           the periods are easier to step through, and it is also how I wrote it.
           But as I've said above, I don't know how to do that for 2 goals at the same time.

         *)
        (*
    +
      left.
      intros s1 s2 Hconcat Hlen.

      assert (length s1 <= n \/ length s1 = S n) as Hlen' by lia.
      destruct Hlen' as [Hlen' | Hlen'].

      * apply IHnAllNoMatch; assumption. (* case length s1 <= n *)
      * destruct (split_string_lemma s (S n) s1 s2 Hlen' Hconcat) as [Hfoo Hbar].

        replace l1 with s1 in * by auto.
        replace l2 with s2 in * by auto.
        subst.
        try (left; assumption).
        try (right; assumption).
*)

Qed.

Lemma substrings_have_smaller_length (s s1 s2: str):
  s = s1 ++ s2 -> length s1 <= length s.
Proof.
  intro H.
  assert (length s1 + length s2 = length s).
  replace s with (s1 ++ s2) by assumption.
  symmetry.
  exact (app_length s1 s2).
  lia.
Qed.


Lemma denotation_concat_is_decidable (p q: regex):
  regex_is_decidable p ->
  regex_is_decidable q ->
  regex_is_decidable (concat p q).
Proof.
  intros Hdecp Hdecq.
  unfold regex_is_decidable.
  intro s.
  Print denotation_concat_is_decidable_helper_attempt2.
  destruct (denotation_concat_is_decidable_helper_attempt2 p q Hdecp Hdecq s (length s))
  as [HAllDontMatch | HExistsMatch].

  - right.
    unfold not.
    intro HmatchContr.
    destruct HmatchContr as [s [s1 [s2 [Hconcat [Hmatchp Hmatchq]]]]].
    symmetry in Hconcat.

    set (Hlen := substrings_have_smaller_length s s1 s2 Hconcat).

    specialize HAllDontMatch with s1 s2.
    destruct (HAllDontMatch Hconcat Hlen); auto.

  - left.
    destruct HExistsMatch as [s1 [s2 [Hconcat [Hlen [Hmatchp Hmatchq]]]]].
    constructor.
    symmetry in Hconcat.
    exists s1. exists s2. exists Hconcat.
    split; assumption.
Qed.

Lemma denotation_star_is_decidable_for_empty_string (r: regex):
  [] `elem` {{ star r }} \/ [] `notelem` {{ star r }}.
Proof.
left.
constructor.
reflexivity.
Qed.

Lemma denotation_is_decidable_on_empty_string (r: regex):
  [] `elem` {{ r }} \/ [] `notelem` {{ r }}.
Proof.
intros.
induction r.
- apply denotation_emptyset_is_decidable.
- apply denotation_lambda_is_decidable.
- apply denotation_symbol_is_decidable.
- apply denotation_concat_is_decidable_for_empty_string.
  + assumption.
  + assumption.
- apply denotation_star_is_decidable_for_empty_string.
- apply denotation_nor_is_decidable.
  + assumption.
  + assumption.
Qed.

Theorem denotation_is_decidable (r: regex) (s: str):
  s `elem` {{ r }} \/ s `notelem` {{ r }}.
Proof.
generalize dependent s.
induction r.
- apply denotation_emptyset_is_decidable.
- apply denotation_lambda_is_decidable.
- intros. apply denotation_symbol_is_decidable.
- admit. (* TODO: Help Wanted *)
  (* apply denotation_concat_is_decidable.
  + assumption.
  + assumption.
  *)
- admit. (* TODO: Help Wanted *)
- intros.
  specialize IHr1 with s.
  specialize IHr2 with s.
  apply denotation_nor_is_decidable; assumption.
Abort.

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
  wreckit.
  invs L.
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
rewrite concat_lang_emptyset_l_is_emptyset.
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
rewrite concat_lang_emptyset_l_is_emptyset.
reflexivity.
Qed.

Theorem concat_lang_emptyset_l: forall (r: lang) (s: str),
  s `notelem` concat_lang emptyset_lang r.
Proof.
intros.
untie.
invs H.
wreckit.
invs L.
Qed.

Theorem concat_lang_emptyset_r_is_emptyset: forall (r: lang),
  concat_lang r emptyset_lang
  {<->}
  emptyset_lang.
Proof.
split.
- intros.
  invs H.
  wreckit.
  invs R.
- intros.
  invs H.
Qed.

Theorem concat_lang_emptyset_r: forall (r: lang) (s: str),
  s `notelem` concat_lang r emptyset_lang.
Proof.
intros.
untie.
invs H.
wreckit.
invs R.
Qed.

Theorem concat_lang_lambda_l_is_l: forall (r: lang),
  concat_lang lambda_lang r
  {<->}
  r.
Proof.
split.
- intros.
  invs H.
  wreckit.
  subst.
  inversion_clear L.
  cbn.
  assumption.
- intros.
  constructor.
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
  inversion_clear R.
  listerine.
  assumption.
- intros.
  constructor.
  exists s.
  exists [].
  assert (s ++ [] = s). listerine. reflexivity.
  exists H0.
  split.
  + assumption.
  + constructor.
Qed.
