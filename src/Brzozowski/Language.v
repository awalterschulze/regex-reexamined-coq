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

Inductive concat_prefix_not_empty_lang (P Q: lang): lang :=
  | mk_concat_prefix_is_not_empty: forall (s: str),
    (exists
      (p: str)
      (a: alphabet)
      (q: str)
      (pqs: (a :: p) ++ q = s),
      (a :: p) `elem` P /\
      q `elem` Q
    ) ->
    concat_prefix_not_empty_lang P Q s
  .

Theorem concat_prefix_not_empty_lang_is_concat_lang:
  forall (P Q: lang) (s: str),
  concat_prefix_not_empty_lang P Q s ->
  concat_lang P Q s.
Proof.
intros.
inversion H.
wreckit.
subst.
constructor.
exists (x0 :: x).
exists x1.
exists eq_refl.
wreckit; assumption.
Qed.

Theorem concat_lang_is_concat_prefix_not_empty_lang:
  forall (P Q: lang) (s: str),
  [] `notelem` P ->
  concat_lang P Q s ->
  concat_prefix_not_empty_lang P Q s.
Proof.
intros.
inversion H0.
wreckit.
subst.
destruct x.
- contradiction.
- constructor.
  exists x.
  exists a.
  exists x0.
  exists eq_refl.
  wreckit; assumption.
Qed.

(*
   concat_prefix_not_empty_lang_morph allows rewrite to work inside concat_prefix_not_empty_lang parameters
*)
Add Parametric Morphism: concat_prefix_not_empty_lang
  with signature lang_iff ==> lang_iff ==> lang_iff as concat_prefix_not_empty_lang_morph.
Proof.
intros P P'.
intros Piff.
intros Q Q'.
intros Qiff.
unfold "{<->}" in *.
unfold "`elem`" in *.
split.
- intro H.
  invs H.
  destruct H0 as [p [a [q [splt [Pmatch Qmatch]]]]].
  constructor.
  exists p.
  exists a.
  exists q.
  exists splt.
  wreckit.
  + specialize Piff with (a :: p).
    apply Piff.
    assumption.
  + specialize Qiff with q.
    apply Qiff.
    assumption.
- intro H.
  invs H.
  destruct H0 as [p [a [q [splt [Pmatch Qmatch]]]]].
  constructor.
  exists p.
  exists a.
  exists q.
  exists splt.
  wreckit.
  + specialize Piff with (a :: p).
    apply Piff.
    assumption.
  + specialize Qiff with q.
    apply Qiff.
    assumption.
Qed.


(*

Different possible definitions of star_lang:

- allowing empty prefixes in `mk_star_more` or not
- using an existence statement or not

This gives 4 equivalent definitions.

The definitions that use an existence statement (e.g. the existence statement
that is part of `concat_lang` and `concat_prefix_not_empty_lang`) require you to
prove your own induction principle, because Coq is not smart enough to figure it
out by itself. The definitions that allow empty prefixes make induction more
difficult if the regular expression matches the empty string.

Therefore, the easiest definition is the one that does not have an empty prefix
and that does not allow empty prefixes, and I suggest that we use that one as
our main definition.

Below, we define all these definitions and prove their equivalence. As part of
the proofs, we prove a stronger induction principle for the two definitions that
use an existence statement.

*)

(* Most convenient definition. *)
Inductive star_lang (R: lang): lang :=
  (* Note to Walter: I've decided to use `star_lang R []`, because otherwise
   when I use the tactic constructor, it always applies the wrong constructor. *)
  | mk_star_zero : star_lang R []
  | mk_star_more : forall (s p q: str),
      p ++ q = s ->
      p <> [] ->
      p `elem` R ->
      q `elem` (star_lang R) ->
      s `elem` star_lang R.

(*
  star_lang_concat is the original definition of star_lang,
  but contains more recursion, since it allows R to match the empty string.
*)
(* The definition allowing empty prefixes. *)
Inductive star_lang_empty (R: lang): lang :=
  | mk_star_zero_empty : forall (s: str),
      s = [] -> star_lang_empty R s
  | mk_star_more_empty : forall (s p q: str),
      p ++ q = s ->
      p `elem` R ->
      q `elem` (star_lang_empty R) ->
      s `elem` star_lang_empty R.

(*
    *Star*. $P^{*} = \cup_{0}^{\infty} P^n$ , where $P^2 = P.P$, etc.
    and $P^0 = \lambda$, the set consisting of the string of zero length.
*)
(* Definition using the existence statement (hidden in `concat_prefix_not_empty_lang`). *)
Inductive star_lang_ex (R: lang): lang :=
  | mk_star_zero_ex : forall (s: str),
      s = [] -> star_lang_ex R s
  | mk_star_more_ex : forall (s: str),
      s `elem` (concat_prefix_not_empty_lang R (star_lang_ex R)) ->
      star_lang_ex R s.

(* The definition allowing empty prefixes and using the existence statement (hidden in `concat_lang`). The most difficult definition to use in Coq, but arguably the closest to the mathematical definition. *)
Inductive star_lang_ex_empty (R: lang): lang :=
  | mk_star_zero_ex_empty : forall (s: str),
      s = [] -> star_lang_ex_empty R s
  | mk_star_more_ex_empty : forall (s: str),
      s `elem` (concat_lang R (star_lang_ex_empty R)) ->
      star_lang_ex_empty R s.

Proposition star_lang_empty_equivalent (R: lang): forall (s: str),
   s `elem` star_lang R <-> s `elem` star_lang_empty R.
Proof.
  split.
  - intro Hmatch.
    induction Hmatch.
    + subst. now constructor.
    + eapply (mk_star_more_empty R s); try (exact H); try assumption.
  - intro Hmatch.
    induction Hmatch as [| s p q Hp_match Hq_match IH].
    + subst. now constructor.
    + destruct p as [p | a p].
      * (* If the prefix is empty, the induction hypothesis is exactly what we want. *)
        subst.
        cbn.
        assumption.
      * (* Otherwise, we only have to apply the constructor and use the IH. *)
        apply (mk_star_more R s (a :: p) q); try assumption.
        trivial.
        listerine.
Qed.

Proposition star_lang_ex_ind_better:
 forall (R : lang) (P : str -> Prop),
   (* base case *)
   P [] ->
   (* induction step *)
   (forall s: str, (exists (p q: str),
                  p ++ q = s /\
                  p <> [] /\
                  p `elem` R /\
                  q `elem` star_lang_ex R /\
                  P q) ->
              P s) ->
   (* conclusion *)
   forall s: str, star_lang_ex R s -> P s.
Proof.
intros R P Hbase Hstep s0 Hs_match0.
refine (
    (fix f s (Hs_match: star_lang_ex R s) {struct Hs_match}: P s  :=
       _) s0 Hs_match0
).
destruct Hs_match.
- subst.
  exact Hbase.
- specialize Hstep with s.
  destruct H as [s [p [a [q [Hconcat [Hp_match Hq_match]]]]]].
  pose (f q Hq_match) as IH.
  apply Hstep.
  exists (a :: p).
  exists q.
  repeat split; try assumption.
  listerine.
Qed.

Proposition star_lang_ex_equivalent (R: lang): forall (s: str),
    s `elem` star_lang R <-> s `elem` star_lang_ex R.
Proof.
  split.
  - intro Hmatch.
    induction Hmatch.
    + subst. now constructor.
    + eapply (mk_star_more_ex R s); try (exact H).
      constructor.
      destruct p as [p | a p].
      * contradiction.
      * exists p.
        exists a.
        exists q.
        exists H.
        split; assumption.
  - intro Hmatch.
    apply (star_lang_ex_ind_better R).
    + now constructor.
    + intros.
      destruct H as [p [q [Hconcat [ Hnon_empty [ Hp_match [Hq_match IH]]]]]].
      constructor 2 with (p := p) (q := q); assumption.
    + assumption.
Qed.

Proposition star_lang_ex_empty_ind_better:
 forall (R : lang) (P : str -> Prop),
   (* base case *)
   P [] ->
   (* induction step *)
   (forall s: str, (exists (p q: str),
                  p ++ q = s /\
                  p `elem` R /\
                  q `elem` star_lang_ex_empty R /\
                  P q) ->
              P s) ->
   (* conclusion *)
   forall s: str, star_lang_ex_empty R s -> P s.
Proof.
intros R P Hbase Hstep s0 Hs_match0.
refine (
    (fix f s (Hs_match: star_lang_ex_empty R s) {struct Hs_match}: P s  :=
       _) s0 Hs_match0
).
destruct Hs_match.
- subst.
  exact Hbase.
- specialize Hstep with s.
  destruct H as [s [p [q [Hconcat [Hp_match Hq_match]]]]].
  pose (f q Hq_match) as IH.
  apply Hstep.
  exists p.
  exists q.
  repeat split; try assumption.
Qed.

Proposition star_lang_ex_empty_equivalent (R: lang): forall (s: str),
    s `elem` star_lang R <-> s `elem` star_lang_ex_empty R.
Proof.
  split.
  - intro Hmatch.
    induction Hmatch.
    + subst. now constructor.
    + eapply (mk_star_more_ex_empty R s); try (exact H).
      constructor.
      destruct p as [p | a p].
      * contradiction.
      * exists (a :: p).
        exists q.
        exists H.
        split; assumption.
  - intro Hmatch.
    apply (star_lang_ex_empty_ind_better R).
    + now constructor.
    + intros.
      destruct H as [p [q [Hconcat [ Hp_match [Hq_match IH]]]]].
      destruct p as [p | a p].
      * subst. cbn. assumption.
      * constructor 2 with (p := (a :: p)) (q := q); try assumption.
        listerine.
    + assumption.
Qed.


(* A fifth definition of star_lang: this definition includes a notion of
"depth". It allows empty prefixes, but it uses an integer to keep track of the
depth of the constructor tree. *)
Inductive star_lang_max_depth (R: lang): nat -> lang :=
  | mk_star_zero'' : forall (s: str),
    s = [] -> star_lang_max_depth R 0 s
  | mk_star_more'' : forall (s: str) (depth: nat),
    s `elem` (concat_lang R (star_lang_max_depth R depth)) ->
    star_lang_max_depth R (S depth) s
  .

Lemma star_lang_depth_equivalent_helper:
  forall (R: lang) (depth: nat) (s: str),
  star_lang_max_depth R depth s -> star_lang R s.
Proof.
    induction depth.
  + intros.
    invs H.
    constructor.
  + intros.
    invs H.
    invs H1.
    wreckit.
    apply IHdepth in R0.
    destruct x.
    * subst.
      cbn.
      assumption.
    * apply mk_star_more with (p := (a ::x)) (q := x0).
      assumption.
      listerine.
      assumption.
      assumption.
Qed.

Lemma star_lang_depth_equivalent:
  forall (R: lang) (s: str),
    (exists (depth: nat), star_lang_max_depth R depth s) <-> star_lang R s.
Proof.
(* TODO: Good First Issue

I don't think we need this lemma anymore, but it could be an interesting first
issue, or an interesting exercise. (Maybe a difficult first issue, though.)
*)
Abort.


Theorem star_lang_morph_helper:
  forall (x y : lang) (s: str) (n: nat) (L: length s <= n),
  (x {<->} y)
  -> (s `elem` star_lang x <-> s `elem` star_lang y).
Proof.
intros R R' s n L Riff.
unfold "{<->}" in *.
unfold "`elem`" in *.
generalize dependent s.
induction n.
- admit.
- split.
  + intro H.
    inversion H.
    * apply mk_star_zero.
      assumption.
    * apply mk_star_more.
      unfold "`elem`" in *.
      induction H0.
      constructor.
      destruct H0 as [p [a [q [splt [Pmatch Qmatch]]]]].
      exists p.
      exists a.
      exists q.
      exists splt.
      unfold "`elem`" in *.
      apply (Riff (a :: p)) in Pmatch.
      wreckit.
      --- assumption.
      --- subst.
          specialize IHn with q.
          assert (length q <= n).
          +++ admit.
          +++ apply IHn in H0.
              apply H0.
              assumption.
  + admit.
(* TODO: Good First Issue *)
Abort.

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

Example lemma_for_setoid_example_concat_lang_emptyset_l_is_emptyset: forall (r: lang),
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
