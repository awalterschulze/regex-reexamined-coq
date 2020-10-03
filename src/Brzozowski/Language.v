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
    *Star*. $P^{*} = \cup_{0}^{\infty} P^n$ , where $P^2 = P.P$, etc.
    and $P^0 = \lambda$, the set consisting of the string of zero length.
*)
Inductive star_lang (R: lang): lang :=
  | mk_star_zero : forall (s: str),
    s = [] -> star_lang R s
  | mk_star_more : forall (s: str),
    s `elem` (concat_prefix_not_empty_lang R (star_lang R)) ->
    star_lang R s
  .

(*
  star_lang_concat is the original definition of star_lang,
  but contains more recursion, since it allows R to match the empty string.
*)
Inductive star_lang_concat (R: lang): lang :=
  | mk_star_zero' : forall (s: str),
    s = [] -> star_lang_concat R s
  | mk_star_more' : forall (s: str),
    (exists
      (p: str)
      (q: str)
      (pqs: p ++ q = s),
      p `elem` R /\
      q `elem` star_lang_concat R
    )
    ->
    star_lang_concat R s
  .

Inductive star_lang_q (R: lang): lang :=
  | mk_star_zero_q : forall (s: str),
    s = [] -> star_lang_q R s
  | mk_star_more_q : forall (s: str) (p: str) (q: str),
      p ++ q = s ->
      p `elem` R ->
      q `elem` star_lang_q R ->
      s `elem` star_lang_q R
  .

Print star_lang_concat_ind.

  (*
  star_lang_concat_ind =
  fun (R : lang) (P : str -> Prop) (f : forall s : str, s = [] -> P s)
    (f0 : forall s : str,
        (exists (p q : str) (_ : p ++ q = s),
             (p `elem` R) /\ q `elem` star_lang_concat R) ->
          P s) (s : str) (s0 : star_lang_concat R s) =>
  match s0 in (star_lang_concat _ s1) return (P s1) with
  | mk_star_zero' _ x x0 => f x x0
  | mk_star_more' _ x x0 => f0 x x0
  end
       : forall (R : lang) (P : str -> Prop),
         (forall s : str, s = [] -> P s) ->
         (forall s : str,
          (exists (p q : str) (_ : p ++ q = s),
             (p `elem` R) /\ q `elem` star_lang_concat R) ->
          P s) ->
          forall s : str, star_lang_concat R s
          -> P s
  *)

Lemma our_better_induction_principle:
 forall (R : lang) (P : str -> Prop),
 (forall s : str, s = [] -> P s) ->
 (forall s: str,
 (exists (p q: str) (_: p ++ q = s),
   p `elem` R /\
   q `elem` star_lang_concat R /\
   P q)
      -> P s
 ) ->
 forall s: str, star_lang_concat R s
 -> P s.
Proof.
intros R P.
refine (
  (fix f (s: str) (Hbase: P []) Hind (x: star_lang_concat R s) {struct x}: P s  := _
  match x with
  | mk_star_zero' _ s _ => _
  | mk_star_more' _ s _ => _
  end) _ _ _ _
).


(*

Fixpoint nat_simple_rec (A:Type) (exp1-basecase:A) (exp2: nat->A  -> A) (x:nat)
  : A :=
  match x with
  | O => exp1
  | S p => exp2 p (nat_simple_rec A exp1 exp2 p)
  end.


*)


intros.
invs H1.
- apply H. reflexivity.
- specialize H0 with s.
  generalize H0.

  apply H0.


 forall s p q : str,
  p ++ q = s ->
  p `elem` R ->
  q `elem` star_lang_q R ->
  P q ->
  P s) ->
forall s : str, star_lang_q R s
-> P s
Print star_lang_q_ind.

(*
star_lang_q_ind =
fun (R : lang) (P : str -> Prop) (f : forall s : str, s = [] -> P s)
  (f0 : forall s p q : str,
	    p ++ q = s -> p `elem` R -> q `elem` star_lang_q R -> P q -> P s) =>
fix F (s : str) (s0 : star_lang_q R s) {struct s0} : P s :=
  match s0 in (star_lang_q _ s1) return (P s1) with
  | mk_star_zero_q _ s1 e => f s1 e
  | mk_star_more_q _ s1 p q e e0 e1 => f0 s1 p q e e0 e1 (F q e1)
  end
     : forall (R : lang) (P : str -> Prop),
       (forall s : str, s = [] -> P s) ->
       (forall s p q : str,
        p ++ q = s ->
        p `elem` R ->
        q `elem` star_lang_q R ->
        P q ->
        P s) ->
       forall s : str, star_lang_q R s
       -> P s
*)

Lemma star_lang_q_helper:
  forall (R: lang) (s: str),
  star_lang_concat R s -> star_lang_q R s.
Proof.
intros.
invs H.
- admit.
- destruct H0.
  wreckit.
  eapply mk_star_more_q.
  + apply x1.
  + assumption.
  +



Lemma star_lang_q_helper:
  forall (R: lang) (s: str),
  star_lang_q R s -> star_lang R s.
Proof.
intros.
induction H.
- constructor.
  assumption.
- destruct p.
  + subst.
    cbn.
    assumption.
  + apply mk_star_more.
    constructor.
    exists p.
    exists a.
    exists q.
    exists H.
    split.
    * assumption.
    * assumption.
Qed.


Inductive depth (R: lang) : str -> nat -> Prop :=
 | depth_zero : forall (s: str),
   s = [] -> depth R s 0
 | depth_more : forall (s: str) (d: nat) (p: str) (q: str),
      p ++ q = s ->
      p `elem` R ->
      depth (star_lang R) q d ->
   depth R s (S d)
 .

Lemma star_is_star_helper:
 forall (R: lang) (s: str),
 star_lang' R s ->
 (exists
   (d: nat),
   depth R s d
 ).
Proof.
intros.

induction s.
- exists 0. constructor. reflexivity.
- invs H.
 + listerine.
 + invs H0.
   wreckit.
   destruct x.
   * listerine.

Inductive star_lang_max_depth (R: lang): nat -> lang :=
  | mk_star_zero'' : forall (s: str),
    s = [] -> star_lang_max_depth R 0 s
  | mk_star_more'' : forall (s: str) (depth: nat),
    s `elem` (concat_lang R (star_lang_max_depth R depth)) ->
    star_lang_max_depth R (S depth) s
  .






Lemma star_is_star_depth_helper:
  forall (R: lang) (depth: nat) (s: str),
  star_lang_max_depth R depth s -> star_lang R s.
Proof.
induction depth.
- intros.
  invs H.
  constructor.
  reflexivity.
- intros.
  invs H.
  invs H1.
  wreckit.
  apply IHdepth in R0.
  destruct x.
  + subst.
    cbn.
    assumption.
  + apply mk_star_more.
    constructor.
    exists x.
    exists a.
    exists x0.
    exists x1.
    split.
    * assumption.
    * assumption.
Qed.

(*
  star_is_star shows that the new definition of star_lang and
  the original definition of star_lang' are equivalent.
*)
Theorem star_is_star:
  forall (R: lang),
  star_lang R {<->} star_lang' R.
Proof.
intros.
split.
- admit.
- intros.
  induction H.
  + admit.
  + invs H.
  induction s.
  + constructor.
    reflexivity.
  +
  induction H.
  + subst.
    constructor.
    reflexivity.
  + induction H0.
    wreckit.
    apply mk_star_more.
    constructor.

    constructor.

(* TODO: Help Wanted *)
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
