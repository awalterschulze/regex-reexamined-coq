Require Import List.
Import ListNotations.

Require Import CoqStock.Invs.
Require Import CoqStock.Listerine.
Require Import CoqStock.Untie.
Require Import CoqStock.WreckIt.

Require Import Brzozowski.Alphabet.
Require Import Brzozowski.Boolean.
Require Import Brzozowski.Regex.
Require Import Brzozowski.Language.

(*
The introduction of arbitrary Boolean functions enriches the language of regular expressions.
For example, suppose we desire to represent the set of all sequences having three consecutive 1's
but not those ending in 01 or consisting of 1's only.
The desired expression is easily seen to be:

R = (I.1.1.1.I)\&(I.0.1+1.1^{*})'.
*)
Definition x1 := symbol A1.
Definition x0 := symbol A0.
Definition xI111I := concat I (concat x1 (concat x1 (concat x1 I))).
Definition xI01 := concat I (concat x0 x1).
Definition x11star := concat x1 (star x1).
Definition exampleR := and xI111I (complement (or xI01 x11star)).

Lemma test_in_xI01_101:
  ([A1] ++ [A0] ++ [A1]) \in {{xI01}}.
Proof.
unfold xI01.
constructor.
exists [A1].
exists ([A0] ++ [A1]).
assert ([A1] ++ [A0] ++ [A1] = [A1; A0; A1]). reflexivity.
exists H.
constructor.
- constructor.
  wreckit.
  apply notin_emptyset.
- constructor.
  exists [A0].
  exists [A1].
  exists eq_refl.
  constructor.
  + constructor.
  + constructor.
Qed.

Lemma test_notin_xI01_101_false:
  ([A1] ++ [A0] ++ [A1]) \notin {{xI01}}  -> False.
Proof.
unfold not.
intros.
apply H.
apply test_in_xI01_101.
Qed.

Local Ltac int :=
  match goal with
  | [ H : _ \in _ |- _ ] =>
    inversion H; clear H
  | [ |- context [_ \notin _ ] ] =>
    unfold not; intros
  end.

Lemma test_notleme_xI01_empty:
    [] \notin {{xI01}}.
Proof.
int.
int.
wreckit.
int.
subst.
cbn in x3.
listerine.
invs R.
wreckit.
listerine.
invs R.
Qed.

Lemma test_notin_xI01_10:
  ([A1] ++ [A0]) \notin {{xI01}}.
Proof.
int.
int.
wreckit.
int.
wreckit.
int.
int.
int.
wreckit.
subst.
assert (x ++ [A0] ++ [A1] <> [A1] ++ [A0]).
listerine.
apply H.
listerine.
- unfold "\notin" .
contradiction.
Qed.

Lemma test_notin_xI01_1110:
  ([A1] ++ [A1] ++ [A1] ++ [A0]) \notin {{xI01}}.
Proof.
int.
int.
wreckit.
int.
wreckit.
int.
int.
subst.
cbn in x3.
listerine.
Qed.

Lemma test_notin_x11star_0:
  [A0] \notin {{ x11star }}.
Proof.
int.
int.
wreckit.
int.
- subst.
  listerine.
  subst.
  int.
- int.
  + wreckit. subst. inversion H2. subst. cbn in x3. listerine.
  + wreckit. subst. inversion H2. subst. cbn in x3. listerine.
Qed.

Lemma test_notin_starx1_0:
  [A0] \notin {{star x1}}.
Proof.
untie.
invs H.
- listerine.
  + apply H1.
    reflexivity.
  + inversion H2.
Qed.

Lemma test_notin_starx1_10:
  [A1; A0] \notin {{star x1}}.
Proof.
untie.
invs H.
- listerine.
  + contradiction.
  + invs H3.
    invs H4.
    listerine.
  + invs H2.
Qed.

Lemma test_notin_starx1_110:
  [A1; A1; A0] \notin {{star x1}}.
Proof.
untie.
invs H.
invs H2.
listerine.
apply test_notin_starx1_10.
assumption.
Qed.

Lemma test_notin_x11star_1110:
  ([A1] ++ [A1] ++ [A1] ++ [A0]) \notin {{x11star}}.
Proof.
untie.
invs H.
wreckit.
listerine; (try invs L).
- apply test_notin_starx1_110.
  assumption.
Qed.

Lemma test_in_xI111I_1110:
    ([A1] ++ [A1] ++ [A1] ++ [A0]) \in {{xI111I}}.
Proof.
constructor.
exists [].
exists ([A1] ++ [A1] ++ [A1] ++ [A0]).
exists eq_refl.
split.
- constructor.
  wreckit.
  untie.
- constructor.
  exists [A1].
  exists ([A1] ++ [A1] ++ [A0]).
  exists eq_refl.
  split.
  + constructor.
  + constructor.
    exists [A1].
    exists ([A1] ++ [A0]).
    exists eq_refl.
    split.
    * constructor.
    * constructor.
      exists [A1].
      exists [A0].
      exists eq_refl.
      split.
      --- constructor.
      --- constructor.
          wreckit.
          untie.
Qed.

Theorem test_exampleR_1110_in:
    ([A1] ++ [A1] ++ [A1] ++ [A0]) \in {{exampleR}}.
Proof.
constructor.
split.
- untie.
  invs H.
  wreckit.
  apply L.
  apply test_in_xI111I_1110.
- untie.
  invs H.
  wreckit.
  apply L.
  clear R.
  clear L.
  constructor.
  wreckit.
  untie.
  invs H.
  wreckit.
  apply L.
  clear L.
  clear R.
  constructor.
  wreckit.
  + untie.
    apply test_notin_xI01_1110.
    assumption.
  + untie.
    apply test_notin_x11star_1110.
    assumption.
Qed.

Theorem test_exampleR_111_notin:
    [A1; A1; A1] \notin {{exampleR}}.
Proof.
untie.
invs H.
wreckit.
apply R.
constructor.
wreckit.
untie.
invs H.
wreckit.
apply L0.
constructor.
wreckit.
untie.
invs H.
wreckit.
apply R1.
constructor.
exists [A1].
exists [A1; A1].
exists eq_refl.
wreckit.
- constructor.
- apply mk_star_more with (p := [A1]) (q := [A1]).
  + listerine. reflexivity.
  + listerine.
  + fold (denote_regex x1).
    constructor.
  + fold (denote_regex x1).
    apply mk_star_more with (p := [A1]) (q := []).
    * now listerine.
    * listerine.
    * constructor.
    * constructor.
Qed.
