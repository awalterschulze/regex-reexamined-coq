Require Import CoqStock.Invs.
Require Import CoqStock.List.
Require Import CoqStock.Listerine.
Require Import CoqStock.Untie.
Require Import CoqStock.WreckIt.

Require Import Brzozowski.Alphabet.
Require Import Brzozowski.Boolean.
Require Import Brzozowski.Regex.
Require Import Brzozowski.ConcatLang.
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

Lemma test_elem_xI01_101:
  ([A1] ++ [A0] ++ [A1]) `elem` {{xI01}}.
Proof.
unfold xI01.
destruct_concat.
exists [A1].
exists ([A0] ++ [A1]).
assert ([A1] ++ [A0] ++ [A1] = [A1; A0; A1]). reflexivity.
exists H.
constructor.
- constructor.
  wreckit.
  apply notelem_emptyset.
- destruct_concat.
  exists [A0].
  exists [A1].
  exists eq_refl.
  constructor.
  + constructor.
  + constructor.
Qed.

Lemma test_notelem_xI01_101_false:
  ([A1] ++ [A0] ++ [A1]) `notelem` {{xI01}}  -> False.
Proof.
unfold not.
intros.
apply H.
apply test_elem_xI01_101.
Qed.

Local Ltac elemt :=
  match goal with
  | [ H : _ `elem` _ |- _ ] =>
    inversion H; clear H
  | [ |- context [_ `notelem` _ ] ] =>
    unfold not; intros
  end.

Lemma test_notleme_xI01_empty:
    [] `notelem` {{xI01}}.
Proof.
elemt.
elemt.
elemt.
subst.
listerine.
elemt.
Qed.

Lemma test_notelem_xI01_10:
  ([A1] ++ [A0]) `notelem` {{xI01}}.
Proof.
elemt.
elemt.
elemt.
elemt.
elemt.
elemt.
subst.
assert (p ++ [A0] ++ [A1] <> [A1] ++ [A0]).
listerine.
contradiction.
Qed.

Lemma test_notelem_xI01_1110:
  ([A1] ++ [A1] ++ [A1] ++ [A0]) `notelem` {{xI01}}.
Proof.
elemt.
elemt.
elemt.
elemt.
elemt.
subst.
listerine.
Qed.

Lemma test_notelem_x11star_0:
  [A0] `notelem` {{ x11star }}.
Proof.
elemt.
elemt.
elemt.
- subst.
  listerine.
  subst.
  elemt.
- elemt.
  + subst. elemt. subst. listerine.
  + subst. invs H1. invs H5. invs H9. listerine.
Qed.

Lemma test_notelem_starx1_0:
  [A0] `notelem` {{star x1}}.
Proof.
untie.
invs H.
- listerine.
  + apply H1.
    reflexivity.
  + inversion H2.
Qed.

Lemma test_notelem_starx1_10:
  [A1; A0] `notelem` {{star x1}}.
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

Lemma test_notelem_starx1_110:
  [A1; A1; A0] `notelem` {{star x1}}.
Proof.
untie.
invs H.
invs H2.
listerine.
apply test_notelem_starx1_10.
assumption.
Qed.

Lemma test_notelem_x11star_1110:
  ([A1] ++ [A1] ++ [A1] ++ [A0]) `notelem` {{x11star}}.
Proof.
untie.
invs H.
wreckit.
listerine; (try invs H1).
- apply test_notelem_starx1_110.
  assumption.
Qed.

Lemma test_elem_xI111I_1110:
    ([A1] ++ [A1] ++ [A1] ++ [A0]) `elem` {{xI111I}}.
Proof.
destruct_concat.
exists [].
exists ([A1] ++ [A1] ++ [A1] ++ [A0]).
exists eq_refl.
split.
- constructor.
  wreckit.
  untie.
- destruct_concat.
  exists [A1].
  exists ([A1] ++ [A1] ++ [A0]).
  exists eq_refl.
  split.
  + constructor.
  + destruct_concat.
    exists [A1].
    exists ([A1] ++ [A0]).
    exists eq_refl.
    split.
    * constructor.
    * destruct_concat.
      exists [A1].
      exists [A0].
      exists eq_refl.
      split.
      --- constructor.
      --- constructor.
          wreckit.
          untie.
Qed.

Theorem test_exampleR_1110_elem:
    ([A1] ++ [A1] ++ [A1] ++ [A0]) `elem` {{exampleR}}.
Proof.
constructor.
split.
- untie.
  invs H.
  wreckit.
  apply L.
  apply test_elem_xI111I_1110.
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
    apply test_notelem_xI01_1110.
    assumption.
  + untie.
    apply test_notelem_x11star_1110.
    assumption.
Qed.

Theorem test_exampleR_111_notelem:
    [A1; A1; A1] `notelem` {{exampleR}}.
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
destruct_concat.
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
