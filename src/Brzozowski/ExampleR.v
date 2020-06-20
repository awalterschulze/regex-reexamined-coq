Require Import List.
Import ListNotations.

Require Import CoqStock.WreckIt.
Require Import CoqStock.Listerine.

Require Import Brzozowski.Alphabet.
Require Import Brzozowski.Boolean.
Require Import Brzozowski.Regex.
Require Import Brzozowski.Sequences.

(*
The introduction of arbitrary Boolean functions enriches the language of regular expressions. 
For example, suppose we desire to represent the set of all sequences having three consecutive 1's 
but not those ending in 01 or consisting of 1's only. 
The desired expression is easily seen to be:

R = (I.1.1.1.I)\&(I.0.1+1.1^{*})'.
*)
Definition x1 := symbol a1.
Definition x0 := symbol a0.
Definition xI111I := concat I (concat x1 (concat x1 (concat x1 I))).
Definition xI01 := concat I (concat x0 x1).
Definition x11star := concat x1 (star x1).
Definition exampleR := and xI111I (complement (or xI01 x11star)).

Lemma test_elem_xI01_101:
  ([a1] ++ [a0] ++ [a1]) `elem` {{xI01}}.
Proof.
unfold xI01.
constructor.
exists [a1].
exists ([a0] ++ [a1]).
assert ([a1] ++ [a0] ++ [a1] = [a1; a0; a1]). reflexivity.
exists H.
constructor.
- constructor.
  wreckit.
  apply notelem_emptyset.
- constructor.
  exists [a0].
  exists [a1].
  exists eq_refl.
  constructor.
  + constructor. reflexivity.
  + constructor. reflexivity.
Qed.

Lemma test_notelem_xI01_101_false:
  ([a1] ++ [a0] ++ [a1]) `notelem` {{xI01}}  -> False.
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
wreckit.
elemt.
subst.
cbn in x3.
apply app_eq_nil in x3.
wreckit.
assert ([a0; a1] <> []).
discriminate.
subst.
elemt.
elemt.
subst.
contradiction.
Qed.

Lemma test_notelem_xI01_10:
  ([a1] ++ [a0]) `notelem` {{xI01}}.
Proof.
elemt.
elemt.
wreckit.
elemt.
wreckit.
elemt.
elemt.
elemt.
wreckit.
subst.
assert (x ++ [a0] ++ [a1] <> [a1] ++ [a0]).
listerine.
contradiction.
Qed.

Lemma test_notelem_xI01_1110:
  ([a1] ++ [a1] ++ [a1] ++ [a0]) `notelem` {{xI01}}.
Proof.
elemt.
elemt.
wreckit.
elemt.
wreckit.
elemt.
elemt.
subst.
cbn in x3.
listerine.
Qed.

Lemma test_notelem_x11star_0: 
  [a0] `notelem` {{ x11star }}.
Proof.
elemt.
elemt.
wreckit.
elemt.
- subst.
  listerine.
  subst.
  elemt.
  discriminate.
- elemt.
  wreckit.
  subst.
  inversion L.
  inversion L0.
  subst.
  listerine.
Qed.

Lemma test_notelem_x11star_1110: 
    ([a1] ++ [a1] ++ [a1] ++ [a0]) `notelem` {{x11star}}.
Proof.
(* TODO: Good First Issue
   first merge listerine
*)
Abort.

Lemma test_elem_xI111I_1110: 
    ([a1] ++ [a1] ++ [a1] ++ [a0]) `elem` {{xI111I}}.
Proof.
(* TODO: Good First Issue
   first merge listerine
*)
Abort.

Theorem test_exampleR_1110_elem: 
    ([a1] ++ [a1] ++ [a1] ++ [a0]) `elem` {{exampleR}}.
Proof.
(* TODO: Good First Issue
   first merge listerine
*)
Abort.


Theorem test_exampleR_111_notelem: 
    [a1; a1; a1] `notelem` {{exampleR}}.
Proof.
(* TODO: Good First Issue
   first merge listerine
*)
Abort.
