(*
This module replaces the standard library's List module.
It reexports Coq.Lists.List and Coq.Lists.List.ListNotations.
It includes extra theorems about lists.
*)

Require Export Coq.Lists.List.
Export Coq.Lists.List.ListNotations.
Require Import Coq.micromega.Lia.

Theorem length_zero_string_is_empty {A: Type} (xs: list A):
  length xs = 0 -> xs = [].
Proof.
  apply length_zero_iff_nil.
Qed.

Theorem length_zero_or_smaller_string_is_empty {A: Type} (xs: list A):
  length xs <= 0 -> xs = [].
Proof.
  intros.
  assert (length xs = 0).
  lia.
  rewrite length_zero_iff_nil in *.
  assumption.
Qed.

Theorem split_list {A: Type} (xs: list A) (n : nat):
  forall (ys zs: list A),
    length ys = n ->
    xs = ys ++ zs ->
    ys = firstn n xs /\
    zs = skipn n xs.
Proof.
  intros.
  set (ys' := firstn n xs).
  set (zs' := skipn n xs).
  subst.

  set (firstn_app (length ys) ys zs) as Hfirst.
  replace (length ys - length ys) with 0 in * by lia.
  replace (firstn 0 zs) with (nil : list A) in * by (symmetry; apply firstn_O).
  rewrite app_nil_r in Hfirst.
  replace (firstn (length ys) ys) with ys in Hfirst by (symmetry; apply firstn_all).

  set (skipn_app (length ys) ys zs) as Hlast.
  replace (length ys - length ys) with 0 in * by lia.
  replace (skipn (length ys) ys) with (nil: list A) in Hlast by (symmetry; apply skipn_all).
  rewrite app_nil_l in Hlast.
  replace (skipn 0 zs) with zs in Hlast by (apply skipn_O).

  split; auto.
Qed.

Lemma prefix_leq_length {A: Type} (xs ys zs: list A):
  xs = ys ++ zs -> length ys <= length xs.
Proof.
  intro H.
  assert (length ys + length zs = length xs).
  replace xs with (ys ++ zs) by assumption.
  symmetry.
  exact (app_length ys zs).
  lia.
Qed.