(*
This module shows off different possible definitions of concat_lang and how they are all equivalent
to the defintion we use in Language.v, namely `concat_lang`.
This also includes the tactic `destruct_concat_lang`, which is a useful replacement for the constructor tactic when concat_lang is in the goal.
*)

Require Import CoqStock.DubStep.
Require Import CoqStock.Invs.
Require Import CoqStock.List.
Require Import CoqStock.Listerine.
Require Import CoqStock.Untie.
Require Import CoqStock.WreckIt.

Require Import Brzozowski.Alphabet.
Require Import Brzozowski.Language.
Require Import Brzozowski.Regex.

(*
concat_lang_ex uses exists to define concat,
instead of forall as is done by `concat_lang`.
This is arguably closer to the mathematical definition of concat.

  $(P.Q) = \{ s | s = p.q; p \in P, q \in Q \}$.

*)
Inductive concat_lang_ex (P Q: lang): lang :=
  | mk_concat_ex: forall (s: str),
    (exists
      (p: str)
      (q: str)
      (pqs: p ++ q = s),
      p \in P /\
      q \in Q
    ) ->
    concat_lang_ex P Q s
  .

(*
concat_ex_equivalent shows how `concat_lang_ex` is equivalent to
the main definition of `concat_lang`.
*)
Theorem concat_ex_equivalent (P Q: lang):
  concat_lang_ex P Q {<->} concat_lang P Q.
Proof.
split.
- intros.
  destruct H.
  destruct H as [p [q [H [Hp Hq]]]].
  apply (mk_concat P Q p q s); assumption.
- intros.
  destruct H.
  constructor.
  exists p.
  exists q.
  exists H.
  split; assumption.
Qed.

(*
When concat is in the goal, it can be harder to apply the tactic,
since now some variables need to be provided to mk_concat.
The destruct_concat_lang tactic solves this by replacing the
concat_lang definition with the concat_lang_ex definition,
which can be easily deconstructed.
*)
Ltac destruct_concat_lang :=
  apply concat_ex_equivalent;
  fold denote_regex;
  apply mk_concat_ex.

(* example_destruct_concat_lang shows how the destruct_concat_lang can be used. *)
Example example_destruct_concat_lang:
  forall (p q: regex),
  [] \in {{p}} /\ [] \in {{q}} ->
  [] \in {{concat p q}}.
Proof.
intros.
destruct_concat_lang.
exists [].
exists [].
listerine.
exists eq_refl.
assumption.
Qed.