Require Import Coq.Classes.Morphisms.
Require Import Coq.setoid_ring.Ring.
Require Import Coq.setoid_ring.Ring_theory.
Require Import Coq.Setoids.Setoid.

Require Import CoqStock.DubStep.
Require Import CoqStock.Invs.
Require Import CoqStock.List.
Require Import CoqStock.Listerine.
Require Import CoqStock.Untie.
Require Import CoqStock.WreckIt.

Require Import Brzozowski.Alphabet.
Require Import Brzozowski.Language.
Require Import Brzozowski.LogicOp.
Require Import Brzozowski.Regex.
Require Import Brzozowski.Setoid.
Require Import Brzozowski.Simplify.

(* TODOs in this file
   Some are theorems that need to be proven or simply applied from Simplify.v
   Other parts are uncommentable once the theorems are proven.
*)

Theorem or_lang_emptyset_l:
  forall n : lang, or_lang emptyset_lang n {<->} n.
(* TODO: Good First Issue *)
Abort.

Theorem or_lang_comm:
  forall n m : lang, or_lang n m {<->} or_lang m n.
(* TODO: Good First Issue *)
Abort.

Theorem or_lang_assoc:
  forall n m p : lang, or_lang n (or_lang m p) {<->} or_lang (or_lang n m) p.
(* TODO: Good First Issue *)
Abort.

Theorem and_lang_neg_emptyset_l:
  forall n : lang, and_lang (neg_lang emptyset_lang) n {<->} n.
(* TODO: Good First Issue *)
Abort.

Theorem and_lang_emptyset_l:
  forall n : lang, and_lang emptyset_lang n {<->} emptyset_lang.
(* TODO: Good First Issue *)
Abort.

Theorem and_lang_comm:
  forall n m : lang, and_lang n m {<->} and_lang m n.
(* TODO: Good First Issue *)
Abort.

Theorem and_lang_assoc:
  forall n m p : lang,
  and_lang n (and_lang m p) {<->} and_lang (and_lang n m) p.
(* TODO: Good First Issue *)
Abort.

Theorem and_lang_or_lang_distrib_l:
  forall n m p : lang,
  and_lang (or_lang n m) p {<->} or_lang (and_lang n p) (and_lang m p).
(* TODO: Good First Issue *)
Abort.

Lemma lang_semi_ring:
  semi_ring_theory emptyset_lang (neg_lang emptyset_lang) or_lang and_lang (lang_iff).
Proof.
constructor.
(* TODO: Good First Issue *)
(* - exact or_lang_emptyset_l.
- exact or_lang_comm.
- exact or_lang_assoc.
- exact and_lang_neg_emptyset_l.
- exact and_lang_emptyset_l.
- exact and_lang_comm.
- exact and_lang_assoc.
- exact and_lang_or_lang_distrib_l. *)
Abort.

Theorem and_lang_morph_Proper:
  Proper (lang_iff ==> lang_iff ==> lang_iff) and_lang.
(* TODO: Delete, there is one already in LogicOp.v *)
Abort.

Lemma Eq_lang_s_ext: sring_eq_ext or_lang and_lang lang_iff.
Proof.
constructor.
- exact or_lang_morph_Proper.
- exact and_lang_morph_Proper.
Qed.

(* TODO: Good First Issue *)
(* Add Ring lang_semi_ring: lang_semi_ring
  (abstract, setoid lang_setoid Eq_lang_s_ext). *)

Lemma or_lang_diag: forall b: lang,
  or_lang b b {<->} b.
(* TODO: Good First Issue *)
Abort.

Lemma or_lang_false_r: forall b:lang,
  or_lang b emptyset_lang {<->} b.
(* TODO: Good First Issue *)
Abort.

Lemma or_lang_false_l: forall b:lang,
  or_lang emptyset_lang b {<->} b.
(* TODO: Good First Issue *)
Abort.

Lemma or_lang_true_r: forall b:lang,
  or_lang b (neg_lang emptyset_lang) {<->} neg_lang emptyset_lang.
(* TODO: Good First Issue *)
Abort.

Lemma or_lang_true_l: forall b:lang,
  or_lang (neg_lang emptyset_lang) b {<->} neg_lang emptyset_lang.
(* TODO: Good First Issue *)
Abort.

(*
truthy is a tactic that repeatedly applies:
  - the semi ring with or_lang tactic
  - removes duplicates in or_lang expressions
  - removes all emptyset values in or_lang expressions
  - returns neg (emptyset), if a neg (emptyset) is found in an or expression
*)
Ltac truthy := repeat
  ( ring
  (* TODO: Good First Issue *)
  (* || rewrite or_lang_diag
  || rewrite or_lang_false_r
  || rewrite or_lang_false_l
  || rewrite or_lang_true_r
  || rewrite or_lang_true_l *)
  ).

Example example_or_lang_commutativity: forall (a b: lang),
  or_lang a b {<->} or_lang b a.
Proof.
intros.
(* TODO: Good First Issue *)
(* ring. *)
Abort.

Example example_or_lang_idempotency_1: forall (a b: lang),
  or_lang a (or_lang a b) {<->} or_lang a b.
Proof.
intros.
(* TODO: Help Wanted *)
Abort.

Example example_or_lang_idempotency_2: forall (a b: lang),
  or_lang (or_lang a b) a {<->} or_lang a b.
Proof.
intros.
(* TODO: Help Wanted *)
Abort.

Example example_or_associativity_1: forall (a b c: lang),
  or_lang (or_lang a b) c {<->} or_lang a (or_lang b c).
Proof.
intros.
(* TODO: Good First Issue *)
(* ring. *)
Abort.

Example example_or_associativity_2: forall (a b c: lang),
  or_lang a (or_lang b c) {<->} or_lang b (or_lang a c).
Proof.
intros.
(* TODO: Good First Issue *)
(* ring *)
Abort.

Example example_or_3: forall (a b c: lang),
  or_lang a (or_lang b (or_lang a c)) {<->} or_lang a (or_lang b c).
Proof.
intros.
(* TODO: Help Wanted *)
Abort.

Example example_or_4: forall (a b c d: lang),
  or_lang a (or_lang b (or_lang c d)) {<->}
  or_lang a (or_lang d (or_lang b (or_lang c d ))).
Proof.
intros.
(* TODO: Help Wanted *)
Abort.

Example example_or_false: forall (a: lang),
  or_lang a emptyset_lang {<->} a.
Proof.
intros.
(* TODO: Good First Issue *)
(* ring. *)
Abort.

Example example_or_true: forall (a: lang),
  or_lang (neg_lang emptyset_lang) a {<->} neg_lang emptyset_lang.
Proof.
intros.
(* TODO: Good First Issue *)
(* truthy. *)
Abort.