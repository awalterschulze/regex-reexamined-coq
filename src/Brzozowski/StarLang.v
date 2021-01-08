Require Import CoqStock.List.
Require Import CoqStock.Listerine.

Require Import Brzozowski.Alphabet.
Require Import Brzozowski.ConcatLang.
Require Import Brzozowski.Language.

(*
This module shows off different possible definitions of star_lang and how they are all equivalent
to the defintion we use in Language.v, namely `star_lang`.
The 4 varieties include switching these options on and off:

  - allowing empty prefixes in `mk_star_more`
  - using an existence statement

Where the definition of the `star_lang` we use in Language.v:

  - does not allow empty prefixes in `mk_star_more`
  - prefers using forall over existence

The reason for preferring forall over existence in this case is that,
the definitions that use an existence statement (e.g. the existence statement
that is part of `concat_lang` and `concat_ex_prefix_not_empty_lang`) require you to
prove your own induction principle, because Coq is not smart enough to figure it
out by itself. The definitions that allow empty prefixes make induction more
difficult if the regular expression matches the empty string.

Therefore, the easiest definition is the one that does not have an existence
statement and that does not allow empty prefixes, so we will use that as our main definition.

Below, we define all these definitions and prove their equivalence. As part of
the proofs, we prove a stronger induction principle for the two definitions that
use an existence statement.

For reference here follows our main definition of `star_lang`

Inductive star_lang (R: lang): lang :=
  | mk_star_zero : star_lang R []
  | mk_star_more : forall (s p q: str),
      p ++ q = s ->
      p <> [] ->
      p \in R ->
      q \in (star_lang R) ->
      s \in star_lang R.

The other definitions are:
  - star_lang_ex_empty
  - star_lang_empty
  - star_lang_ex
*)

(*
  star_lang_ex_empty is the original definition of star_lang:
  - Uses existence
  - Allows empty prefixes in mk_star_more
  It contains more recursion, since it allows R to match the empty string.
  The definition allowing empty prefixes and using the existence statement is hidden in `concat_lang_ex`.
  This is the most difficult definition to use in Coq, but arguably the closest to the mathematical definition:
    *Star*. $P^{*} = \cup_{0}^{\infty} P^n$ , where $P^2 = P.P$, etc.
    and $P^0 = \lambda$, the set consisting of the string of zero length.
*)
Inductive star_lang_ex_empty (R: lang): lang :=
  | mk_star_zero_ex_empty : forall (s: str),
    s = [] -> star_lang_ex_empty R s
  | mk_star_more_ex_empty : forall (s: str),
    s \in (concat_lang_ex R (star_lang_ex_empty R)) ->
    star_lang_ex_empty R s.

(* star_lang_empty is a middle ground:
  - Does not use existence
  - Allows empty prefixes
*)
Inductive star_lang_empty (R: lang): lang :=
  | mk_star_zero_empty : forall (s: str),
      s = [] -> star_lang_empty R s
  | mk_star_more_empty : forall (s p q: str),
      p ++ q = s ->
      p \in R ->
      q \in (star_lang_empty R) ->
      s \in star_lang_empty R.

(* concat_ex_prefix_not_empty_lang is a helper for star_lang_ex
   It uses existence to define concat and
   the prefix language is not allowed to match the empty string
*)
Inductive concat_ex_prefix_not_empty_lang (P Q: lang): lang :=
  | mk_concat_prefix_is_not_empty: forall (s: str),
    (exists
      (p: str)
      (a: alphabet)
      (q: str)
      (pqs: (a :: p) ++ q = s),
      (a :: p) \in P /\
      q \in Q
    ) ->
    concat_ex_prefix_not_empty_lang P Q s
.

(* star_lang_ex is another middle ground:
  - Uses existence that is hidden in concat_ex_prefix_not_empty_lang
  - Does not allow empty prefixes in mk_star_more, which is also hidden in concat_ex_prefix_not_empty_lang
*)
Inductive star_lang_ex (R: lang): lang :=
  | mk_star_zero_ex : forall (s: str),
      s = [] -> star_lang_ex R s
  | mk_star_more_ex : forall (s: str),
      s \in (concat_ex_prefix_not_empty_lang R (star_lang_ex R)) ->
      star_lang_ex R s.

(* The Propositions below shows how each of the 4 definitions are equivalent to star_lang. *)

Proposition star_lang_empty_equivalent (R: lang):
  star_lang R {<->} star_lang_empty R.
Proof.
  split.
  - intro Hmatch.
    induction Hmatch.
    + subst. now constructor.
    + eapply (mk_star_more_empty R s); try (exact H); try assumption.
  - intro Hmatch.
    induction Hmatch as [| s p q Hp_match Hq_match IH].
    + subst. now constructor.
    + destruct p.
      * (* If the prefix is empty, the induction hypothesis is exactly what we want. *)
        subst.
        cbn.
        assumption.
      * (* Otherwise, we only have to apply the constructor and use the IH. *)
        apply (mk_star_more R s (a :: p) q); try assumption.
        trivial.
        listerine.
Qed.

Local Proposition star_lang_ex_ind_better:
 forall (R : lang) (P : str -> Prop),
   (* base case *)
   P [] ->
   (* induction step *)
   (forall s: str, (exists (p q: str),
                  p ++ q = s /\
                  p <> [] /\
                  p \in R /\
                  q \in star_lang_ex R /\
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

Proposition star_lang_ex_equivalent (R: lang):
    star_lang R {<->} star_lang_ex R.
Proof.
  split.
  - intro Hmatch.
    induction Hmatch.
    + subst. now constructor.
    + eapply (mk_star_more_ex R s); try (exact H).
      constructor.
      destruct p.
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

Local Proposition star_lang_ex_empty_ind_better:
 forall (R : lang) (P : str -> Prop),
   (* base case *)
   P [] ->
   (* induction step *)
   (forall s: str, (exists (p q: str),
                  p ++ q = s /\
                  p \in R /\
                  q \in star_lang_ex_empty R /\
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

Proposition star_lang_ex_empty_equivalent (R: lang):
    star_lang R {<->} star_lang_ex_empty R.
Proof.
  split.
  - intro Hmatch.
    induction Hmatch.
    + subst. now constructor.
    + eapply (mk_star_more_ex_empty R s); try (exact H).
      constructor.
      destruct p.
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
      destruct p.
      * subst. cbn. assumption.
      * constructor 2 with (p := (a :: p)) (q := q); try assumption.
        listerine.
    + assumption.
Qed.
