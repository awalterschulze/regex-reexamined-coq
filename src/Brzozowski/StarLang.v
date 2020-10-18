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

Require Import Language.

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
