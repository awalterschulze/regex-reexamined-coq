Require Import List.
Import ListNotations.

Require Import CoqStock.WreckIt.
Require Import CoqStock.Listerine.

Require Import Brzozowski.Alphabet.
Require Import Brzozowski.Regex.
Require Import Brzozowski.Sequences.

(* the *intersection* $P \& Q$, *)
Theorem elem_intersection: forall (p q: regex) (s: str),
  s `elem` {{p}} ->
  s `elem` {{q}} ->
  s `elem` {{and p q}}.
Proof.
intros.
cbn.
constructor.
constructor.
- unfold not. intros.
  inversion H1. subst.
  inversion H2.
  contradiction.
- unfold not. intros.
  inversion H1. subst.
  inversion H2.
  contradiction.
Qed.

Theorem elem_union_l: forall (p q: regex) (s: str),
  s `elem` {{p}} ->
  s `elem` {{or p q}}.
Proof.
intros.
cbn.
constructor.
constructor.
- unfold not.
  intros.
  inversion H0.
  subst.
  inversion H1.
  subst.
  contradiction.
- unfold not.
  intros.
  inversion H0.
  subst.
  inversion H1.
  subst.
  contradiction.
Qed.

Theorem elem_union_r: forall (p q: regex) (s: str),
  s `elem` {{q}} ->
  s `elem` {{or p q}}.
Proof.
(* TODO: Good First Issue *)
Abort.

Theorem elem_complement: forall (p: regex) (s: str),
  s `notelem` {{p}} ->
  s `elem` {{complement p}}.
Proof.
unfold not.
intros.
cbn.
constructor.
wreckit.
unfold not.
assumption.
Qed.

Theorem notelem_complement: forall (p: regex) (s: str),
  s `elem` {{p}} ->
  s `notelem` {{complement p}}.
Proof.
unfold not.
intros.
cbn in H0.
inversion H0. subst.
inversion H1.
contradiction.
Qed.

Theorem elem_complement_emptyset: forall (s: str),
  s `elem` {{complement emptyset}}.
Proof.
intros.
cbn.
constructor.
wreckit.
unfold not.
unfold "`elem`".
intros.
inversion H.
Qed.

Theorem notelem_emptyset: forall (s: str),
  s `notelem` {{emptyset}}.
Proof.
intros.
unfold not.
cbn.
intros.
inversion H.
Qed.

Theorem notelem_intersection_l: forall (p q: regex) (s: str),
  s `notelem` {{p}} ->
  s `notelem` {{and p q}}.
Proof.
unfold not.
intros.
cbn in H0.
inversion H0.
inversion H1.
subst.
unfold not in H3.
apply H3.
constructor.
wreckit.
unfold not.
assumption.
Qed.

Theorem notelem_intersection_r: forall (p q: regex) (s: str),
    s `notelem` {{q}} ->
    s `notelem` {{and p q}}.
Proof.
unfold not.
intros.
cbn in H0.
inversion H0.
subst.
inversion H1.
clear H1.
unfold not in H2.
unfold not in H3.
apply H3.
constructor.
wreckit.
unfold not.
assumption.
Qed.

Theorem notelem_union: forall (p q: regex) (s: str),
    s `notelem` {{p}} ->
    s `notelem` {{q}}->
    s `notelem` {{or p q}}.
Proof.
unfold not.
intros.
cbn in H1.
inversion H1.
subst.
inversion H2.
unfold not in H3.
apply H3.
constructor.
unfold not.
constructor; assumption.
Qed.

Lemma elem_or_notelem_symbol: forall (a: alphabet) (s: str),
  s `elem` {{symbol a}} \/ s `notelem` {{symbol a}}.
Proof.
induction s.
- right.
  unfold not.
  intros.
  inversion H.
- induction s.
  + induction a, a0.
    * left. constructor.
    * right. unfold not. intros. inversion H.
    * right. unfold not. intros. inversion H.
    * left. constructor.
  + right.
    unfold not.
    intros.
    inversion H.
Qed.   

Lemma elem_or_notelem_emptyset: forall (s: str),
  s `elem` {{emptyset}} \/ s `notelem` {{emptyset}}.
Proof.
intros.
right.
unfold not.
intros.
inversion H.
Qed.

Lemma elem_or_notelem_lambda: forall (s: str),
  s `elem` {{lambda}} \/ s `notelem` {{lambda}}.
Proof.
intros.
induction s.
- left. constructor.
- right. unfold not. intros. inversion H.
Qed.

Lemma elem_or_notelem_concat: forall (r1 r2: regex) (s: str),
  s `elem` {{concat r1 r2}} \/ s `notelem` {{concat r1 r2}}.
Proof.
(* TODO: Help Wanted *)
Abort.

Lemma elem_or_notelem_star: forall (r: regex) (s: str),
  s `elem` {{star r}} \/ s `notelem` {{star r}}.
Proof.
(* TODO: Help Wanted *)
Abort.

Lemma elem_or_notelem_nor: forall (r1 r2: regex) (s: str),
  s `elem` {{nor r1 r2}} \/ s `notelem` {{nor r1 r2}}.
Proof.
(* TODO: Help Wanted *)
Abort.

Theorem elem_or_notelem : forall (r: regex) (s: str),
    s `elem` {{r}} \/ s `notelem` {{r}}.
Proof.
induction r.
- apply elem_or_notelem_emptyset.
- apply elem_or_notelem_lambda.
- apply elem_or_notelem_symbol.
(*
- apply elem_or_notelem_concat.
- apply elem_or_notelem_star.
- apply elem_or_notelem_nor.
*)
(* TODO: Help Wanted *)
Abort.