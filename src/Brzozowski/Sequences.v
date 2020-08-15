Require Import List.
Import ListNotations.
Require Import Setoid.

Require Import CoqStock.Invs.
Require Import CoqStock.Listerine.
Require Import CoqStock.Untie.
Require Import CoqStock.WreckIt.

Require Import Brzozowski.Alphabet.
Require Import Brzozowski.Regex.

(* A sequence is a list of characters or string. *)
Definition seq := (list alphabet).
(* A regular expression denotes a set of sequences. *)
Definition seqs := seq -> Prop.
Definition elem (ss: seqs) (s: seq): Prop := ss s.
Notation "p `elem` P" := (elem P p) (at level 80).
Notation "p `notelem` P" := (~ (elem P p)) (at level 80).

Definition seqs_if (s1 s2: seqs): Prop :=
  forall (s: seq),
  s `elem` s1 -> s `elem` s2.

Notation "s1 {->} s2" := (seqs_if s1 s2) (at level 80).

Definition seqs_iff (s1 s2: seqs): Prop :=
  forall (s: seq),
  s `elem` s1 <-> s `elem` s2.

Notation "s1 {<->} s2" := (seqs_iff s1 s2) (at level 80).

(* seqs_setoid makes it possible to use:
  - rewrite for proven seqs_iff theorems
  - reflexivity for seqs_iff relations where both sides are equal
  see Example SeqsSetoidRewriteReflexivity
*)
Section SeqsSetoid.

Theorem seqs_iff_refl : forall A:seqs, A {<->} A.
  Proof.
    split; auto.
  Qed.

Theorem seqs_iff_trans : forall A B C:seqs, (A {<->} B) -> (B {<->} C) -> (A {<->} C).
  Proof.
    intros.
    unfold "{<->}" in *.
    intros.
    specialize H with s.
    specialize H0 with s.
    unfold "`elem`" in *.
    apply iff_trans with (A := A s) (B := B s); assumption.
  Qed.

Theorem seqs_iff_sym : forall A B:seqs, (A {<->} B) -> (B {<->} A).
  Proof.
    intros.
    unfold "{<->}" in *.
    intros.
    specialize H with s.
    unfold "`elem`" in *.
    apply iff_sym.
    assumption.
  Qed.

Add Parametric Relation: seqs seqs_iff
  reflexivity proved by seqs_iff_refl
  symmetry proved by seqs_iff_sym
  transitivity proved by seqs_iff_trans as seqs_setoid.

End SeqsSetoid.

Existing Instance seqs_setoid.

(* Concatenation*. $(P.Q) = \{ s | s = p.q; p \in P, q \in Q \}$. *)
Inductive concat_seqs (P Q: seqs): seqs :=
  | mk_concat: forall (s: seq),
    (exists
      (p: seq)
      (q: seq)
      (pqs: p ++ q = s),
      p `elem` P /\
      q `elem` Q
    ) ->
    concat_seqs P Q s
  .

(*
   concat_seqs_morph allows rewrite to work inside concat_seqs parameters
*)
Add Parametric Morphism: concat_seqs
  with signature seqs_iff ==> seqs_iff ==> seqs_iff as concat_seqs_morph.
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

(*
    *Star*. $P^{*} = \cup_{0}^{\infty} P^n$ , where $P^2 = P.P$, etc.
    and $P^0 = \lambda$, the set consisting of the sequence of zero length.
*)
Inductive star_seqs (R: seqs): seqs :=
  | mk_star_zero : forall (s: seq),
    s = [] -> star_seqs R s
  | mk_star_more : forall (s: seq),
    s `elem` (concat_seqs R (star_seqs R)) ->
    star_seqs R s
  .

(*
   star_seqs_morph allows rewrite to work inside star_seqs parameters
*)
Add Parametric Morphism: star_seqs
  with signature seqs_iff ==> seqs_iff as star_seqs_morph.
Proof.
(* TODO: Help Wanted *)
Abort.

(*
    *Boolean function*. We shall denote any Boolean function of $P$ and $Q$ by $f(P, Q)$.
    Of course, all the laws of Boolean algebra apply.
    `nor` is used to emulate `f`, since nor can be used to emulate all boolean functions.
*)
Inductive nor_seqs (P Q: seqs): seqs :=
  | mk_nor : forall s,
    s `notelem` P /\ s `notelem` Q ->
    nor_seqs P Q s
  .

(*
   nor_seqs_morph allows rewrite to work inside nor_seqs parameters
   see Example NorSeqsMorphSetoidRewrite
*)
Add Parametric Morphism: nor_seqs
  with signature seqs_iff ==> seqs_iff ==> seqs_iff as nor_seqs_morph.
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

Existing Instance nor_seqs_morph_Proper.

Inductive emptyset_seqs: seqs :=
  .
  (*
  This is equivalent to:
  ```
  | mk_emptyset: forall (s: seq),
    False ->
    emptyset_seqs s
  ```
  *)

Inductive lambda_seqs: seqs :=
  | mk_lambda: lambda_seqs []
  .
  (*
  This is equivalent to:
  ```
  | mk_lambda:
    forall (s: seq),
    s = [] ->
    lambda_seqs s
  ```
  *)

Inductive symbol_seqs (a: alphabet): seqs :=
  | mk_symbol: symbol_seqs a [a].
  (*
  This is equivalent to:
  ```
  | mk_symbol:
    forall (s: seq),
    s = [a] ->
    symbol_seqs a s
  ```
  *)

(*
  Here we use a mix of Fixpoint and Inductive predicates to define the denotation of regular expressions.
*)
Reserved Notation "{{ r }}" (r at level 60, no associativity).
Fixpoint denote_regex (r: regex): seqs :=
  match r with
  | emptyset => emptyset_seqs
  | lambda => lambda_seqs
  | symbol y => symbol_seqs y
  | concat r1 r2 => concat_seqs {{r1}} {{r2}}
  | star r1 => star_seqs {{r1}}
  | nor r1 r2 => nor_seqs {{r1}} {{r2}}
  end
where "{{ r }}" := (denote_regex r).

Theorem notelem_emptyset: forall (s: seq),
  s `notelem` emptyset_seqs.
Proof.
intros.
untie.
Qed.

Lemma denotation_emptyset_is_decidable (s: seq):
  s `elem` {{ emptyset }} \/ s `notelem` {{ emptyset }}.
Proof.
right.
apply notelem_emptyset.
Qed.

Lemma denotation_lambda_is_decidable (s: seq):
  s `elem` {{ lambda }} \/ s `notelem` {{ lambda }}.
Proof.
destruct s.
- left. constructor.
- right. untie. invs H.
Qed.

Lemma denotation_symbol_is_decidable (s: seq) (a: alphabet):
  s `elem` {{ symbol a }} \/ s `notelem` {{ symbol a }}.
Proof.
destruct s.
- right. untie. invs H.
- destruct a, a0.
  + destruct s.
    * left.
      constructor.
    * right.
      untie.
      invs H.
  + right.
    untie.
    invs H.
  + right.
    untie.
    invs H.
  + destruct s.
    * left.
      constructor.
    * right.
      untie.
      invs H.
Qed.

Lemma denotation_nor_is_decidable (p q: regex) (s: seq):
  s `elem` {{ p }} \/ s `notelem` {{ p }} ->
  s `elem` {{ q }} \/ s `notelem` {{ q }} ->
  s `elem` {{ nor p q }} \/ s `notelem` {{ nor p q }}.
Proof.
simpl.
intros.
wreckit.
- right.
  untie.
  invs H.
  wreckit.
  contradiction.
- right.
  untie.
  invs H.
  wreckit.
  contradiction.
- right.
  untie.
  invs H.
  wreckit.
  contradiction.
- left.
  constructor.
  wreckit.
  * assumption.
  * assumption.
Qed.

Lemma denotation_concat_is_decidable_for_empty_string (p q: regex):
  [] `elem` {{ p }} \/ [] `notelem` {{ p }} ->
  [] `elem` {{ q }} \/ [] `notelem` {{ q }} ->
  [] `elem` {{ concat p q }} \/ [] `notelem` {{ concat p q }}.
Proof.
intros.
wreckit.
- left.
  constructor.
  exists [].
  exists [].
  exists eq_refl.
  wreckit; assumption.
- right.
  untie.
  invs H.
  wreckit.
  listerine.
  contradiction.
- right.
  untie.
  invs H.
  wreckit.
  listerine.
  contradiction.
- right.
  untie.
  invs H.
  wreckit.
  listerine.
  contradiction.
Qed.

Lemma denotation_star_is_decidable_for_empty_string (r: regex):
  [] `elem` {{ star r }} \/ [] `notelem` {{ star r }}.
Proof.
left.
constructor.
reflexivity.
Qed.

Lemma denotation_is_decidable_on_empty_string (r: regex):
  [] `elem` {{ r }} \/ [] `notelem` {{ r }}.
Proof.
intros.
induction r.
- apply denotation_emptyset_is_decidable.
- apply denotation_lambda_is_decidable.
- apply denotation_symbol_is_decidable.
- apply denotation_concat_is_decidable_for_empty_string.
  + assumption.
  + assumption.
- apply denotation_star_is_decidable_for_empty_string.
- apply denotation_nor_is_decidable.
  + assumption.
  + assumption.
Qed.

Theorem denotation_is_decidable (r: regex) (s: seq):
  s `elem` {{ r }} \/ s `notelem` {{ r }}.
Proof.
induction s.
- apply denotation_is_decidable_on_empty_string.
- induction r.
  + apply denotation_emptyset_is_decidable.
  + apply denotation_lambda_is_decidable.
  + apply denotation_symbol_is_decidable.
  + wreckit.
    * invs B.
      wreckit.
(* TODO: Help Wanted *)
Abort.

Definition not_seqs (R: seqs) : seqs :=
  nor_seqs R R.

Theorem not_not_regex_is_regex:
  forall (r: regex) (s: seq),
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

Theorem not_seqs_not_seqs_is_seqs: forall (r: regex),
  not_seqs (not_seqs {{r}})
  {<->}
  {{r}}.
Proof.
intros.
split.
- assert (s `elem` {{ r }} \/ s `notelem` {{ r }}).
  admit. (* TODO: apply denotation_is_decidable *)
  intros.
  wreckit.
  + assumption.
  + invs H0.
    wreckit.
    unfold not in L.
    exfalso.
    apply L.
    constructor.
    wreckit.
    assumption.
- assert (s `elem` {{ r }} \/ s `notelem` {{ r }}).
  admit. (* TODO: apply denotation_is_decidable *)
  intros.
  constructor.
  wreckit.
  + unfold not.
    intros.
    invs H.
    wreckit.
    contradiction.
  + contradiction.
Abort.

Theorem concat_seqs_emptyset_l_is_emptyset: forall (r: seqs),
  concat_seqs emptyset_seqs r
  {<->}
  emptyset_seqs.
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
  The implementation of Setoid for seqs allows the use of rewrite and reflexivity.
*)
Example SeqsSetoidRewriteReflexivity: forall (r: seqs),
  concat_seqs emptyset_seqs r
  {<->}
  emptyset_seqs.
Proof.
intros.
rewrite concat_seqs_emptyset_l_is_emptyset.
reflexivity.
Qed.

(*
  The implementation of not_seqs_morph allows the use of rewrite inside nor_seqs parameters.
*)
Example NorSeqsMorphSetoidRewrite: forall (r s: seqs),
  nor_seqs (concat_seqs emptyset_seqs r) s
  {<->}
  nor_seqs emptyset_seqs s.
Proof.
intros.
rewrite concat_seqs_emptyset_l_is_emptyset.
reflexivity.
Qed.

Theorem concat_seqs_emptyset_l: forall (r: seqs) (s: seq),
  s `notelem` concat_seqs emptyset_seqs r.
Proof.
intros.
untie.
invs H.
wreckit.
invs L.
Qed.

Theorem concat_seqs_emptyset_r_is_emptyset: forall (r: seqs),
  concat_seqs r emptyset_seqs
  {<->}
  emptyset_seqs.
Proof.
split.
- intros.
  invs H.
  wreckit.
  invs R.
- intros.
  invs H.
Qed.

Theorem concat_seqs_emptyset_r: forall (r: seqs) (s: seq),
  s `notelem` concat_seqs r emptyset_seqs.
Proof.
intros.
untie.
invs H.
wreckit.
invs R.
Qed.

Theorem concat_seqs_lambda_l_is_l: forall (r: seqs),
  concat_seqs lambda_seqs r
  {<->}
  r.
Proof.
split.
- intros.
  invs H.
  wreckit.
  subst.
  inversion_clear L.
  cbn.
  assumption.
- intros.
  constructor.
  exists [].
  exists s.
  exists eq_refl.
  split.
  + constructor.
  + assumption.
Qed.

Theorem concat_seqs_lambda_r_is_r: forall (r: seqs),
  concat_seqs r lambda_seqs
  {<->}
  r.
Proof.
split.
- intros.
  invs H.
  wreckit.
  subst.
  inversion_clear R.
  listerine.
  assumption.
- intros.
  constructor.
  exists s.
  exists [].
  assert (s ++ [] = s). listerine. reflexivity.
  exists H0.
  split.
  + assumption.
  + constructor.
Qed.