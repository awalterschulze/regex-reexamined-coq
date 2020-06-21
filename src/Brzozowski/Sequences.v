Require Import List.
Import ListNotations.

Require Import CoqStock.Invs.
Require Import CoqStock.Listerine.
Require Import CoqStock.WreckIt.

Require Import Brzozowski.Alphabet.
Require Import Brzozowski.Regex.

(*  A regular expression denotes a set of sequences. *)
Definition seq := (list alphabet).
Definition seqs := seq -> Prop.
Definition elem (ss: seqs) (s: seq): Prop := ss s.
Notation "p `elem` P" := (elem P p) (at level 80).
Notation "p `notelem` P" := (~ (elem P p)) (at level 80).

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
    *Boolean function*. We shall denote any Boolean function of $P$ and $Q$ by $f(P, Q)$. 
    Of course, all the laws of Boolean algebra apply.
    `nor` is used to emulate `f`, since nor can be used to emulate all boolean functions.
*)
Inductive nor_seqs (P Q: seqs): seqs :=
  | mk_nor : forall s,
    s `notelem` P /\ s `notelem` Q ->
    nor_seqs P Q s
  .

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

Definition seqs_impl (s1 s2: seqs): Prop :=
  forall (s: seq),
  s `elem` s1 -> s `elem` s2.

Notation "s1 {->} s2" := (seqs_impl s1 s2) (at level 80).

Definition seqs_eq (s1 s2: seqs): Prop :=
  forall (s: seq),
  s `elem` s1 <-> s `elem` s2.

Notation "s1 {<->} s2" := (seqs_eq s1 s2) (at level 80).

Theorem concat_emptyset_l: forall (r: seqs),
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

Theorem concat_emptyset_r: forall (r: seqs),
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

Theorem concat_lambda_l: forall (r: seqs),
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

Theorem concat_lambda_r: forall (r: seqs),
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