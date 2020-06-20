Require Import List.
Import ListNotations.

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
  (* | mk_emptyset: forall (s: seq),
    False ->
    emptyset_seqs s *)
  .

Inductive lambda_seqs: seqs :=
  | mk_lambda: forall (s: seq),
    s = [] ->
    lambda_seqs s
  .

Inductive symbol_seqs (a: alphabet): seqs :=
  | mk_symbol: forall (s: seq),
    s = [a] ->
    symbol_seqs a s
  .

(* Here we use a mix of Fixpoint and Inductive predicates to define the denotation of regular expressions.
   This works, but it would be nicer to define it purely as an Inductive predicate.
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