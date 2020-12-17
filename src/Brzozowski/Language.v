Require Import CoqStock.DubStep.
Require Import CoqStock.Invs.
Require Import CoqStock.List.
Require Import CoqStock.Listerine.
Require Import CoqStock.Untie.
Require Import CoqStock.WreckIt.

Require Import Brzozowski.Alphabet.
Require Import Brzozowski.Regex.

(* A string is a list of characters. *)
Definition str := list alphabet.
(* A regular expression denotes a set of strings called a _language_. *)
Definition lang := str -> Prop.
Definition elem (l: lang) (s: str): Prop := l s.
Notation "p `elem` P" := (elem P p) (at level 80).
Notation "p `notelem` P" := (~ (elem P p)) (at level 80).

Definition lang_if (s1 s2: lang): Prop :=
  forall (s: str),
  s `elem` s1 -> s `elem` s2.

Notation "s1 {->} s2" := (lang_if s1 s2) (at level 80).

Definition lang_iff (s1 s2: lang): Prop :=
  forall (s: str),
  s `elem` s1 <-> s `elem` s2.

Notation "s1 {<->} s2" := (lang_iff s1 s2) (at level 80).

Inductive emptyset_lang: lang :=
  .
  (*
  This is equivalent to:
  ```
  | mk_emptyset: forall (s: str),
    False ->
    emptyset_lang s
  ```
  *)

Inductive lambda_lang: lang :=
  | mk_lambda: lambda_lang []
  .
  (*
  This is equivalent to:
  ```
  | mk_lambda:
    forall (s: str),
    s = [] ->
    lambda_lang s
  ```
  *)

Inductive symbol_lang (a: alphabet): lang :=
  | mk_symbol: symbol_lang a [a].
  (*
  This is equivalent to:
  ```
  | mk_symbol:
    forall (s: str),
    s = [a] ->
    symbol_lang a s
  ```
  *)

(*
    *Boolean function*. We shall denote any Boolean function of $P$ and $Q$ by $f(P, Q)$.
    Of course, all the laws of Boolean algebra apply.
    `nor` is used to emulate `f`, since nor can be used to emulate all boolean functions.
*)
Inductive nor_lang (P Q: lang): lang :=
  | mk_nor : forall s,
    s `notelem` P /\ s `notelem` Q ->
    nor_lang P Q s
  .

(* Concatenation*. $(P.Q) = \{ s | s = p.q; p \in P, q \in Q \}$. *)
Inductive concat_lang (P Q: lang): lang :=
  | mk_concat: forall (p q s: str),
    p ++ q = s ->
    p `elem` P ->
    q `elem` Q ->
    concat_lang P Q s
  .

Inductive star_lang (R: lang): lang :=
  | mk_star_zero : star_lang R []
  | mk_star_more : forall (s p q: str),
      p ++ q = s ->
      p <> [] ->
      p `elem` R ->
      q `elem` (star_lang R) ->
      s `elem` star_lang R.

(*
  Here we use a mix of Fixpoint and Inductive predicates to define the denotation of regular expressions.
*)
Reserved Notation "{{ r }}" (r at level 60, no associativity).
Fixpoint denote_regex (r: regex): lang :=
  match r with
  | emptyset => emptyset_lang
  | lambda => lambda_lang
  | symbol y => symbol_lang y
  | concat r1 r2 => concat_lang {{r1}} {{r2}}
  | star r1 => star_lang {{r1}}
  | nor r1 r2 => nor_lang {{r1}} {{r2}}
  end
where "{{ r }}" := (denote_regex r).

