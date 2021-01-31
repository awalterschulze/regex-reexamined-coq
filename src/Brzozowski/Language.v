Require Import CoqStock.DubStep.
Require Import CoqStock.Invs.
Require Import CoqStock.List.
Require Import CoqStock.Listerine.
Require Import CoqStock.Untie.
Require Import CoqStock.WreckIt.

Require Import Brzozowski.Alphabet.
Require Import Brzozowski.Regex.

Create HintDb lang.

(* A string is a list of characters. *)
Definition str := list alphabet.
(* A regular expression denotes a set of strings called a _language_. *)
Definition lang := str -> Prop.

Definition elem (s: str) (l: lang): Prop := l s.

Notation " p \in P " := (elem p P) (at level 20).
Notation " p \notin P " := (not (elem p P)) (at level 20).

#[export]
Hint Unfold elem: lang.

Definition lang_if (s1 s2: lang): Prop :=
  forall (s: str),
  s \in s1 -> s \in s2.

Notation "s1 {->} s2" := (lang_if s1 s2) (at level 80).

#[export]
Hint Unfold lang_if: lang.

Definition lang_iff (s1 s2: lang): Prop :=
  forall (s: str),
  s \in s1 <-> s \in s2.

Notation "s1 {<->} s2" := (lang_iff s1 s2) (at level 80).

#[export]
Hint Unfold lang_iff: lang.

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

#[export]
Hint Constructors emptyset_lang: lang.

Inductive emptystr_lang: lang :=
  | mk_emptystr: emptystr_lang []
  .
  (*
  This is equivalent to:
  ```
  | mk_emptystr:
    forall (s: str),
    s = [] ->
    emptystr_lang s
  ```
  *)

#[export]
Hint Constructors emptystr_lang: lang.

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

#[export]
Hint Constructors symbol_lang: lang.

(*
    *Boolean function*. We shall denote any Boolean function of $P$ and $Q$ by $f(P, Q)$.
    Of course, all the laws of Boolean algebra apply.
    `neg` and `or` are used to emulate `f`, since they can be used to emulate all boolean functions.
*)
Inductive or_lang (P Q: lang): lang :=
  | mk_or : forall s,
    s \in P \/  s \in Q ->
    or_lang P Q s
  .

#[export]
Hint Constructors or_lang: lang.

Inductive neg_lang (P: lang): lang :=
  | mk_neg : forall s,
    s \notin P ->
    neg_lang P s
  .

#[export]
Hint Constructors neg_lang: lang.

(* Concatenation*. $(P.Q) = \{ s | s = p.q; p \in P, q \in Q \}$. *)
Inductive concat_lang (P Q: lang): lang :=
  | mk_concat: forall (p q s: str),
    p ++ q = s ->
    p \in P ->
    q \in Q ->
    concat_lang P Q s
  .

#[export]
Hint Constructors concat_lang: lang.

Inductive star_lang (R: lang): lang :=
  | mk_star_zero : star_lang R []
  | mk_star_more : forall (s p q: str),
      p ++ q = s ->
      p <> [] ->
      p \in R ->
      q \in (star_lang R) ->
      s \in star_lang R.

#[export]
Hint Constructors star_lang: lang.

(*
  Here we use a mix of Fixpoint and Inductive predicates to define the denotation of regular expressions.
*)
Reserved Notation "{{ r }}" (r at level 60, no associativity).
Fixpoint denote_regex (r: regex): lang :=
  match r with
  | emptyset => emptyset_lang
  | emptystr => emptystr_lang
  | symbol y => symbol_lang y
  | or r1 r2 => or_lang {{r1}} {{r2}}
  | neg r1 => neg_lang {{r1}}
  | concat r1 r2 => concat_lang {{r1}} {{r2}}
  | star r1 => star_lang {{r1}}
  end
where "{{ r }}" := (denote_regex r).

#[export]
Hint Unfold denote_regex: lang.