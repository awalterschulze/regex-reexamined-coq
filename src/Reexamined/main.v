Set Implicit Arguments.
Set Asymmetric Patterns.

Require Import List.

Require Import CoqStock.comparable.
Require Import Reexamined.compare_regex.
Require Import Reexamined.derive.
Require Import Reexamined.nullable.
Require Import Reexamined.regex.
Require Import Reexamined.smart.

(*Using only or_comm, or_assoc and or_idemp 
  Brzozowski proved that a notion of RE similarity including only
  r + r = r
  r + s = s + r
  (r + s) + t = r + (s + t)
  is enough to ensure that every RE has only a finite number of dissimilar derivatives. 
  Hence, DFA construction is guaranteed to terminate if we use similarity as an approximation for equivalence
  see https://www.ccs.neu.edu/home/turon/re-deriv.pdf
  Regular-expression derivatives reexamined - Scott Owens, John Reppy, Aaron Turon
*)

(* Definition 4.2
   Two input characters are equivalent if for the same regex r
   they produce the same derivative.
*)
Definition eqv_char {A: Type} {cmp: comparable A} (a b: A) (r: regex A) : Prop :=
  derive r a = derive r b.

(* Lemma 4.1 proves that given the equivalent_character property
   it also holds for the combinators.
   If characters a and b are equivalent for regular expressions r and s.
   Then they are also equivalent for the:
   - concat
   - or
   - and
   - star
   - not
   or those regular expressions.
*)
Lemma eqv_concat : forall {A: Type} {cmp: comparable A} (a b: A) (r s: regex A)
  (eqvr: eqv_char a b r) (eqvs: eqv_char a b s),
eqv_char a b (concat r s).
Proof.
(* TODO: Good First Issue *)
Abort.

Lemma eqv_or : forall {A: Type} {cmp: comparable A} (a b: A) (r s: regex A)
  (eqvr: eqv_char a b r) (eqvs: eqv_char a b s),
eqv_char a b (or r s).
Proof.
unfold eqv_char.
intros.
simpl.
rewrite eqvr.
rewrite eqvs.
reflexivity.
Qed.

Lemma eqv_and : forall {A: Type} {cmp: comparable A} (a b: A) (r s: regex A)
  (eqvr: eqv_char a b r) (eqvs: eqv_char a b s),
eqv_char a b (and r s).
Proof.
(* TODO: Good First Issue *)
Abort.

Lemma eqv_star : forall {A: Type} {cmp: comparable A} (a b: A) (r: regex A)
  (eqvr: eqv_char a b r),
eqv_char a b (star r).
Proof.
(* TODO: Good First Issue *)
Abort.

Lemma eqv_not : forall {A: Type} {cmp: comparable A} (a b: A) (r: regex A)
  (eqvr: eqv_char a b r),
eqv_char a b (not r).
Proof.
(* TODO: Good First Issue *)
Abort.


