Require Import List.
Require Import comparable.
Require Import regex.
Require Import compare_regex.
Require Import nullable.
Require Import derive.
Require Import smart.
Set Implicit Arguments.
Set Asymmetric Patterns.

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
Definition eqv_char {X: Set} {tc: comparable X} (a b: X) (r: regex X) : Prop :=
  derive r a = derive r b.

(* Lemma 4.1 proves that given the equivalent_character property
   it also holds for the combinators.
   If characters a and b are equivalent for regular expressions r and s.
   Then they are also equivalent for the:
   - concat
   - or
   - and
   - zero_or_more
   - not
   or those regular expressions.
*)
Lemma eqv_concat : forall {X: Set} {tc: comparable X} (a b: X) (r s: regex X)
  (eqvr: eqv_char a b r) (eqvs: eqv_char a b s),
eqv_char a b (concat r s).
Proof.
(* TODO *)
Admitted.

Lemma eqv_or : forall {X: Set} {tc: comparable X} (a b: X) (r s: regex X)
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

Lemma eqv_and : forall {X: Set} {tc: comparable X} (a b: X) (r s: regex X)
  (eqvr: eqv_char a b r) (eqvs: eqv_char a b s),
eqv_char a b (and r s).
Proof.
(* TODO *)
Admitted.

Lemma eqv_zero_or_more : forall {X: Set} {tc: comparable X} (a b: X) (r: regex X)
  (eqvr: eqv_char a b r),
eqv_char a b (zero_or_more r).
Proof.
(* TODO *)
Admitted.

Lemma eqv_not : forall {X: Set} {tc: comparable X} (a b: X) (r: regex X)
  (eqvr: eqv_char a b r),
eqv_char a b (not r).
Proof.
(* TODO *)
Admitted.


