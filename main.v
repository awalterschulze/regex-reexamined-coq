Require Import List.
Require Import comparable.
Require Import regex.
Require Import compare_regex.
Require Import nullable.
Require Import derive.
Require Import smart.
Set Implicit Arguments.
Set Asymmetric Patterns.

(* simple is a simpler version of simplified to learn how to prove simplified in future *)
Fixpoint simple {X: Set} {tc: comparable X} (r: regex X) : Prop :=
  match r with
  | nothing => True
  | empty => True
  | char _ => True
  | or s t => simple s /\ simple t
    /\ ~(compare_regex s t = Eq)
  | and s t => simple s /\ simple t
  | concat s t => simple s /\ simple t
  | not s => simple s
  | zero_or_more s => simple s
  end.

Lemma smart_or_is_simple: forall {X: Set} {tc: comparable X} (r s: regex X) (simple_r: simple r) (simple_s: simple s),
  simple (smart_or r s).
intros.
induction r, s; simpl; try easy.
- unfold smart_or.
  remember (compare_regex (char x) (char x0)) as c.
  induction c.
  + assumption.
  + simpl.
    simpl in Heqc.
    rewrite <- Heqc.
    firstorder.
    (* Locate "<>". *)
    unfold Logic.not.
    discriminate.
  + simpl.
    firstorder.
    unfold Logic.not.
    simpl in Heqc.
    intros.
    apply (proof_compare_eq_symm x0 x) in H.
    rewrite H in Heqc.
    discriminate.
- unfold smart_or.
  remember (compare_regex (or r1 r2) (or s1 s2)) as c.
  induction c.
  + assumption.
  + unfold simple.
    fold simple.
    simpl in simple_r.
    simpl in simple_s.
    split.
    * assumption.
    * split.
      -- assumption.
      -- unfold Logic.not.
         intros.
         rewrite H in Heqc.
         discriminate.
  + unfold simple; fold simple.
    split.
    * assumption.
    * split.
      -- assumption.
      -- unfold Logic.not.
         intros.
         assert (h := H).
         apply compare_equal in H.
         rewrite H in Heqc.
         rewrite compare_reflex in Heqc.
         discriminate.
- unfold smart_or.
  remember (compare_regex (and r1 r2) (and s1 s2)) as c.
  induction c.
  + assumption.
  + unfold simple; fold simple.
    simpl in simple_r.
    simpl in simple_s.
    split.
    * assumption.
    * split.
      -- assumption.
      -- unfold Logic.not.
         intros.
         rewrite H in Heqc.
         discriminate.
  + unfold simple; fold simple.
    split.
    * assumption.
    * split.
      -- assumption.
      -- unfold Logic.not.
         intros.
         assert (h := H).
         apply compare_equal in H.
         rewrite H in Heqc.
         rewrite compare_reflex in Heqc.
         discriminate.
- unfold smart_or.
  remember (compare_regex (concat r1 r2) (concat s1 s2)) as c.
  induction c.
  + assumption.
  + unfold simple; fold simple.
    simpl in simple_r.
    simpl in simple_s.
    split.
    * assumption.
    * split.
      -- assumption.
      -- unfold Logic.not.
         intros.
         rewrite H in Heqc.
         discriminate.
  + unfold simple; fold simple.
    split.
    * assumption.
    * split.
      -- assumption.
      -- unfold Logic.not.
         intros.
         assert (h := H).
         apply compare_equal in H.
         rewrite H in Heqc.
         rewrite compare_reflex in Heqc.
         discriminate.
- unfold smart_or.
  remember (compare_regex (not r) (not s)) as c.
  induction c.
  + assumption.
  + unfold simple; fold simple.
    simpl in simple_r.
    simpl in simple_s.
    split.
    * assumption.
    * split.
      -- assumption.
      -- unfold Logic.not.
         intros.
         rewrite H in Heqc.
         discriminate.
  + unfold simple; fold simple.
    split.
    * assumption.
    * split.
      -- assumption.
      -- unfold Logic.not.
         intros.
         assert (h := H).
         apply compare_equal in H.
         rewrite H in Heqc.
         rewrite compare_reflex in Heqc.
         discriminate.
- unfold smart_or.
  remember (compare_regex (zero_or_more r) (zero_or_more s)) as c.
  induction c.
  + assumption.
  + unfold simple; fold simple.
    simpl in simple_r.
    simpl in simple_s.
    split.
    * assumption.
    * split.
      -- assumption.
      -- unfold Logic.not.
         intros.
         rewrite H in Heqc.
         discriminate.
  + unfold simple; fold simple.
    split.
    * assumption.
    * split.
      -- assumption.
      -- unfold Logic.not.
         intros.
         assert (h := H).
         apply compare_equal in H.
         rewrite H in Heqc.
         rewrite compare_reflex in Heqc.
         discriminate.
Qed.

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


