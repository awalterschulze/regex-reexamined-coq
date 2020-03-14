Set Implicit Arguments.
Set Asymmetric Patterns.

Require Import List.

Require Import comparable.
Require Import compare_regex.
Require Import derive.
Require Import nullable.
Require Import regex.
Require Import smart.

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