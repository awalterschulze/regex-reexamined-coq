Set Implicit Arguments.
Set Asymmetric Patterns.

Require Import List.

Require Import CoqStock.comparable.
Require Import Reexamined.compare_regex.
Require Import Reexamined.derive.
Require Import Reexamined.nullable.
Require Import Reexamined.regex.
Require Import Reexamined.smart_or.

(* sderive is the same as derive, except that it applies
   simplification rules by construction.
   This way we don't have to apply simplification after derivation.
   We hope this will also make it easier to prove things.
*)
Definition sderive {A: Type} {cmp: comparable A} (r: regex A) (x: A) : regex A :=
  match r with
  | fail => fail
  | empty => fail
  | char y => if is_eq x y
    then empty
    else fail
  | or s t => smart_or (derive s x) (derive t x)
  | and s t => and (derive s x) (derive t x)
  | concat s t =>
    if nullable s
    then or (concat (derive s x) t) (derive t x)
    else concat (derive s x) t
  | not s => not (derive s x)
  | star s => concat (derive s x) (star s)
  end.

Definition smatchesb {A: Type} {cmp: comparable A} (r: regex A) (xs: list A) : bool :=
  nullable (fold_left sderive xs r)
.

(* mathing without simplification is the same as with simplification *)
Theorem simplify_is_correct : forall {A: Type} {cmp: comparable A} (xs: list A) (r: regex A),
  matchesb r xs = smatchesb r xs.
Proof.
unfold matchesb.
unfold smatchesb.
induction xs.
- simpl.
  reflexivity.
- simpl.
  induction r; simpl; try (apply IHxs).
  * unfold smart_or.
    remember (compare_regex (derive r1 a) (derive r2 a)).
    induction c.
    + symmetry in Heqc.
      remember or_idemp as H_or_idemp.
      remember (H_or_idemp xs (derive r1 a) (derive r2 a)) as Hmatch_or_if.
      remember (Hmatch_or_if Heqc) as Hmatch_or.
      unfold matchesb in Hmatch_or.
      rewrite Hmatch_or.
      remember regex_proof_compare_eq_is_equal as H_compare_equal.
      remember (H_compare_equal (derive r1 a) (derive r2 a) Heqc) as Heq_r1_r2.
      rewrite Heq_r1_r2.
      apply IHxs.
    + apply IHxs.
    + remember or_comm as H_or_comm.
      unfold matchesb in H_or_comm.
      rewrite H_or_comm.
      apply IHxs.
Qed.