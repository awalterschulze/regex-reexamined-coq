Set Implicit Arguments.
Set Asymmetric Patterns.

Require Import List.

Class comparable (A : Type) :=
  { compare : A -> A -> comparison (* Eq | Lt | Gt *)

  ; proof_compare_eq_is_equal
    : forall (x y: A)
             (p: compare x y = Eq)
    , x = y
  ; proof_compare_eq_reflex
    : forall (x: A)
    , compare x x = Eq
  ; proof_compare_eq_trans
    : forall (x y z: A)
             (p: compare x y = Eq)
             (q: compare y z = Eq)
    , compare x z = Eq
  ; proof_compare_lt_trans
    : forall (x y z: A)
             (p: compare x y = Lt)
             (q: compare y z = Lt)
    , compare x z = Lt
  ; proof_compare_gt_trans
    : forall (x y z: A)
             (p: compare x y = Gt)
             (q: compare y z = Gt)
    , compare x z = Gt
  }.

(* compare_to_eq turns an hypothesis:
  `Eq = compare x y` into:
  `x = y`
  and then tries to rewrite with it.
*)
Ltac compare_to_eq :=
  match goal with
  | [ H_Eq_Compare : Eq = ?Compare |- _ ] =>
    symmetry in H_Eq_Compare;
    let Heq := fresh "Heq"
    in apply proof_compare_eq_is_equal in H_Eq_Compare as Heq;
       try (rewrite Heq)
  end.

Lemma test_tactic_compare_to_eq
  : forall {A: Type}
           {cmp: comparable A}
           (x y: A)
           (p: Eq = compare x y),
  x = y.
Proof.
intros.
set (Heq := cmp).
compare_to_eq.
reflexivity.
Qed.

(* induction_on_compare starts induction on a `compare` expression in the goal.
   It makes sense to remember this comparison, so that it be rewritten to an
   equality in the Eq induction goal.
*)
Ltac induction_on_compare :=
  (*
  Find an expression (compare ?X ?Y)
  inside the goal and remember it.
  *)
  match goal with
  | [ |- context [(compare ?X ?Y)] ] =>
    remember (compare X Y)
  end;
  (* remember (compare a b) =>
    [
    c: comparison
    Heqc: c = compare a b
    |- _ ]
  *)
  match goal with
  | [ C: comparison |- _ ] =>
    induction C; [ (* Eq *) compare_to_eq | (* Lt *) | (* Gt *)]
  end
.

Theorem proof_compare_eq_symm
  : forall {A: Type}
           {cmp: comparable A}
           (x y: A)
           (p: compare x y = Eq)
  , compare y x = Eq.
Proof.
intros.
assert (p1 := p).
apply proof_compare_eq_is_equal in p.
rewrite p.
rewrite p in p1.
assumption.
Qed.

Theorem compare_eq_is_only_equal
  : forall {A: Type}
           {cmp: comparable A}
           (x1 x2: A)
           (p: compare x1 x2 = compare x2 x1)
  , compare x1 x2 = Eq.
Proof.
intros.
induction_on_compare.
- reflexivity.
- symmetry in Heqc.
  symmetry in p.
  remember (proof_compare_lt_trans x1 x2 x1 Heqc p).
  rewrite <- e.
  apply proof_compare_eq_reflex.
- symmetry in Heqc.
  symmetry in p.
  remember (proof_compare_gt_trans x1 x2 x1 Heqc p).
  rewrite <- e.
  apply proof_compare_eq_reflex.
Qed.

Theorem compare_lt_not_symm_1
  : forall {A: Type}
           {cmp: comparable A}
           (x1 x2: A)
           (c12: compare x1 x2 = Lt)
           (c21: compare x2 x1 = Lt)
  , False.
Proof.
intros.
assert (p1 := proof_compare_lt_trans x1 x2 x1 c12 c21).
assert (p2 := proof_compare_eq_reflex x1).
rewrite p1 in p2.
discriminate.
Qed.

Theorem compare_lt_not_symm_2
  : forall {A: Type}
           {cmp: comparable A}
           (x1 x2: A)
           (c12: compare x1 x2 = Lt)
           (c21: compare x2 x1 = Lt)
  , False.
Proof.
intros.
assert (c := c21).
rewrite <- c12 in c.
apply compare_eq_is_only_equal in c.
rewrite c21 in c.
discriminate.
Qed.

Theorem compare_gt_not_symm
  : forall {A: Type}
           {cmp: comparable A}
           (x1 x2: A)
           (c12: compare x1 x2 = Gt)
           (c21: compare x2 x1 = Gt)
  , False.
Proof.
intros.
assert (c := c12).
rewrite <- c21 in c.
apply compare_eq_is_only_equal in c.
rewrite c12 in c.
discriminate.
Qed.

Theorem compare_lt_gt_symm
  : forall {A: Type}
           {cmp: comparable A}
           (x1 x2: A)
           (p: compare x1 x2 = Lt)
  , compare x2 x1 = Gt.
Proof.
intros.
remember (compare x2 x1) as iH.
induction iH.
- symmetry in HeqiH.
  apply proof_compare_eq_symm in HeqiH.
  rewrite HeqiH in p.
  discriminate.
- symmetry in HeqiH.
  assert (a := proof_compare_lt_trans x1 x2 x1 p HeqiH).
  rewrite proof_compare_eq_reflex in a.
  discriminate.
- reflexivity.
Qed.

Theorem compare_gt_lt_symm
  : forall {A: Type}
           {cmp: comparable A}
           (x1 x2: A)
           (p: compare x1 x2 = Gt)
  , compare x2 x1 = Lt.
Proof.
  intros.
  induction_on_compare.
  - rewrite Heq in p.
    rewrite proof_compare_eq_reflex in p.
    discriminate.
  - trivial.
  - symmetry in Heqc.
    set (a := proof_compare_gt_trans x1 x2 x1 p Heqc).
    rewrite proof_compare_eq_reflex in a.
    discriminate.
Qed.

Fixpoint comparable_list {A: Type} {cmp: comparable A} (xs: list A) (ys: list A) : comparison :=
  match xs with
  | nil => match ys with
      | nil => Eq
      | _ => Lt
      end
  | x :: xs => match ys with
      | nil => Gt
      | y :: ys => match compare x y with
          | Eq => comparable_list xs ys
          | Lt => Lt
          | Gt => Gt
          end
      end
  end.


Definition compare_leq {A: Type} {cmp: comparable A} (x y: A) : Prop :=
  (compare x y = Eq) \/ (compare x y = Lt).

Lemma compare_leq_trans {A: Type} {cmp: comparable A} (x y z: A) :
  (compare_leq x y) -> (compare_leq y z) -> (compare_leq x z).
Proof.
  intros.
  unfold compare_leq in *.
  Hint Resolve 
  match goal with
  | P: context [compare ?x ?y] |- _ => destruct (compare x y)
  end; auto.

