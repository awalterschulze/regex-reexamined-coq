Set Implicit Arguments.
Set Asymmetric Patterns.

Require Import List.

Class comparable (X : Set) :=
  { compare : X -> X -> comparison

  ; proof_compare_eq_is_equal
    : forall (x y: X) 
             (p: compare x y = Eq)
    , x = y
  ; proof_compare_eq_reflex
    : forall (x: X)
    , compare x x = Eq
  ; proof_compare_eq_trans
    : forall (x y z: X)
             (p: compare x y = Eq)
             (q: compare y z = Eq)
    , compare x z = Eq
  ; proof_compare_lt_assoc
    : forall (x y z: X)
             (p: compare x y = Lt)
             (q: compare y z = Lt)
    , compare x z = Lt
  ; proof_compare_gt_assoc
    : forall (x y z: X)
             (p: compare x y = Gt)
             (q: compare y z = Gt)
    , compare x z = Gt
  }.

Theorem proof_compare_eq_symm
  : forall {X: Set}
           {tc: comparable X}
           (x y: X)
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
  : forall {X: Set}
           {tc: comparable X}
           (x1 x2: X)
           (p: compare x1 x2 = compare x2 x1)
  , compare x1 x2 = Eq.
Proof.
intros.
remember (compare x1 x2) as c.
induction c.
- reflexivity.
- symmetry in Heqc.
  symmetry in p.
  remember (proof_compare_lt_assoc x1 x2 x1 Heqc p).
  rewrite <- e.
  apply proof_compare_eq_reflex.
- symmetry in Heqc.
  symmetry in p.
  remember (proof_compare_gt_assoc x1 x2 x1 Heqc p).
  rewrite <- e.
  apply proof_compare_eq_reflex.
Qed.

Theorem compare_lt_not_symm_1
  : forall {X: Set}
           {tc: comparable X}
           (x1 x2: X)
           (c12: compare x1 x2 = Lt)
           (c21: compare x2 x1 = Lt)
  , False.
Proof.
intros.
assert (p1 := proof_compare_lt_assoc x1 x2 x1 c12 c21).
assert (p2 := proof_compare_eq_reflex x1).
rewrite p1 in p2.
discriminate.
Qed.

Theorem compare_lt_not_symm_2
  : forall {X: Set}
           {tc: comparable X}
           (x1 x2: X)
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
  : forall {X: Set}
           {tc: comparable X}
           (x1 x2: X)
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
  : forall {X: Set}
           {tc: comparable X}
           (x1 x2: X)
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
  assert (a := proof_compare_lt_assoc x1 x2 x1 p HeqiH).
  rewrite proof_compare_eq_reflex in a.
  discriminate.
- reflexivity.
Qed.

Theorem compare_gt_lt_symm
  : forall {X: Set}
           {tc: comparable X}
           (x1 x2: X)
           (p: compare x1 x2 = Gt)
  , compare x2 x1 = Lt.
(* TODO: Good First Issue *)
Admitted.

Fixpoint comparable_list {X: Set} {tc: comparable X} (xs: list X) (ys: list X) : comparison :=
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
