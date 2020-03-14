Set Implicit Arguments.
Set Asymmetric Patterns.

Require Import comparable.
Require Import compare_regex.
Require Import nullable.
Require Import regex.

(* simplified is a property that a regex's ors are somewhat simplified *)
Fixpoint simplified {X: Set} {tc: comparable X} (r: regex X) : Prop :=
  match r with
  | nothing => True
  | empty => True
  | char _ => True
  | or s t =>
    simplified s
    /\ simplified t
    /\ compare_regex s t = Lt
    /\ match s with
       | or _ _ => False
       | _ => True
       end
    /\ match t with
       | or tl _ => compare_regex s tl = Lt
       | _ => True
       end
  | and s t => simplified s /\ simplified t
  | concat s t => simplified s /\ simplified t
  | not s => simplified s
  | zero_or_more s => simplified s
  end.

(*
(or (char x1) (or (char x2) (or (char x3) (char x4))))
or
- x1
- or
  - x2
  - or
    - x3
    - x4
*)
Lemma test_simplified_or_all_left_in_order : forall {X: Set} {tc: comparable X} (x1 x2 x3 x4: X)
  (p12: compare x1 x2 = Lt)
  (p23: compare x2 x3 = Lt)
  (p34: compare x3 x4 = Lt),
  simplified (or (char x1) (or (char x2) (or (char x3) (char x4)))) -> True.
Proof.
intros.
firstorder.
Qed.

(*
(or (char x1) (or (char x2) (or (char x2) (char x1))))
or
- x1
- or
  - x2
  - or
    - x2
    - x1
*)
Lemma test_simplified_or_all_left_out_of_order : forall
  {X: Set}
  {tc: comparable X}
  (x1 x2 x3 x4: X)
  (p12: compare x1 x2 = Lt)
  (p23: compare x2 x3 = Lt)
  (p34: compare x3 x4 = Lt),
  simplified (or (char x1) (or (char x3) (or (char x2) (char x4)))) -> False.
Proof.
intros x tc.
intros x1 x2 x3 x4.
intros p12 p23 p34.
simpl.
firstorder.
assert (p := proof_compare_lt_assoc x2 x3 x2 p23 H7).
rewrite proof_compare_eq_reflex in p.
discriminate.
Qed.

(*
(or (or (char x1) (char x2)) (or (char x3) (char x4)))
or
  - or
    - x1
    - x2
  - or
    - x3
    - x4
*)
Lemma test_simplified_or_symmetric: forall {X: Set} {tc: comparable X} (x1 x2 x3 x4: X)
  (p12: compare x1 x2 = Lt)
  (p23: compare x2 x3 = Lt)
  (p34: compare x3 x4 = Lt),
  simplified (or (or (char x1) (char x2)) (or (char x3) (char x4))) -> False.
Proof.
intros x tc.
intros x1 x2 x3 x4 p12 p23 p34.
simpl.
firstorder.
Qed.