Set Implicit Arguments.
Set Asymmetric Patterns.

Require Import List.

Require Import comparable.
Require Import compare_regex.
Require Import nullable.
Require Import regex.

Definition is_eq {X: Set} {tc: comparable X} (x y: X) : bool :=
  match compare x y with
  | Eq => true
  | _ => false
  end.

(* derive returns the regular expression that is left to match
   after matching the input character x, for example:
   derive (ba)*      b    = a(ba)*
   derive a          a    = empty
   derive b          a    = nothing
   derive ab|a       a    = b|empty
   derive bc         b    = c
   derive (a|empty)b a    = b
   derive (a|empty)b b    = empty
   derive empty b    b    = empty
*)
Fixpoint derive {X: Set} {tc: comparable X} (r: regex X) (x: X) : regex X :=
  match r with
  | nothing => nothing _
  | empty => nothing _
  | char y => if is_eq x y
    then empty _
    else nothing _
  | or s t => or (derive s x) (derive t x)
  | and s t => and (derive s x) (derive t x)
  | concat s t =>
    if nullable s
    then or (concat (derive s x) t) (derive t x)
    else concat (derive s x) t
  | not s => not (derive s x)
  | zero_or_more s => concat (derive s x) (zero_or_more s)
  end.

Definition matches {X: Set} {tc: comparable X} (r: regex X) (xs: list X) : bool :=
  nullable (fold_left derive xs r)
.

(* r&r = r *)
Theorem and_idemp : forall {X: Set} {tc: comparable X} (xs: list X) (r1 r2: regex X) (p: compare_regex r1 r2 = Eq),
  matches (and r1 r2) xs = matches r1 xs.
Proof.
unfold matches.
induction xs.
- simpl.
  intros.
  rewrite (compare_equal r1 r2 p).
  apply Bool.andb_diag.
- simpl.
  intros.
  rewrite (compare_equal r1 r2 p).
  apply IHxs.
  apply compare_reflex.
Qed.

(* r&s = s&r *)
Theorem and_comm : forall {X: Set} {tc: comparable X} (xs: list X) (r1 r2: regex X),
  matches (and r1 r2) xs = matches (and r2 r1) xs.
Proof.
unfold matches.
induction xs.
- simpl.
  firstorder.
- simpl.
  intros.
  apply IHxs.
Qed.

(* (r&s)&t = r&(s&t) *)
Theorem and_assoc : forall {X: Set} {tc: comparable X} (xs: list X) (r s t: regex X),
    matches (and (and r s) t) xs = matches (and r (and s t)) xs.
Proof.
unfold matches.
induction xs.
- simpl.
  firstorder.
- simpl.
  intros.
  apply IHxs.
Qed.

(* nothing&r = nothing *)
Theorem and_nothing : forall {X: Set} {tc: comparable X} (xs: list X) (r: regex X),
  matches (and (nothing _) r) xs = matches (nothing _) xs.
Proof.
unfold matches.
induction xs.
- simpl.
  trivial.
- simpl.
  intros.
  apply IHxs.
Qed.

(* not(nothing)&r = r *)
Theorem and_not_nothing : forall {X: Set} {tc: comparable X} (xs: list X) (r: regex X),
    matches (and (not (nothing _)) r) xs = matches r xs.
Proof.
unfold matches.
induction xs.
- simpl.
  trivial.
- simpl.
  intros.
  apply IHxs.
Qed.

(* TODO *)
(* (r.s).t = r.(s.t) *)
Theorem concat_assoc: forall {X: Set} {tc: comparable X} (xs: list X) (r s t: regex X),
  matches (concat (concat r s) t) xs = matches (concat r (concat s t)) xs.
Admitted.

(* nothing.r = nothing *)
Theorem concat_nothing : forall {X: Set} {tc: comparable X} (xs: list X) (r: regex X),
  matches (concat (nothing _) r) xs = matches (nothing _) xs.
Proof.
unfold matches.
induction xs.
- simpl.
  reflexivity.
- simpl.
  exact IHxs.
Qed.

Lemma fold_at_nothing : forall {X: Set} {tc: comparable X} (xs : list X), (fold_left derive xs (nothing _) = (nothing _)).
Proof.
simpl.
intros.
induction xs.
- simpl.
  trivial.
- simpl.
  apply IHxs.
Qed.

Lemma nullable_fold : forall {X: Set} {tc: comparable X} (xs : list X) (r s: regex X), (nullable (fold_left derive xs (or r s))) = (orb (nullable (fold_left derive xs r)) (nullable (fold_left derive xs s))).
Proof.
induction xs.
- intros.
  simpl.
  reflexivity.
- intros.
  simpl.
  apply IHxs.
Qed.

(* r.nothing = nothing *)
Theorem concat_nothing2 : forall {X: Set} {tc: comparable X} (xs: list X) (r: regex X),
  matches (concat r (nothing _)) xs = matches (nothing _) xs.
Proof.
unfold matches.
induction xs.
- intros.
  simpl.
  apply Bool.andb_false_r.
- simpl.
  intros.
  remember (nullable r).
  destruct b.
  + rewrite nullable_fold.
    case (nullable(fold_left derive xs (nothing _))).
    * firstorder.
    * rewrite IHxs.
      rewrite fold_at_nothing.
      simpl.
      trivial.
  + apply IHxs.
Qed.

(* TODO *)
(* empty.r = r *)
Theorem concat_empty : forall {X: Set} {tc: comparable X} (xs: list X) (r: regex X),
  matches (concat (empty _) r) xs = matches r xs.
Admitted.

(* TODO *)
(* r.empty = r *)
Theorem concat_empty2: forall {X: Set} {tc: comparable X} (xs: list X) (r: regex X),
  matches (concat r (empty _)) xs = matches r xs.
Admitted.

(* r|r = r *)
Theorem or_idemp : forall {X: Set} {tc: comparable X} (xs: list X) (r1 r2: regex X) (p: compare_regex r1 r2 = Eq),
  matches (or r1 r2) xs = matches r1 xs.
Proof.
unfold matches.
induction xs.
- simpl.
  intros.
  rewrite (compare_equal r1 r2 p).
  induction (nullable r2); compute; reflexivity.
- simpl.
  intros.
  rewrite (compare_equal r1 r2 p).
  apply IHxs.
  apply compare_reflex.
Qed.

(* r|s = s|r *)
Theorem or_comm : forall {X: Set} {tc: comparable X} (xs: list X) (r s: regex X),
  matches (or r s) xs = matches (or s r) xs.
Proof.
unfold matches.
induction xs.
- simpl.
  firstorder.
- simpl.
  intros.
  apply IHxs.
Qed.

(* (r|s)|t = r|(s|t) *)
Theorem or_assoc : forall {X: Set} {tc: comparable X} (xs: list X) (r s t: regex X),
  matches (or r (or s t)) xs = matches (or (or r s) t) xs.
Proof.
unfold matches.
induction xs.
- simpl.
  intros.
  firstorder.
- intros.
  apply IHxs.
Qed.

(* TODO *)
(* not(nothing)|r = not(nothing) *)
Theorem or_not_nothing : forall {X: Set} {tc: comparable X} (xs: list X) (r: regex X),
  matches (or (not (nothing _)) r) xs = matches (not (nothing _)) xs.
Admitted.

(* nothing|r = r *)
Theorem or_id : forall {X: Set} {tc: comparable X} (xs: list X) (r: regex X),
  matches (or r (nothing _)) xs = matches r xs.
Proof.
unfold matches.
induction xs.
- simpl.
  firstorder.
- intros.
  simpl.
  apply IHxs.
Qed.

(* TODO *)
(* zero_or_more(zero_or_more(r)) = zero_or_more(r) *)
Theorem zero_or_more_zero_or_more : forall {X: Set} {tc: comparable X} (xs: list X) (r: regex X),
  matches (zero_or_more (zero_or_more r)) xs = matches (zero_or_more r) xs.
Admitted.

(* TODO *)
(* (empty)* = empty *)
Theorem zero_or_more_empty : forall {X: Set} {tc: comparable X} (xs: list X),
  matches (zero_or_more (empty _)) xs = matches (empty _) xs.
Admitted.

(* (nothing)* = empty *)
Theorem nothing_zero_or_more : forall {X: Set} {tc: comparable X} (xs: list X),
  matches (zero_or_more (nothing _)) xs = matches (empty _) xs.
Proof.
unfold matches.
induction xs.
- simpl.
  reflexivity.
- simpl.
  apply concat_nothing.
Qed.

(* TODO *)
(* not(not(r)) = r *)
Theorem not_not : forall {X: Set} {tc: comparable X} (xs: list X) (r: regex X),
  matches (not (not r)) xs = matches r xs.
Admitted.

