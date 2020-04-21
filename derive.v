Set Implicit Arguments.
Set Asymmetric Patterns.

Require Import List.
Require Import Bool.

Require Import comparable.
Require Import compare_regex.
Require Export derive_def.
Require Import nullable.
Require Import orb_simple.
Require Import regex.
Require Import reduce_orb.
Require Import setoid.


Theorem nothing_is_terminating : forall {X: Set} {tc: comparable X} (xs: list X),
  matches (nothing _) xs = false.
Proof.
  induction xs; intros; simpl_matches; trivial.
Qed.

(* or_simple simplifies or expressions *)
Ltac or_simple := repeat
  (  orb_simple
  || rewrite or_is_logical_or
  || rewrite nothing_is_terminating
  ).

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


(* concat (or r s) t => or (concat r t) (concat s t) *)
Theorem concat_or_distrib_r': forall
  {X: Set}
  {tc: comparable X}
  (xs: list X)
  (r s t: regex X),
  matches (concat (or r s) t) xs
  = matches (or (concat r t) (concat s t)) xs.
Proof.
induction xs.
- intros. simpl_matches.
  orb_simple.
- intros. simpl_matches.
  case (nullable r), (nullable s).
  + cbn.
    repeat rewrite or_is_logical_or.
    rewrite IHxs.
    or_simple.
  + cbn.
    repeat rewrite or_is_logical_or.
    rewrite IHxs.
    or_simple.
  + cbn.
    repeat rewrite or_is_logical_or.
    rewrite IHxs.
    or_simple.
  + cbn.
    repeat rewrite or_is_logical_or.
    rewrite IHxs.
    or_simple.
Qed.

(* (r.s).t = r.(s.t) *)
Theorem concat_assoc': forall
  {X: Set}
  {tc: comparable X}
  (xs: list X)
  (r s t: regex X),
  matches (concat (concat r s) t) xs
  = matches (concat r (concat s t)) xs.
Proof.
induction xs.
- intros.
  cbn.
  firstorder.
- intros.
  simpl_matches.
  case (nullable r), (nullable s);
  try ( cbn;
    repeat rewrite or_is_logical_or;
    try rewrite concat_or_distrib_r';
    repeat rewrite or_is_logical_or;
    rewrite IHxs;
    orb_simple).
Qed.

(* nothing.r = nothing *)
Theorem concat_nothing_l : forall {X: Set} {tc: comparable X} (xs: list X) (r: regex X),
  matches (concat (nothing _) r) xs = matches (nothing _) xs.
Proof.
unfold matches.
induction xs.
- simpl.
  reflexivity.
- simpl.
  exact IHxs.
Qed.

Theorem concat_nothing_r :
  forall {X : Set}
         {tc : comparable X}
         (xs : list X)
         (r : regex X),
    matches (concat r (nothing _)) xs = matches (nothing _) xs.
Proof.
  induction xs; intros; simpl_matches.
  - rewrite andb_false_r.
    reflexivity.
  - destruct (nullable r).
    + rewrite or_is_logical_or.
      rewrite IHxs.
      rewrite orb_diag.
      reflexivity.
    + rewrite IHxs.
      reflexivity.
Qed.

(* concat (or r s) t => or (concat r t) (concat s t) *)
Lemma concat_or_distrib_r:
  forall {X: Set}
         {tc: comparable X}
         (xs: list X)
         (r s t: regex X),
    matches (concat (or r s) t) xs = matches (or (concat r t) (concat s t)) xs.
Proof.
  induction xs; intros; simpl_matches.
  - rewrite andb_orb_distrib_l.
    reflexivity.
  - destruct (nullable r), (nullable s);
      simpl_matches;
      repeat rewrite or_is_logical_or;
      try apply IHxs;
      try rewrite IHxs;
      repeat rewrite or_is_logical_or;
      orb_simple.
Qed.

(* (r.s).t = r.(s.t) *)
Theorem concat_assoc: forall {X: Set} {tc: comparable X} (xs: list X) (r s t: regex X),
  matches (concat (concat r s) t) xs = matches (concat r (concat s t)) xs.
Proof.
  induction xs; intros; simpl_matches.
  - firstorder.
  - destruct (nullable r), (nullable s);
      simpl_matches;
      repeat rewrite or_is_logical_or;
      try apply IHxs;
      try rewrite IHxs;
      rewrite concat_or_distrib_r;
      repeat rewrite or_is_logical_or;
      rewrite IHxs;
      orb_simple.
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
Theorem concat_nothing_r' : forall {X: Set} {tc: comparable X} (xs: list X) (r: regex X),
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

(* empty.r = r *)
Theorem concat_empty : forall {X: Set} {tc: comparable X} (xs: list X) (r: regex X),
  matches (concat (empty _) r) xs = matches r xs.
Proof.
  induction xs; intros; simpl_matches.
  - reflexivity.
  - rewrite or_is_logical_or.
    rewrite concat_nothing_l.
    rewrite nothing_is_terminating.
    rewrite orb_false_l.
    reflexivity.
Qed.

(* r.empty = r *)
Theorem concat_empty2: forall {X: Set} {tc: comparable X} (xs: list X) (r: regex X),
  matches (concat r (empty _)) xs = matches r xs.
Proof.
  induction xs; intros; simpl_matches.
  - rewrite andb_true_r.
    reflexivity.
  - case (nullable r).
    + rewrite or_is_logical_or.
      rewrite IHxs.
      rewrite nothing_is_terminating.
      rewrite orb_false_r.
      reflexivity.
    + apply IHxs.
Qed.

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

(* not(nothing)|r = not(nothing) *)
Theorem or_not_nothing : forall {X: Set} {tc: comparable X} (xs: list X) (r: regex X),
  matches (or (not (nothing _)) r) xs = matches (not (nothing _)) xs.
Proof.
  induction xs; intros; simpl_matches; trivial.
Qed.

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

(* zero_or_more(zero_or_more(r)) = zero_or_more(r) *)
Theorem zero_or_more_zero_or_more : forall {X: Set} {tc: comparable X} (xs: list X) (r: regex X),
  matches (zero_or_more (zero_or_more r)) xs = matches (zero_or_more r) xs.
(* TODO: Good First Issue *)
Admitted.

(* (empty)* = empty *)
Theorem zero_or_more_empty : forall {X: Set} {tc: comparable X} (xs: list X),
  matches (zero_or_more (empty _)) xs = matches (empty _) xs.
Proof.
  induction xs; intros; simpl_matches.
  - trivial.
  - rewrite concat_nothing_l.
    reflexivity.
Qed.

(* (nothing)* = empty *)
Theorem nothing_zero_or_more : forall {X: Set} {tc: comparable X} (xs: list X),
  matches (zero_or_more (nothing _)) xs = matches (empty _) xs.
Proof.
unfold matches.
induction xs.
- simpl.
  reflexivity.
- simpl.
  apply concat_nothing_l.
Qed.

(* not(not(r)) = r *)
Theorem not_not : forall {X: Set} {tc: comparable X} (xs: list X) (r: regex X),
  matches (not (not r)) xs = matches r xs.
Proof.
  induction xs; intros; simpl_matches.
  - rewrite negb_involutive.
    reflexivity.
  - apply IHxs.
Qed.

Theorem not_nothing_is_terminating : forall {X: Set} {tc: comparable X} (xs: list X),
  matches (not (nothing _)) xs = true.
Proof.
  induction xs; intros; simpl_matches.
  - trivial.
  - apply IHxs.
Qed.

