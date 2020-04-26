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

Theorem fail_is_terminating : forall {X: Type} {C: comparable X} (xs: list X),
  matchesb fail xs = false.
Proof.
  induction xs; intros; simpl_matchesb; trivial.
Qed.

(* or_simple simplifies or expressions *)
Ltac or_simple := repeat
  (  orb_simple
  || rewrite or_is_logical_or
  || rewrite fail_is_terminating
  ).

Section Derive.

Context {X: Type}.
Context {C: comparable X}.

(* r&r = r *)
Theorem and_idemp : forall (xs: list X) (r1 r2: regex X) (p: compare_regex r1 r2 = Eq),
  matchesb (and r1 r2) xs = matchesb r1 xs.
Proof.
unfold matchesb.
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
Theorem and_comm : forall (xs: list X) (r1 r2: regex X),
  matchesb (and r1 r2) xs = matchesb (and r2 r1) xs.
Proof.
unfold matchesb.
induction xs.
- simpl.
  firstorder.
- simpl.
  intros.
  apply IHxs.
Qed.

(* (r&s)&t = r&(s&t) *)
Theorem and_assoc : forall (xs: list X) (r s t: regex X),
    matchesb (and (and r s) t) xs = matchesb (and r (and s t)) xs.
Proof.
unfold matchesb.
induction xs.
- simpl.
  firstorder.
- simpl.
  intros.
  apply IHxs.
Qed.

(* fail&r = fail *)
Theorem and_fail : forall (xs: list X) (r: regex X),
  matchesb (and fail r) xs = matchesb fail xs.
Proof.
unfold matchesb.
induction xs.
- simpl.
  trivial.
- simpl.
  intros.
  apply IHxs.
Qed.

(* not(fail)&r = r *)
Theorem and_not_fail : forall (xs: list X) (r: regex X),
    matchesb (and (not fail) r) xs = matchesb r xs.
Proof.
unfold matchesb.
induction xs.
- simpl.
  trivial.
- simpl.
  intros.
  apply IHxs.
Qed.


(* concat (or r s) t => or (concat r t) (concat s t) *)
Theorem concat_or_distrib_r': forall
  (xs: list X)
  (r s t: regex X),
  matchesb (concat (or r s) t) xs
  = matchesb (or (concat r t) (concat s t)) xs.
Proof.
induction xs.
- intros. simpl_matchesb.
  orb_simple.
- intros. simpl_matchesb.
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
  (xs: list X)
  (r s t: regex X),
  matchesb (concat (concat r s) t) xs
  = matchesb (concat r (concat s t)) xs.
Proof.
induction xs.
- intros.
  cbn.
  firstorder.
- intros.
  simpl_matchesb.
  case (nullable r), (nullable s);
  try ( cbn;
    repeat rewrite or_is_logical_or;
    try rewrite concat_or_distrib_r';
    repeat rewrite or_is_logical_or;
    rewrite IHxs;
    orb_simple).
Qed.

(* fail.r = fail *)
Theorem concat_fail_l : forall (xs: list X) (r: regex X),
  matchesb (concat fail r) xs = matchesb fail xs.
Proof.
unfold matchesb.
induction xs.
- simpl.
  reflexivity.
- simpl.
  exact IHxs.
Qed.

Theorem concat_fail_r :
  forall (xs : list X)
         (r : regex X),
    matchesb (concat r fail) xs = matchesb fail xs.
Proof.
  induction xs; intros; simpl_matchesb.
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
  forall (xs: list X)
         (r s t: regex X),
    matchesb (concat (or r s) t) xs = matchesb (or (concat r t) (concat s t)) xs.
Proof.
  induction xs; intros; simpl_matchesb.
  - rewrite andb_orb_distrib_l.
    reflexivity.
  - destruct (nullable r), (nullable s);
      simpl_matchesb;
      repeat rewrite or_is_logical_or;
      try apply IHxs;
      try rewrite IHxs;
      repeat rewrite or_is_logical_or;
      orb_simple.
Qed.

(* (r.s).t = r.(s.t) *)
Theorem concat_assoc: forall (xs: list X) (r s t: regex X),
  matchesb (concat (concat r s) t) xs = matchesb (concat r (concat s t)) xs.
Proof.
  induction xs; intros; simpl_matchesb.
  - firstorder.
  - destruct (nullable r), (nullable s);
      simpl_matchesb;
      repeat rewrite or_is_logical_or;
      try apply IHxs;
      try rewrite IHxs;
      rewrite concat_or_distrib_r;
      repeat rewrite or_is_logical_or;
      rewrite IHxs;
      orb_simple.
Qed.

Lemma fold_at_fail : forall (xs : list X), (fold_left derive xs fail = fail).
Proof.
simpl.
intros.
induction xs.
- simpl.
  trivial.
- simpl.
  apply IHxs.
Qed.

Lemma nullable_fold : forall (xs : list X) (r s: regex X), (nullable (fold_left derive xs (or r s))) = (orb (nullable (fold_left derive xs r)) (nullable (fold_left derive xs s))).
Proof.
induction xs.
- intros.
  simpl.
  reflexivity.
- intros.
  simpl.
  apply IHxs.
Qed.

(* r.fail = fail *)
Theorem concat_fail_r' : forall (xs: list X) (r: regex X),
  matchesb (concat r fail) xs = matchesb fail xs.
Proof.
unfold matchesb.
induction xs.
- intros.
  simpl.
  apply Bool.andb_false_r.
- simpl.
  intros.
  remember (nullable r).
  destruct b.
  + rewrite nullable_fold.
    case (nullable(fold_left derive xs fail)).
    * firstorder.
    * rewrite IHxs.
      rewrite fold_at_fail.
      simpl.
      trivial.
  + apply IHxs.
Qed.

(* empty.r = r *)
Theorem concat_empty : forall (xs: list X) (r: regex X),
  matchesb (concat empty r) xs = matchesb r xs.
Proof.
  induction xs; intros; simpl_matchesb.
  - reflexivity.
  - rewrite or_is_logical_or.
    rewrite concat_fail_l.
    rewrite fail_is_terminating.
    rewrite orb_false_l.
    reflexivity.
Qed.

(* r.empty = r *)
Theorem concat_empty2: forall (xs: list X) (r: regex X),
  matchesb (concat r empty) xs = matchesb r xs.
Proof.
  induction xs; intros; simpl_matchesb.
  - rewrite andb_true_r.
    reflexivity.
  - case (nullable r).
    + rewrite or_is_logical_or.
      rewrite IHxs.
      rewrite fail_is_terminating.
      rewrite orb_false_r.
      reflexivity.
    + apply IHxs.
Qed.

(* r|r = r *)
Theorem or_idemp : forall (xs: list X) (r1 r2: regex X) (p: compare_regex r1 r2 = Eq),
  matchesb (or r1 r2) xs = matchesb r1 xs.
Proof.
unfold matchesb.
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
Theorem or_comm : forall (xs: list X) (r s: regex X),
  matchesb (or r s) xs = matchesb (or s r) xs.
Proof.
unfold matchesb.
induction xs.
- simpl.
  firstorder.
- simpl.
  intros.
  apply IHxs.
Qed.

(* (r|s)|t = r|(s|t) *)
Theorem or_assoc : forall (xs: list X) (r s t: regex X),
  matchesb (or r (or s t)) xs = matchesb (or (or r s) t) xs.
Proof.
unfold matchesb.
induction xs.
- simpl.
  intros.
  firstorder.
- intros.
  apply IHxs.
Qed.

(* not(fail)|r = not(fail) *)
Theorem or_not_fail : forall (xs: list X) (r: regex X),
  matchesb (or (not fail) r) xs = matchesb (not fail) xs.
Proof.
  induction xs; intros; simpl_matchesb; trivial.
Qed.

(* fail|r = r *)
Theorem or_id : forall (xs: list X) (r: regex X),
  matchesb (or r fail) xs = matchesb r xs.
Proof.
unfold matchesb.
induction xs.
- simpl.
  firstorder.
- intros.
  simpl.
  apply IHxs.
Qed.

(* star(star(r)) = star(r) *)
Theorem star_star : forall (xs: list X) (r: regex X),
  matchesb (star (star r)) xs = matchesb (star r) xs.
(* TODO: Help Wanted *)
Admitted.

(* (empty)* = empty *)
Theorem star_empty : forall (xs: list X),
  matchesb (star empty) xs = matchesb empty xs.
Proof.
  induction xs; intros; simpl_matchesb.
  - trivial.
  - rewrite concat_fail_l.
    reflexivity.
Qed.

(* (fail)* = empty *)
Theorem fail_star : forall (xs: list X),
  matchesb (star fail) xs = matchesb empty xs.
Proof.
unfold matchesb.
induction xs.
- simpl.
  reflexivity.
- simpl.
  apply concat_fail_l.
Qed.

(* not(not(r)) = r *)
Theorem not_not : forall (xs: list X) (r: regex X),
  matchesb (not (not r)) xs = matchesb r xs.
Proof.
  induction xs; intros; simpl_matchesb.
  - rewrite negb_involutive.
    reflexivity.
  - apply IHxs.
Qed.

Theorem not_fail_is_terminating : forall (xs: list X),
  matchesb (not fail) xs = true.
Proof.
  induction xs; intros; simpl_matchesb.
  - trivial.
  - apply IHxs.
Qed.

End Derive.