Require Import List.
Require Import comparable.
Require Import regex.
Require Import compare_regex.
Require Import nullable.
Set Implicit Arguments.
Set Asymmetric Patterns.

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

(* TODO add associativity *)
Definition smart_or {X: Set} {tc: comparable X} (r s: regex X) : regex X :=
  match compare_regex r s with
  | Eq => s
  | Lt => or r s
  | Gt => or s r
  end.

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

(* sderive is the same as derive, except that it applies
   simplification rules by construction.
   This way we don't have to apply simplification after derivation.
   We hope this will also make it easier to prove things.
*)
Fixpoint sderive {X: Set} {tc: comparable X} (r: regex X) (x: X) : regex X :=
  match r with
  | nothing => nothing _
  | empty => nothing _
  | char y => if is_eq x y
    then empty _
    else nothing _
  | or s t => smart_or (derive s x) (derive t x)
  | and s t => and (derive s x) (derive t x)
  | concat s t =>
    if nullable s
    then or (concat (derive s x) t) (derive t x)
    else concat (derive s x) t
  | not s => not (derive s x)
  | zero_or_more s => concat (derive s x) (zero_or_more s)
  end.

Definition smatches {X: Set} {tc: comparable X} (r: regex X) (xs: list X) : bool :=
  nullable (fold_left sderive xs r)
.

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

(* mathing without simplification is the same as with simplification *)
Theorem simplify_is_correct : forall {X: Set} {tc: comparable X} (xs: list X) (r: regex X),
  matches r xs = smatches r xs.
Proof.
unfold matches.
unfold smatches.
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
      unfold matches in Hmatch_or.
      rewrite Hmatch_or.
      remember compare_equal as H_compare_equal.
      remember (H_compare_equal (derive r1 a) (derive r2 a) Heqc) as Heq_r1_r2.
      rewrite Heq_r1_r2.
      apply IHxs.
    + apply IHxs.
    + remember or_comm as H_or_comm.
      unfold matches in H_or_comm.
      rewrite H_or_comm.
      apply IHxs.
Qed.

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


