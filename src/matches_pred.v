Require Import List.
Import ListNotations.

Require Import comparable.
Require Import derive_def.
Require Import regex.

Reserved Notation "xs =~ r" (at level 80).
Reserved Notation "xs <>~ r" (at level 80).

Inductive matches_prop {A: Type} {cmp: comparable A} : regex A -> (list A) ->  Prop :=
  | empty_matches :
    [] =~ empty

  | char_matches (a : A):
    [a] =~ char a

  | or_matches_l (r s : regex A) (xs : list A):
    xs =~ r ->
    (* --------- *)
    xs =~ or r s

  | or_matches_r (r s : regex A) (xs : list A):
    xs =~ s ->
    (* --------- *)
    xs =~ or r s

  | and_matches (r s : regex A) (xs: list A) :
    xs =~ r ->
    xs =~ s ->
    (* --------- *)
    xs =~ and r s

  | concat_matches (r s : regex A) (xs ys: list A) :
    xs =~ r ->
    ys =~ s ->
    (* --------- *)
    (xs ++ ys) =~ concat r s

  | not_matches (r s : regex A) (xs : list A):
    xs <>~ r ->
    (* --------- *)
    xs =~ (not r)

  | star_matches_nil (r : regex A):
    [] =~ star r

  | star_matches_concat (r : regex A) (xs ys : list A):
    xs =~ r ->
    ys =~ star r ->
    (* --------- *)
    (xs ++ ys) =~ star r

  where "xs =~ r" := (matches_prop r xs)

with mismatches_prop {A : Type} {cmp : comparable A} : regex A -> list A -> Prop :=
  | fail_mismatches xs:
    xs <>~ fail

  | empty_mismatches x xs:
    x :: xs <>~ empty

  | char_mismatches_empty a:
    [] <>~ char a

  | char_mismatches_many a b c xs:
    a :: b :: xs <>~ char c

  | char_mismatches_other a b:
    a <> b ->
    (* --------- *)
    [b] <>~ char a

  | or_mismatches r s xs:
    xs <>~ r ->
    xs <>~ s ->
    (* --------- *)
    xs <>~ (or r s)

  | and_mismatches_l r s xs:
    xs <>~ r ->
    (* --------- *)
    xs <>~ (and r s)

  | and_mismatches_r r s xs:
    xs <>~ s ->
    (* --------- *)
    xs <>~ (and r s)

  | concat_mismatches_l r s xs ys:
    xs <>~ r ->
    (* --------- *)
    xs ++ ys <>~ (concat r s)

  | concat_mismatches_r r s xs ys:
    xs <>~ s ->
    (* --------- *)
    xs ++ ys <>~ (concat r s)

  | not_mismatches r xs:
    xs =~ r ->
    (* --------- *)
    xs <>~ (not r)

  | star_mismatches r xs ys:
    xs <>~ r ->
    (* --------- *)
    xs ++ ys <>~ (star r)

  where "xs <>~ r" := (mismatches_prop r xs).

Theorem charP A {cmp: comparable A} a xs:
  xs =~ char a ->
  (* ----- *)
  xs = [a].
Proof.
  intros.
  remember (char a) as r'.
  induction H; (try inversion Heqr').
  - trivial.
Qed.

Theorem test_char_mis_many A {cmp: comparable A} a b:
  [a; b] <>~ char a /\ [a; b] <>~ char b.
Proof.
  split.
  - apply char_mismatches_many.
  - apply char_mismatches_many.
Qed.

Theorem proof_compare_lt_neq A {cmp : comparable A} c a b:
  c <> Eq ->
  compare a b = c -> a <> b.
Proof.
Admitted.

Lemma is_member_or_not_member A {cmp: comparable A} r xs:
    xs =~ r \/ xs <>~ r.
Proof.
  induction r.
  - (* fail *) right.
    apply fail_mismatches.
  - (* empty *) induction xs.
    + (* nil *) left.
      apply empty_matches.
    + (* cons *) right.
      apply empty_mismatches.
  - (* char *) induction xs.
    + (* nil *) right.
      apply char_mismatches_empty.
    + (* cons *) destruct IHxs.
      * (* left disjunct *) apply charP in H.
        subst.
        right.
        apply char_mismatches_many.
      * (* right disjunct *) remember (char a) as r'.
        induction H; (try inversion Heqr').
        -- subst.
           assert (a <> a0 \/ a = a0).
           {
             remember (compare a a0) as c.
             induction c.
             - compare_to_eq.
               subst.
               right; trivial.
             - symmetry in Heqc.
               apply proof_compare_lt_neq in Heqc.
               left; assumption.
               unfold "~".
               intros H; inversion H.
             - symmetry in Heqc.
               apply proof_compare_lt_neq in Heqc.
               left; assumption.
               unfold "~".
               intros H; inversion H.
           }
           destruct H.
           ++ right.
              apply char_mismatches_other.
              assumption.
           ++ subst.
              left.
              apply char_matches.
        -- subst.
           right.
           apply char_mismatches_many.
        -- subst.
           right.
           apply char_mismatches_many.
  -



(* TODO: Help Wanted *)
Abort.

Theorem matches_prop_describes_matches_impl:
  forall
    {A: Type}
    {cmp: comparable A}
    (r: regex A)
    (xs: list A),
  matchesb r xs = true <-> matches_prop r xs.
(* TODO: Help Wanted
   If this theorem is proved,
   then matches_prop can be used in proofs,
   rather than induction on xs and matchesb.
*)
Abort.
