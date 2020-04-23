Require Import List.

Inductive regex {A : Type} : Type :=
  | fail    : regex
  | empty   : regex
  | char    : A -> regex
  | concat  : regex -> regex -> regex
  | or      : regex -> regex -> regex
  | star    : regex -> regex.

Inductive matches {A} : regex -> (list A) ->  Prop :=
| empty_matches :
    matches empty nil

| char_matches (a : A):
    matches (char a) (a::nil)

| concat_matches (r s : regex) (xs ys: list A) :
    (matches r xs) -> (matches s ys) -> matches (concat r s) (xs ++ ys)

| or_matches_l (r s : regex) (xs : list A):
    (matches r xs) -> matches (or r s) xs

| or_matches_r (r s : regex) (xs : list A):
    (matches s xs) -> matches (or r s) xs

| star_matches_nil (r : regex):
    matches (star r) nil

| star_matches_concat (r : regex) (xs ys : list A):
    matches r xs -> matches (star r) ys -> matches (star r) (xs ++ ys).

Notation "r =? s" := (matches r s) (at level 80).

(* Notation "r =~ s" := *)
(*   (forall {A : Type} (xs : list A), matches r xs -> matches s xs) (at level 80). *)

Theorem concat_empty_l: forall {A : Type}
                          (xs : list A)
                          (r : regex),
    r =? xs
    -> concat r empty =? xs.
Proof.
  intros.
  rewrite <- app_nil_r.
  apply concat_matches.
  - assumption.
  - apply empty_matches.
Qed.

Theorem concat_empty_r: forall {A : Type}
                          (xs : list A)
                          (r : regex),
    r =? xs -> concat r empty =? xs.
Proof.
  intros.
  rewrite <- app_nil_r.
  apply concat_matches.
  - assumption.
  - apply empty_matches.
Qed.

Theorem concat_nil:
  forall {A : Type}
    (xs : list A)
    (r : regex),
    r =? xs
    -> r =? (xs ++ nil).
Proof.
  intros.
  rewrite <- app_nil_r in H.
  assumption.
Qed.

Example regex_ex2 : (concat (char 1) (char 2)) =? (1::nil) ++ (2::nil).
Proof.
  apply concat_matches.
  - apply char_matches.
  - apply char_matches.
Qed.

Example regex_ex3 : (char 1) =? (1::nil) ++ (2::nil) -> False.
Proof.
  intros.
  inversion H.
Qed.

Theorem star1 : forall {A : Type}
                  (xs : list A)
                  (r : regex),
    r =? xs -> (star r) =? xs.
Proof.
  intros.
  rewrite app_nil_end.
  apply star_matches_concat.
  - assumption.
  - apply star_matches_nil.
Qed.

Theorem concatP:
  forall {A : Type}
    (xs : list A)
    (r s : regex),
    concat r s =? xs
    -> (exists (prefix suffix : list A),
          xs = prefix ++ suffix
          /\ r =? prefix
          /\ s =? suffix).
Proof.
  intros.
  remember (concat r s) as r'.
  induction H; (try inversion Heqr').
  - rewrite H2 in *; clear H2.
    rewrite H3 in *; clear H3.
    clear Heqr' IHmatches1 IHmatches2.
    exists xs.
    exists ys.
    split.
    + reflexivity.
    + split; assumption.
Qed.

Theorem concat_assoc:
  forall {A : Type}
    (l : list A)
    (r s t: regex),
    (concat (concat r s) t) =? l
    -> (concat r (concat s t)) =? l.
Proof.
  intros.
  apply concatP in H.
  elim H; clear H.
  intros xs_ys H0.
  elim H0; clear H0.
  intros zs H1.
  elim H1; clear H1.
  intros.
  elim H0; clear H0.
  intros.
  rewrite H.
  apply concatP in H0.
  elim H0; clear H0.
  intros xs H0.
  elim H0; clear H0.
  intros ys H0.
  elim H0; clear H0.
  intros.
  elim H2; clear H2.
  intros.
  (* TODO clean up above *)


  rewrite H0 in *; clear H0.
  rewrite <- app_assoc.

  apply concat_matches.
  - assumption.
  - apply concat_matches; assumption.
Qed.
 
Theorem concat_assoc1:
  forall {A : Type}
    (xs ys zs l : list A)
    (r s t: regex),
    r =? xs
    -> s =? ys
    -> t =? zs
    -> l = xs ++ ys ++ zs
    -> (concat (concat r s) t) =? l
    -> (concat r (concat s t)) =? l.
Proof.
  intros.
  rewrite H2 in *.
  rewrite app_assoc in H3.
  apply concat_matches.
  - assumption.
  - apply concat_matches.
    + assumption.
    + assumption.
Qed.

Theorem orP:
  forall {A : Type}
    (xs : list A)
    (r s : regex),
    or r s =? xs
    -> r =? xs \/ s =? xs.
Proof.
  intros.
  remember (or r s) as r'.
  induction H; (try inversion Heqr').
  -
    rewrite H1 in *; clear H1.
    left; assumption.
  - rewrite H2 in *; clear H2.
    right; assumption.
Qed.

Theorem concat_or_distrib_r:
  forall {A : Type}
    (xs: list A)
    (r s t: regex),
    (concat (or r s) t) =? xs -> or (concat r t) (concat s t) =? xs.
Proof.
  intros.
  remember (concat (or r s) t) as r'.
  induction H; (try inversion Heqr').
  - rewrite H2 in *; clear H2.
    rewrite H3 in *; clear H3.
    clear IHmatches2.
    clear IHmatches1.

    apply orP in H.
    elim H.
    + intros.
      apply or_matches_l.
      apply concat_matches; assumption.
    + intros.
      apply or_matches_r.
      apply concat_matches; assumption.
Qed.

Theorem concat_fail_l:
  forall {A : Type}
    (xs : list A)
    (r : regex),
    concat fail r =? xs
    -> fail =? xs.
Proof.
  intros.
  inversion H.
  inversion H2.
Qed.

Theorem concat_fail_r:
  forall {A : Type}
    (xs : list A)
    (r : regex),
    concat r fail =? xs -> fail =? xs.
Proof.
  intros.
  inversion H.
  inversion H4.
Qed.

Theorem or_comm:
  forall {A : Type}
    (xs : list A)
    (r s : regex),
    (or r s) =? xs
    -> (or s r) =? xs.
Proof.
  intros.
  apply orP in H; elim H; intros.
  - apply or_matches_r; assumption.
  - apply or_matches_l; assumption.
Qed.

Theorem starP:
  forall {A : Type}
    (xs : list A)
    (r : regex),
    star r =? xs
    -> xs <> nil
    -> exists prefix suffix : list A,
        xs = prefix ++ suffix
        /\ r =? prefix
        /\ star r =? suffix.
Proof.
  intros.
  remember (star r) as r'.
  induction H; (try inversion Heqr').
  - elim (H0 (eq_refl nil)).
  - rewrite H3 in *; clear H3.
    exists xs.
    exists ys.
    split.
    + reflexivity.
    + split; assumption.
Qed.

Lemma star_app:
  forall {A : Type}
    (xs ys : list A)
    (r : regex),
    (star r) =? xs
    -> (star r) =? ys
    -> (star r) =? xs ++ ys.
Proof.
  intros.
  remember (star r) as r'.
  induction H; (try inversion Heqr').
  (* star nil case *)
  (* TODO an example of why blindly applying stuff is wrong,
          applying `star_matches_concat' here would lead to a dead-end :) *)
  - rewrite H1 in *.
    cbn.
    assumption.
  (* star concat case *)
  - rewrite H3 in *; clear H3.
    clear IHmatches1.
    rewrite <- app_assoc.
    apply star_matches_concat.
    + assumption.
    + apply IHmatches2.
      * reflexivity.
      * assumption.
Qed.

Theorem star_idem:
  forall {A : Type}
    (xs : list A)
    (r : regex),
    star (star r) =? xs -> (star r) =? xs.
Proof.
  intros.
  remember (star (star r)) as r'.
  induction H; (try inversion Heqr').
  - apply star_matches_nil.
  - rewrite H2 in *; clear H2.
    apply star_app.
    + assumption.
    + apply IHmatches2.
      assumption.
Qed.
