Require Import List.
Import ListNotations.

Require Import CoqStock.comparable.
Require Import CoqStock.WreckIt.
Require Import Reexamined.regex.
Require Import matches_pred.


Theorem concat_empty_l:
  forall {A : Type} {cmp : comparable A} (xs : list A) (r : regex A),
    xs =~ r ->
    xs =~ concat r empty.
Proof.
  intros.
  rewrite <- app_nil_r.
  apply concat_matches.
  - assumption.
  - apply empty_matches.
Qed.

Theorem concat_empty_r:
  forall {A : Type} {cmp : comparable A} (xs : list A) (r : regex A),
    xs =~ r ->
    xs =~ concat r empty.
Proof.
  intros.
  rewrite <- app_nil_r.
  apply concat_matches.
  - assumption.
  - apply empty_matches.
Qed.

Theorem concat_nil:
  forall {A : Type} {cmp : comparable A} (xs : list A) (r : regex A),
    xs =~ r ->
    (xs ++ nil) =~ r.
Proof.
  intros.
  rewrite <- app_nil_r in H.
  assumption.
Qed.

Theorem concatP:
  forall {A : Type} {cmp : comparable A} (xs : list A) (r s : regex A),
    xs =~ concat r s ->
    (exists (prefix suffix : list A),
        xs = prefix ++ suffix /\ prefix =~ r /\ suffix =~ s).
Proof.
  intros.
  remember (concat r s) as r'.
  induction H; (try inversion Heqr').
  - subst.
    clear Heqr' IHmatches_prop1 IHmatches_prop2.
    exists xs.
    exists ys.
    split.
    + reflexivity.
    + split; assumption.
Qed.

Theorem concat_assoc:
  forall {A : Type} {cmp : comparable A} (l : list A) (r s t: regex A),
    l =~ (concat (concat r s) t) ->
    l =~ (concat r (concat s t)).
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
  (* TODO: Help Wanted
     clean up above *)


  subst.
  rewrite <- app_assoc.

  apply concat_matches.
  - assumption.
  - apply concat_matches; assumption.
Qed.

Theorem concat_assoc':
  forall {A : Type} {cmp : comparable A} (l : list A) (r s t: regex A),
    l =~ (concat (concat r s) t) ->
    l =~ (concat r (concat s t)).
Proof.
  intros.
  apply concatP in H.
  wreckit.
  apply concatP in H.
  wreckit.
  rewrite <- app_assoc.
  apply concat_matches.
  - assumption.
  - apply concat_matches; assumption.
Qed.

Theorem orP:
  forall {A : Type} {cmp : comparable A} (xs : list A) (r s : regex A),
    xs =~ or r s ->
    xs =~ r \/ xs =~ s.
Proof.
  intros.
  remember (or r s) as r'.
  induction H; (try inversion Heqr').
  - subst.
    left; assumption.
  - subst.
    right; assumption.
Qed.

Theorem concat_or_distrib_r:
  forall {A : Type} {cmp : comparable A} (xs: list A) (r s t: regex A),
    xs =~ (concat (or r s) t) ->
    xs =~ or (concat r t) (concat s t).
Proof.
  intros.
  remember (concat (or r s) t) as r'.
  induction H; (try inversion Heqr').
  - subst.
    clear IHmatches_prop2.
    clear IHmatches_prop1.

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
  forall {A : Type} {cmp : comparable A} (xs : list A) (r : regex A),
    xs =~ concat fail r ->
    xs =~ fail.
Proof.
  intros.
  inversion H.
  inversion H2.
Qed.

Theorem concat_fail_r:
  forall {A : Type} {cmp : comparable A} (xs : list A) (r : regex A),
    xs =~ concat r fail ->
    xs =~ fail.
Proof.
  intros.
  inversion H.
  inversion H4.
Qed.

Theorem or_comm:
  forall {A : Type} {cmp : comparable A} (xs : list A) (r s : regex A),
    xs =~ (or r s) ->
    xs =~ (or s r).
Proof.
  intros.
  apply orP in H; elim H; intros.
  - apply or_matches_r; assumption.
  - apply or_matches_l; assumption.
Qed.

Theorem starP:
  forall {A : Type} {cmp : comparable A} (xs : list A) (r : regex A),
    xs =~ star r ->
    xs <> nil ->
    exists prefix suffix : list A,
      xs = prefix ++ suffix /\ prefix =~ r /\ suffix =~ star r.
Proof.
  intros.
  remember (star r) as r'.
  induction H; (try inversion Heqr').
  - elim (H0 (eq_refl nil)).
  - subst.
    exists xs.
    exists ys.
    split.
    + reflexivity.
    + split; assumption.
Qed.

Lemma star_app:
  forall {A : Type} {cmp : comparable A} (xs ys : list A) (r : regex A),
    xs =~ (star r) ->
    ys =~ (star r) ->
    xs ++ ys =~ (star r).
Proof.
  intros.
  remember (star r) as r'.
  induction H; (try inversion Heqr').
  - rewrite H1 in *.
    cbn.
    assumption.
  - subst.
    clear IHmatches_prop1.
    rewrite <- app_assoc.
    apply star_matches_concat.
    + assumption.
    + apply IHmatches_prop2.
      * reflexivity.
      * assumption.
Qed.

Theorem star_idem:
  forall {A : Type} {cmp : comparable A} (xs : list A) (r : regex A),
    xs =~ star (star r) ->
    xs =~ (star r).
Proof.
  intros.
  remember (star (star r)) as r'.
  induction H; (try inversion Heqr').
  - apply star_matches_nil.
  - subst.
    apply star_app.
    + assumption.
    + apply IHmatches_prop2.
      assumption.
Qed.
