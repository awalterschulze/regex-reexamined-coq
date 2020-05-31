Require Import List.
Import ListNotations.

Require Import CoqStock.comparable.
Require Import CoqStock.compare_nat.
Require Import Reexamined.regex.
Require Import derive_def.

(*
  A set of sequences is interpreted as a value of `list A -> Prop`
  where the sequence `list A` is in the set if the value on the sequence is `True`.
*)
Definition set_of_sequences {A: Type} {cmp: comparable A} := list A -> Prop.

Notation "xs \in R" := (R xs) (at level 80).
Notation "{ xs | P }" := (fun xs => P) (at level 0, xs at level 99).

Reserved Notation "| r |" (at level 60).
Reserved Notation "xs \in * R" (at level 80).

Inductive matching_sequences_for_star {A: Type} {cmd: comparable A} (R: set_of_sequences): set_of_sequences :=
| star_matches_nil : [] \in *R
| star_matches_concat : forall zs,
    (exists xs ys, xs ++ ys = zs -> xs \in R /\ ys \in *R) -> zs \in *R
where "xs \in * R" := ((matching_sequences_for_star R) xs).

Fixpoint matching_sequences_for_regex {A: Type} {cmp: comparable A} (r: regex A): set_of_sequences :=
  match r with
  | fail => { _ | False }
  | empty => { xs | xs = [] }
  | char a => { xs | xs = [a] }
  | or r1 r2 => { xs | xs \in |r1| \/ xs \in |r2| }
  | and r1 r2 => { xs | xs \in |r1| /\ xs \in |r2| }
  | concat r1 r2 => { xs | exists ys zs, xs = ys ++ zs /\ ys \in |r1| /\ zs \in |r2| }
  | not r1 => { xs | ~ (xs \in |r1|) }
  | star r1 => { xs | xs \in *|r1| }
  end
where "| r |" := (matching_sequences_for_regex r).

Definition derive_sequence {A: Type} {cmd: comparable A} (a: A) (R: set_of_sequences) : set_of_sequences :=
  { xs | (a :: xs) \in R }.

Theorem derive_is_derivative {A: Type} {cmd: comparable A} (a: A) (r: regex A):
  forall (xs: list A), xs \in |derive r a| <-> xs \in derive_sequence a (|r|).
Abort.

Example test_not_not_char : [1] \in |not (not (char 1))|.
Proof.
  unfold  matching_sequences_for_regex.
  unfold Logic.not.
  intros.
  remember (H eq_refl).
  assumption.
Qed.

Example test_two_not_not_in_char_one : ~ ([2] \in |not (not (char 1))|).
Proof.
  unfold  matching_sequences_for_regex.
  unfold Logic.not.
  intros.
  apply H.
  intros.
  discriminate.
Qed.

Example test_list_in_concat_one : [1;2] \in |concat (char 1) (char 2)|.
Proof.
  unfold  matching_sequences_for_regex.
  exists [1].
  exists [2].
  repeat split; reflexivity.
Qed.

Example test_list_not_in_concat_one_two : ~([1;2;3] \in |concat (char 1) (char 2)|).
Proof.
  unfold  matching_sequences_for_regex.
  unfold Logic.not.
  intros.
  destruct H as [x [y [l1 [l2 l3]]]].
  subst.
  discriminate.
Qed.

Example test_one_in_star_char_one : [1] \in |star (char 1)|.
Proof.
  unfold  matching_sequences_for_regex.
  constructor.
  exists [1].
  exists [].
  intros.
  constructor.
  - reflexivity.
  - constructor.
Qed.
