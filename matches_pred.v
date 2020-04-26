Require Import List.
Import ListNotations.

Require Import comparable.
Require Import regex.

Reserved Notation "xs =~ r" (at level 80).

Inductive matches {A: Type} {C: comparable A} : regex A -> (list A) ->  Prop :=
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

  (* | not_matches (r : regex A) (xs : list A):
    TODO: Help Wanted
  *)

  | star_matches_nil (r : regex A):
    [] =~ star r

  | star_matches_concat (r : regex A) (xs ys : list A):
    xs =~ r ->
    ys =~ star r ->
    (* --------- *)
    (xs ++ ys) =~ star r

  where "xs =~ r" := (matches r xs).
