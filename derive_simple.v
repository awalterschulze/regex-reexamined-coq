(* derive_simple uses theorems from the derive module to simplify regular expressions *)

From Coq Require Import Ring.

Require Import derive.
Require Import orb_simple.
Require Import comparable.
Require Import regex.
Require Import compare_regex.
Require Import compare_nat.

(* or_simple simplifies or expressions *)
Ltac or_simple := repeat
    (  orb_simple
    || rewrite or_is_logical_or
    || rewrite nothing_is_terminating
    ).
