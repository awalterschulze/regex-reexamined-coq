(* derive_simple uses theorems from the derive module to simplify regular expressions *)

Set Implicit Arguments.
Set Asymmetric Patterns.

Require Import derive.
Require Import orb_simple.

(* or_simple simplifies or expressions *)
Ltac or_simple := repeat
    (  orb_simple
    || rewrite or_is_logical_or
    || rewrite nothing_is_terminating
    ).
