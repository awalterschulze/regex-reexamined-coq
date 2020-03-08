Require Import List.
Require Import comparable.
Require Import regex.
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