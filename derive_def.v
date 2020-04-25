Require Import List.
Require Import Bool.

Require Import comparable.
Require Import nullable.
Require Import regex.

Definition is_eq {X: Type} {tc: comparable X} (x y: X) : bool :=
  match compare x y with
  | Eq => true
  | _ => false
  end.

(* derive returns the regular expression that is left to match
   after matching the input character x, for example:
   derive (ba)*      b    = a(ba)*
   derive a          a    = empty
   derive b          a    = fail
   derive ab|a       a    = b|empty
   derive bc         b    = c
   derive (a|empty)b a    = b
   derive (a|empty)b b    = empty
   derive empty b    b    = empty
*)
Fixpoint derive {X: Type} {tc: comparable X} (r: regex X) (x: X) : regex X :=
  match r with
  | fail => fail
  | empty => fail
  | char y => if is_eq x y
    then empty
    else fail
  | or s t => or (derive s x) (derive t x)
  | and s t => and (derive s x) (derive t x)
  | concat s t =>
    if nullable s
    then or (concat (derive s x) t) (derive t x)
    else concat (derive s x) t
  | not s => not (derive s x)
  | star s => concat (derive s x) (star s)
  end.

Definition matches {X: Type} {tc: comparable X} (r: regex X) (xs: list X) : bool :=
  nullable (fold_left derive xs r).

(* fold_matches tries to find a expression
   `nullable (fold_left derive XS R)`
   in the goal, where XS and R are variables.
   It then applies the fold tactic to
   refold:
   `nullable (fold_left derive XS R)`
   into:
   `matches XS R`
   since that is the definition of matches.
*)
Ltac fold_matches :=
  match goal with
    | [ |- context [nullable (fold_left derive ?XS ?R)] ] =>
      fold (matches R XS)
  end.

(*
simpl_matches simplifies the current expression
with the cbn tactic and tries to fold back up any
matches expressions it can spot.
*)
Ltac simpl_matches :=
  cbn; repeat fold_matches.

Theorem or_is_logical_or: forall {X: Type} {tc: comparable X} (xs: list X) (r s: regex X),
  matches (or r s) xs = (orb (matches r xs) (matches s xs)).
Proof.
  induction xs; intros; simpl_matches.
  - trivial.
  - apply IHxs.
Qed.

Theorem and_is_logical_and: forall {X: Type} {tc: comparable X} (xs: list X) (r s: regex X),
  matches (and r s) xs = (andb (matches r xs) (matches s xs)).
Proof.
(* TODO: Good First Issue *)
Admitted.

(* not(not(r)) = r *)
Theorem not_is_logical_not : forall {X: Type} {tc: comparable X} (xs: list X) (r: regex X),
  matches (not r) xs = negb (matches r xs).
Proof.
  induction xs; intros; simpl_matches.
  - reflexivity.
  - apply IHxs.
Qed.
