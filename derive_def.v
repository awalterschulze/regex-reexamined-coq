Require Import List.
Require Import Bool.

Require Import comparable.
Require Import nullable.
Require Import regex.

Definition is_eq {A: Type} {tc: comparable A} (x y: A) : bool :=
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
Fixpoint derive {A: Type} {tc: comparable A} (r: regex A) (x: A) : regex A :=
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

Definition matchesb {A: Type} {tc: comparable A} (r: regex A) (xs: list A) : bool :=
  nullable (fold_left derive xs r).

(* fold_matchesb tries to find a expression
   `nullable (fold_left derive XS R)`
   in the goal, where XS and R are variables.
   It then applies the fold tactic to
   refold:
   `nullable (fold_left derive XS R)`
   into:
   `matchesb XS R`
   since that is the definition of matchesb.
*)
Ltac fold_matchesb :=
  match goal with
    | [ |- context [nullable (fold_left derive ?XS ?R)] ] =>
      fold (matchesb R XS)
  end.

(*
simpl_matchesb simplifies the current expression
with the cbn tactic and tries to fold back up any
matchesb expressions it can spot.
*)
Ltac simpl_matchesb :=
  cbn; repeat fold_matchesb.

Theorem or_is_logical_or: forall {A: Type} {tc: comparable A} (xs: list A) (r s: regex A),
  matchesb (or r s) xs = (orb (matchesb r xs) (matchesb s xs)).
Proof.
  induction xs; intros; simpl_matchesb.
  - trivial.
  - apply IHxs.
Qed.

Theorem and_is_logical_and: forall {A: Type} {tc: comparable A} (xs: list A) (r s: regex A),
  matchesb (and r s) xs = (andb (matchesb r xs) (matchesb s xs)).
Proof.
(* TODO: Good First Issue *)
Admitted.

(* not(not(r)) = r *)
Theorem not_is_logical_not : forall {A: Type} {tc: comparable A} (xs: list A) (r: regex A),
  matchesb (not r) xs = negb (matchesb r xs).
Proof.
  induction xs; intros; simpl_matchesb.
  - reflexivity.
  - apply IHxs.
Qed.
