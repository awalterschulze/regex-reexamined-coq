Require Import List.
Import ListNotations.
Require Import Bool.

Require Import comparable.
Require Import nullable.
Require Import regex.
Require Import derive_def.

Hypothesis (A: Type).
Hypothesis (cmp: comparable A).

(* Note: sig and ex are more or less the same, except that sig returns a Type,
 while ex returns a Prop.
 The notation { .. | ..} defines a sig.
 The name "sig" comes from "sigma type". *)
Print sig.
Print ex.


(*
Goal (with respect to previous version that Paul came up with):

We want to replace the original

   { x | P }   (where P: list A -> Prop)

with the sigma type

   { xs : list A | P xs}.

Reasons why this might be a good idea:

1. They both seem to denote more or less the same thing: a subset of all lists
   defined by a proposition (all lists that satisfy that proposition).
2. The latter is built-in.
3. The latter is a type, so it might allow us to use Coq's type system more effectively.


The explanations for the changes I made are interspersed with the code.
 *)

Definition set_of_sequences := Type.
(* Explanation:
This used to be:

  Definition set_of_sequences {A: Type} {cmp: comparable A} := list A -> Prop.

I also wonder whether it would be better to replace Prop by bool.
But at least one nice thing with this definition is:
the notation

   "xs \in R" := (R xs)

actually denotes a certain Prop. So "xs \in R" is a proposition that you can prove or disprove.
Is that better than having it be a bool?
(I suppose in this case, all of our conditions R are decidable,
so maybe it doesn't matter too much?)

Anyway, I defined `set_of_sequences` as `Type`,
because in the new notation, something like

   { xs : list A | xs = [a] }

shoud have type `set_of_sequences`, and the type of `{ xs : list A | xs = [a]}` is `Type`.

But this already shows what I think is the main problem:
I don't want every inhabitant of `Type` to be a `set_of_sequences`.
I only want those of the above form.
*)


Notation "xs \in R" := (exists xspf: R, proj1_sig xspf = xs) (at level 80).
(* Explanation:
This used to be

  Notation "xs \in R" := (R xs) (at level 80).

The inhibitants of { xs : list A | P xs }
are pairs (xs : list A, pf: P xs) (this is pseudo-notation)
and this statement says that xs0 is in { xs : list A | P xs }
if there exists a pair of the form (xs0, pf).

(So equivalently, you could just say: xs0 is in the "set" {xs : list A | P xs})
if there is an inhibitant of `P xs`, which is what Paul was doing.
So this is a lot less direct.)
*)

Check (forall (xs: list A), xs \in {ys : list A | ys <> []}).

Reserved Notation "| r |" (at level 60).
Reserved Notation "xs \in * R" (at level 80).

(* I've commented this out to just focus on the main part below. *)
(* Inductive matching_sequences_for_star {A: Type} {cmd: comparable A} (R: set_of_sequences): set_of_sequences := *)
(* | star_matches_nil : [] \in *R *)
(* | star_matches_concat : forall xs ys, *)
(*     xs \in R -> *)
(*     ys \in *R -> *)
(*     xs ++ ys \in *R *)
(* where "xs \in * R" := ((matching_sequences_for_star R) xs). *)




(* ATTEMPT 1 *)
Fail Fixpoint matching_sequences_for_regex {cmp: comparable A} (r: regex A): Type :=
  match r with
  | fail => { xs: list A | xs = [] }
  | empty => { xs: list A | xs = [] }
  | char a => { xs: list A | xs = [a] }
  (* | _ => { xs: list A | xs = [] } *)
  | or r1 r2 => { xs: list A | (xs \in |r1| \/ xs \in |r2|) }
  | and r1 r2 => { xs: list A | (xs \in |r1| /\ xs \in |r2|) }
  | concat r1 r2 => { xs: list A | (exists ys zs, xs = ys ++ xs /\ ys \in |r1| /\ zs \in |r2|) }
  | not r1 => { xs: list A | ~ (xs \in |r1|) }
  | star r => { xs: list A | xs \in |empty| \/ xs \in |concat r (star r)| }
  end
where "| r |" := (matching_sequences_for_regex r).
(* This fails, because we need to be able to say

     xs \in |r1|

but |r1| has type Type, and the notation `xs \in T` as I defined it above only
works when `T` is a sigma type.
 *)


(* ATTEMPT 2:
I tried to fix the above problem by trying to say that `matching_sequences_for_regex`
doesn't return just any old type, it actually returns a type of the form
{ xs : list A | P xs }.
However, this fails because of some universe inconsistency:

The term "{x : list A | P x}" has type "Type" while it is expected to have type 
"Prop" (universe inconsistency).
 *)
Fail Fixpoint matching_sequences_for_regex {cmp: comparable A} (r: regex A):
  (exists (P: list A -> Prop), (@sig (list A) P)) :=
  match r with
  | fail => { xs: list A | xs = [] }
  | empty => { xs: list A | xs = [] }
  | char a => { xs: list A | xs = [a] }
  (* | _ => { xs: list A | xs = [] } *)
  | or r1 r2 => { xs: list A | (xs \in |r1| \/ xs \in |r2|) }
  | and r1 r2 => { xs: list A | (xs \in |r1| /\ xs \in |r2|) }
  | concat r1 r2 => { xs: list A | (exists ys zs, xs = ys ++ xs /\ ys \in |r1| /\ zs \in |r2|) }
  | not r1 => { xs: list A | ~ (xs \in |r1|) }
  | star r => { xs: list A | xs \in |empty| \/ xs \in |concat r (star r)| }
  end
where "| r |" := (matching_sequences_for_regex r).

Definition derive_sequence {A: Type} {cmd: comparable A} (a: A) (R: set_of_sequences) : set_of_sequences :=
  { xs | (a :: xs) \in R }.

Theorem derive_is_derivative {A: Type} {cmd: comparable A} (a: A) (r: regex A):
  forall (xs: list A), xs \in |derive r a| <-> xs \in derive_sequence a (|r|).
Admitted.
