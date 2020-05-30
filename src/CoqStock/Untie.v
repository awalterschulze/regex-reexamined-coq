(*
untie the not

untie tactic:
unfolds the not in the goal, if there is one.
```
~x => x -> False
```
It then turns the expression inside the not, into an hypothesis
```
H: x
False
```
Then it inverts the new hypothesis H and clears it.
*)

Local Ltac untie_goal :=
let H := fresh "H"
in unfold not;
   intros H;
   inversion_clear H;
   subst.

Ltac untie :=
  match goal with
  | [ |- ~ _ ] =>
    untie_goal
  end.

Example example_untie_neq: 5 <> 4.
Proof.
untie.
Qed.

Example example_untie_not: forall (x: nat), 
  x = 4 -> ~ (5 = 4).
Proof.
intros.
untie.
Qed.