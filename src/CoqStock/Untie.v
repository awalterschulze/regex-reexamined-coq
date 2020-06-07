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
It attempts to rewrite with the hypothesis, if possible.
If rewrite succeeds, the hypothesis is cleared.
If the resulting hypothesis is also a not, that is applied to the goal again,
thus untying a double not.
Finally tries to apply discriminate and contradiction.
*)

Ltac untie_step :=
  match goal with
  | [ H: context [?X] |- ?X <> _ ] =>
    let Heq := fresh "Heq"
    in unfold not; 
       intro Heq;
       try (discriminate || contradiction);
       rewrite Heq in *;
       clear Heq
  | [ H: context [?X] |- _ <> ?X ] =>
    let Heq := fresh "Heq"
    in unfold not;
       intro Heq;
       try (discriminate || contradiction);
       rewrite <- Heq in *;
       clear Heq
  | [ |- not (_) -> False ] =>
    let H := fresh "H"
    in unfold not;
       intro H;
       apply H
  | [ |- ~ _ ] =>
    unfold not; intro
  | [ |- _ ] =>
    discriminate || contradiction
  end.

Ltac untie := repeat untie_step.

Example example_subst_0: forall (x: nat),
  x = 1 -> x <> 2.
Proof.
intros.
untie.
Qed.

Example example_subst_1: forall (x: nat),
 1 = x -> x <> 2.
Proof.
intros.
untie.
Qed.

Example example_subst_2: forall (x: nat),
 1 = x -> 2 <> x.
Proof.
intros.
untie.
Qed.

Example example_subst_3: forall (x: nat),
 x = 1 -> 2 <> x.
Proof.
intros.
untie.
Qed.

Example example_untie_neq: 5 <> 4.
Proof.
intros.
untie.
Qed.

Example example_untie_not: forall (x: nat), 
  x = 4 -> ~ (5 = 4).
Proof.
intros.
untie.
Qed.

Example example_untie_double_neq: 5 <> 5 -> False.
Proof.
untie.
Qed.