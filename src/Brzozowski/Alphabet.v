(* Alphabet is Sigma_k *)
(* We are defining it here as a1 and x0, but we could do any disjoint set *)
Inductive alphabet := a0 | a1.

Lemma alphabet_disjoint: forall (x y: alphabet),
  x = y \/ x <> y.
Proof.
(* This is the exact usecase for the decide equality tactic.
   It only works when the type of x and y is a simple inductive type.
*)
decide equality.
Qed.

Lemma alphabet_disjoint': forall (x y: alphabet),
  x = y \/ x <> y.
Proof.
destruct x, y.
- left. reflexivity.
- right. discriminate.
- right. discriminate.
- left. reflexivity.
Qed. 

Definition eqa (x y: alphabet): bool :=
  match (x, y) with
  | (a0, a0) => true
  | (a1, a1) => true
  | _ => false
  end.