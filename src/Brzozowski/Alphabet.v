(* Alphabet is Sigma_k *)
(* We are defining it here as A1 and A0, but we could do any disjoint set *)
Inductive alphabet := A0 | A1.

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
  | (A0, A0) => true
  | (A1, A1) => true
  | _ => false
  end.

Definition compare_alphabet (x y: alphabet): comparison :=
  match (x, y) with
  | (A0, A0) => Eq
  | (A1, A1) => Eq
  | (A0, A1) => Lt
  | (A1, A0) => Gt
  end.