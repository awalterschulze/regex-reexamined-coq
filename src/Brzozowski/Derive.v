Require Import List.
Import ListNotations.

Require Import CoqStock.WreckIt.
Require Import CoqStock.Listerine.
Require Import CoqStock.Invs.

Require Import Brzozowski.Alphabet.
Require Import Brzozowski.Delta.
Require Import Brzozowski.Regex.
Require Import Brzozowski.Sequences.

(* D_a R = {t | a.t \in R} *)
Definition derive_seqs (R: seqs) (a: alphabet) (t: seq): Prop :=
  (a :: t) `elem` R.

(* Alternative inductive predicate for derive_seqs *)
Inductive derive_seqs' (R: seqs) (a: alphabet) (t: seq): Prop :=
  | mk_derive_seqs:
    (a :: t) `elem` R ->
    t `elem` (derive_seqs' R a)
  .

Definition seqs_eq (s1 s2: seqs): Prop :=
   forall (s: seq),
   s `elem` s1 <-> s `elem` s2.

Notation "s1 `seqs_eq` s2" := (seqs_eq s1 s2) (at level 80).

Theorem derive_seqs_emptyset_a0:
    derive_seqs {{ emptyset }} a0
    `seqs_eq`
    {{ emptyset }}.
Proof.
unfold seqs_eq.
intros.
split.
- intros.
  inversion_clear H.
- intros.
  inversion_clear H.
Qed.

Theorem derive_seqs_lambda_a0:
    derive_seqs {{ lambda }} a0
    `seqs_eq`
    {{ emptyset }}.
Proof.
unfold seqs_eq.
split.
- intros.
  inversion_clear H.
  discriminate.
- intros.
  inversion_clear H.
Qed. 

Theorem derive_seqs_symbol_a0:
    derive_seqs {{ symbol a0 }} a0
    `seqs_eq`
    {{ lambda }}.
Proof.
unfold seqs_eq.
split.
- intros.
  inversion_clear H.
  constructor.
  listerine.
- intros.
  inversion_clear H.
  apply mk_derive_seqs.
  constructor.
  subst.
  reflexivity.
Qed.

Theorem derive_seqs_symbol_a1:
    derive_seqs {{ symbol a0 }} a1
    `seqs_eq`
    {{ emptyset }}.
Proof.
unfold seqs_eq.
split.
- intros.
  inversion_clear H.
  listerine.
- intros.
  inversion_clear H.
Qed.

Theorem derive_seqs_star_a0:
  derive_seqs {{ star (symbol a0) }} a0
  `seqs_eq`
  {{ star (symbol a0) }}.
Proof.
split.
- intros.
  inversion_clear H.
  + inversion H0.
  + inversion H0.
    wreckit.
    inversion L.
    listerine.
    assumption.
- intros.
  inversion_clear H.
  + apply mk_star_more.
    subst.
    constructor.
    exists [a0].
    exists [].
    exists eq_refl.
    split.
    * constructor. reflexivity.
    * apply mk_star_zero.
      reflexivity.
  + inversion_clear H0.
    wreckit.
    subst.
    unfold derive_seqs.
    cbn.
    apply mk_star_more.
    inversion L.
    subst.
    constructor.
    exists [a0].
    exists (a0 :: x0).
    exists eq_refl.
    split.
    -- constructor. reflexivity.
    -- apply mk_star_more.
       constructor.
       exists [a0].
       exists x0.
       exists eq_refl.
       split.
       ++ constructor. reflexivity.
       ++ cbn in R.
          exact R.
Qed.

Fixpoint delta_def (r: regex): regex :=
match r with
| emptyset => emptyset
| lambda => lambda
| symbol _ => emptyset
| concat s t => match (delta_def s, delta_def t) with
  | (lambda, lambda) => lambda
  | _ => emptyset
  end
| star s => lambda
| nor s t => 
    match (delta_def s, delta_def t) with
    | (emptyset, emptyset) => lambda
    | _ => emptyset
    end
end.

Fixpoint derive_def (r: regex) (a: alphabet) : regex :=
  match r with
  | emptyset => emptyset
  | lambda => emptyset
  | symbol b => 
    if (eqa b a)
    then lambda
    else emptyset
  | concat s t =>
    or (concat (derive_def s a) t) 
       (concat (delta_def s) (derive_def t a))
  | star s => concat (derive_def s a) (star s)
  | nor s t => nor (derive_def s a) (derive_def t a)
  end.

Theorem emptyset_terminates: forall (a: alphabet),
  derive_seqs emptyset_seqs a `seqs_eq` emptyset_seqs.
Proof.
intros.
split.
- intros.
  inversion H.
- intros.
  inversion H.
Qed.  

Theorem commutes_emptyset: forall (a: alphabet),
  derive_seqs {{ emptyset }} a
  `seqs_eq`
  {{ derive_def emptyset a }}.
Proof.
intros.
cbn.
apply emptyset_terminates.
Qed.

Theorem commutes_lambda: forall (a: alphabet),
  derive_seqs {{ lambda }} a
  `seqs_eq`
  {{ derive_def lambda a }}.
Proof.
intros.
split.
- intros.
  inversion H.
  discriminate.
- intros.
  inversion H.
Qed.

Theorem commutes_symbol: forall (a b: alphabet),
  derive_seqs {{ symbol b }} a
  `seqs_eq`
  {{ derive_def (symbol b) a }}.
Proof.
intros.
split; intros.
- inversion H.
  subst.
  destruct a, b; cbn.
  + constructor.
    listerine.
  + discriminate.
  + discriminate.
  + constructor.
    listerine.
- destruct a, b; cbn in H.
  + invs H. constructor. reflexivity.
  + inversion H.
  + inversion H.
  + invs H. constructor. reflexivity.
Qed.   


Theorem commutes: forall (r: regex) (a: alphabet),
  derive_seqs {{ r }} a
  `seqs_eq`
  {{ derive_def r a }}.
Proof.
intros.
induction r.
- apply commutes_emptyset.
- 
  
