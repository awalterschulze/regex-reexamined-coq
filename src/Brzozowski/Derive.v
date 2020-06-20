Require Import List.
Import ListNotations.

Require Import CoqStock.Listerine.
Require Import CoqStock.Invs.
Require Import CoqStock.Untie.
Require Import CoqStock.WreckIt.

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
- intros.
  inversion_clear H.
  apply mk_derive_seqs.
  constructor.
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
    * constructor.
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
    -- constructor.
    -- apply mk_star_more.
       constructor.
       exists [a0].
       exists x0.
       exists eq_refl.
       split.
       ++ constructor.
       ++ cbn in R.
          exact R.
Qed.

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
  destruct a; cbn.
  + constructor.
  + constructor.
- destruct a, b; cbn in H.
  + invs H. constructor.
  + inversion H.
  + inversion H.
  + invs H. constructor.
Qed.

Theorem commutes_concat: forall (s t: regex) (a: alphabet),
  derive_seqs {{s}} a `seqs_eq` {{derive_def s a}} ->
  derive_seqs {{t}} a `seqs_eq` {{derive_def t a}} ->
  derive_seqs {{ concat s t }} a
  `seqs_eq`
  {{ derive_def (concat s t) a }}.
Proof.
intros.
split; intros.
- invs H1. wreckit. cbn. constructor. wreckit.
  untie.
  invs H1.
  wreckit.
  listerine.
  apply delta_lambda in L.
  apply delta_implies_delta_def in L.
  + apply H0 in R.
    apply R0.
    constructor.
    exists [].
    exists s0.
    exists eq_refl.
    split.
    * rewrite L.
      constructor.
    * assumption.
  + apply H in L.
    apply L0.
    constructor.
    exists L1.
    exists x0.
    exists eq_refl.
    split.
    * assumption.
    * assumption.
- cbn.
  inversion_clear H1.
  wreckit.
  induction s.
  + exfalso. apply R.
    constructor.
    split.
    * untie.
      inversion_clear H1.
      wreckit.
      inversion L0.
    * untie.
      inversion_clear H1.
      wreckit.
      inversion L0.
  + constructor.
    exists [].
    exists (a :: s0).
    exists eq_refl.
    split.
    * constructor.
    * induction t.
      -- exfalso.
         apply R.
         constructor.
         split.
         ++ untie.
            inversion H1.
            wreckit.
            inversion R0.
         ++ untie.
            inversion H1.
            wreckit.
            inversion R0.
      -- exfalso.
         apply R.
         constructor.
         split.
         ++ untie.
            inversion H1.
            wreckit.
            inversion L0.
         ++ untie.
            inversion H1.
            wreckit.
            inversion R0.
      -- destruct s0.
         ++ destruct a.
            ** exfalso.
               apply R.
               constructor.
               split.
               --- untie.
                   inversion H1.
                   wreckit.
                   inversion L0.
               --- untie.
                   inversion H1.
                   wreckit.
                   inversion L0.
                   listerine.
                   wreckit.
                   subst.
                   cbn in R0.
                   destruct a0.
                   +++ inversion R0. 

                   inversion R1.
                   cbn in R0.
                   inversion R0. 

  

   
   
  




Theorem commutes: forall (r: regex) (a: alphabet),
  derive_seqs {{ r }} a
  `seqs_eq`
  {{ derive_def r a }}.
Proof.
intros.
induction r.
- apply commutes_emptyset.
- apply commutes_lambda.
- apply commutes_symbol.
-   
  
