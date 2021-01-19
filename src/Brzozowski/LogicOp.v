Require Import Coq.Setoids.Setoid.

Require Import CoqStock.Invs.
Require Import CoqStock.Untie.
Require Import CoqStock.WreckIt.

Require Import Brzozowski.Decidable.
Require Import Brzozowski.Language.
Require Import Brzozowski.Regex.
Require Import Brzozowski.Setoid.

(* We chose to include `nor`, since it can represent any possible boolean expression,
   which is one of the selling points of Brzozowski's derivatives for regular expressions.
*)

Definition nor (r s: regex) : regex :=
  neg (or r s).

Definition and (r s: regex) : regex :=
  neg (or (neg r) (neg s)).

Definition xor (r s: regex) : regex :=
  or (and r (neg s)) (and (neg r) s).

(* I matches all strings *)
Definition I: regex :=
  neg (emptyset).

Inductive nor_lang (P Q: lang): lang :=
  | mk_nor : forall s,
    s \notin P /\ s \notin Q ->
    nor_lang P Q s.

Inductive and_lang (P Q: lang): lang :=
  | mk_and : forall s,
    s \in P /\ s \in Q ->
    and_lang P Q s.

Lemma nor_denotes_nor_lang:
  forall (p q: regex),
  {{nor p q}} {<->} nor_lang {{p}} {{q}}.
Proof.
intros.
cbn.
split; intros.
- specialize denotation_is_decidable with (s := s) (r := p) as Dp.
  specialize denotation_is_decidable with (s := s) (r := q) as Dq.
  invs H.
  constructor.
  split.
  + destruct Dp.
    * exfalso.
      apply H0.
      constructor.
      left.
      assumption.
    * assumption.
  + destruct Dq.
    * exfalso.
      apply H0.
      constructor.
      right.
      assumption.
    * assumption.
- constructor.
  invs H.
  untie.
  invs H.
  invs H0.
  invs H1; contradiction.
Qed.

Lemma and_denotes_and_lang:
  forall (p q: regex),
  {{and p q}} {<->} and_lang {{p}} {{q}}.
Proof.
intros.
cbn.
split.
- intros.
  specialize denotation_is_decidable with (r := p) (s := s) as Dp.
  specialize denotation_is_decidable with (r := q) (s := s) as Dq.
  destruct Dp, Dq.
  + constructor. auto.
  + constructor.
    split.
    * assumption.
    * exfalso.
      invs H.
      apply H2.
      constructor.
      right.
      constructor.
      assumption.
  + constructor.
    split.
    * exfalso.
      invs H.
      apply H2.
      constructor.
      left.
      constructor.
      assumption.
    * assumption.
  + exfalso.
    invs H.
    apply H2.
    constructor.
    left.
    constructor.
    assumption.
- intros.
  invs H.
  destruct H0.
  constructor.
  untie.
  invs H1.
  invs H2.
  + invs H1.
    contradiction.
  + invs H1.
    contradiction.
Qed.

Add Parametric Morphism: nor_lang
  with signature lang_iff ==> lang_iff ==> lang_iff as nor_lang_morph.
Proof.
intros.
unfold lang_iff in *.
intros.
specialize H with (s := s).
specialize H0 with (s := s).
split; intros.
- constructor.
  invs H1.
  destruct H2.
  rewrite H in H1.
  rewrite H0 in H2.
  auto.
- constructor.
  invs H1.
  destruct H2.
  rewrite <- H in H1.
  rewrite <- H0 in H2.
  auto.
Qed.

Existing Instance nor_lang_morph_Proper.

Add Parametric Morphism: and_lang
  with signature lang_iff ==> lang_iff ==> lang_iff as and_lang_morph.
Proof.
intros.
unfold lang_iff in *.
intros.
specialize H with s.
specialize H0 with s.
split; intros.
- invs H1.
  constructor.
  rewrite <- H.
  rewrite <- H0.
  auto.
- invs H1.
  constructor.
  rewrite H.
  rewrite H0.
  auto.
Qed.

Existing Instance and_lang_morph_Proper.

Theorem or_denotes_or_lang:
  forall (p q: regex),
  {{or p q}} {<->} or_lang {{p}} {{q}}.
Proof.
  intros.
  split; intros; constructor; inversion H; assumption.
Qed.

Theorem neg_denotes_neg_lang:
  forall (p : regex),
  {{neg p}} {<->} neg_lang {{p}}.
Proof.
  intros.
  split; intros; constructor; inversion H; assumption.
Qed.