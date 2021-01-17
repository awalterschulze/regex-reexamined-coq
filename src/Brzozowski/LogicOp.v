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

Definition nor_lang (P Q: lang) : lang :=
  neg_lang (or_lang P Q).

Definition and_lang (P Q: lang) : lang :=
  neg_lang (or_lang (neg_lang P) (neg_lang Q)).

Lemma denote_regex_or_step:
  forall (p q: regex),
  {{nor p q}} {<->} nor_lang {{p}} {{q}}.
Proof.
  intros.
  cbn.
  unfold nor_lang.
  reflexivity.
Qed.

Lemma denote_regex_and_step:
  forall (p q: regex),
  {{and p q}} {<->} and_lang {{p}} {{q}}.
Proof.
  intros.
  cbn.
  unfold and_lang.
  reflexivity.
Qed.

Theorem and_lang_is_conj:
  forall (p q: regex) (s: str),
  s \in and_lang {{p}} {{q}} <-> s \in {{p}} /\ s \in {{q}}.
Proof.
intros.
unfold and_lang.
specialize denotation_is_decidable with (r := p) (s := s) as Dp.
specialize denotation_is_decidable with (r := q) (s := s) as Dq.
destruct Dp, Dq; split; intros; split; try assumption.
- untie. 
  invs H2.
  invs H3; invs H2; contradiction. 
- invs H1.
  exfalso.
  apply H2.
  constructor.
  right.
  constructor.
  assumption.
- untie.
  invs H2.
  invs H1.
  contradiction.
- invs H1.
  exfalso.
  apply H2.
  constructor.
  left.
  constructor.
  assumption.
- untie.
  invs H2.
  invs H1.
  contradiction.
- invs H1.
  exfalso.
  apply H2.
  constructor.
  left.
  constructor.
  assumption.
- invs H1.
  exfalso.
  apply H2.
  constructor.
  left.
  constructor.
  assumption.
- invs H1.
  contradiction.
Qed.

Add Parametric Morphism: nor_lang
  with signature lang_iff ==> lang_iff ==> lang_iff as nor_lang_morph.
Proof.
intros.
unfold nor_lang.
rewrite H.
rewrite H0.
reflexivity.
Qed.

Existing Instance nor_lang_morph_Proper.

Add Parametric Morphism: and_lang
  with signature lang_iff ==> lang_iff ==> lang_iff as and_lang_morph.
Proof.
intros.
unfold and_lang.
rewrite H.
rewrite H0.
reflexivity.
Qed.

Existing Instance and_lang_morph_Proper.

Theorem nor_denotes_nor_lang:
  forall (p q: regex),
  {{nor p q}} {<->} nor_lang {{p}} {{q}}.
Proof.
intros.
split.
- intros.
  cbn in *.
  unfold nor_lang.
  assumption.
- intros.
  cbn in *.
  unfold nor_lang in H.
  assumption.
Qed.
