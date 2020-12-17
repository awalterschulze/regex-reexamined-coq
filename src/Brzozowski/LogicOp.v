Require Import Coq.Setoids.Setoid.

Require Import CoqStock.Untie.
Require Import CoqStock.WreckIt.

Require Import Brzozowski.Decidable.
Require Import Brzozowski.Language.
Require Import Brzozowski.Regex.
Require Import Brzozowski.Setoid.

(* We chose to include `nor`, since it can represent any possible boolean expression,
   which is one of the selling points of Brzozowski's derivatives for regular expressions.
*)

Definition complement (r: regex) : regex :=
  nor r r.

Definition and (r s: regex) : regex :=
  nor (nor r r) (nor s s).

Definition or (r s: regex) : regex :=
  nor (nor r s) (nor r s).

Definition xor (r s: regex) : regex :=
  or (and r (complement s)) (and (complement r) s).

(* I matches all strings *)
Definition I: regex :=
  complement (emptyset).

Definition not_lang (R: lang) : lang :=
  nor_lang R R.

Definition and_lang (P Q: lang) : lang :=
  nor_lang (nor_lang P P) (nor_lang Q Q).

Definition or_lang (P Q: lang) : lang :=
  nor_lang (nor_lang P Q) (nor_lang P Q).

Lemma denote_regex_or_step:
  forall (p q: regex),
  {{or p q}} {<->} or_lang {{p}} {{q}}.
Proof.
  intros.
  cbn.
  unfold or_lang.
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

Lemma denote_regex_complement_step:
  forall (r: regex),
  {{complement r}} {<->} not_lang {{r}}.
Proof.
  intros.
  cbn.
  unfold not_lang.
  reflexivity.
Qed.

Add Parametric Morphism: or_lang
  with signature lang_iff ==> lang_iff ==> lang_iff as or_lang_morph.
Proof.
intros.
unfold or_lang.
rewrite H.
rewrite H0.
reflexivity.
Qed.

Existing Instance or_lang_morph_Proper.

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

Add Parametric Morphism: not_lang
  with signature lang_iff ==> lang_iff as not_lang_morph.
Proof.
intros.
unfold not_lang.
rewrite H.
reflexivity.
Qed.

Existing Instance not_lang_morph_Proper.

Theorem or_denotes_or_lang:
  forall (p q: regex),
  {{or p q}} {<->} or_lang {{p}} {{q}}.
Proof.
intros.
split.
- intros.
  cbn in *.
  unfold or_lang.
  assumption.
- intros.
  cbn in *.
  unfold or_lang in H.
  assumption.
Qed.

Theorem or_lang_is_disj:
  forall (p q: regex) (s: str),
  s `elem` or_lang {{p}} {{q}} <-> s `elem` {{p}} \/ s `elem` {{q}}.
Proof.
intros.
split.
- intros.
  destruct H.
  destruct H.
  clear H0.
  unfold elem in H.
  destruct (denotation_is_decidable p s);
  destruct (denotation_is_decidable q s);
  auto.
  + exfalso. apply H. constructor. split; assumption.
- intros.
  constructor.
  split; destruct H; unfold elem; untie;
  destruct H0; wreckit; contradiction.
Qed.

Theorem or_is_disj:
  forall (p q: regex) (s: str),
  s `elem` {{ or p q }} <-> s `elem` {{p}} \/ s `elem` {{q}}.
Proof.
intros.
specialize or_denotes_or_lang with (p := p) (q := q).
intros or_is_or_lang.
unfold lang_iff in or_is_or_lang.
specialize or_is_or_lang with (s := s).
rewrite or_is_or_lang.
rewrite or_lang_is_disj.
reflexivity.
Qed.
