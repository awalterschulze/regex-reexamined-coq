Require Import CoqStock.Invs.
Require Import CoqStock.List.

Require Import Brzozowski.Alphabet.
Require Import Brzozowski.Derive.
Require Import Brzozowski.Language.

CoInductive bisimilar : lang -> lang -> Prop :=
  | bisim : forall (P Q: lang),
      ([] \in P <-> [] \in Q)
    /\
      (forall (a: alphabet),
        bisimilar (derive_lang_a P a) (derive_lang_a Q a)
      )
    -> bisimilar P Q.

Notation "P <<->> Q" := (bisimilar P Q) (at level 80).

Lemma equivalence_impl_derive_lang_a_is_equivalent:
    forall (P Q: lang) (a: alphabet),
    P {<->} Q ->
    derive_lang_a P a {<->} derive_lang_a Q a.
Proof.
unfold lang_iff.
intros.
unfold derive_lang_a.
unfold elem.
specialize H with (s := (a :: s)).
assumption.
Qed.

Lemma equivalence_impl_bisimilar:
  forall (P Q: lang),
  P {<->} Q -> P <<->> Q.
Proof.
cofix G.
intros.
constructor.
unfold lang_iff in H.
split.
- apply H.
- intros.
  apply G.
  apply equivalence_impl_derive_lang_a_is_equivalent.
  assumption.
Qed.

Lemma fold_derive_lang_a:
  forall (R: lang) (a: alphabet) (s: str),
  (a :: s) \in R <-> s \in (derive_lang_a R a).
Proof.
intros.
unfold derive_lang_a.
unfold elem.
reflexivity.
Qed.

Lemma bisimilar_impl_equivalence:
  forall (P Q: lang),
  P <<->> Q -> P {<->} Q.
Proof.
unfold lang_iff.
intros.
generalize dependent P.
generalize dependent Q.
induction s.
- intros.
  inversion H.
  destruct H0.
  assumption.
- intros.
  inversion H.
  destruct H0.
  specialize H3 with (a := a).
  subst.
  rewrite (fold_derive_lang_a P a s).
  rewrite (fold_derive_lang_a Q a s).
  apply IHs.
  assumption.
Qed.

Theorem bisimilar_is_equivalence:
  forall (P Q: lang),
  P <<->> Q <-> P {<->} Q.
Proof.
split.
- apply bisimilar_impl_equivalence.
- apply equivalence_impl_bisimilar.
Qed.