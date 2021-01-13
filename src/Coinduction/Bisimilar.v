Require Import Coq.micromega.Lia.

Require Import CoqStock.Untie.
Require Import CoqStock.List.

Require Import Brzozowski.Alphabet.
Require Import Brzozowski.Decidable.
Require Import Brzozowski.Derive.
Require Import Brzozowski.Language.
Require Import Brzozowski.LogicOp.
Require Import Brzozowski.Regex.

CoInductive bisimilar : lang -> lang -> Prop :=
  | bisim : forall (s s': lang),
      ([] \in s <-> [] \in s')
    /\
      (forall (a: alphabet),
        bisimilar (derive_lang_a s a) (derive_lang_a s' a)
      )
    -> bisimilar s s'.

Lemma equivalence_impl_derive_lang_a_is_equivalent:
    forall (l l': lang) (a: alphabet),
    l {<->} l' ->
    derive_lang_a l a {<->} derive_lang_a l' a.
Proof.
unfold lang_iff.
intros.
unfold derive_lang_a.
unfold elem.
specialize H with (s := (a :: s)).
assumption.
Qed.

Lemma equivalence_impl_bisimilar:
  forall (l l': lang),
  l {<->} l' -> bisimilar l l'.
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
  forall (l: lang) (a: alphabet) (s: str),
  (a :: s) \in l <-> s \in (derive_lang_a l a).
Proof.
intros.
unfold derive_lang_a.
unfold elem.
reflexivity.
Qed.

Lemma bisimilar_impl_equivalence:
  forall (l l': lang),
  bisimilar l l' -> l {<->} l'.
Proof.
unfold lang_iff.
intros.
generalize dependent l.
generalize dependent l'.
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
  rewrite (fold_derive_lang_a l a s).
  rewrite (fold_derive_lang_a l' a s).
  apply IHs.
  assumption.
Qed.

Theorem bisimilar_is_equivalence:
  forall (l l': lang),
  bisimilar l l' <-> l {<->} l'.
Proof.
split.
- apply bisimilar_impl_equivalence.
- apply equivalence_impl_bisimilar.
Qed.

Theorem star_star_bisimilar: forall (r: lang),
  bisimilar
  (star_lang r)
  (star_lang (star_lang r)).
Proof.
(* TODO: Help Wanted *)
Abort.

Theorem or_lang_commutativity_bisimilar: forall (a b: lang),
  bisimilar
  (or_lang a b)
  (or_lang b a).
Proof.
(* TODO: Help Wanted *)
Abort.

Theorem concat_lang_assoc_bisimilar: forall (a b c: lang),
  bisimilar
  (concat_lang a (concat_lang b c))
  (concat_lang (concat_lang a b) c).
Proof.
(* TODO: Help Wanted *)
Abort.

Theorem concat_lang_emptyset_l_bisimilar_emptyset: forall (r: lang),
    bisimilar
    (concat_lang emptyset_lang r)
    emptyset_lang.
Proof.
(* TODO: Help Wanted *)
Abort.