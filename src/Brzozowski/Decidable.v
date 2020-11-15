Require Import Coq.micromega.Lia.

Require Import CoqStock.DubStep.
Require Import CoqStock.Invs.
Require Import CoqStock.List.
Require Import CoqStock.Listerine.
Require Import CoqStock.Untie.
Require Import CoqStock.WreckIt.

Require Import Brzozowski.Alphabet.
Require Import Brzozowski.ConcatLang.
Require Import Brzozowski.Language.
Require Import Brzozowski.Regex.

Definition regex_is_decidable (r: regex) :=
  (forall s: str, s `elem` {{r}} \/ s `notelem` {{r}}).

Lemma star_lang_a_split_matches:
  forall (r: regex) (s: str) (s_is_not_empty: s <> []),
    s `elem` {{ star r }}
  <->
  (exists (index: nat) (index_range : 0 < index <= length s),
    let prefix := firstn index s in
    let suffix := skipn index s in
    (prefix `elem` {{r}} /\ suffix `elem` {{star r}})).
Proof.
intros.
split.
- intro s_elem_star_r.
  destruct s_elem_star_r.
  + contradiction.
  + exists (length p).
    exists (prefix_is_gt_zero_and_leq p q s H0 H).
    intros.
    unfold prefix.
    unfold suffix.
    rewrite <- H.
    rewrite (firstn_length_prefix_is_prefix p q).
    rewrite (skipn_length_prefix_is_suffix p q).
    split; assumption.
- intros split_of_star_r.
  destruct split_of_star_r as [index [index_range [prefix_r suffix_r]]].
  apply (mk_star_more {{r}} s (firstn index s) (skipn index s)).
  + auto with list.
  + now apply prefix_is_not_empty_with_index_gt_zero.
  + assumption.
  + assumption.
Qed.

Lemma star_lang_no_split_matches:
  forall (r: regex) (s: str) (s_is_not_empty: s <> []),
  s `notelem` {{ star r }}
  <->
  (forall (index: nat) (index_range : 0 < index <= length s),
     let prefix := firstn index s in
     let suffix := skipn index s in
     (not (prefix `elem` {{r}} /\ suffix `elem` {{star r}}))).
Proof.
intros.
split.
- intros s_not_elem_star_r.
  intros index index_range.
  intros.
  untie.
  unfold not in s_not_elem_star_r.
  destruct H as [prefixr suffixr].
  apply s_not_elem_star_r.
  apply (mk_star_more {{r}} s (firstn index s) (skipn index s)).
  + auto with list.
  + now apply prefix_is_not_empty_with_index_gt_zero.
  + assumption.
  + assumption.
- intros split_of_not_star_r.
  untie.
  destruct H.
  + contradiction.
  + set (prefix_is_gt_zero_and_leq p q s H0 H) as p_range.
    set (split_of_not_star_r (length p) p_range) as specialized_split_of_not_star_r.
    apply specialized_split_of_not_star_r.
    split.
    * rewrite <- H.
      rewrite firstn_length_prefix_is_prefix.
      assumption.
    * rewrite <- H.
      rewrite skipn_length_prefix_is_suffix.
      assumption.
Qed.

Theorem star_lang_a_split_matches_or_no_split_matches:
  forall (r: regex) (s: str) (s_is_not_empty: s <> []),
    s `elem` {{star r}}
  \/
    s `notelem` {{star r}}
  <->
    (exists (index: nat) (index_range : 0 < index <= length s),
      (firstn index s `elem` {{r}} /\ skipn index s `elem` {{star r}}))
  \/
    (forall (index: nat) (index_range : 0 < index <= length s),
      (not (firstn index s `elem` {{r}} /\ skipn index s `elem` {{star r}}))).
Proof.
intros.
destruct (star_lang_a_split_matches r s s_is_not_empty).
destruct (star_lang_no_split_matches r s s_is_not_empty).
(* This theorem clearly follows by the above theorems. *)
split; intros decide; destruct decide; eauto.
Qed.

Lemma breakdown_leq (n: nat):
  forall i: nat, i <= S n -> i <= n \/ i = S n.
Proof.
  intros.
  lia.
Qed.

Lemma deciding_for_all_elements_in_finite_sets (P: nat -> Prop) (n: nat):
  (forall (i : nat), i <= n -> (P i \/ ~ (P i))) ->
  ((forall (i: nat), i <= n -> ~ (P i)) \/ (exists (i: nat) (pi: i <= n), P i)).
Proof.
   intro.
    induction n.
    + specialize H with (i := 0).
      assert (0 <= 0) as ofcourse by lia.
      destruct (H ofcourse).
      * right.
        exists 0.
        split; assumption.
      * left.
        intros.
        assert (i = 0) by lia.
        subst.
        assumption.
    + assert (forall i : nat, i <= n -> P i \/ ~ P i) as Hsmaller.
      * intros.
        apply H.
        lia.

      * apply IHn in Hsmaller.
        destruct Hsmaller.
        -- assert (S n <= S n) as eq_so_leq by lia.
           destruct (H (S n) eq_so_leq).
           ++ right.
              exists (S n).
              split; assumption.
           ++ left.
              intros i ibounded.
              destruct (breakdown_leq n i ibounded).
              ** apply H0.
                 assumption.
              ** subst.
                 assumption.
        -- right.
           destruct H0 as [i [ibounded imatch]].
           exists i.
           split.
           ++ lia.
           ++ assumption.
Qed.

Lemma breakdown_leq_one (n: nat):
  forall i: nat, 0 < i <= S n -> 0 < i <= n \/ i = S n.
Proof.
  intros.
  lia.
Qed.

Theorem deciding_for_all_elements_of_non_empty_finite_sets (P: nat -> Prop) (n: nat):
  (forall (i : nat), 0 < i <= n -> (P i \/ ~ (P i))) ->
  ((forall (i: nat), 0 < i <= n -> ~ (P i)) \/ (exists (i: nat) (pi: 0 < i <= n), P i)).
Proof.
  intro.
  induction n.
  + left.
    intros.
    lia.
  + assert (forall i : nat, 0 < i <= n -> P i \/ ~ P i) as Hsmaller.
    * intros.
      apply H.
      lia.
    * apply IHn in Hsmaller.
      destruct Hsmaller.
      -- assert (0 < S n <= S n) as eq_so_leq by lia.
         destruct (H (S n) eq_so_leq).
         ++ right.
            exists (S n).
            split; assumption.
         ++ left.
            intros i ibounded.
            destruct (breakdown_leq_one n i ibounded).
            ** apply H0.
               assumption.
            ** subst.
               assumption.
      -- right.
         destruct H0 as [i [ibounded imatch]].
         exists i.
         split.
         ++ lia.
         ++ assumption.
Qed.

Lemma denotation_star_is_decidable_helper (r: regex) (n: nat):
  regex_is_decidable r ->
  (forall
    (s: str)
    (range: length s <= n),
    (s `elem` {{star r}} \/ s `notelem` {{star r}})
  ).
Proof.
intros.
generalize dependent s.
induction n.
- left.
  apply length_zero_or_smaller_string_is_empty in range.
  rewrite range.
  constructor.
- intros s max_length_S.
  unfold regex_is_decidable in H.
  destruct s.
  + left. constructor.
  + assert (a :: s <> []) as a_is_not_empty; listerine.
    apply (star_lang_a_split_matches_or_no_split_matches r (a :: s) a_is_not_empty).
    rewrite or_comm.
    apply deciding_for_all_elements_of_non_empty_finite_sets with (n := (length (a :: s))).
    intros.
    set (prefix := firstn i (a :: s)).
    set (suffix := skipn i (a :: s)).
    specialize H with prefix.
    specialize IHn with suffix.
    assert (length suffix <= n).
    * unfold suffix.
      destruct H0.
      rewrite skipn_length.
      lia.
    * apply IHn in H1.
      clear IHn max_length_S a_is_not_empty H0.
      destruct H, H1.
      --- left. auto.
      --- right. untie. destruct H1. contradiction.
      --- right. untie. destruct H1. contradiction.
      --- right. untie. destruct H1. contradiction.
Qed.

Lemma denotation_star_is_decidable (r: regex):
  regex_is_decidable r ->
  regex_is_decidable (star r).
Proof.
unfold regex_is_decidable.
intro Hr.
intro s.
apply (denotation_star_is_decidable_helper r (length s) Hr).
lia.
Qed.

Definition no_splitting_is_an_elem_for_length (p q: regex) (s: str) (n: nat) :=
  forall (s1 s2: str),
  s = s1 ++ s2 ->
  length s1 <= n ->
  ((s1 `notelem` {{ p }} \/ s2 `notelem` {{ q }})).

Definition a_splitting_is_an_elem_for_length (p q: regex) (s: str) (n: nat) :=
  exists (s1 s2: str),
  s = s1 ++ s2 /\
  length s1 <= n /\
  (s1 `elem` {{ p }} /\ s2 `elem` {{ q }}).

Lemma denotation_concat_is_decidable_helper (p q: regex):
  regex_is_decidable p ->
  regex_is_decidable q ->
  (forall (s: str) (n : nat),
    no_splitting_is_an_elem_for_length p q s n
    \/ a_splitting_is_an_elem_for_length p q s n
  ).
Proof.
  intros Hdecp Hdecq s n.
  induction n.
  - (* case that s1 is empty string *)
    destruct (Hdecp []) as [Hpmatches | Hpnomatch]; destruct (Hdecq s) as [Hqmatches | Hqnomatch].


    2,3,4: left; intros s1 s2 Hconcat Hlen';
      (* this could maybe use some refactoring.
         But in principle it is simple: I want to do exactly this
         for goals 2,3 and 4.
       *)
      (* now starts: we know what it is when it is split *)
      assert (s1 = []) by (apply length_zero_or_smaller_string_is_empty; assumption);
      assert (s2 = s) by (replace (s1 ++ s2) with s2 in Hconcat by (subst; auto);
                          symmetry;
                          assumption);
      clear Hconcat;
      clear Hlen';
      subst;
      try (now left);
      try (now right).

    + (* this is the case where in fact s matches q, [] matches p *)
      right.
      exists [].
      exists s.
      intros.
      auto.

  - (* induction step *)
    set (l1 := firstn (S n) s).
    set (l2 := skipn (S n) s).

    (* case distinction on the induction hyptohesis (which is an or) *)
    destruct IHn as [IHnAllNoMatch | IHnExistsMatch ].

    (* The case where there is already a match with a smaller split. *)
    2: {
    right.
    destruct IHnExistsMatch as [s1 IHn1].
    destruct IHn1 as [s2 IHn].
    exists s1. exists s2.
    destruct IHn as [H0 [H1 [H2 H3]]].
    repeat split; try assumption.
    lia. }


    (* If none of the earlier splits match. *)
    destruct (Hdecp l1) as [Hpmatch | Hpnomatch].
      destruct (Hdecq l2) as [Hqmatch | Hqnomatch ].

      2,3: left;
      intros s1 s2 Hconcat Hlen;
      assert (length s1 <= n \/ length s1 = S n) as Hlen' by lia;
      destruct Hlen' as [Hlen' | Hlen'];
      try (apply IHnAllNoMatch; assumption); (* case length s1 <= n *)
      try (
          destruct (split_list s (S n) s1 s2 Hlen' Hconcat) as [Hfoo Hbar];

          replace l1 with s1 in * by auto;
          replace l2 with s2 in * by auto;
          subst;
          try (left; assumption);
          try (right; assumption)).


    + right. exists l1. exists l2. intros.

      repeat split; try assumption.

      * symmetry. apply firstn_skipn.
      * apply firstn_le_length.


        (* The proof below is the proof for 2,3, but written with periods instead of semicolons...
           the periods are easier to step through, and it is also how I wrote it.
           But as I've said above, I don't know how to do that for 2 goals at the same time.

         *)
        (*
    +
      left.
      intros s1 s2 Hconcat Hlen.

      assert (length s1 <= n \/ length s1 = S n) as Hlen' by lia.
      destruct Hlen' as [Hlen' | Hlen'].

      * apply IHnAllNoMatch; assumption. (* case length s1 <= n *)
      * destruct (split_string_lemma s (S n) s1 s2 Hlen' Hconcat) as [Hfoo Hbar].

        replace l1 with s1 in * by auto.
        replace l2 with s2 in * by auto.
        subst.
        try (left; assumption).
        try (right; assumption).
*)

Qed.

Lemma denotation_concat_is_decidable (p q: regex):
  regex_is_decidable p ->
  regex_is_decidable q ->
  regex_is_decidable (concat p q).
Proof.
  intros Hdecp Hdecq.
  unfold regex_is_decidable.
  intro s.
  destruct (denotation_concat_is_decidable_helper p q Hdecp Hdecq s (length s))
  as [HAllDontMatch | HExistsMatch].

  - right.
    unfold not.
    intro HmatchContr.
    destruct HmatchContr.
    symmetry in H.

    set (Hlen := prefix_leq_length s p0 q0 H).
    unfold no_splitting_is_an_elem_for_length in HAllDontMatch.
    specialize HAllDontMatch with p0 q0.
    destruct (HAllDontMatch H Hlen); auto.

  - left.
    destruct HExistsMatch as [s1 [s2 [Hconcat [Hlen [Hmatchp Hmatchq]]]]].
    symmetry in Hconcat.
    destruct_concat_lang.
    exists s1.
    exists s2.
    exists Hconcat.
    split; assumption.
Qed.

Theorem notelem_emptyset: forall (s: str),
  s `notelem` emptyset_lang.
Proof.
intros.
untie.
Qed.

Lemma denotation_emptyset_is_decidable (s: str):
  s `elem` {{ emptyset }} \/ s `notelem` {{ emptyset }}.
Proof.
right.
apply notelem_emptyset.
Qed.

Lemma denotation_lambda_is_decidable (s: str):
  s `elem` {{ lambda }} \/ s `notelem` {{ lambda }}.
Proof.
destruct s.
- left. constructor.
- right. untie. invs H.
Qed.

Lemma denotation_symbol_is_decidable (s: str) (a: alphabet):
  s `elem` {{ symbol a }} \/ s `notelem` {{ symbol a }}.
Proof.
destruct s.
- right. untie. invs H.
- destruct a, a0.
  + destruct s.
    * left.
      constructor.
    * right.
      untie.
      invs H.
  + right.
    untie.
    invs H.
  + right.
    untie.
    invs H.
  + destruct s.
    * left.
      constructor.
    * right.
      untie.
      invs H.
Qed.

Lemma denotation_nor_is_decidable (p q: regex) (s: str):
  s `elem` {{ p }} \/ s `notelem` {{ p }} ->
  s `elem` {{ q }} \/ s `notelem` {{ q }} ->
  s `elem` {{ nor p q }} \/ s `notelem` {{ nor p q }}.
Proof.
simpl.
intros.
wreckit.
- right.
  untie.
  invs H.
  wreckit.
  contradiction.
- right.
  untie.
  invs H.
  wreckit.
  contradiction.
- right.
  untie.
  invs H.
  wreckit.
  contradiction.
- left.
  constructor.
  wreckit.
  * assumption.
  * assumption.
Qed.

Lemma denotation_concat_is_decidable_for_empty_string (p q: regex):
  [] `elem` {{ p }} \/ [] `notelem` {{ p }} ->
  [] `elem` {{ q }} \/ [] `notelem` {{ q }} ->
  [] `elem` {{ concat p q }} \/ [] `notelem` {{ concat p q }}.
Proof.
intros.
wreckit.
- left.
  destruct_concat_lang.
  exists [].
  exists [].
  exists eq_refl.
  split; assumption.
- right.
  untie.
  invs H.
  wreckit.
  listerine.
  contradiction.
- right.
  untie.
  invs H.
  wreckit.
  listerine.
  contradiction.
- right.
  untie.
  invs H.
  wreckit.
  listerine.
  contradiction.
Qed.


Lemma denotation_star_is_decidable_for_empty_string (r: regex):
  [] `elem` {{ star r }} \/ [] `notelem` {{ star r }}.
Proof.
left.
constructor.
Qed.

Lemma denotation_is_decidable_on_empty_string (r: regex):
  [] `elem` {{ r }} \/ [] `notelem` {{ r }}.
Proof.
intros.
induction r.
- apply denotation_emptyset_is_decidable.
- apply denotation_lambda_is_decidable.
- apply denotation_symbol_is_decidable.
- apply denotation_concat_is_decidable_for_empty_string.
  + assumption.
  + assumption.
- apply denotation_star_is_decidable_for_empty_string.
- apply denotation_nor_is_decidable.
  + assumption.
  + assumption.
Qed.

Theorem denotation_is_decidable (r: regex) (s: str):
  s `elem` {{ r }} \/ s `notelem` {{ r }}.
Proof.
generalize dependent s.
induction r.
- apply denotation_emptyset_is_decidable.
- apply denotation_lambda_is_decidable.
- intros. apply denotation_symbol_is_decidable.
- intros. apply denotation_concat_is_decidable;
  unfold regex_is_decidable;
  assumption.
- apply denotation_star_is_decidable.
  assumption.
- intros.
  specialize IHr1 with s.
  specialize IHr2 with s.
  apply denotation_nor_is_decidable; assumption.
Qed.