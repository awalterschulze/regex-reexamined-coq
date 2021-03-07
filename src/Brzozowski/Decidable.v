(*
In this module we prove the denotation of regular expressions is decidable, using:
```
Theorem denotation_is_decidable (r: regex) (s: str):
  s \in {{ r }} \/ s \notin {{ r }}.
```
*)

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
  (forall s: str, s \in {{r}} \/ s \notin {{r}}).

Lemma denotation_emptyset_is_decidable (s: str):
  s \in {{ emptyset }} \/ s \notin {{ emptyset }}.
Proof.
right.
untie.
Qed.

Lemma denotation_emptystr_is_decidable (s: str):
  s \in {{ emptystr }} \/ s \notin {{ emptystr }}.
Proof.
destruct s.
- left. constructor.
- right. untie. invs H.
Qed.

Lemma denotation_symbol_is_decidable (s: str) (a: alphabet):
  s \in {{ symbol a }} \/ s \notin {{ symbol a }}.
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

Lemma denotation_or_is_decidable (p q: regex) (s: str):
  s \in {{ p }} \/ s \notin {{ p }} ->
  s \in {{ q }} \/ s \notin {{ q }} ->
  s \in {{ or p q }} \/ s \notin {{ or p q }}.
Proof.
simpl.
intros.
wreckit.
- left.
  constructor.
  auto.
- left.
  constructor.
  auto.
- left.
  constructor.
  auto.
- right.
  untie.
  invs H.
  wreckit; contradiction.
Qed.

Lemma denotation_neg_is_decidable (p: regex) (s: str):
  s \in {{ p }} \/ s \notin {{ p }} ->
  s \in {{ neg p }} \/ s \notin {{ neg p }}.
Proof.
intros.
wreckit.
- right. simpl. untie. invs H. contradiction.
- left. simpl. untie. constructor. assumption.
Qed.

(*
  To prove concat is decidable, we have to first show that:
  - if a concat expression `concat P Q` matches
      then there exists some splitting where
      the prefix matches `P` and the suffix matches `Q`
  - if a concat expression `concat P Q` does not match
      then forall splittings
      the prefix does not match `P`
      or the suffix does not match `Q`
  Next we can combine these two lemmas into one decidability lemma.
  Then we can prove concat is decidable for some maximum length using the above lemma.
  And finally we can prove concat is decidable using this final lemma.
*)

Definition elem_of_concat_split (p q: regex) (s: str) (index: nat) :=
  let prefix := firstn index s in
  let suffix := skipn index s in
  (prefix \in {{p}} /\ suffix \in {{q}}).

Lemma concat_lang_a_split_matches:
  forall (P Q: regex) (s: str),
    s \in {{ concat P Q }}
  <->
  (exists (index: nat) (index_range : index <= length s),
    elem_of_concat_split P Q s index
  ).
Proof.
intros.
split.
- intros s_elem_concat.
  destruct s_elem_concat.
  exists (length p).
  assert (length p <= length s).
  + rewrite <- H.
    autorewrite with list.
    lia.
  + exists H2.
    constructor.
    * rewrite <- H.
      rewrite firstn_length_prefix_is_prefix.
      assumption.
    * rewrite <- H.
      rewrite skipn_length_prefix_is_suffix.
      assumption.
- intros exists_elem.
  wreckit.
  unfold elem_of_concat_split in H.
  wreckit.
  destruct_concat_lang.
  exists (firstn index s).
  exists (skipn index s).
  assert (firstn index s ++ skipn index s = s) by auto with list.
  exists H3.
  auto.
Qed.

Lemma concat_lang_no_split_matches:
  forall (P Q: regex) (s: str),
  s \notin {{ concat P Q }}
  <->
  (forall (index: nat) (index_range : index <= length s),
    not (elem_of_concat_split P Q s index)
  ).
Proof.
intros.
split.
- intros s_not_elem_concat index bounded_index.
  unfold not.
  intros elem_of_split.
  apply s_not_elem_concat.
  apply concat_lang_a_split_matches.
  exists index.
  exists bounded_index.
  assumption.
- intros not_elem_of_split.
  unfold not.
  intros s_elem_concat.
  destruct s_elem_concat.
  specialize not_elem_of_split with (index := length p).
  rewrite <- H in *.
  assert (length p <= length (p ++ q)) as bounded by (autorewrite with list; lia).
  apply not_elem_of_split in bounded as not_elem_of_split'.
  apply not_elem_of_split'.
  unfold elem_of_concat_split.
  rewrite firstn_length_prefix_is_prefix.
  rewrite skipn_length_prefix_is_suffix.
  auto.
Qed.

Theorem concat_lang_a_split_matches_or_no_split_matches:
  forall (P Q: regex) (s: str),
      s \in {{concat P Q}}
    \/
      s \notin {{concat P Q}}
  <->
      (exists (index: nat) (index_range : index <= length s),
        elem_of_concat_split P Q s index
      )
    \/
      (forall (index: nat) (index_range : index <= length s),
        not (elem_of_concat_split P Q s index)
      ).
Proof.
intros.
destruct (concat_lang_a_split_matches P Q s).
destruct (concat_lang_no_split_matches P Q s).
split; intros decide; destruct decide; eauto.
Qed.

(*
  lift_index_and_max_len_from_disjunction
  is used to lift the index and its max length bounds
  out of a disjunction, by applying it on the goal.
*)
Theorem lift_index_and_max_len_from_disjunction
  (P: nat -> Prop) (len: nat):
  (forall (index : nat) (bounded_index: index <= len),
      P index
    \/
      ~ (P index)
  )
  ->
  (
    (forall (index: nat) (bounded_index: index <= len),
      ~ (P index)
    )
    \/
    (exists (index: nat) (bounded_index: index <= len),
      P index
    )
  ).
Proof.
intro lifted.
induction len.
- specialize lifted with (index := 0).
  assert (0 <= 0) as ofcourse by lia.
  destruct (lifted ofcourse) as [P0 | notP0].
  + right.
    exists 0.
    split; assumption.
  + left.
    intros.
    assert (index = 0) as index0 by lia.
    rewrite index0.
    assumption.
- assert (forall (index: nat) (bounded_index: index <= len), P index \/ ~ P index) as smaller_lifted.
  + intros.
    apply lifted.
    lia.
  + apply IHlen in smaller_lifted.
    destruct smaller_lifted as [notPindex | Pindex].
    * assert (S len <= S len) as slen_leq by lia.
      destruct (lifted (S len) slen_leq) as [PSlen | notPSlen].
      --- right.
          exists (S len).
          split; assumption.
      --- left.
          intros.
          assert (forall (len: nat) (index: nat),
            index <= S len -> index <= len \/ index = S len
          ) as breakdown_leq by lia.
          destruct (breakdown_leq len index bounded_index) as [leqlen | eqSlen].
          +++ apply notPindex.
              assumption.
          +++ rewrite eqSlen.
              assumption.
    * right.
      destruct Pindex as [index [bounded_index Pindex]].
      exists index.
      split.
      --- lia.
      --- assumption.
Qed.

Lemma denotation_concat_is_decidable_bounded_len
  (P Q: regex) (len: nat) (decidableP: regex_is_decidable P) (decidableQ: regex_is_decidable Q):
  (forall
    (s: str)
    (bounded_len: length s <= len),
    (s \in {{concat P Q}} \/ s \notin {{concat P Q}})
  ).
Proof.
intros.
apply concat_lang_a_split_matches_or_no_split_matches.
rewrite or_comm.
apply lift_index_and_max_len_from_disjunction.
unfold elem_of_concat_split.
unfold regex_is_decidable in *.
intros.
specialize decidableP with (s := firstn index s).
specialize decidableQ with (s := skipn index s).
destruct decidableP, decidableQ.
- left. split; assumption.
- right. untie. destruct H1. contradiction.
- right. untie. destruct H1. contradiction.
- right. untie. destruct H1. contradiction.
Qed.

Lemma denotation_concat_is_decidable (P Q: regex):
  regex_is_decidable P ->
  regex_is_decidable Q ->
  regex_is_decidable (concat P Q).
Proof.
unfold regex_is_decidable.
intros Hp Hq s.
apply (denotation_concat_is_decidable_bounded_len P Q (length s) Hp Hq).
lia.
Qed.

(*
An alternative proof for concat is decidable that uses a similar technique.
*)

Definition no_splitting_is_an_elem_for_length (p q: regex) (s: str) (n: nat) :=
  forall (s1 s2: str),
  s = s1 ++ s2 ->
  length s1 <= n ->
  ((s1 \notin {{ p }} \/ s2 \notin {{ q }})).

Definition a_splitting_is_an_elem_for_length (p q: regex) (s: str) (n: nat) :=
  exists (s1 s2: str),
  s = s1 ++ s2 /\
  length s1 <= n /\
  (s1 \in {{ p }} /\ s2 \in {{ q }}).

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

Lemma denotation_concat_is_decidable' (p q: regex):
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

(*
  To prove star is decidable, we have to first show that:
  - if a star expression `star r` matches a non empty string
      then there exists some splitting where
      the prefix matches the contained regular expression `r`
      and the suffix matches `star r`.
  - if a star expression `star r` does not match a non empty string
      then forall splittings
      the prefix does not match the contained regular expressions `r`
      or the suffix does not match `star r`
  Next we can combine these two lemmas into one decidability lemma.
  Then we can prove star is decidable for some maximum length using the above lemma.
  And finally we can prove star is decidable using this final lemma.
*)

Definition elem_of_star_split (r: regex) (s: str) (index: nat) :=
  let prefix := firstn index s in
  let suffix := skipn index s in
  (prefix \in {{r}} /\ suffix \in {{star r}}).

Lemma star_lang_a_split_matches:
  forall (r: regex) (s: str) (s_is_not_empty: s <> []),
    s \in {{ star r }}
  <->
  (exists (index: nat) (index_range : 0 < index <= length s),
    elem_of_star_split r s index
  ).
Proof.
intros.
split.
- intro s_elem_star_r.
  destruct s_elem_star_r as [ | s p q pqs p_not_empty p_elem_r q_elem_star_r ].
  + contradiction.
  + exists (length p).
    exists (prefix_is_gt_zero_and_leq p q s p_not_empty pqs).
    unfold elem_of_star_split.
    rewrite <- pqs.
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
  s \notin {{ star r }}
  <->
  (forall (index: nat) (index_range : 0 < index <= length s),
    not (elem_of_star_split r s index)
  ).
Proof.
intros.
split.
- intros s_not_elem_star_r.
  intros index index_range.
  unfold not.
  intro elem_split.
  unfold not in s_not_elem_star_r.
  destruct elem_split as [prefixr suffixr].
  apply s_not_elem_star_r.
  apply (mk_star_more {{r}} s (firstn index s) (skipn index s)).
  + auto with list.
  + now apply prefix_is_not_empty_with_index_gt_zero.
  + assumption.
  + assumption.
- intros split_of_not_star_r.
  unfold not.
  intro s_elem_star_r.
  destruct s_elem_star_r as [ | s p q pqs p_not_empty p_elem_r q_elem_star_r ].
  + contradiction.
  + set (prefix_is_gt_zero_and_leq p q s p_not_empty pqs) as p_range.
    set (split_of_not_star_r (length p) p_range) as specialized_split_of_not_star_r.
    apply specialized_split_of_not_star_r.
    unfold elem_of_star_split.
    split.
    * rewrite <- pqs.
      rewrite firstn_length_prefix_is_prefix.
      assumption.
    * rewrite <- pqs.
      rewrite skipn_length_prefix_is_suffix.
      assumption.
Qed.

Theorem star_lang_a_split_matches_or_no_split_matches:
  forall (r: regex) (s: str) (s_is_not_empty: s <> []),
      s \in {{star r}}
    \/
      s \notin {{star r}}
  <->
      (exists (index: nat) (index_range : 0 < index <= length s),
        elem_of_star_split r s index
      )
    \/
      (forall (index: nat) (index_range : 0 < index <= length s),
        not (elem_of_star_split r s index)
      ).
Proof.
intros.
destruct (star_lang_a_split_matches r s s_is_not_empty).
destruct (star_lang_no_split_matches r s s_is_not_empty).
(* This theorem clearly follows by the above theorems. *)
split; intros decide; destruct decide; eauto.
Qed.

(*
  lift_index_and_non_empty_and_max_len_bounds_from_disjunction
  is used to lift the index and its bounds
  out of a disjunction, by applying it on the goal.
*)
Theorem lift_index_and_non_empty_and_max_len_bounds_from_disjunction
  (P: nat -> Prop) (len: nat):
  (forall (index : nat) (bounded_index: 0 < index <= len),
      P index
    \/
      ~ (P index)
  )
  ->
  (
    (forall (index: nat) (bounded_index: 0 < index <= len),
      ~ (P index)
    )
    \/
    (exists (index: nat) (bounded_index: 0 < index <= len),
      P index
    )
  ).
Proof.
intro lifted.
induction len.
- left.
  intros.
  lia.
- assert (forall (index: nat) (bounded_index: 0 < index <= len), P index \/ ~ P index) as smaller_lifted.
  + intros.
    apply lifted.
    lia.
  + apply IHlen in smaller_lifted.
    destruct smaller_lifted as [notPindex | Pindex].
    * assert (0 < S len <= S len) as slen_leq by lia.
      destruct (lifted (S len) slen_leq) as [PSlen | notPSlen].
      --- right.
          exists (S len).
          split; assumption.
      --- left.
          intros.
          assert (forall (len: nat) (index: nat),
            0 < index <= S len -> 0 < index <= len \/ index = S len
          ) as breakdown_leq by lia.
          destruct (breakdown_leq len index bounded_index) as [leqlen | eqSlen].
          +++ apply notPindex.
              assumption.
          +++ rewrite eqSlen.
              assumption.
    * right.
      destruct Pindex as [index [bounded_index Pindex]].
      exists index.
      split.
      --- lia.
      --- assumption.
Qed.

Lemma denotation_star_is_decidable_bounded_len
  (r: regex) (len: nat) (decidable_r: regex_is_decidable r):
  (forall
    (s: str)
    (bounded_len: length s <= len),
    (s \in {{star r}} \/ s \notin {{star r}})
  ).
Proof.
intros.
generalize dependent s.
induction len.
- left.
  apply length_zero_or_smaller_string_is_empty in bounded_len.
  rewrite bounded_len.
  constructor.
- intros s max_length_S.
  unfold regex_is_decidable in decidable_r.
  destruct s.
  + left. constructor.
  + assert (a :: s <> []) as a_is_not_empty; listerine.
    apply (star_lang_a_split_matches_or_no_split_matches r (a :: s) a_is_not_empty).
    rewrite or_comm.
    apply lift_index_and_non_empty_and_max_len_bounds_from_disjunction with (len := (length (a :: s))).
    intros.
    set (prefix := firstn index (a :: s)).
    set (suffix := skipn index (a :: s)).
    specialize decidable_r with prefix.
    specialize IHlen with suffix.
    assert (length suffix <= len) as suffix_bound.
    * unfold suffix.
      destruct bounded_index as [index0 indexlen].
      rewrite skipn_length.
      lia.
    * apply IHlen in suffix_bound as decidable_suffix.
      clear IHlen max_length_S a_is_not_empty suffix_bound.
      unfold elem_of_star_split.
      destruct decidable_r as [prefix_elem | prefix_not_elem];
      destruct decidable_suffix as [suffix_elem | suffix_not_elem].
      --- left. auto.
      --- right. untie. destruct H. contradiction.
      --- right. untie. destruct H. contradiction.
      --- right. untie. destruct H. contradiction.
Qed.

Lemma denotation_star_is_decidable (r: regex):
  regex_is_decidable r ->
  regex_is_decidable (star r).
Proof.
unfold regex_is_decidable.
intro Hr.
intro s.
apply (denotation_star_is_decidable_bounded_len r (length s) Hr).
lia.
Qed.

Theorem denotation_is_decidable (r: regex) (s: str):
  s \in {{ r }} \/ s \notin {{ r }}.
Proof.
generalize dependent s.
induction r.
- apply denotation_emptyset_is_decidable.
- apply denotation_emptystr_is_decidable.
- intros. apply denotation_symbol_is_decidable.
- intros. apply denotation_or_is_decidable.
  + specialize IHr1 with s. assumption.
  + specialize IHr2 with s. assumption.
- intros. apply denotation_neg_is_decidable.
  specialize IHr with s. assumption.
- intros. apply denotation_concat_is_decidable;
  unfold regex_is_decidable;
  assumption.
- apply denotation_star_is_decidable.
  assumption.
Qed.