Require Import List.
Import ListNotations.
Require Import Setoid.

Require Import CoqStock.DubStep.
Require Import CoqStock.Invs.
Require Import CoqStock.Listerine.
Require Import CoqStock.Untie.
Require Import CoqStock.WreckIt.

Require Import Brzozowski.Alphabet.
Require Import Brzozowski.Language.
Require Import Brzozowski.Regex.

Require Import Lia.

Definition regex_is_decidable (r: regex) :=
    (forall s: str, s `elem` {{r}} \/ s `notelem` {{r}}).

(* TODO: move into listerine *)
Lemma length_zero_string_is_empty (s : str) :
  length s <= 0 -> s = [].
Proof.
  intros.
  assert (length s = 0).
  lia.
  rewrite length_zero_iff_nil in *.
  assumption.
Qed.

(* TODO: move into listerine *)
Lemma split_string_lemma (s : str) (n : nat):
  forall (s1 s2: str),
    length s1 = n ->
    s = s1 ++ s2 ->
    s1 = firstn n s /\
    s2 = skipn n s.
Proof.
  intros.
  set (s1' := firstn n s).
  set (s2' := skipn n s).
  subst.

  set (firstn_app (length s1) s1 s2) as Hfirst.
  replace (length s1 - length s1) with 0 in * by lia.
  replace (firstn 0 s2) with (nil : str) in * by (symmetry; apply firstn_O).
  rewrite app_nil_r in Hfirst.
  replace (firstn (length s1) s1) with s1 in Hfirst by (symmetry; apply firstn_all).

  set (skipn_app (length s1) s1 s2) as Hlast.
  replace (length s1 - length s1) with 0 in * by lia.
  replace (skipn (length s1) s1) with (nil: str) in Hlast by (symmetry; apply skipn_all).
  rewrite app_nil_l in Hlast.
  replace (skipn 0 s2) with s2 in Hlast by (apply skipn_O).

  split; auto.
Qed.

(* TODO: move into listerine *)
Lemma substrings_have_smaller_length (s s1 s2: str):
  s = s1 ++ s2 -> length s1 <= length s.
Proof.
  intro H.
  assert (length s1 + length s2 = length s).
  replace s with (s1 ++ s2) by assumption.
  symmetry.
  exact (app_length s1 s2).
  lia.
Qed.

Lemma denotation_concat_is_decidable_helper (p q: regex):
  regex_is_decidable p ->
  regex_is_decidable q ->
  (forall (s: str) (n : nat),
      (* prove that either all splittings don't match, or there is a match;
         but only consider a subset of all splttings
       *)
      (forall (s1 s2: str),
          s = s1 ++ s2 ->
          length s1 <= n ->
          (* does not match concat pairwise *)
          ((s1 `notelem` {{ p }} \/ s2 `notelem` {{ q }})))
      \/ (exists (s1 s2: str),
            s = s1 ++ s2 /\
            length s1 <= n /\
            (s1 `elem` {{ p }} /\ s2 `elem` {{ q }}))).
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
      assert (s1 = []) by (apply length_zero_string_is_empty; assumption);
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
          destruct (split_string_lemma s (S n) s1 s2 Hlen' Hconcat) as [Hfoo Hbar];

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



(*

(s : str)

s `elem` (concat p q)
or not
s `elem` (concat p q)





*)


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
    destruct HmatchContr as [s [s1 [s2 [Hconcat [Hmatchp Hmatchq]]]]].
    symmetry in Hconcat.

    set (Hlen := substrings_have_smaller_length s s1 s2 Hconcat).

    specialize HAllDontMatch with s1 s2.
    destruct (HAllDontMatch Hconcat Hlen); auto.

  - left.
    destruct HExistsMatch as [s1 [s2 [Hconcat [Hlen [Hmatchp Hmatchq]]]]].
    constructor.
    symmetry in Hconcat.
    exists s1. exists s2. exists Hconcat.
    split; assumption.
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
  constructor.
  exists [].
  exists [].
  exists eq_refl.
  wreckit; assumption.
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
reflexivity.
Qed.


Lemma denotation_star_is_decidable_helper (r: regex) (k: nat) (s: str) (a: alphabet):
  regex_is_decidable r ->
  (forall (s': str),
      length s' < length (a::s) -> (
        s' `elem` {{star r}}
           \/ s' `notelem` {{star r}})) ->
      (forall (s1 s2: str),
          length s1 <= k ->
          (a::s) = a::s1 ++ s2 ->
          (* does not match concat pairwise *)
          ((a::s1 `notelem` {{ r }} \/ s2 `notelem` {{ star r }})))
      \/ (exists (s1 s2: str),
            length s1 <= k /\
            (a::s) = a::s1 ++ s2 /\
            (a::s1 `elem` {{ r }} /\ s2 `elem` {{ star r }})).
Proof.
  intro Hdecr.
  intro Hdecstarr.
  induction k.
  -
    unfold regex_is_decidable in Hdecr.
    specialize Hdecr with [a].
    destruct Hdecr as [ Hrmatch | Hrnomatch ].
    + destruct (Hdecstarr s) as [ Hstarmatch | Hstarnomatch].
      * admit.
      * right.
        exists [].
        exists s.
        wreckit.
        -- now listerine.
        -- now listerine.
        -- assumption.
        -- assumption.
      * admit.
    + destruct (Hdecstarr s) as [ Hstarmatch | Hstarnomatch].
      * admit.
      * left.
        admit.
      * left. admit.

  -
    unfold regex_is_decidable in Hdecr.
    destruct IHk as [ IHallnomatch | IHexistsmatch ].
    + (* only check case length s1 = S k *)

      (* s = a::s1 ++ s2
      where length s1 = k + 1

so s1 = (skipn 1 (firstn (k + 2) s))

       *)
      set (s1 := (firstn (S k) s)).
      set (s2 := (skipn (S k) s)).

      specialize Hdecr with (a::s1).
      destruct Hdecr as [ Hrmatch | Hrnomatch ].
      *
        destruct (Hdecstarr s2) as [ Hstarmatch | Hstarnomatch ].
        -- admit.
        --
          right.
          exists s1.
          exists s2.
          wreckit.
          ++ admit.
          ++ admit.
          ++ assumption.
          ++ assumption.
        --
          left.
          intros s1' s2'.
          intro Hlen.
          intro Happ.
          inversion Hlen.
          ++
            replace s1' with s1.
            replace s2' with s2.
            right. assumption.

            (* admit; use listerine *)
            admit.
            admit.

          ++ specialize IHallnomatch with s1' s2'.
             apply IHallnomatch.
             assumption.
             assumption.

      * admit. (* probably (almost) copy of the above *)
    +
      right.

      destruct IHexistsmatch as [ s1 [ s2 [Hlen] ] ].
      destruct H as [ Happ [ Hstart Htail ]].
      exists s1.
      exists s2.

      wreckit.
      * lia.
      * assumption.
      * assumption.
      * assumption.
(* TODO: Good First Issue *)
Abort.


Lemma denotation_star_is_decidable_for_small_strings (r: regex) (n: nat):
  (regex_is_decidable r)
  -> (forall (s: str),
        length s <= n
        ->
        (s `elem` {{star r}}
            \/ s `notelem` {{star r}})).
Proof.
  intro Hdec.
  induction n.
  - intros s Hlen.
    apply length_zero_string_is_empty in Hlen.
    subst.
    apply denotation_star_is_decidable_for_empty_string.
  - intros s Hlen.
    destruct s.
    + apply denotation_star_is_decidable_for_empty_string.
    + simpl in Hlen.
      (* TODO: apply denotation_star_is_decidable_helper, but first prove it *)
      (* apply (denotation_star_is_decidable_helper r n s a) in Hdec.
      * wreckit.
        --- right.
            untie.
            inversion H.
            +++ discriminate.
            +++ invs H0.
                wreckit. 




      * intros. apply IHn. admit. *)

    (* TODO: NEXT STEP: use the denotation_star_is_decidable_helper
to prove this. Then use this to prove denotation_star_is_decidable
     *)


    (*

Let s = s1 ++ s2

then ....

     *)


    (*
we know: doesn't match empty (b/c of length)

we know: (concat r (star r)) is decidable

take any splitting s = s1 ++ s2
where s1 matches r and s1 is not empty
(But: also need: there are only finitely many such splittings. (Need this
for constructivity (no excluded middle).))

For every splitting s = s1 ++ s2
where ...

we want to prove:
     s1




     *)

Abort.

Lemma denotation_star_is_decidable (r: regex):
  regex_is_decidable r -> regex_is_decidable (star r).
Proof.
  (* TODO: Help Wanted *)
  (* See NEXT STEP above in denotation_star_is_decidable_for_small_strings
for our idea on how to prove this. *)
Abort.

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
- admit. (* TODO: Help Wanted *)
- intros.
  specialize IHr1 with s.
  specialize IHr2 with s.
  apply denotation_nor_is_decidable; assumption.
Abort.