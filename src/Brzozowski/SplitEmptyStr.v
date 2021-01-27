Require Import CoqStock.DubStep.
Require Import CoqStock.Invs.
Require Import CoqStock.List.
Require Import CoqStock.Listerine.
Require Import CoqStock.Untie.
Require Import CoqStock.WreckIt.

Require Import Brzozowski.Alphabet.
Require Import Brzozowski.ConcatLang.
Require Import Brzozowski.Decidable.
Require Import Brzozowski.Null.
Require Import Brzozowski.NullCommutes.
Require Import Brzozowski.Language.
Require Import Brzozowski.LogicOp.
Require Import Brzozowski.Regex.
Require Import Brzozowski.Ring.
Require Import Brzozowski.Simplify.
Require Import Brzozowski.StarLang.

(*
null_split_emptystr_or splits a regular expression into
a possible emptystr and the regular expression that does not match emptystr.
This theorem is needed for finding the derive function for the concat operator.
Let:
  R = null_def(R) or R'
  where null_def(R') = emptyset
=>
Let:
  R = E or R'
  E = null_def(R)
  where null_def(R') = emptyset
*)

Definition split_into_null_or (r: regex) :=
  exists (e r': regex),
  null r e /\
  null r' emptyset /\
  {{r}} {<->} {{or e r'}}.

Lemma split_emptyset_into_emptyset_or_emptyset:
  split_into_null_or emptyset.
Proof.
unfold split_into_null_or.
exists emptyset.
exists emptyset.
split; try split.
- constructor. untie.
- constructor. untie.
- cbn.
  rewrite or_lang_emptyset_l_is_r.
  reflexivity.
Qed.

Lemma split_emptystr_into_emptystr_or_emptyset:
  split_into_null_or emptystr.
Proof.
unfold split_into_null_or.
exists emptystr.
exists emptyset.
split; try split.
- constructor. constructor.
- constructor. untie.
- cbn.
  rewrite or_lang_emptyset_r_is_l.
  reflexivity.
Qed.

Lemma split_symbol_into_emptyset_or_symbol:
  forall (a: alphabet),
  split_into_null_or (symbol a).
Proof.
unfold split_into_null_or.
intros.
exists emptyset.
exists (symbol a).
split; try split.
- constructor. untie. invs H.
- constructor. untie. invs H.
- cbn.
  rewrite or_lang_emptyset_l_is_r.
  reflexivity.
Qed.

Lemma split_or_into_null_or:
  forall
    (p q: regex)
    (IHp: split_into_null_or p)
    (IHq: split_into_null_or q),
  split_into_null_or (or p q).
Proof.
unfold split_into_null_or.
intros.
destruct IHp as [pn [p' [nullp [nullp' IHp]]]].
destruct IHq as [qn [q' [nullq [nullq' IHq]]]].
exists (null_or pn qn).
exists (or p' q').
split; try split.
- apply null_or_is_or; assumption.
- constructor.
  untie.
  invs H.
  invs nullq'.
  invs nullp'.
  destruct H0; contradiction.
- invs nullq'.
  invs nullp'.
  invs nullp; invs nullq.
  + cbn.
    rewrite IHp.
    rewrite IHq.
    cbn.
    rewrite or_lang_assoc.
    rewrite or_lang_assoc.
    rewrite (or_lang_comm emptystr_lang _).
    rewrite <- (or_lang_assoc {{p'}} emptystr_lang emptystr_lang).
    truthy.
  + cbn.
    rewrite IHp.
    rewrite IHq.
    cbn.
    truthy.
  + cbn.
    rewrite IHp.
    rewrite IHq.
    cbn.
    truthy.
  + cbn.
    rewrite IHp.
    rewrite IHq.
    cbn.
    truthy.
Qed.

(*
  We can split a regex (not r) into
  null_neg r
  or
  neg (or r (null_neg r))

  Consider the two cases:
1.
  [] \in r            rn = emptystr
  [] \notin (neg r)
  [] \notin r'        nullr' = emptyset
  [] \in (neg r')
  neg r = or emptyset r
  neg r = or (null_neg rn) r
  neg r = or (null_neg rn) (neg r)
2.
  [] \notin r         rn = emptyset
  [] \in (neg r)
  [] \notin r'        nullr' = emptyset
  [] \in (neg r')
  neg r = or emptystr (neg r)
  neg r = or (null_neg rn) (neg (or r emptystr))
*)
Lemma split_neg_into_null_or:
  forall
    (r: regex)
    (IHr: split_into_null_or r),
  split_into_null_or (neg r).
Proof.
unfold split_into_null_or.
intros.
destruct IHr as [rn [r' [nullr [nullr' IHr]]]].
exists (null_neg rn).
exists (neg (or r (null_neg rn))).
split; try split.
- apply null_neg_is_neg. assumption.
- constructor.
  untie.
  invs H.
  apply H0.
  constructor.
  invs nullr.
  + left. assumption.
  + right. cbn. constructor.
- invs nullr.
  + cbn.
    rewrite IHr.
    cbn.
    rewrite or_lang_emptyset_l_is_r.
    rewrite or_lang_emptyset_r_is_l.
    reflexivity.
  + simpl null_neg.
    split; intros.
    * invs H0.
      constructor.
      specialize denotation_is_decidable with (r := emptystr) (s := s) as Demptystr.
      destruct Demptystr.
      --- left. assumption.
      --- right. constructor. untie. invs H2. destruct H3.
          +++ contradiction.
          +++ contradiction.
    * constructor.
      untie.
      invs H0.
      invs H2.
      --- invs H0.
          contradiction.
      --- invs H0.
          apply H2.
          constructor.
          left.
          assumption.
Qed.

Lemma split_concat_into_null:
  forall
    (p q pn qn: regex)
    (Hnp: [] \notin {{p}})
    (Hnq: [] \notin {{q}})
    (Hpn: pn = emptyset \/ pn = emptystr)
    (Hqn: qn = emptyset \/ qn = emptystr),
  concat_lang
    (or_lang {{pn}} {{p}})
    (or_lang {{qn}} {{q}})
  {<->}
  or_lang
    {{null_and pn qn}}
    (or_lang
      (concat_lang
        {{p}}
        (or_lang {{qn}} {{q}})
      )
      (concat_lang
        (or_lang {{pn}} {{p}})
        {{q}}
      )
    ).
Proof.
intros.
destruct Hpn, Hqn.
- subst.
  rewrite or_lang_emptyset_l_is_r.
  cbn.
  rewrite or_lang_emptyset_l_is_r.
  rewrite or_lang_emptyset_l_is_r.
  rewrite or_lang_idemp.
  reflexivity.
- subst.
  rewrite or_lang_emptyset_l_is_r.
  cbn.
  rewrite or_lang_emptyset_l_is_r.
  rewrite lift_or_lang_over_concat_lang_r.
  rewrite concat_lang_emptystr_r_is_r.
  rewrite <- or_lang_assoc.
  truthy.
- subst.
  cbn.
  truthy.
  rewrite lift_or_lang_over_concat_lang_l.
  truthy.
  rewrite or_lang_assoc.
  rewrite (or_lang_comm (concat_lang {{p}} {{q}}) (concat_lang emptystr_lang {{q}})).
  rewrite <- or_lang_assoc.
  truthy.
- subst.
  cbn.
  repeat rewrite lift_or_lang_over_concat_lang_l.
  repeat rewrite lift_or_lang_over_concat_lang_r.
  repeat rewrite concat_lang_emptystr_r_is_r.
  repeat rewrite concat_lang_emptystr_l_is_l.
  (* or (or emptystr q) (or p (concat p q)) *)
  (* or
      emptystr
      (or
        (or
          p
          (concat p q)
        )
        (or
          q
          (concat p q)
        )
      )
  *)
  symmetry.
  rewrite <- or_lang_assoc.
  rewrite (or_lang_comm (concat_lang {{p}} {{q}}) _).
  rewrite <- or_lang_assoc.
  truthy.
Qed.

Lemma split_concat_into_null_or:
  forall
    (p q: regex)
    (IHp: split_into_null_or p)
    (IHq: split_into_null_or q),
  split_into_null_or (concat p q).
Proof.
unfold split_into_null_or.
intros.
destruct IHp as [pn [p' [nullp [nullp' IHp]]]].
destruct IHq as [qn [q' [nullq [nullq' IHq]]]].
exists (null_and pn qn).
exists (or (concat p' q) (concat p q')).
split; try split.
- rewrite <- null_iff_null_def in nullq.
  rewrite <- null_iff_null_def in nullp.
  rewrite <- null_iff_null_def.
  cbn.
  subst.
  reflexivity.
- rewrite <- null_iff_null_def in *.
  cbn.
  rewrite nullp'.
  rewrite nullq'.
  specialize null_is_emptystr_or_emptyset with (r := p) as Dp.
  invs Dp.
  + rewrite H.
    reflexivity.
  + rewrite H.
    reflexivity.
- simpl denote_regex.
  rewrite IHp.
  rewrite IHq.
  simpl denote_regex.
  apply split_concat_into_null.
  + invs nullp'. assumption.
  + invs nullq'. assumption.
  + invs nullp; auto.
  + invs nullq; auto.
Qed.

(*
If r does not contain emptystr then (r, star r) does not contain emptystr.
If r contains emptystr then (r', star r) does not contain the emptystr.
*)
Lemma split_star_into_null_or:
  forall
    (r: regex)
    (IHr: split_into_null_or r),
  split_into_null_or (star r).
Proof.
unfold split_into_null_or.
intros.
destruct IHr as [rn [r' [nullr [nullr' IHr]]]].
exists emptystr.
exists (concat r' (star r)).
split; try split.
- constructor. constructor.
- constructor. untie.
  invs H.
  listerine.
  invs nullr'.
  contradiction.
- split; intros.
  + constructor.
    inversion H.
    * subst.
      left.
      constructor.
    * subst.
      right.
      destruct_concat_lang.
      exists p.
      exists q.
      exists eq_refl.
      split.
      --- unfold lang_iff in IHr.
          specialize IHr with (s := p).
          apply IHr in H2 as H7.
          inversion H7.
          inversion nullr.
          +++ subst.
              invs H0.
              *** invs H4.
                  contradiction.
              *** assumption.
          +++ subst.
              invs H0.
              *** invs H4.
              *** assumption.
      --- assumption.
  + invs H.
    invs H0.
    * invs H.
      constructor.
    * inversion H.
      invs nullr.
      --- unfold lang_iff in IHr.
          specialize IHr with (s := p).
          cbn.
          apply (mk_star_more {{r}} (p ++ q) p q).
          +++ reflexivity.
          +++ invs nullr'.
              untie.
          +++ rewrite IHr.
              constructor.
              right.
              assumption.
          +++ assumption.
      --- unfold lang_iff in IHr.
          specialize IHr with (s := p).
          apply (mk_star_more {{r}} (p ++ q) p q).
          +++ reflexivity.
          +++ invs nullr'.
              untie.
          +++ rewrite IHr.
              constructor.
              right.
              assumption.
          +++ assumption.
Qed.

Theorem null_split_emptystr_or (r: regex):
  exists
    (e r': regex),
    null r e /\
    null r' emptyset /\
    {{r}} {<->} {{or e r'}}.
Proof.
induction r.
- apply split_emptyset_into_emptyset_or_emptyset.
- apply split_emptystr_into_emptystr_or_emptyset.
- apply split_symbol_into_emptyset_or_symbol.
- apply split_or_into_null_or; assumption.
- apply split_neg_into_null_or; assumption.
- apply split_concat_into_null_or; assumption.
- apply split_star_into_null_or; assumption.
Qed.
