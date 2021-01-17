Require Import CoqStock.DubStep.
Require Import CoqStock.Invs.
Require Import CoqStock.List.
Require Import CoqStock.Listerine.
Require Import CoqStock.Untie.
Require Import CoqStock.WreckIt.

Require Import Brzozowski.Alphabet.
Require Import Brzozowski.ConcatLang.
Require Import Brzozowski.Decidable.
Require Import Brzozowski.Regex.
Require Import Brzozowski.Language.
Require Import Brzozowski.LogicOp.

(*
    **Definition 3.2.**
    Given any language $R$ we define $\nu(R)$ to be

    $$
    \begin{aligned}
    \nu(R) & = \epsilon\ \text{if}\ \epsilon \in R \\
              & = \emptyset\ \text{if}\ \epsilon \notin R \\
    \end{aligned}
    $$
*)

Inductive null: regex -> regex -> Prop :=
  | null_emptystr (r: regex):
    [] \in {{r}} ->
    null r emptystr
  | null_emptyset (r: regex):
    [] \notin {{r}} ->
    null r emptyset
    .

(*
null_and is only true when both regexes are true, where
true = emptystr
false = emptyset
*)
Definition null_and (p q: regex): regex :=
  match (p, q) with
  | (emptystr, emptystr) => emptystr
  | _ => emptyset
  end.

(*
null_nor is only true when both regexes are false, where
true = emptystr
false = emptyset
*)
Definition null_nor (p q: regex): regex :=
  match (p, q) with
  | (emptyset, emptyset) => emptystr
  | _ => emptyset
  end.

(*
  It is clear that:

  $$
  \begin{aligned}
  \nu(a) & = \emptyset\ \text{for any}\ a \in \Sigma_k, \\
  \nu(\epsilon) & = \epsilon, \text{and} \\
  \nu(\emptyset) & = \emptyset . \\
  \end{aligned}
  $$
*)

Theorem null_emptystr_is_emptystr: null emptystr emptystr.
Proof.
apply null_emptystr.
constructor.
Qed.

Theorem null_emptyset_is_emptyset: null emptyset emptyset.
Proof.
apply null_emptyset.
unfold not.
intros.
inversion H.
Qed.

Theorem null_symbol_is_emptyset: forall (a: alphabet),
    null (symbol a) emptyset.
Proof.
intros.
apply null_emptyset.
unfold not.
intros.
inversion H.
Qed.

(*
    Furthermore

    $$
    \begin{aligned}
    \nu(P* ) &= \epsilon\ \text{(by definition of * ), and} \\
    \nu(P.Q) &= \nu(P)\ \&\ \nu(Q).
    \end{aligned}
    $$
*)

(* \nu(P* ) = \epsilon\ *)
Theorem null_star_is_emptystr: forall (r: regex),
    null (star r) emptystr.
Proof.
intros.
apply null_emptystr.
constructor.
Qed.

Theorem null_concat_is_and_emptystr: forall (p q: regex),
    null p emptystr ->
    null q emptystr ->
    null (concat p q) emptystr.
Proof.
intros.
constructor.
destruct_concat_lang.
exists [].
exists [].
assert ([] ++ [] = (@nil alphabet)). cbn. reflexivity.
exists H1.
split.
- inversion H.
  exact H2.
- inversion H0.
  exact  H2.
Qed.

(* \nu(P.Q) = \nu(P)\ \&\ \nu(Q) *)
Theorem null_concat_is_and:
  forall (p q: regex)
         (dp dq: regex)
         (dc: regex)
         (null_p: null p dp)
         (null_q: null q dq),
  null (concat p q) (null_and dp dq).
Proof.
intros.
invs null_p; invs null_q; cbn; constructor; try untie.
- destruct_concat_lang.
  exists []. exists []. exists eq_refl.
  split; assumption.
- invs H1. wreckit. listerine. subst.
  apply H0. assumption.
- invs H1. wreckit. listerine. subst.
  apply H. assumption.
- invs H1. wreckit. listerine. subst.
  apply H. assumption.
Qed.

Theorem null_concat_is_and_emptyset_r: forall (p q: regex),
    null p emptyset ->
    null q emptystr ->
    null (concat p q) emptyset.
Proof.
(*TODO: Good First Issue *)
Abort.

Theorem null_concat_is_and_emptyset_l: forall (p q: regex),
    null p emptystr ->
    null q emptyset ->
    null (concat p q) emptyset.
Proof.
(* TODO: Good First Issue *)
Abort.

Theorem null_concat_is_and_emptyset: forall (p q: regex),
    null p emptyset ->
    null q emptyset ->
    null (concat p q) emptyset.
Proof.
(* TODO: Good First Issue *)
Abort.

(*
  If $R = f(P, Q)$ it is also easy to determine $\nu(R)$. For example,

  $$
  \begin{aligned}
  \text{(3.1)}&\ \nu(P + Q)    &= \nu(P) + \nu(Q). \\
  \text{(3.2)}&\ \nu(P\ \&\ Q) &= \nu(P)\ \&\ \nu(Q). \\
  \text{(3.3)}&\ \nu(P')       &= \epsilon\ \text{if}\ \nu(P) = \emptyset \\
              &                   &= \emptyset\ \text{if}\ \nu(P) = \epsilon \\
  \end{aligned}
  $$

  where $\&$ and $+$ is defined for $\nu$ similar to
  $\epsilon$ being True and $\emptyset$ being False in a boolean equation.

  $$
  \begin{aligned}
  A\ \&\ B = \epsilon\ \text{if and only if}\ A = \epsilon\ \text{and}\ B = \epsilon \\
  A + B = \emptyset\ \text{if and only if}\ A = \emptyset\ \text{and}\ B = \emptyset
  \end{aligned}
  $$
*)

(*
null_or is only true when one of the regexes are true, where
true = emptystr
false = emptyset
*)
Definition null_or (p q: regex): regex :=
  match (p, q) with
  | (emptystr, _) => emptystr
  | (_, emptystr) => emptystr
  | _ => emptyset
  end.

(* \nu(P + Q) = \nu(P) + \nu(Q) *)
Theorem null_or_is_or:
  forall
    (p q: regex)
    (pn qn: regex)
    (null_p: null p pn)
    (null_q: null q qn),
    null (or p q) (null_or pn qn).
Proof.
intros.
invs null_p; invs null_q; cbn; constructor; cbn.
- constructor. auto.
- constructor. auto.
- constructor. auto.
- untie. invs H1. wreckit; contradiction.
Qed.

(* \nu(P\ \&\ Q) = \nu(P)\ \&\ \nu(Q). *)
Theorem null_and_is_and:
  forall
    (p q: regex)
    (dp dq: regex)
    (null_p: null p dp)
    (null_q: null q dq),
    null (and p q) (null_and dp dq).
Proof.
intros.
invs null_p; invs null_q; cbn; constructor; cbn;
  try constructor;
  untie.
- invs H1. destruct H2.
  + invs H1. contradiction.
  + invs H1. contradiction.
- invs H1. destruct H2.
  constructor. right. constructor. assumption.
- invs H1. destruct H2.
  constructor. left. constructor. assumption.
- invs H1. destruct H2.
  constructor. left. constructor. assumption.
Qed.

(*
null_neg is only true if input is false and vice versa, where
true = emptystr
false = emptyset
*)
Definition null_neg (p: regex): regex :=
  match p with
  | emptystr => emptyset
  | _ => emptystr
  end.

(*
\nu(P') = \epsilon\ \text{if}\ \nu(P) = \emptyset \\
\nu(P') = \emptyset\ \text{if}\ \nu(P) = \epsilon
*)
Theorem null_neg_is_neg:
  forall
    (p: regex)
    (dp: regex)
    (null_p: null p dp),
    null (neg p) (null_neg dp).
Proof.
intros.
invs null_p; cbn; constructor.
- untie.
  cbn in H0.
  invs H0.
  contradiction.
- cbn.
  constructor.
  assumption.
Qed.

Theorem null_or_emptystr: forall (p q: regex),
    null p emptystr ->
    null q emptystr ->
    null (or p q) emptystr.
Proof.
(* TODO: Good First Issue *)
Abort.

Theorem null_or_emptystr_l: forall (p q: regex),
    null p emptystr ->
    null q emptyset ->
    null (or p q) emptystr.
Proof.
(* TODO: Good First Issue *)
Abort.

Theorem null_or_emptystr_r: forall (p q: regex),
    null p emptyset ->
    null q emptystr ->
    null (or p q) emptystr.
Proof.
(* TODO: Good First Issue *)
Abort.

Theorem null_or_emptyset: forall (p q: regex),
    null p emptyset ->
    null q emptyset ->
    null (or p q) emptyset.
Proof.
(* TODO: Good First Issue *)
Abort.

Theorem null_and_emptystr: forall (p q: regex),
    null p emptystr ->
    null q emptystr ->
    null (and p q) emptystr.
Proof.
(* TODO: Good First Issue *)
Abort.

Theorem null_and_l_emptyset: forall (p q: regex),
  null p emptyset ->
  null (and p q) emptyset.
Proof.
(* TODO: Good First Issue *)
Abort.

Theorem null_and_emptyset_l: forall (p q: regex),
    null p emptyset ->
    null q emptystr ->
    null (and p q) emptyset.
Proof.
(* TODO: Good First Issue *)
Abort.

Theorem null_and_r_emptyset: forall (p q: regex),
  null q emptyset ->
  null (and p q) emptyset.
Proof.
intros.
constructor.
untie.
invs H0.
apply H1.
invs H.
constructor.
right.
cbn.
constructor.
assumption.
Qed.

Theorem null_and_emptyset_r: forall (p q: regex),
    null p emptystr ->
    null q emptyset ->
    null (and p q) emptyset.
Proof.
intros.
apply null_and_r_emptyset.
assumption.
Qed.

Theorem null_and_emptyset: forall (p q: regex),
    null p emptyset ->
    null q emptyset ->
    null (and p q) emptyset.
Proof.
intros.
apply null_and_r_emptyset.
assumption.
Qed.

Theorem null_and_emptyset_either: forall (p q: regex),
    null p emptyset \/
    null q emptyset ->
    null (and p q) emptyset.
Proof.
intros.
destruct H.
- constructor.
  untie.
  invs H0.
  apply H1.
  constructor.
  invs H.
  left.
  cbn.
  constructor.
  assumption.
- constructor.
  untie.
  invs H0.
  invs H.
  apply H1.
  constructor.
  right.
  cbn.
  constructor.
  assumption.
Qed.

Theorem null_neg_emptyset: forall (r: regex),
    null r emptystr ->
    null (neg r) emptyset.
Proof.
intros.
constructor.
invs H.
cbn.
untie.
invs H.
contradiction.
Qed.

Theorem null_neg_emptystr_emptyset:
  null (neg emptystr) emptyset.
Proof.
apply null_neg_emptyset.
apply null_emptystr_is_emptystr.
Qed.

Theorem null_neg_emptystr: forall (r: regex),
    null r emptyset ->
    null (neg r) emptystr.
Proof.
intros.
constructor.
invs H.
cbn.
constructor.
assumption.
Qed.

Fixpoint null_def (r: regex): regex :=
  match r with
  | emptyset => emptyset
  | emptystr => emptystr
  | symbol _ => emptyset
  | or s t => null_or (null_def s) (null_def t)
  | neg s => null_neg (null_def s)
  | concat s t => null_and (null_def s) (null_def t)
  | star s => emptystr
end.

Theorem null_is_null_def:
  forall (r: regex),
  null r (null_def r).
Proof.
intros.
induction r.
- cbn.
  apply null_emptyset.
  untie.
- cbn.
  apply null_emptystr.
  constructor.
- cbn.
  apply null_emptyset.
  untie.
  invs H.
- cbn.
  invs IHr1; invs IHr2.
  + apply null_emptystr.
    constructor.
    auto.
  + apply null_emptystr.
    constructor.
    auto.
  + apply null_emptystr.
    constructor.
    auto.
  + apply null_emptyset.
    untie.
    invs H2.
    invs H4; contradiction.
- cbn.
  invs IHr.
  + apply null_emptyset.
    cbn.
    untie.
    invs H0.
    contradiction.
  + apply null_emptystr.
    cbn.
    constructor.
    assumption.
- cbn.
  invs IHr1;
  invs IHr2.
  + apply null_emptystr.
    destruct_concat_lang.
    exists [].
    exists [].
    exists eq_refl.
    split; assumption.
  + apply null_emptyset.
    untie.
    invs H2.
    wreckit.
    listerine.
    contradiction.
  + apply null_emptyset.
    untie.
    invs H2.
    wreckit.
    listerine.
    contradiction.
  + apply null_emptyset.
    untie.
    invs H2.
    wreckit.
    listerine.
    contradiction.
- cbn.
  apply null_emptystr.
  constructor.
Qed.

Theorem null_def_implies_null:
  forall (r s: regex),
  null_def r = s -> null r s.
Proof.
intros.
rewrite <- H.
apply null_is_null_def.
Qed.

Theorem null_def_is_emptystr_or_emptyset: forall (r: regex),
  (null_def r = emptystr) \/ (null_def r = emptyset).
Proof.
intros.
induction r.
- cbn. auto.
- cbn. auto.
- cbn. auto.
- cbn. destruct IHr1; destruct IHr2; rewrite H; (try rewrite H0); auto.
- cbn. destruct IHr; rewrite H; cbn; auto.
- cbn. destruct IHr1; destruct IHr2; rewrite H; (try rewrite H0); auto.
- cbn. auto.
Qed.

Theorem null_implies_null_def:
  forall (r s: regex),
  null r s -> null_def r = s.
Proof.
intros.
inversion_clear H.
- induction r.
  + inversion H0.
  + cbn. reflexivity.
  + inversion H0.
  + invs H0. wreckit.
    * apply IHr1 in B as B1.
      cbn.
      rewrite B1.
      reflexivity.
    * apply IHr2 in B as B1.
      cbn.
      rewrite B1.
      specialize null_def_is_emptystr_or_emptyset with (r := r1).
      intros.
      destruct H; rewrite H; reflexivity.
  + invs H0.
    cbn.
    specialize null_def_is_emptystr_or_emptyset with (r := r).
    intros.
    destruct H0.
    * apply null_def_implies_null in H0.
      invs H0.
      contradiction.
    * rewrite H0.
      cbn.
      reflexivity.
  + invs H0. listerine. subst.
    remember (IHr1 H1).
    remember (IHr2 H2).
    cbn.
    rewrite e.
    rewrite e0.
    reflexivity.
  + cbn. reflexivity.
- induction r.
  + cbn. reflexivity.
  + exfalso.
    apply H0.
    constructor.
  + cbn. reflexivity.
  + cbn.
    specialize null_def_is_emptystr_or_emptyset with (r := r1).
    specialize null_def_is_emptystr_or_emptyset with (r := r2).
    intros Dr1 Dr2.
    destruct Dr1, Dr2; rewrite H; (try rewrite H1);
    apply null_def_implies_null in H;
    apply null_def_implies_null in H1;
    invs H; invs H1.
    * exfalso. apply H0. cbn. constructor. auto.
    * exfalso. apply H0. cbn. constructor. auto.
    * exfalso. apply H0. cbn. constructor. auto.
    * reflexivity.
  + cbn.
    specialize null_def_is_emptystr_or_emptyset with (r := r).
    intros Dr.
    cbn in H0.
    destruct Dr; rewrite H; cbn;
    apply null_def_implies_null in H.
    * reflexivity.
    * invs H. exfalso. apply H0. constructor. assumption.
  + cbn.
    remember (null_def r1) as dr1.
    remember (null_def r2) as dr2.
    symmetry in Heqdr1.
    symmetry in Heqdr2.
    apply null_def_implies_null in Heqdr1.
    apply null_def_implies_null in Heqdr2.
    induction dr1; inversion_clear Heqdr1.
    * reflexivity.
    * induction dr2; inversion_clear Heqdr2.
      -- reflexivity.
      -- exfalso.
         apply H0.
         destruct_concat_lang.
         exists [].
         exists [].
         exists eq_refl.
         split; assumption.
  + exfalso.
    apply H0.
    constructor.
Qed.

Theorem null_iff_null_def:
  forall (r s: regex),
  null_def r = s <-> null r s.
Proof.
split.
apply null_def_implies_null.
apply null_implies_null_def.
Qed.

Theorem null_is_emptystr_or_emptyset (r: regex):
  null_def r = emptystr \/ null_def r = emptyset.
Proof.
induction r.
- right.
  cbn; reflexivity.
- left.
  cbn; reflexivity.
- right.
  cbn; reflexivity.
- wreckit; (cbn;
  try rewrite B0;
  try rewrite B);
  auto.
- wreckit; cbn; rewrite B; auto.
- wreckit; (cbn;
    try rewrite B0;
    try rewrite B);
    auto.
- left.
  cbn.
  reflexivity.
Qed.

Theorem null_only_emptyset_or_emptystr (r: regex):
  null r emptyset \/ null r emptystr.
Proof.
specialize denotation_is_decidable with (r := r) (s := []).
intros.
destruct H.
- right. constructor. assumption.
- left. constructor. assumption.
Qed.
