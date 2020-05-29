Require Import List.
Import ListNotations.

(* Alphabet is Sigma_k *)
(* We are defining it here as a1 and x0, but we could do any disjoint set *)
Inductive alphabet := a1 | a0.

Lemma alphabet_disjoint: forall (x y: alphabet),
  x = y \/ x <> y.
Proof.
(* This is the exact usecase for the decide equality tactic.
   It only works when the type of x and y is a simple inductive type.
*)
decide equality.
Qed.

Lemma alphabet_disjoint': forall (x y: alphabet),
  x = y \/ x <> y.
Proof.
destruct x, y.
- left. reflexivity.
- right. discriminate.
- right. discriminate.
- left. reflexivity.
Qed. 

Definition string := (list alphabet).

(*
**Definition 2.1.** A regular expression is defined recursively as follows:
1. The symbols of the alphabet $\Sigma_k$, $\lambda$ and $\emptyset$ are regular expressions.
2. If $P$ and $Q$ are regular expressions, then so are $P.Q$, $P^*$, and $f(P, Q)$,
   where $f$ is any Boolean function of $P$ and $Q$.
3. Nothing else is a regular expression unless its being so follows from a
   finite number of applications of Rules 1 and 2.
*)

Inductive regex :=
  | emptyset : regex
  | lambda : regex
  | symbol : alphabet -> regex
  | concat : regex -> regex -> regex
  | star : regex -> regex
  (* We can use nor to express f, 
     Since any Boolean function can be expressed using a finite number of sums and complements
     See https://en.wikipedia.org/wiki/Logical_NOR
     P | Q | P `nor` Q
     -----------------
     T | T | F
     T | F | F
     F | T | F
     F | F | T
  *)
  | nor : regex -> regex -> regex
  .

Definition complement (r: regex) : regex :=
  nor r r.

Definition and (r s: regex) : regex :=
  nor (nor r r) (nor s s).

Definition or (r s: regex) : regex :=
  nor (nor r s) (nor r s).

(* See https://en.wikipedia.org/wiki/Exclusive_or *)
Definition xor (r s: regex) : regex :=
  or (and r (complement s)) (and (complement r) s).

Definition I: regex :=
  complement (emptyset).

(*  A regular expression represents a set of sequences.
    We define the following operations on sets of sequences: 
    If $P$ and $Q$ are two sets of sequences of symbols from our alphabet, $\Sigma_k$, we have:
*)

Inductive is_member: regex -> string -> Prop :=
  | is_member_lambda :
    is_member lambda []
  | is_member_symbol (a: alphabet) :
    is_member (symbol a) [a]
  (*
    *Product or Concatenation*. $(P.Q) = \{ s | s = p.q; p \in P, q \in Q \}$.
    (Sometimes the dot is omitted for convenience. Also, since the operation is associative we omit parentheses.)
  *)
  | is_member_concat (p q: regex) (s: string):
    (exists
      (p_s: string)
      (q_s: string)
      (pq_s: p_s ++ q_s = s),
      is_member p p_s /\
      is_member q q_s
    ) ->
    is_member (concat p q) s
  (*
    *Iterate or Star Operation*. $P^{*} = \cup_{0}^{\infty} P^n$ , where $P^2 = P.P$, etc. 
    and $P^0 = \lambda$, the set consisting of the sequence of zero length, 
    which has the property $\lambda . R = R .\lambda = R$.
  *)
  | is_member_star_0 (p: regex):
    is_member (star p) []
  | is_member_star_n (p: regex) (s: string):
    is_member (concat p (star p)) s ->
    is_member (star p) s
  (*
    *Boolean function*. We shall denote any Boolean function of $P$ and $Q$ by $f(P, Q)$. 
    Of course, all the laws of Boolean algebra apply.
    `nor` is used to emulate `f`, since nor can be used to emulate all boolean functions.
  *)
  | is_member_nor (p q: regex) (s: string):
    not_member p s ->
    not_member q s ->
    is_member (nor p q) s
(* 
  See how even and odd are defined in:
  http://www.cs.umd.edu/class/fall2019/cmsc631/res/IndPrinciples.html 
*)
with not_member: regex -> string -> Prop :=
  (*
    The empty set is denoted by $\emptyset$ and the universal set by $I$.
    Thus we have the complement $P'$ (with respect to $I$) of $P$,
  *)
  | not_member_emptyset (s: string):
    not_member emptyset s
  | not_member_lambda (s: string):
    (s <> []) ->
    not_member lambda s
  | not_member_symbol (a: alphabet) (s: string):
    (s <> [a]) ->
    not_member (symbol a) s
  | not_member_concat (p q: regex) (s: string):
    (forall
      (p_s: string)
      (q_s: string)
      (pq_s: p_s ++ q_s = s),
      not_member p p_s \/
      not_member q q_s
    ) ->
    not_member (concat p q) s
  | not_member_star (p: regex) (s: string):
    (s <> []) ->
    not_member (concat p (star p)) s ->
    not_member (star p) s
  | not_member_nor_l (p q: regex) (s: string):
    is_member p s ->
    not_member (nor p q) s
  | not_member_nor_r (p q: regex) (s: string):
    is_member q s ->
    not_member (nor p q) s
  .

  (* the *intersection* $P \& Q$, *)
Theorem is_member_intersection: forall (p q: regex) (s: string),
  is_member p s ->
  is_member q s ->
  is_member (and p q) s.
Proof.
  intros.
  constructor.
  - constructor.
    assumption.
  - constructor.
    assumption.
Qed.  

(* the sum or union $P + Q$, *)
Theorem is_member_union_l: forall (p q: regex) (s: string),
  is_member p s ->
  is_member (or p q) s.
Proof.
intros.
constructor.
- constructor.
  assumption.
- constructor.
  assumption.
Qed.  

Theorem is_member_union_r: forall (p q: regex) (s: string),
  is_member q s ->
  is_member (or p q) s.
Proof.
intros.
constructor.
- apply not_member_nor_r.
  assumption.
- apply not_member_nor_r.
  assumption.
Qed.

Theorem is_member_not: forall (p: regex) (s: string),
  not_member p s ->
  is_member (complement p) s.
Proof.
intros.
constructor.
- assumption.
- assumption.
Qed.  

Theorem not_member_not: forall (p: regex) (s: string),
    is_member p s ->
    not_member (complement p) s.
Proof.
intros.
constructor.
assumption.
Qed.

Theorem not_member_intersection_l: forall (p q: regex) (s: string),
    not_member p s ->
    not_member (and p q) s.
Proof.
intros.
constructor.
constructor.
- assumption.
- assumption.
Qed.  

Theorem not_member_intersection_r: forall (p q: regex) (s: string),
    not_member q s ->
    not_member (and p q) s.
Proof.
intros.
unfold and.
apply not_member_nor_r.
constructor; assumption.
Qed.

Theorem not_member_union: forall (p q: regex) (s: string),
    not_member p s ->
    not_member q s ->
    not_member (or p q) s.
Proof.
intros.
unfold or.
constructor.
constructor; assumption.
Qed.

(*
   TODO: Good First Issue
   Add the modulo-two sum (exclusive OR) $P \oplus Q$, etc.
*)

Lemma is_member_or_not_member_symbol: forall (a: alphabet) (s: string),
  is_member (symbol a) s \/ not_member (symbol a) s.
Proof.
induction s.
- right.
  constructor.
  discriminate.
- induction s.
  (* TODO: Help Wanted 
     Is there a better way (maybe a tatic)
     to show that a = a2 \/ a <> a2
     without proving a Lemma about it first.
  *)
  + remember (alphabet_disjoint a2 a). 
    case o.
    * intros.
      rewrite H.
      left.
      constructor.
    * intros.
      right.
      constructor.
      injection.
      unfold not in H.
      assumption.
  + right.
    constructor.
    discriminate.
Qed.

Lemma is_member_or_not_member_emptyset: forall (s: string),
  (is_member emptyset s) \/ (not_member emptyset s).
Proof.
intros.
right.
constructor.
Qed.

Lemma is_member_or_not_member_lambda: forall (s: string),
  (is_member lambda s) \/ (not_member lambda s).
Proof.
destruct s.
- left.
  constructor.
- right.
  constructor.
  discriminate.
Qed.

Lemma is_member_or_not_member_concat: forall (r1 r2: regex) (s: string),
  is_member (concat r1 r2) s \/ not_member (concat r1 r2) s.
Proof.
(* TODO: Help Wanted *)
Abort.

Lemma is_member_or_not_member_star: forall (r: regex) (s: string),
  is_member (star r) s \/ not_member (star r) s.
Proof.
(* TODO: Help Wanted *)
Abort.

Lemma is_member_or_not_member_nor: forall (r1 r2: regex) (s: string),
  is_member (nor r1 r2) s \/ not_member (nor r1 r2) s.
Proof.
(* TODO: Help Wanted *)
Abort.

Theorem is_member_or_not_member : forall (r: regex) (s: string),
    (is_member r s) \/ (not_member r s).
Proof.
induction r.
- apply is_member_or_not_member_emptyset.
- apply is_member_or_not_member_lambda.
- apply is_member_or_not_member_symbol.
(*
- apply is_member_or_not_member_concat.
- apply is_member_or_not_member_star.
- apply is_member_or_not_member_nor.
*)
(* TODO: Help Wanted *)
Abort.

Lemma is_member_not_member_dec : forall (r: regex) (s: string),
    {is_member r s} + {not_member r s}.
Proof.
(* TODO: Help Wanted *)
Abort.

Lemma is_member_false_not_member : forall (r: regex) (s: string),
    (is_member r s -> False) -> not_member r s.
Proof.
(* TODO: Help Wanted *)
Abort.

Lemma not_member_false_is_member : forall (r: regex) (s: string),
    (not_member r s -> False) -> is_member r s.
Proof.
(* TODO: Help Wanted *)
Abort.

Lemma not_member_is_member_false : forall (r: regex) (s: string),
    not_member r s -> is_member r s -> False.
Proof.
intros.
inversion H; subst.
- inversion H0.
- inversion H0.
  rewrite <- H3 in H1.
  contradiction.
- inversion H0.
  rewrite <- H2 in H1.
  contradiction.
(* TODO: Help Wanted *)
Abort.

Lemma is_member_not_member_false : forall (r: regex) (s: string),
    is_member r s -> not_member r s -> False.
Proof.
(* TODO: Help Wanted *)
Abort.

Lemma is_member_emptyset_false: 
    forall (p: string),
    is_member emptyset p -> False.
Proof.
intros.
inversion H.
Qed.

Lemma not_member_is_is_member_complement : forall (r: regex) (s: string),
    not_member r s -> is_member (complement r) s.
Proof.
intros.
apply is_member_not.
apply H.
Qed.

Lemma is_member_not_is_not_member : forall (r: regex) (s: string),
    is_member (complement r) s -> not_member r s.
Proof.
intros.
inversion H; subst.
- assumption.
Qed.

(* \lambda.R = R.\lambda = R *)

Theorem expand_concat_lambda_l: forall (r: regex) (s: string),
    is_member r s -> is_member (concat lambda r) s.
Proof.
- intros.
  apply (is_member_concat lambda r s).
  exists [].
  exists s.
  cbn.
  assert (s = s).
  reflexivity.
  exists H0.
  split.
  + apply is_member_lambda.
  + apply H.
Qed.

Theorem collapse_concat_lambda_l: forall (r: regex) (s: string),
    is_member (concat lambda r) s -> is_member r s.
Proof.
intros.
inversion H.
subst.
inversion H3.
inversion H0.
inversion H1.
inversion H2.
subst.
inversion H4.
cbn.
assumption.
Qed.

Theorem expand_concat_lambda_r: forall (r: regex) (s: string),
    is_member r s -> is_member (concat r lambda) s.
Proof.
intros.
constructor.
exists s.
exists [].
assert (s ++ [] = s). {
  rewrite app_nil_end.
  reflexivity.
}
exists H0.
constructor.
- assumption.
- constructor.
Qed.

Theorem collapse_concat_lambda_r: forall (r: regex) (s: string),
    is_member (concat r lambda) s -> is_member r s.
Proof.
intros.
inversion H.
inversion H3.
inversion H4.
inversion H5.
inversion H6.
subst.
inversion H8.
rewrite <- app_nil_end.
assumption.
Qed.

(*
The introduction of arbitrary Boolean functions enriches the language of regular expressions. 
For example, suppose we desire to represent the set of all sequences having three consecutive 1's 
but not those ending in 01 or consisting of 1's only. 
The desired expression is easily seen to be:

R = (I.1.1.1.I)\&(I.0.1+1.1^{*})'.
*)
Definition x1 := symbol a1.
Definition x0 := symbol a0.
Definition xI111I := concat I (concat x1 (concat x1 (concat x1 I))).
Definition xI01 := concat I (concat x0 x1).
Definition x11star := concat x1 (star x1).
Definition exampleR := and xI111I (complement (or xI01 x11star)).

Lemma test_member_xI01_101:
    is_member xI01 ([a1] ++ [a0] ++ [a1]).
Proof.
unfold xI01.
apply is_member_concat.
exists [a1].
exists ([a0] ++ [a1]).
split.
- constructor.
- split.
  + constructor.
    * constructor.
    * constructor. 
  + constructor.
    * exists [a0]. exists [a1].
      assert ([a0] ++ [a1] = [a0] ++ [a1]).
      reflexivity.
      exists H.
      split.
      constructor.
      constructor.
Qed.

Lemma test_not_member_xI01_101_false:
    not_member xI01 ([a1] ++ [a0] ++ [a1]) -> False.
Proof.
(* TODO: Help Wanted *)
Abort.

Lemma test_not_member_xI01_empty:
    not_member xI01 [].
Proof.
constructor.
intros.
remember (app_eq_nil p_s q_s pq_s).
destruct a.
right.
apply not_member_concat.
intros.
rewrite e0 in pq_s0.
remember (app_eq_nil p_s0 q_s0 pq_s0).
destruct a.
rewrite e1.
rewrite e2.
left.
constructor.
discriminate.
Qed.

Lemma list_app_eq_unit_2 : forall (A: Type) (xs ys: list A) (x y: A),
    xs ++ ys = [x;y] <->
    (xs = [] /\ ys = [x;y])
    \/ (xs = [x] /\ ys = [y])
    \/ (xs = [x;y] /\ ys = []).
Proof.
(* TODO: Good First Issue *)
Admitted.

Local Ltac breakdown :=
    repeat match goal with
            | [ H: _ \/ _ |- _ ] =>
                destruct H
            | [ H: _ /\ _ |- _ ] =>
                destruct H
            | [ H: ?X ++ ?Y = ?XS ++ ?YS |- _ ] =>
                cbn in H
            | [ H: ?XS ++ ?YS = [?X;?Y] |- _ ] =>
                apply (list_app_eq_unit_2 alphabet XS YS X Y) in H
           end.

Lemma test_not_member_xI01_10:
    not_member xI01 ([a1] ++ [a0]).
Proof.
unfold xI01.
apply not_member_concat.
intros p' q' H_p_app_q.
right.
constructor.
intros p0 q0 H_p0_app_q0.
rewrite <- H_p0_app_q0 in H_p_app_q.
breakdown.
- left.
  constructor.
  rewrite H0.
  discriminate.
- left.
  constructor.
  rewrite H0.
  discriminate.
- left.
  constructor.
  rewrite H0.
  discriminate.
- apply app_eq_unit in H0.
  breakdown.
  + left.
    constructor.
    rewrite H0.
    discriminate.
  + right.
    constructor.
    rewrite H1.
    discriminate.
- apply app_eq_nil in H0.
  breakdown.
  left.
  constructor.
  rewrite H0.
  discriminate.
Qed.

Lemma list_fst1: forall (A: Type) (x: A) (y: A) (xs: list A) (ys: list A),
    x :: xs = [y] ++ ys ->
    x = y /\ xs = ys.
Proof.
(* TODO: Good First Issue *)
Admitted.

Lemma list_fst2: forall (A: Type) (x: A) (y: A) (xy: x <> y) (xs ys zs: list A),
    xs ++ ys = x :: zs ->
    xs <> [y].
Proof.
(* TODO: Good First Issue *)
Admitted.

Lemma list_three: forall (A: Type) (x y z: A),
    [x; y; z] = [x; y] ++ [z].
Proof.
(* TODO: Good First Issue *)
Admitted.

Lemma list_last1: forall (A: Type) (x y: A) (xy: x <> y) (xs ys zs xs': list A),
    xs ++ ys ++ zs = xs' ++ [x] ->
    zs <> [y].
Proof.
(* TODO: Good First Issue *)
Admitted.

Lemma test_not_member_xI01_1110:
    not_member xI01 ([a1] ++ [a1] ++ [a1] ++ [a0]).
Proof.
unfold xI01.
apply not_member_concat.
intros.
destruct p_s.
- destruct q_s.
  + left. cbn. discriminate.
  + right.
    apply not_member_concat.
    intros.
    left.
    constructor.
    cbn in pq_s.
    rewrite pq_s in pq_s0.
    breakdown.
    apply list_fst1 in pq_s.
    assert (a1 <> a0) as a10. discriminate.
    apply (list_fst2 alphabet a1 a0 a10) in pq_s0.
    exact pq_s0.
- cbn in pq_s.
  apply list_fst1 in pq_s.
  destruct pq_s.
  right.
  apply not_member_concat.
  intros.
  rewrite <- pq_s in H0.
  right.
  constructor.
  assert (a0 <> a1) as a01. discriminate.
  rewrite list_three in H0.
  apply (list_last1 alphabet a0 a1 a01) in H0.
  exact H0.
Qed.

Lemma list_combo4: forall (A: Type) (x y: A) (xs ys: list A),
    xs ++ ys = [x;x;x;y] ->
    (xs = [] /\ ys = [x;x;x;y])
    \/ (xs = [x] /\ ys = [x;x;y])
    \/ (xs = [x;x] /\ ys = [x;y])
    \/ (xs = [x;x;x] /\ ys = [y])
    \/ (xs = [x;x;x;y] /\ ys = []).
Proof.
(* TODO: Good First Issue *)
Admitted.

Lemma list_combo3: forall (A: Type) (x y: A) (xs ys: list A),
    xs ++ ys = [x;x;y] ->
    (xs = [] /\ ys = [x;x;y])
    \/ (xs = [x] /\ ys = [x;y])
    \/ (xs = [x;x] /\ ys = [y])
    \/ (xs = [x;x;y] /\ ys = []).
Proof.
(* TODO: Good First Issue *)
Admitted.

Lemma test_not_member_x11star_0: 
    not_member x11star ([a0]).
Proof.
constructor.
intros.
apply app_eq_unit in pq_s.
breakdown.
- left.
  rewrite H.
  constructor.
  discriminate.
- left.
  rewrite H.
  constructor.
  discriminate.
Qed.

Lemma test_not_member_x11star_10: 
    not_member x11star ([a1] ++ [a0]).
Proof.
constructor.
intros.
cbn in pq_s.
apply list_app_eq_unit_2 in pq_s.
breakdown.
- left. rewrite H. constructor. discriminate.
- right. constructor.
  + rewrite H0. discriminate.
  + rewrite H0. apply test_not_member_x11star_0.
- left. rewrite H. constructor. discriminate.
Qed.  

Lemma test_not_member_x11star_110: 
    not_member x11star ([a1] ++ [a1] ++ [a0]).
Proof.
constructor.
intros.
cbn in pq_s.
apply list_combo3 in pq_s.
breakdown.
- left. rewrite H. constructor. discriminate.
- right. constructor.
  + rewrite H0. discriminate.
  + rewrite H0. apply test_not_member_x11star_10.
- left. rewrite H. constructor. discriminate.
- left. rewrite H. constructor. discriminate.
Qed.

Lemma test_not_member_x11star_1110: 
    not_member x11star ([a1] ++ [a1] ++ [a1] ++ [a0]).
Proof.
unfold x11star.
apply not_member_concat.
intros.
apply list_combo4 in pq_s.
breakdown.
- left. apply not_member_symbol. rewrite H. discriminate.
- right. constructor.
  + rewrite H0. discriminate.
  + rewrite H0. apply test_not_member_x11star_110.
- left. apply not_member_symbol. rewrite H. discriminate.
- left. apply not_member_symbol. rewrite H. discriminate.
- left. apply not_member_symbol. rewrite H. discriminate.
Qed.

Lemma test_member_xI111I_1110: 
    is_member xI111I ([a1] ++ [a1] ++ [a1] ++ [a0]).
Proof.
unfold xI111I.
rewrite <- app_nil_l.
apply is_member_concat.
exists [].
exists ([a1] ++ [a1] ++ [a1] ++ [a0]).
unfold I.
split.
reflexivity.
split.
apply is_member_not.
apply not_member_emptyset.
apply is_member_concat.
exists [a1].
exists ([a1] ++ [a1] ++ [a0]).
split.
reflexivity.
split.
apply is_member_symbol.
apply is_member_concat.
exists [a1].
exists ([a1] ++ [a0]).
split.
reflexivity.
split.
apply is_member_symbol.
apply is_member_concat.
exists [a1].
exists [a0].
split.
reflexivity.
split.
apply is_member_symbol.
apply is_member_not.
apply not_member_emptyset.
Qed.

Theorem test_exampleR_1110_member: 
    is_member exampleR ([a1] ++ [a1] ++ [a1] ++ [a0]).
Proof.
unfold exampleR.
apply is_member_intersection.
- apply test_member_xI111I_1110.
- apply is_member_not.
  apply not_member_union.
  + apply test_not_member_xI01_1110.
  + apply test_not_member_x11star_1110. 
Qed.

Theorem test_exampleR_111_not_member : not_member exampleR [a1; a1; a1].
Proof.
(* TODO: Help Wanted *)
Abort.

(*
    **Definition 3.2.** Given any set $R$ of sequences we define $\delta(R)$ to be

    $$
    \begin{aligned}
    \delta(R) & = \lambda\ \text{if}\ \lambda \in R \\
              & = \emptyset\ \text{if}\ \lambda \notin R \\
    \end{aligned}
    $$
*)

Inductive delta: regex -> regex -> Prop :=
    | delta_lambda (r: regex):
        is_member r [] ->
        delta r lambda
    | delta_emptyset (r: regex):
        not_member r [] ->
        delta r emptyset
    .

(*
    It is clear that:

    $$
    \begin{aligned}
    \delta(a) & = \emptyset\ \text{for any}\ a \in \Sigma_k, \\
    \delta(\lambda) & = \lambda, \text{and} \\
    \delta(\emptyset) & = \emptyset . \\
    \end{aligned}
    $$
*)

Theorem delta_lambda_is_lambda: delta lambda lambda.
Proof.
apply delta_lambda.
apply is_member_lambda.
Qed.

Theorem delta_emptyset_is_emptyset: delta emptyset emptyset.
Proof.
apply delta_emptyset.
apply not_member_emptyset.
Qed.

Theorem delta_symbol_is_emptyset: forall (a: alphabet),
    delta (symbol a) emptyset.
Proof.
intros.
apply delta_emptyset.
apply not_member_symbol.
discriminate.
Qed.

(*
    Furthermore

    $$
    \begin{aligned}
    \delta(P* ) &= \lambda\ \text{(by definition of * ), and} \\
    \delta(P.Q) &= \delta(P)\ \&\ \delta(Q).
    \end{aligned}
    $$
*)

Theorem delta_star_is_lambda: forall (r: regex),
    delta (star r) lambda.
Proof.
intros.
apply delta_lambda.
apply is_member_star_0.
Qed.

Theorem delta_concat_is_and_lambda: forall (p q: regex),
    delta p lambda ->
    delta q lambda ->
    delta (concat p q) lambda.
Proof.
intros.
constructor.
constructor.
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

Lemma list_cons_is_not_empty: forall {A: Type} (x: A) (xs ys: list A),
  xs ++ x :: ys = [] -> False.
Proof.
(*TODO: Good First Issue *)
Admitted.

Theorem delta_concat_is_and_emptyset_r: forall (p q: regex),
    delta p emptyset ->
    delta q lambda ->
    delta (concat p q) emptyset.
Proof.
intros.
inversion H.
inversion H0.
subst.
constructor.
constructor.
intros.
left.
assert (p_s = []).
- destruct q_s.
  + rewrite <- pq_s.
    apply app_nil_end.
  + apply list_cons_is_not_empty in pq_s.
    contradiction.
- subst.
  assumption.
Qed.

Theorem delta_concat_is_and_emptyset_l: forall (p q: regex),
    delta p lambda ->
    delta q emptyset ->
    delta (concat p q) emptyset.
Proof.
(* TODO: Good First Issue *)
Abort.

Theorem delta_concat_is_and_emptyset: forall (p q: regex),
    delta p emptyset ->
    delta q emptyset ->
    delta (concat p q) emptyset.
Proof.
(* TODO: Good First Issue *)
Abort.

(*
    If $R = f(P, Q)$ it is also easy to determine $\delta(R)$. For example,

    $$
    \begin{aligned}
    \text{(3.1)}&\ \delta(P + Q)    &= \delta(P) + \delta(Q). \\
    \text{(3.2)}&\ \delta(P\ \&\ Q) &= \delta(P)\ \&\ \delta(Q). \\
    \text{(3.3)}&\ \delta(P')       &= \lambda\ \text{if}\ \delta(P) = \emptyset \\
                &                   &= \emptyset\ \text{if}\ \delta(P) = \lambda \\
    \end{aligned}
    $$
*)

Theorem delta_or_lambda: forall (p q: regex),
    delta p lambda ->
    delta q lambda ->
    delta (or p q) lambda.
Proof.
constructor.
apply is_member_union_l.
inversion H.
assumption.
Qed.

Theorem delta_or_lambda_l: forall (p q: regex),
    delta p lambda ->
    delta q emptyset ->
    delta (or p q) lambda.
Proof.
intros.
constructor.
apply is_member_union_l.
inversion H.
assumption.
Qed.

Theorem delta_or_lambda_r: forall (p q: regex),
    delta p emptyset ->
    delta q lambda ->
    delta (or p q) lambda.
Proof.
(* TODO: Good First Issue *)
Abort.

Theorem delta_or_emptyset: forall (p q: regex),
    delta p emptyset ->
    delta q emptyset ->
    delta (or p q) emptyset.
Proof.
intros.
constructor.
apply not_member_union.
- inversion H.
  assumption.
- inversion H0.
  assumption.
Qed.

Theorem delta_and_lambda: forall (p q: regex),
    delta p lambda ->
    delta q lambda ->
    delta (and p q) lambda.
Proof.
(* TODO: Good First Issue *)
Abort.

Theorem delta_and_emptyset_r: forall (p q: regex),
    delta p emptyset ->
    delta q lambda ->
    delta (and p q) emptyset.
Proof.
intros.
constructor.
apply not_member_intersection_l.
inversion H.
assumption.
Qed.

Theorem delta_and_emptyset_l: forall (p q: regex),
    delta p lambda ->
    delta q emptyset ->
    delta (and p q) emptyset.
Proof.
(* TODO: Good First Issue *)
Abort.

Theorem delta_and_emptyset: forall (p q: regex),
    delta p emptyset ->
    delta q emptyset ->
    delta (and p q) emptyset.
Proof.
(* TODO: Good First Issue *)
Abort.

Theorem delta_not_emptyset: forall (r: regex),
    delta r lambda ->
    delta (complement r) emptyset.
Proof.
intros.
constructor.
inversion H.
constructor.
assumption.
Qed.

Theorem delta_not_lambda: forall (r: regex),
    delta r emptyset ->
    delta (complement r) lambda.
Proof.
intros.
constructor.
inversion H.
constructor.
- assumption.
- assumption. 
Qed.

(* TODO: Translate more proofs from the paper *)