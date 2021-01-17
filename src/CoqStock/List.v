(*
This module replaces the standard library's List module.
It reexports Coq.Lists.List and Coq.Lists.List.ListNotations.
It includes extra theorems about lists.
*)

Require Export Coq.Lists.List.
Export Coq.Lists.List.ListNotations.
Require Import Coq.micromega.Lia.

Create HintDb list.

Theorem length_zero_string_is_empty {A: Type} (xs: list A):
  length xs = 0 -> xs = [].
Proof.
  apply length_zero_iff_nil.
Qed.

(* The command Hint Resolve adds a new candidate proof step *)
#[export]
Hint Resolve length_zero_string_is_empty: list.

Example example_length_zero_string_is_empty_with_auto {A: Type} (xs: list A):
  length xs = 0 -> xs = [].
Proof.
  debug auto with list. (* To see steps taken, see: debug auto with list *)
Qed.

#[export]
Hint Resolve
  Coq.Lists.List.nil_cons (* [] <> x :: l *)
  Coq.Lists.List.app_nil_l (* [] ++ l = l *)
  Coq.Lists.List.app_nil_r (* l ++ [] = l *)
  Coq.Lists.List.app_assoc (* l ++ m ++ n = (l ++ m) ++ n *)
  Coq.Lists.List.app_assoc_reverse (* (l ++ m) ++ n = l ++ m ++ n *)
  Coq.Lists.List.app_comm_cons (* a :: (x ++ y) = (a :: x) ++ y *)
  Coq.Lists.List.app_cons_not_nil (* [] <> x ++ a :: y *)
  Coq.Lists.List.app_eq_unit (* x ++ y = [a] -> x = [] /\ y = [a] \/ x = [a] /\ y = [] *)
  Coq.Lists.List.app_inj_tail (* x ++ [a] = y ++ [b] -> x = y /\ a = b *)
  Coq.Lists.List.app_nil_end (* l = l ++ [] *)
  Coq.Lists.List.app_length (* length (l++l') = length l + length l' *)
  Coq.Lists.List.last_length (* length (l ++ a :: nil) = S (length l) *)
  : list.

Hint Rewrite
  Coq.Lists.List.app_nil_l (* [] ++ l = l *)
  Coq.Lists.List.app_nil_r (* l ++ [] = l *)
  Coq.Lists.List.app_length (* length (l++l') = length l + length l' *)
  Coq.Lists.List.last_length (* length (l ++ a :: nil) = S (length l) *)
  : list.

#[export]
Hint Unfold
  Init.Logic.iff
  Init.Logic.not
  : list.

#[export]
Hint Constructors
  Coq.Init.Logic.and
  Coq.Init.Logic.or
  : list.

Theorem lessthan_zero_is_zero:
  forall (n: nat),
  n <= 0 -> n = 0.
Proof.
intros.
inversion H.
reflexivity.
Qed.

#[export]
Hint Resolve
  lessthan_zero_is_zero
  : list.

Theorem length_zero_or_smaller_string_is_empty {A: Type} (xs: list A):
  length xs <= 0 -> xs = [].
Proof.
  intros.
  assert (length xs = 0).
  lia.
  rewrite length_zero_iff_nil in *.
  assumption.
Qed.

(*
  We can now prove the same theorem as
  `length_zero_or_smaller_string_is_empty`
  simply with `auto with list`,
  given all the hints we have added to the `list` database.
*)
Example example_length_zero_or_smaller_string_is_empty_with_auto {A: Type} (xs: list A):
  length xs <= 0 -> xs = [].
Proof.
  auto with list.
Qed.

#[export]
Hint Resolve
  Coq.Lists.List.firstn_nil (* firstn n [] = [] *)
  Coq.Lists.List.firstn_cons (* firstn (S n) (a::l) = a :: (firstn n l) *)
  Coq.Lists.List.firstn_all (* firstn (length l) l = l *)
  Coq.Lists.List.firstn_all2 (* (length l) <= n -> firstn n l = l *)
  Coq.Lists.List.firstn_O (* firstn 0 l = [] *)
  Coq.Lists.List.firstn_le_length (* length (firstn n l) <= n *)
  Coq.Lists.List.firstn_length_le (* n <= length l -> length (firstn n l) = n *)
  Coq.Lists.List.firstn_app (* firstn n (l1 ++ l2) = (firstn n l1) ++ (firstn (n - length l1) l2) *)
  Coq.Lists.List.firstn_app_2 (* firstn ((length l1) + n) (l1 ++ l2) = l1 ++ firstn n l2 *)
  Coq.Lists.List.firstn_firstn (* firstn i (firstn j l) = firstn (min i j) l *)
  Coq.Lists.List.firstn_skipn_comm (* firstn m (skipn n l) = skipn n (firstn (n + m) l) *)
  Coq.Lists.List.skipn_firstn_comm (* skipn m (firstn n l) = firstn (n - m) (skipn m l) *)
  Coq.Lists.List.skipn_O (* skipn 0 l = l *)
  Coq.Lists.List.skipn_nil (* skipn n ([] : list A) = [] *)
  Coq.Lists.List.skipn_cons (* skipn (S n) (a::l) = skipn n l *)
  Coq.Lists.List.skipn_all (* skipn (length l) l = nil *)
  Coq.Lists.List.skipn_all2 (* length l <= n -> skipn n l = [] *)
  Coq.Lists.List.firstn_skipn (* firstn n l ++ skipn n l = l *)
  Coq.Lists.List.firstn_length (* length (firstn n l) = min n (length l) *)
  Coq.Lists.List.skipn_length (* length (skipn n l) = length l - n *)
  Coq.Lists.List.skipn_app (* skipn n (l1 ++ l2) = (skipn n l1) ++ (skipn (n - length l1) l2) *)
  : list.

Hint Rewrite
  Coq.Lists.List.firstn_nil (* firstn n [] = [] *)
  Coq.Lists.List.firstn_cons (* firstn (S n) (a::l) = a :: (firstn n l) *)
  Coq.Lists.List.firstn_all (* firstn (length l) l = l *)
  Coq.Lists.List.firstn_O (* firstn 0 l = [] *)
  Coq.Lists.List.skipn_O (* skipn 0 l = l *)
  Coq.Lists.List.skipn_nil (* skipn n ([] : list A) = [] *)
  Coq.Lists.List.skipn_cons (* skipn (S n) (a::l) = skipn n l *)
  Coq.Lists.List.skipn_all (* skipn (length l) l = nil *)
  Coq.Lists.List.skipn_length (* length (skipn n l) = length l - n *)
  Coq.Lists.List.firstn_skipn (* firstn n l ++ skipn n l = l *)
  : list.

Theorem firstn_app_length {A: Type} (xs ys: list A):
  firstn (length xs) (xs ++ ys) = xs.
Proof.
intros.
set (firstn_app (length xs) xs ys) as Hfirst.
replace (length xs - length xs) with 0 in * by lia.
rewrite app_nil_r in Hfirst.
replace (firstn (length xs) xs) with xs in Hfirst by (symmetry; apply firstn_all).
assumption.
Qed.

Theorem skipn_app_length {A: Type} (xs ys: list A):
  skipn (length xs) (xs ++ ys) = ys.
Proof.
intros.
set (skipn_app (length xs) xs ys) as Hlast.
replace (length xs - length xs) with 0 in * by lia.
replace (skipn (length xs) xs) with (nil: list A) in Hlast by (symmetry; apply skipn_all).
rewrite app_nil_l in Hlast.
replace (skipn 0 ys) with ys in Hlast by (apply skipn_O).
assumption.
Qed.

#[export]
Hint Resolve
  firstn_app_length
  skipn_app_length
  : list.

Theorem split_list {A: Type} (xs: list A) (n : nat):
  forall (ys zs: list A),
    length ys = n ->
    xs = ys ++ zs ->
    ys = firstn n xs /\
    zs = skipn n xs.
Proof.
  intros.
  subst.
  auto with list.
Qed.

Lemma prefix_leq_length {A: Type} (xs ys zs: list A):
  xs = ys ++ zs -> length ys <= length xs.
Proof.
  intro H.
  subst.
  autorewrite with list.
  lia.
Qed.

#[export]
Hint Resolve
  split_list
  prefix_leq_length
  : list.

Lemma skipn_length_prefix_is_suffix {A: Type} (prefix suffix: list A):
  skipn (length prefix) (prefix ++ suffix) = suffix.
Proof.
auto with list.
Qed.

(* TODO: Help Wanted
Cannot infer the implicit parameter A of skipn_length_prefix_is_suffix
whose type is "Type".
Hint Rewrite
  skipn_length_prefix_is_suffix
  : list.
*)

Lemma firstn_length_prefix_is_prefix {A: Type} (prefix suffix: list A):
  firstn (length prefix) (prefix ++ suffix) = prefix.
Proof.
auto with list.
Qed.

(* TODO: Help Wanted
Cannot infer the implicit parameter A of firstn_length_prefix_is_prefix
whose type is "Type".
Hint Rewrite
  firstn_length_prefix_is_prefix
  : list.
*)

Theorem prefix_length_leq:
  forall {A: Type} (prefix suffix list: list A),
  prefix ++ suffix = list -> length prefix <= length list.
Proof.
intros.
rewrite <- H.
autorewrite with list.
auto with arith.
Qed.

#[export]
Hint Resolve
  prefix_length_leq
  : list.

Theorem length_gt_zero:
  forall {A: Type} (xs: list A),
  xs <> [] -> 0 < length xs.
Proof.
induction xs.
- contradiction.
- cbn.
  lia.
Qed.

#[export]
Hint Resolve
  length_gt_zero
  : list.

Theorem prefix_is_gt_zero_and_leq:
  forall {A: Type} (prefix suffix list: list A),
  (prefix <> []) -> prefix ++ suffix = list ->
  (0 < length prefix <= length list).
Proof.
intros.
remember (prefix_length_leq prefix suffix list).
remember (length_gt_zero prefix).
(* This theorem clearly follows by the above theorems. *)
auto.
Qed.

#[export]
Hint Resolve
  prefix_is_gt_zero_and_leq
  : list.

Theorem prefix_is_not_empty_with_index_gt_zero:
  forall {A: Type} (xs: list A) (index: nat) (index_range: 0 < index <= length xs),
    firstn index xs <> [].
Proof.
intros.
induction index.
- lia.
- destruct index_range.
  induction xs.
  + cbn in H0. lia.
  + cbn. auto with list.
Qed.

#[export]
Hint Resolve
  prefix_is_not_empty_with_index_gt_zero
  : list.
