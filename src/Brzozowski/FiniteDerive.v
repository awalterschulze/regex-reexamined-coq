Require Import CoqStock.List.

Require Import Brzozowski.Alphabet.
Require Import Brzozowski.CompareRegex.
Require Import Brzozowski.Language.
Require Import Brzozowski.Null.
Require Import Brzozowski.Regex.

(* finite_or merges two regexes.
It applies a merge sort on the root ors, while removing duplicates.
It can do this because of the following properties:
  idempotency: r + r = r
  commutativity: r + s = s + r
  associativity: (r + s) + t = r + (s + t)
It does this to normalize the regular expression.
It assumes the two regexes that is provided as input is already sorted with duplicates removed.

For a Fixpoint function Coq always needs to know which argument is decreasing.
For finite_or either `r` or `s` is decreasing, which is confusing to the termination checker, we need to be consistent.
We introduce a closure fixpoint `finite_or_r` inside of our fixpoint `finite_or`.
finite_or's descreasing argument is always `r` and
finite_or_r's decreasing argument is always `s`, while `r` is not decreasing and is the original `r`, hence `_or_r`.

For another example for a closure fixpoint inside a fixpoint, see the merge function in:
https://coq.inria.fr/library/Coq.Sorting.Mergesort.html
*)
Fixpoint finite_or (r s: regex) : regex :=
  let fix finite_or_r s :=
    match r with
    | or r_1 r_next =>
      match s with
      | or s_1 s_next =>
        match compare_regex r_1 s_1 with
        | Lt => or r_1 (finite_or r_next s)
        | Eq => or r_1 (finite_or r_next s_next)
        | Gt => or s_1 (finite_or_r s_next)
        end
      | _ =>
        match compare_regex r_1 s with
        | Lt => or r_1 (finite_or r_next s)
        | Eq => r
        | Gt => or s r
        end
      end
    | _ =>
      match s with
      | or s_1 s_next =>
        match compare_regex r s_1 with
        | Lt => or r s
        | Eq => s
        | Gt => or s_1 (finite_or_r s_next)
        end
      | _ =>
        match compare_regex r s with
        | Lt => or r s
        | Eq => s
        | Gt => or s r
        end
      end
    end
  in finite_or_r s.

Fixpoint finite_derive_def (r: regex) (a: alphabet) : regex :=
  match r with
  | emptyset => emptyset
  | emptystr => emptyset
  | symbol b =>
    if (eqa b a)
    then emptystr
    else emptyset
  | or s t => finite_or (finite_derive_def s a) (finite_derive_def t a)
  | neg s => neg (finite_derive_def s a)
  | concat s t =>
    or (concat (finite_derive_def s a) t)
       (concat (null_def s) (finite_derive_def t a))
  | star s => concat (finite_derive_def s a) (star s)
  end.

Definition finite_derive_defs (r: regex) (s: str) : regex :=
  fold_left finite_derive_def s r.

(* finite_or_step rewrite finite_or without an fix closure,
   which was just there so Coq can see that the function is terminating.
   This way the function is easier to read and smaller steps can be taken inside proofs.
*)
Theorem finite_or_step: forall (r s: regex),
  finite_or r s = match r with
  | or r_1 r_next =>
    match s with
    | or s_1 s_next =>
      match compare_regex r_1 s_1 with
      | Lt => or r_1 (finite_or r_next s)
      | Eq => or r_1 (finite_or r_next s_next)
      | Gt => or s_1 (finite_or r s_next)
      end
    | _ =>
      match compare_regex r_1 s with
      | Lt => or r_1 (finite_or r_next s)
      | Eq => r
      | Gt => or s r
      end
    end
  | _ =>
    match s with
    | or s_1 s_next =>
      match compare_regex r s_1 with
      | Lt => or r s
      | Eq => s
      | Gt => or s_1 (finite_or r s_next)
      end
    | _ =>
      match compare_regex r s with
      | Lt => or r s
      | Eq => s
      | Gt => or s r
      end
    end
  end.
Proof.
induction r, s; simpl; trivial.
Qed.
