Set Implicit Arguments.
Set Asymmetric Patterns.

Require Import CoqStock.comparable.
Require Import Reexamined.regex.

Fixpoint compare_regex {A: Type} {cmp: comparable A} (r s: regex A) : comparison :=
  match r with
  | fail => match s with
    | fail => Eq
    | _ => Lt
    end
  | empty => match s with
    | fail => Gt
    | empty => Eq
    | _ => Lt
    end
  | char x => match s with
    | fail => Gt
    | empty => Gt
    | char y => compare x y
    | _ => Lt
    end
  | or r1 r2 => match s with
    | fail => Gt
    | empty => Gt
    | char _ => Gt
    | or s1 s2 =>
      match compare_regex r1 s1 with
      | Lt => Lt
      | Eq => compare_regex r2 s2
      | Gt => Gt
      end
    | _ => Lt
    end
  | and r1 r2 => match s with
    | fail => Gt
    | empty => Gt
    | char _ => Gt
    | or _ _ => Gt
    | and s1 s2 =>
      match compare_regex r1 s1 with
      | Lt => Lt
      | Eq => compare_regex r2 s2
      | Gt => Gt
      end
    | _ => Lt
    end
  | concat r1 r2 => match s with
    | fail => Gt
    | empty => Gt
    | char _ => Gt
    | or _ _ => Gt
    | and _ _ => Gt
    | concat s1 s2 =>
      match compare_regex r1 s1 with
      | Lt => Lt
      | Eq => compare_regex r2 s2
      | Gt => Gt
      end
    | _ => Lt
    end
  | not r1 => match s with
    | fail => Gt
    | empty => Gt
    | char _ => Gt
    | or _ _ => Gt
    | and _ _ => Gt
    | concat _ _ => Gt
    | not s1 => compare_regex r1 s1
    | _ => Lt
    end
  | star r1 => match s with
    | star s1 => compare_regex r1 s1
    | _ => Gt
    end
  end.

Lemma test_compare_regex_char : forall 
  {A: Type}
  {cmp: comparable A}
  (x1 x2: A)
  (p: compare x1 x2 = Lt),
  compare_regex (char x1) (char x2) = Lt.
Proof. intros. simpl. now (rewrite p). Qed.

(* 
(or (char x1) (or (char x2) (or (char x2) (char x1))))
or
- x1
- or
  - x2
  - or
    - x2
    - x1
*)
Example example_compare_regex_or_all_left : forall {A: Type} {cmp: comparable A} (x1 x2: A) (p: compare x1 x2 = Lt),
  compare_regex (char x1) (or (char x2) (or (char x2) (char x1))) = Lt.
Proof. intros. simpl. reflexivity. Qed.

(*
(or (or (char x1) (char x2)) (or (char x2) (char x1)))
or
  - or
    - x1
    - x2
  - or
    - x2
    - x1
*)
Example example_compare_regex_or_symmetric: forall {A: Type} {cmp: comparable A} (x1 x2: A) (p: compare x1 x2 = Lt),
  compare_regex (or (char x1) (char x2)) (or (char x2) (char x1)) = Lt.
Proof. intros. simpl. now (rewrite p). Qed.

Lemma regex_proof_compare_eq_is_equal
    : forall {A: Type}
             {cmp: comparable A}
             (r1 r2: regex A) 
             (p: compare_regex r1 r2 = Eq)
    , r1 = r2.
Proof.
induction r1.
 - induction r2; simpl; trivial; discriminate. (* fail *)
 - induction r2; simpl; trivial; discriminate. (* empty *) 
 - induction r2; simpl; try discriminate. (* char *)
  + remember (compare a a0).
    induction c; simpl; try discriminate.
    * symmetry in Heqc.
      apply proof_compare_eq_is_equal in Heqc.
      rewrite <- Heqc.
      reflexivity.
 - induction r2; simpl; try discriminate. (* or *)
  + remember (compare_regex r1_1 r2_1).
    remember (compare_regex r1_2 r2_2).
    induction c; try discriminate.
    * induction c0; try discriminate.
      -- symmetry in Heqc.
         symmetry in Heqc0.
         remember (IHr1_1 r2_1).
         remember (e Heqc).
         rewrite e.
         remember (IHr1_2 r2_2).
         remember (e1 Heqc0).
         rewrite e2.
         reflexivity.
         apply Heqc.
 - induction r2; simpl; try discriminate. (* and *)
  + remember (compare_regex r1_1 r2_1).
    remember (compare_regex r1_2 r2_2).
    induction c; try discriminate.
    * induction c0; try discriminate.
      -- symmetry in Heqc.
         symmetry in Heqc0.
         remember (IHr1_1 r2_1).
         remember (e Heqc).
         rewrite e.
         remember (IHr1_2 r2_2).
         remember (e1 Heqc0).
         rewrite e2.
         reflexivity.
         apply Heqc.
 - induction r2; simpl; try discriminate. (* concat *)
  + remember (compare_regex r1_1 r2_1).
    remember (compare_regex r1_2 r2_2).
    induction c; try discriminate.
    * induction c0; try discriminate.
      -- symmetry in Heqc.
         symmetry in Heqc0.
         remember (IHr1_1 r2_1).
         remember (e Heqc).
         rewrite e.
         remember (IHr1_2 r2_2).
         remember (e1 Heqc0).
         rewrite e2.
         reflexivity.
         apply Heqc.
 - induction r2; simpl; try discriminate. (* not *)
  + remember (IHr1 r2).
    remember (IHr1 (not r2)).
    intros.
    remember (e p).
    rewrite e1.
    reflexivity.
 - induction r2; simpl; try discriminate. (* star *)
  + remember (IHr1 r2).
    remember (IHr1 (star r2)).
    intros.
    remember (e p).
    rewrite e1.
    reflexivity.
Qed.

Theorem regex_proof_compare_eq_reflex : forall {A: Type} {cmp: comparable A} (r: regex A), 
  compare_regex r r = Eq.
Proof.
induction r; try reflexivity; simpl.
- apply proof_compare_eq_reflex.
- rewrite IHr1. rewrite IHr2. reflexivity.
- rewrite IHr1. rewrite IHr2. reflexivity.
- rewrite IHr1. rewrite IHr2. reflexivity.
- rewrite IHr. reflexivity.
- rewrite IHr. reflexivity.
Qed.

Lemma regex_proof_compare_eq_trans
    : forall {A: Type}
             {cmp: comparable A}
             (x y z: regex A)
             (p: compare_regex x y = Eq)
             (q: compare_regex y z = Eq)
    , compare_regex x z = Eq.
Proof.
(* TODO: Good First Issue *)
Admitted.

Lemma regex_proof_compare_lt_trans
    : forall {A: Type}
             {cmp: comparable A}
             (x y z: regex A)
             (p: compare_regex x y = Lt)
             (q: compare_regex y z = Lt)
    , compare_regex x z = Lt.
Proof.
(* TODO: Good First Issue *)
Admitted.

Lemma regex_proof_compare_gt_trans
    : forall {A: Type}
             {cmp: comparable A}
             (x y z: regex A)
             (p: compare_regex x y = Gt)
             (q: compare_regex y z = Gt)
    , compare_regex x z = Gt.
Proof.
(* TODO: Good First Issue *)
Admitted.

Instance comparable_regex {A: Type} {cmp: comparable A} : comparable (regex A) :=
  { compare := compare_regex
  ; proof_compare_eq_is_equal := regex_proof_compare_eq_is_equal
  ; proof_compare_eq_reflex := regex_proof_compare_eq_reflex
  ; proof_compare_eq_trans := regex_proof_compare_eq_trans
  ; proof_compare_lt_trans := regex_proof_compare_lt_trans
  ; proof_compare_gt_trans := regex_proof_compare_gt_trans
  }.

Theorem compare_regex_is_compare: forall
  {A: Type}
  {cmp: comparable A}
  (r s: regex A),
  compare_regex r s = compare r s.
Proof.
simpl.
reflexivity.
Qed.

(* induction_on_compare_regex starts induction on a `compare_regex` expression in the goal.
   It makes sense to remember this comparison, so that it be rewritten to an
   equality in the Eq induction goal.
*)
Ltac induction_on_compare_regex :=
  rewrite compare_regex_is_compare;
  induction_on_compare.

(* test_compare_list simply tests whether nat can be used
   with a function that expects a comparable instance.
   compare_list is defined in comparable, 
   specifically for this use case.
*)
Require Import compare_nat.
Definition list_a : list (@regex nat _) := (empty :: fail :: nil).
Definition list_b : list (@regex nat _) := (empty:: (char 1) :: nil).
Definition test_compare_list : Prop :=
  comparable_list list_a list_b = Lt.
