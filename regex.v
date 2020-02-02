Require Import List.

Section Regexes.

Variable X: Set.
Parameter is_eq : X -> X -> bool.
Parameter compare : X -> X -> comparison.
Parameter hash: X -> nat.
Parameter proof_compare_equal: forall (x y: X) (p: compare x y = Eq),
  x = y.
Parameter proof_compare_reflex: forall (x: X), compare x x = Eq. 
Parameter proof_is_eq_equal: forall (x y: X) (p: is_eq x y = true),
  x = y.
Parameter proof_is_eq_reflex: forall (x: X), is_eq x x = true.

Inductive regex :=
  nothing : regex
  | empty : regex
  | char : X -> regex
  | or : regex -> regex -> regex
  | concat : regex -> regex -> regex
  | zero_or_more : regex -> regex
  .

Fixpoint compare_regex (r s: regex) : comparison :=
  match r with
  | nothing => match s with
    | nothing => Eq
    | _ => Lt
    end
  | empty => match s with
    | nothing => Gt
    | empty => Eq
    | _ => Lt
    end
  | char x => match s with
    | nothing => Gt
    | empty => Gt
    | char y => compare x y
    | _ => Lt
    end
  | or r1 r2 => match s with
    | nothing => Gt
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
  | concat r1 r2 => match s with
    | nothing => Gt
    | empty => Gt
    | char _ => Gt
    | or _ _ => Gt
    | concat s1 s2 =>
      match compare_regex r1 s1 with
      | Lt => Lt
      | Eq => compare_regex r2 s2
      | Gt => Gt
      end
    | _ => Lt
    end
  | zero_or_more r1 => match s with
    | zero_or_more s1 => compare_regex r1 s1
    | _ => Lt
    end
  end.

Fixpoint nullable (r: regex) : bool :=
  match r with
  | nothing => false
  | empty => true
  | char _ => false
  | or s t => nullable s || nullable t
  | concat s t => nullable s && nullable t
  | zero_or_more _ => true
  end.

Fixpoint derive (r: regex) (x: X) : regex :=
  match r with
  | nothing => nothing
  | empty => nothing
  | char y => if is_eq x y
    then empty
    else nothing
  | or s t => or (derive s x) (derive t x)
  | concat s t =>
    if nullable s
    then or (concat (derive s x) t) (derive t x)
    else concat (derive s x) t
  | zero_or_more s => concat (derive s x) (zero_or_more s)
  end.

(*
ab(ab)*
concat a (concat b (zeroormore (concat a b)))
b(ab)*
concat empty (concat b ...)

(ab)*ab
concat (zeroormore (concat a b)) (concat a b)
or
  (concat (derive (zeroormore a b) a) (concat a b))
  (derive (concat a b) a)
  
or 
  (concat (concat (concat empty b) (zeroormore a b)) (concat a b))
  (concat empty b)

emptyb(ab)*ab | emptyb
nothingb(ab)*ab | (ab)*ab | nothingb | empty
nothingb(ab)*ab | 

empty(ab)*ab | empty
*)

Definition matches (r: regex) (xs: list X) : bool :=
  nullable (fold_left derive xs r)
.

Fixpoint simplify (r: regex) : regex :=
  match r with
  | nothing => nothing
  | empty => empty
  | char x => char x
  | or r1 r2 => match compare_regex r1 r2 with
    | Lt => or (simplify r1) (simplify r2)
    | Eq => simplify r1
    | Gt => or (simplify r2) (simplify r1)
    end
  | concat r1 r2 => concat r1 r2
  | zero_or_more r1 => zero_or_more r1
  end.

Definition sderive (r: regex) (x: X) : regex :=
  simplify (derive r x)
.

Definition smatches (r: regex) (xs: list X) : bool :=
  nullable (fold_left sderive xs r)
.

(* Theorem derive_eq_sderive : forall (r: regex) (x: X),
  derive r x = sderive r x.
Proof.
induction r; unfold sderive; simpl.
- reflexivity.
- reflexivity.
- intros.
*)

Theorem or_comm : forall (xs: list X) (r s: regex),
  matches (or r s) xs = matches (or s r) xs.
Proof.
unfold matches.
induction xs.
- simpl.
  firstorder.
- simpl.
  intros.
  apply IHxs.
Qed.

Theorem or_assoc : forall (xs: list X) (r s t: regex),
  matches (or r (or s t)) xs = matches (or (or r s) t) xs.
Proof.
unfold matches.
induction xs.
- simpl.
  intros.
  firstorder.
- intros.
  apply IHxs.
Qed.

Theorem compare_equal : forall (r1 r2: regex) (p: compare_regex r1 r2 = Eq),
  r1 = r2.
Proof.
induction r1.
 - induction r2; simpl; trivial; discriminate. (* nothing *)
 - induction r2; simpl; trivial; discriminate. (* empty *) 
 - induction r2; simpl; try discriminate. (* char *)
  + remember (compare x x0).
    induction c; simpl; try discriminate.
    * symmetry in Heqc.
      apply proof_compare_equal in Heqc.
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
 - induction r2; simpl; try discriminate. (* zero_or_more *)
  + remember (IHr1 r2).
    remember (IHr1 (zero_or_more r2)).
    intros.
    remember (e p).
    rewrite e1.
    reflexivity.
Qed.

Theorem compare_reflex : forall (r: regex), 
 compare_regex r r = Eq.
Proof.
induction r; try reflexivity; simpl.
- apply proof_compare_reflex.
- rewrite IHr1. rewrite IHr2. reflexivity.
- rewrite IHr1. rewrite IHr2. reflexivity.
- rewrite IHr. reflexivity.
Qed.

Theorem or_idemp : forall (xs: list X) (r1 r2: regex) (p: compare_regex r1 r2 = Eq),
  matches (or r1 r2) xs = matches r1 xs.
Proof.
unfold matches.
induction xs.
- simpl.
  intros.
  rewrite (compare_equal r1 r2 p).
  induction (nullable r2); compute; reflexivity.
- simpl.
  intros.
  rewrite (compare_equal r1 r2 p).
  apply IHxs.
  apply compare_reflex.
Qed.

Theorem or_id : forall (xs: list X) (r: regex),
  matches (or r nothing) xs = matches r xs.
Proof.
unfold matches.
induction xs.
- simpl.
  firstorder.
- intros.
  simpl.
  apply IHxs.
Qed.

Theorem concat_nothing : forall (xs: list X) (r: regex),
  matches (concat nothing r) xs = matches nothing xs.
Proof.
unfold matches.
induction xs.
- simpl.
  reflexivity.
- simpl.
  exact IHxs.
Qed.

Theorem nothing_zero_or_more : forall (xs: list X),
  matches (zero_or_more nothing) xs = matches empty xs.
Proof.
unfold matches.
induction xs.
- simpl.
  reflexivity.
- simpl.
  apply concat_nothing.
Qed.

Theorem simplify_is_correct : forall (xs: list X) (r: regex),
  matches r xs = smatches r xs.
Proof.
unfold matches.
unfold smatches.
induction xs.
- simpl.
  reflexivity.
- simpl.
  induction r; unfold sderive at 2; simpl.
  * apply IHxs.
  * apply IHxs.
  * induction (is_eq a x).
    + unfold simplify.
      apply IHxs.
    + unfold simplify.
      apply IHxs.
  * remember (compare_regex (derive r1 a) (derive r2 a)).
    induction c.
    + symmetry in Heqc.
      remember or_idemp.
      remember (e xs (derive r1 a) (derive r2 a)).
      remember (e0 Heqc).
      unfold matches in e1.
      rewrite e1.
      apply IHr1.
    + assert (derive (or r1 r2) a = (or (derive r1 a) (derive r2 a))).
      simpl.
      reflexivity.
      assert (sderive (or r1 r2) a = (or (simplify (derive r1 a)) (simplify (derive r2 a)))).
      unfold sderive.
      rewrite H.
      simpl.
      rewrite <- Heqc.
      reflexivity.
      rewrite <- H.
      rewrite <- H0.
      assert (forall f, fold_left f xs (f (or r1 r2) a) = fold_left f (a::xs) (or r1 r2)).
      simpl.
      reflexivity.
      rewrite (H1 sderive).
      rewrite (H1 derive).
      rewrite <- (IHxs (or r1 r2)).
       fold fold_left.
      rewrite IHxs.
      unfold simplify.
      simpl.
      unfold derive.
      cbn.
      simpl.
      
      
      
      
      
    

(*Using only or_comm, or_assoc and or_idemp 
  Brzozowski proved that a notion of RE similarity including only
  r + r \u2248 r
  r + s \u2248 s + r
  (r + s) + t \u2248 r + (s + t)
  is enough to ensure that every RE has only a finite number of dissimilar derivatives. 
  Hence, DFA construction is guaranteed to terminate if we use similarity as an approximation for equivalence
  see https://www.ccs.neu.edu/home/turon/re-deriv.pdf
  Regular-expression derivatives reexamined - Scott Owens, John Reppy, Aaron Turon
*)
End Regexes.


