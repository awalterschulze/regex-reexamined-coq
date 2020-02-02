Require Import List.

Section Regexes.

(* A character for a regular expression is generic,
   but it needs to implement an interface.
   It needs to be comparable.
*)

Variable X: Set.
Parameter compare : X -> X -> comparison.
Parameter proof_compare_equal: forall (x y: X) (p: compare x y = Eq),
  x = y.
Parameter proof_compare_reflex: forall (x: X), compare x x = Eq. 

Definition is_eq (x y: X) : bool :=
  match compare x y with
  | Eq => true
  | _ => false
  end.

Inductive regex :=
  nothing : regex (* matches no strings *)
  | empty : regex (* matches the empty string *)
  | char : X -> regex (* matches a single character *)
  | or : regex -> regex -> regex
  | and : regex -> regex -> regex
  | concat : regex -> regex -> regex
  | not : regex -> regex
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
  | and r1 r2 => match s with
    | nothing => Gt
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
    | nothing => Gt
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
    | nothing => Gt
    | empty => Gt
    | char _ => Gt
    | or _ _ => Gt
    | and _ _ => Gt
    | concat _ _ => Gt
    | not s1 => compare_regex r1 s1
    | _ => Lt
    end
  | zero_or_more r1 => match s with
    | zero_or_more s1 => compare_regex r1 s1
    | _ => Gt
    end
  end.

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
- rewrite IHr1. rewrite IHr2. reflexivity.
- rewrite IHr. reflexivity.
- rewrite IHr. reflexivity.
Qed.

(* nullable returns whether the regular expression matches the
   empty string, for example:
   nullable (ab)*        = true
   nullable a(ab)*       = false
   nullable a            = false
   nullable (abc)*|ab    = true
   nullable a(abc)*|ab   = false
*)
Fixpoint nullable (r: regex) : bool :=
  match r with
  | nothing => false
  | empty => true
  | char _ => false
  | or s t => nullable s || nullable t
  | and s t => nullable s && nullable t
  | concat s t => nullable s && nullable t
  | not s => negb (nullable s)
  | zero_or_more _ => true
  end.

(* derive returns the regular expression that is left to match
   after matching the input character x, for example:
   derive (ba)* b = a(ba)*
   derive a     a = empty
   derive b     a = nothing
   derive ab|a  a = b|empty
*)
Fixpoint derive (r: regex) (x: X) : regex :=
  match r with
  | nothing => nothing
  | empty => nothing
  | char y => if is_eq x y
    then empty
    else nothing
  | or s t => or (derive s x) (derive t x)
  | and s t => and (derive s x) (derive t x)
  | concat s t =>
    if nullable s
    then or (concat (derive s x) t) (derive t x)
    else concat (derive s x) t
  | not s => not (derive s x)
  | zero_or_more s => concat (derive s x) (zero_or_more s)
  end.

Definition matches (r: regex) (xs: list X) : bool :=
  nullable (fold_left derive xs r)
.

(* sderive is the same as derive, except that it applies
   simplification rules by construction.
   This way we don't have to apply simplification after derivation.
   We hope this will also make it easier to prove things.
*)
Fixpoint sderive (r: regex) (x: X) : regex :=
  match r with
  | nothing => nothing
  | empty => nothing
  | char y => if is_eq x y
    then empty
    else nothing
  | or s t => 
    let ds := derive s x in
    let dt := derive t x in
    match compare_regex ds dt with
    | Eq => ds
    | Lt => or ds dt
    | Gt => or dt ds
    end
  | and s t => and (derive s x) (derive t x)
  | concat s t =>
    if nullable s
    then or (concat (derive s x) t) (derive t x)
    else concat (derive s x) t
  | not s => not (derive s x)
  | zero_or_more s => concat (derive s x) (zero_or_more s)
  end.

Definition smatches (r: regex) (xs: list X) : bool :=
  nullable (fold_left sderive xs r)
.

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

(* r|s = s|r *)
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

(* (r|s)|t = r|(s|t) *)
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

(* r|r = r *)
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

(* nothing|r = r *)
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

(* nothing.r = r *)
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

(* (nothing)* = empty *)
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

(* mathing without simplification is the same as with simplification *)
Theorem simplify_is_correct : forall (xs: list X) (r: regex),
  matches r xs = smatches r xs.
Proof.
unfold matches.
unfold smatches.
induction xs.
- simpl.
  reflexivity.
- simpl.
  induction r; simpl; try (apply IHxs).
  * remember (compare_regex (derive r1 a) (derive r2 a)).
    induction c.
    + symmetry in Heqc.
      remember or_idemp.
      remember (e xs (derive r1 a) (derive r2 a)).
      remember (e0 Heqc).
      unfold matches in e1.
      rewrite e1.
      apply IHxs.
    + apply IHxs.
    + remember or_comm.
      unfold matches in e.
      rewrite e.
      apply IHxs.
Qed.

End Regexes.


