Require Import List.
Require Import Program.Basics.

Section Tregexes.

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

Inductive tree :=
  tree_node : X -> list tree -> tree.

(* 
[a[a[]b[]] b[]]

concat (node a (node a empty)) (node b empty)
*)

Inductive tregex :=
  nothing : tregex
  | empty : tregex
  | node : X -> tregex -> tregex
  | or : tregex -> tregex -> tregex
  | concat : tregex -> tregex -> tregex
  | zero_or_more : tregex -> tregex
  .

Fixpoint nullable (r: tregex) : bool :=
  match r with
  | nothing => false
  | empty => true
  | node _ _ => false
  | or s t => nullable s || nullable t
  | concat s t => nullable s && nullable t
  | zero_or_more _ => true
  end.

Fixpoint derive (r: tregex) : (tree -> tregex) :=
  match r with
  | nothing => fun _ => nothing
  | empty => fun _ => nothing
  | node y yr => fix derive1 (tx: tree) := match tx with
    | tree_node x xs => if is_eq x y && nullable (fold_left derive xs yr)
      then empty
      else nothing
    end
  | or s t => fun tx => or (derive s tx) (derive t tx)
  | concat s t => fun tx =>
    if nullable s
    then or (concat (derive s tx) t) (derive t tx)
    else concat (derive s tx) t
  | zero_or_more s => fun tx => concat (derive s tx) (zero_or_more s)
  end.




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

