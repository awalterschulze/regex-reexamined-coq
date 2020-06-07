Require Import Brzozowski.Alphabet.

Inductive regex :=
  (* emptyset matches absolutely no strings *)
  | emptyset : regex
  (* lambda matches only the empty string *)
  | lambda : regex
  (* symbol matches only strings of length 1 containing the exact alphabet symbol *)
  | symbol : alphabet -> regex
  (* concat is used to build of regular expressions that can match longer strings *)
  | concat : regex -> regex -> regex
  (* zero or more, as you are familiar with from regular expressions *)
  | star : regex -> regex
  (* `nor` is a boolean operator, here is the truth table
     P | Q | P `nor` Q
     -----------------
     T | T | F
     T | F | F
     F | T | F
     F | F | T
  *)
  | nor : regex -> regex -> regex
  .

(* We chose to include `nor`, since it can represent any possible boolean expression,
   which is one of the selling points of Brzozowski's derivatives for regular expressions.
*)

Definition complement (r: regex) : regex :=
  nor r r.

Definition and (r s: regex) : regex :=
  nor (nor r r) (nor s s).

Definition or (r s: regex) : regex :=
  nor (nor r s) (nor r s).

Definition xor (r s: regex) : regex :=
  or (and r (complement s)) (and (complement r) s).

(* I matches all strings *)
Definition I: regex :=
    complement (emptyset).