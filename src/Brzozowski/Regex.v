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
