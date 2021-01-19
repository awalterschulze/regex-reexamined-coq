Require Import Brzozowski.Alphabet.

Inductive regex :=
  (* emptyset matches absolutely no strings *)
  | emptyset : regex
  (* lambda matches only the empty string *)
  | lambda : regex
  (* symbol matches only strings of length 1 containing the exact alphabet symbol *)
  | symbol : alphabet -> regex
  (* or takes the union of two regular expressions *)
  | or : regex -> regex -> regex
  (* 
    neg or negation is the `not` or `complement` operator, that we use to avoid confusion with
    the `not` function for properties.s
    Using the two logical operators `or` and `neg` we can represent all other logical operators 
  *)
  | neg : regex -> regex
  (* concat is used to build of regular expressions that can match longer strings *)
  | concat : regex -> regex -> regex
  (* zero or more, as you are familiar with from regular expressions *)
  | star : regex -> regex
  .
