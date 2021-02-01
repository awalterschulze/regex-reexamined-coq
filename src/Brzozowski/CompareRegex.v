Require Import Brzozowski.Alphabet.
Require Import Brzozowski.Regex.

Fixpoint compare_regex (p q: regex) : comparison :=
  match p with
  | emptyset => match q with
    | emptyset => Eq
    | _ => Lt
    end
  | emptystr => match q with
    | emptyset => Gt
    | emptystr => Eq
    | _ => Lt
    end
  | symbol x => match q with
    | emptyset => Gt
    | emptystr => Gt
    | symbol y => compare_alphabet x y
    | _ => Lt
    end
  | or p1 p2 => match q with
    | emptyset => Gt
    | emptystr => Gt
    | symbol _ => Gt
    | or q1 q2 =>
      match compare_regex p1 q1 with
      | Lt => Lt
      | Eq => compare_regex p2 q2
      | Gt => Gt
      end
    | _ => Lt
    end
  | neg p1 => match q with
    | emptyset => Gt
    | emptystr => Gt
    | symbol _ => Gt
    | or _ _ => Gt
    | neg q1 => compare_regex p1 q1
    | _ => Lt
    end
  | concat p1 p2 => match q with
    | emptyset => Gt
    | emptystr => Gt
    | symbol _ => Gt
    | or _ _ => Gt
    | neg _ => Gt
    | concat q1 q2 =>
      match compare_regex p1 q1 with
      | Lt => Lt
      | Eq => compare_regex p2 q2
      | Gt => Gt
      end
    | _ => Lt
    end
  | star p1 => match q with
    | star q1 => compare_regex p1 q1
    | _ => Gt
    end
  end.