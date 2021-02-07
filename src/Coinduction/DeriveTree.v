Require Import Brzozowski.Alphabet.
Require Import Brzozowski.Derive.
Require Import Brzozowski.Language.
Require Import Brzozowski.Regex.

CoInductive DeriveTree: Type :=
  | mk_derive: lang -> (alphabet -> DeriveTree) -> DeriveTree.

CoFixpoint build_regex_tree (r: regex): DeriveTree :=
  mk_derive {{r}} (fun a => (build_regex_tree (derive_def r a))).

CoFixpoint build_lang_tree (l: lang): DeriveTree :=
  mk_derive l (fun a => (build_lang_tree (derive_lang a l))).