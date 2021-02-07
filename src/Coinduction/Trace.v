Require Import CoqStock.Invs.
Require Import CoqStock.List.

Require Import Brzozowski.Alphabet.
Require Import Brzozowski.Derive.
Require Import Brzozowski.DeriveCommutes.
Require Import Brzozowski.Language.
Require Import Brzozowski.Null.
Require Import Brzozowski.NullCommutes.
Require Import Brzozowski.Regex.

CoInductive Trace: regex -> lang :=
| empty_trace : forall q:regex, null_def q = emptystr -> Trace q []
| cons_trace :
    forall (q q':regex) (a:alphabet) (s:str),
        derive_def q a = q' -> Trace q' s -> Trace q (a :: s).

Theorem trace_is_equivalent:
  forall (p: regex),
    {{p}} {<->} Trace p.
Proof.
intros.
split; intros.
- generalize dependent p.
  generalize dependent s.
  cofix G.
  intros.
  unfold "\in".
  (* `induction s` would break Guarded *)
  destruct s.
  + constructor.
    rewrite null_iff_null_def.
    constructor.
    assumption.
    Guarded.
  + apply (cons_trace p (derive_def p a) a).
    * reflexivity.
    * specialize G with (s := s) (p := (derive_def p a)).
      apply G.
      rewrite <- derive_commutes_a.
      assumption.
      Guarded.
- generalize dependent p.
  induction s.
  + intros.
    inversion H.
    rewrite null_iff_null_def in H0.
    invs H0.
    assumption.
  + intros.
    specialize IHs with (p := (derive_def p a)).
    replace ((a :: s) \in {{p}}) with (s \in (derive_lang a {{p}})).
    * rewrite derive_commutes_a.
      apply IHs.
      invs H.
      assumption.
    * unfold derive_lang.
      unfold "\in".
      reflexivity.
Qed.
