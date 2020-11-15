(*
TODO: Good First Issue
Proving these equivalences will be good first issues in future.
First the definition of regular expressions in this folder, need to be revisited.

Simplification rules from re-examined

r&r = r
r&s = s&r
(r&s)&t = r&(s&t)
∅&r = ∅
~∅&r = ~@

r+r = r
r+s = s+r
(r+s)+t = r+(s+t)
~∅+r = ~∅
∅+r = r

(r,s),t = r,(s,t)
∅,r = ∅
r,∅ = ∅
ε,r = r
r,ε = r

r** = r*
ε* = ε
∅* = ε
~~r = r
*)