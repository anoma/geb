import GebLean.LawvereGodelTReduces
import GebLean.Utilities.Tower

/-!
# Lemma 16: structural tower bound for `GodelTTerm`

Following Beckmann-Weiermann 2000 Definitions 7-10 and the
proof of Lemma 16 on pp. 480-484.  All measures are defined
parametrically over `S : Set GodelTBase` and apply uniformly
to the nucleus (`S = {.nat}`) and the binary-tree extension
(`S = {.nat, .tree}`).

`tower` from `Utilities/Tower.lean` matches Beckmann-Weiermann's
`2_m`: `tower 0 x = x`, `tower (k+1) x = 2 ^ tower k x`.
-/

namespace GebLean

/-- Term tree size, mirroring Beckmann-Weiermann's `lh(a)`.
Each constructor (variable or atomic constant) contributes 1;
`app` sums the sub-sizes plus 1. -/
def GodelTTerm.lh {S : Set GodelTBase} :
    {n : Nat} → {σ : GodelTType S} →
    GodelTTerm S n σ → Nat
  | _, _, .var _ _      => 1
  | _, _, .app f a      => f.lh + a.lh + 1
  | _, _, .zero _       => 1
  | _, _, .succ _       => 1
  | _, _, .pred _       => 1
  | _, _, .K _ _        => 1
  | _, _, .S_comb _ _ _ => 1
  | _, _, .disc _       => 1
  | _, _, .iter _       => 1
  | _, _, .leaf _       => 1
  | _, _, .node _       => 1
  | _, _, .treeIter _ _ => 1

/-- Iter-nesting depth, mirroring Beckmann-Weiermann's `d(a)`
from Definition 10.  The `iter` and `treeIter` constants
contribute 1 to the nesting depth; `app` takes the max of its
two children.  All other constructors contribute 0. -/
def GodelTTerm.d {S : Set GodelTBase} :
    {n : Nat} → {σ : GodelTType S} →
    GodelTTerm S n σ → Nat
  | _, _, .var _ _      => 0
  | _, _, .app f a      => max f.d a.d
  | _, _, .zero _       => 0
  | _, _, .succ _       => 0
  | _, _, .pred _       => 0
  | _, _, .K _ _        => 0
  | _, _, .S_comb _ _ _ => 0
  | _, _, .disc _       => 0
  | _, _, .iter _       => 1
  | _, _, .leaf _       => 0
  | _, _, .node _       => 0
  | _, _, .treeIter _ _ => 1

/-- Maximum type level among all sub-terms of a term.  At a
constant or variable of type `σ`, contributes `σ.level`; at
`app f a`, takes the max over `f.G` and `a.G`. -/
def GodelTTerm.G {S : Set GodelTBase} {n : Nat} {σ : GodelTType S}
    (t : GodelTTerm S n σ) : Nat :=
  match t with
  | .var _ _      => σ.level
  | .app f a      => max f.G a.G
  | .zero _       => σ.level
  | .succ _       => σ.level
  | .pred _       => σ.level
  | .K _ _        => σ.level
  | .S_comb _ _ _ => σ.level
  | .disc _       => σ.level
  | .iter _       => σ.level
  | .leaf _       => σ.level
  | .node _       => σ.level
  | .treeIter _ _ => σ.level

end GebLean
