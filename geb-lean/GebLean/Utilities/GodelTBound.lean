import GebLean.LawvereGodelTQuot
import Mathlib.Algebra.BigOperators.Fin

/-!
# Structural Measures on `GodelTMor1`

Two structural measures on `GodelTMor1` terms paralleling the
nesting and length measures used in Beckmann-Weiermann's
analysis of T*: `nestDepth`, the maximum depth of nested
iteration constructors, and `termSize`, the tree-size
counting one per primitive and summing across composites.
-/

namespace GebLean

/-- Iteration-nesting degree of a `GodelTMor1` term, mirroring
B-W's `d(a)`.  Atomic primitives have degree `0`; iteration
constructors increment the degree of their argument; `comp`
takes the maximum over its head and the family of
sub-arguments. -/
def GodelTMor1.nestDepth : {n : ℕ} → GodelTMor1 n → ℕ
  | _, .zero => 0
  | _, .succ => 0
  | _, .pred => 0
  | _, .proj _ => 0
  | _, .sub => 0
  | _, .disc => 0
  | _, .bsum f => f.nestDepth + 1
  | _, .bprod f => f.nestDepth + 1
  | _, .comp f g =>
      max f.nestDepth
        (Finset.univ.sup (fun i => (g i).nestDepth))

/-- Tree-size of a `GodelTMor1` term, mirroring B-W's `lh(a)`.
Atomic primitives contribute `1`; iteration constructors add
`1` to the size of their argument; `comp` sums the head size
and the family-of-arguments size, plus `1`. -/
def GodelTMor1.termSize : {n : ℕ} → GodelTMor1 n → ℕ
  | _, .zero => 1
  | _, .succ => 1
  | _, .pred => 1
  | _, .proj _ => 1
  | _, .sub => 1
  | _, .disc => 1
  | _, .bsum f => f.termSize + 1
  | _, .bprod f => f.termSize + 1
  | _, .comp f g =>
      f.termSize +
        (Finset.univ.sum (fun i => (g i).termSize)) + 1

end GebLean
