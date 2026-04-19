import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Nat.Factorial.Basic
import GebLean.Utilities.SzudzikSeq

/-!
# Nat-Level ER-Style Bounded Recursion Helpers

Mirror the witness-search semantics of `ERMor1.foldBTLOnCode`
and `ERMor1.boundedRec` at the Nat level.  Used by the bounded
NatBT theory's interp clauses to make `LawvereERCat ≃
LawvereNatBTBounded` on-the-nose at the raw constructor level.

Each helper produces the same output on every input as the
corresponding ER combinator's interp.  Soundness theorems
linking each helper to the ER combinator are proven in
`GebLean/Utilities/NatERStyleSoundness.lean` (a separate file
introduced in Task 1.2).
-/

namespace Nat

/-- Search range for the β-witness, mirroring
`ERMor1.boundedRecRange`.  Given the bound's value at the
target position and the target index, returns the upper limit
of the witness search. -/
def boundedRecRangeAt (boundCode : ℕ) (code : ℕ) : ℕ :=
  ((code + boundCode + 3).factorial)
    ^ ((code + boundCode + 3).factorial) + 1

/-- Bounded search: returns the least `j < range` with
`pred j = true`, or `range + 1` if no such `j`.  Mirrors
`ERMor1.boundedSearch`'s interp at the Nat level. -/
def boundedSearchAt (range : ℕ) (pred : ℕ → Bool) : ℕ :=
  if h : ∃ j, j < range ∧ pred j = true then
    Nat.find h
  else
    range + 1

/-- Per-position β-witness predicate for the course-of-values
fold on a `BTL` Gödel code.  Returns `true` iff the candidate
`cand`'s β-extraction at index `j` matches the leaf/step
recurrence (leaf for even `j`, step for odd `j`).  Mirrors
`ERMor1.foldBTLPred`'s interp at index `j`. -/
def foldBTLPredAtIndex
    (baseLeaf : ℕ → ℕ) (stepNode : ℕ → ℕ → ℕ)
    (cand : ℕ) (j : ℕ) : Bool :=
  let a := cand.unpair.1
  let b := cand.unpair.2
  let betaJ := a % (1 + (j + 1) * b)
  if j % 2 = 1 then
    let k := j / 2
    let l := k.unpair.1
    let r := k.unpair.2
    decide (betaJ = stepNode
      (a % (1 + (l + 1) * b))
      (a % (1 + (r + 1) * b)))
  else
    decide (betaJ = baseLeaf (j / 2))

/-- ER-style course-of-values fold on a `BTL` Gödel code.
Mirrors `ERMor1.foldBTLOnCode`'s interp on the nose: returns
the trace value when the supplied `bound` is pointwise
adequate and counter-monotonic, witness-search-fallback value
otherwise.  The `bound` parameter has type `ℕ → ℕ` and
represents the bound's value as a function of the index slot. -/
def foldBTLOnCodeERStyle
    (baseLeaf : ℕ → ℕ) (stepNode : ℕ → ℕ → ℕ)
    (bound : ℕ → ℕ) (code : ℕ) : ℕ :=
  let B := bound code
  let range := boundedRecRangeAt B code
  let cand := boundedSearchAt range
    (fun c =>
      decide (∀ j, j < code + 1 →
        foldBTLPredAtIndex baseLeaf stepNode c j = true))
  let betaCode :=
    cand.unpair.1 % (1 + (code + 1) * cand.unpair.2)
  Nat.min betaCode B

/-- Per-position β-witness predicate for primitive recursion.
For `j = 0`, the β-extract should equal `base`; for `j ≥ 1`,
the β-extract at `j` should equal `step (j-1) β(j-1)`.
Mirrors `ERMor1.boundedRecPred`'s interp at index `j`. -/
def boundedRecPredAtIndex
    (base : ℕ) (step : ℕ → ℕ → ℕ)
    (cand : ℕ) (j : ℕ) : Bool :=
  let a := cand.unpair.1
  let b := cand.unpair.2
  let betaJ := a % (1 + (j + 1) * b)
  if j = 0 then
    decide (betaJ = base)
  else
    let prev := a % (1 + j * b)
    decide (betaJ = step (j - 1) prev)

/-- ER-style bounded primitive recursion at the Nat level.
Mirrors `ERMor1.boundedRec`'s interp on the nose. -/
def boundedRecERStyle
    (base : ℕ) (step : ℕ → ℕ → ℕ)
    (bound : ℕ → ℕ) (n : ℕ) : ℕ :=
  let B := bound n
  let range := boundedRecRangeAt B n
  let cand := boundedSearchAt range
    (fun c =>
      decide (∀ j, j ≤ n →
        boundedRecPredAtIndex base step c j = true))
  let betaN :=
    cand.unpair.1 % (1 + (n + 1) * cand.unpair.2)
  Nat.min betaN B

end Nat
