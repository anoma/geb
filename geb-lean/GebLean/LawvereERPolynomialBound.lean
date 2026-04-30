import GebLean.LawvereER
import GebLean.LawvereERBoundComputable
import GebLean.Utilities.ComputationalComplexity

/-!
# ER polynomial bounds and structural towerHeight lemma

ER-side polynomial-value-bound infrastructure used in
the K^sim → ER forward translation's interp-preservation
theorem.

The principal results are:

- `ERMor1.PolyBound` — data-bearing structure carrying
  a polynomial degree `degree : ℕ` and a value-bound
  proof.
- `ERMor1.PolyBound.log_le_towerHeight` — structural
  lemma relating polynomial degree to the project's
  `ERMor1.towerHeight`.

References `ERMor1` but not `KMor1`.

See `docs/plans/2026-04-30-er-polynomial-bound-design.md`
(Module B) and
`docs/research/2026-04-30-ksim-polynomial-bound-references.md`
(Claim 7 / FOLKLORE 4).
-/

namespace GebLean

/-- Data-bearing polynomial-value-bound for an ER term.
The `degree` field is the polynomial degree; the
`bounds` field is the pointwise inequality. -/
structure ERMor1.PolyBound {n : ℕ} (f : ERMor1 n) where
  degree : ℕ
  bounds : ∀ ctx : Fin n → ℕ,
    f.interp ctx ≤
      ((Finset.univ : Finset (Fin n)).sup ctx + 1) ^ degree

end GebLean
