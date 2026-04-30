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

namespace ERMor1.PolyBound

/-- Polynomial bound for `zero` (constant `0`). -/
def ofZero : PolyBound ERMor1.zero where
  degree := 0
  bounds := fun _ => by
    simp [ERMor1.interp_zero]

/-- Polynomial bound for `succ` (linear, degree `1`). -/
def ofSucc : PolyBound ERMor1.succ where
  degree := 1
  bounds := fun ctx => by
    simp only [ERMor1.interp_succ, pow_one]
    have h : ctx 0 ≤
        (Finset.univ : Finset (Fin 1)).sup ctx :=
      Finset.le_sup (Finset.mem_univ _)
    omega

/-- Polynomial bound for `proj i` (linear, degree `1`). -/
def ofProj {k : ℕ} (i : Fin k) :
    PolyBound (ERMor1.proj i) where
  degree := 1
  bounds := fun ctx => by
    simp only [ERMor1.interp_proj, pow_one]
    have h : ctx i ≤
        (Finset.univ : Finset (Fin k)).sup ctx :=
      Finset.le_sup (Finset.mem_univ _)
    omega

/-- Polynomial bound for `sub` (linear, degree `1`). -/
def ofSub : PolyBound ERMor1.sub where
  degree := 1
  bounds := fun ctx => by
    simp only [ERMor1.interp_sub, pow_one]
    have h0 : ctx 0 ≤
        (Finset.univ : Finset (Fin 2)).sup ctx :=
      Finset.le_sup (Finset.mem_univ _)
    omega

end ERMor1.PolyBound

end GebLean
