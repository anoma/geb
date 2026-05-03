import GebLean.LawvereER
import GebLean.Utilities.ERArith
import GebLean.LawvereERBoundComputable
import GebLean.LawvereERPolynomialBound
import GebLean.Utilities.Tower

/-!
# Tourlakis A_n^r majorant family in ER

Lean-side realization of Tourlakis 2018 page 22 (proof of
§0.1.0.44 ⊆ direction) majorant family for K^sim level 2:

- `ERMor1.A_one : ERMor1 1` (interp `λx. 2x + 2`).
- `ERMor1.A_one_iter : ℕ → ERMor1 1`
  (interp `λx. 2^r * x + (2^{r+1} - 2)`).
- `ERMor1.A_two_iter : ℕ → ERMor1 1` (alias of
  `ERMor1.towerER`, interp `λx. tower r x`).

`A_one` and `A_one_iter` carry `PolyBound` builders
(linear in the input).  `A_two_iter` does not: `tower r x`
for `r ≥ 1` is not polynomially bounded in `x`, and
`ERMor1.PolyBound` is the bprod-free polynomial fragment
per `LawvereERPolynomialBound.lean`'s structural-towerHeight
section.  Downstream consumers (step 4 majorization,
step 5 `kToER` simrec at level 2) reason about
`A_two_iter`'s growth via `interp_A_two_iter` plus
`Utilities/Tower.lean`'s monotonicity lemmas (`tower_mono_right`,
`tower_mono_left`, `self_le_tower`,
`mul_tower_le_tower_add_two`,
`tower_pow_le_tower_add_three`), and feed the resulting
Nat-level dominance hypothesis into
`simultaneousBoundedRec_interp_correct` directly — no
`PolyBound` builder is invoked at level 2.

See
`docs/superpowers/specs/2026-05-03-step-3-er-tourlakis-A-majorants-design.md`
and master design §3.3 in
`docs/research/2026-05-02-er-ksim2-equiv-via-urm-master-design.md`.
Cross-reference network:
`docs/research/2026-04-30-ksim-polynomial-bound-references.md`
for the polynomial-bound infrastructure context.
-/

namespace GebLean

namespace ERMor1

end ERMor1

end GebLean
