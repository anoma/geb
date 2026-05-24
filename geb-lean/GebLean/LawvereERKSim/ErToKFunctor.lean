import GebLean.LawvereERKSim.ErToK
import GebLean.LawvereERQuot
import GebLean.LawvereKSimQuot

/-!
# `ErToKFunctor` — multi-output ER-to-K^sim translator and functor

This module lifts the single-output translator `erToK` (from
`ErToK.lean`) to the multi-output level (`erToKN`) and then to
the quotient category level, producing the functor
`erToKFunctor : LawvereERCat ⥤ LawvereKSimDCat 2` realising the
⊇ direction of Tourlakis 2018 Corollary 0.1.0.44 at `n = 2`.

## Main definitions

- `erToKN` : multi-output ER-to-K^sim translator.
- `erToKFunctor_map` : morphism component of the forward
  functor `LawvereERCat ⥤ LawvereKSimDCat 2`, lifting
  `ERMorNQuo n m` to `KSimMor 2 n m`.

## Main statements

- `erToKN_interp` : interp-faithfulness per output slot.
- `erToKN_level` : level ≤ 2 per output slot.
- `erToKN_compat_extEq` : extensionally-equal ER families
  produce extensionally-equal K^sim families.

## References

- Tourlakis 2018, *Topics in PR Complexity*, §0.1.0.44.
- Spec: `docs/superpowers/specs/2026-05-22-step-t4-runtime-bound-design.md`.
- Mirror: `kToERN` and `kToERFunctor` in `GebLean/LawvereKSimER.lean`.

## Tags

ertok, functor, simulator, quotient
-/

namespace GebLean

/-- Multi-output ER-to-K^sim translator: apply the single-output
translator `erToK` slotwise to an `ERMorN n m` family. The level
bound is uniform-by-construction (each slot is level ≤ 2 by
`erToK_level`), so no level hypothesis is required as input. -/
def erToKN {n m : ℕ} (e : ERMorN n m) : KMorN n m :=
  fun j => erToK (e j)

-- AXIOM_ALLOW: Classical.choice (transitively via `erToK_interp`;
-- see .claude/rules/lean-coding.md § Accepted exceptions).
/-- Componentwise correctness of `erToKN`: each component of the
erToKN-translated family agrees with the corresponding ER
component on every context. -/
theorem erToKN_interp {n m : ℕ} (e : ERMorN n m)
    (v : Fin n → ℕ) (j : Fin m) :
    (erToKN e j).interp v = (e j).interp v :=
  erToK_interp (e j) v

-- AXIOM_ALLOW: Classical.choice (transitively via `erToK_level`;
-- see .claude/rules/lean-coding.md § Accepted exceptions).
/-- Per-slot level bound for `erToKN`: every output component of
the translated family has structural level at most 2. -/
theorem erToKN_level {n m : ℕ} (e : ERMorN n m)
    (j : Fin m) : (erToKN e j).level ≤ 2 :=
  erToK_level (e j)

-- AXIOM_ALLOW: Classical.choice (transitively via `erToK_interp`;
-- see .claude/rules/lean-coding.md § Accepted exceptions).
/-- Compatibility of `erToKN` with ER ext-eq: extensionally-equal
ER families produce extensionally-equal K^sim families. Used by
`erToKFunctor.map` to discharge the `Quotient.lift`
well-definedness obligation. -/
theorem erToKN_compat_extEq {n m : ℕ}
    {e₁ e₂ : ERMorN n m}
    (he : ∀ v j, (e₁ j).interp v = (e₂ j).interp v) :
    ∀ v j, (erToKN e₁ j).interp v
            = (erToKN e₂ j).interp v := by
  intro v j
  rw [erToKN_interp, erToKN_interp]
  exact he v j

-- AXIOM_ALLOW: Classical.choice (transitively via
-- `erToKN_compat_extEq`; see .claude/rules/lean-coding.md
-- § Accepted exceptions).
/-- Morphism component of the forward functor.  Lifts an
`ERMorNQuo n m` (an equivalence class of `ERMorN n m`
families under ext-equality) to a `KSimMor 2 n m` whose
`hom` is the class of `erToKN`-translated family and whose
`depth_witness` is the canonical level-≤-2 raw witness
furnished by `erToKN_level`.  Well-definedness of the lift
reduces (via `KSimMor.ext`) to extensional equality of
`erToKN` images, discharged by `erToKN_compat_extEq`. -/
def erToKFunctor_map {n m : ℕ}
    (e : ERMorNQuo n m) : KSimMor 2 n m :=
  Quotient.liftOn e
    (fun rec =>
      { hom := Quotient.mk (kMorNSetoid n m) (erToKN rec),
        depth_witness := Quotient.mk _
          { rep := erToKN rec,
            rep_level := fun i => erToKN_level rec i,
            rep_eq := rfl } })
    (fun e₁ e₂ h => by
      apply KSimMor.ext
      apply Quotient.sound
      intro v
      funext j
      exact erToKN_compat_extEq
        (fun v' j' => congr_fun (h v') j') v j)

end GebLean
