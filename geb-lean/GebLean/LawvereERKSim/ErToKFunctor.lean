import GebLean.LawvereERKSim.ErToK
import GebLean.LawvereERQuot
import GebLean.LawvereKSimQuot
import GebLean.LawvereERInterp
import GebLean.LawvereKSimDCatInterp

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
- `erToKFunctor` : the forward functor
  `LawvereERCat ⥤ LawvereKSimDCat 2` assembled from
  `erToKFunctor_map`, `erToKFunctor_map_id`, and
  `erToKFunctor_map_comp`.

## Main statements

- `erToKN_interp` : interp-faithfulness per output slot.
- `erToKN_level` : level ≤ 2 per output slot.
- `erToKN_compat_extEq` : extensionally-equal ER families
  produce extensionally-equal K^sim families.
- `erToKFunctor_map_id` : `erToKFunctor_map` preserves identities.
- `erToKFunctor_map_comp` : `erToKFunctor_map` preserves
  composition.

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

-- AXIOM_ALLOW: Classical.choice (transitively via `erToK_interp`;
-- see .claude/rules/lean-coding.md § Accepted exceptions).
/-- Functor law: `erToKFunctor_map` preserves identities.
The `𝟙 n` morphism in `LawvereERCat` has representative
`ERMorN.id n`; its erToKN-translation componentwise equals
`KMorN.id n` (since `erToK (ERMor1.proj i) = KMor1.proj i`
modulo `interp`). -/
theorem erToKFunctor_map_id (n : LawvereERCat) :
    erToKFunctor_map
        (CategoryTheory.CategoryStruct.id
          (obj := LawvereERCat) n)
      = CategoryTheory.CategoryStruct.id
          (obj := LawvereKSimDCat 2)
          (n : LawvereKSimDCat 2) := by
  apply KSimMor.ext
  apply Quotient.sound
  intro v
  funext i
  change (erToKN (ERMorN.id n) i).interp v
      = (KMorN.id n i).interp v
  rw [erToKN_interp]
  rfl

-- AXIOM_ALLOW: Classical.choice (transitively via `erToK_interp`;
-- see .claude/rules/lean-coding.md § Accepted exceptions).
/-- Functor law: `erToKFunctor_map` preserves composition.
On raw representatives, `ERMorN.comp e f` slotwise equals
`ERMor1.comp (f j) e`; `erToK` is interp-faithful, and
`KMor1.comp` on the K^sim side composes the translated
heads with the translated tail componentwise. -/
theorem erToKFunctor_map_comp {n m k : ℕ}
    (e : ERMorNQuo n m) (f : ERMorNQuo m k) :
    erToKFunctor_map
        (CategoryTheory.CategoryStruct.comp
          (obj := LawvereERCat) e f)
      = CategoryTheory.CategoryStruct.comp
          (obj := LawvereKSimDCat 2)
          (erToKFunctor_map e) (erToKFunctor_map f) := by
  apply KSimMor.ext
  refine Quotient.inductionOn₂
    (motive := fun (e : ERMorNQuo n m) (f : ERMorNQuo m k) =>
      (erToKFunctor_map
          (CategoryTheory.CategoryStruct.comp
            (obj := LawvereERCat) e f)).hom
        = (CategoryTheory.CategoryStruct.comp
            (obj := LawvereKSimDCat 2)
            (erToKFunctor_map e) (erToKFunctor_map f)).hom)
    e f ?_
  intro er fr
  apply Quotient.sound
  intro v
  funext j
  change (erToKN (ERMorN.comp er fr) j).interp v
      = (KMorN.comp (erToKN fr) (erToKN er) j).interp v
  rw [erToKN_interp]
  simp only [ERMorN.comp, KMorN.comp,
    ERMor1.interp_comp, KMor1.interp_comp]
  rw [← erToK_interp (fr j)]
  congr 1
  funext i
  exact (erToKN_interp er v i).symm

/-- The forward functor of the categorical equivalence
`LawvereERCat ≌ LawvereKSimDCat 2` — reverse of `kToERFunctor`.
Master design §3.5; ⊇ direction of Tourlakis 2018 Cor.
0.1.0.44 at `n = 2`. -/
def erToKFunctor : CategoryTheory.Functor
    LawvereERCat (LawvereKSimDCat 2) where
  obj n     := n
  map       := erToKFunctor_map
  map_id    := erToKFunctor_map_id
  map_comp  := erToKFunctor_map_comp

-- AXIOM_ALLOW: Classical.choice (transitively via
-- `erToKN_interp` → `erToK_interp`; see
-- .claude/rules/lean-coding.md § Accepted exceptions).
/-- Morphism-level interpretation preservation: the
K^sim-quotient interpretation of `erToKFunctor_map e` agrees
with the ER-quotient interpretation of `e`.  Mirror:
`kToERFunctor_map_interp` at `LawvereKSimER.lean:488–520`,
with K and ER swapped; the proof asymmetry is that
`LawvereERCat`'s morphisms are a bare quotient (no depth
witness wrapping), so `Quotient.inductionOn` applies directly
to `e` rather than to a depth-witness component. -/
theorem erToKFunctor_map_interp {n m : ℕ}
    (e : ERMorNQuo n m) :
    (erToKFunctor_map e).hom.interp = e.interp := by
  unfold erToKFunctor_map
  refine Quotient.inductionOn
    (motive := fun (e : ERMorNQuo n m) =>
      KMorNQuo.interp
        (Quotient.liftOn (s := erMorNSetoid n m) e
          (fun rec =>
            ({ hom := Quotient.mk (kMorNSetoid n m) (erToKN rec),
               depth_witness := Quotient.mk _
                 { rep := erToKN rec,
                   rep_level := fun i => erToKN_level rec i,
                   rep_eq := rfl } } : KSimMor 2 n m))
          _).hom
      = ERMorNQuo.interp e) e ?_
  intro rec
  funext ctx; funext j
  change (erToKN rec j).interp ctx = (rec j).interp ctx
  exact erToKN_interp rec ctx j

end GebLean
