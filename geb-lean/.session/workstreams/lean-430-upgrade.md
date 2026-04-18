# Lean v4.30.0-rc1 Upgrade

## Status

Tree is at `leanprover/lean4:v4.30.0-rc1` with mathlib master pinned.
18 of 19 affected files are fully migrated; only `GebLean/Polynomial.lean`
remains broken.

Uncommitted working tree — do not `lake build` and expect success
project-wide.

## The breaking change (one sentence)

Mathlib 4.30 wraps `Type u` morphisms in a structure
`TypeCat.Hom X Y ≃ TypeCat.Fun X Y ≃ (X → Y)`; every place that built
or consumed a raw function as a `Type` morphism now needs
`TypeCat.ofHom` / `ConcreteCategory.hom` / the FunLike coercion.

### Translation reference

| Old API                                  | New API                                              |
| ---------------------------------------- | ---------------------------------------------------- |
| `map f := fun x => ...`                  | `map f := TypeCat.ofHom fun x => ...`                |
| `app := fun c => fun t => ...`           | `app := fun c => TypeCat.ofHom fun t => ...`         |
| `funext x` to prove morphism equality    | `apply ConcreteCategory.ext_apply; intro x`          |
| `congr_fun (α.naturality f) t`           | `NatTrans.naturality_apply α f t`                    |
| `congr_fun (congr_app h c) x`            | `ConcreteCategory.congr_hom (NatTrans.congr_app h c) x` |
| `congr_fun (F.map_id _) x`               | `ConcreteCategory.congr_hom (F.map_id _) x`          |
| `congr_fun (F.map_comp f g) x`           | `Functor.map_comp_apply F f g x`                     |
| `types_comp_apply`                       | `ConcreteCategory.comp_apply`                        |
| `types_id_apply` (as `simp`)             | Drop; `simp` already reduces `𝟙 X x = x`              |
| `id` where morphism expected             | `TypeCat.ofHom _root_.id` or `𝟙 _`                    |
| `FunctorToTypes.map_comp_apply`          | `Functor.map_comp_apply`                             |
| `FunctorToTypes.map_id_apply`            | `Functor.map_id_apply`                               |
| `push_neg`                               | `push Not`                                           |
| `Mathlib.CategoryTheory.Topos.Classifier`| `Mathlib.CategoryTheory.Subobject.Classifier.Defs`   |
| `Classifier`                             | `Subobject.Classifier`                               |
| `HasClassifier`                          | `HasSubobjectClassifier`                             |
| `f.base x` (old TypeCat)                 | `f.base.hom x`                                       |
| `show` that changes the goal             | `change` (style linter flags `show`)                 |

Subtype HEq across sigma-index changes:
```
refine Sigma.ext h_fst ?_
apply (Subtype.heq_iff_coe_eq ?_).mpr rfl
intro y
exact ⟨fun hp => hp.trans h_fst, fun hp => hp.trans h_fst.symm⟩
```

## Completed files (18)

### Originally-listed in the first pass (5 files)
- `GebLean/Utilities/Families.lean`
- `GebLean/ComprehensiveFactorization.lean`
- `GebLean/Utilities/Presheaf.lean`
- `GebLean/CatJudgmentAdjunction.lean`
- `GebLean/DepCategoryJudgments.lean`

### Discovered during first post-fix build (5 files)
- `GebLean/Utilities/WSubfunctor.lean`
- `GebLean/Utilities/Slice.lean`
- `GebLean/PLang/CatJudgGrothendieck.lean`
- `GebLean/PshRelDouble.lean`
- (reuses all pre-existing fixed files)

### Discovered during second post-fix build (5 files)
- `GebLean/Utilities/TwistedArrow.lean`
- `GebLean/PshRelEdgeOverOmega.lean`
- `GebLean/PshRelEdgeExp.lean`
- `GebLean/PshInternalCat.lean`
- `GebLean/PLang/CatJudgGrAdjunction.lean`

### Already-completed in prior session (pre-start)
- `GebLean/Utilities/{SetoidCat, Equalities, Category, ArrowSpanAdjunction, Profunctors, OverCategoryEquiv, Graph, Elements, Grothendieck}.lean`
- `GebLean/{BarResolution, LawvereERInterp, LawvereERTetration, LayeredEquivalence}.lean`
- `GebLean/PLang/JudgmentUniverse.lean`

## Remaining file

### `GebLean/Polynomial.lean` (6027 lines, 100+ errors, display-capped at 103)

Two local private helper simp lemmas have been added at the top of the
file's `GebLean` namespace (after `import Mathlib.CategoryTheory.Types.Basic`):

- `polynomial_typeCat_comp_toFun`: reduces
  `(ConcreteCategory.hom (f ≫ g)).toFun x` to sequential application.
- `polynomial_typeCat_ofHom_toFun`: reduces
  `(ConcreteCategory.hom (TypeCat.ofHom f)).toFun x` to `f x`.

Both are `@[simp]`. However, testing shows mathlib's current simp normal
form rewrites past these helpers' LHS pattern before they can fire in
many contexts, so a further set of helpers at the `.hom'.toFun` projection
level may be needed.

#### Findings from 2026-04-18 session

Added a third helper `polynomial_typeCat_eqToHom_toFun` alongside the
two existing helpers at the top of Polynomial.lean's `GebLean`
namespace:

```
@[simp]
private lemma polynomial_typeCat_eqToHom_toFun
    {A B : Type u} (h : A = B) (x : A) :
    (ConcreteCategory.hom (eqToHom (C := Type u) h)).toFun x =
      cast h x := by
  subst h; rfl
```

Behaviour observed while attempting `polyComp_homMk_inv_hom` at line
3086:

- `polynomial_typeCat_comp_toFun` *does* fire via `simp only`.
- `polynomial_typeCat_eqToHom_toFun` *does* fire via `simp only` once
  the outer `Over.Hom.left (eqToHom h)` has been rewritten to
  `eqToHom (…)` (using `Over.eqToHom_left` / `Comma.eqToHom_left`).
- `polynomial_typeCat_ofHom_toFun` does **not** fire under
  `simp only` even though its LHS `(ConcreteCategory.hom
  (TypeCat.ofHom f)).toFun x` literally appears in the goal. Cause
  not yet identified; possibly a universe-unification or
  `ConcreteCategory.hom` vs `TypeCat.Hom.hom` abbrev form issue.
  Until that is resolved, uses of `TypeCat.ofHom`-composed morphisms
  on literal arguments require either manual `show`/`change`
  restatement or bypassing the helper with a different proof
  strategy.
- `types_eqToHom_eq_cast` from `Utilities/Category.lean` cannot
  rewrite `(ConcreteCategory.hom (eqToHom h)).toFun x` — its LHS
  is stated with the FunLike coercion, which does not match the
  `.toFun` form syntactically. The new helper
  `polynomial_typeCat_eqToHom_toFun` handles this case.

#### Remaining blockers by region
1. Lines 3069-3265 (`polyComp_homMk_inv_hom`, `polyComp_hom_inv_at_idx`,
   `polyComp_homMk_hom_inv`, `polyComp_inv_hom_at_idx`): Sigma-equality
   reduction of `(ConcreteCategory.hom (TypeCat.ofHom (fun q => ⟨q.fst, g q⟩))).toFun ⟨e, ef⟩`
   doesn't unify with `⟨e, g ⟨e, ef⟩⟩` through `simp`/`rfl`. Approach
   forward: add a `polynomial_typeCat_ofHom_sigma_fst` helper; restate
   proof to avoid `Sigma.ext` and instead use `Subtype.ext_iff` or direct
   `heq_of_eq` after `apply Over.OverMorphism.ext; ext`.
2. Lines 3580-4390 (`polyHorizComp`, `WTypeDiagram.comp`, `WTypeDiagramHom`):
   `.base.hom` / `.left.hom` propagation. `rcases e : (fiberOver X Z (g.comp f) b).1`
   fails because Sigma is no longer destructuring at the expected level;
   use `obtain ⟨fst, snd⟩ := ...` with explicit field names.
3. Lines 3968-3970 (`WTypeDiagram.comp_eval_fiberEquiv.left_inv`): elaboration
   failure emits `declaration uses sorry` — no explicit `sorry` text in
   file, but the tactic chain leaves residual goals. Same Sigma.ext
   pattern as region 1.
4. Lines 4369-4434 (`wTypeToPolyBetweenMap`, `polyBetweenToWTypeMap`):
   `⟨...⟩` anonymous-constructor type inference failures and `rfl`
   failures — need explicit type ascriptions and `TypeCat.ofHom` wrapping.
5. Lines 4560-5500 (`unitBase_*`, `counitIndex_*`, `counitFiberMap`,
   `counitHom`): multiple kernel-level issues including "incorrect number
   of universe levels parameters" for match types, and "unknown constant
   `GebLean.polyBetweenToWTypeMap_comp`" suggesting some referenced
   definitions fail to elaborate upstream. Line 4583 also emits
   `declaration uses sorry` indirect.
6. Lines 4938-4962 (`counitIndex_toFun.match_3`): match-function
   universe-level mismatch.
7. Lines 5642-5929 (`polyCell*`) and 6037-6079 (`polyDoubleLaws`,
   `polyDoubleData`): obscured by maxErrors cutoff; expected to contain
   the same patterns.

#### Procedure to resume Polynomial.lean
1. Add more simp helpers at the top of Polynomial.lean for the
   `.hom'.toFun` pattern form (matching mathlib's simp normal form) and
   for `Sigma.mk`-style reductions of composed `TypeCat.ofHom` applications.
2. Work through regions in order, starting at line 3069. Each region's
   pattern is localised; a successful fix in one region's representative
   lemma should copy-paste to its peers.
3. Regions 5 and 6 may need separate investigation for the kernel-level
   issues; check whether any upstream definitions are partially
   specified or need their declaration headers restructured.

## Procedure (to reset or resume)

1. Current toolchain: `lean-toolchain` = `leanprover/lean4:v4.30.0-rc1`.
   Mathlib revision pinned in `lake-manifest.json`.
2. To resume: `lake build GebLean.Polynomial` iteratively. Apply the
   translation table and helper-lemma strategy.
3. When Polynomial.lean is clean: run `lake build` (whole project) and
   `lake test`. Any further files that fail are downstream of Polynomial
   and should resolve once it builds.
