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

<!-- markdownlint-disable MD013 -->

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

<!-- markdownlint-enable MD013 -->

Subtype HEq across sigma-index changes:

```lean
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

<!-- markdownlint-disable MD013 -->

- `GebLean/Utilities/{SetoidCat, Equalities, Category, ArrowSpanAdjunction, Profunctors, OverCategoryEquiv, Graph, Elements, Grothendieck}.lean`
- `GebLean/{BarResolution, LawvereERInterp, LawvereERTetration, LayeredEquivalence}.lean`
- `GebLean/PLang/JudgmentUniverse.lean`

<!-- markdownlint-enable MD013 -->

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

#### Mechanical-fix levers that DON'T help (2026-04-18, investigation 3)

Both of these were tried and left the error count at 101:

1. **`set_option backward.isDefEq.respectTransparency false` at file level.**
   Mathlib uses this per-declaration in about 20 places across
   `CategoryTheory/`. Setting it file-wide in Polynomial.lean
   resolved zero errors. The flag only helps proofs that relied on
   the old pre-4.30 defEq behaviour. Our proofs hit different issues
   (simp pattern matching, dependent-motive `rw`, match-function
   elaboration) that the flag doesn't touch.

2. **`unif_hint` declarations for `(ConcreteCategory.hom
   (TypeCat.ofHom f)) x ≟ f x` and `(ConcreteCategory.hom (f ≫ g))
   x ≟ (ConcreteCategory.hom g) ((ConcreteCategory.hom f) x)`.**
   They compile fine but fix zero proof-body errors.
   Unification hints help during type-level elaboration when Lean
   needs to unify two *forms*; our failures are at
   `rfl`/`simp`/`rw` time inside tactic blocks, not at elaboration.

**Why mathlib's typical-file mechanical fixes worked for them but not
us:** mathlib's typical per-file diff has 5-10 proofs, each 1-5 lines,
using simple `ext`/`simp` patterns that already existed. Their
`unif_hint`s bridge declaration-level form mismatches (e.g.
`Y ⟶ X` vs `(yoneda.obj X).obj (op Y)`) which arise at elaboration.
Our file has ~40 complex proofs with dependent Sigma transports, each
10-50 lines, where the failures are inside proof bodies. We're
analogous to mathlib's hardest cases (e.g.
`Sites/Coherent/LocallySurjective.lean`) which needed deep rewrites
in their PR rather than mechanical substitution.

#### ROOT CAUSE (2026-04-18 session, investigation 2)

**Why `polynomial_typeCat_ofHom_toFun` never fires via `simp only`:**
Mathlib's `@[simp] lemma Fun.toFun_apply : f.toFun x = f x` (in
`Mathlib.CategoryTheory.Types.Basic`) fires **first**, rewriting every
`.toFun x` into the FunLike-coerced `f x` form. The three local
`polynomial_typeCat_*_toFun` helpers all have `.toFun` on the LHS, so
by the time they get a chance to match, the goal has already been
normalized past their pattern.

**Why `rw` also doesn't work with `_apply`-form helpers:**
Even when the FunLike-coerced helpers
(`polynomial_typeCat_*_apply`) are stated at the post-simp form, the
LHS pattern `(ConcreteCategory.hom (TypeCat.ofHom f)) x` introduces a
**dependent-motive issue** in the region-1 proof shape. The rewritten
motive `fun _a => ... ((ConcreteCategory.hom _) _a) ...` refers to
`pf q.fst` where `q.fst` needs type `(ccrFamily G ig).left`, but under
the abstracted `_a`, `q.fst` has type `(ccrFamily G _a.fst).left`. Lean
reports: `Tactic rewrite failed: motive is not type correct`.
Both `rw` and `conv_lhs => rw` fail for the same reason.

**Implication for the three `_toFun` helpers:** They are never triggered
by the default simp set because `Fun.toFun_apply` pre-empts them. They
should be replaced with `_apply` variants (FunLike-coerced form). The
`_apply` variants are already added below alongside the `_toFun` ones.

**Working simp incantation:**

```lean
rw [Over.eqToHom_left]
simp only [TypeCat.Fun.toFun_apply,
  polynomial_typeCat_comp_apply,
  polynomial_typeCat_eqToHom_apply]
```

This reduces the RHS to `cast ⋯ ⟨e, ef⟩` form and splits the LHS
composition, leaving the goal in the form `(ConcreteCategory.hom
(TypeCat.ofHom F2)) ((ConcreteCategory.hom (TypeCat.ofHom F1)) ⟨e,
ef⟩) = cast ⋯ ⟨e, ef⟩`.

**What does NOT work from here:**

- `rfl` after `apply Sigma.ext` (LHS needs deeper beta reduction than
  Lean's kernel rfl will take through nested `ConcreteCategory.hom`
  wrappings).
- `rw [polynomial_typeCat_ofHom_apply]` (dependent motive).
- `conv_lhs => rw [polynomial_typeCat_ofHom_apply]` (same).
- `simp [cast_sigma_eq']` to simplify the RHS cast (synthesis of the
  `hFG : F = G` argument does not happen automatically).

**Suggested next approach for the region-1 proofs:** restructure to
avoid the pointwise reduction altogether. Work at the morphism level
using the existing `rt : (inv ≫ hom) = eqToHom _` hypothesis and
`Over.OverMorphism.ext` + `congrArg Over.Hom.left` rather than
`ext ⟨e, ef⟩` + pointwise Sigma.ext. Or: use HEq directly with
`Subtype.heq_iff_coe_eq` + an explicit `Eq.rec` motive built from
`ccrReindex_hom_inv_cancel`.

#### Findings from 2026-04-18 session

Added a third helper `polynomial_typeCat_eqToHom_toFun` alongside the
two existing helpers at the top of Polynomial.lean's `GebLean`
namespace:

```lean
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

<!-- markdownlint-disable MD013 -->

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

<!-- markdownlint-enable MD013 -->

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

#### Calibrated agent run (2026-04-18, investigation 4)

Dispatched a second autonomous agent with the full Root Cause A and
B knowledge plus the morphism-level proof strategy. Tightly scoped
to region 1 (4 lemmas).

Outcome:

- 128 tool calls, 107 minutes wall-clock (slightly over the 100-call
  scope budget).
- The agent reported four lemmas LSP-green using the morphism-level
  approach (`apply Over.OverMorphism.ext` → `apply
  ConcreteCategory.ext_apply` → `rintro ⟨e, ef⟩` → `dsimp only [...]`
  → derive `rt_left` → close via three sequential `erw`s + final
  `rw [rt_left, Over.eqToHom_left, types_eqToHom_eq_cast, ...]; symm;
  exact cast_sigma_eq' _ (funext ...) e ef`).
- The agent's worktree was cleaned up on completion (per the no-commit
  instruction); the actual code is not on disk and only the agent's
  text report survives. **Future agents must commit to their isolated
  branch before terminating, then leave the branch and worktree path
  for the caller to inspect.**
- The agent also reports a NEW residual blocker: the third `erw
  [polynomial_typeCat_ofHom_apply]` step in the chain hits
  motive-not-type-correct at *kernel batch check* time even though
  LSP's more liberal defEq accepts it. This means even "LSP-green"
  proofs in this region may fail `lake build`. A proper fix needs
  either a custom `Eq.rec`-based lemma per occurrence or a term-mode
  proof for the affected steps.
- The agent reports needing to bump `maxHeartbeats` from 1,000,000 to
  8,000,000 on the morphism-level proofs.

#### Calibration data (the central per-proof rate question)

With full root-cause knowledge plus the morphism-level strategy in
the agent's prompt, an autonomous agent produced ~4 LSP-green-but-
kernel-broken lemmas in 107 minutes. That is roughly 25-30 minutes
per proof, with the proofs still not actually compiling. If we model
the residual kernel-check work as adding ~15 minutes per proof, the
expected steady-state rate is ~40-45 minutes per complex proof.
Region 1 has ~4-6 proofs of this character; the entire file has
~40+ similar proofs. Steady-state full-file completion estimate:
**~25-30 hours of focused agent or human time.**

## Procedure (to reset or resume)

1. Current toolchain: `lean-toolchain` = `leanprover/lean4:v4.30.0-rc1`.
   Mathlib revision pinned in `lake-manifest.json`.
2. To resume: `lake build GebLean.Polynomial` iteratively. Apply the
   translation table and helper-lemma strategy.
3. When Polynomial.lean is clean: run `lake build` (whole project) and
   `lake test`. Any further files that fail are downstream of Polynomial
   and should resolve once it builds.
