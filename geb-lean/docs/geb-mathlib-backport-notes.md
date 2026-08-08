# geb-mathlib back-port notes

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
## Contents

- [Categories](#categories)
  - [1. `GebMeta` not vendored](#1-gebmeta-not-vendored)
  - [2. `linter.checkUnivs` configuration absent in v4.29](#2-lintercheckunivs-configuration-absent-in-v429)
  - [3. `ConcreteCategory` redesign (mathlib pull request 34741)](#3-concretecategory-redesign-mathlib-pull-request-34741)
  - [4. Eliminator motive left as an unreduced beta-redex](#4-eliminator-motive-left-as-an-unreduced-beta-redex)
  - [5. `simp` rewriting under dependent proof arguments narrowed in v4.33](#5-simp-rewriting-under-dependent-proof-arguments-narrowed-in-v433)
  - [6. Explicit universe arguments in generalized field notation](#6-explicit-universe-arguments-in-generalized-field-notation)
  - [7. `rw`'s closing `rfl` runs at reducible transparency](#7-rws-closing-rfl-runs-at-reducible-transparency)
  - [8. Derived `Repr` instances carry an unused precedence argument](#8-derived-repr-instances-carry-an-unused-precedence-argument)
  - [9. Subobject classifier moved out of `Topos` in v4.33](#9-subobject-classifier-moved-out-of-topos-in-v433)
  - [10. `simp` leaves a `cast`'s proof argument unfolded](#10-simp-leaves-a-casts-proof-argument-unfolded)
- [Updating the patch for a new upstream](#updating-the-patch-for-a-new-upstream)
  - [The no-op condition](#the-no-op-condition)
- [Module exclusion](#module-exclusion)
- [Tooling notes](#tooling-notes)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

These notes catalogue the categories of change in
`scripts/geb-mathlib-backport.patch`, which adapts the vendored
`geb-mathlib` `Geb` source (mathlib `v4.33.0-rc1`) to compile under this
repository's `v4.29.0-rc6`. When a refresh fails, check whether the new
failure matches a category below (extend the corresponding hunk) or is
genuinely new (decide the adaptation, add a category here).

## Categories

### 1. `GebMeta` not vendored

- Upstream cause: the `Geb` index imports `GebMeta`, a separate library
  not vendored (its `@[env_linter]` would mis-audit `geb-lean`).
- v4.29 symptom: `unknown module GebMeta` building the `Geb` index.
- Adaptation: delete the `import GebMeta` line from `Geb.lean`.

### 2. `linter.checkUnivs` configuration absent in v4.29

- Upstream cause: `geb-mathlib` suppresses the `linter.checkUnivs`
  universe linter on its `Slice` and `Presheaf` structures and on the
  `IndRec` declarations whose separated arity universes `uA`/`uB`
  appear only together under `max`. As of upstream commit `0a772c2`
  the suppression is the `set_option linter.checkUnivs false in` lines
  alone; the `@[nolint checkUnivs]` attributes were removed upstream.
- v4.29 symptom: `Unknown option 'linter.checkUnivs'`; without a
  replacement suppression, the `checkUnivs` env-linter then fires on
  the structures under `lake lint`.
- Adaptation: delete the `set_option linter.checkUnivs false in` lines
  and insert an `@[nolint checkUnivs]` attribute between each affected
  declaration's docstring and its `structure` or `def` keyword
  (`nolint` is the v4.29-compatible suppression). Where the
  declaration already carries an attribute list, the suppression joins
  it in place (`@[expose, nolint checkUnivs]`). The affected
  structures are `SliceDomPFunctor` and `SlicePFunctor` in
  `Slice/Basic.lean`; `PresheafDomPFunctorData`,
  `PresheafDomPFunctor`, `PresheafPFunctorData`, and `PresheafPFunctor`
  in `Presheaf/Basic.lean`; and `FinitePresheafPFunctor` in
  `Presheaf/Finite/Basic.lean`. The affected definitions in
  `Slice/Basic.lean` are `SliceDomPFunctor.prod`,
  `SliceDomPFunctor.representable`, `SliceDomPFunctor.prodSlice`,
  `SlicePFunctor.coprod`, and `SlicePFunctor.ofFamily`; those in
  `IndRec/Basic.lean` are `IR.Shape`, `IR.pFunctor`, `IR.Obj`,
  `IR.ObjFst`, `IR.Dest`, `IR.Alg`, the top-level `IR`, and
  `IR.interpObjIota`; those in `IndRec/Slice.lean` are `IR.sliceCode`,
  `IR.toSlicePFunctorIota`, `IR.toSlicePFunctorSigma`,
  `IR.toSlicePFunctorDelta`, and `IR.toSlicePFunctorAlg`.
- Prose adaptation: the module docstrings of `Presheaf/Basic.lean` and
  `IndRec/Basic.lean` describe the suppression as
  "The `linter.checkUnivs false` option suppresses the ...". Because
  the option line is deleted and the attribute inserted, reword to
  "The `@[nolint checkUnivs]` attribute suppresses the ..." so the
  docstring describes the code as it stands in v4.29.

### 3. `ConcreteCategory` redesign (mathlib pull request 34741)

- Upstream cause: the post-`HasForget` `ConcreteCategory` adds the
  `ConcreteCategory.hom` accessor, `ConcreteCategory.comp_apply`,
  `ConcreteCategory.hom_ext`, and `ConcreteCategory.hom_ofHom`; the same
  redesign routes a `Type`-category morphism through the `TypeCat.Fun`
  coercion layer, with `TypeCat.Fun.toFun_apply` and
  `NatTrans.naturality_apply` reading through it. In v4.29 an `Over`
  base map, an `Iᵒᵖ ⥤ Type` presheaf map, and a `Type`-category
  morphism are already functions, so neither the accessors nor the
  coercion layer exist.
- v4.29 symptom: `Unknown identifier 'ConcreteCategory.hom'` /
  `'ConcreteCategory.comp_apply'` / `'ConcreteCategory.hom_ext'` /
  `'ConcreteCategory.hom_ofHom'` / `'TypeCat.Fun.toFun_apply'`, or
  `Unknown constant 'CategoryTheory.NatTrans.naturality_apply'`.
- Adaptation in `Slice/Functor.lean`: drop the `ConcreteCategory.hom`
  wrapper (and its two docstring mentions); rewrite the `over_hom_comp`
  proof to `exact congrFun (Over.w g) z`.
- Adaptation in `Presheaf/Basic.lean`: the input-presheaf `map`
  naturality proof closes with
  `simp only [← ConcreteCategory.comp_apply]; rw [α.naturality f.op]`.
  Replace both tactics with `exact FunctorToTypes.naturality _ _ α f.op _`,
  the `Type`-valued naturality lemma whose statement is the goal
  (`α.app Y (Z.map f x) = Z'.map f (α.app X x)`).
- Adaptation in `Presheaf/W.lean` (`value_wRestrTree`): the same
  `ConcreteCategory.comp_apply` gap appears in a naturality step, a
  term-mode proof chaining `ConcreteCategory.comp_apply` and
  `ConcreteCategory.congr_hom`. Replace the chain with the term
  `(FunctorToTypes.naturality _ _ α f.op _).symm`; the `.symm` is
  needed because this goal is the naturality equation with sides
  reversed.
- Adaptation in `Univariate/W.lean` (`wElim`, `wUniqueHom`): the algebra
  structure map and the algebra-morphism component are morphisms of
  `Type (max uA uB)`, read through `ConcreteCategory.hom` and compared
  with `ConcreteCategory.hom_ext`. Drop the wrapper, replace
  `ConcreteCategory.hom_ext _ _` with `funext`, and replace
  `ConcreteCategory.congr_hom g.h` with `congrFun g.h`: in v4.29 the
  morphism is the function and its equation is the function equation.
- Adaptation in `Internal/PresheafIRProto/Basic.lean`
  (`postcompArityHom`): the arity-hom naturality proof closes with
  `simp only [← ConcreteCategory.comp_apply]; rw [ν.naturality f.op]`.
  Replace both tactics with
  `exact FunctorToTypes.naturality _ _ ν f.op _`, as in
  `Presheaf/Basic.lean` above.
- Adaptation in `Internal/PresheafIRProto/Codes.lean`
  (`BaseArity.reindexHom`): the naturality proof strips the coercion
  layers with
  `simp only [TypeCat.Fun.toFun_apply, comp_apply, ConcreteCategory.hom_ofHom]`
  before `exact congrFun (hP.reindex_naturality g f.unop).symm d`.
  Delete the `simp only` line; in v4.29 the goal is already the
  function equation the `exact` closes.
- Adaptation in `Internal/PresheafIRProto/Functor.lean`
  (`arityHomEquivNatTrans`): the backward direction re-states
  naturality with `NatTrans.naturality_apply α f.op b`. Replace it
  with `FunctorToTypes.naturality _ _ α f.op b`.

### 4. Eliminator motive left as an unreduced beta-redex

- Upstream cause: a proof applies a dependent eliminator with an
  explicit `motive` and enters the minor premise via
  `fun ... => by ...`. The affected sites are `elimData_valid` in
  `Slice/W.lean` and `wValidBool_eq_true_iff` in `Slice/Decidable.lean`
  (both `WType.rec`), `isHereditarilyNaturalBoolCore_eq_true_iff` in
  `Presheaf/Decidable.lean` (`SlicePFunctor.W.induction`), and
  `ofRose_toRose` in `Internal/ConcreteSyntax.lean` (`Ast.ind`).
- v4.29 symptom: the goal is `(fun w => ...) (WType.mk a f)` — the motive
  lambda is not beta-reduced at the constructor — so the opening
  `rw` reports "Did not find an occurrence of the pattern" (the rewritten
  subterm is hidden inside the unapplied lambda). Later mathlib
  elaborates the motive application in reduced form, so upstream needs no
  such step.
- Adaptation: prepend `beta_reduce` as the first tactic of the minor
  premise, exposing the subterm for the existing rewrite. The induction
  hypothesis stays in unreduced form, which is harmless: it is used only
  where its type is needed up to beta.

### 5. `simp` rewriting under dependent proof arguments narrowed in v4.33

- Upstream cause: `Presheaf/W.lean`'s `isHereditarilyNatural_mk_forgetNode`
  closes its converse direction with
  `exact h.trans (wRestrTree_congr F g (value_down F n b) _ _)`. The
  `wRestrTree_congr` bridge compensates for v4.33's `simp`, which no
  longer rewrites the `value_down` occurrence sitting under
  `wRestrTree`'s dependent head-index proof argument.
- v4.29 symptom: `simp only [value_down F n, map_down F g] at h`
  rewrites that occurrence as well, so the bridge's left-hand side no
  longer occurs in `h`: application type mismatch on the `h.trans`
  argument.
- Adaptation: close with `exact h` (drop the `.trans` bridge). The
  private `wRestrTree_congr` lemma compiles under v4.29 and is left
  unmodified, unused.

### 6. Explicit universe arguments in generalized field notation

- Upstream cause: `Univariate/W.lean`, `Univariate/Initial.lean`, and
  `Slice/Functor.lean` instantiate `PFunctor.functor` at an explicit
  universe list written in generalized field notation on a local
  variable: `P.functor.{uA, uB, max uA uB}` and
  `F.toPFunctor.functor.{uA, uB, uD}`; `FinCat/Hom2.lean`'s
  `Hom₂.toNatTrans` states its result type through
  `F.toFunctor.{v, u}` on the local variables `F` and `G`.
- v4.29 symptom: ``invalid use of explicit universe parameters, `P` is a
  local variable``. v4.29 binds the universe list to the local variable
  the notation is applied to, rather than to the constant the notation
  resolves to.
- Adaptation: write the application in prefix form, so the universe list
  sits on the constant: `PFunctor.functor.{uA, uB, max uA uB} P`,
  `PFunctor.functor.{uA, uB, uD} F.toPFunctor`, and
  `NatTrans (Hom.toFunctor.{v, u} F) (Hom.toFunctor.{v, u} G)`.

### 7. `rw`'s closing `rfl` runs at reducible transparency

- Upstream cause: `FinSetSkel/Exponential/Closed.lean`'s
  `expHomEquiv_naturality` proves its whiskering step `hten` by
  `rw [comp_get, whiskerLeft_get]` alone.
- v4.29 symptom: `unsolved goals`, on a goal whose two sides are the
  same term at the two spellings `Fin (X ⊗ Z').len` and
  `Fin (X.len * Z'.len)` of the index type. The two are definitionally
  equal — `⊗` is `FinSetSkel.prodObj` on the nose — but not reducibly
  so, and `rw` closes a residual goal only with `with_reducible rfl`.
- Adaptation: append `rfl`, which runs at default transparency:
  `rw [comp_get, whiskerLeft_get]; rfl`.
- Second site: `Internal/PresheafIRProto/Codes.lean`'s
  `isFunctorial_pullback` closes its `reindex_id` field with a `rw`
  whose residual goal is `cast ⋯ d = cast ⋯ d`. The two transport
  proofs are definitionally equal by proof irrelevance but not
  reducibly so. Append `rfl` after the `rw`.

### 8. Derived `Repr` instances carry an unused precedence argument

- Upstream cause: `FinSetSkel/Basic.lean` declares the objects with
  `deriving DecidableEq, Repr`, and `Internal/ConcreteSyntax.lean`
  declares `Ann` with `deriving Repr, DecidableEq, Inhabited`.
- v4.29 symptom: the `unusedArguments` env-linter reports
  `instReprFinSetSkel.repr argument 2 prec✝ : ℕ` (respectively
  `instReprAnn.repr argument 2 prec✝ : ℕ`) under `lake lint`; v4.29's
  `Repr` deriving handler emits a `repr` that ignores the precedence
  argument for a structure whose representation needs no
  parenthesisation.
- Adaptation: suppress the linter on the generated declaration,
  `attribute [nolint unusedArguments] instReprFinSetSkel.repr`
  (respectively `attribute [nolint unusedArguments] instReprAnn.repr`),
  after the structure (the attribute cannot be attached to a `deriving`
  clause).

### 9. Subobject classifier moved out of `Topos` in v4.33

- Upstream cause: `CategoryTheory/ElementaryTopos.lean` and
  `FinSetSkel/Classifier/Instance.lean` import
  `Mathlib.CategoryTheory.Subobject.Classifier.Defs` and name the
  structure `Subobject.Classifier`.
- v4.29 symptom: `unknown module` on the import. The declarations
  themselves are present: v4.29 has the same `Classifier` structure,
  `Classifier.isTerminalΩ₀`, and a `Classifier.mkOfTerminalΩ₀` of
  identical signature, in `Mathlib.CategoryTheory.Topos.Classifier`
  under the namespace `CategoryTheory` rather than
  `CategoryTheory.Subobject`.
- Adaptation: import `Mathlib.CategoryTheory.Topos.Classifier` and drop
  the `Subobject.` qualifier. In `ElementaryTopos.lean` the enclosing
  `namespace CategoryTheory` leaves `Classifier C` and
  `Classifier.isTerminalΩ₀` unambiguous; in
  `FinSetSkel/Classifier/Instance.lean` the surrounding
  `namespace FinSetSkel` has a `Classifier` namespace of its own, so
  the mathlib structure is named in full as
  `CategoryTheory.Classifier`.

### 10. `simp` leaves a `cast`'s proof argument unfolded

- Upstream cause: `Internal/PresheafIRProto/Codes.lean`'s
  `isFunctorial_pullback` proves its `reindex_comp` field by
  `simp only [pullback] at d ⊢` followed by
  `rw [reindex_cast_shape (hh := ...), ← reindex_comp_apply P hP]`. The
  goal carries a `cast` transporting `d` along the shape equality
  `hh`, and `reindex_cast_shape` states that transport with the motive
  `fun u ↦ (P.fam (F.q u.1)).Dir i`.
- v4.29 symptom: `Did not find an occurrence of the pattern`
  `P.reindex ?k (cast ⋯ ?d)`, on a target that visibly contains such a
  subterm. The `simp only [pullback]` rewrites the goal but not the
  proof argument of `cast`, which simp treats as irrelevant, so the
  goal's motive stays
  `fun u ↦ ((P.pullback F.toPresheafPFunctorData).fam ↑u).Dir i`. That
  is the lemma's motive after delta-reducing `BaseArity.pullback`,
  below the transparency at which `rw` matches.
- Adaptation: precede the `rw` with a `change` restating the goal's
  `cast` at the lemma's motive, leaving the rest of the goal to
  unification:

  ```lean
  change _ = P.reindex _ (P.reindex _
    (cast (congrArg (fun u : F.Shape j'' ↦ (P.fam (F.q u.1)).Dir i)
      (congrFun (F.isFunctorial.shapeRestr_comp g h) s)) d))
  ```

  `change` rather than `show`: the `show` tactic is restricted by a
  linter to indicating intermediate goal states, and this restatement
  is a transparency adjustment.

## Updating the patch for a new upstream

The vendored tree is a pure function of two committed inputs: the
upstream `geb-mathlib` commit and this patch.
`scripts/refresh-geb-mathlib.sh` recomputes it by re-cloning upstream
and re-applying the patch with `git apply`. A patch hunk's context
lines are tied to the upstream revision it was generated against; when
upstream moves, the context drifts and `git apply` rejects the patch
even though the adaptation itself is still valid. (The rejection that
prompted this procedure was a docstring reword upstream that displaced
the category-2 hunk's context.)

To update the patch to a new upstream revision, ahead of the automated
refresh:

1. Clone upstream at the target revision and overlay it on a scratch
   copy of `vendor/geb-mathlib`, exactly as the refresh script does
   (wipe `Geb.lean` and `Geb/`, copy the fresh source in).
2. Re-apply each adaptation category above to the fresh source.
   `patch -F<n>` (or `git apply --3way`) re-anchors a hunk whose
   context drifted but whose removed lines are unchanged. A category
   whose removed lines themselves changed, or a newly-ingested module
   carrying the same v4.29 incompatibility, needs the category extended
   by hand.
3. Build and check the result with the same commands CI runs:
   `bash scripts/tests/test-lint-driver.sh`, `lake build Geb`,
   `lake test`, `lake lint -- Geb`, and
   `lake build GebLeanAxiomChecks`. The `Geb` library's
   `globs = ["Geb.*"]` compiles every vendored module whether or not it
   is imported, so a newly-ingested module that might need to be excluded
   surfaces here rather than silently.
4. Regenerate the patch as the diff between the pristine fresh source
   and the adapted tree (for example
   `git diff --no-index <pristine> <adapted>`), preserving the
   `a/vendor/geb-mathlib/...` path prefixes the refresh script expects.

### The no-op condition

A patch update is correct exactly when re-running the refresh against
the same upstream revision is a no-op: the regenerated vendored source
is byte-identical to what the update produced. After the patch and the
regenerated vendored tree are committed together,
`scripts/refresh-geb-mathlib.sh <rev>` followed by
`git diff -- vendor/geb-mathlib` must leave the tree unchanged.
`PROVENANCE.md` participates in the check: it records the upstream
commit SHA and a content checksum of the patch, both of which are
stable under a same-inputs re-run. When a refresh changes nothing but
`PROVENANCE.md` (for example, a new upstream revision touching none of
the mirrored files), the script restores `PROVENANCE.md` so the
refresh workflow opens no pull request.

## Module exclusion

When a vendored module depends on a mathlib definition or theorem that
does not exist in `v4.29.0-rc6` (a genuinely new result, not a rename),
no patch hunk can supply it and `sorry`/`admit` are banned. Such a module
is dropped from the vendored copy via the refresh script's exclusion list
until either `geb-lean` is forward-migrated to `v4.33.0-rc1` or the
consuming exploration is deferred. No module has yet met that condition,
so the script carries no exclusion list.

A reference to an unknown module does not necessarily require a module to be
excluded: a  declaration that moved between modules or namespaces is a rename,
and category 9 is the worked case. Before excluding a module, locate each
name it needs in the v4.29 tree and compare signatures.

## Tooling notes

- Linting: `lake lint Geb` (a lib name) is not a valid invocation —
  `lake lint` names modules. The refresh lints the single root module:
  `lake lint -- Geb`. `runLinter` loads one flat environment whose
  declaration set covers the root module's import closure, so the
  umbrella module gives whole-tree coverage for one environment's
  memory cost; enumerating every vendored module on the command line
  instead loads an environment per module and exhausts memory.
  `scripts/tests/test-lint-driver.sh` guards both halves of the
  invariant: the workflow keeps the root-module invocation, and no
  vendored `Geb.*` module is orphaned from the `Geb` umbrella (an
  orphan would silently escape the linter).
- Axiom check: the `GebLeanMeta.detectNonstandardAxiom` env_linter
  scans the vendored `Geb.*` tree via the
  `GebLeanAxiomChecks/Vendored.lean` gate
  (`#lint only detectNonstandardAxiom in Geb`), so a patch-introduced
  non-standard axiom fails `lake build GebLeanAxiomChecks`. This
  complements the build under `-DwarningAsError=true` (which rejects
  `sorry`). `propext`, `Quot.sound`, and `Classical.choice` are
  accepted; everything else is fatal.
- Category 2 above retains the `@[nolint checkUnivs]` attributes: only
  the `set_option linter.checkUnivs false in` lines are stripped; the
  `nolint` attributes remain the suppression the universe linter needs.
