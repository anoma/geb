# geb-mathlib back-port notes

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
## Contents

- [Categories](#categories)
  - [1. `GebMeta` not vendored](#1-gebmeta-not-vendored)
  - [2. `linter.checkUnivs` configuration absent in v4.29](#2-lintercheckunivs-configuration-absent-in-v429)
  - [3. `ConcreteCategory` redesign (mathlib pull request 34741)](#3-concretecategory-redesign-mathlib-pull-request-34741)
  - [4. `WType.rec` motive left as an unreduced beta-redex](#4-wtyperec-motive-left-as-an-unreduced-beta-redex)
- [Updating the patch for a new upstream](#updating-the-patch-for-a-new-upstream)
  - [The no-op condition](#the-no-op-condition)
- [The hard wall](#the-hard-wall)
- [Tooling notes](#tooling-notes)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

These notes catalogue the categories of change in
`scripts/geb-mathlib-backport.patch`, which adapts the vendored
`geb-mathlib` `Geb` source (mathlib `v4.32.0-rc1`) to compile under this
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
  universe linter on its `Slice` and `Presheaf` structures. As of
  upstream commit `0a772c2` the suppression is the
  `set_option linter.checkUnivs false in` lines alone; the
  `@[nolint checkUnivs]` attributes were removed upstream.
- v4.29 symptom: `Unknown option 'linter.checkUnivs'`; without a
  replacement suppression, the `checkUnivs` env-linter then fires on
  the structures under `lake lint`.
- Adaptation: delete the `set_option linter.checkUnivs false in` lines
  and insert an `@[nolint checkUnivs]` attribute between each affected
  structure's docstring and its `structure` keyword (`nolint` is the
  v4.29-compatible suppression). The affected structures are
  `SliceDomPFunctor` and `SlicePFunctor` in `Slice/Basic.lean` and
  `PresheafDomPFunctorData`, `PresheafDomPFunctor`,
  `PresheafPFunctorData`, and `PresheafPFunctor` in
  `Presheaf/Basic.lean`.
- Prose adaptation: `Presheaf/Basic.lean`'s module docstring describes
  the suppression as "The `linter.checkUnivs false` option suppresses
  the ...". Because the option line is deleted and the attribute
  inserted, reword to "The `@[nolint checkUnivs]` attribute suppresses
  the ..." so the docstring describes the code as it stands in v4.29.

### 3. `ConcreteCategory` redesign (mathlib pull request 34741)

- Upstream cause: the post-`HasForget` `ConcreteCategory` adds the
  `ConcreteCategory.hom` accessor and `ConcreteCategory.comp_apply`; in
  v4.29 an `Over` base map and an `Iᵒᵖ ⥤ Type` presheaf map are already
  functions.
- v4.29 symptom: `Unknown identifier 'ConcreteCategory.hom'` /
  `'ConcreteCategory.comp_apply'`.
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
  `ConcreteCategory.comp_apply` gap appears in a naturality step written
  `rw [← ConcreteCategory.comp_apply, ← α.naturality f.op,
  ConcreteCategory.comp_apply]`. Replace with
  `exact (FunctorToTypes.naturality _ _ α f.op _).symm`; the `.symm` is
  needed because this goal is the naturality equation with sides
  reversed.

### 4. `WType.rec` motive left as an unreduced beta-redex

- Upstream cause: `Slice/W.lean`'s `elimData_valid` proves an `↔` by
  applying the dependent recursor `WType.rec` with an explicit `motive`,
  entering the minor premise via `fun a f ih => by ...`.
- v4.29 symptom: the goal is `(fun w => ...) (WType.mk a f)` — the motive
  lambda is not beta-reduced at the constructor — so the opening
  `rw [F.wValid_mk, elimData_valid_mk]` reports "Did not find an
  occurrence of the pattern" (the `F.WValid (WType.mk a f)` subterm is
  hidden inside the unapplied lambda). Later mathlib elaborates the
  recursor's motive application in reduced form, so upstream needs no
  such step.
- Adaptation: prepend `beta_reduce` as the first tactic of the minor
  premise, exposing `F.WValid (WType.mk a f)` for the existing rewrite.

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
   `lake build Geb`, `lake test`, `lake lint -- $VMODS`, and
   `lake build GebLeanAxiomChecks`. The `Geb` library's
   `globs = ["Geb.*"]` compiles every vendored module whether or not it
   is imported, so a newly-ingested module that hits the hard wall
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

## The hard wall

When a vendored module depends on a mathlib definition or theorem that
does not exist in `v4.29.0-rc6` (a genuinely new result, not a rename),
no patch hunk can supply it and `sorry`/`admit` are banned. Such a module
is dropped from the vendored copy via the refresh script's exclusion list
until either `geb-lean` is forward-migrated to `v4.32.0-rc1` or the
consuming exploration is deferred.

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
