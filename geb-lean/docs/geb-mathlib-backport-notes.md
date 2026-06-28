# geb-mathlib back-port notes

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
## Contents

- [Categories](#categories)
  - [1. `GebMeta` not vendored](#1-gebmeta-not-vendored)
  - [2. `linter.checkUnivs` configuration absent in v4.29](#2-lintercheckunivs-configuration-absent-in-v429)
  - [3. `ConcreteCategory` redesign (mathlib pull request 34741)](#3-concretecategory-redesign-mathlib-pull-request-34741)
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
  universe linter on its `Slice` structures.
- v4.29 symptom: `Unknown option 'linter.checkUnivs'`.
- Adaptation: delete the `set_option linter.checkUnivs false in` lines;
  keep the `@[nolint checkUnivs]` attributes (the universe linter still
  fires on the structures, and `nolint` is the v4.29-compatible
  suppression).

### 3. `ConcreteCategory` redesign (mathlib pull request 34741)

- Upstream cause: the post-`HasForget` `ConcreteCategory` adds the
  `ConcreteCategory.hom` accessor and `ConcreteCategory.comp_apply`; in
  v4.29 an `Over` base map is already a function.
- v4.29 symptom: `Unknown identifier 'ConcreteCategory.hom'` /
  `'ConcreteCategory.comp_apply'`.
- Adaptation: drop the `ConcreteCategory.hom` wrapper (and its two
  docstring mentions); rewrite the `over_hom_comp` proof to
  `exact congrFun (Over.w g) z`.

## The hard wall

When a vendored module depends on a mathlib definition or theorem that
does not exist in `v4.29.0-rc6` (a genuinely new result, not a rename),
no patch hunk can supply it and `sorry`/`admit` are banned. Such a module
is dropped from the vendored copy via the refresh script's exclusion list
until either `geb-lean` is forward-migrated to `v4.32.0-rc1` or the
consuming exploration is deferred.

## Tooling notes

- Linting: `lake lint Geb` (a lib name) is not a valid invocation —
  `lake lint` names modules. The refresh lints the vendored modules
  computed from the `.lean` files on disk: `lake lint -- $VMODS` where
  `VMODS=$(cd vendor/geb-mathlib && find . -name '*.lean' -printf '%P\n'
  | sed 's|\.lean$||; s|/|.|g')`. This stays generic as the namespace
  grows.
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
