# geb-mathlib back-port notes

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
## Contents

- [Categories](#categories)
  - [1. `GebMeta` not vendored](#1-gebmeta-not-vendored)
  - [2. `linter.checkUnivs` configuration absent in v4.29](#2-lintercheckunivs-configuration-absent-in-v429)
  - [3. `ConcreteCategory` redesign (mathlib pull request 34741)](#3-concretecategory-redesign-mathlib-pull-request-34741)
  - [4. Eliminator motive or functional argument left as an unreduced beta-redex](#4-eliminator-motive-or-functional-argument-left-as-an-unreduced-beta-redex)
  - [5. `simp` rewriting under dependent proof arguments narrowed in v4.33](#5-simp-rewriting-under-dependent-proof-arguments-narrowed-in-v433)
  - [6. Explicit universe arguments in generalized field notation](#6-explicit-universe-arguments-in-generalized-field-notation)
  - [7. `rw`'s closing `rfl` runs at reducible transparency](#7-rws-closing-rfl-runs-at-reducible-transparency)
  - [8. Derived `Repr` instances carry an unused precedence argument](#8-derived-repr-instances-carry-an-unused-precedence-argument)
  - [9. Subobject classifier moved out of `Topos` in v4.33](#9-subobject-classifier-moved-out-of-topos-in-v433)
  - [10. `simp` leaves a `cast`'s proof argument unfolded](#10-simp-leaves-a-casts-proof-argument-unfolded)
  - [11. Conditional-rewrite lemmas renamed in v4.34](#11-conditional-rewrite-lemmas-renamed-in-v434)
  - [12. `Computability.Encoding` alphabet became a parameter](#12-computabilityencoding-alphabet-became-a-parameter)
  - [13. `unusedArguments` reports a constant function](#13-unusedarguments-reports-a-constant-function)
  - [14. Declaration reached upstream through a wider import closure](#14-declaration-reached-upstream-through-a-wider-import-closure)
  - [15. `Arrow.mk_eq_mk_iff` states its endpoints through `𝟭 C`](#15-arrowmk_eq_mk_iff-states-its-endpoints-through-%F0%9D%9F%AD-c)
  - [16. `isDefEq` transparency changed in v4.34](#16-isdefeq-transparency-changed-in-v434)
  - [17. `Mathlib.Logic.IsEmpty` moved under the `Mathlib.Basic` folder](#17-mathliblogicisempty-moved-under-the-mathlibbasic-folder)
  - [18. `List.sum_le_card_nsmul` renamed to `List.sum_le_length_nsmul`](#18-listsum_le_card_nsmul-renamed-to-listsum_le_length_nsmul)
  - [19. `ULift.ext` takes its two points implicitly](#19-uliftext-takes-its-two-points-implicitly)
  - [20. `set_option doc.verso true in` does not scope a module docstring](#20-set_option-docverso-true-in-does-not-scope-a-module-docstring)
  - [21. `Functor.Elements` refactored into structures](#21-functorelements-refactored-into-structures)
- [Updating the patch for a new upstream](#updating-the-patch-for-a-new-upstream)
  - [The no-op condition](#the-no-op-condition)
- [Module exclusion](#module-exclusion)
  - [Mechanism](#mechanism)
  - [Current exclusions](#current-exclusions)
- [Tooling notes](#tooling-notes)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

These notes catalogue the categories of change in
`scripts/geb-mathlib-backport.patch`, which adapts the vendored
`geb-mathlib` `Geb` source (mathlib `v4.35.0-rc2`) to compile under this
repository's `v4.29.0-rc6`. When a refresh fails, check whether the new
failure matches a category below (extend the corresponding hunk) or is
genuinely new (decide the adaptation, add a category here).

## Categories

### 1. `GebMeta` not vendored

- Upstream cause: `GebMeta` is a separate library, not vendored (its
  `@[env_linter]` would mis-audit `geb-lean`). The `Geb` index imports
  it, and each literate module (upstream `docs/rules/lean-coding.md`
  § Literate modules) carries `meta import GebMeta` for the `{cite}`
  docstring role it defines, writing its docstrings as Verso markup
  under `set_option doc.verso true`.
- v4.29 symptom: `unknown module prefix 'GebMeta'` building the `Geb`
  index or a literate module. The pinned toolchain accepts `doc.verso`
  and the `{name}`, `{lit}`, and `{option}` roles; only `{cite}` is
  unknown to it, and a bare `[Key]` under `doc.verso` is a link-syntax
  error. A `{name}` role naming a `GebMeta` declaration, as
  `Prototypes/LargeIR/Grothendieck.lean`'s module docstring does with
  `GebMeta.classicalAllowedModules`, reports `Unknown constant`: the
  role resolves the constant it names, and the constant is absent.
- Adaptation: `scripts/refresh-geb-mathlib.sh` deletes every import of
  `GebMeta`, in any of the module system's four import forms; rewrites
  each ``{cite}`Key` `` span to `\[Key\]`, the `doc.verso` spelling of
  mathlib's bare `[Key]` citation form (the conversion upstream's
  `scripts/extract-pr.sh` applies at extraction); and rewrites each
  ``{name}`GebMeta.Decl` `` span to ``{lit}`GebMeta.Decl` ``, which
  renders the same text without resolving it. The pass
  runs after `git apply`, as module exclusion does, so no patch hunk is
  involved and a newly-ingested literate module needs no patch
  extension. `PROVENANCE.md` records the pass.

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
  `IR.toSlicePFunctorDelta`, and `IR.toSlicePFunctorAlg`. The affected
  declarations in `IndRec/W.lean` are `IR.PosToSliceSig`,
  `IR.posToSliceIota`, `IR.posToSliceSigma`, `IR.posToSliceDelta`,
  `IR.PosSlice`, `IR.posSliceIota`, `IR.posSliceSigma`,
  `IR.posSliceDelta`, `IR.posSliceAlg`, `IR.posSlice`,
  `IR.posSlice_interp`, `IR.posSlice_spf`, `IR.W`, `IR.wDecode`,
  `IR.wObj`, `IR.W.mk`, and `IR.wDecode_mk`; those in
  `IndRec/Indexed.lean` are `IIR.Shape`, `IIR.Direction`,
  `IIR.pFunctor`, `IIR.Obj`, `IIR.Alg`, `IIR.Alg.toHom`, the top-level
  `IIR`, `IIR.FamSlice`, `IIR.interpAlg`, `IIR.interp`, `IIR.toIRAlg`,
  `IIR.toIR`, `IIR.W`, and `IIR.wDecode`.
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
  `'ConcreteCategory.hom_ofHom'` / `'TypeCat.Fun.toFun_apply'` /
  `'TypeCat.ofHom'`, or
  `Unknown constant 'CategoryTheory.NatTrans.naturality_apply'`, or
  `cannot coerce to function` on an explicit `⇑` applied to a
  `Type`-category morphism, followed by cascading type mismatches in
  each declaration mentioning the one that failed.
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
- Adaptation in `Prototypes/PresheafIRProto/Basic.lean`
  (`postcompArityHom`): the arity-hom naturality proof closes with
  `simp only [← ConcreteCategory.comp_apply]; rw [ν.naturality f.op]`.
  Replace both tactics with
  `exact FunctorToTypes.naturality _ _ ν f.op _`, as in
  `Presheaf/Basic.lean` above.
- Adaptation in `Prototypes/PresheafIRProto/Codes.lean`
  (`BaseArity.reindexHom`): the naturality proof strips the coercion
  layers with
  `simp only [TypeCat.Fun.toFun_apply, comp_apply, ConcreteCategory.hom_ofHom]`
  before `exact congrFun (hP.reindex_naturality g f.unop).symm d`.
  Delete the `simp only` line; in v4.29 the goal is already the
  function equation the `exact` closes.
- Adaptation in `Prototypes/PresheafIRProto/Functor.lean`
  (`arityHomEquivNatTrans`): the backward direction re-states
  naturality with `NatTrans.naturality_apply α f.op b`. Replace it
  with `FunctorToTypes.naturality _ _ α f.op b`.
- Adaptation in `CategoryTheory/DiscreteFibration/FiberPresheaf.lean`:
  `fiberPresheaf` wraps its `map` field in `TypeCat.ofHom` and proves
  the two functor laws by `ConcreteCategory.hom_ext _ _`. Drop the
  wrapper and replace `ConcreteCategory.hom_ext _ _` with `funext`; the
  two laws then read `funext fun c => D.restrict_id c` and
  `funext fun c => D.restrict_comp g'.unop g.unop c`. In the same
  module, `fiberPresheafEquiv` reads a functor's identity law through
  `ConcreteCategory.congr_hom (F.map_id _)`; replace that with
  `congrFun (F.map_id _)` at both occurrences.
- Adaptation in `CategoryTheory/DiscreteFibration/Packaged.lean`
  (`fiberPresheafIso`): the naturality component is
  `ConcreteCategory.hom_ext _ _ fun x => by ...`. Replace
  `ConcreteCategory.hom_ext _ _` with `funext`.
- Adaptation in `Prototypes/LargeIR/Basic.lean` (`ofSliceHom`) and
  `Prototypes/LargeIR/Morphism.lean` (`arrowHom`): the naturality
  square's nontrivial case is closed by
  `congrArg TypeCat.ofHom hh.symm` (respectively `w.symm`), transporting
  the function equation across the coercion layer. Drop the
  `congrArg TypeCat.ofHom`; in v4.29 the equation of morphisms is the
  function equation.
- Adaptation in `Prototypes/LargeIR/Grothendieck.lean`: `famFib` passes
  the index map to `Pi.comap` as `⇑h.unop`, and `homGrEquiv` reads a
  morphism's components back as `⇑(CoGrothendieck.homBase f)` and
  `⇑(CoGrothendieck.homFiber f u)`. Drop the three `⇑` coercions; in
  v4.29 each morphism is the function.
- Adaptation in `Mathlib/Data/PFunctor/Presheaf/WalkingArrow.lean`
  (`baseNode`): the compatibility proof closes with
  `exact (Z.map_id_apply _ _).symm` on a presheaf
  `Z : (Fin 2)ᵒᵖ ⥤ Type uZ`, reported as
  `` Invalid field `map_id_apply` ``. Replace it with
  `exact (FunctorToTypes.map_id_apply Z _).symm`, the `Type`-valued
  identity-law lemma whose statement is the goal.
- Adaptation in `Prototypes/Typechecker.lean` (`interpretation`,
  `interpretation_faithful`): the functor's `map` field wraps the
  restriction in `TypeCat.ofHom`, and faithfulness reads the two
  morphisms back as functions through
  `congrArg (fun k : Fiber X ⟶ Fiber Y ↦ (k : Fiber X → Fiber Y))`.
  Drop the wrapper and pass the hypothesis to `Hom.ext` directly; in
  v4.29 the morphism is the function.

### 4. Eliminator motive or functional argument left as an unreduced beta-redex

- Upstream cause: a proof applies a dependent eliminator with an
  explicit `motive`, or a uniqueness principle at an explicit
  functional argument, and enters the minor premise via
  `fun ... => by ...`. The affected sites are `elimData_valid` in
  `Slice/W.lean` and `wValidBool_eq_true_iff` in `Slice/Decidable.lean`
  (both `WType.rec`), `isHereditarilyNaturalBoolCore_eq_true_iff` in
  `Presheaf/Decidable.lean` (`SlicePFunctor.W.induction`),
  `ofRose_toRose` in `Prototypes/ConcreteSyntax.lean` (`Ast.ind`),
  `length_spell` in `Data/Tree/Ranked/Preorder.lean`,
  `length_fold_le_of_growth` in
  `Prototypes/Computability/CobhamFoldProto/Variable.lean`, and
  `dropEntry_algPara` in
  `Prototypes/Computability/CobhamFoldProto/Destruct.lean` (all three
  `RankedAlphabet.Term.induction`),
  `scanFinal_replicate_false` in
  `Prototypes/Computability/CobhamFoldProto/Layout.lean` (`Nat.rec`),
  `length_lengths` and `sum_lengths` in
  `Prototypes/Computability/BitTree/Elias/Tree.lean` (`tree_ind`, at an
  explicit `P`), `length_stepEnv_le` in
  `Prototypes/Computability/SizeBounded/Basic.lean` (`Fin.addCases`),
  and `Term.fold_map` in
  `Prototypes/Computability/CobhamFoldProto/Fold.lean`, where the
  unreduced application is not a motive but the carrier map
  `fun t ↦ e (Term.fold R alg t)` supplied to `Term.fold_unique`. Two
  sites in `Prototypes/Computability/SizeBounded/Cost.lean` are of the
  latter kind: `time_evalValueC` passes a value family
  `fun l ↦ (evalSRNC ...).value` to `length_stepEnv_le`, and
  `isPolyBounded_timePoly` passes `p := fun m ↦ (m + 1) + (m + 1)` to
  `isPolyBounded_of_le`; in each the bound obligation on the
  applied lambda is discharged by `omega`, which treats the
  unreduced application and its reduct as distinct atoms.
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
- Second site: `Prototypes/PresheafIRProto/Codes.lean`'s
  `isFunctorial_pullback` closes its `reindex_id` field with a `rw`
  whose residual goal is `cast ⋯ d = cast ⋯ d`. The two transport
  proofs are definitionally equal by proof irrelevance but not
  reducibly so. Append `rfl` after the `rw`.

### 8. Derived `Repr` instances carry an unused precedence argument

- Upstream cause: `FinSetSkel/Basic.lean` declares the objects with
  `deriving DecidableEq, Repr`, `Prototypes/ConcreteSyntax.lean`
  declares `Ann` with `deriving Repr, DecidableEq, Inhabited`,
  `Prototypes/Computability/SizeBounded/Cost.lean` declares `Account`
  with `deriving DecidableEq, Repr`, and
  `Prototypes/Computability/SizeBounded/Logspace/Rep.lean` declares
  `Rep` with `deriving DecidableEq, Repr, Inhabited`.
- v4.29 symptom: the `unusedArguments` env-linter reports
  `instReprFinSetSkel.repr argument 2 prec✝ : ℕ` (respectively
  `instReprAnn.repr argument 2 prec✝ : ℕ`,
  `instReprAccount.repr argument 2 prec✝ : ℕ`, and
  `instReprRep.repr argument 2 prec✝ : ℕ`) under `lake lint`; v4.29's
  `Repr` deriving handler emits a `repr` that ignores the precedence
  argument for a structure whose representation needs no
  parenthesisation.
- Adaptation: suppress the linter on the generated declaration,
  `attribute [nolint unusedArguments] instReprFinSetSkel.repr`
  (respectively `attribute [nolint unusedArguments] instReprAnn.repr`
  and `attribute [nolint unusedArguments] instReprAccount.repr`),
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

- Upstream cause: `Prototypes/PresheafIRProto/Codes.lean`'s
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

### 11. Conditional-rewrite lemmas renamed in v4.34

- Upstream cause: Lean core `Init/Core.lean` renames `if_pos` to
  `ite_eq_left`, `if_neg` to `ite_eq_right`, `dif_pos` to
  `dite_eq_left`, and `dif_neg` to `dite_eq_right` as of
  `v4.34.0-rc1`, deprecating the four old names (`since := "2026-07-21"`).
  The statements are unchanged; only the names move, to read off which
  branch the conditional collapses to, as the pre-existing
  `ite_eq_left_iff` / `dite_eq_right_iff` family already did. Upstream
  `geb-mathlib` sets `weak.warningAsError = true`, so it cannot keep the
  deprecated names.
- v4.29 symptom: ``Unknown identifier `ite_eq_right` `` (and the three
  others), followed by `unsolved goals` wherever the failed `rw` left
  the goal standing. The affected modules are `Prototypes/CanonicalSExpr.lean`,
  `Prototypes/ConcreteSyntax.lean`, `Prototypes/LargeIR/General.lean`,
  `Prototypes/ReadableSExpr.lean`, `CategoryTheory/FinCat/Basic.lean`,
  `CategoryTheory/FinCat/Hom.lean`,
  `Computability/BellantoniCook/Tree.lean`,
  `Computability/Cobham/RankedTree.lean`,
  `Computability/Cobham/Tree.lean`, `Data/Tree/Ranked/Code.lean`,
  `Data/Tree/Ranked/Preorder.lean`, `Data/W/Basic.lean`,
  `Prototypes/Computability/BitTree/Encoding.lean`,
  `Prototypes/Computability/Mazzanti/Derived.lean`,
  `Prototypes/Computability/Mazzanti/Diagonal.lean`,
  `Prototypes/Computability/SizeBounded/Logspace/Rep.lean`, and, under
  `Prototypes/Computability/CobhamFoldProto/`, `Degenerate.lean`,
  `Destruct.lean`, `Fold.lean`, `Layout.lean`, `SelfDelim.lean`,
  `SmashFree.lean`, and `Variable.lean`. Only a few of them appear in
  any one build log: lake does not attempt a module whose imports
  failed.
- Adaptation: substitute the v4.29 names throughout the vendored tree.
  The adaptation is mechanical, so re-applying it to a fresh upstream
  source is a re-run rather than a hunk-by-hunk re-anchoring:

  ```sh
  grep -rlZ '\bd\?ite_eq_\(left\|right\)\b' vendor/geb-mathlib | xargs -0 sed -i \
    -e 's/\bdite_eq_left\b/dif_pos/g'  -e 's/\bdite_eq_right\b/dif_neg/g' \
    -e 's/\bite_eq_left\b/if_pos/g'    -e 's/\bite_eq_right\b/if_neg/g'
  ```

  The word boundaries keep the `…_iff` lemmas of the same stem
  untouched; substituting the `dite` forms first keeps the `ite` forms
  from matching inside them.

### 12. `Computability.Encoding` alphabet became a parameter

- Upstream cause: `Data/Tree/Ranked/Preorder.lean`'s
  `RankedAlphabet.encoding` builds a `Computability.Encoding R.Term Bool`.
  Mathlib has since moved the alphabet `Γ` out of `Encoding`'s fields and
  into a second type parameter.
- v4.29 symptom: `Function expected at Computability.Encoding R.Term`,
  the structure taking one parameter there, with a `declaration uses ⋯`
  on the downstream `spell_injective` as a cascade.
- Adaptation: drop the second argument and supply the alphabet as the
  structure instance's first field, `Γ := Bool`. The remaining three
  fields and `Encoding.encode_injective` are unchanged between the two
  versions.
- Prose adaptation: the declaration docstring reads "as a
  `Computability.Encoding`, whose three fields they are". Under v4.29 the
  structure has a fourth field, so reword to "as a
  `Computability.Encoding` over the alphabet `Bool`, whose remaining
  three fields they are".

### 13. `unusedArguments` reports a constant function

- Upstream cause:
  `Prototypes/Computability/CobhamFoldProto/Degenerate.lean` defines the
  terminal carrier's encoding, decoding, and algebra — `encUnit`,
  `decUnit`, and `algUnit` — as constant functions, each ignoring an
  argument its type obliges it to take. Constant functions of the same
  kind are `oneFam` and `counterFam` in
  `Prototypes/FinCardUniverse/Value.lean`, `jUnitBool` and `pUnit` in
  `Prototypes/ParanaturalRank.lean`, `univR` in
  `Prototypes/PresheafIRUniv/Basic.lean`, and `treeStep` in
  `Prototypes/Computability/SizeBounded/BitTree.lean`.
- v4.29 symptom: under `lake lint -- Geb`, the `unusedArguments`
  env-linter reports `Geb.CobhamFold.encUnit argument 1`,
  `Geb.CobhamFold.decUnit argument 1`,
  `Geb.CobhamFold.algUnit argument 3`, and the corresponding report for
  each of the other six. The declarations are unchanged from upstream;
  the report is v4.29's linter.
- Adaptation: insert `@[nolint unusedArguments]` between each
  declaration's docstring and its `def` keyword, as category 2 does for
  `checkUnivs`; `treeStep` already carries `@[expose]`, which the
  suppression joins as `@[expose, nolint unusedArguments]`.
  `Prototypes/ParanaturalRank.lean` imports nothing, so
  the attribute is out of scope there: add
  `public import Batteries.Tactic.Lint` to its import block. The
  umbrella is needed rather than `Batteries.Tactic.Lint.Basic`, which
  declares the attribute: the attribute checks that the linter it names
  exists, and `unusedArguments` is declared in
  `Batteries.Tactic.Lint.Misc`.

### 14. Declaration reached upstream through a wider import closure

- Upstream cause:
  `CategoryTheory/DiscreteFibration/Basic.lean` uses
  `Sigma.mk.inj_iff` without importing `Mathlib.Data.Sigma.Basic`,
  reaching it through the transitive closure of its
  `Mathlib.CategoryTheory` imports.
- v4.29 symptom: `` Unknown constant `Sigma.mk.inj_iff` ``, followed by
  `` Tactic `rcases` failed: `x✝ : ?m…` is not an inductive datatype ``
  wherever the failed term stands as an `obtain` scrutinee. The
  declaration itself is present in v4.29 under the same name, in
  `Mathlib/Data/Sigma/Basic.lean`; only the import closure differs.
- Adaptation: add `public import Mathlib.Data.Sigma.Basic` to the
  module's import block, in alphabetical position.

### 15. `Arrow.mk_eq_mk_iff` states its endpoints through `𝟭 C`

- Upstream cause:
  `CategoryTheory/DiscreteFibration/Packaged.lean`'s
  `IsDiscreteFibration.toDiscreteFibration` obtains a hypothesis
  `hf : p.map q.hom = eqToHom hX ≫ g ≫ eqToHom hY.symm`, where
  `q := H.equiv.symm ⟨(Arrow.mk g, c), rfl⟩`,
  from `Arrow.mk_eq_mk_iff` and discharges the `map_hom` field with
  `simp only [Functor.map_comp, eqToHom_map, hf]` followed by `simp`.
- v4.29 symptom: `This simp argument is unused: hf`, then
  `unsolved goals`; `rw [hf]` reports that its pattern, which prints
  identically to a subterm of the goal, does not occur there. An
  `Arrow C` is a `Comma (𝟭 C) (𝟭 C)`, so `hf`'s endpoints are
  `p.obj ((𝟭 C).obj …)` — visible in the types of `hX` and `hY` — while
  the goal's are `p.obj …`; the two `p.map` applications differ in their
  implicit endpoint arguments.
- Adaptation: normalise the hypothesis and the goal first, prepending
  `simp only [Functor.id_obj] at hf ⊢` to the existing `simp only`.

### 16. `isDefEq` transparency changed in v4.34

- Upstream cause: Lean core narrowed the backward-compatibility option
  `backward.isDefEq.respectTransparency` to
  `backward.isDefEq.respectTransparency.types`, and the underlying
  `isDefEq` change that the option compensates for also makes several
  unifications in `CategoryTheory/Grothendieck/Functor/From.lean`
  succeed under `v4.34.0-rc2` that do not under v4.29. Upstream sets
  the option on `Grothendieck.functorFromData` (in its `.types`
  spelling) and on `Grothendieck.ofFunctorFrom` (in the unnarrowed
  spelling, which both versions accept).
- v4.29 symptom:
  `` Unknown option `backward.isDefEq.respectTransparency.types` `` on
  the `set_option` line, repeated once per syntax linter as
  `linter ... failed: Unknown option ...`; the declaration the option
  guards then elaborates with metavariables, and every later
  declaration mentioning it cascades into `(kernel) application type
  mismatch`, `(kernel) declaration has metavariables`, and
  `` Unknown constant `_inhabitedExprDummy` ``.
- Adaptation, option name: substitute the v4.29 spelling throughout the
  vendored tree. The adaptation is mechanical, so re-applying it to a
  fresh upstream source is a re-run rather than a hunk-by-hunk
  re-anchoring:

  ```sh
  grep -rlZ 'backward\.isDefEq\.respectTransparency\.types' vendor/geb-mathlib \
    | xargs -0 sed -i \
        's/backward\.isDefEq\.respectTransparency\.types/backward.isDefEq.respectTransparency/g'
  ```

- Adaptation, further declarations needing the option: under v4.29 the
  stricter `isDefEq` also blocks rewrites for which upstream needs no
  option. In `Grothendieck.natTransFrom`'s `naturality` field the
  `(nat.fibNat Y.base).naturality f.fiber` argument of the `simp only`
  fails to fire (reported as `This simp argument is unused`), leaving
  the following `rw [..., h, ...]` without its pattern; in
  `Grothendieck.NatTransFromData.comp`'s `coherence` field the opening
  `rw [← Category.assoc, ...]` reports that `?f ≫ ?g ≫ ?h` does not
  occur in a target that visibly contains it. Prepend
  `set_option backward.isDefEq.respectTransparency false in` to each of
  the two declarations, leaving the proofs as upstream writes them.
  Setting the option for the whole module instead is not equivalent: it
  makes the `simp only` in `Grothendieck.functorFromDataToFunctorCat`'s
  `map_comp` field close its goal, so the `rfl` after it reports
  `No goals to be solved`.
- Adaptation, closing `rfl`: two proofs in the module end one
  definitional step short under v4.29, as in category 7.
  `Functor.leftOpEquiv`'s `functor_unitIso_comp` field is left with
  `((𝟙 x).unop.app _).unop = 𝟙 _` after its `simp`, and
  `CoGrothendieck.FunctorFromData.mk`'s `hom_id` field with
  `eqToHom ⋯ = eqToHom ⋯` after its `erw [eqToHom_app]`. Append `rfl`
  to each, which runs at default transparency.

### 17. `Mathlib.Logic.IsEmpty` moved under the `Mathlib.Basic` folder

- Upstream cause: mathlib pull request 39703 (2026-08-26) creates a
  `Basic` top-level folder and moves `Mathlib/Logic/IsEmpty/Defs.lean`
  to `Mathlib/Basic/IsEmpty/Defs.lean`. The declarations are unchanged;
  only the module path moves.
  `Prototypes/Computability/BitTree/Scanner.lean` imports the new path.
- v4.29 symptom: `unknown module prefix 'Mathlib.Basic'`: the pinned
  mathlib has no `Mathlib/Basic/` directory, and the module is
  `Mathlib.Logic.IsEmpty.Defs` there (split from `Mathlib.Logic.IsEmpty`
  in mathlib pull request 35137).
- Adaptation: rewrite the import to `Mathlib.Logic.IsEmpty.Defs`.

### 18. `List.sum_le_card_nsmul` renamed to `List.sum_le_length_nsmul`

- Upstream cause: mathlib pull request 43155 (2026-08-27) renames the
  `card` in lemma names about `List.length` to `length`;
  `List.prod_le_pow_card` and its additive companion
  `List.sum_le_card_nsmul` become `List.prod_le_pow_length` and
  `List.sum_le_length_nsmul`. The statements are unchanged.
  `Prototypes/Computability/SizeBounded/Iteration.lean`
  (`srnStorage_le`) uses the additive lemma.
- v4.29 symptom: ``Unknown constant `List.sum_le_length_nsmul` ``,
  followed by `unsolved goals`.
- Adaptation: substitute `List.sum_le_card_nsmul`.

### 19. `ULift.ext` takes its two points implicitly

- Upstream cause: Lean core pull request 15062 (2026-09-08, in
  `v4.35.0-rc1`) adds `ext` theorems for `ULift`, `PULift`, `PLift`,
  and `MProd`, with the two points implicit, superseding mathlib's
  `ULift.ext (x y : ULift α) (h : x.down = y.down)` of
  `Mathlib/Data/ULift.lean`. Upstream's `subsingleton_arityB` in
  `Prototypes/PresheafIRProto/Basic.lean` passes the proof as the
  first explicit argument.
- v4.29 symptom: `Application type mismatch` at the proof argument,
  expected to have type `ULift ?m`, followed by an `omega` failure
  on the goal that the mismatch leaves with metavariables.
- Adaptation: pass the two points as placeholders, `ULift.ext _ _`.

### 20. `set_option doc.verso true in` does not scope a module docstring

- Upstream cause: the modules under `Prototypes/LargeIR/` with
  several `/-! ... -/` sections (`Basic`, `Code`, `General`,
  `Grothendieck`, `Morphism`, `Product`) write the leading module
  docstring under `set_option doc.verso true in` and set the option
  globally only after it, since the upstream commit that bumped
  mathlib to `v4.34.0`. Under `v4.34` the `in` form applies the
  option to the module docstring that follows it.
- v4.29 symptom: `Can't add Verso-format module docs because there is
  already Markdown-format content present`, reported at the first
  later `/-! ... -/` section: under `v4.29` the `in` form leaves the
  leading module docstring in Markdown format, and the later sections,
  under the global option, are Verso-format, and a module's docs are
  all of one format. A module with only the leading docstring, such as
  `Prototypes/LargeIR/Binder.lean` or the `Prototypes/Computability/Triage/`
  modules, is unaffected.
- Adaptation: set the option globally before the leading module
  docstring and delete the later global `set_option`, the form these
  modules had before the bump.

### 21. `Functor.Elements` refactored into structures

- Upstream cause: mathlib pull request 43228 (2026-09-03) makes
  `Functor.Elements` a structure with fields `obj` and `val` (from the
  sigma type `Σ c, F.obj c`), makes its morphisms a structure with
  fields `hom` and `map_val` (from a subtype of the base morphisms),
  and moves the constructor and extensionality lemma to
  `Functor.Elements.homMk` (with implicit endpoints) and
  `Functor.Elements.hom_ext` (from `CategoryOfElements.homMk` with
  explicit endpoints and `Subtype.ext`).
  `CategoryTheory/DiscreteFibration/Elements.lean` reads and builds
  elements and their morphisms through these names.
- v4.29 symptom: ``Invalid field `obj` `` / `` `val` `` /
  `` `hom` `` / `` `map_val` `` on `Sigma` and `Subtype` values,
  ``Unknown constant `CategoryTheory.Functor.Elements.homMk` `` and
  `` `hom_ext` ``, followed by cascading `Not a definitional equality`
  and `Type mismatch` errors in every `rfl` proof about them.
- Adaptation: read the sigma and subtype projections (`.1`, `.2`),
  build an element as the anonymous constructor `⟨op b, x⟩`, and use
  `CategoryOfElements.homMk (Opposite.unop y) (Opposite.unop x)` and
  `Subtype.ext`; the seven sites are the module's `base`, `elt`, `mk`,
  `homBase`, `map_homBase_elt`, `homMk`, and `hom_ext`.

## Updating the patch for a new upstream

The vendored tree is a pure function of three committed inputs: the
upstream `geb-mathlib` commit, this patch, and the exclusion list in
`scripts/refresh-geb-mathlib.sh` (see [Module exclusion](#module-exclusion)).
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
   by hand. An upstream module rename leaves the hunks themselves
   valid: rewrite the old path to the new one throughout the patch
   before re-applying, and rename the module in the exclusion list and
   in the category descriptions above.
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
consuming exploration is deferred. The same applies to a dependency on
`Cslib`, pinned alongside mathlib at `v4.29.0-rc6`.

A reference to an unknown module does not necessarily require a module to be
excluded: a  declaration that moved between modules or namespaces is a rename,
and category 9 is the worked case. Before excluding a module, locate each
name it needs in the v4.29 tree and compare signatures.

### Mechanism

`EXCLUDED_MODULES` in `scripts/refresh-geb-mathlib.sh` names modules in
Lean dotted form. For each entry the script removes the module's own
file and its submodule directory, then deletes every `import` of the
entry or of one of its submodules from the surviving files, so that no
bad import remains. The removal runs after `git apply`, so each patch
hunk still anchors against the pristine upstream text it was generated
from. `PROVENANCE.md` records the list, the vendored tree being a
function of it as well as of the upstream commit and the patch.

An entry names the narrowest module carrying the unavailable
dependency rather than an ancestor namespace: a sibling added upstream
under an excluded ancestor would be dropped without a signal, whereas
under a retained ancestor it is ingested and any incompatibility of its
own surfaces in the refresh workflow's build.

A module importing an excluded module is excluded in turn: the import
deletion would otherwise leave it referring to declarations it no
longer imports. The exception is a directory's index module, which
carries nothing but imports and survives the deletion of one of them;
`Geb.Prototypes.Computability` is one, retaining its remaining imports
after its `TreeScanner` import is deleted.

### Current exclusions

- `Geb.Prototypes.Computability.TreeScanner` (and its `Machine`, `Steps`,
  and `Bound` submodules) imports
  `Cslib.Computability.Machines.Turing.MultiTape.Deterministic` and
  `Cslib.Computability.Machines.Turing.MultiTape.TapeLemmas`, and uses
  the `Turing.MultiTapeTM` namespace those modules introduce. Neither
  module exists at the pinned cslib revision `9a159ac`
  (`v4.29.0-rc6`), whose only Turing-machine material is
  `Cslib.Computability.Machines.SingleTapeTuring.Basic`.
  `git log --follow --name-status` over cslib records both as additions —
  `MultiTape/Deterministic.lean` in cslib PR #384 and
  `MultiTape/TapeLemmas.lean` in cslib PR #768 — not as renames of
  anything present at the pin, and the pinned tree contains no
  occurrence of `MultiTape`. Lifting the exclusion requires advancing
  the cslib pin, which the mathlib and toolchain pins govern.
- Under `Geb.Prototypes.Computability.BitTree`, the modules `Bound`,
  `Machine`, `Steps`, `BinaryMachine.Bound`, `BinaryMachine.Machine`,
  `Elias.Bound`, `Elias.Machine`, and `EliasBinary.Bound`, and
  `Geb.Prototypes.Computability.BitTreeScanner.Machine`, import the
  same two `MultiTape` modules.
- `Geb.Prototypes.Computability.BitTreeScanner.Encoding` imports
  `Cslib.Foundations.Data.PFunctor.Free` and instantiates the
  `PFunctor.FreeM` it defines, at a `PFunctor` shape, through
  `PFunctor.FreeM.rec` and `PFunctor.FreeM.liftM`. cslib's history
  records `PFunctor/Free.lean` as an addition in cslib PR #477
  (2026-06-12); the pinned revision `9a159ac` (2026-03-12) has no
  `Cslib/Foundations/Data/PFunctor/` directory. The `Cslib.FreeM` of
  the pinned `Cslib/Foundations/Control/Monad/Free.lean` (cslib PR
  #53) is a different structure, the free monad over an arbitrary
  `F : Type u → Type v` whose `liftBind` constructor takes an
  operation `op : F ι`, where `PFunctor.FreeM.liftBind` takes a shape
  `a : P.A` and a continuation on `P.B a`; it is not a rename.
- The modules importing one of the above, directly or through a chain
  of such imports, are excluded with them: the rest of
  `BitTreeScanner`, excluded as a whole since every submodule is such
  an importer; and, under `BitTree`, the `BinaryMachine` submodules
  other than `Accounting` and `Difference`, every `Elias.Machine*`
  module together with `Elias.Execution`, the `EliasBinary` submodules
  other than `Account`, `Cost`, and `Need`, and `Mazzanti.BitTree`,
  `Mazzanti.Bound`, `Mazzanti.Growth`, and `Mazzanti.Words`. The index
  modules `BitTree`, `BitTree.BinaryMachine`, `BitTree.Elias`,
  `BitTree.EliasBinary`, and `Mazzanti` survive with those imports
  deleted. `PROVENANCE.md` lists every entry.
- `Geb.Prototypes.Computability.MultiTape.OutputString` and
  `Geb.Prototypes.Computability.MultiTape.Rename`, and
  `Geb.Prototypes.Computability.SizeBounded.Machine.Exec`,
  `Geb.Prototypes.Computability.SizeBounded.Machine.Program`, and
  `Geb.Prototypes.Computability.SizeBounded.Machine.Register`, import
  `Cslib.Computability.Machines.Turing.MultiTape.Configuration`,
  `Cslib.Computability.Machines.Turing.MultiTape.Deterministic`, or
  `Cslib.Computability.Machines.Turing.MultiTape.TapeLemmas`, and
  `Geb.Prototypes.Computability.SizeBounded.WordMachine` imports the
  excluded `TreeScanner.Machine`. `MultiTape` is excluded as a whole,
  every submodule being such an importer. Every module under
  `SizeBounded.Machine` imports `Register`, `Program`, or `Exec`,
  directly or through a chain, so `SizeBounded.Machine` is excluded as
  a whole; likewise every module under `SizeBounded.Logspace.Machine`
  imports a `SizeBounded.Machine` module, so it too is excluded as a
  whole. `SizeBounded.MachineBound` imports `WordMachine`, and
  `Kristiansen.MachineBound` imports `SizeBounded.Machine.Main`; both
  are excluded. The index modules `SizeBounded`, `SizeBounded.Logspace`,
  and `Kristiansen` survive with those imports deleted.

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
