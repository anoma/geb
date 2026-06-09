# Subobject classifier for `Type u` via `Prop` — design

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [1 Scope and goal](#1-scope-and-goal)
- [2 Sources and provenance](#2-sources-and-provenance)
- [3 Background: obstruction and resolution](#3-background-obstruction-and-resolution)
- [4 File layout](#4-file-layout)
- [5 Public API surface](#5-public-api-surface)
  - [5.1 Core construction](#51-core-construction)
  - [5.2 Comparison with the presheaf classifier](#52-comparison-with-the-presheaf-classifier)
  - [5.3 Naming rationale](#53-naming-rationale)
- [6 Proof shapes](#6-proof-shapes)
- [7 Axiom budget](#7-axiom-budget)
- [8 Test plan](#8-test-plan)
- [9 Scope guardrails](#9-scope-guardrails)
- [10 Implementation operational notes](#10-implementation-operational-notes)
- [11 Adversarial-review punch list](#11-adversarial-review-punch-list)
- [12 References](#12-references)

<!-- END doctoc -->

## 1 Scope and goal

Construct a subobject classifier for the category `Type u`, in
the sense of mathlib's `CategoryTheory.Classifier`, with
classifying object `ULift.{u} Prop`, and prove the full
universal property (pullback square and uniqueness of the
classifying map). Provide `Classifier (Type u)` and an
`instance : HasClassifier (Type u)`.

Additionally, relate the new classifier to this repository's
presheaf classifier (`pshClassifierData` in
`GebLean/Utilities/Presheaf.lean`): specialized to presheaves
over the terminal category, the presheaf classifying object
evaluates at the unique point to a type equivalent to
`ULift.{u} Prop`, compatibly with the truth morphisms.

This work transcribes the mathematical content of the
subobject-classifier construction in
`geb-idris/src/Library/IdrisCategories.idr` (lines 1244–1320),
which follows the Homotopy Type Theory book's description of
the type of mere propositions as a classifying object
([UF13] §10.1.4, Theorem 10.1.12). The Lean version replaces
the type of mere propositions, which cannot satisfy the
universal property in Lean (§3), with Lean's `Prop`.

## 2 Sources and provenance

| Item | Status | Source |
| --- | --- | --- |
| Classifying object `Ω = ULift Prop` | Transcription | [UF13] Thm 10.1.12 (`Ω : 𝒰` of all mere propositions); [MM92] §I.4 (classifier in `Set`); Lean `Prop` as the resized `Ω` |
| `typesCharMap` (image membership) | Transcription | [UF13] §10.1.4; `ChiForHProp` in `IdrisCategories.idr` |
| Truth morphism from terminal | Transcription | [MM92] §I.3–I.4; `TrueForHProp` in `IdrisCategories.idr` |
| Pullback-square proof | Transcription | [MM92] §I.4 elementary argument, via mathlib `Types.isPullback_iff` |
| Uniqueness of classifying map | Transcription | [MM92] §I.4; unattained in the Idris source (§3) |
| `Classifier (Type u)` packaging | Novel glue | mathlib `Classifier.mkOfTerminalΩ₀` |
| Comparison with `pshClassifierData` at the terminal category | Novel glue | This repository's `Presheaf.lean` |

Prior art: the Lean 3 project `b-mehta/topos`
(<https://github.com/b-mehta/topos>) defined the abstract
subobject-classifier structure (`subobject_classifier.lean`) and
a presheaf classifier (`applications/functor_category.lean`);
its source contains no classifier instance for `Type u` and no
use of `Prop` as a classifying object. mathlib's
`CategoryTheory.Topos.Classifier` ports the abstract structure.
As of the pinned mathlib revision, no mathlib or CSLib
declaration connects `Prop` (or any other object) to
`Classifier` for `Type u`; the construction here is new content
relative to both libraries. A `Classifier (Type u)` is in
principle derivable from this repository's `pshClassifierData`
via mathlib's `Classifier.ofEquivalence` along
`(Discrete PUnit)ᵒᵖ ⥤ Type u ≌ Type u`, but its classifying
object would be the image of the sieve functor under the
equivalence, not `ULift Prop`; the present construction's
contribution is `ULift Prop` as the classifying object, with
computable data and mathlib-only dependencies.

## 3 Background: obstruction and resolution

The Idris source defines the classifying object as the subtype
of types that are mere propositions
(`SubCFromHProp = Subset0 Type IsHProp`, where
`IsHProp a = (x, y : a) -> x = y`). It constructs the
characteristic map (`ChiForHProp`, sending `eb : b` to the
fiber of the mono over `eb`) and partial maps toward the
pullback square, then stops: the map from the mono's domain
into the pullback, and uniqueness of the characteristic map,
are absent.

The missing pieces require, for subsingleton types `α β`
that are equivalent, the type equality `α = β`. This is
univalence restricted to mere propositions; it is unprovable in
Idris's and Lean's type theories (for Idris, independence
follows from the set-theoretic and simplicial models; for Lean,
unprovability suffices for this design and is what the
set-theoretic model establishes), so the construction cannot be
completed for a subtype of `Type u` in either system. (Full
univalence for `Type u` is refutable in Lean, since Lean proves
unique identity proofs; univalence restricted to subsingletons
is merely unprovable.) Separately, [UF13] §10.1.4 notes that
`Σ (X : 𝒰), isProp(X)` is as large as `𝒰`, so it is not an
object of the category it would classify; Theorem 10.1.12
therefore *assumes* a small type `Ω : 𝒰` of all mere
propositions (propositional resizing).

Lean's `Prop` discharges both assumptions natively:

- Impredicativity: `∃ a : U, m a = x : Prop` for `U : Type u`
  at any `u`, so membership propositions land in `Prop`
  regardless of universe. This is propositional resizing.
- `propext`: equivalent propositions are equal. This is
  univalence restricted to `Prop`.

Hence `ULift.{u} Prop : Type u` (note `Prop : Type 0`) is an
object of `Type u` and satisfies the full universal property,
including the uniqueness clause unattainable for the subtype
formulation. The subtype of mere propositions is therefore not
transcribed; this design records its obstruction here in its
place.

## 4 File layout

| File | Change |
| --- | --- |
| `GebLean/Utilities/TypesClassifier.lean` | New module: core construction and comparison section |
| `GebLean/Utilities.lean` | Add `import GebLean.Utilities.TypesClassifier` |
| `GebLeanTests/Utilities/TypesClassifier.lean` | New test module (`example`-based) |
| `GebLeanTests.lean` | Add `import GebLeanTests.Utilities.TypesClassifier` |

The core construction depends only on mathlib. The comparison
section depends on `GebLean.Utilities.Presheaf` (for
`pshTerminal`, `pshSieveFunctor`, and `pshSieveTruth`); since
imports are per-module, the comparison lives in the same module
and the module imports both. If a later `geb-mathlib` port
extracts the core, the comparison section is not ported.

Estimated size: 120–180 lines core, 60–90 lines comparison,
20–40 lines tests.

## 5 Public API surface

All declarations live in namespace `GebLean`, universe
variable `u`.

### 5.1 Core construction

```lean
/-- `PUnit` is terminal in `Type u`. Computable variant of
mathlib's `noncomputable` `Limits.Types.isTerminalPUnit`. -/
def typesIsTerminalPUnit :
    Limits.IsTerminal (PUnit.{u + 1} : Type u) :=
  Limits.IsTerminal.ofUnique _

/-- The truth morphism: the point of `ULift Prop`
selecting `True`. -/
def typesTruth : PUnit.{u + 1} ⟶ ULift.{u} Prop :=
  fun _ => ULift.up True

/-- The characteristic map of a morphism `m : U ⟶ X` in
`Type u`: membership in the image of `m`. -/
def typesCharMap {U X : Type u} (m : U ⟶ X) :
    X ⟶ ULift.{u} Prop :=
  fun x => ULift.up (∃ a, m a = x)

theorem typesCharMap_apply_eq_true {U X : Type u} (m : U ⟶ X)
    (a : U) : typesCharMap m (m a) = ULift.up True

theorem typesCharMap_isPullback {U X : Type u} (m : U ⟶ X)
    [Mono m] :
    IsPullback m (typesIsTerminalPUnit.from U)
      (typesCharMap m) typesTruth

theorem typesCharMap_unique {U X : Type u} (m : U ⟶ X)
    [Mono m] (χ' : X ⟶ ULift.{u} Prop)
    (hχ' : IsPullback m (typesIsTerminalPUnit.from U)
      χ' typesTruth) :
    χ' = typesCharMap m

/-- `ULift Prop` is a subobject classifier for `Type u`. -/
def typesClassifier : Classifier (Type u)

instance typesHasClassifier : HasClassifier (Type u)
```

`typesCharMap` and `typesCharMap_apply_eq_true` do not require
`Mono m`; the hypothesis appears only where the universal
property needs it. `typesClassifier` is assembled with
`Classifier.mkOfTerminalΩ₀` from `typesIsTerminalPUnit`.
mathlib's `Limits.Types.isTerminalPUnit` (current name; the
lowercase `isTerminalPunit` is deprecated as of mathlib
2026-02-08) is `noncomputable` (it routes through the
choice-based `⊤_ (Type u)`), and `IsTerminal` is data consumed
by `mkOfTerminalΩ₀`'s `χ₀` field; using it would force
`noncomputable def typesClassifier`, violating the project
rule. `typesIsTerminalPUnit := IsTerminal.ofUnique _` is
computable, following the precedent of
`pshTerminalIsTerminal` in `Presheaf.lean`.

`mkOfTerminalΩ₀` derives `mono_truth` via
`IsTerminal.mono_from`, so no separate monomorphism lemma for
`typesTruth` is needed.

### 5.2 Comparison with the presheaf classifier

For `C := Discrete PUnit.{u + 1}` (so `C : Type u` with
`Category.{u} C`, and presheaves `Cᵒᵖ ⥤ Type (max u u)
= Type u`, matching the `Type (max u v)` universe pattern of
`pshSieveFunctor` and `pshClassifierData` in
`Presheaf.lean`):

```lean
/-- A sieve on an object of the terminal category is
determined by whether it contains the identity. -/
def sievePUnitEquiv (c : Discrete PUnit.{u + 1}) :
    Sieve c ≃ ULift.{u} Prop

theorem sievePUnitEquiv_truth
    (c : (Discrete PUnit.{u + 1})ᵒᵖ)
    (x : (pshTerminal (Discrete PUnit.{u + 1})).obj c) :
    sievePUnitEquiv c.unop
      ((pshSieveTruth (Discrete PUnit.{u + 1})).app c x) =
      typesTruth PUnit.unit
```

Forward direction of `sievePUnitEquiv`: membership of
`𝟙 c`. Inverse: the constant sieve. Both directions are
computable. `sievePUnitEquiv_truth` states that the presheaf
truth morphism (which selects the maximal sieve `⊤`)
corresponds to `typesTruth` under the equivalence.

The comparison stops at the pointed-object level. mathlib's
`Classifier.ofEquivalence` could transport `pshClassifierData`
across `(Discrete PUnit)ᵒᵖ ⥤ Type u ≌ Type u`, but the
transported classifying object is the equivalence-image of the
sieve functor, not `ULift Prop`, so the transport neither
replaces the direct construction nor adds to the pointwise
cross-check; see §9.

### 5.3 Naming rationale

- `typesCharMap` parallels the repository's
  `wClassifierCharMap`; the `types` prefix parallels mathlib's
  `Types.*` lemma family for the category of types and the
  repository's `pshSieveFunctor`/`pshSieveTruth` precedent.
- Theorem names follow mathlib conventions: conclusions named
  (`_isPullback`, `_unique`, `_apply_eq_true`); data in
  lowerCamelCase.
- The `Equiv` (rather than `Iso`) form of `sievePUnitEquiv`
  follows mathlib's preference for `Equiv` between types;
  `Equiv.toIso` recovers the categorical iso if needed.

## 6 Proof shapes

- `typesCharMap_apply_eq_true`: `propext` upgrades
  `(∃ a', m a' = m a) ↔ True` (witness `a`) to an equality;
  `congrArg ULift.up` finishes. No `Mono` needed.
- `typesCharMap_isPullback`: via `Types.isPullback_iff`
  (`Mathlib.CategoryTheory.Limits.Types.Pullbacks`), which
  reduces `IsPullback` in `Type u` to three elementwise
  clauses:
  1. Commutativity: pointwise `typesCharMap_apply_eq_true`
     plus `Subsingleton.elim` on the `PUnit` leg.
  2. Joint injectivity: `(mono_iff_injective m).mp`
     (`Mathlib.CategoryTheory.Types.Basic`).
  3. Existence: from `typesCharMap m x = typesTruth p`,
     project with `congrArg ULift.down` and rewrite with
     `eq_true_iff`-style lemmas to obtain `∃ a, m a = x`;
     `Exists.elim` (Prop-to-Prop, no choice) produces the
     witness; the `PUnit` component is `Subsingleton.elim`.
- `typesCharMap_unique`: `funext x`; `ULift.ext`; `propext`.
  Forward implication (`(χ' x).down → ∃ a, m a = x`):
  `Types.exists_of_isPullback` applied to `hχ'` at
  `(x, PUnit.unit)`, where `χ' x = typesTruth PUnit.unit`
  follows from `(χ' x).down` by `propext` and `ULift.ext`.
  Backward: from `m a` and the commutativity leg `hχ'.w`
  evaluated at `a`.
- `sievePUnitEquiv`: round trips by `Sieve.ext` (sieve side)
  and `ULift.ext` + `propext` (`Prop` side). The sieve-side
  step relating `S.arrows f` for arbitrary `f : Y ⟶ c` to
  `S.arrows (𝟙 c)` first needs `Y = c` (from
  `Subsingleton PUnit` and `Discrete.ext`; `f` and `𝟙 c`
  inhabit different hom-sets until then) and an
  `eqToHom`/`cases` transport, after which hom-subsingleton
  elimination or downward closure closes the goal. The
  transport is the expected cost center of this proof.
- `sievePUnitEquiv_truth`: reduces to
  `(⊤ : Sieve c).arrows (𝟙 c) = True`; `propext` and
  triviality of `⊤`.

If `Types.isPullback_iff` does not apply directly
(its mathlib proof uses `grind`; only the statement matters
here), the fallback is a direct `PullbackCone.IsLimit.mk`
construction; the elementwise content is identical.

## 7 Axiom budget

| Declaration | Expected axioms |
| --- | --- |
| `typesIsTerminalPUnit`, `typesTruth`, `typesCharMap` | none beyond definitional |
| `sievePUnitEquiv` (carries `Prop`-valued round-trip fields; `#print axioms` reports per declaration) | `propext`, possibly `Quot.sound` |
| Theorems and `typesClassifier`/instance | `propext`, `Quot.sound`, `Classical.choice` (proofs only, inherited from mathlib lemmas) |

No `noncomputable` anywhere: all data fields are explicit
closed terms; witness extraction from `∃` occurs only inside
`Prop`-valued goals (`IsPullback`, `uniq`), where
`Exists.elim` suffices. `Classical.choice` may nevertheless
enter through cited mathlib lemmas (for example, the `grind`
step inside `Types.isPullback_iff`); this is accepted under
the project axiom policy. `scripts/check-axioms.sh` gates the
result as usual.

## 8 Test plan

`GebLeanTests/Utilities/TypesClassifier.lean`, `example`-based
(no
`#guard` on `Prop`-valued data, per project policy):

- `typesCharMap` of a concrete mono (e.g. the subtype
  inclusion `(Subtype.val : {n : Nat // n % 2 = 0} → Nat)`)
  evaluates correctly on a member and a non-member, proven by
  `simp`/`decide`-free term proofs.
- `typesClassifier.Ω = ULift Prop` and
  `typesClassifier.truth = typesTruth` hold by `rfl`,
  confirming `mkOfTerminalΩ₀` did not obscure the data.
- `sievePUnitEquiv` round-trip `example`s on `⊤` and `⊥`.

## 9 Scope guardrails

Excluded from this work:

- Power objects (`PowerObjFromProp`/`PowObjType` in the Idris
  source): separable; add only when needed.
- The `SubCFromEq`, `SubCFromBoolPred`, and `SubCFromType`
  variants of `GebTopos.idr` (lines 2669–2888): exploratory
  antecedents, superseded by the present construction.
- Transcription of the subtype-of-mere-propositions
  classifier: unprovable universal property (§3); recorded as
  documentation only.
- Equivalence-transfer of `Classifier` across
  `PSh(1) ≌ Type u`: requires new general machinery; the
  pointed comparison of §5.2 delivers the intended
  cross-check.
- Topos-structure corollaries (cartesian closure, power
  objects, `IsTopos`-style packaging): out of scope.

## 10 Implementation operational notes

- Build with `lake build`/`lake test` only (never
  `lake env lean`).
- Pre-commit: `bash scripts/pre-commit.sh` for every commit
  touching `.lean`.
- Mathlib name verification at implementation time via
  `lean_local_search`/`lean_loogle` before first use of each
  cited lemma; names verified against the pinned revision at
  design time: `CategoryTheory.mono_iff_injective`
  (`Mathlib/CategoryTheory/Types/Basic.lean`),
  `Types.isPullback_iff`, `Types.exists_of_isPullback`
  (`Mathlib/CategoryTheory/Limits/Types/Pullbacks.lean`),
  `Classifier.mkOfTerminalΩ₀`, `Classifier.ofEquivalence`
  (`Mathlib/CategoryTheory/Topos/Classifier.lean`).
  `Limits.Types.isTerminalPUnit`
  (`Mathlib/CategoryTheory/Limits/Types/Products.lean`) is
  `noncomputable` and is referenced in §5.1 only as the name
  not used.
- Verify computability of every data-position dependency
  before use (`#print axioms` plus absence of `noncomputable`
  in the dependency's definition); §5.1's `typesIsTerminalPUnit`
  exists because the mathlib counterpart fails this check.
- Commit granularity: core construction and comparison
  section as separate commits; index-file and test wiring
  with their respective content commits.

## 11 Adversarial-review punch list

1. Mathlib upstream guides honoured (naming, docstrings,
   commit messages); re-fetch the guides each round.
2. Universe annotations correct (`PUnit.{u + 1}`,
   `ULift.{u} Prop`, `Discrete PUnit.{u + 1}`; comparison
   universes match `WClassifier`'s `Type (max u v)` pattern).
3. Mathlib API names exist at the pinned revision with the
   stated signatures.
4. Citations complete and accurate ([UF13] Thm 10.1.12 page
   447 first edition; [MM92] §I.3–I.4; Idris source line
   ranges).
5. Axiom budget table consistent with the constructive-only
   rule (no `noncomputable`; `Classical.choice` proofs-only).
   In particular: every declaration consumed in a data
   position (`mkOfTerminalΩ₀` arguments, `Equiv` data fields)
   is computable at the pinned revision.
6. Obstruction analysis (§3) mathematically accurate as
   stated (UIP vs univalence; independence claims).
7. Scope guardrails complete; no scope creep into power
   objects or transfer machinery.
8. No development-history references in docstrings (document
   only the persistent).
9. Test plan does not rely on kernel reduction of `Prop`
   data.
10. LOC estimates plausible.

## 12 References

- [UF13] The Univalent Foundations Program, *Homotopy Type
  Theory: Univalent Foundations of Mathematics*, 2013,
  §10.1.4–10.1.5, Theorem 10.1.12.
  <https://homotopytypetheory.org/book/>
- [MM92] S. MacLane and I. Moerdijk, *Sheaves in Geometry and
  Logic*, Springer, 1992, §I.3–I.4.
- nLab, *mere proposition*:
  <https://ncatlab.org/nlab/show/mere+proposition>
- Idris antecedents:
  `geb-idris/src/Library/IdrisCategories.idr` lines
  1244–1320; `geb-idris/src/LanguageDef/GebTopos.idr` lines
  2669–2888.
- Lean 3 prior art: <https://github.com/b-mehta/topos>.
- mathlib: `Mathlib.CategoryTheory.Topos.Classifier`.
