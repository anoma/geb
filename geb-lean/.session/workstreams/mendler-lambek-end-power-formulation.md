# Workstream: Mendler-Lambek Equivalence via Ends and Powers

## Status

Phases 1-5 complete. Phase 6: Tasks 11-13 done;
Task 14 in progress. Type-valued impredicative
GExt section and C=Type v pointwise equivalences
complete. Categorical equivalence deferred to
existing `mendlerLambekEquiv` infrastructure
(under `HasAllHomToProfCoends G`).

Phases 1-5 established the equivalence
`MendlerAlgebra G ≌ ConventionalAlgebra F`
where `F = PowerEndGExtFunctor G`, with morphisms
defined via the end/power characterization. However,
`F.obj pt` is still defined as `CopowerGExtObj G pt`
(a coend of copowers). Phase 6 addresses this gap:
define a functor with end/power-based carrier,
naturally isomorphic to `PowerEndGExtFunctor G`,
and transfer the algebra equivalence.

The `ihomCoendWedge` (completed in Phase 5b) shows
`[CopowerGExtObj G pt, Y]_C` carries a wedge for
`ihomPowerProf G pt Y`. Proving terminality of this
wedge establishes the internal representability:
`∫_A [G(A,A), Y^{A→pt}]_C ≅ [CopowerGExtObj G pt, Y]_C`.

File: `GebLean/MendlerLambekPresheaf.lean`. Two
equivalences stated for `C = E ⥤ Type (max w₁ v₁ u₁)`:

1. `presheafMendlerAlgPowerEndEquiv`:
   unconditional (copowers/powers automatic).
2. `presheafMendlerLambekEndPowerEquiv`:
   requires `HasAllHomToProfCoends G`.

The impredicative equivalence was removed (it
required a parametricity condition not
dischargeable in predicative type theory).
The `ImpredicativeGExtIso` section in
`MendlerLambekEndPower.lean` retains the
one-direction morphisms
(`impredicativeGExtToCopowerGExt`,
`copowerGExtToImpredicativeGExt`,
`copowerGExt_backward_forward`).

### Universe generalization

`EndsAndCoends.lean` has universe-generalized
coend-end duality (`typeCoend.endEquiv` with
independent universe parameters for profunctor
values, index category, and target type).
These may enable a cross-universe approach to
the Mendler-Lambek equivalence using `typeCoend`
directly, bypassing `HasAllCopowerProfCoends`.

## Context

This workstream extends the completed Mendler-Lambek correspondence
(in `WeightedAlg.lean`) to derive an equivalent formulation using
ends and powers instead of restricted coends. The existing
`mendlerLambekEquiv` uses restricted coends (initial objects in
the category of hom-restricted cowedges). This workstream
re-expresses the same equivalence via ends and powers, yielding
a power-end Mendler algebra category and a parallel equivalence.

### Mathematical Goal

The existing equivalence is:

```text
MendlerAlgebra G ≌ ConventionalAlgebra (GExtFunctor G)
```

where `GExtFunctor G` is defined via restricted coends and
`MendlerAlgebra G` consists of families
`∀ A (γ : A ⟶ pt), G(A,A) ⟶ pt` satisfying dinaturality.

The target equivalence is:

```text
PowerEndMendlerAlgebra G ≌ ConventionalAlgebra (GExtFunctor G)
```

where `PowerEndMendlerAlgebra G` consists of families
`∀ A, G(A,A) ⟶ pt^(A ⟶ pt)` satisfying the end wedge
condition — equivalently, elements of
`typeEnd (powerSliceProf G pt pt)`.

The derivation chain for the representable characterization:

1. Transfer restricted coend to copower-profunctor coend.
2. Apply coend-end duality:
   `Hom(coend, Y) ≅ typeEnd (P ⇓ Y)`.
3. Replace copowers with powers inside the end via
   `copowerPowerEquiv`.

Final characterization:

```text
Hom(G^e(pt), Y) ≅ ∫_A Hom(G(A,A), Y^(A→pt))
```

### References

- Vene, "Categorical Programming with Inductive and Coinductive
  Types", sections 5.3-5.7
- Existing codebase:
  - `GebLean/WeightedAlg.lean` — mendlerLambekEquiv,
    MendlerAlgebra, GExtFunctor, ConventionalAlgebra
  - `GebLean/RestrictedCoendAsColimit.lean` —
    homRestrictedCopowerEquiv, HasAllCopowerProfCoends,
    mendlerLambekCopowerEquiv, copowerGExtIso
  - `GebLean/MendlerLambekEndPower.lean` —
    cowedgeHomEndEquiv, copowerGExtHomEndEquiv,
    powerSliceProf, endCopowerPowerEquiv,
    gExtEndPowerEquiv
  - `GebLean/Utilities/EndsAndCoends.lean` —
    typeEnd, typeEnd.map, typeEndFunctor
  - `GebLean/Utilities/PowersAndCopowers.lean` —
    copowerPowerEquiv, copowerPowerAdjunction

## Tasks

### Phase 1: Representable Characterization (DONE)

Tasks 1-4 derive the end-power formula for hom-sets out
of `G^e(pt)`.

#### Task 1: Restricted coend as copower-profunctor coend (DONE)

File: `GebLean/RestrictedCoendAsColimit.lean`

- [x] 1a. `HasAllCopowerProfCoends` typeclass
- [x] 1b. `HasAllHomToProfCoends.toCopowerProfCoends`
- [x] 1c. `HasAllCopowerProfCoends.toHomToProfCoends`
- [x] 1d. `CopowerGExtObj`, `CopowerGExtInj`
- [x] 1e. `mendlerLambekCopowerEquiv`
- [x] 1f. `copowerGExtIso`

#### Task 2: Coend-end duality for initial cowedges (DONE)

File: `GebLean/MendlerLambekEndPower.lean`

- [x] 2a. `cowedgeHomEndEquiv` — generic coend-end duality
  for C-valued profunctors with initial cowedges

#### Task 3: End formula for GExtFunctor (DONE)

File: `GebLean/MendlerLambekEndPower.lean`

- [x] 3a. `copowerGExtHomEndEquiv` — applies
  `cowedgeHomEndEquiv` to the copower-profunctor coend

#### Task 4: Replace copower with power inside the end (DONE)

File: `GebLean/MendlerLambekEndPower.lean`

- [x] 4a. `powerSliceProf` — the profunctor
  `(A, B) ↦ (G(op B, A.unop) ⟶ Y^(B ⟶ pt))`
- [x] 4b. `endCopowerPowerEquiv` — lifts componentwise
  `copowerPowerEquiv` to an equivalence of ends
- [x] 4c. `gExtEndPowerEquiv` — the final composition:
  `(CopowerGExtObj G pt ⟶ Y) ≃
    typeEnd (powerSliceProf G pt Y)`

### Phase 2: Power-End Mendler Algebras (DONE)

Tasks 5-8 define the power-end Mendler algebra category
and establish its equivalence with conventional algebras.

The existing `MendlerAlgebra G` bundles:

- carrier `pt : C`
- family `∀ A (γ : A ⟶ pt), G(A,A) ⟶ pt`
  (equivalently, a `ParanatSig (HomToProf pt) (G ⇓ pt)`)
- dinaturality of the family

The power-end version bundles:

- carrier `pt : C`
- element of `typeEnd (powerSliceProf G pt pt)`,
  i.e., a family `∀ A, G(A,A) ⟶ pt^(A ⟶ pt)` satisfying
  the end wedge condition

These are equivalent via `copowerPowerEquiv` at each
component, currying `(A ⟶ pt) → (G(A,A) ⟶ pt)` into
`G(A,A) ⟶ pt^(A ⟶ pt)`.

#### Task 5: Define PowerEndMendlerAlgebra

File: `GebLean/MendlerLambekEndPower.lean`

- [x] 5a. Define `PowerEndMendlerAlgebra G`:

  ```lean
  structure PowerEndMendlerAlgebra where
    pt : C
    str : typeEnd (powerSliceProf G pt pt)
  ```

  The `str` field packages a family
  `∀ A, G(A,A) ⟶ pt^(A ⟶ pt)` satisfying the end wedge
  condition (naturality in A).

- [x] 5b. Define accessor abbreviations parallel to
  `MendlerAlgebra`:
  - `algOp (m : PowerEndMendlerAlgebra G) (A : C) :
      G(A,A) ⟶ power m.pt (A ⟶ m.pt)` — the algebra
    operation at `A`
  - `wedgeCondition` — the naturality condition extracted
    from `str.property`

#### Task 6: Define PowerEndMendlerAlgebra category

File: `GebLean/MendlerLambekEndPower.lean`

- [x] 6a. Define `PowerEndMendlerAlgebraHom`:

  ```lean
  structure PowerEndMendlerAlgebraHom
      (m₁ m₂ : PowerEndMendlerAlgebra G) where
    hom : m₁.pt ⟶ m₂.pt
    comm : ∀ (A : C),
      m₁.algOp A ≫ HasPowers.mapVal hom =
        (G.obj (op A)).map hom ≫
          (G.map hom.op).app A ≫
          m₂.algOp A ≫ HasPowers.mapIdx (hom ≫ ·)
  ```

  (The exact form of `comm` needs verification; it should
  express that `hom` is compatible with the algebra
  structures. The condition says that for each `A`, the
  two paths from `G(A,A)` to `power m₂.pt (A ⟶ m₂.pt)`
  agree.)

  Alternative (may be cleaner): the compatibility condition
  could be expressed as: for all `A` and `s : A ⟶ m₁.pt`,

  ```lean
  m₁.algOp A ≫ proj s = (G.obj (op A)).map hom ≫
    (G.map hom.op).app A ≫ m₂.algOp A ≫ proj (s ≫ hom)
  ```

  which is the power-end form of the existing
  `MendlerAlgebraHom.comm`:
  `m₁.family A γ ≫ hom = m₂.family A (γ ≫ hom)`.

  The cleanest approach is probably to define the hom
  condition as `m₁.algOp A ≫ HasPowers.mapVal hom`
  equals the appropriate composition, then verify it
  matches the existing condition under the equivalence.

- [x] 6b. Define identity, composition for
  `PowerEndMendlerAlgebraHom`

- [x] 6c. Define `PowerEndMendlerAlgebraCat`:
  `Category (PowerEndMendlerAlgebra G)`

#### Task 7: Equivalence with MendlerAlgebra

File: `GebLean/MendlerLambekEndPower.lean`

- [x] 7a. Define `MendlerAlgebra.toPowerEnd`:
  `MendlerAlgebra G → PowerEndMendlerAlgebra G`
  — applies `copowerPowerEquiv` componentwise to convert
  `∀ A (γ : A ⟶ pt), G(A,A) ⟶ pt` to
  `∀ A, G(A,A) ⟶ pt^(A ⟶ pt)`, with the wedge condition
  following from dinaturality.

- [x] 7b. Define `PowerEndMendlerAlgebra.toMendler`:
  `PowerEndMendlerAlgebra G → MendlerAlgebra G`
  — applies `copowerPowerEquiv.symm` (uncurrying).

- [x] 7c. Lift to functors and prove they form an
  equivalence:
  `mendlerAlgPowerEndEquiv :
    MendlerAlgebra G ≌ PowerEndMendlerAlgebra G`

  The object-level round-trips follow from
  `copowerPowerEquiv.left_inv`/`right_inv` at each
  component (same pattern as `endCopowerPowerEquiv`).
  The morphism-level compatibility follows from the
  adjunction naturality.

#### Task 8: Power-end Mendler-Lambek equivalence

File: `GebLean/MendlerLambekEndPower.lean`

- [x] 8a. Compose equivalences to get the final result:

  ```lean
  mendlerLambekEndPowerEquiv :
    PowerEndMendlerAlgebra G ≌
      ConventionalAlgebra (GExtFunctor G)
  ```

  This is `mendlerAlgPowerEndEquiv.symm.trans
    mendlerLambekEquiv` (or
  `mendlerLambekCopowerEquiv` if using copower coends).

  Alternatively, if the user prefers, we could construct
  this directly using `gExtEndPowerEquiv` and the
  Yoneda-style argument that the representable
  characterization determines the algebra structure.

### Phase 3: ImpredicativeGExtFunctor (DONE)

Task 9 defines `ImpredicativeGExtFunctor G`, naturally
isomorphic to `GExtFunctor G` but with carrier defined
entirely via ends, powers, and internal homs. It also
defines a copower-coend variant
`CopowerCoendGExtFunctor G` whose maps are defined by
conjugation with `copowerGExtIso`.

#### Task 9: ImpredicativeGExtFunctor and full equivalence

File: `GebLean/MendlerLambekEndPower.lean`

- [x] 9a. Define `ImpredicativeGExtFunctor G : C ⥤ C`
  with `obj pt := ImpredicativeGExtObj G pt` and maps
  via end transport (`HasTerminalWedge.map` and
  `churchProfMapPt`).
  Also `CopowerCoendGExtFunctor G : C ⥤ C` with
  `obj pt := CopowerGExtObj G pt` and maps via
  `copowerGExtIso` conjugation.
  Also `copowerCoendGExtNatIso :
  CopowerCoendGExtFunctor G ≅ GExtFunctor G`
  and `mendlerLambekCopowerCoendEquiv`.
- [removed] 9b-9c. The impredicative equivalence
  (parameterized by a parametricity condition) was
  removed as the condition is not dischargeable in
  predicative type theory.

#### Removed impredicative equivalence

Tasks 9b-9c and the associated gap analysis have
been removed. The impredicative equivalence
required a parametricity condition (asserting
every element of the Church encoding is
representable) that is not derivable in a
general monoidal closed category and could not
be discharged for concrete categories due to
the universe bump from self-indexed (co)ends.

## Notes

### Existing Infrastructure (Phase 1)

- `isInitialOfEquivFunctor` (Category.lean) — transfers
  initial objects across category equivalences
- `homRestrictedCopowerEquiv`
  (RestrictedCoendAsColimit.lean) — category equivalence
  between hom-restricted and hom-copower cowedges
- `copowerPowerEquiv` (PowersAndCopowers.lean) —
  `(S . X ⟶ Y) ≃ (X ⟶ Y^S)`
- `copowerPowerAdjunction` (PowersAndCopowers.lean) —
  packages naturality of `copowerPowerEquiv`

### Existing Infrastructure (Phase 2)

- `MendlerAlgebra` (WeightedAlg.lean:469) — structure
  with `pt`, `toMendlerAlgebraOver`
- `MendlerAlgebraHom` (WeightedAlg.lean:577) — morphism
  with `hom : m₁.pt ⟶ m₂.pt` and `comm`
- `mendlerLambekEquiv` (WeightedAlg.lean:1615) —
  `MendlerAlgebra G ≌ ConventionalAlgebra (GExtFunctor G)`
- `mendlerLambekCopowerEquiv`
  (RestrictedCoendAsColimit.lean:2857) — same under
  `HasAllCopowerProfCoends`
- `ConventionalAlgebra F` (WeightedAlg.lean:1397) —
  abbreviation for `Endofunctor.Algebra F`
- `copowerGExtIso` (RestrictedCoendAsColimit.lean:2867) —
  `CopowerGExtObj G pt ≅ GExtObj G pt`

### File Placement

- Phase 1: `RestrictedCoendAsColimit.lean` (Task 1),
  `MendlerLambekEndPower.lean` (Tasks 2-4)
- Phase 2: `MendlerLambekEndPower.lean` (Tasks 5-8)

### Dependencies

Phase 1:

- Task 1 and Task 2 are independent
- Task 3 depends on Tasks 1 and 2
- Task 4 depends on Task 3

Phase 2:

- Task 5 depends on Task 4 (uses `powerSliceProf`)
- Task 6 depends on Task 5
- Task 7 depends on Tasks 5, 6, and Phase 1
  (uses `copowerPowerEquiv` and existing
  `MendlerAlgebra` category)
- Task 8 depends on Task 7 (composes equivalences)

### Design Decisions

- `PowerEndMendlerAlgebra` uses `typeEnd` directly for
  the algebra data, giving maximal reuse of end
  infrastructure.
- The hom condition in `PowerEndMendlerAlgebraHom` should
  be the exact transport of `MendlerAlgebraHom.comm`
  through `copowerPowerEquiv`. The precise form will be
  determined during implementation of Task 6.
- Task 8 composes existing equivalences rather than
  constructing a direct proof, to minimize new proof
  obligations.

### Phase 4: Universe Generalization (10a-10c DONE)

Generalize `MendlerLambekEndPower.lean` from
`{C : Type v} [Category.{v} C]` to
`{C : Type u} [Category.{v} C]` so that the
framework can be instantiated for `C = Type v`
(where `Type v : Type (v+1)`, requiring `u = v+1`).

#### Analysis

The obstacle was `cowedgeHomEndEquiv`, which returns
`(c.pt ⟶ Y) ≃ typeEnd (P ⇓ Y)`. When `C : Type u`:

- LHS `(c.pt ⟶ Y) : Type v` (morphism universe)
- RHS `typeEnd (P ⇓ Y) : Type (max u v)`

The previous implementation went through
`ordinaryHomIsoEndApex`, which gives a categorical
`≅` in `Type v` and requires the terminal wedge
apex to also be in `Type v`. The `typeEndWedge`
apex is in `Type (max u v)`, so this path fails
when `u > v`.

The resolution: `Equiv` (unlike `Iso`) is
universe-polymorphic — `Equiv α β` allows
`α : Sort u₁` and `β : Sort u₂` with `u₁ ≠ u₂`.
So `(c.pt ⟶ Y) ≃ typeEnd (P ⇓ Y)` is well-typed
at any universe levels. The equiv can be constructed
directly from the coend universal property
(`homOrdinaryWedge_isTerminal`) without going
through `typeEndWedge`.

#### Phase 4 tasks

##### Task 10a: Generalize `HasTerminalWedge` (DONE)

Changed `{J : Type v} [Category.{v} J]` to
`{J : Type u} [Category.{v} J]` in the structure
and all four methods (`map`, `map_ι`, `hom_ext`,
`map_id`, `map_comp`).

##### Task 10b: Rewrite `cowedgeHomEndEquiv` (DONE)

Replaced the `ordinaryHomIsoEndApex`-based
implementation with a direct `Equiv` construction:

- `toFun`: uses `homOrdinaryWedge` legs to build
  the compatible family in `typeEnd (P ⇓ Y)`
- `invFun`: constructs a `PUnit.{v+1}` wedge
  from the compatible family and lifts through
  `Wedge.IsLimit.lift` (derived from
  `homOrdinaryWedge_isTerminal`)
- `left_inv`: by `Multifork.IsLimit.hom_ext`
  (uniqueness of the lift)
- `right_inv`: by `Wedge.IsLimit.lift_ι`
  (projection of the lift)

##### Task 10c: Generalize section variables (DONE)

Changed all `{C : Type v} [Category.{v} C]` to
`{C : Type u} [Category.{v} C]` (14 occurrences)
throughout `MendlerLambekEndPower.lean`. The
`typeEnd` elements now live in `Type (max u v)`
instead of `Type v`; this is transparent to
downstream code since `Equiv` bridges the gap.
No downstream proof breakage occurred (the two
`change` tactics referencing `homOrdinaryWedge`
still work because `cowedgeHomEndEquiv.toFun`
reduces through the same `homOrdinaryWedge` legs).

##### Task 10d: Verify presheaf instantiability

DONE. Verified for presheaf categories
`E ⥤ Type (max w₁ v₁ u₁)` (generalizing `Type v`).

File: `GebLean/MendlerLambekPresheaf.lean`.

All basic instances resolve automatically:
`Category`, `MonoidalCategory`, `MonoidalClosed`,
`BraidedCategory`, `HasCopowers`, `HasPowers`.

Two equivalences are stated:

1. `presheafMendlerAlgPowerEndEquiv` — unconditional
2. `presheafMendlerLambekEndPowerEquiv` —
   requires `HasAllHomToProfCoends G`

The impredicative equivalence (formerly item 3)
was removed.

### Phase 5: Coend-End Duality for Algebras (DONE)

Use the new cowedge/wedge duality infrastructure
(`cowedgeOpWedgeEquivalence`,
`weightedCowedgeOpWedgeEquivalence`, etc. in
`Weighted.lean`) to show a further equivalence of
`PowerEndMendlerAlgebra G` with conventional algebras
of a functor defined via ends rather than coends.

#### Mathematical Context

The existing `CopowerCoendGExtFunctor G : C ⥤ C`
sends `pt ↦ CopowerGExtObj G pt`, where
`CopowerGExtObj G pt` is the carrier of the coend
(initial cowedge) of `copowerProf (HomToProf pt) G`.

The duality `cowedgeOpWedgeEquivalence` provides:

```text
Cowedge (copowerProf (HomToProf pt) G)
  ≌ (Wedge (profunctorSwapOp C
       (copowerProf (HomToProf pt) G)))ᵒᵖ
```

Under this equivalence, the initial cowedge (coend)
maps to a terminal wedge (end). The wedge category
lands in `Cᵒᵖ` since `profunctorSwapOp C` sends
`Cᵒᵖ ⥤ C ⥤ C` to `Cᵒᵖ ⥤ C ⥤ Cᵒᵖ`.

The swapped-op profunctor at `(op A, A)` gives:

```text
profunctorSwapOp C (copowerProf (HomToProf pt) G)
  .obj (op A) .obj A
  = op((A ⟶ pt) · G(A, A))
```

The terminal wedge has apex
`op(CopowerGExtObj G pt) : Cᵒᵖ`, with projections
being morphisms `(A ⟶ pt) · G(A, A) ⟶
CopowerGExtObj G pt` in `C` — exactly the coend
injections, repackaged as end projections.

The connection to `powerSliceProf` is via
`copowerPowerEquiv`: hom from the wedge apex
`op Y` to the diagonal value
`op((A ⟶ pt) · G(A, A))` in `Cᵒᵖ` is
`(A ⟶ pt) · G(A, A) ⟶ Y` in `C`, which by
copower-power adjunction is
`G(A, A) ⟶ Y^(A ⟶ pt)` — the `powerSliceProf`
diagonal.

#### Plan

**Step 1**: Show the relationship between
`profunctorSwapOp C (copowerProf (HomToProf pt) G)`
and `powerSliceProf G pt Y`. The hom-set version
is already captured by `gExtEndPowerEquiv`. The
categorical version connects
`cowedgeOpWedgeEquivalence` with
`endCopowerPowerEquiv`. Look at existing
infrastructure in `PowersAndCopowers.lean`,
`EndsAndCoends.lean`, `Weighted.lean`, and
`WeightedAlg.lean` for end/coend correspondences,
weighted limit/colimit correspondences, and
power/copower correspondences (including
impredicative variants).

**Step 2**: Define `PowerEndGExtFunctor G : C ⥤ C`
using the end characterization. Since the carrier is
the same object `CopowerGExtObj G pt` (the duality
preserves carriers, only wrapping in `op`), the
functor is naturally isomorphic to
`CopowerCoendGExtFunctor G`. Use whichever approach
(direct definition via terminal wedge, or via NatIso
from the existing functor) produces clearer code.

**Step 3**: Derive the extended equivalence:

```text
PowerEndMendlerAlgebra G
  ≌ ConventionalAlgebra (CopowerCoendGExtFunctor G)
  ≌ ConventionalAlgebra (PowerEndGExtFunctor G)
```

The second step is via
`Endofunctor.Algebra.equivOfNatIso`.

**Step 4 (if straightforward)**: Connect to coalgebras in
`Cᵒᵖ`. The duality gives coalgebras rather than
algebras since the end lives in `Cᵒᵖ`:

```text
ConventionalAlgebra (CopowerCoendGExtFunctor G)
  ≌ (Endofunctor.Coalgebra F')ᵒᵖ
```

where `F' : Cᵒᵖ ⥤ Cᵒᵖ` is the end-based
endofunctor on `Cᵒᵖ`. This is lower priority.

#### Completion Notes

Step 1 is implicit in the supporting lemmas:

- `gExtEndPowerEquiv_proj` — projection formula
  for `gExtEndPowerEquiv`
- `inj_comp_powerEndGExtMap` — commutativity of
  `powerEndGExtMap` with coend injections

Step 2: `PowerEndGExtFunctor G : C ⥤ C` defined
with `obj pt := CopowerGExtObj G pt` and
`map h := powerEndGExtMap G h`. The composition
law (`powerEndGExtMap_comp`) proved via the coend
injection commutativity lemma. The functor is
naturally isomorphic to `CopowerCoendGExtFunctor G`
via `powerEndGExtNatIso`, using coend uniqueness
(`restrictedCoendIsInitial.hom_ext`) to show
`powerEndGExtMap G h = CopowerCoendGExtFunctor.map h`.

Step 3: `mendlerLambekPowerEndGExtEquiv :
PowerEndMendlerAlgebra G ≌
ConventionalAlgebra (PowerEndGExtFunctor G)` derived
by composing `mendlerLambekCopowerCoendEquiv G` with
`Endofunctor.Algebra.equivOfNatIso
(powerEndGExtNatIso G).symm`.

Step 4 (coalgebras in `Cᵒᵖ`) was not pursued.

#### Relevant Existing Infrastructure

- `cowedgeOpWedgeEquivalence` (Weighted.lean) —
  `Cowedge P ≌ (Wedge (profunctorSwapOp C P))ᵒᵖ`
- `wedgeOpCowedgeEquivalence` (Weighted.lean) —
  `Wedge P ≌ (Cowedge (profunctorSwapOp C P))ᵒᵖ`
- `weightedCowedgeOpWedgeEquivalence`
  (Weighted.lean) — weighted version of the above
- `weightedWedgeOpCowedgeEquivalence`
  (Weighted.lean) — weighted reverse direction
- `copowerPowerEquiv` (PowersAndCopowers.lean) —
  `(S · X ⟶ Y) ≃ (X ⟶ Y^S)`
- `endCopowerPowerEquiv` (MendlerLambekEndPower) —
  lifts copowerPowerEquiv to ends
- `gExtEndPowerEquiv` (MendlerLambekEndPower) —
  `(CopowerGExtObj G pt ⟶ Y) ≃
    typeEnd (powerSliceProf G pt Y)`
- `copowerCoendGExtNatIso` (MendlerLambekEndPower)
  — `CopowerCoendGExtFunctor G ≅ GExtFunctor G`
- `Endofunctor.Algebra.equivOfNatIso` (mathlib) —
  transfers algebra categories along NatIso
- Various end/coend, power/copower, and
  weighted limit/colimit correspondences in
  `PowersAndCopowers.lean`, `EndsAndCoends.lean`,
  `Weighted.lean`, and `WeightedAlg.lean`

#### Files

Implementation goes in
`GebLean/MendlerLambekEndPower.lean` (extending
the existing module).

#### User Direction

The user emphasized:

- Look at existing equivalences in
  `PowersAndCopowers.lean` and `EndsAndCoends.lean`
  for correspondences that might be reusable
- Look at `Weighted.lean` and `WeightedAlg.lean`
  for end/coend, weighted limit/colimit, and
  power/copower correspondences
- Some of these are designed for impredicative
  polymorphism and might be relevant
- Step 4 (coalgebras in Cᵒᵖ) is not urgent but
  can be added if straightforward

### Phase 5b: Internal End Characterization (DONE)

Proved `ihomCoendWedge G pt Y`, showing
`[CopowerGExtObj G pt, Y]_C` carries a wedge for
`ihomPowerProf G pt Y`. This is a prerequisite
for Phase 6.

### Phase 6: End-Based GExt Functor (IN PROGRESS)

#### End Goal

Define a functor `F : C ⥤ C` satisfying:

1. `F.obj pt` is defined via ends and powers
   (no reference to coends or copowers)
2. `F ≅ PowerEndGExtFunctor G` (natural iso)
3. `ConventionalAlgebra F ≌ MendlerAlgebra G`
   (by composing the nat iso with
   `mendlerLambekPowerEndGExtEquiv`)

The existing `PowerEndGExtFunctor G` (which should
be renamed — its name suggests end/power-based
definition, but `obj pt := CopowerGExtObj G pt`
still references the coend of copowers) satisfies
conditions 2-3 trivially but NOT condition 1.

#### Renaming

`PowerEndGExtFunctor G` should be renamed to
reflect that it uses `CopowerGExtObj` (a coend
of copowers) as its carrier. Suggested name:
`CopowerCoendGExtEndMapFunctor G` or similar,
indicating that the carrier is coend-based while
the maps use the end characterization.

#### Mathematical Analysis

The internal end `∫_A [G(A,A), Y^{A→pt}]_C`
(terminal wedge apex of `ihomPowerProf G pt Y`)
equals `[CopowerGExtObj G pt, Y]_C` by the
`ihomCoendWedge` terminality (once proved).

Setting `Y = pt`: the end-of-powers object at
`pt` is `[CopowerGExtObj G pt, pt]_C`, which is
the internal hom from the coend to `pt`. This
is NOT the same as `CopowerGExtObj G pt`.

The relationship between the two:

- `Hom(𝟙_C, [X, pt]) ≅ Hom(X, pt)` (by the
  tensor-hom adjunction and unit iso), so
  global sections of the end biject with
  conventional algebra structure maps.
- But `[X, pt] ⟶ pt` (a C-morphism from the
  end object) is more data than `X ⟶ pt`.

So `pt ↦ [CopowerGExtObj G pt, pt]_C` gives an
endofunctor whose algebras are RICHER than those
of `pt ↦ CopowerGExtObj G pt`. The algebra
categories are not equivalent in general.

#### Open Questions

1. Is there a construction that gives
   `CopowerGExtObj G pt` as an end object in C
   (not just characterized by an end)?
2. Can we define the functor parameterized by
   abstract terminal wedge families, where the
   carrier IS the terminal wedge apex, and show
   the algebra equivalence under the assumption
   that the terminal wedges come from
   `ihomCoendWedge`?
3. For concrete categories (presheaf categories),
   does the internal end equal the representing
   object (avoiding the general-category
   subtlety)?

#### Prerequisite Tasks

##### Task 11: Terminality of ihomCoendWedge (DONE)

Proved `ihomCoendWedge_isLimit` via
`Multifork.IsLimit.mk`, using
`ihomCoendWedgeLift` (lift),
`ihomCoendWedgeLift_fac` (factorization), and
`ihomCoendWedgeLift_uniq` (uniqueness). Packaged
as `ihomCoendHasTerminalWedge`.

##### Task 12: Natural iso (DONE)

##### ihomPowerEndFunctor ≅ ihom ∘ CopowerGExtObj

Proved `ihomCoendPowerEndNatIso`:
`ihom (CopowerGExtObj G pt) ≅
  ihomPowerEndFunctor G pt
    (fun Y => ihomCoendHasTerminalWedge G pt Y)`
via `NatIso.ofComponents` with `Iso.refl`
components. Naturality follows from
`ihom_map_comp_ihomCoendWedgeProj` (naturality
of the coend wedge projections in Y) and
`HasTerminalWedge.hom_ext` (uniqueness of
terminal wedge lifts). Supporting lemmas:

- `copowerIhomToPowerIhom_naturalY` — naturality
  of the copower-ihom-to-power-ihom map in Y
- `ihom_map_comp_ihomCoendWedgeProj` — `(ihom X).map f`
  commutes with coend wedge projections

##### Task 13: Composed single equivalence (DONE)

Defined `mendlerLambekGExtEquiv :
  MendlerAlgebra G ≌
    ConventionalAlgebra (PowerEndGExtFunctor G)`
as `mendlerAlgPowerEndEquiv G |>.trans
    (mendlerLambekPowerEndGExtEquiv G)`.

##### Task 14: End-based functor and algebra equiv

Depends on resolving the open questions above.
Define the end-based functor and its algebra
equivalence with `MendlerAlgebra G`.

###### Type-valued impredicative GExt (DONE)

For a Type-valued profunctor
`G : Cᵒᵖ ⥤ C ⥤ Type v` over an arbitrary
category `C : Type u`, the following are defined
in the `TypeValuedGExt` section of
`MendlerLambekEndPower.lean`:

- `mendlerTypeProf pt G` — the Type-valued
  Mendler extension profunctor sending
  `(op A, B) ↦ (A ⟶ pt) × G(A, B)`.
- `mendlerTypeProf.mapPt G h` — natural
  transformation induced by `h : pt₁ ⟶ pt₂`.
- `mendlerExtType pt G` — the coend
  (`typeCoend (mendlerTypeProf pt G)`).
- `mendlerUnivType pt G` — the Church encoding
  (`endLimitFunctor ⟶ 𝟭`).
- `mendlerUnivTypeEquiv` — unconditional
  equivalence between Church encoding and coend
  (via `typeCoend.endImpredicative`).
- `mendlerExtType.map`, `mendlerUnivType.map` —
  functorial actions on the carrier.
- `mendlerAlgTypeEquiv pt G X` — the coend
  algebra characterization:
  `(mendlerExtType pt G → X) ≃
    typeEnd (sliceProfunctorPoly ...)`.
- `mendlerUnivAlgTypeEquiv pt G X` — the
  universal algebra characterization (composing
  `Equiv.arrowCongr` of `mendlerUnivTypeEquiv`
  with `mendlerAlgTypeEquiv`).
- `mendlerTypeProfFunctor G` — packages
  `pt ↦ mendlerTypeProf pt G` as
  `C ⥤ (Cᵒᵖ ⥤ C ⥤ Type v)`.
- `mendlerExtTypeFunctor G` — the Mendler
  extension as `C ⥤ Type (max u v)`,
  i.e., `mendlerTypeProfFunctor G ⋙
  typeCoendFunctor C`.
- Functor laws: `mapPt_id`, `mapPt_comp`,
  `map_id`, `map_comp`.

This generalizes the Idris `ProfMendlerExt`,
`ProfMendlerUniv`, `MendlerAlg`,
`MendlerAlgToFAlgExt`/`FAlgToMendlerAlgExt`,
and `MendlerAlgToFAlgUniv`/`FAlgToMendlerAlgUniv`
from `.claude/docs/InternalProfunctor.idr`
(lines 3390-3497) to arbitrary categories with
Type-valued profunctors. The Church encoding
equivalence is unconditional (no parametricity
condition).

###### Type-valued pointwise equivalences (DONE)

For `C = Type v`, the `TypeValuedMendlerAlgConnection`
section provides:

- `mendlerFamilyUncurry` / `mendlerFamilyCurry`:
  currying isomorphism between Mendler algebra
  families and type end families.
- `mendlerFamilyUncurry_wedge` /
  `mendlerFamilyCurry_isDinatural`:
  dinaturality/wedge condition correspondence.
- `mendlerAlgOverTypeEndEquiv pt G`:
  `MendlerAlgebraOver G pt ≃ typeEnd
  (sliceProfunctorPoly (mendlerTypeProf pt G) pt)`.
  Roundtrip is definitional (`left_inv _ := rfl`,
  `right_inv _ := rfl`).
- `mendlerAlgOverAlgMapEquiv pt G`:
  `MendlerAlgebraOver G pt ≃
  (mendlerExtType pt G → pt)`.
- `mendlerHom_to_algMapComm` /
  `algMapComm_to_mendlerHom`: bidirectional
  characterization of Mendler hom conditions
  via `mendlerExtType.map` and
  `mendlerAlgOverAlgMapEquiv`.

###### Design decision: categorical equivalence

A custom `TypeMendlerAlg` category was
abandoned: `mendlerExtTypeFunctor G :
C ⥤ Type (max u v)` crosses universes when
`C = Type v` (where `u = v+1`), so
`Endofunctor.Algebra` (which requires `F : C ⥤ C`)
cannot be used. The constraint `u ≤ v` cannot be
satisfied since `Type v : Type (v+1)` forces
`u = v+1`.

The categorical equivalence for `C = Type v`
should instead use the existing
`mendlerLambekEquiv` from `WeightedAlg.lean`,
which gives
`MendlerAlgebra G ≌ Endofunctor.Algebra
(GExtFunctor G)` under `HasAllHomToProfCoends G`.

###### End-based `impFloor_impCeil` (IN PROGRESS)

New lemmas (no `twOuter` dependency):

- `CopowerGExtInj_comp_cgeChurchLeg`: coend
  injection composed with church leg = copower
  desc of church components.
- `inj_inj_cgeChurchLeg_direct`: full
  componentwise identity at `(A, s)` level.
- `cgeChurchLeg_wedge_direct`: church profunctor
  wedge condition proved from definition.
- `cgeChurchWedge`: wedge with apex `cge` and
  legs `cgeChurchLeg` (enriched Yoneda wedge).
- `cgeChurchLift`: lift from arbitrary church
  profunctor wedge to `cge` via `bwdGlobalSection`.
- Bridging instances for
  `multicospanShapeEnd C` (typeclass synthesis
  workaround for `maxSynthPendingDepth = 3`).

The `impFloor_impCeil` goal:

```lean
ι a ≫ ihomEvalAt(mendlerGlobalSection G m
  twInner) = str
```

All proof approaches reduce to the enriched
Yoneda factorization: for a church profunctor
wedge `s`, the equation
`s.ι cge ≫ ihomEvalAt(bwdGS) ≫ cgeChurchLeg Y
  = s.ι Y`
(the factorization property for `cgeChurchLift`).
This is NOT provable from wedge conditions alone;
it IS the terminal wedge property (enriched
Yoneda lemma). Proving it requires a deeper
argument, likely specializing to
`twInner := ihomCoendHasTerminalWedge G pt`
and using `bwdGS = curry'(𝟙 cge)` under that
specialization.

###### Remaining for Task 14

- Prove enriched Yoneda factorization
  (`cgeChurchLift_fac`) under the
  `ihomCoendHasTerminalWedge` specialization.
- Complete `impFloor_impCeil` using the
  factorization.
- Instantiate `HasAllHomToProfCoends G` for
  `C = Type v` (if possible; requires
  restricted coends to exist as objects of
  `Type v`, which involves showing the
  type-level coend is `Small.{v}`).
- Presheaf instantiation: for
  `C = E ⥤ Type v`, instantiate
  `mendlerExtTypeFunctor` and connect to
  `pointwiseTypeCoend.endImpredicative`.

#### Source Files

Implementation in
`GebLean/MendlerLambekEndPower.lean`.
