# Workstream: Mendler-Lambek Equivalence via Ends and Powers

## Status

Complete

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

### Phase 3: PowerEndGExtFunctor (DONE)

Task 9 defines `PowerEndGExtFunctor G`, naturally
isomorphic to `GExtFunctor G` but with carrier
`CopowerGExtObj G` (copower-profunctor coend), and
composes the full equivalence.

#### Task 9: PowerEndGExtFunctor and full equivalence

File: `GebLean/MendlerLambekEndPower.lean`

- [x] 9a. Define `PowerEndGExtFunctor G : C ⥤ C` with
  `obj pt := CopowerGExtObj G pt` and maps via
  `copowerGExtIso` conjugation
- [x] 9b. Define `powerEndGExtNatIso :
  PowerEndGExtFunctor G ≅ GExtFunctor G` using
  `copowerGExtIso` as components
- [x] 9c. Define `mendlerLambekPowerEndFullEquiv :
  PowerEndMendlerAlgebra G ≌
    ConventionalAlgebra (PowerEndGExtFunctor G)`
  using `mendlerLambekEndPowerEquiv` composed with
  `Endofunctor.Algebra.equivOfNatIso`

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
