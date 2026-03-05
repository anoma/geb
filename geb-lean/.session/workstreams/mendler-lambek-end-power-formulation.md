# Workstream: Mendler-Lambek Equivalence via Ends and Powers

## Status

Phase 3, Tasks 9b-9c in progress

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
isomorphic to `GExtFunctor G` but with carrier
`CopowerGExtObj G` (copower-profunctor coend), and
composes the full equivalence.

#### Task 9: ImpredicativeGExtFunctor and full equivalence

File: `GebLean/MendlerLambekEndPower.lean`

- [x] 9a. Define `ImpredicativeGExtFunctor G : C ⥤ C` with
  `obj pt := CopowerGExtObj G pt` and maps via
  `copowerGExtIso` conjugation
- [ ] 9b. Define `powerEndGExtNatIso :
  ImpredicativeGExtFunctor G ≅ GExtFunctor G` using
  `copowerGExtIso` as components
- [ ] 9c. Define `mendlerLambekPowerEndFullEquiv :
  PowerEndMendlerAlgebra G ≌
    ConventionalAlgebra (ImpredicativeGExtFunctor G)`
  using `mendlerLambekEndPowerEquiv` composed with
  `Endofunctor.Algebra.equivOfNatIso`

### Task 9b-9c Detailed Sub-steps

The component iso for 9b requires
`ImpredicativeGExtObj G pt twInner twOuter ≅
 CopowerGExtObj G pt` (composed with
`copowerGExtIso : CopowerGExtObj ≅ GExtObj`).

We have:

- `fwd = copowerGExtToImpredicativeGExt :
  CopowerGExtObj → ImpredicativeGExtObj`
  (line 1773, defined via `gExtEndPowerEquiv.symm`
  using `churchLift`)
- `bwd = impredicativeGExtToCopowerGExt :
  ImpredicativeGExtObj → CopowerGExtObj`
  (line 1561, defined as
  `twOuter.wedge.ι cge ≫ ihomEvalAt gs`)
- `copowerGExt_backward_forward : fwd ≫ bwd = 𝟙`
  (line 2010, proved)
- `impredicativeGExt_backward_forward :
  bwd ≫ fwd = 𝟙` (**TO PROVE**)

#### Analysis of the proof obligation

Proving `bwd ≫ fwd = 𝟙` cannot be derived from
`fwd ≫ bwd = 𝟙` by abstract categorical reasoning.
Confirmed approaches that do NOT work:

1. **Section-retraction algebra**: `fwd ≫ bwd = 𝟙`
   makes fwd split mono (hence mono) and bwd split
   epi (hence epi), but neither mono+epi in a
   general category, nor mono-of-fwd applied to
   fwd's right-cancellation, yield `bwd ≫ fwd = 𝟙`.
2. **Joint epicity of churchLift family**: The
   derived fact `churchLift A s ≫ (bwd ≫ fwd) =
   churchLift A s` is provable, but the churchLift
   family is not jointly epic (they are lifts into
   a limit, not colimit injections).
3. **isIso_of_epi_of_isSplitMono**: Would require
   showing fwd is epi, which is equivalent to the
   original problem.

The proof genuinely requires the **enriched Yoneda
argument** via the specific terminal wedge and
coend structures.

#### Available helper lemmas (all proved)

1. `churchLift_comp_backward` (line 1940):
   `churchLift A s ≫ bwd = inj(s) ≫
   CopowerGExtInj A`
2. `inj_comp_forward` (line 1978):
   `CopowerGExtInj A ≫ fwd = HasCopowers.desc
   (fun s => churchLift A s)`
3. `churchComponent_ihomEvalAt_eq` (line 1803):
   `churchComponent cge A s ≫ ihomEvalAt gs =
   inj(s) ≫ CopowerGExtInj A`
4. `churchComponent_wedge` (line 1609):
   wedge condition for `churchComponent`
5. `churchComponent_dinatural` (line 1663):
   dinaturality of `churchComponent`
6. `ihomEvalAt_natural` (line 2037):
   `(ihom X).map f ≫ ihomEvalAt gs =
   ihomEvalAt gs ≫ f`

#### Proof strategy: terminal wedge on cge

Construct a terminal `churchProf`-wedge with apex
`CopowerGExtObj G pt`, then use `isTerminalWedgeIso`
to get `ImpredicativeGExtObj ≅ CopowerGExtObj` with
both round-trips free. Match the iso components with
`fwd` and `bwd`.

##### Step A: Define `cgeChurchLeg Y`

Define `cgeChurchLeg Y : cge → [(twInner Y).pt, Y]`
as the unique coend-morphism satisfying:
`CopowerGExtInj A ≫ cgeChurchLeg Y =
 HasCopowers.desc (fun s => churchComponent Y A s)`

Construction: use `gExtEndPowerEquiv.symm` applied
to the typeEnd element with components
`HasPowers.lift (fun s => churchComponent Y A s)`.
The wedge condition for typeEnd follows from
`churchComponent_dinatural`.

##### Step B: cgeChurchLeg wedge condition

Show for `f : Y₁ → Y₂`:
`cgeChurchLeg Y₁ ≫ (churchProf.obj (op Y₁)).map f =
 cgeChurchLeg Y₂ ≫ (churchProf.map f.op).app Y₂`

Reduce to injection level via
`copowerGExtHomEndEquiv.injective`, then to
per-s level via `HasCopowers.ext`. At each `(A, s)`,
follows from `churchComponent_wedge`.

##### Step C: Show `fwd ≫ ι Y = cgeChurchLeg Y`

Reduce to injection level. At each `(A, s)`:
LHS = `churchLift A s ≫ ι Y = churchComponent Y A s`
RHS = definition of `cgeChurchLeg`. Both equal.

##### Step D: Terminality factoring

For a general `churchProf`-wedge W with apex X,
define lift `h := W.ι cge ≫ ihomEvalAt gs : X → cge`.

Need: `h ≫ cgeChurchLeg Y = W.ι Y` for all Y.

This is `W.ι cge ≫ ihomEvalAt gs ≫ cgeChurchLeg Y =
W.ι Y`.

**This is the hard step.** Two approaches:

**Approach D1 (curry-level):** Show
`ihomEvalAt gs ≫ cgeChurchLeg Y :
[(twInner cge).pt, cge] → [(twInner Y).pt, Y]`
by uncurrying both sides to
`[(twInner cge).pt, cge] ⊗ (twInner Y).pt → Y`,
then verify at each inner end projection.

**Approach D2 (wedge condition + naturality):**
Use `ihomEvalAt_natural` to rewrite
`ihomEvalAt gs ≫ cgeChurchLeg Y` as
`(ihom _).map (cgeChurchLeg Y) ≫ ihomEvalAt gs`.
Then use the wedge condition of W applied at the
morphism `cgeChurchLeg Y : cge → [(twInner Y).pt, Y]`
in the indexing category C.

The wedge condition gives:
`W.ι cge ≫ (ihom (twInner cge).pt).map
(cgeChurchLeg Y) = W.ι [(twInner Y).pt, Y] ≫
(pre (ihomPowerEndFunctor.map (cgeChurchLeg Y))
).app [(twInner Y).pt, Y]`

This introduces `W.ι [(twInner Y).pt, Y]` at a
different index, leading to an infinite regress.
So Approach D2 alone is insufficient.

**Approach D3 (direct computation):** Define
`evalLeg Y := ihomEvalAt gs ≫ cgeChurchLeg Y` and
show `W.ι cge ≫ evalLeg Y = W.ι Y` by expressing
both sides as curried forms and comparing their
uncurried counterparts at each inner end projection.

This requires a **generalized
churchComponent_ihomEvalAt_eq** that works for
arbitrary wedge legs rather than specific ones.
Specifically, prove:
For any `φ : X → [(twInner cge).pt, cge]` and
the global section `gs`:
`φ ≫ ihomEvalAt gs ≫ cgeChurchLeg Y`
can be expressed in terms of `φ` composed with
the inner end structure.

This is essentially the enriched Yoneda lemma
at the morphism level.

**Current recommendation:** Begin implementing
Steps A-C (which are straightforward) and then
tackle Step D. Step D may require 2-3 additional
lemmas about the interaction of `ihomEvalAt` with
the inner/outer end structures.

##### Step E: Terminality uniqueness

If `h₁, h₂ : X → cge` both satisfy
`h_i ≫ cgeChurchLeg Y = W.ι Y` for all Y,
then `h₁ = h₂`.

Reduce to `CopowerGExtInj A ≫ h₁ =
CopowerGExtInj A ≫ h₂` via
`copowerGExtHomEndEquiv.injective`. At each A,
compose with `HasCopowers.inj s` and use the
`cgeChurchLeg` characterization to show both
sides equal the same `churchComponent`-based
expression.

##### Step F: Assemble iso via isTerminalWedgeIso

Use `isTerminalWedgeIso (churchProf G pt twInner)
twOuter.isTerminal cgeTerminal` to get
`ImpredicativeGExtObj ≅ CopowerGExtObj`. Show the
iso components match `bwd` and `fwd` by uniqueness
of the terminal lifts. Then both round-trip proofs
come for free from `isTerminalWedgeIso`.

##### Step G: Bundle NatIso (9b)

```lean
def powerEndGExtNatIso :
    ImpredicativeGExtFunctor G twInner twOuter ≅
    GExtFunctor G :=
  NatIso.ofComponents
    (fun pt => iso_from_step_F pt ≪≫ copowerGExtIso)
    (fun h => naturality_proof h)
```

Naturality follows from the naturality of
`copowerGExtIso` and the functorial maps of both
functors.

##### Step H: Final equivalence (9c)

```lean
def mendlerLambekPowerEndFullEquiv :
    PowerEndMendlerAlgebra G ≌
    ConventionalAlgebra
      (ImpredicativeGExtFunctor G twInner twOuter) :=
  mendlerLambekEndPowerEquiv.trans
    (Endofunctor.Algebra.equivOfNatIso
      powerEndGExtNatIso.symm)
```

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
