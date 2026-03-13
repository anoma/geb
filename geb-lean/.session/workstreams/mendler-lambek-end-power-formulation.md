# Workstream: Mendler-Lambek Equivalence via Ends and Powers

## Status

Phases 1-3 complete. Phase 4 tasks 10a-10d complete.

File: `GebLean/MendlerLambekPresheaf.lean`. Two
equivalences stated for `C = E ⥤ Type (max w₁ v₁ u₁)`:

1. `presheafMendlerAlgPowerEndEquiv`:
   unconditional (copowers/powers automatic).
2. `presheafMendlerLambekEndPowerEquiv`:
   requires `HasAllHomToProfCoends G`.

The `bwdFwd`-parameterized impredicative
equivalence (`mendlerLambekImpredicativeEquiv`,
`impredicativeGExtCopowerIso`,
`impredicativeGExtNatIso`, etc.) was removed.
It required a parametricity condition that could
not be discharged in predicative type theory.
The remaining `ImpredicativeGExtIso` section in
`MendlerLambekEndPower.lean` retains the
one-direction morphisms
(`impredicativeGExtToCopowerGExt`,
`copowerGExtToImpredicativeGExt`,
`copowerGExt_backward_forward`) which do not
require `bwdFwd`.

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
- [x] 9b. Define `impredicativeGExtCopowerIso`
  (per-point iso from ImpredicativeGExtObj to
  CopowerGExtObj, parameterized by `bwdFwd`),
  `impredicativeGExtIso` (composed per-point iso
  to GExtObj), and `impredicativeGExtNatIso :
  ImpredicativeGExtFunctor G twInner twOuter ≅
  GExtFunctor G` (parameterized by `bwdFwd` and
  `natBwd`).
- [x] 9c. Define `mendlerLambekImpredicativeEquiv :
  PowerEndMendlerAlgebra G ≌
    ConventionalAlgebra
      (ImpredicativeGExtFunctor G twInner twOuter)`
  using `mendlerLambekEndPowerEquiv` composed with
  `Endofunctor.Algebra.equivOfNatIso`.
  Parameterized by `bwdFwd` and `natBwd`.

#### Open hypothesis

The nat iso and equivalence in 9b-9c are parameterized
by one hypothesis:

1. `bwdFwd : ∀ pt, bwd_pt ≫ fwd_pt = 𝟙` — the
   backward-forward iso condition. Equivalent to the
   gap `ι_Z_ihomEvalAt_eq_ι_Y`. Requires the enriched
   Yoneda identity for Church encodings.

The naturality of `bwd` (`natBwd`) was previously a
separate hypothesis but is now derived from `bwdFwd`
via `natBwd_of_bwdFwd` (line ~2667), using the
algebraic identity:

```text
F.map h ≫ bwd₂
  = (bwd₁ ≫ fwd₁) ≫ (F.map h ≫ bwd₂)
  = bwd₁ ≫ (fwd₁ ≫ F.map h ≫ bwd₂)
  = bwd₁ ≫ (G'.map h ≫ fwd₂ ≫ bwd₂)
  = bwd₁ ≫ G'.map h
```

This uses `copowerGExtToImpredicativeGExt_natural`
(line ~2633, proved abstractly via
`HasTerminalWedge.hom_ext` and
`cgeChurchLeg_natural_pt`).

The naturality of `copowerCoendGExtNatIso` (the iso
from CopowerCoendGExt to GExt) is proved by
construction.

#### Universe constraint

Discharging the hypotheses for `Type v` faces
a universe mismatch: the abstract framework uses
`{C : Type v} [Category.{v} C]` (small category),
but `Type v : Type (v+1)` is inherently large. All
required instances (`MonoidalCategory`, `MonoidalClosed`,
`BraidedCategory`, `HasCopowers`, `HasPowers`) exist
for `Type v` — see `MendlerLambekEndPowerTypeV.lean` —
but the objects live in `Type (v+1)`, not `Type v`.

To enable concrete instantiation, the framework would
need to be generalized to `{C : Type u} [Category.{v} C]`
with separate object and morphism universe parameters.

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
4. **Idempotent argument**: `e := bwd ≫ fwd` is
   idempotent (`e ≫ e = e`) since
   `bwd ≫ (fwd ≫ bwd) ≫ fwd = bwd ≫ fwd`.
   But showing `e = 𝟙` from idempotence requires
   additional structure (e.g., Karoubi envelope
   properties) not available in a general category.
5. **Left-cancellation of fwd from
   cgeChurchLeg_Z_ihomEvalAt**: The proved lemma
   `cgeChurchLeg Z ≫ ihomEvalAt(gs ≫ m) =
   cgeChurchLeg Y` expands to
   `fwd ≫ ι Z ≫ ihomEvalAt(gs ≫ m) = fwd ≫ ι Y`.
   Left-cancelling `fwd` would give the goal, but
   `fwd ≫ bwd = 𝟙` makes `fwd` a **split mono**
   (right-cancellable), NOT left-cancellable (epi).
   Left-cancellation requires `fwd` epi, equivalent
   to the goal.
6. **Wedge condition at ihomEvalAt(gs ≫ m)**:
   Using the wedge condition of `twOuter` at the
   morphism `ihomEvalAt(gs ≫ m) : Z ⟶ Y` gives
   an equation involving `ι Z` and `ι Y`, but in
   `[innerEnd_Z, Y]` (not `[innerEnd_Y, Y]`), and
   introduces `innerEndMap(ihomEvalAt(gs ≫ m))`
   which does not simplify.

The proof genuinely requires the **enriched Yoneda
argument** via the specific terminal wedge and
coend structures, or proving terminality of the
`cge`-wedge directly.

#### Promising approach: wedge naturality + uncurrying

The wedge condition of `twOuter` at the morphism
`ihomEvalAt(y') : Z ⟶ Y` (for any
`y' : 𝟙_ C ⟶ innerEnd_Y`) gives, after composing
with `ihomEvalAt(gs ≫ m)`:

```text
ι Z ≫ ihomEvalAt(gs ≫ m) ≫ ihomEvalAt(y')
= ι Y ≫ ihomEvalAt(gs ≫ m ≫
    innerEndMap(ihomEvalAt(y')))
```

If `gs ≫ m ≫ innerEndMap(ihomEvalAt(y')) = y'`
for all `y' : 𝟙_ C ⟶ innerEnd_Y`, then the
RHS equals `ι Y ≫ ihomEvalAt(y')`, giving:

```text
ι Z ≫ ihomEvalAt(gs ≫ m) ≫ ihomEvalAt(y')
= ι Y ≫ ihomEvalAt(y')
```

for all `y'`. By `curry'_injective`, this
gives `ι Z ≫ ihomEvalAt(gs ≫ m) = ι Y`
(at the enriched level, not just at global
elements).

The enriched version of the identity
`gs ≫ m ≫ innerEndMap(ihomEvalAt(y')) = y'`
is: the composition

```text
innerEnd_Y → (cge ⟶ Y)
            → (innerEnd_cge ⟶ innerEnd_Y)
```

given by `y' ↦ cgeChurchLeg Y ≫ ihomEvalAt(y')`
then `f ↦ gs ≫ innerEndMap(f)`, should be the
identity `innerEnd_Y ⟶ innerEnd_Y`.

This is a form of the enriched Yoneda lemma:
`gs` is the "universal element" (corresponding
to `𝟙_cge` via `gExtEndPowerEquiv`), and
mapping along the church leg composed with
evaluation recovers the original element.

To prove this enriched identity, it may be
helpful to:

1. Prove it first in `Type v` (where it
   reduces to pointwise computation with
   function application)
2. Identify which categorical axioms are used
   (monoidal closure, adjunction counit = eval,
   mates / conjugate equivalences from
   `MonoidalClosed.pre`)
3. Generalize using the same axioms in
   arbitrary `C`

`MonoidalClosed.pre`
is defined via a conjugate equivalence that
relates natural transformations and corresponds
to the theory of mates. Mathlib may have lemmas
about mates that capture the needed identity.

#### Uniqueness of terminal lift into cge

Even without proving existence (the factoring
condition), we can prove UNIQUENESS of the
terminal lift `h : X ⟶ cge` for the
`cgeChurchLeg` wedge:

If `h₁ ≫ cgeChurchLeg Y = h₂ ≫ cgeChurchLeg Y`
for all Y, then (at Y = cge):
`h₁ ≫ cgeChurchLeg_cge = h₂ ≫ cgeChurchLeg_cge`.
Composing with `ihomEvalAt(gs)`:
`h₁ ≫ cgeChurchLeg_cge ≫ ihomEvalAt(gs) =
 h₂ ≫ cgeChurchLeg_cge ≫ ihomEvalAt(gs)`.
And `cgeChurchLeg_cge ≫ ihomEvalAt(gs) =
fwd ≫ ι_cge ≫ ihomEvalAt(gs) = fwd ≫ bwd =
𝟙_cge` (from `copowerGExt_backward_forward`).
So `h₁ = h₂`. This means: once the factoring
condition is established for ANY morphism, it
determines the morphism uniquely.

#### Available helper lemmas (all proved)

1. `churchLift_comp_backward` (line ~1940):
   `churchLift A s ≫ bwd = inj(s) ≫
   CopowerGExtInj A`
2. `inj_comp_forward` (line ~1978):
   `CopowerGExtInj A ≫ fwd = HasCopowers.desc
   (fun s => churchLift A s)`
3. `churchComponent_ihomEvalAt_eq` (line ~1803):
   `churchComponent cge A s ≫ ihomEvalAt gs =
   inj(s) ≫ CopowerGExtInj A`
4. `churchComponent_wedge` (line ~1609):
   wedge condition for `churchComponent`
5. `churchComponent_dinatural` (line ~1663):
   dinaturality of `churchComponent`
6. `ihomEvalAt_natural` (line ~2038):
   `(ihom X).map f ≫ ihomEvalAt gs =
   ihomEvalAt gs ≫ f`
7. `cgeChurchLeg` (line ~2088):
   `cge ⟶ [(twInner Y).pt, Y]`, defined via
   `gExtEndPowerEquiv.symm`
8. `cgeChurchLeg_wedge` (proved):
   wedge condition for `cgeChurchLeg`
9. `fwd_comp_ι_eq_cgeChurchLeg` (proved):
   `fwd ≫ ι Y = cgeChurchLeg Y`
10. `bwdGlobalSection` (line ~2199):
    `gs : 𝟙_ C ⟶ (twInner cge).wedge.pt`
11. `innerEndMap` (line ~2211):
    `m : innerEnd_cge ⟶ innerEnd_Z`
    where `Z = [innerEnd_Y, Y]`
12. `pre_comp_ihomEvalAt` (line ~2228):
    `(pre h).app Z ≫ ihomEvalAt gs =
    ihomEvalAt (gs ≫ h)`
13. `ι_cge_ihomMap_cgeChurchLeg` (line ~2243):
    `ι cge ≫ (ihom innerEnd_cge).map
    (cgeChurchLeg Y) =
    ι Z ≫ (pre m).app Z`
    (the outer wedge condition at
    `cgeChurchLeg Y`)
14. `inj_inj_cgeChurchLeg` (line ~2270):
    `inj(s) ≫ CopowerGExtInj A ≫
    cgeChurchLeg Y = churchComponent Y A s`
15. `churchComponent_Z_ihomEvalAt` (line ~2298):
    `churchComponent Z A s ≫
    ihomEvalAt(gs ≫ m) =
    churchComponent Y A s`
    (per-component enriched Yoneda chain)
16. `cgeChurchLeg_Z_ihomEvalAt` (line ~2337):
    `cgeChurchLeg Z ≫ ihomEvalAt(gs ≫ m) =
    cgeChurchLeg Y`
    (coend-level enriched Yoneda chain,
    lifted from 15 via joint epicity)
17. `copowerGExtIso_hom_eq_id` (line ~2404):
    `(copowerGExtIso G pt).hom = 𝟙`
18. `copowerGExtIso_inv_eq_id` (line ~2428):
    `(copowerGExtIso G pt).inv = 𝟙`
19. `CopowerCoendGExtFunctor_map_eq` (line ~2438):
    `(CopowerCoendGExtFunctor G).map h =
    (GExtFunctor G).map h`
20. `GExtInj_eq_inj_comp_copowerGExtInj`
    (line ~2448):
    `GExtInj G pt A s =
    HasCopowers.inj _ s ≫ CopowerGExtInj G pt A`
21. `churchComponent_churchProfMapPt`
    (line ~2375):
    `churchComponent pt₁ tw₁ Y A s ≫
    churchProfMapPt h = churchComponent pt₂ tw₂
    Y A (s ≫ h)`
22. `cgeChurchLeg_natural_pt` (line ~2470):
    `GExtFunctor.map h ≫ cgeChurchLeg pt₂ tw₂ Y =
    cgeChurchLeg pt₁ tw₁ Y ≫
    churchProfMapPt h`
23. `copowerGExtToImpredicativeGExt_natural`
    (line ~2633):
    `CopowerCoendGExt.map h ≫ fwd₂ =
    fwd₁ ≫ ImprGExt.map h`
24. `natBwd_of_bwdFwd` (line ~2667):
    Derives `natBwd` from `bwdFwd` +
    `copowerGExtToImpredicativeGExt_natural`

#### Current gap: `bwdFwd`

**Status**: The gap is currently handled as a
hypothesis `bwdFwd` parameterizing
`impredicativeGExtCopowerIso`,
`impredicativeGExtNatIso`, and
`mendlerLambekImpredicativeEquiv`. The naturality
hypothesis `natBwd` was eliminated via
`natBwd_of_bwdFwd` (derived from `bwdFwd` +
`copowerGExtToImpredicativeGExt_natural`).

**Statement**: For `Z = [innerEnd_Y, Y]`:

```lean
Multifork.ι twOuter.wedge Z ≫
  ihomEvalAt (gs ≫ m) =
Multifork.ι twOuter.wedge Y
```

Equivalently (using `HasTerminalWedge.hom_ext`):

```lean
impredicativeGExtToCopowerGExt ≫
  copowerGExtToImpredicativeGExt = 𝟙
```

**Usage chain**:
The `bwdFwd` hypothesis is used directly by
`impredicativeGExtCopowerIso` (as `hom_inv_id`),
`natBwd_of_bwdFwd`, `impredicativeGExtNatIso`,
and `mendlerLambekImpredicativeEquiv`.

**What the existing lemmas give us**:
Lemma 16 (`cgeChurchLeg_Z_ihomEvalAt`) gives
`cgeChurchLeg Z ≫ ihomEvalAt(gs ≫ m) =
cgeChurchLeg Y`, which by lemma 9 equals
`fwd ≫ ι Z ≫ ihomEvalAt(gs ≫ m) = fwd ≫ ι Y`.
Left-cancelling `fwd` would give the goal, but
`fwd` is mono (split mono from
`fwd ≫ bwd = 𝟙`), not epi.

**The mathematical situation**:
The equation relates two morphisms
`ImpredicativeGExtObj ⟶ [innerEnd_Y, Y]`.
Two morphisms `f, g : X ⟶ [W, Y]` are equal
iff `uncurry(f) = uncurry(g) : X ⊗ W ⟶ Y`
(by `curry'_injective` from mathlib).

So we need:
`uncurry(ι Z ≫ ihomEvalAt(gs ≫ m)) =
 uncurry(ι Y) : ImpredicativeGExtObj ⊗
 innerEnd_Y ⟶ Y`

The inner end `innerEnd_Y = (twInner Y).wedge.pt`
has projections `π_A` that are jointly mono (as
a limit cone). One could try to show the uncurried
versions agree when composed with `𝟙 ⊗ π_A` for
each `A`, reducing to a statement about the
profunctor components.

**Reduction chain**: By `HasTerminalWedge.hom_ext`,
`bwdFwd` reduces to:
`∀ Y, bwd ≫ cgeChurchLeg Y = ι Y`
Using `fwd_comp_ι_eq_cgeChurchLeg`, this is:
`∀ Y, bwd ≫ fwd ≫ ι Y = ι Y`
Unfolding `bwd = ι cge ≫ ihomEvalAt gs` and
applying `ihomEvalAt_natural` then the wedge
condition `ι_cge_ihomMap_cgeChurchLeg` then
`pre_comp_ihomEvalAt`, this reduces to:
`∀ Y, ι Z ≫ ihomEvalAt(gs ≫ m) = ι Y`
where `Z = [innerEnd_Y, Y]`,
`gs = bwdGlobalSection`, `m = innerEndMap Y`.

**Approaches tried**:

1. **Left-cancellation of `fwd`**: We have
   `fwd ≫ (ι Z ≫ ihomEvalAt(gs ≫ m)) = fwd ≫ ι Y`
   (from `cgeChurchLeg_Z_ihomEvalAt` +
   `fwd_comp_ι_eq_cgeChurchLeg`), but `fwd` is
   mono (split mono), not epi. Left cancellation
   requires epi.

2. **`curry'_injective` + inner end extensionality**:
   `curry'_injective` converts the goal to
   uncurried form (`ImprGExt ⊗ innerEnd_Y ⟶ Y`),
   but decomposing `innerEnd_Y` via limit
   projections and tensor products does not simplify
   in a general monoidal closed category (tensor
   does not preserve joint monomorphisms in general).

3. **Outer wedge condition at
   `ihomEvalAt(gs ≫ m) : Z ⟶ Y`**: Gives
   `ι Z ≫ (ihom innerEnd_Z).map (ihomEvalAt(gs ≫ m))
   = ι Y ≫ (pre (innerEndMap(ihomEvalAt(gs ≫ m)))).app Y`,
   but this involves the internal hom's functorial
   action, not the morphism itself, and does not
   close the gap.

4. **Terminality of `(cge, cgeChurchLeg)`**: For a
   general wedge `(X, legs)`, the factoring condition
   reduces to `legs Z ≫ ihomEvalAt(gs ≫ m) = legs Y`,
   the same structural gap with `legs` replacing `ι`.

5. **Idempotent argument**: `bwd ≫ fwd` is
   idempotent but showing `e = 𝟙` from idempotence
   requires Karoubi properties.

6. **Section-retraction algebra**: Invalid.

**Remaining viable approaches**:

1. **Type v instantiation**: Prove `bwdFwd` for
   `C = Type v` where the gap reduces to function
   extensionality. Possibly-unnecessary universe constraint:
   framework uses `{C : Type v} [Category.{v} C]`
   but `Type v : Type (v+1)`. Requires generalizing
   to `{C : Type u} [Category.{v} C]`, which used to
   fail because `typeEnd` produced `Type (max u v)`,
   but that has been fixed.

2. **Accept as hypothesis** (CURRENT APPROACH):
   `bwdFwd` is parameterized as a hypothesis
   throughout Phases B and C. The construction
   compiles and all downstream definitions
   (`impredicativeGExtCopowerIso`,
   `impredicativeGExtNatIso`,
   `mendlerLambekImpredicativeEquiv`) are complete.

**Approaches confirmed not viable**:

1. **Separator hypothesis**: Adding
   `IsSeparator (𝟙_ C)` does NOT suffice. To show
   `p ≫ ι_Y = ι_Y` (where `p = bwd ≫ fwd`), the
   separator reduces to showing
   `h ≫ p ≫ ι_Y = h ≫ ι_Y` for all `h : 𝟙 → Imp`.
   Using the wedge condition and
   `curry'_ihomEvalAt`, the LHS reduces to
   `(h ≫ bwd) ≫ cgeChurchLeg Y`, and by
   `fwd_comp_ι_eq_cgeChurchLeg` this equals
   `h ≫ p ≫ ι_Y` — circular. The separator tests
   an endomorphism of the limit against itself.

2. **Enriched Yoneda at global section level**:
   The per-component chain
   (`churchComponent_Z_ihomEvalAt`) proves the
   enriched Yoneda identity at the COEND level
   (`cgeChurchLeg_Z_ihomEvalAt`), which factors
   through `fwd`. Since `fwd` is a split mono
   (from `fwd ≫ bwd = 𝟙`), it is mono (left-
   cancellable), but NOT epi (right-cancellable),
   so the equation `fwd ≫ X = fwd ≫ Y` does NOT
   imply `X = Y`.

**Analysis: why `bwdFwd` is a parametricity
condition**:

The statement `bwd ≫ fwd = 𝟙_Imp` asserts that
every element of the Church encoding
`∫_Y [innerEnd_Y, Y]` is representable — i.e.,
arises from an element of the coend `cge` via
`fwd`. This is the categorical analogue of the
parametricity / free theorem for Church encodings
in System F. Parametricity is a meta-property
of the type system (or, categorically, a
property of the specific category), not derivable
from the axioms of monoidal closed categories.
It holds in Type v (function extensionality),
presheaf categories (Yoneda), and other
categories with sufficient structure, but
not in all monoidal closed categories.

**Added utility**: `curry'_ihomEvalAt` (line ~1803)
proves `curry' f ≫ ihomEvalAt p = p ≫ f`,
relating curried morphisms to evaluation at global
sections. Used in the analysis but not in the
gap proof itself.

#### Proof chain for `churchComponent_Z_ihomEvalAt`

This is the enriched Yoneda chain at the
per-component level. The proof proceeds:

1. `pre_comp_ihomEvalAt` expands
   `ihomEvalAt(gs ≫ m)` into
   `(pre m).app Z ≫ ihomEvalAt gs`
2. `churchComponent_wedge.symm` swaps from
   the `Z`-component to the `cge`-component:
   `churchComponent Z A s ≫ (pre m).app Z =
   churchComponent cge A s ≫
   (ihom innerEnd_cge).map (cgeChurchLeg Y)`
3. `ihomEvalAt_natural` commutes:
   `(ihom innerEnd_cge).map (cgeChurchLeg Y) ≫
   ihomEvalAt gs = ihomEvalAt gs ≫
   cgeChurchLeg Y`
4. `churchComponent_ihomEvalAt_eq` evaluates
   at `cge`:
   `churchComponent cge A s ≫ ihomEvalAt gs =
   inj(s) ≫ CopowerGExtInj A`
5. `inj_inj_cgeChurchLeg` recovers:
   `inj(s) ≫ CopowerGExtInj A ≫
   cgeChurchLeg Y = churchComponent Y A s`

#### Proof chain for `cgeChurchLeg_Z_ihomEvalAt`

Lifts the per-component chain to the coend level:

1. `copowerGExtHomEndEquiv.injective` reduces
   to showing equality of end elements
2. `Subtype.ext` + `funext A` reduces to
   per-`A` equation
3. `HasCopowers.ext` reduces to per-`(A, s)`
   equation
4. `change` converts `((HomToProf pt).obj
   (op A)).obj A` to `(A ⟶ pt)` for
   `reassoc_of%` matching
5. `reassoc_of% inj_inj_cgeChurchLeg` +
   `inj_inj_cgeChurchLeg` converts to
   `churchComponent` form
6. `churchComponent_Z_ihomEvalAt` closes

#### Lean-specific technical notes

- `churchProf.map f` is definitionally
  `MonoidalClosed.pre (ihomPowerEndFunctor.map
  f)`, but `rw` cannot match through this
  definitional equality. Use `have` with
  explicit type annotation to let the unifier
  handle it.
- `HasCopowers.inj (A ⟶ pt)` vs
  `HasCopowers.inj (((HomToProf pt).obj
  (op A)).obj A)` are definitionally equal but
  syntactically different. Use `change` before
  `rw`/`reassoc_of%` to convert.
- `reassoc_of%` creates the `_assoc` variant
  of a lemma for rewriting in right-associated
  chains.

#### Proof strategy: terminal wedge on cge

Construct a terminal `churchProf`-wedge with apex
`CopowerGExtObj G pt`, then use `isTerminalWedgeIso`
to get `ImpredicativeGExtObj ≅ CopowerGExtObj` with
both round-trips free. Match the iso components with
`fwd` and `bwd`.

##### Step A: Define `cgeChurchLeg Y` (DONE)

`cgeChurchLeg Y : cge → [(twInner Y).pt, Y]`
defined at line ~2088 via `gExtEndPowerEquiv.symm`.
Satisfies:
`CopowerGExtInj A ≫ cgeChurchLeg Y =
 HasCopowers.desc (fun s => churchComponent Y A s)`

##### Step B: cgeChurchLeg wedge condition (DONE)

`cgeChurchLeg_wedge` (proved). Reduced to
per-`(A, s)` level via
`copowerGExtHomEndEquiv.injective` +
`HasCopowers.ext`, closed by
`churchComponent_wedge`.

##### Step C: Show `fwd ≫ ι Y = cgeChurchLeg Y`

(DONE)

`fwd_comp_ι_eq_cgeChurchLeg` (proved).

##### Step D: Terminality factoring

For a `churchProf`-wedge `(X, legs)`, the
candidate lift is
`h := legs cge ≫ ihomEvalAt gs : X → cge`.
The factoring condition
`h ≫ cgeChurchLeg Y = legs Y` reduces to
`legs cge ≫ ihomEvalAt gs ≫ cgeChurchLeg Y =
legs Y`.

For `X = ImpredicativeGExtObj` and `legs = ι`,
this is exactly `bwd ≫ cgeChurchLeg Y = ι Y`,
which reduces to `ι_Z_ihomEvalAt_eq_ι_Y`.
This is the gap.

For a GENERAL wedge `(X, legs)`, the equation
involves `legs cge ≫ ihomEvalAt gs ≫
cgeChurchLeg Y = legs Y`. The wedge condition
of `legs` at the morphism `cgeChurchLeg Y`
gives:
`legs cge ≫ (ihom innerEnd_cge).map
 (cgeChurchLeg Y) = legs Z ≫
 (pre m).app Z`

By `ihomEvalAt_natural` and `pre_comp_ihomEvalAt`,
this transforms to:
`legs cge ≫ ihomEvalAt gs ≫ cgeChurchLeg Y =
 legs Z ≫ ihomEvalAt(gs ≫ m)`

So the factoring condition becomes:
`legs Z ≫ ihomEvalAt(gs ≫ m) = legs Y`

This is the SAME equation as
`ι_Z_ihomEvalAt_eq_ι_Y` but with `legs` in
place of `ι`. The gap is structural, not
specific to `twOuter`.

The gap is that `ihomEvalAt(gs ≫ m) : Z ⟶ Y`
(where `Z = [innerEnd_Y, Y]`) should act as
a "counit" that, when composed with any
`churchProf`-wedge leg at `Z`, recovers the
leg at `Y`. This is the enriched Yoneda
identity for the Church encoding.

##### Step E: Terminality uniqueness (STRAIGHTFORWARD)

If `h₁, h₂ : X → cge` both satisfy
`h_i ≫ cgeChurchLeg Y = W.ι Y` for all Y,
then `h₁ = h₂`.

Reduce via `copowerGExtHomEndEquiv.injective`

- `HasCopowers.ext`. At each `(A, s)`:
`h_i ≫ CopowerGExtInj A ≫ HasCopowers.inj s =
 h_i ≫ (something)`. Use
`inj_inj_cgeChurchLeg` to show both sides
equal the same `churchComponent`-based
expression.

##### Step F: Assemble iso via isTerminalWedgeIso

Use the terminal wedge iso machinery. Both
round-trip proofs come for free. Match the
iso components with `fwd` and `bwd` by
uniqueness of the terminal lifts.

##### Step G: Bundle NatIso (9b)

```lean
def powerEndGExtNatIso :
    ImpredicativeGExtFunctor G twInner twOuter ≅
    GExtFunctor G :=
  NatIso.ofComponents
    (fun pt => iso_from_step_F pt ≪≫ copowerGExtIso)
    (fun h => naturality_proof h)
```

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

Three equivalences are stated:

1. `presheafMendlerAlgPowerEndEquiv` — unconditional
2. `presheafMendlerLambekEndPowerEquiv` —
   requires `HasAllHomToProfCoends G`
3. `presheafMendlerLambekImpredicativeEquiv` —
   requires `HasAllCopowerProfCoends G`,
   `HasTerminalWedge` (inner/outer), `bwdFwd`

#### Large-(co)end obstacle

The `HasTerminalWedge` and restricted-coend
hypotheses involve (co)ends indexed by the
presheaf category itself. The `typeEnd`
construction for `J : Type u, Category.{v} J`
and `F : Jᵒᵖ ⥤ J ⥤ Type w` produces
`Type (max u w)`. When `J` is the presheaf
category, `u = w + 1 > w`, so the end lives
in a strictly larger universe. This is the
impredicativity barrier: Church encodings
quantify over all types in the ambient
universe, which inherently requires a universe
bump in predicative type theory.

For abstract `G`, the hypotheses are supplied
parametrically. For specific `G` (e.g.,
polynomial or representable functors), the ends
may have small representatives, enabling
discharge of the hypotheses.
