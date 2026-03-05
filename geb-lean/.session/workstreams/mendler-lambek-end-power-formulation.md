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
- `impredicativeGExt_backward_forward : bwd ≫ fwd = 𝟙`
  (line 2055, **TO PROVE**)

Proving `bwd ≫ fwd = 𝟙` is the remaining proof
obligation. This cannot be derived from
`fwd ≫ bwd = 𝟙` by abstract categorical reasoning
(section-retraction pairs do not automatically yield
isomorphisms). The proof uses the enriched Yoneda
argument via constructing a terminal
`churchProf`-wedge on `CopowerGExtObj`.

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

#### Derived facts (provable from helpers)

- `churchLift A s ≫ (bwd ≫ fwd) = churchLift A s`
  (from helpers 1 and 2, by
  `churchLift A s ≫ bwd ≫ fwd =
   inj(s) ≫ CopowerGExtInj A ≫ fwd =
   inj(s) ≫ HasCopowers.desc ... = churchLift A s`)
- `churchLift A s ≫ (bwd ≫ fwd) ≫ ι Y =
  churchComponent Y A s`
  (from above plus `twOuter.isLimit.fac`)

#### Sub-step 9b-i: Define `cgeChurchLeg`

```
def cgeChurchLeg Y :
    CopowerGExtObj G pt ⟶
      (churchProf G pt twInner).obj (op Y)).obj Y
```

The legs of a `churchProf`-wedge with apex
`CopowerGExtObj G pt`. Defined as the unique morphism
from the coend `cge` such that for each `A`:
`CopowerGExtInj A ≫ cgeChurchLeg Y =
 HasCopowers.desc (fun s => churchComponent Y A s)`.

Construction: use `(gExtEndPowerEquiv G pt
[(twInner Y).pt, Y]).symm` applied to the type-end
element whose components at `A` are
`HasPowers.lift (fun s => churchComponent Y A s)`.
Need to verify the wedge condition on the power-slice
profunctor, which follows from
`churchComponent_wedge` and `churchComponent_dinatural`.

Alternatively, use
`copowerGExtHomEndEquiv.symm (cowedge)` where the
cowedge at `A` is
`HasCopowers.desc (fun s => churchComponent Y A s)`.
The cowedge condition follows from
`churchComponent_dinatural`.

Once defined, verify:
`CopowerGExtInj A ≫ cgeChurchLeg Y =
HasCopowers.desc (fun s => churchComponent Y A s)`

#### Sub-step 9b-ii: `cgeChurchLeg` wedge condition

Prove for `f : Y₁ → Y₂`:
`cgeChurchLeg Y₁ ≫ (churchProf.obj (op Y₁)).map f =
 cgeChurchLeg Y₂ ≫ (churchProf.map f.op).app Y₂`

Both sides are maps `cge → [(twInner Y₁).pt, Y₂]`.
Reduce to checking at each `CopowerGExtInj A` using
`copowerGExtHomEndEquiv.injective`, then at each
`HasCopowers.inj s`. At each `(A, s)`, this follows
from `churchComponent_wedge`.

#### Sub-step 9b-iii: `cgeChurchLeg` factoring

Prove `fwd ≫ ι Y = cgeChurchLeg Y`, i.e., the
forward map followed by the terminal wedge projection
equals the independently-defined leg.

Both sides are maps `cge → [(twInner Y).pt, Y]`.
Reduce to checking at `CopowerGExtInj A` and
`HasCopowers.inj s`:
- LHS: `inj(s) ≫ CopowerGExtInj A ≫ fwd ≫ ι Y =
  inj(s) ≫ HasCopowers.desc (churchLift A) ≫ ι Y =
  churchLift A s ≫ ι Y = churchComponent Y A s`
  (by `inj_comp_forward`, `HasCopowers.fac`, fac)
- RHS: `inj(s) ≫ CopowerGExtInj A ≫ cgeChurchLeg Y =
  inj(s) ≫ HasCopowers.desc (churchComponent Y A) =
  churchComponent Y A s`
  (by the defining property of `cgeChurchLeg`)

#### Sub-step 9b-iv: Terminal wedge lift

Define the lift for the cge wedge: given a
`churchProf`-wedge W with apex X, the lift is
`h = W.ι cge ≫ ihomEvalAt gs : X → cge`.

Prove factoring: `h ≫ cgeChurchLeg Y = W.ι Y`.

This is: `W.ι cge ≫ ihomEvalAt gs ≫ cgeChurchLeg Y =
W.ι Y`.

Strategy: reduce `ihomEvalAt gs ≫ cgeChurchLeg Y`
to a form involving the wedge condition of W.

Using `ihomEvalAt_natural`:
`ihomEvalAt gs ≫ cgeChurchLeg Y =
 (ihom (twInner cge).pt).map (cgeChurchLeg Y) ≫
 ihomEvalAt gs`

(where the right `ihomEvalAt gs` now targets
`[(twInner Y).pt, Y]`)

Then `W.ι cge ≫ (ihom (twInner cge).pt).map
(cgeChurchLeg Y)` relates to the wedge condition of W
evaluated at a morphism `cge → [(twInner Y).pt, Y]`.

**Alternative factoring strategy**: Reduce to
checking at each inner end projection and each
coend injection, using the specific structure of
`ihomEvalAt`, `gs`, and `cgeChurchLeg`.

At injection `CopowerGExtInj A` and coprojection
`HasCopowers.inj s`:
`churchComponent cge A s ≫ ihomEvalAt gs ≫
cgeChurchLeg Y`
`= (inj(s) ≫ CopowerGExtInj A) ≫ cgeChurchLeg Y`
(by `churchComponent_ihomEvalAt_eq`)
`= inj(s) ≫ HasCopowers.desc (churchComponent Y A)`
(by defining property of `cgeChurchLeg`)
`= churchComponent Y A s`
(by `HasCopowers.fac`)

And `churchComponent Y A s = churchLift A s ≫ ι Y`.

So precomposing the LHS with `churchLift A s` gives
`churchComponent Y A s = churchLift A s ≫ ι Y`,
which matches `churchLift A s ≫ W.ι Y` when
`W = twOuter.wedge`.

For a GENERAL wedge W: we need
`W.ι cge ≫ ihomEvalAt gs ≫ cgeChurchLeg Y = W.ι Y`.

This does NOT follow from the injection-level
argument because the `churchLift` family is specific
to `twOuter.wedge`, not a general wedge.

**Revised strategy for terminality:**

The factoring for a general W requires showing that
`ihomEvalAt gs ≫ cgeChurchLeg Y` has a specific
relationship to the `churchProf` wedge condition.

Define: `evalLeg Y := ihomEvalAt gs ≫ cgeChurchLeg Y
: [(twInner cge).pt, cge] → [(twInner Y).pt, Y]`.

Need to show: for any churchProf-wedge W with
apex X, `W.ι cge ≫ evalLeg Y = W.ι Y`.

This is equivalent to showing `evalLeg Y` is the
morphism that the churchProf wedge condition
prescribes between components cge and Y.

**Key decomposition of `evalLeg Y`**: Using curry
bijectivity, `evalLeg Y` is determined by its
uncurried form
`[(twInner cge).pt, cge] ⊗ (twInner Y).pt → Y`.

The proof reduces to showing this equals a specific
composition involving the inner end projections,
braiding, evaluation, and power projections — which
is how `churchComponent` is defined.

This decomposition is a generalization of
`churchComponent_ihomEvalAt_eq` from specific
injection-level morphisms to the full morphism
`evalLeg Y`.

**Further investigation needed for sub-step 9b-iv.**
This is the hard step and may require additional
lemmas about the interaction of `ihomEvalAt` with
the inner end structure. If proving terminality of
the cge wedge proves intractable, an alternative is:

**Alternative approach (bypass terminality):**
Prove `bwd ≫ fwd = 𝟙` directly by:
1. Apply `Multifork.IsLimit.hom_ext` to reduce to
   per-Y components
2. For each Y, show
   `ι cge ≫ ihomEvalAt gs ≫ fwd ≫ ι Y = ι Y`
3. Use `ihomEvalAt_natural` to rewrite
   `ihomEvalAt gs ≫ (fwd ≫ ι Y)` as
   `(ihom _).map (fwd ≫ ι Y) ≫ ihomEvalAt gs`
4. Use the twOuter wedge condition with
   Y₁ = cge and f = (fwd ≫ ι Y) (but note f goes
   from cge to [(twInner Y).pt, Y], not from cge
   to Y, so the wedge condition applies with Y₂ =
   [(twInner Y).pt, Y])
5. Continue reducing using wedge conditions and
   `ihomEvalAt` properties

Both approaches require further exploration. The
terminal-wedge approach is cleaner architecturally
but may require the same amount of proof work.

#### Sub-step 9b-v: Terminal wedge uniqueness

Prove uniqueness of the lift. If `h₁, h₂ : X → cge`
both satisfy `h_i ≫ cgeChurchLeg Y = W.ι Y`, then
`h₁ = h₂`.

Reduce to showing
`CopowerGExtInj A ≫ h₁ = CopowerGExtInj A ≫ h₂`
for all A (using `copowerGExtHomEndEquiv.injective`),
then `HasCopowers.inj s ≫ CopowerGExtInj A ≫ h_i`
for all s (using `HasCopowers.ext`), which equals
`HasCopowers.inj s ≫ HasCopowers.desc
(churchComponent Y A) ≫ (ihomEvalAt gsY)`... this
needs further development.

Uniqueness may follow from the Yoneda embedding
being faithful, or from the inner end structure.

#### Sub-step 9b-vi: Bundle component iso

Once `impredicativeGExt_backward_forward` is proved:
```
def impredicativeGExtCopowerIso pt :
    ImpredicativeGExtObj G pt twInner twOuter ≅
    CopowerGExtObj G pt where
  hom := bwd
  inv := fwd
  hom_inv_id := impredicativeGExt_backward_forward
  inv_hom_id := copowerGExt_backward_forward
```

Component iso for nat iso:
```
def impredicativeGExtGExtIso pt :
    ImpredicativeGExtObj G pt twInner twOuter ≅
    GExtObj G pt :=
  impredicativeGExtCopowerIso pt ≪≫ copowerGExtIso
```

#### Sub-step 9b-vii: Naturality

Prove naturality of the component isos. For
`h : pt₁ → pt₂`:
`ImpredicativeGExtFunctor.map h ≫
 (impredicativeGExtGExtIso pt₂).hom =
 (impredicativeGExtGExtIso pt₁).hom ≫
 GExtFunctor.map h`

This involves showing that the backward map `bwd`
commutes with the functorial maps of both functors,
up to the `copowerGExtIso` components.

#### Sub-step 9b-viii: Bundle NatIso

```
def powerEndGExtNatIso :
    ImpredicativeGExtFunctor G twInner twOuter ≅
    GExtFunctor G :=
  NatIso.ofComponents
    (fun pt => impredicativeGExtGExtIso pt)
    (fun h => naturality_proof h)
```

#### Sub-step 9c: Final equivalence

```
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
