# Workstream: Coend-End Correspondence

## Status

In Progress

## Context

The Mendler algebra code uses coends and their relationship to ends. We need to
properly formalize:

1. The coend elimination rule: `Hom(∫^A P(A,A), Y) ≅ ∫_A Hom(P(A,A), Y)`
2. The co-Yoneda characterization of coends in terms of natural transformations
3. The connection between our weighted ends/coends and mathlib's ends/coends

The current `CoendAsNatTransformations` section in `RestrictedCoendAsColimit.lean`
has partial definitions but doesn't complete the proofs or make the end structure
explicit.

### Generalized Elimination Hierarchy

The elimination rules form a hierarchy of increasing generality:

#### Level 1: Weighted Colimit → Weighted Limit

The most general formula. For weight `W : J^op → V` and diagram `F : J → C`:

```text
C(W * F, Y) ≅ {W, C(F(-), Y)}
```

where `W * F` is the W-weighted colimit of F, and `{W, C(F(-), Y)}` is the
W-weighted limit of the functor `j ↦ C(F(j), Y)`.

#### Level 2: Weighted Coend → Weighted End

Special case where F is a profunctor `P : C^op × C → D`:

```text
Hom(∫^A W(A) ⊗ P(A,A), Y) ≅ ∫_A [W(A), Hom(P(A,A), Y)]
```

where `⊗` is tensor/copower and `[-,-]` is cotensor/power.

#### Level 3: Ordinary Coend → Ordinary End

Special case where `W = terminalProfunctor` (since `PUnit ⊗ X ≅ X` and
`[PUnit, Y] ≅ Y`):

```text
Hom(∫^A P(A,A), Y) ≅ ∫_A Hom(P(A,A), Y)
```

### Implementation Strategy

Since our code has:

- `WeightedCone`/`WeightedCocone` as the general weighted limit/colimit cones
- `WeightedWedge`/`WeightedCowedge` as special cases for ends/coends
- `terminalProfunctor` giving ordinary ends/coends from weighted ones

We should formalize Level 1 first (weighted colimit elimination via weighted
limits), then derive Level 2 and Level 3 as special cases. This requires:

1. Powers (dual to copowers) for the cotensor `[-,-]` operation
2. The elimination isomorphism at the weighted cone/cocone level
3. Specialization to wedges/cowedges for ends/coends

### Powers and Copowers as Weighted Limits/Colimits

Powers and copowers are weighted limits/colimits over the terminal category:

- **Copower**: `S ·. X` = weighted colimit of `1 → C` picking X, weighted by
  `1^op → Set` picking S
- **Power**: `X ^. S` = weighted limit of `1 → C` picking X, weighted by
  `1 → Set` picking S

This provides a consistency check for our definitions and allows deriving
properties of powers/copowers from the general weighted limit/colimit theory.

### Tensor-Hom Adjunction (Copower-Power Adjunction)

When a category has both copowers and powers, they are adjoint:

```text
C(S ·. X, Y) ≅ Set(S, C(X, Y)) ≅ C(X, Y ^. S)
```

This is the "elimination rule for copowers using powers" - morphisms out of a
copower correspond to morphisms into a power.

### Weighted (Co)Limits via Ordinary (Co)Limits + Powers/Copowers

For categories with powers/copowers and ordinary limits/colimits:

```text
{W, F} ≅ ∫_j F(j) ^. W(j)     (weighted limit via end of powers)
W * F ≅ ∫^j W(j) ·. F(j)      (weighted colimit via coend of copowers)
```

These formulas express weighted (co)limits as ends/coends of powers/copowers,
providing an alternative construction when the category has these structures.

References:

- [nLab: weighted colimit](https://ncatlab.org/nlab/show/weighted+colimit)
- [nLab: weighted limit](https://ncatlab.org/nlab/show/weighted+limit)
- [nLab: end](https://ncatlab.org/nlab/show/end)
- [nLab: copower](https://ncatlab.org/nlab/show/copower)
- [nLab: power](https://ncatlab.org/nlab/show/power)
- [Emily Riehl: Weighted Limits and Colimits](https://emilyriehl.github.io/files/weighted.pdf)
- [Fosco Loregian: Coend Calculus](https://arxiv.org/pdf/1501.02503)
- [Bartosz Milewski: Weighted Colimits](https://bartoszmilewski.com/2020/07/20/weighted-colimits/)
- [n-Category Café: Enrichment and its Limits](https://golem.ph.utexas.edu/category/2017/04/enrichment_and_its_limits.html)

## Tasks

- [x] Search mathlib for existing coend elimination formula
  - Result: Mathlib does NOT have `Hom(∫^A P(A,A), Y) ≅ ∫_A Hom(P(A,A), Y)`
  - Mathlib only provides: `coend.desc` (universal property), `coend.ι_desc` (factorization)
  - We need to prove this formula ourselves
- [x] Add explicit equivalences between mathlib's ends/coends and our weighted
      ends/coends (with unit/terminal weight profunctor)
  - We already have equivalences for Wedge/Cowedge
  - Mathlib defines ends as terminal wedges, coends as initial cowedges
  - Transfer initiality/terminality across the categorical equivalences
  - Result: Added `Prop`-level transfers via `hasTerminalWeightedWedgeIffHasEnd`,
    `hasInitialWeightedCowedgeIffHasCoend` using `Equivalence.hasTerminal_iff`
    and `hasLimit_iff_hasTerminal_cone`
  - Added data-level transfers `isTerminalOfEquivFunctor`/`isInitialOfEquivFunctor`
    in `Utilities/Category.lean` (computable, no `choice`)
  - Added weighted end/coend to mathlib end/coend transfers:
    `isTerminalWedgeOfIsWeightedEnd`, `isWeightedEndOfIsTerminalWedge`,
    `isInitialCowedgeOfIsWeightedCoend`, `isWeightedCoendOfIsInitialCowedge`
  - Added computable isomorphisms (computably, no `choice`):
    - `isTerminalWedgeIso` - isomorphism between two terminal wedge apices
    - `isInitialCowedgeIso` - isomorphism between two initial cowedge apices
    - `weightedEndIsoTerminalWedge : c.pt ≅ w.pt` (given `IsWeightedEnd c` and
      `IsTerminal w`)
    - `weightedCoendIsoInitialCowedge : c.pt ≅ w.pt` (given `IsWeightedCoend c`
      and `IsInitial w`)
  - Added computable `HasEnd`/`HasCoend` constructors from terminal/initial data:
    - `hasEndOfIsTerminalWedge : IsTerminal w → HasEnd P`
    - `hasCoendOfIsInitialCowedge : IsInitial w → HasCoend P`
    - `hasEndOfIsWeightedEnd : IsWeightedEnd c → HasEnd P`
    - `hasCoendOfIsWeightedCoend : IsWeightedCoend c → HasCoend P`
  - Added computable end/coend objects and structure maps from weighted data:
    - `weightedEnd P c hc : D` - the end object (= `c.pt`)
    - `weightedCoend P c hc : D` - the coend object (= `c.pt`)
    - `weightedEnd.π P c hc j : weightedEnd P c hc ⟶ (P.obj (op j)).obj j`
    - `weightedCoend.ι P c hc j : (P.obj (op j)).obj j ⟶ weightedCoend P c hc`
  - Added computable `LimitCone`/`ColimitCocone` constructors from weighted data:
    - `weightedEndToLimitCone` - from `IsWeightedEnd c` to `LimitCone`
    - `weightedCoendToColimitCocone` - from `IsWeightedCoend c` to `ColimitCocone`
    - `WeightedEndWedge.toLimitCone` - wrapper taking bundled structure
    - `WeightedCoendCowedge.toColimitCocone` - wrapper taking bundled structure
- [x] Add `End`/`Coend` abbreviations
  - `End P` = `WeightedEndWedge terminalProfunctor P`
  - `Coend P` = `WeightedCoendCowedge terminalProfunctor P`
  - These serve as our computable "end" and "coend" since mathlib's are not
    computable
- [x] Extract `HasCopowers` to `GebLean/Utilities/PowersAndCopowers.lean`
- [x] Add `HasPowers` (dual to `HasCopowers`) in `PowersAndCopowers.lean`
  - Powers are characterized by `Hom(Y, X ^. S) ≅ (S → Hom(Y, X))`
  - Added `mapVal`, `mapIdx`, `bimap` and their lemmas (dual to copowers)
  - Note: `mapIdx` is contravariant for powers (vs covariant for copowers)
- [x] Prove copowers/powers are weighted colimits/limits over terminal category
  - `S ·. X` = weighted colimit of `1 → C` picking X, weight picking S
  - `X ^. S` = weighted limit of `1 → C` picking X, weight picking S
  - Added `terminalDiagram`, `terminalWeight`, `terminalWeightCov` functors
  - Added `copowerCocone`, `copowerIsWeightedColimit` (initiality proof)
  - Added `powerCone`, `powerIsWeightedLimit` (terminality proof)
  - Validates our definitions are consistent with weighted (co)limit theory
- [x] Prove the tensor-hom adjunction (copower-power elimination)
  - `C(S ·. X, Y) ≅ Set(S, C(X, Y)) ≅ C(X, Y ^. S)`
  - Added `copowerHomEquiv : (S ·. X ⟶ Y) ≃ (S → (X ⟶ Y))`
  - Added `powerHomEquiv : (S → (Y ⟶ X)) ≃ (Y ⟶ X ^. S)`
  - Added `copowerPowerEquiv : (S ·. X ⟶ Y) ≃ (X ⟶ Y ^. S)` (composition)
  - This is the elimination rule for copowers using powers
  - Added `copowerWithTypeFunctor S : C ⥤ C` mapping `X ↦ S ·. X`
  - Added `powerByTypeFunctor S : C ⥤ C` mapping `X ↦ X ^. S`
  - Added `copowerPowerAdjunction S`:
    `copowerWithTypeFunctor S ⊣ powerByTypeFunctor S`
- [x] Prove weighted (co)limits via ordinary (co)limits + powers/copowers
  - `{W, F} ≅ ∫_j F(j) ^. W(j)` (weighted limit via end of powers)
  - `W * F ≅ ∫^j W(j) ·. F(j)` (weighted colimit via coend of copowers)
  - Progress:
    - [x] Added `copowerProfunctor W F : Jᵒᵖ ⥤ J ⥤ C` in `PowersAndCopowers.lean`
      - Diagonal: `(copowerProfunctor W F).obj (op j).obj j = W(j) ·. F(j)`
      - Inner functor: `copowerProfunctorInner W F j =`
        `F ⋙ copowerWithTypeFunctor (W.obj j)`
    - [x] Added `powerProfunctor W F : Jᵒᵖ ⥤ J ⥤ C` in `PowersAndCopowers.lean`
      - Diagonal: `(powerProfunctor W F).obj (op j).obj j = F(j) ^. W(j)`
      - Inner functor: `powerProfunctorInner W F j =`
        `F ⋙ powerByTypeFunctor (W.obj j.unop)`
    - [x] Established equivalence
      `WeightedCocone W F ≌ Cocone (profunctorOnCoTwistedArrow J`
      `(copowerProfunctor W F))`
      via `weightedCoconeCopowerCoconeEquiv`
    - [x] Composed with cowedge-cocone equivalence to get
      `WeightedCocone W F ≌ Cowedge (copowerProfunctor W F)`
      via `weightedCoconeCowedgeEquiv`
    - [x] Dual: `WeightedCone W F ≌ Cone (profunctorOnTwistedArrow J
      (powerProfunctor W F))` via `weightedConePowerConeEquiv`
      - [x] `powerConeπApp_naturality` - cone legs form natural transformation
      - [x] `weightedConeToPowerCone` - conversion from weighted cones
      - [x] `powerConeToWeightedCone` - conversion from power cones
      - [x] Round-trip theorems (weighted → power → weighted = id)
      - [x] Round-trip theorems (power → weighted → power = id)
      - [x] Morphism mappings (weighted cone homs ↔ power cone homs)
      - [x] Functors and final equivalence `weightedConePowerConeEquiv`
    - [x] Compose with wedge-cone equivalence:
      `WeightedCone W F ≌ Wedge (powerProfunctor W F)`
      via `weightedConeWedgeEquiv`
    - [x] Transfer initiality across `weightedCoconeCowedgeEquiv` to prove
      `W * F ≅ ∫^j W(j) ·. F(j)` (weighted colimit = coend of copowers)
      - Added `hasInitialWeightedCoconeOfHasInitialCopowerCowedge`
      - Added `hasInitialCopowerCowedgeOfHasInitialWeightedCocone`
      - Added `isInitialCopowerCowedgeOfIsWeightedColimit`
      - Added `isWeightedColimitOfIsInitialCopowerCowedge`
    - [x] Transfer terminality across `weightedConeWedgeEquiv` to prove
      `{W, F} ≅ ∫_j F(j) ^. W(j)` (weighted limit = end of powers)
      - Added `hasTerminalWeightedConeOfHasTerminalPowerWedge`
      - Added `hasTerminalPowerWedgeOfHasTerminalWeightedCone`
      - Added `isTerminalPowerWedgeOfIsWeightedLimit`
      - Added `isWeightedLimitOfIsTerminalPowerWedge`
    - [x] Added apex isomorphisms formalizing the (co)limit-(co)end formulas:
      - `weightedColimitIsoCopowerCoend : c.pt ≅ w.pt`
        (given `IsWeightedColimit c` and `IsInitial w` for cowedge
        over `copowerProfunctor W F`)
      - `weightedLimitIsoPowerEnd : c.pt ≅ w.pt` (given `IsWeightedLimit c`
        and `IsTerminal w` for wedge over `powerProfunctor W F`)
- [x] Extend to weighted cowedges/wedges with profunctor weights
  - [x] Define composed profunctor for weighted cowedge:
    `copowerWeightedProfunctor W P` where W is profunctor weight
  - [x] Establish `WeightedCowedge W P ≌ Cowedge (copowerWeightedProfunctor W P)`
    via `weightedCowedgeCowedgeEquiv`
  - [x] Dual: `WeightedWedge W P ≌ Wedge (powerWeightedProfunctor W P)`
    via `weightedWedgeWedgeEquiv`
  - [x] Transfer initiality/terminality for weighted coends/ends:
    - `hasInitialWeightedCowedgeOfHasInitialCopowerCowedge`
    - `hasInitialCopowerCowedgeOfHasInitialWeightedCowedge`
    - `isInitialCopowerCowedgeOfIsWeightedCoend`
    - `isWeightedCoendOfIsInitialCopowerCowedge`
    - `weightedCoendIsoCopowerCowedge`
    - `hasTerminalWeightedWedgeOfHasTerminalPowerWedge`
    - `hasTerminalPowerWedgeOfHasTerminalWeightedWedge`
    - `isTerminalPowerWedgeOfIsWeightedEnd`
    - `isWeightedEndOfIsTerminalPowerWedge`
    - `weightedEndIsoPowerWedge`
- [x] Formalize Level 1: Weighted colimit elimination via weighted limits
  - `C(W * F, Y) ≅ {W, C(F(-), Y)}`
  - Implemented at the `WeightedCone`/`WeightedCocone` level in `Weighted.lean`
  - Added `WeightedColimitElimination` section with:
    - `WeightedCocone.postcompose` - post-compose cocone with morphism
    - `WeightedCocone.ofCoconeOver` - construct cocone from cocone over apex
    - `WeightedCocone.postcompose_id`, `postcompose_comp`, `postcompose_hom`
    - `IsWeightedColimit.toWeightedCoconeOver` - forward direction
    - `IsWeightedColimit.fromWeightedCoconeOver` - backward direction
    - `homEquivWeightedCoconeOver : (c.pt ⟶ Y) ≃ WeightedCoconeOver W D Y`
    - `homEquivWeightedCoconeOver_naturality` - naturality in Y
  - Uses `homToFunctorBifunctor` from `Profunctors.lean` to express
    `C(F(-), Y)` as a functor
  - Added `WeightedLimitInType` section connecting to weighted limits:
    - `WeightedLimitInType W P := W ⟶ P` (weighted limit of P by W in Type
      equals natural transformations, by the formula `{W,P} = ∫_j [W(j), P(j)]`)
    - `weightedCoconeOver_eq_weightedLimitInType` - definitional equality
    - `homEquivWeightedLimitInType` - the elimination rule with explicit
      weighted limit type
- [x] Formalize Level 2: Weighted coend elimination via weighted ends
  - `Hom(∫^A W(A) ⊗ P(A,A), Y) ≅ ∫_A [W(A), Hom(P(A,A), Y)]`
  - Implemented in `WeightedCoendElimAsEnd` section of `Weighted.lean`
  - Added `homWeightedWedge_isWeightedEnd` - proves `homWeightedWedge c Y` is
    a weighted end when `c` is a weighted coend
  - Added `homIsoWeightedEndApex` - isomorphism `(c.pt ⟶ Y) ≅ d.pt` for
    weighted end `d` of `homFromSwappedProfunctor P Y`
- [x] Show that `WeightedCowedgeOver terminalProfunctor P Y` is the end
      `∫_A Hom(P(A,A), Y)`
  - Added `cowedgeOverWedgeπ` - extracts diagonal component from cowedge-over
  - Added `cowedgeOverToHom` - maps cowedge-over to `c.pt ⟶ Y` via coend
    universal property
  - Added `cowedgeOverFromHom` - maps `c.pt ⟶ Y` to cowedge-over by
    post-composition
  - Added `cowedgeOver_roundtrip` - proves cowedge-over → hom → cowedge-over
    = identity
  - Added `hom_roundtrip` - proves hom → cowedge-over → hom = identity
  - Combined with Level 3 (`homOrdinaryWedge_isTerminal`), this establishes
    the bijection `WeightedCowedgeOver terminalProfunctor P Y ≃ ∫_A Hom(P(A,A), Y)`
- [x] Formalize Level 3: Ordinary coend elimination via ordinary ends
  - `Hom(∫^A P(A,A), Y) ≅ ∫_A Hom(P(A,A), Y)`
  - Derive from Level 2 with `W = terminalProfunctor`
  - Added `homOrdinaryWedge` - constructs mathlib wedge from cowedge
  - Added `homOrdinaryWedge_isTerminal` - proves terminality (end property)
  - Added `ordinaryHomIsoEndApex` - extracts `(c.pt ⟶ Y) ≅ d.pt`
- [ ] Prove the co-Yoneda isomorphism:
      `∫^A P(A,A) ≅ Nat(Y ↦ ∫_A Hom(P(A,A), Y), Id)`
- [x] Complete the proof that `coendToNatTrans` and `natTransToCoend` are
      mutually inverse
  - `natTransToCoend_coendToNatTrans` - proves natural trans → coend → natural
    trans = id
  - `coendToNatTrans_natTransToCoend` - proves coend → natural trans → coend
    = id
- [ ] Clean up `CoendAsNatTransformations` section to use proper
      initiality/terminality rather than assuming coend existence via parameters

## Notes

### Level 1 Elimination Rule Implementation

The weighted colimit elimination rule `C(W * F, Y) ≅ {W, C(F(-), Y)}` is
implemented in `GebLean/Weighted.lean` in the `WeightedColimitElimination`
section.

The formula expresses that morphisms from a weighted colimit into `Y` are
isomorphic to weighted limits of the hom functor `C(F(-), Y)`. Since
`WeightedCoconeOver W D Y` is defined as `W ⟶ homToFunctor D Y`, and this is
exactly the weighted limit structure `{W, C(D(-), Y)}`, the elimination rule
becomes:

```text
(c.pt ⟶ Y) ≃ WeightedCoconeOver W D Y
```

where `c` is the weighted colimit cocone.

The forward direction `toWeightedCoconeOver` uses post-composition with the
morphism `f : c.pt ⟶ Y`, relying on `homToFunctorBifunctor` from
`Profunctors.lean` which gives the functoriality of `j ↦ C(D(j), Y)` in Y.

The backward direction `fromWeightedCoconeOver` uses the universal property
`descHom` to factor the cocone over through the colimit.

The round-trip proofs use:

- The morphism property of weighted cocone homomorphisms (for
  `toWeightedCoconeOver_fromWeightedCoconeOver`)
- The uniqueness of morphisms from the initial object (for
  `fromWeightedCoconeOver_toWeightedCoconeOver`)

### Weighted Limits in Type

The weighted limit formula specializes in the category `Type v`. For functors
`W, P : Jᵒᵖ ⥤ Type v`, the weighted limit is:

```text
{W, P} = ∫_j [W(j), P(j)] = ∫_j (W(j) → P(j)) = Nat(W, P) = W ⟶ P
```

where `[-,-]` is the internal hom in `Type` (function types), and the end
over function types is the type of natural transformations.

This makes `WeightedCoconeOver W D Y = W ⟶ homToFunctor D Y` definitionally
equal to the weighted limit `{W, C(D(-), Y)}` in `Type`. The full elimination
chain becomes:

1. `(c.pt ⟶ Y)` - morphisms from weighted colimit
2. `≃ WeightedCoconeOver W D Y` - by `homEquivWeightedCoconeOver`
3. `= (W ⟶ homToFunctor D Y)` - by definition of `WeightedCoconeOver`
4. `= {W, C(D(-), Y)}` - by the weighted limit formula in `Type`

This is formalized in the `WeightedLimitInType` section of `Weighted.lean`.

### Level 2 Elimination Rule Implementation

The weighted coend elimination rule `Hom(∫^A W(A) ⊗ P(A,A), Y) ≅ ∫_A [W(A),
Hom(P(A,A), Y)]` is implemented in `GebLean/Weighted.lean` in the
`WeightedCoendElimAsEnd` section.

The formula expresses that morphisms from a weighted coend into `Y` are
isomorphic to weighted ends of the hom profunctor. This is:

```text
(c.pt ⟶ Y) ≅ {W, Hom(P(-,-), Y)}
```

where `c` is the weighted coend cowedge and `{W, ...}` denotes weighted end.

The implementation consists of:

1. `homWeightedWedge c Y` - constructs a weighted wedge over
   `homFromSwappedProfunctor P Y` with apex `c.pt ⟶ Y`
2. `homWeightedWedge_isWeightedEnd` - proves this wedge is terminal
   (a weighted end) when `c` is a weighted coend
3. `homIsoWeightedEndApex` - extracts the isomorphism `(c.pt ⟶ Y) ≅ d.pt`
   for any other weighted end `d`

The proof uses the duality between cowedge morphisms and wedge morphisms:

- Forward: post-composing with `c.pt ⟶ Y` using `descHom`
- Backward: converting a weighted wedge to a cowedge via `wedgeToCowedge`

The uniqueness proof uses the equivalence `coTwistedArrowOpEquivTwistedArrow`
to transport between cowedge and wedge conditions.

### Level 3 Elimination Rule Implementation

The ordinary coend elimination rule `Hom(∫^A P(A,A), Y) ≅ ∫_A Hom(P(A,A), Y)`
is implemented by specializing Level 2 to the trivial weight (`terminalProfunctor`).

Since `PUnit ⊗ X ≅ X` (trivial copower) and `[PUnit, Y] ≅ Y` (trivial power),
the weighted formula reduces to the ordinary (unweighted) formula.

The implementation consists of:

1. `homOrdinaryWedge P c Y` - converts a mathlib cowedge to a mathlib wedge:
   - Converts cowedge to weighted cowedge via `trivialWeightedCowedgeCowedgeEquiv`
   - Applies `homWeightedWedge` to get weighted wedge for hom profunctor
   - Converts back via `trivialWeightedWedgeWedgeEquiv`

2. `homOrdinaryWedge_isTerminal P hc Y` - proves the wedge is terminal:
   - Uses `isWeightedCoendOfIsInitialCowedge` to get weighted coend
   - Applies `homWeightedWedge_isWeightedEnd` from Level 2
   - Uses `isTerminalWedgeOfIsWeightedEnd` to convert to mathlib terminality

3. `ordinaryHomIsoEndApex P hc Y hd` - extracts the isomorphism:
   - Uses `isTerminalWedgeIso` to get isomorphism between terminal wedges
   - Result: `(c.pt ⟶ Y) ≅ d.pt` where `c` is coend cowedge, `d` is end wedge

### Current State of CoendAsNatTransformations

The section defines:

- `cowedgeFamilyFunctor`: `Y ↦ WeightedCowedgeOver terminalProfunctor P Y`
- `CowedgeNatTrans`: Natural transformations `cowedgeFamilyFunctor P ⟶ Id`
- `coendInjectionCowedge`: Injection maps form a cowedge
- `coendToNatTrans`: Coend element → natural transformation (assumes coend exists)
- `natTransToCoend`: Natural transformation → coend element
- `coTwToDomDiag`: Morphism from any co-twisted arrow to its domain's diagonal
- `natTransToCoend_coendToNatTrans`: Round-trip proof (nat trans → coend → nat
  trans = id)
- `coendToNatTrans_natTransToCoend`: Round-trip proof (coend → nat trans → coend
  = id)

Still missing:

- Explicit connection to ends
- Use of initiality (currently assumes `desc`, `fac`, `unique` as parameters)

### Dinaturality vs Paranaturality

When the target profunctor is constant (a fixed type), dinaturality and
paranaturality coincide. The cowedge condition `hι` in the current code is
exactly the dinaturality condition for the injection maps.

### Mathlib Resources

- `Mathlib.CategoryTheory.Limits.Shapes.End` - ends and coends

**What mathlib has:**

- `Wedge F` = `Multifork (multicospanIndexEnd F)` - cones for ends
- `Cowedge F` = `Multicofork (multispanIndexCoend F)` - cocones for coends
- `HasEnd F` = `HasMultiequalizer (multicospanIndexEnd F)`
- `HasCoend F` = `HasMulticoequalizer (multispanIndexCoend F)`
- `end_ F` = `multiequalizer (multicospanIndexEnd F)` - the end object
- `coend F` = `multicoequalizer (multispanIndexCoend F)` - the coend object
- `end_.π F j : end_ F ⟶ (F.obj (op j)).obj j` - projection from end
- `coend.ι F j : (F.obj (op j)).obj j ⟶ coend F` - injection into coend
- `end_.lift` / `coend.desc` - universal property constructors
- `endFunctor J C` / `coendFunctor J C` - functorial construction

**What mathlib does NOT have:**

- The coend elimination rule: `Hom(∫^A P(A,A), Y) ≅ ∫_A Hom(P(A,A), Y)`
- Any connection between ends and coends via Hom functors
- The co-Yoneda characterization of coends

## Related Files

- `GebLean/RestrictedCoendAsColimit.lean` - CoendAsNatTransformations section
- `GebLean/WeightedAlg.lean` - WeightedWedge, WeightedCowedge definitions
- `GebLean/Weighted.lean` - HasWeightedEnd, HasWeightedCoend, End, Coend
- `GebLean/Utilities/PowersAndCopowers.lean` - HasCopowers (and HasPowers)
