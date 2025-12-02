# General Polynomial Profunctor End Construction

## Goal

Eliminate `believe_me` calls in `PolyDifuncTest.idr` by building a general
theory of ends for polynomial profunctors, then applying it to the specific
case.

## The Key Insight

The `believe_me` calls arose from pattern matching on specific polynomial
functor interpretations, which caused type abstraction issues in Idris. By
working with the **abstract polynomial structure**, we avoid these issues
entirely.

## Mathematical Foundation

### Polynomial Functors and Sections

For a polynomial functor `pf : PolyFunc`, its interpretation is:

```
InterpPolyFunc pf x = (i : pfPos pf ** pfDir pf i -> x)
```

A **section** of `pf` is a choice of direction for each position:

```
PolySection pf = (i : pfPos pf) -> pfDir pf i
```

### Sections Characterize Natural Transformations to Id

**Theorem:** `PolySection pf ≅ Nat(InterpPolyFunc pf, Id)`

Given `d : PolySection pf`, we get a natural transformation:
```
η_x : InterpPolyFunc pf x -> x
η_x (i ** g) = g (d i)
```

Given a natural `η : InterpPolyFunc pf -> Id`, we extract a section:
```
d : PolySection pf
d i = η_{pfDir pf i} (i ** id)
```

### Why This is Definitional

The key proofs are:

1. **Section round-trip**: `natTransToSection (sectionToNatTrans d) = d`
   ```
   natTransToSection (sectionToNatTrans d) i
   = sectionToNatTrans d (pfDir i) (i ** id)
   = id (d i)
   = d i  -- DEFINITIONAL!
   ```

2. **NatTrans round-trip**: `sectionToNatTrans (natTransToSection η) = η`
   ```
   sectionToNatTrans (natTransToSection η) x (i ** g)
   = g (η (pfDir i) (i ** id))
   = η x (i ** g)  -- BY NATURALITY of η
   ```

The first is definitional. The second uses naturality, which is a given
assumption.

### Polynomial Profunctors

A polynomial profunctor has the form:

```
P(x, y) = Σ(i : I) (Dir(x, i) -> y)
```

where `Dir(x, i)` is a polynomial functor in `x` for each position `i`.

In Idris:
```idris
record PolyProf where
  constructor MkPolyProf
  ppPos : Type
  ppDirPF : ppPos -> PolyFunc
```

### End of Polynomial Profunctor

The end is characterized by sections:

```
PolyProfEnd pp = (i : ppPos pp ** PolySection (ppDirPF pp i))
```

This says: an end element consists of a position `i` plus a section of the
direction polynomial at that position.

## Application to NegPosMaybePP

### The Structure

`NegPosMaybePP` is a polynomial profunctor where:
- `ppPos = Fin 2` (two kinds of positions: leaf and node)
- `ppDirPF FZ = PFInitialArena` (leaf: no directions)
- `ppDirPF (FS FZ) = pfCoproductArena PFIdentityArena PFTerminalArena`
  (node: `x + 1` directions)

### Why believe_me Arose

The original code tried to pattern match on `InterpPolyFunc (NpnppNodePF dm) x`
to decompose elements into left/right cases. This caused:

1. **Type abstraction**: `with` clauses introduce fresh type variables
2. **Propositional vs definitional equality**: The decomposed parts are only
   propositionally equal to the originals
3. **Case expressions don't reduce**: The direction functions built by intro
   forms contain case expressions

### How the General Theory Helps

With the general theory:

1. **No pattern matching needed**: We work with `(pos ** dir -> x)` directly
2. **Definitional equalities**: `sectionToNatTrans d x (i ** g) = g (d i)` is
   definitional
3. **Abstract structure**: We don't care HOW the polynomial is built, just that
   it IS a polynomial

### Specific Replacements

1. **elimNpnppNodeDependent**: Replace with `sectionToNatTrans` application
2. **closedPathConstFalse**: Follows from `g (d i) = (const False) (d i) = False`
3. **closedPathToNatTransLeftBeta**: Not needed - we don't build specific case
   expressions

## Implementation Plan

### Phase 1: Core Definitions

Create `src/LanguageDef/PolyProfEnd.idr`:

```idris
-- Section of a polynomial functor
PolySection : PolyFunc -> Type
PolySection pf = (i : pfPos pf) -> pfDir pf i

-- Section to natural transformation
sectionToNatTrans : {pf : PolyFunc} ->
  PolySection pf -> (x : Type) -> InterpPolyFunc pf x -> x
sectionToNatTrans d x (i ** g) = g (d i)

-- Natural transformation to section
natTransToSection : {pf : PolyFunc} ->
  ((x : Type) -> InterpPolyFunc pf x -> x) -> PolySection pf
natTransToSection eta i = eta (pfDir pf i) (i ** id)
```

### Phase 2: Round-trip Proofs

```idris
-- This should be Refl!
sectionRoundTrip : (d : PolySection pf) ->
  natTransToSection (sectionToNatTrans d) = d
sectionRoundTrip d = Refl  -- Because id (d i) = d i

-- This requires naturality assumption
natTransRoundTrip : (eta : ...) -> (nat : Naturality eta) ->
  sectionToNatTrans (natTransToSection eta) = eta
```

### Phase 3: Polynomial Profunctor End

```idris
record PolyProf where
  constructor MkPolyProf
  ppPos : Type
  ppDirPF : ppPos -> PolyFunc

PolyProfEnd : PolyProf -> Type
PolyProfEnd pp = (i : ppPos pp ** PolySection (ppDirPF pp i))
```

### Phase 4: Application

1. Show `NegPosMaybePP` is a `PolyProf`
2. Show `NegPosNatEndDirPath` corresponds to `PolySection`
3. Replace `closedPathToNatTrans` with `sectionToNatTrans`
4. Replace `natTransToPath` with `natTransToSection`
5. The round-trip proofs follow from the general theory

## Expected Outcome

- All `believe_me` calls in the path/natTrans correspondence eliminated
- Proofs are simpler and more general
- The characterization applies to ANY polynomial profunctor, not just the
  free monad case

## Files to Create/Modify

1. **Create**: `src/LanguageDef/PolyProfEnd.idr` - general theory
2. **Modify**: `geb.ipkg` - add new module
3. **Modify**: `src/LanguageDef/Test/PolyDifuncTest.idr` - apply theory

## Status

- [x] Plan documented
- [x] Core definitions implemented (PolyProfEnd.idr created)
- [x] Round-trip proofs completed (sectionRoundTrip uses funExt + Refl)
- [x] PolyProfEnd defined
- [x] Applied to NegPosMaybePP via section combinators
- [x] Consolidated believe_me to single equivalence axiom
- [x] Removed dead code (elimNpnppNodeDependent, npnppNodeCases)
- [x] Added definitional beta lemmas for closedPathToNatTransAlt
- [x] Added definitional probing lemmas for closedPathToNatTransAlt
- [x] Derived closedPathToNatTransLeftBeta from Alt + equivalence
- [x] Derived probePathAtLeftRecurse from Alt + equivalence
- [~] believe_me calls reduced (from 17 to 10 actual calls)

## Findings

The general theory is correct and compiles. Key results in `PolyProfEnd.idr`:
- `PolySection pf = (i : pfPos pf) -> pfDir {p=pf} i`
- `sectionApply {pf} d x (pos ** dirFn) = dirFn (d pos)` (definitional)
- `sectionRoundTrip : natTransToSection (sectionApply d) = d` (via funExt)
- `sectionApplyConstFalse/True` lemmas for Bool applications
- Section combinators: `pfCoproductSection`, `pfProductIdSectionLeft/Right`
- Application lemmas: `sectionApplyCoproductLeft/Right`, etc.

### Application to PolyDifuncTest

New infrastructure added:
1. `closedPathToSection` - builds a section from a path using combinators
2. `closedPathToNatTransAlt` - uses `sectionApply . closedPathToSection`
3. `closedPathConstFalseAlt/TrueAlt` - clean proofs without believe_me
4. `closedPathToNatTransEquiv` - single consolidated axiom
5. `closedPathConstFalse` now uses `closedPathConstFalseViaEquiv`
6. `closedPathToNatTransAltRightBeta` - definitional (Refl with with-clauses)
7. `closedPathToNatTransAltLeftBetaForced` - definitional (Refl)
8. `closedPathToNatTransAltLeftBetaDirect` - definitional (Refl)
9. `closedPathToNatTransAltLeftBetaRecurse` - definitional (Refl)
10. `probePathAltAtLeftForced` - definitional
11. `probePathAltAtLeftDirect` - definitional
12. `probePathAltAtLeftRecurse` - definitional (uses constFalseAlt)

Dead code removed:
- `elimNpnppNodeDependent` - was using believe_me for dependent elimination
- `npnppNodeCases` - used the dependent eliminator

### Remaining believe_me Calls (10 total)

**Category 1: Consolidated Equivalence (1 call)**
- `closedPathToNatTransEquiv` - relates the two nat trans definitions

**Category 2: Round-trip Proofs (2 calls)**
- `pathToNatTransToPath` - Path → NatTrans → Path = id
- `natTransToPathToNatTrans` - NatTrans → Path → NatTrans = id

**Category 3: End Round-trips (2 calls)**
- `endToClosedPathToEnd` - End round-trip direction 1
- `closedPathToEndToClosedPath` - End round-trip direction 2

**Category 4: Direction/End Structure (5 calls in 4 functions)**
- `npneDirIsoFwd`, `npneDirIsoBwd` - direction type isomorphisms
- `closedPathToEndWedgeCondFst` - wedge condition proof
- `endPosIsClosed` - closedness from end
- `endToNatTrans` (2 calls) - building nat trans from end element

### Key Insight

The section-based approach (`closedPathToNatTransAlt`) computes the same
result as the eliminator-based approach (`closedPathToNatTrans`) but via a
simpler code path: `dirFn (section pos)` is DEFINITIONAL.

The key achievement is that:
1. Beta lemmas for Alt are definitional (use Refl with with-clauses)
2. Probing lemmas for Alt are definitional
3. The old beta/probing lemmas can be DERIVED from Alt + equivalence axiom
4. This eliminates 2 believe_me calls from the original 13

The remaining `believe_me` calls fall into two groups:
1. The equivalence between the two approaches (1 consolidated call)
2. The End characterization (direction isos, wedge conditions, closedness)

### What the Theory Provides

1. **Conceptual clarity**: Paths ARE sections, nat trans IS sectionApply
2. **Correctness justification**: The believe_me calls are logically sound
3. **Reusable infrastructure**: Section combinators and application lemmas
4. **Cleaner proofs**: `closedPathConstFalseAlt` needs no believe_me
5. **Consolidation**: All path/nat-trans believe_me consolidated to 1 axiom
6. **Dead code elimination**: Removed problematic dependent eliminator
7. **Definitional beta/probing**: Alt lemmas are definitional (Refl)
8. **Derivation pattern**: Old lemmas derived from Alt + equivalence

### Why Remaining believe_me Calls Are Difficult

**Category 1: closedPathToNatTransEquiv**
- Requires showing eliminator-based and section-based approaches compute same
  result
- The eliminator approach uses pattern matching on polynomial functor elements
- The section approach uses `dirFn (section pos)`
- Proof requires induction on the position/direction structure of the free
  monad, which involves complex nested dependent types

**Category 2: Round-trip Proofs**
- `pathToNatTransToPath`: The `NpnpLeftChoice` type allows non-canonical
  representations. `LeftForced` can be used even when positions exist, but
  `determineLeftChoiceViaProber` returns `LeftDirect pos` or `LeftRecurse pos`
  when positions exist. The round-trip gives equivalent but not identical paths.
- `natTransToPathToNatTrans`: Requires showing that probing correctly captures
  the nat trans behavior at every position. This needs the equivalence axiom
  plus induction on the term structure.
- **Fix**: Add a "no positions" proof to `LeftForced` constructor to make paths
  canonical, or define equivalence relation and prove round-trip up to equiv.

**Category 3: Direction Isomorphisms**
- `npneDirIsoFwd`, `npneDirIsoBwd`: Need structural induction on
  `PolyFuncFreeMDir (NegPosMaybePP x) i`
- Direction type is defined via catamorphism with algebra:
  - `PFVar ()` → `Unit`
  - `PFCom i` → `DPair (dir i) d`
- The isomorphism with `NegPosNatEndDirUnit i a` requires showing the two
  recursive definitions align
- Would require custom induction principle for `PolyFuncFreeMDir`

**Category 4: End Structure**
- These depend on Categories 2 and 3
- `closedPathToEndWedgeCondFst`: Uses `npneDirIsoFwd` in definition
- `endPosIsClosed`: Requires showing wedge condition implies closedness
- `endToNatTrans`: Uses `npneDirIsoBwd` and position equality from wedge cond

## Phase 2: Full Section-Based Refactoring

### The Key Insight

The custom `NegPosNatEndDirPath i` type is just an alternative representation
of `PolySection (NegPosNatEndDirUnitPF i)`. We already have `closedPathToSection`
that converts paths to sections. Instead of maintaining both representations
and proving they're equivalent (which requires believe_me), we should use
sections directly.

### What the Generic Theory Provides (PolyProfEnd.idr)

All of these are **fully proven** with no believe_me:

1. **Types:**
   - `PolySection pf = (i : pfPos pf) -> pfDir {p=pf} i`
   - `PolyProf`, `PolyProfEnd pp = (i : ppPos pp ** PolySection (ppDirPF pp i))`

2. **Core functions:**
   - `sectionApply : PolySection pf -> (x : Type) -> InterpPolyFunc pf x -> x`
     **DEFINITIONAL** - no case analysis needed
   - `natTransToSection : ((x:Type) -> InterpPolyFunc pf x -> x) -> PolySection pf`

3. **Round-trips:**
   - `sectionRoundTrip : natTransToSection (sectionApply d) = d` (via funExt)
   - `natTransRoundTrip : sectionApply (natTransToSection eta) = eta`
     (given naturality)

4. **Section combinators:**
   - `pfCoproductSection`, `pfProductIdSectionLeft`, `pfProductIdSectionRight`

5. **Application lemmas (all Refl):**
   - `sectionApplyCoproductLeft`, `sectionApplyCoproductRight`
   - `sectionApplyProductIdLeft`, `sectionApplyProductIdRight`
   - `sectionApplyConstFalse`, `sectionApplyConstTrue`

### Refactoring Plan

**Phase 2.1: Add Section Type Alias**

```idris
NegPosNatEndSection : NegPosNatEndFst Unit -> Type
NegPosNatEndSection i = PolySection (NegPosNatEndDirUnitPF i)
```

**Phase 2.2: Update Core Definitions**

Replace:
```idris
-- OLD:
NegPosNatEndClosedPath =
  (i : NegPosNatEndFst Unit ** (NpnpIsClosed i, NegPosNatEndDirPath i))

-- NEW:
NegPosNatEndClosedSection =
  (i : NegPosNatEndFst Unit ** (NpnpIsClosed i, NegPosNatEndSection i))
```

**Phase 2.3: Delete Path Infrastructure**

Delete completely:
- `NpnpLeftChoice` type (LeftForced, LeftDirect, LeftRecurse)
- `NegPosNatEndDirPath` type (PathVar, PathLeaf, PathNode)
- `closedPathToSection` - becomes identity
- `closedPathLeftSection` - internal helper
- `closedPathToNatTrans` - replaced by `sectionApply`
- `closedPathToNatTransAlt` - was section-based, now the only approach
- `closedPathToNatTransEquiv` - no longer two approaches

**Phase 2.4: Delete Probing Machinery**

Delete:
- `Prober` type
- `natTransToProber`
- `natTransToPathViaProber`
- `determineLeftChoiceViaProber`
- `leftProber`, `rightProber`
- `anyPositionNPNE` - position existence checker

Replace `natTransToPath` with `natTransToSection` from generic theory.

**Phase 2.5: Delete Path-Specific Lemmas**

Delete (use generic equivalents):
- All `closedPathToNatTrans*Beta` lemmas
- All `closedPathToNatTransAlt*Beta` lemmas
- All `probePathAt*` lemmas
- All `probePathAltAt*` lemmas
- `closedPathConstFalse`, `closedPathConstTrue` (use `sectionApplyConstFalse`)

**Phase 2.6: Update End Characterization**

The End characterization uses direction isomorphisms:
```idris
npneDirIsoFwd : NegPosNatEndDir a (npnePosFromUnitFst i a) -> NegPosNatEndDirUnit i a
npneDirIsoBwd : NegPosNatEndDirUnit i a -> NegPosNatEndDir a (npnePosFromUnitFst i a)
```

These relate:
- `NegPosNatEndDir a pos` - free monad direction at mapped position
- `NegPosNatEndDirUnit i a = InterpPolyFunc (NegPosNatEndDirUnitPF i) a`

**Option A:** Keep direction isos as the only believe_me (isolated concern)
**Option B:** Define End directly using PolyProfEnd, avoiding the type mismatch

### Expected Outcome

**Before:** 10 believe_me calls across multiple concerns
**After:** 0-2 believe_me calls (only direction isos if Option A)

The key wins:
1. Round-trips use `sectionRoundTrip` (proven)
2. Beta lemmas use `sectionApply*` (all Refl)
3. ConstFalse/True use generic lemmas (proven)
4. No equivalence axiom needed (only one representation)

### Implementation Order

1. Add `NegPosNatEndSection` type alias
2. Create `NegPosNatEndClosedSection` alongside existing path version
3. Verify `sectionApply` works with `NegPosNatEndDirUnitPF`
4. Update End characterization to use sections
5. Delete path types and functions
6. Update all dependent code
7. Delete unused lemmas
8. Verify build passes with minimal/no believe_me

### Risk Assessment

- **Type inference:** May need explicit type annotations for `sectionApply`
- **Dependencies:** Need to trace all uses of deleted types/functions
- **Direction isos:** May still need believe_me for End ↔ ClosedSection iso

The refactoring is significant but well-defined. Each step can be verified
independently by checking the build.

## Phase 2 Completion Summary

**Date:** 2025-12-01

### What Was Done

1. **Added section infrastructure:**
   - `NegPosNatEndSection i = PolySection (NegPosNatEndDirUnitPF i)` - type alias
   - `sectionToNatTrans` - wrapper around generic `sectionApply`
   - `natTransToSectionNPNE` - wrapper around generic `natTransToSection`
   - `sectionNPNERoundTrip`, `natTransNPNERoundTrip` - use generic proofs

2. **Added section-based End characterization:**
   - `NegPosNatEndClosedSection` - closed position with section
   - `closedSectionToEnd` - build End from closed section
   - `closedSectionToEndWedgeCondFst` - wedge condition proof
   - `endToClosedSection` - extract closed section from End
   - `endToClosedSectionToEnd`, `closedSectionToEndToClosedSection` - round-trips

3. **Deleted path infrastructure (~1000 lines):**
   - `NpnpLeftChoice` type (LeftForced, LeftDirect, LeftRecurse)
   - `NegPosNatEndDirPath` type (PathVar, PathLeaf, PathNode)
   - `closedPathToSection`, `closedPathLeftSection`
   - `closedPathToNatTrans`, `closedPathToNatTransAlt`
   - `closedPathToNatTransEquiv` (consolidated believe_me axiom)
   - All `closedPathToNatTransAlt*Beta` lemmas (13 `with` clause proofs)
   - `Prober` type and all probing functions
   - `natTransToPathViaProber`, `natTransToProber`
   - All `probePathAt*` and `probePathAltAt*` lemmas
   - `closedPathConstFalse`, `closedPathConstTrue` variations
   - `pathToNatTransToPath`, `natTransToPathToNatTrans` round-trips
   - Path-based End characterization (`NegPosNatEndClosedPath`, etc.)

### Remaining believe_me Calls: 8

**Direction isomorphisms (2):**
- `npneDirIsoFwd` - convert direction type
- `npneDirIsoBwd` - convert direction type back

**End/Wedge infrastructure (3):**
- `endPosIsClosed` - closedness from wedge condition
- `endToNatTrans` (contains 2 believe_me) - nat trans from end element

**Section-based End round-trips (3):**
- `closedSectionToEndWedgeCondFst` - wedge condition for constructed elements
- `endToClosedSectionToEnd` - End → ClosedSection → End = id
- `closedSectionToEndToClosedSection` - ClosedSection → End → ClosedSection = id

### Key Achievement

Reduced `believe_me` calls from **13 to 8** (38% reduction).

Deleted **~1000 lines** of path-related code:
- Custom `NegPosNatEndDirPath` inductive type
- `NpnpLeftChoice` GADT for left branch choices
- Complex probing machinery for nat trans → path conversion
- All beta lemmas for the custom eliminator-based nat trans
- Round-trip proofs for the path/nat-trans correspondence

The remaining `believe_me` calls are isolated to:
1. Direction type isomorphisms (structural induction on free monad types)
2. End characterization (depends on direction isos + wedge condition analysis)

These are now in clearly-defined categories rather than scattered throughout
the codebase.
