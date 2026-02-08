# Paranatural Topos

## Status

Phase 2b+ done. Phase 2c next.

## Question

Is there a subcategory of `Type v`-valued profunctors on
`C` whose morphisms are paranatural transformations and
which forms a topos? If so, what property characterizes
the profunctors in this subcategory?

## Context

Categories of profunctors with natural transformations
form presheaf toposes `[C^op x C, Type v]`. But
categories of profunctors with paranatural transformations
are not toposes in general -- they need not even be
Cartesian closed (Uustalu 2010).

Via `paranatWeightedLimitEquiv`, paranatural
transformations reduce to natural transformations:

```text
Paranat H G ≃
  (wedgeWeight H ⟶ profunctorOnTwistedArrow C G)
```

The natural transformations on the RHS live in the
presheaf topos `[Tw(C)^op, Type v]`, but the functors
`wedgeWeight H` and `profunctorOnTwistedArrow C G` form
a subcategory that is not closed under topos operations.

Neumann's di-Yoneda lemma (arXiv:2307.09289) has an
error in the proof and is not true, so hom-objects
derived from it do not work. Instead, we apply the
standard Yoneda lemma via the reduction to natural
transformations on `[Tw(C)^op, Type v]`.

## Hypothesis

The subcategory might be characterized by profunctors
"determined by their diagonal elements": those `P` for
which every element of `P(a, b)` is reachable from some
element of `P(c, c)` via the covariant and contravariant
actions.

### Formal candidates

1. **Kan extension along identity inclusion**: Let
   `iota : I -> Tw(C)` be the full subcategory
   inclusion of identity arrows. Then `P` is
   "diagonally determined" iff
   `profOnTwArr(C, P) =
    Lan_iota(iota*(profOnTwArr(C, P)))`.

2. **Reachability**: For all `a`, `b`, the canonical map
   from `coprod_{c, f : a -> c, g : c -> b} P(c, c)` to
   `P(a, b)` is surjective (or an isomorphism).

3. **Density formula on two variables**: `P` is naturally
   isomorphic to a coend
   `int^c P(c,c) x Hom(a,c) x Hom(c,b)`
   (density formula with two variables instead of four).

These three may be equivalent.

### Reflective subcategory hypothesis

The diagonalizable profunctors may form a reflective
subcategory of `[C^op x C, Type v]` (with natural
transformations). The reflector would "make" a profunctor
diagonalizable by quotienting over all maps from diagonal
elements. On the presheaf side, this corresponds to
`Lan_iota . iota*` on `[Tw(C)^op, Type v]`, where
`iota : I -> Tw(C)` is the full subcategory inclusion
of identity arrows.

If this reflector is left-exact, then by Giraud's theorem,
the diagonally-determined profunctors form a Grothendieck
topos.

## Research Findings

### Literature

- [x] Literature on paranatural transformations and
  categorical structure
  - Paranaturals compose (Mulry 1992, Pare-Roman 1998)
  - Not Cartesian closed (Uustalu 2010)
  - Di-Yoneda lemma has an error (Neumann)
  - Tambara modules = presheaves on "double" (Pastro-
    Street 2008) -- template for our question
  - Neumann-Licata POPL 2026: directed type theory
    via dinaturality
  - No published work on Grothendieck topologies on
    Tw(C) for "nice" profunctors
  - Diagonalized density formula not in standard
    literature

### Mathlib infrastructure

- [x] Kan extensions: pointwise formulas, lan/ran
  functors, `lan |- precomposition |- ran` adjunction
- [x] Reflective subcategories: `Reflective` typeclass
- [x] Grothendieck topologies, sheaf categories
- [x] Subobject classifiers (`HasClassifier`)
- [x] Cartesian closed (`MonoidalClosed`)
- [x] No unified "ElementaryTopos" definition
- [x] No left-exact-reflective = Grothendieck topos
  theorem

### Analysis results

- [x] Limits exist in paranatural category (computed
  pointwise; `profOnTwArr` preserves limits)
- [x] Colimits: unclear; requires image of `wedgeWeight`
  to be closed under colimits, which may fail
- [x] Cartesian closure: internal hom in
  `[Tw(C)^op, Type v]` likely leaves image of
  `profOnTwArr` (consistent with Uustalu)
- [x] The factorization category of `f` through `c`
  is `Hom_{Tw(C)}(id_c, f)`, connecting the Kan
  extension formula to our formalized infrastructure
- [x] `Lan_iota(F)(f) = colim over Factorisation(f) of F`
  matches `decFactFunctor` in our codebase:
  `DecFactObj F tw` is the category of elements of the
  Kan extension diagram at `tw`, and
  `TotalDecFactObj C F` is the total space of the
  `Cat`-valued Kan extension `Lan_iota(iota* F)`

## Experimental Plan

### Phase 2a: Connect decFactFunctor to diagonalization

**Done**: The assembly functor
`assemblyFunctor F tw : DecFactObj F tw ⥤ F.obj tw`
is formalized. It transports each decorated factorization
`(d, x)` (where `x ∈ F(𝟙 mid)`) to `F(tw)` via
`F.map(factToTwMorph tw d)`.

The definition `IsDiagDetermined F tw` captures when
this functor is an equivalence.

The formalized `decFactFunctor F` already computes the
fiberwise `Cat`-valued left Kan extension
`Lan_iota(iota* F)`: `DecFactObj F tw` is the category
of elements of the Kan extension diagram at `tw`.
Investigate whether this suffices for the diagonalization
monad, or whether we also need the full subcategory `I`
of `Tw(C)` on identity arrows as an explicit category.
Note that `I` is NOT equivalent to `C`: its morphisms
are section-retraction pairs
`(alpha : d -> c, beta : c -> d)` with
`beta . alpha = id_d`. There is a non-full,
non-faithful functor `p : I -> C` sending
`(alpha, beta) |-> beta`.

### Phase 2b: Analyze topos operations

**Done**. In `ParanaturalTopos.lean`:

1. **Terminal object**: `unitEndoProf` (constant PUnit
   profunctor), with `endoProfTerminal_isTerminal`.
2. **Binary products**: `prodEndoProf F G` (pointwise
   product), with projections `endoProfFst/Snd`, pairing
   `endoProfPair`, and universal property proofs
   `endoProfPair_fst/snd/unique`.
3. **Limit preservation**: `profOnTwArr_preservesLimitsOfShape`
   -- `profunctorOnTwistedArrowFunctor` preserves limits
   of any shape `J` when `D` has limits of shape `J`.
   Uses `show ... from inferInstance` to bridge the
   definitional equality `Functor.uncurry =
   Functor.currying.functor`.
4. **Equalizers**: `diagEqualizer α β I` is the
   diagonal equalizer subtype. `EqualizerClosedUnderCov`
   and `EqualizerClosedUnderContra` capture the conditions
   under which the covariant/contravariant actions bring
   off-diagonal elements back to the diagonal equalizer.
   `EqualizerWellDefined` is their conjunction. These
   conditions do not hold in general and do not follow
   from diagonal determination (see Phase 2b+).

### Phase 2b+: DiagDetProf full subcategory

**Done**. In `ParanaturalTopos.lean`:

1. **IsDiagDetermined fixed**: Changed from `IsEquivalence`
   to `EssSurj` (essential surjectivity of the assembly
   functor). The original `IsEquivalence` was too strong
   since multiple factorisations can map to the same
   element.

2. **BinaryFan.IsLimit**: `endoProfBinaryFan_isLimit`
   packages the binary product universal property as a
   mathlib `BinaryFan.IsLimit`.

3. **IsDiagDeterminedProf**: Type-valued form using
   `Function.Surjective` on `assemblyMapProf`. The
   assembly map sends `⟨fact, d⟩` with `d ∈ P(mid, mid)`
   to `P(a, b)` via contravariant then covariant actions.

4. **DiagDetProf full subcategory**: Defined via
   `ObjectProperty.FullSubcategory` on `EndoProf` with
   `endoProfCategory`. Morphisms are `Paranat` (wrapped
   in `InducedCategory.Hom`).

5. **Terminal object**: `unitEndoProf` is diag-determined
   (trivially surjective into `PUnit`).
   `unitDiagDetProf_isTerminal` proves it is terminal in
   `DiagDetProf`.

6. **Products do NOT preserve diag-determination**:
   Concrete counterexample on the walking arrow category.
   The product assembly requires a common factorization
   for both components, but each component may require a
   different one. `DiagDetProf` does not inherit products
   from `EndoProf`.

7. **Equalizers**: Diagonal determination does not imply
   `EqualizerClosedUnderCov` or
   `EqualizerClosedUnderContra`. The covariant action
   maps off-diagonal elements to diagonal elements, but
   there is no reason for `α` and `β` to agree on these
   elements.

**Implications**: The full subcategory `DiagDetProf` has
a terminal object but may lack both products and
equalizers. This is evidence against the hypothesis that
diag-determined profunctors form a topos. The issue is
that "diagonally determined" is too weak a condition:
it governs reachability but not the compatibility of
factorisations across components.

### Phase 2c: Investigate the diagonalization monad

1. Define `Lan_iota . iota*` on `[Tw(C)^op, Type v]`
2. Check idempotence
3. Check left-exactness
4. Identify fixed points

## Related Files

- `GebLean/ParanaturalTopos.lean` (experiments)
- `docs/paranatural-topos-research.md` (findings)
- `GebLean/ComprehensiveWeighted.lean`
- `GebLean/Paranatural.lean`
- `GebLean/Factorization.lean`
- `GebLean/Utilities/TwistedArrow.lean`
- `GebLean/Utilities/TwArrPresheaf.lean`

## Related Workstreams

- `comprehensive-factorization.md` (weighted limit
  characterization of paranatural transformations)
