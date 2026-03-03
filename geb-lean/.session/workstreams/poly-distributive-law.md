# Workstream: Polynomial Distributive Law (C3 + E1)

## Status

Active

## Context

Constructing the canonical distributive law
`lambda : T . D --> D . T` where `T = polyFreeMonad X P` and
`D = polyCofreeComonad X P`, and abstract GSOS rules (E1).

## Completed

- [x] Step 1: P-coalgebra on free monad trees
  (`polyFreeMCoalgStrAt`, `polyFreeMCoalgStr`, `polyFreeMCoalg`)
- [x] Step 2: polyScale coalgebra on T(D(A))
  (`polyDistLawScaleCoalgStrAt`, `polyDistLawScaleCoalgStr`,
  `polyDistLawScaleCoalg`)
- [x] Step 3: Distributive law morphism via anamorphism
  (`polyDistLawMor`)
- [x] Step 5: Counit coherence
  (`polyDistLawMor_head_fst`, `polyDistLaw_counit`)
- [x] Step 6: Unit coherence
  (`polyFreeMPure_proof_irrel`,
  `polyDistLaw_unit_approx`, `polyDistLaw_unit`)
- [x] Import added to `GebLean.lean`

## Remaining Tasks

- [ ] Step 4: Naturality of `polyDistLawMor`
  - Need `NatTrans` construction
  - Proof by `PolyCofix.ext` + induction on approx depth
  - **Node case compiles** (uses `polyDistLaw_annot_natural`
    + `congr 1` + `funext` + IH)
  - **Leaf case is blocked** by dependent-type transport:
    the P-index `(polyCofreeMapAt ... mA).head.2` differs
    propositionally from `mA.head.2` (equal by
    `polyCofreeMapAt_head_snd`), and this affects the
    children domain types.  `subst`/`rw`/`congr` all fail
    because the P-index appears in dependent positions.
  - **Recommended approach**: define a helper lemma
    `polyCofixApprox_intro_polyScale_congr` that takes
    the index and children equalities as `HEq` arguments
    (the version with `{p1 p2}` as implicit parameters
    and `subst` in the proof compiles).  The remaining
    issue is constructing the children `HEq` for the
    leaf case: each child from `polyFreeMCoalgStrAt` on
    the mapped tree relates to the mapped version of the
    child from the original tree via the IH, but the
    transport through `polyCofreeMapAt` children must be
    made explicit.
  - Utility lemmas available:
    - `polyDistLaw_annot_natural` (annotation compatibility)
    - `polyCofreeMapAt_head_snd` (P-index preservation)
    - `polyCofreeExtract_mapAt_val` (annotation value)
    - `polyCofreeCounit_naturality` (counit naturality)
    - `polyFreeMapAt_comp` (free map composition)
    - `polyCofixApprox_intro_polyScale_congr` (intro eq)
  - Consider writing a lemma about `polyCofreeMapAt`
    children: `(polyCofreeMapAt A B P f mA).children e1
    ≍ polyCofreeMapAt A B P f (mA.children e2)` when
    `HEq e1 e2` (with appropriate casts from `hidx`)
- [ ] Step 6: Unit coherence
  (`T.eta.app (D.obj A) >> dist.app A = D.map (T.eta.app A)`)
  - LHS: embed in leaf then unfold via anamorphism
  - RHS: map annotations by `polyFreeUnit`
  - Both produce same cofree element at each approx depth
  - Similar proof structure to `polyCofree_right_triangle_approx`
- [ ] Step 7: Comultiplication coherence
  - Both sides map `T(D(A)) --> D(D(T(A)))`
  - Use `polyCofixUnfoldHom_unique`: show both are coalgebra
    homomorphisms from the same source to the terminal
    `polyScale(D(T(A)), P)`-coalgebra
- [ ] Step 8: Multiplication coherence
  - Both sides map `T(T(D(A))) --> D(T(A))`
  - Similar approach to Step 7 with
    `polyCofixUnfoldHom_unique`
- [ ] Step 9: Package as `DistributiveLaw`
  - Requires Steps 4-8
- [ ] Steps 10-14: GSOS rules (E1)
  - `PolyGSOS.lean` (new file)
  - Fiberwise product, `GSOSRule` structure,
    canonical GSOS, distributive law from GSOS

## Notes

### Proof strategy for coherence axioms

The coherence proofs require one of two approaches:

1. **Direct approximation induction**: Show equality of
   `PolyCofixApprox` values at every depth by induction.
   Pattern: `polyCofree_right_triangle_approx` in
   PolyAlg.lean (lines 7334-7395). Each proof is 40-80
   lines due to index matching and transport handling.

2. **Terminal coalgebra uniqueness**: Use
   `polyCofixUnfoldHom_unique` (PolyAlg.lean:2296) to
   reduce to showing both sides are coalgebra
   homomorphisms from the same source. Requires defining
   the source coalgebra and proving the homomorphism
   conditions.

Approach (2) is preferred for Steps 7-8 since the
compositions are long, while approach (1) may be more
direct for Steps 4 and 6.

### Transport considerations

The leaf case of `polyFreeMCoalgStrAt` uses `hfib ▸` to
transport results. For our coalgebra
`polyDistLawScaleCoalg`, this transport is trivially
`rfl` since the structure map preserves fibers. The
anamorphism's `polyCofixUnfoldApprox` also uses `hx ▸`,
which is `rfl` for the same reason. This simplifies
the counit coherence proof (Step 5) but the other
coherence proofs involve compositions where the
transport is non-trivial.

### Monad/comonad functor actions

The monad `polyFreeMonad X P` has
`T.toFunctor.map f = polyFreeMap ... f` and
`T.toFunctor.obj A = polyFreeMCarrier A P` (literally,
through the adjunction). Similarly
`D.toFunctor.map f = polyCofreeMap ... f`. So the
distributive law at the abstract level uses the
same concrete morphisms.
