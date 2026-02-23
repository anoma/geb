# Presheaf Parametric Free Theorems

## Status: Active

## Goal

Formalize free theorems from Wadler's "Theorems for free!" and
the Reasonably Polymorphic blog post, generalize them using the
PshRel infrastructure, and complete the bridge between Type-level
and presheaf-level parametricity.

## Prerequisites

- `PshParametricFamily` structure (`PshTypeExpr.lean`)
- `pshTypeAbsRel_self_implies_parametric` (`PshTypeExpr.lean`)
- `yonedaULiftRel_graphRel` (`PshTypeExpr.lean`)
- `ParametricFamily.toPshParametricAtRep` (`PshTypeExpr.lean`)
- `dialgebraTypeExpr_relInterp_iff` (`ParanaturalTopos.lean`)
- `algebraParametricEquivParanat`,
  `dinaturalParametricEquivParanat` (`ParanaturalTopos.lean`)
- `ParametricFamily.wedge` (`ParanaturalTopos.lean`)
- `pshRelComp`, `pshBarrLiftSkel_related`,
  `pshArrowRelSkel_related` (`PshRelDouble.lean`)

## Items

### F1. Reverse bridge: PshParametricFamily to ParametricFamily

Restrict a `PshParametricFamily T.toPshTypeExpr` to
representable presheaves `yonedaULift I` to recover a
`ParametricFamily T`.

Given `pf : PshParametricFamily T.toPshTypeExpr`, define
`app I` by pulling back `pf.app (yonedaULift I)` through
`T.toPshTypeExpr_interp_iso`. The parametricity condition
at `f : I₀ → I₁` follows from `pf.parametric` at
`yonedaULiftMap f`, using the backward direction of
`fullRelInterp_bridge` (which is constructive -- no `choice`
hypothesis needed).

Together with `ParametricFamily.toPshParametricAtRep` (which
requires `choice`), this would establish:
- Choice-free: `PshParametricFamily T.toPshTypeExpr →
  ParametricFamily T`
- With choice: `ParametricFamily T →
  pshRelSectionsRelated`-at-representables

### F2. PshParametricFamily.wedge

The presheaf-level analogue of `ParametricFamily.wedge`:
every `PshParametricFamily` satisfies the presheaf profunctor
wedge condition.

Requires presheaf-level versions of:
- `PshTypeExpr.relInterp_of_offDiag`: off-diagonal elements
  produce related pairs via `relInterp`
- `PshTypeExpr.relInterp_implies_wedge`: `relInterp`-related
  implies profunctor wedge equality

The induction follows the same pattern as the Type-level
versions, using `pshBarrLiftSkel_related` and
`pshArrowRelSkel_related` from `PshRelDouble.lean`.

### F3. Identity free theorem [DONE]

`homTypeExpr_parametric_is_id` proves every parametric
family for `X → X` is the identity.
`homParametricEquivUnit` constructs the equivalence
`ParametricFamily homTypeExpr ≃ Unit`.

File: `ParanaturalTopos.lean`

### F4. General dialgebra naturality equivalence [DONE]

`dialgebraParametricEquivNatTrans` constructs
`ParametricFamily (dialgebraTypeExpr F G) ≃ (F ⟶ G)`.

The parametricity condition reduces via
`dialgebraTypeExpr_relInterp_iff` to the naturality
square, giving a direct equivalence.

This generalizes `algebraParametricEquivParanat` (which
handles `F → Id`) and one direction of
`dinaturalParametricEquivParanat` (which handles `Id → Id`).

The presheaf-level analogue would give
`PshParametricFamily (PshTypeExpr.arrow (leaf G₁) (leaf G₂))`
equivalent to `G₁ ⟹ G₂` for endofunctors `G₁, G₂` on
`PSh(C)`.

File: `ParanaturalTopos.lean`

### F5. Constant-type free theorem

For the one-variable type `a → a → a` (encoded as
`arrow var (arrow var var)`), parametricity forces the
two projections `fun a b => a` and `fun a b => b` as the
only inhabitants.

The parametricity condition at `f : I₀ → I₁` says: for
related inputs `(a₀, f a₀)` and `(b₀, f b₀)`, the output
`(app I₀ a₀ b₀, app I₁ (f a₀) (f b₀))` is related, i.e.,
`f (app I₀ a₀ b₀) = app I₁ (f a₀) (f b₀)`. Specializing
at `I₀ = Bool`, `I₁ = Unit`, `a₀ = true`, `b₀ = false`
forces the result to be one of the inputs. Separate
arguments distinguish the two cases and show no other
inhabitants exist.

This yields `ParametricFamily (arrow var (arrow var var))
≃ Bool` (or `≃ Fin 2`).

File: `ParanaturalTopos.lean`

### F6. Composition of fullRelInterp at PshRel level

Does `T.fullRelInterp` preserve `pshRelComp`? That is:
```
T.fullRelInterp (pshRelComp R S)
  = pshRelComp (T.fullRelInterp R) (T.fullRelInterp S)
```

- `var` case: trivial
- `app G T` case: depends on whether the Barr extension
  commutes with relation composition (a property of
  regular functors)
- `arrow` case: expected to fail in general, paralleling
  the Type-level counterexample
  `relInterp_decomp_homTypeExpr_fails`

This would characterize which presheaf type expressions
have a "functorial" relational interpretation, extending
the analysis in `RelInterpComposition.lean` to the presheaf
setting.

File: `PshTypeExpr.lean` or new file

### F7. Yoneda extension of ParametricFamily

Every presheaf is a colimit of representables. A
`ParametricFamily T` provides data at all representable
presheaves `yonedaULift I`. This data should extend
canonically to all presheaves via the density/Yoneda
extension argument, yielding a `PshParametricFamily
T.toPshTypeExpr` without requiring `choice`.

The construction:
- For a general presheaf `P`, write `P` as a colimit
  `colim (yonedaULift ∘ diagram)` (via the co-Yoneda
  lemma / density theorem)
- Define `app P` as the section induced by the
  parametric family's compatibility with the colimit
  cocone

This connects to the blog post's observation that relations
specialize to bifunctors: the Yoneda extension of a
parametric family is the enriched left Kan extension along
the Yoneda embedding.

This is more ambitious than F1 (which just restricts to
representables). It produces a genuine extension to
arbitrary presheaves, not just a round-trip.

### F8. typeExprWeight functor

Define `typeExprWeight : TypeExpr → (TwistedArrow Type
⥤ Type)` recursively from `relInterp` pairs.

At a twisted arrow `(f : I₀ → I₁)`:
- `var`: the graph `{ (a, b) | f a = b }`, equivalently
  just `I₀`
- `app F T`: `F`-image of `T.typeExprWeight` at `f`
- `arrow T₁ T₂`: the set of pairs `(α, β)` with
  `T₁.relInterp f`-inputs mapping to `T₂.relInterp f`-
  outputs

Construct a comparison natural transformation
`typeExprWeight T → wedgeWeight (T.toProfunctor)`.
For types where parametricity = paranaturality (F3, F4),
this should be an isomorphism. For the divergence type,
it should not be.

This is a concrete step toward W2a/W2b in
`parametric-generalization.md`.

File: new file or `WedgeWeightComputation.lean`

### F9. Parametric cofamilies and terminal coalgebras

Dual of the initial algebra equivalence
(`initialAlgebraParametricEquiv`).

Define `ParametricCofamily (coalgebraTypeExpr F)` and
show it is equivalent to elements of the terminal
`F`-coalgebra `νF`.

Design question: `ParametricFamily` uses universal
quantification (`∀ (I₀ I₁) (f), relInterp f ...`).
The dual should use existential quantification or
a co-end-like construction. The PshRel infrastructure
(symmetric in both presheaf arguments) should inform
the right formulation.

File: `ParanaturalTopos.lean`

## Priority

### Completed (F3, F4)
Concrete free theorems that directly formalize Wadler.

### Short-term (F1, F2)
Complete the presheaf-level theory and the Type/presheaf
bridge.

### Medium-term (F5, F6)
Additional free theorems and structural analysis of
relational interpretation.

### Long-term (F7, F8, F9)
Yoneda extension, twisted-arrow weights, and coalgebra
duality -- new territory requiring more infrastructure.
