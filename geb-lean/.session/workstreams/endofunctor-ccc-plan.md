# Workstream: Endofunctor CCC for PshRelEdge

## Status

All building blocks complete. Adjunction needs density.

## Completed Definitions

All in `PshRelEdgeSeparation.lean`, section `EndoIhom`:

- `endoIhom F G : PshRelEdge C ==> PshRelEdge C`
- `endoIhomFunctor F` : G |-> [F, G] (right adjoint)
- `endoIhomMapG` + 4 bifunctoriality lemmas
- `endoIhomCurrySrcApp` : curry product component

## Adjunction Plan

### Mathlib infrastructure to use

1. `colimitOfRepresentable` (Limits/Presheaf.lean):
   every presheaf is a colimit of representables

2. `uliftYonedaAdjunction` (Limits/Presheaf.lean):
   left Kan extension along Yoneda is left adjoint
   to `restrictedULiftYoneda`

3. `coyonedaEquiv` (Yoneda.lean):
   `Nat(Hom(X,-), F) ~= F(X)` for covariant F

4. `Functor.IsDense` (KanExtension/Dense.lean):
   abstract density, char. by restricted Yoneda
   being fully faithful

### Step 1: Density of pshRelEdgeRepresentable

The representable embedding is CONTRAVARIANT:
`(WalkingSpan x C^op)^op -> PshRelEdge C`.
It factors as: Yoneda into PSh(SpanCat) composed
with the separation functor.

To show density, use:
- `colimitOfRepresentable` for PSh(SpanCat)
  (Yoneda into PSh is dense)
- Separation is a left adjoint (preserves colimits)
- So the composed embedding is dense

### Step 2: Evaluation counit via density

Given density, for any endofunctor G and edge E:
1. Write G0(Y) = G(Y).src.obj d as a covariant
   functor PshRelEdge C -> Type
2. The dinatural family gives a natural
   transformation Hom(E, iota(-)) -> G0(iota(-))
   restricted to representables
3. By density (fully faithful restricted Yoneda),
   this extends uniquely to Hom(E, -) -> G0
4. By coyonedaEquiv, get element of G0(E)

### Step 3: Build Adjunction

Use `Adjunction.mkOfHomEquiv`:
- homEquiv: curry uses Closed.adj.homEquiv at
  representables + H.map(alpha)
- inverse uses density evaluation from Step 2
- naturality conditions from functoriality

### Alternative: Direct use of uliftYonedaAdjunction

The pattern from mathlib:
1. Define `restrictedULiftYoneda A : E ==> PSh`
   sending E |-> (A(-) -> E)
2. Left Kan extension `L` along uliftYoneda
3. `uliftYonedaAdjunction` gives `L adj restrictedULiftYoneda A`
4. The counit gives the evaluation map

Apply with A = pshRelEdgeRepresentableFunctor
to get the density adjunction, then derive the
endofunctor CCC adjunction from it.
