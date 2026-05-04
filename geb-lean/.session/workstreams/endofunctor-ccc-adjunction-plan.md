# Endofunctor CCC Adjunction Implementation Plan

> **For agentic workers:** REQUIRED: Use
> superpowers:executing-plans to implement this plan.
> Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Build `MonoidalClosed (PshRelEdge C ⥤
PshRelEdge C)` — the endofunctor category of
`PshRelEdge C` is cartesian closed.

**Architecture:** The internal hom `endoIhom F G`
(already defined) computes the powered end
`int_{(i,c)} [F(y), G(y)]^{Hom(E, y)}` over
representable edges. The adjunction
`tensorLeft F adj endoIhomFunctor F` is built
using (1) density of the representable embedding
to define the evaluation counit, (2) the
object-level CCC adjunction at representables
for the curry, and (3) round-trip proofs using
the Yoneda co-Yoneda lemma.

**Tech Stack:** Lean 4, mathlib (CategoryTheory),
GebLean project infrastructure.

---

## File Structure

- **Create**: `GebLean/Utilities/RepresentableDensity.lean`
  Representable functor definition + IsDense instance
- **Modify**: `GebLean/PshRelEdgeSeparation.lean`
  EndoIhom section: projection, curry, uncurry,
  adjunction, MonoidalClosed instance
- **Modify**: `GebLean/Utilities.lean`
  Add import for RepresentableDensity
- **Modify**: `GebLean.lean`
  Add import if needed for public API

---

## Task 1: Representable Functor

**Goal:** Define the contravariant representable
embedding as a proper Lean functor.

**Files:**

- Create: `GebLean/Utilities/RepresentableDensity.lean`
- Modify: `GebLean/Utilities.lean` (add import)

### Background

The representable embedding sends `(i, c)` to
`pshRelEdgeRepresentable i c`. It is
contravariant: a morphism `(i₁, c₁) ⟶ (i₂, c₂)`
in `WalkingSpan × Cᵒᵖ` induces a morphism
`rep(i₂, c₂) ⟶ rep(i₁, c₁)` by precomposition.
So the functor source is `(WalkingSpan × Cᵒᵖ)ᵒᵖ`.

It factors as: `spanRepresentableFunctor ⋙
pshRelEdgeSepFunctor C` where
`spanRepresentableFunctor` embeds into the span
presheaf category.

- [ ] **Step 1.1: Define spanRepresentableFunctor**

```lean
def spanRepresentableFunctor :
    (WalkingSpan × Cᵒᵖ)ᵒᵖ ⥤
      (WalkingSpan ⥤ Cᵒᵖ ⥤ Type (max u v))
```

Source: `(WalkingSpan × Cᵒᵖ)ᵒᵖ`.
`obj (op (i, c)) := spanRepresentable i c`.
For a morphism in the op category from
`op(i₀, c₀)` to `op(i₁, c₁)`, the unop is
`(φ : i₁ ⟶ i₀, g : c₁ ⟶ c₀)`.

The representable `Hom(i₀, -)` is covariant
in `j`. For `φ : i₁ ⟶ i₀`, precomposition
gives `Hom(i₀, j) → Hom(i₁, j)` via
`h ↦ φ ≫ h`, yielding
`spanRep(i₀, c) ⟶ spanRep(i₁, c)`.

So `spanRepresentableMapSpan c₀ φ` gives
`spanRep(i₀, c₀) ⟶ spanRep(i₁, c₀)`, and
`spanRepresentableMapPsh i₁ g` gives
`spanRep(i₁, c₀) ⟶ spanRep(i₁, c₁)`.
Their composition gives the map
`spanRep(i₀, c₀) ⟶ spanRep(i₁, c₁)`.

Proof obligations: `map_id` and `map_comp`.
`map_id`: both components are identity.
`map_comp`: associativity of the compositions.

Run: `lake build`
Expected: PASS

- [ ] **Step 1.2: Define pshRelEdgeRepresentableFunctor**

```lean
def pshRelEdgeRepresentableFunctor :
    (WalkingSpan × Cᵒᵖ)ᵒᵖ ⥤
      PshRelEdge.{u, v, max u v} C :=
  spanRepresentableFunctor ⋙
    pshRelEdgeSepFunctor C
```

Run: `lake build`
Expected: PASS

- [ ] **Step 1.3: Add import to Utilities.lean**

Add `import GebLean.Utilities.RepresentableDensity`

Run: `lake build && lake test`
Expected: PASS

- [ ] **Step 1.4: Commit**

```bash
git add GebLean/Utilities/RepresentableDensity.lean
git add GebLean/Utilities.lean
git commit -m "Representable embedding functor"
```

---

## Task 2: Density of Representable Embedding

**Goal:** Show `pshRelEdgeRepresentableFunctor` is
dense in `PshRelEdge C`.

**Files:**

- Modify: `GebLean/Utilities/RepresentableDensity.lean`

### Approach

Use `isDense_iff_fullyFaithful_restrictedULiftYoneda`
from mathlib: a full functor `F` is dense iff
`restrictedULiftYoneda F` is fully faithful.

Alternatively, show density directly by proving
every edge is a colimit of representable edges,
using:

1. `colimitOfRepresentable` for the span presheaf
   category (every span presheaf = colimit of
   representable span presheaves)
2. `pshRelEdgeSepFunctor` preserves colimits
   (left adjoint of `pshRelEdgeInclusionFunctor`)
3. The reflective counit
   `sep(incl(E)) ≅ E` gives the colimit structure

- [ ] **Step 2.1: Explore approach**

Use `_` as implementation to check types.
Try both approaches:
(a) `colimitOfRepresentable` + reflective subcategory
(b) `isDense_iff_fullyFaithful_restrictedULiftYoneda`

Pick whichever has fewer universe constraints.

- [ ] **Step 2.2: Prove IsDense instance**

```lean
instance pshRelEdgeRepresentableIsDense :
    pshRelEdgeRepresentableFunctor.IsDense
```

The proof should:

- Show that for every `E : PshRelEdge C`, `E` is
  a colimit of representable edges
- Use `colimitOfRepresentable` for the underlying
  presheaf + separation functor

Run: `lake build`
Expected: PASS (no sorry, no warnings)

- [ ] **Step 2.3: Commit**

```bash
git add GebLean/Utilities/RepresentableDensity.lean
git commit -m "Density of representable embedding"
```

---

## Task 3: End Projection at Representables

**Goal:** Define the projection from the
endofunctor internal hom end to the object-level
internal hom at representable edges.

**Files:**

- Modify: `GebLean/PshRelEdgeSeparation.lean`

- [ ] **Step 3.1: Define endoIhomProj**

At a representable edge `y(i,c)`, the identity
`𝟙 (rep i c) : rep i c ⟶ rep i c` is in the
power index set. The projection extracts this
component.

```lean
def endoIhomProj
    (F G : PshRelEdge C ⥤ PshRelEdge C)
    (i : WalkingSpan) (c : Cᵒᵖ) :
    endoIhomObj F G
      (pshRelEdgeRepresentable i c) ⟶
    pshRelEdgeExp
      (F.obj (pshRelEdgeRepresentable i c))
      (G.obj (pshRelEdgeRepresentable i c))
```

srcMap sends a dinatural family `h` to
`h.1 ⟨i, c, 𝟙 (rep i c)⟩`. Similarly for
tgtMap. The sq condition follows from the
product relation at the identity component.

Run: `lake build`
Expected: PASS

- [ ] **Step 3.2: Commit**

```bash
git add GebLean/PshRelEdgeSeparation.lean
git commit -m "End projection at representables"
```

---

## Task 4: Complete Curry Direction

**Goal:** Build the full curry map
`Nat(F ⊗ H, G) → Nat(H, [F, G])`.

**Files:**

- Modify: `GebLean/PshRelEdgeSeparation.lean`

### Subtasks

- [ ] **Step 4.1: Dinatural conditions for curry**

Prove that `endoIhomCurrySrcApp` satisfies
`endoDinatSpanCond` and `endoDinatPshCond`.

Uses `η.naturality` at the representable morphism
`β`, lifted through the base CCC adjunction.
Pattern: same as `endoDinatSpanCond_ihomMap`
(covar by rfl, contra by η.naturality +
Functor.map_comp).

- [ ] **Step 4.2: Build tgt version of curry**

`endoIhomCurryTgtApp` — same structure as
`endoIhomCurrySrcApp` but using `.tgtMap`.

- [ ] **Step 4.3: Build VertEdgeHom for curry**

Assemble srcMap + tgtMap + sq into
`endoIhomCurryAtE F H G η E :
  H.obj E ⟶ endoIhomObj F G E`

The sq condition: if `(s, t)` are related in
`H.obj E`, show the curried families are related
in `endoIhomRel F G E`. Uses the sq field of
`Closed.adj.homEquiv (η.app y)`.

- [ ] **Step 4.4: Show naturality in E**

For `g : E₁ ⟶ E₂`:
`H.map g ≫ curryAtE(E₂) = curryAtE(E₁) ≫
endoIhom.map(g)`

This should hold by computation: both sides
compose `H.map(g ≫ α)` with `curry(η_y)`.

- [ ] **Step 4.5: Assemble endoIhomCurry**

```lean
def endoIhomCurry
    (F H G : PshRelEdge C ⥤ PshRelEdge C)
    (η : (tensorLeft F).obj H ⟶ G) :
    H ⟶ (endoIhomFunctor F).obj G
```

Run: `lake build`
Expected: PASS

- [ ] **Step 4.6: Commit**

```bash
git add GebLean/PshRelEdgeSeparation.lean
git commit -m "Complete curry for endofunctor CCC"
```

---

## Task 5: Uncurry via Density + Evaluation

**Goal:** Build the uncurry map
`Nat(H, [F, G]) → Nat(F ⊗ H, G)`.

**Files:**

- Modify: `GebLean/PshRelEdgeSeparation.lean`

### Uncurry construction

At representable `y(i,c)`:

1. `μ.app(y) : H(y) ⟶ [F,G](y)`
2. `endoIhomProj : [F,G](y) ⟶ [F(y), G(y)]`
3. Compose: `μ.app(y) ≫ endoIhomProj :
   H(y) ⟶ [F(y), G(y)]`
4. Object-level uncurry:
   `(Closed.adj.homEquiv _ _).symm` gives
   `F(y) ⊗ H(y) ⟶ G(y)`

At general E: use density to extend the family
of uncurried maps at representables to a
natural transformation `F ⊗ H → G` at all edges.

- [ ] **Step 5.1: Define uncurry at representables**

```lean
def endoIhomUncurryAtRep
    (F H G : PshRelEdge C ⥤ PshRelEdge C)
    (μ : H ⟶ (endoIhomFunctor F).obj G)
    (i : WalkingSpan) (c : Cᵒᵖ) :
    (tensorLeft F).obj H |>.obj
      (pshRelEdgeRepresentable i c) ⟶
    G.obj (pshRelEdgeRepresentable i c)
```

- [ ] **Step 5.2: Show naturality at representables**

Show the family `{uncurryAtRep(i,c)}` is natural
with respect to representable morphisms. This
uses μ's naturality and the object-level CCC
naturality.

- [ ] **Step 5.3: Extend via density**

Use `Functor.IsDense` (from Task 2) to extend
the natural transformation from representables
to all edges. The extension uses the colimit
structure from density.

```lean
def endoIhomUncurry
    (F H G : PshRelEdge C ⥤ PshRelEdge C)
    (μ : H ⟶ (endoIhomFunctor F).obj G) :
    (tensorLeft F).obj H ⟶ G
```

Run: `lake build`
Expected: PASS

- [ ] **Step 5.4: Commit**

```bash
git add GebLean/PshRelEdgeSeparation.lean
git commit -m "Uncurry via density"
```

---

## Task 6: Round-Trip Proofs and Assembly

**Goal:** Show curry and uncurry are inverse,
build the adjunction and MonoidalClosed instance.

**Files:**

- Modify: `GebLean/PshRelEdgeSeparation.lean`

- [ ] **Step 6.1: Left inverse (curry then uncurry = id)**

Show `endoIhomCurry(endoIhomUncurry(μ)) = μ`
for all `μ : H ⟶ [F, G]`.

At representable y: both sides project to the
same component at `id_y`, by the object-level
curry-uncurry round-trip. For general E: by
naturality and density uniqueness.

- [ ] **Step 6.2: Right inverse (uncurry then curry = id)**

Show `endoIhomUncurry(endoIhomCurry(η)) = η`
for all `η : F ⊗ H ⟶ G`.

At representable y: the composition
`(curry η).app(y) ≫ proj ≫ uncurry` returns
to `η.app(y)` by the object-level round-trip.
For general E: by naturality.

- [ ] **Step 6.3: Naturality conditions**

`homEquiv_naturality_left_symm` and
`homEquiv_naturality_right` for
`Adjunction.mkOfHomEquiv`.

- [ ] **Step 6.4: Assemble MonoidalClosed**

```lean
instance endoFunctorClosed
    (F : PshRelEdge C ⥤ PshRelEdge C) :
    Closed F where
  rightAdj := endoIhomFunctor F
  adj := Adjunction.mkOfHomEquiv
    { homEquiv := fun H G =>
        { toFun := endoIhomCurry F H G
          invFun := endoIhomUncurry F H G
          left_inv := ...
          right_inv := ... }
      homEquiv_naturality_left_symm := ...
      homEquiv_naturality_right := ... }

instance endoFunctorMonoidalClosed :
    MonoidalClosed
      (PshRelEdge C ⥤ PshRelEdge C) where
  closed F := endoFunctorClosed F
```

Run: `lake build && lake test`
Expected: PASS

- [ ] **Step 6.5: Final commit**

```bash
git add GebLean/PshRelEdgeSeparation.lean
git commit -m "MonoidalClosed for PshRelEdge endofunctors"
```

---

## Dependency Graph

```text
Task 1 (repr functor) ──→ Task 2 (density)
                                 ↓
Task 3 (proj at reps) ──→ Task 5 (uncurry)
                                 ↓
Task 4 (curry) ─────────→ Task 6 (assembly)
```

Tasks 1, 3, 4 can be developed in parallel.
Task 2 is on the critical path.
Tasks 5 and 6 depend on Task 2.

## Mathlib References

- `Presheaf.colimitOfRepresentable` —
  Mathlib/CategoryTheory/Limits/Presheaf.lean
- `Functor.IsDense` —
  Mathlib/CategoryTheory/Functor/KanExtension/Dense.lean
- `coyonedaEquiv` —
  Mathlib/CategoryTheory/Yoneda.lean
- `Closed.adj.homEquiv` —
  Mathlib/CategoryTheory/Monoidal/Closed/Basic.lean
- `Adjunction.mkOfHomEquiv` —
  Mathlib/CategoryTheory/Adjunction/Basic.lean

## Lean-Specific Notes

- Build one definition at a time (CLAUDE.md rule)
- Use `_` to inspect goal types before writing proofs
- Use `VertEdgeHom.ext` for morphism equality in
  PshRelEdge
- Use `NatTrans.ext` + `funext` for NatTrans equality
- For dinatural proofs: covar by `rfl`, contra by
  `η.naturality` + `Functor.map_comp`
- Use `Closed.adj.homEquiv` to handle tensor/product
  order mismatches (includes braiding)
- Never use `sorry`, `admit`, `noncomputable`,
  `Classical`, or `axiom`
- 80 char line length limit
