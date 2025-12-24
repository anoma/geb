# PLang Category Judgments

This document describes the PLang formulation of category-judgment copresheaves
in `GebLean/PLang/CatJudgment.lean`.

## Overview

The PLang module provides a formulation of category-judgment copresheaves that:

1. Specializes the target category to `Type` (for universe `u`)
2. Uses explicit universe parameters throughout
3. Builds structures incrementally via sigma types

## Structure

The table below shows the PLang definitions and their roles:

| PLang Definition | Description |
|------------------|-------------|
| `ObjCopr.{u}` | Type of objects |
| `ObjMorObj.{u,v}` | Objects and morphisms types |
| `ObjMorProj` | Projection function type |
| `ObjMorMor` | Domain and codomain functions |
| `ObjMorCopr` | Bundled quiver data |
| `ObjMorIdObj` | Quiver plus identity type |
| `IdProj` | Identity morphism projection |
| `ObjMorIdMor` | Quiver with identity function |
| `ObjMorIdObjMor` | Bundled identity data (sigma) |
| `ObjMorIdObjMorEndo` | Identity endomorphism condition |
| `ObjMorIdCopr` | Identity copresheaf (subtype) |
| `ObjMorCompObj` | Quiver plus composition type |
| `CompProj` | Composition projection |
| `ObjMorCompProj` | Triple of projections |
| `ObjMorCompMor` | Full composition data |
| `ObjMorCompObjMor` | Bundled composition data (sigma) |
| `ObjMorCompObjMorMatch` | Composability condition |
| `ObjMorCompObjMorCompDom` | Domain preservation |
| `ObjMorCompObjMorCompCod` | Codomain preservation |
| `ObjMorCompObjMorCond` | Conjunction of conditions |
| `ObjMorCompCopr` | Composition copresheaf (subtype) |
| `CatJudgObj` | Full object data |
| `CatJudgMor` | All functions |
| `CatJudgObjMor` | Bundled object-morphism (sigma) |
| `CatJudgObjMorCond` | Identity and composition laws |
| `CatJudgCopr` | Full copresheaf |

## Universe Levels

The PLang formulation uses explicit universe parameters:

```text
CatJudgCopr.{u, v, w, x} : Type (max u v w x + 1)
```

Where:

- `u` controls the objects type (`ObjCopr.{u} = Sort u`)
- `v` controls the morphisms type
- `w` controls the identity type
- `x` controls the composition type

## Incremental Construction

The PLang approach builds structures layer by layer:

```text
ObjCopr           -- just objects
  |
ObjMorObj         -- add morphisms type
  |
ObjMorCopr        -- add dom/cod functions
  |
ObjMorIdObjMor    -- add identity data
  |
ObjMorIdCopr      -- add identity condition
  |
ObjMorCompObjMor  -- add composition data
  |
ObjMorCompCopr    -- add composition conditions
  |
CatJudgCopr       -- combine identity and composition
```

Each layer is a sigma type extending the previous, allowing operations to
be defined at intermediate stages.

## The Adjunction: Cat ⊣ CatJudgCopr

The adjunction consists of two functors:

### Embedding Functor Phi: Cat → CatJudgCopr

Given a category C with `C : Type u` and `Category.{v} C`:

```text
catToCatJudgCopr C : CatJudgCopr.{u+1, v+1, u+1, max u v + 1}
```

The components are:

| Component | Construction | Type |
|-----------|--------------|------|
| obj | C | Type u |
| mor | Σ (a b : C), (a ⟶ b) | Type (max u v) |
| idType | C | Type u |
| compType | Σ (a b c : C), (a ⟶ b) × (b ⟶ c) | Type (max u v) |
| dom | λ ⟨a, b, f⟩ => a | mor → obj |
| cod | λ ⟨a, b, f⟩ => b | mor → obj |
| idMor | λ a => ⟨a, a, 𝟙 a⟩ | obj → mor |
| left | λ ⟨a, b, c, f, g⟩ => ⟨b, c, g⟩ | compType → mor |
| right | λ ⟨a, b, c, f, g⟩ => ⟨a, b, f⟩ | compType → mor |
| composite | λ ⟨a, b, c, f, g⟩ => ⟨a, c, f ≫ g⟩ | compType → mor |

The coherence conditions (id_endo, comp_match, comp_dom, comp_cod) follow
from the definitions.

For a functor `F : C ⥤ D`, the induced morphism `catFunToCatJudgNatTrans F`
maps components via:

- objMap = F.obj
- morMap = λ ⟨a, b, f⟩ => ⟨F.obj a, F.obj b, F.map f⟩
- idMap = F.obj
- compMap = λ ⟨a, b, c, f, g⟩ => ⟨F.obj a, F.obj b, F.obj c, F.map f, F.map g⟩

### Reflection Functor L: CatJudgCopr → Cat

Given a CatJudgCopr s, construct a category via quotienting:

```text
catJudgCoprToCat s : Cat.{max s.v s.w s.x, s.u}
```

The construction uses:

1. Extract the underlying quiver from s (obj, mor, dom, cod)
2. Build FreeMor trees representing formal compositions
3. Quotient by FreeMorEquiv which equates:
   - Identity laws: id ≫ f ~ f, f ≫ id ~ f
   - Associativity: (f ≫ g) ≫ h ~ f ≫ (g ≫ h)
   - Identity witnesses: var(idMor i) ~ id(idObj i)
   - Composition witnesses: var(left c) ≫ var(right c) ~ var(composite c)

The resulting category has:

- Objects: s.obj
- Morphisms a → b: Quot (FreeMorEquiv s between a and b)
- Identity: class of FreeMor.id a
- Composition: class of FreeMor.comp

### Unit and Counit

The unit η : id → Phi ∘ L sends each CatJudgCopr s to Phi(L(s)):

- objMap: id (objects unchanged)
- morMap: inject s.mor into FreeMor via FreeMor.var, then bundle
- idMap, compMap: similarly inject through the quotienting process

The counit ε : L ∘ Phi → id sends L(Phi(C)) to C:

- Object map: id (objects are exactly C)
- Morphism map: interpret FreeMor trees as actual morphisms in C
  - FreeMor.var ⟨a, b, f⟩ ↦ f
  - FreeMor.id a ↦ 𝟙 a
  - FreeMor.comp g f ↦ (interpret f) ≫ (interpret g)

This is well-defined on the quotient because C satisfies the category axioms
and the identity/composition witnesses from Phi(C) exactly match C's structure.

### Triangle Identities

1. ε_{Phi C} ∘ Phi(η_C) = id_{Phi C}

   Starting from Phi(C), applying η gives the unit transformation, then
   applying ε reconstructs the original morphisms.

2. L(ε_s) ∘ η_{L(s)} = id_{L(s)}

   Starting from L(s), applying η injects into L(Phi(L(s))), then applying
   L(ε) quotients back to L(s). The quotient identifies terms that were
   equivalent in the first place.

## Connection to PolyPresentation

The PolyPresentation work provides an alternative characterization of
copresheaves via the density formula:

```text
PolyPresentationLoc D ≃ (D ⥤ Type)
```

The relationship between these approaches:

1. CatJudgCopr captures category-like data with explicit witnesses
2. PolyPresentation captures copresheaves as coequalizers of polynomials
3. The evaluation functor from CatJudgCopr connects to the copresheaf view

For a CatJudgCopr s, evaluating at each judgment level gives:

- evalAt objLevel s = s.obj : Type
- evalAt morLevel s = s.mor : Type
- etc.

This evaluation should factor through the density formula, connecting
the two characterizations.

## Planned Generalization

The eventual goal is to replace the target `Type` with an arbitrary
`CatJudgCopr`, making the definition recursive:

```text
CatJudgCoprRec.{u, v, w, x} (target : CatJudgCoprRec ...) : Type ...
```

This generalization would allow category-judgment copresheaves to be
valued in arbitrary category-judgment copresheaves rather than just
`Type`. Since `Type` itself embeds into `CatJudgCopr` via the discrete
category construction, this strictly generalizes the current formulation.

Properties of this generalization:

1. `CatJudgCopr` forms a topos (as a presheaf category)
2. Categories embed via the adjunction
3. The recursive definition provides internal hom objects
4. Category theory can be rebuilt as embedded in category-judgment theory

## Implementation Notes

The PLang definitions use:

- `Sort` instead of `Type` to include `Prop` at level 0
- Function composition for conditions
- Subtypes (`{x // P x}`) for constrained structures
- Sigma types for dependent bundling

## Files

- `GebLean/PLang/CatJudgment.lean`: Main definitions (complete)
- `GebLean/PLang/CatJudgmentAdjunction.lean`: Adjunction port (planned)
- `GebLean/CatJudgmentAdjunction.lean`: Original adjunction implementation

## References

- `docs/categories-as-copresheaves.md`: Mathematical background
- `docs/polynomial-presentation-localization.md`: PolyPresentation approach
