# Copresheaf Self-Representation

This document describes how to represent the copresheaf topos [J, Type] as an
object within itself, enabling the CatJudgmentAdjunction to be expressed
entirely in terms of copresheaves.

## The Problem

We have:

- A judgment category J encoding categorical structure levels
- The copresheaf topos [J, Type] on J
- An adjunction Cat ⟷ [J, Type] (CatJudgmentAdjunction)

To express the full adjunction internally, we need [J, Type] itself to be
representable as an object (copresheaf) within [J, Type].

## The Universe Copresheaf

### General Construction

For any small category C, define the **universe copresheaf**:

```text
Universe_C : C → Type (u+1)
Universe_C(c) = Type u   (constant at all c)
```

This is the constant functor assigning the universe Type u to each object.

### Copresheaves as Sections

A copresheaf F : C → Type u corresponds to a choice of:

- For each c ∈ C, an element F(c) ∈ Type u = Universe_C(c)
- Functoriality: for f : c → c', a map F(f) : F(c) → F(c')

This is a **section** of the Grothendieck fibration for Universe_C:

```text
[C, Type u] ≃ Sections(∫ Universe_C → C)
```

### Universe Polymorphism

The construction is universe-polymorphic:

- Universe_C^{(u)} : C → Type (u+1) represents [C, Type u]
- Universe_C^{(u+1)} : C → Type (u+2) represents [C, Type (u+1)]
- Universe_C^{(u)} ∈ [C, Type (u+1)]

This gives a tower:

```text
Type u → [C, Type u] → [C, Type (u+1)] → [C, Type (u+2)] → ...
```

## The Judgment Universe Copresheaf

### Structured Universe

For the judgment category J, we use a **structured** universe copresheaf:

```text
JudgmentUniverse : J → Type (u+1)
```

Where JudgmentUniverse(j) captures "j-structures in Type u":

| Judgment Level | JudgmentUniverse Value |
| -------------- | ---------------------- |
| j_Obj | Type u |
| j_Mor | Σ(O : Type u), Type u |
| j_Quiv | Σ(O M : Type u), (M → O) × (M → O) |
| j_Cat | Σ(q : Quiv), IdentityData × CompositionData × Axioms |

Each level adds the appropriate categorical structure.

### Functoriality

The morphisms in J (refinements) induce projections:

- j_Mor → j_Obj: project out the object type
- j_Quiv → j_Mor: forget dom/cod functions
- j_Cat → j_Quiv: forget identity and composition

JudgmentUniverse is functorial with respect to these projections.

### Self-Representation

JudgmentUniverse is itself an object of [J, Type (u+1)]:

```text
JudgmentUniverse ∈ [J, Type (u+1)]
```

And [J, Type u] is "described by" JudgmentUniverse in the sense that sections
of JudgmentUniverse ARE copresheaves on J.

## Internal Category Structure

### Objects and Morphisms

To express [J, Type u] as an internal category in [J, Type (u+1)], we define:

1. **Object copresheaf**: Obj_J = JudgmentUniverse

2. **Morphism copresheaf**: Mor_J : J → Type (u+1)

   ```text
   Mor_J(j) = Σ(F G : JudgmentUniverse(j)), (F → G)
   ```

   At each level, morphisms are triples of source, target, and component map.

3. **Source and Target**: s, t : Mor_J → Obj_J

   ```text
   s(j)(F, G, η) = F
   t(j)(F, G, η) = G
   ```

4. **Identity**: id : Obj_J → Mor_J

   ```text
   id(j)(F) = (F, F, id_F)
   ```

5. **Composition**: comp : Mor_J ×_{Obj_J} Mor_J → Mor_J

   ```text
   comp(j)((F, G, η), (G, H, θ)) = (F, H, θ ∘ η)
   ```

### Naturality

The internal category structure must be compatible with J's morphisms:

- For f : j → j' in J, the induced maps on Obj_J and Mor_J must commute with
  source, target, identity, and composition

This follows from the functoriality of JudgmentUniverse.

## Connection to CatJudgmentAdjunction

### The Adjunction

The adjunction Cat ⟷ [J, Type] consists of:

- **Right adjoint** U : Cat → [J, Type]: sends category C to its judgment
  copresheaf (object type, morphism type, structure)

- **Left adjoint** F : [J, Type] → Cat: freely generates a category from a
  copresheaf

### Internal Expression

With the self-representation, both functors can be expressed internally:

1. **U internally**: For C a category, U(C) is a section of JudgmentUniverse

2. **F internally**: For P a copresheaf (section of JudgmentUniverse), F(P) is
   the "free category" on the structure encoded by P

The adjunction unit η : Id → U ∘ F and counit ε : F ∘ U → Id are natural
transformations between internal functors.

## Implementation Strategy

### Phase 1: Universe Copresheaf

1. Define `UniverseCopresheaf : (C : Cat) → C ⥤ Cat`

   ```lean
   def UniverseCopresheaf (C : Type*) [Category C] : C ⥤ Cat :=
     (Functor.const C).obj (Cat.of (Type u))
   ```

2. Prove that [C, Type u] ≃ Sections of ∫UniverseCopresheaf

### Phase 2: Judgment Universe

1. Define `JudgmentUniverse : J ⥤ Cat` for the judgment category J

2. Express each judgment level's structure type

3. Define the projection maps induced by J's morphisms

### Phase 3: Internal Category

1. Define Obj_J and Mor_J copresheaves

2. Define source, target, identity, composition

3. Verify internal category axioms

### Phase 4: Adjunction Internalization

1. Express U : Cat → [J, Type] using JudgmentUniverse

2. Express F : [J, Type] → Cat as internal functor

3. Prove adjunction internally

## Generalization

### Arbitrary Base Categories

The construction generalizes beyond J:

For any category C with a "structure functor" S : C → Cat describing what
structure each object encodes, we can represent [C, Type u] via S.

### Enriched Setting

In the Cat-enriched setting (from enriched-hom-unification.md):

- JudgmentUniverse is a Cat-valued functor
- The internal category [J, Type] is a Cat-enriched internal category
- This connects to the 2-categorical structure of Cat

### Topos-Theoretic Perspective

The self-representation connects to:

- Subobject classifiers in [J, Type]
- Generic families and universe constructions
- The "object classifier" in higher topos theory

## References

- Internal categories in toposes
- Universe constructions in type theory
- Grothendieck fibrations and sections
- Presheaf/copresheaf topos theory
