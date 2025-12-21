import GebLean.PolyAdjunctions
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-!
# Polynomial Presentations

This module defines the category of polynomial presentations, where objects
are parallel pairs of morphisms between polynomial functors and morphisms
are pairs that make both squares commute.

## Main Definitions

* `PolyPresentation D` - A parallel pair (P, Q, α, β) in CoprodCovarRepCat D
* `PolyPresentationHom` - Morphisms between presentations (commuting squares)
* `PolyPresentationCat D` - The category of polynomial presentations

## Mathematical Background

Every copresheaf F : D → Type can be expressed as a coequalizer of polynomial
functors. A polynomial presentation (P, Q, α, β) represents the copresheaf
coeq(eval(α), eval(β)) where eval is the fully faithful evaluation functor
from polynomial functors to copresheaves.

The category of polynomial presentations is equivalent to the category of
copresheaves (D ⥤ Type), providing a concrete description of copresheaves
in terms of polynomial functor operations.
-/

namespace GebLean

open CategoryTheory

universe u v w

variable (D : Type u) [Category.{v} D]

/-! ## Polynomial Presentations -/

/--
A polynomial presentation consists of two polynomial functors P and Q
together with two parallel morphisms α, β : P ⟶ Q.

The presentation represents the copresheaf coeq(eval(α), eval(β)).
-/
structure PolyPresentation where
  /-- The source polynomial functor -/
  src : CoprodCovarRepCat.{u, v, w} D
  /-- The target polynomial functor -/
  tgt : CoprodCovarRepCat.{u, v, w} D
  /-- The first parallel morphism -/
  fst : src ⟶ tgt
  /-- The second parallel morphism -/
  snd : src ⟶ tgt

namespace PolyPresentation

variable {D}

/--
A morphism of polynomial presentations (P, Q, α, β) → (P', Q', α', β')
consists of morphisms f : P → P' and g : Q → Q' making both squares commute:

```
    P --α--> Q          P --β--> Q
    |        |          |        |
    f        g    and   f        g
    |        |          |        |
    v        v          v        v
    P' -α'-> Q'         P' -β'-> Q'
```
-/
structure Hom (X Y : PolyPresentation.{u, v, w} D) where
  /-- The morphism on source polynomial functors -/
  srcHom : X.src ⟶ Y.src
  /-- The morphism on target polynomial functors -/
  tgtHom : X.tgt ⟶ Y.tgt
  /-- Commutativity for the first parallel morphism -/
  fst_comm : srcHom ≫ Y.fst = X.fst ≫ tgtHom
  /-- Commutativity for the second parallel morphism -/
  snd_comm : srcHom ≫ Y.snd = X.snd ≫ tgtHom

attribute [reassoc (attr := simp)] Hom.fst_comm Hom.snd_comm

namespace Hom

variable {X Y Z : PolyPresentation.{u, v, w} D}

@[ext]
theorem ext (f g : Hom X Y) (hsrc : f.srcHom = g.srcHom) (htgt : f.tgtHom = g.tgtHom) :
    f = g := by
  cases f
  cases g
  simp only [mk.injEq]
  exact ⟨hsrc, htgt⟩

/-- The identity morphism on a polynomial presentation. -/
def id (X : PolyPresentation.{u, v, w} D) : Hom X X where
  srcHom := 𝟙 X.src
  tgtHom := 𝟙 X.tgt
  fst_comm := by simp
  snd_comm := by simp

/-- Composition of morphisms of polynomial presentations. -/
def comp (f : Hom X Y) (g : Hom Y Z) : Hom X Z where
  srcHom := f.srcHom ≫ g.srcHom
  tgtHom := f.tgtHom ≫ g.tgtHom
  fst_comm := by
    rw [Category.assoc, g.fst_comm, ← Category.assoc, f.fst_comm, Category.assoc]
  snd_comm := by
    rw [Category.assoc, g.snd_comm, ← Category.assoc, f.snd_comm, Category.assoc]

@[simp]
theorem id_srcHom (X : PolyPresentation.{u, v, w} D) : (id X).srcHom = 𝟙 X.src := rfl

@[simp]
theorem id_tgtHom (X : PolyPresentation.{u, v, w} D) : (id X).tgtHom = 𝟙 X.tgt := rfl

@[simp]
theorem comp_srcHom (f : Hom X Y) (g : Hom Y Z) :
    (comp f g).srcHom = f.srcHom ≫ g.srcHom := rfl

@[simp]
theorem comp_tgtHom (f : Hom X Y) (g : Hom Y Z) :
    (comp f g).tgtHom = f.tgtHom ≫ g.tgtHom := rfl

end Hom

/-- The category structure on polynomial presentations. -/
instance category : Category (PolyPresentation.{u, v, w} D) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp f := by ext <;> simp
  comp_id f := by ext <;> simp
  assoc f g h := by ext <;> simp [Category.assoc]

@[simp]
theorem id_srcHom' (X : PolyPresentation.{u, v, w} D) :
    Hom.srcHom (𝟙 X) = 𝟙 X.src := rfl

@[simp]
theorem id_tgtHom' (X : PolyPresentation.{u, v, w} D) :
    Hom.tgtHom (𝟙 X) = 𝟙 X.tgt := rfl

@[simp]
theorem comp_srcHom' {X Y Z : PolyPresentation.{u, v, w} D} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).srcHom = f.srcHom ≫ g.srcHom := rfl

@[simp]
theorem comp_tgtHom' {X Y Z : PolyPresentation.{u, v, w} D} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).tgtHom = f.tgtHom ≫ g.tgtHom := rfl

end PolyPresentation

/--
The category of polynomial presentations over D.

Objects are parallel pairs (P, Q, α, β) where P, Q : CoprodCovarRepCat D
and α, β : P ⟶ Q are parallel morphisms.

Morphisms are pairs (f, g) making both squares commute.
-/
abbrev PolyPresentationCat.{u', v', w'} (D' : Type u') [Category.{v'} D'] :=
  PolyPresentation.{u', v', w'} D'

/-! ## Evaluation Functor

The evaluation functor sends a polynomial presentation (P, Q, α, β) to the
coequalizer of the induced natural transformations eval(α), eval(β) between
the corresponding copresheaves.
-/

section Evaluation

open CategoryTheory.Limits

variable {D}

/--
The copresheaf represented by a polynomial presentation. For a presentation
(P, Q, α, β), this is the coequalizer of the natural transformations
`ccrToFunctorMap α` and `ccrToFunctorMap β`.

This requires that the target category has coequalizers for these particular
natural transformations.
-/
noncomputable def PolyPresentation.toCopresheaf
    (X : PolyPresentation.{u, v, w} D)
    [HasCoequalizer (ccrToFunctorMap X.fst) (ccrToFunctorMap X.snd)] :
    D ⥤ Type (max w v) :=
  coequalizer (ccrToFunctorMap X.fst) (ccrToFunctorMap X.snd)

/--
For a morphism of polynomial presentations, the induced morphism on coequalizers.

Given f : X → Y where X = (P, Q, α, β) and Y = (P', Q', α', β'), the morphism
`ccrToFunctorMap f.tgtHom` coequalizes the parallel pair for Y (when composed
appropriately), so it factors through the coequalizer of X.
-/
noncomputable def PolyPresentation.Hom.toCopresheafHom
    {X Y : PolyPresentation.{u, v, w} D}
    (f : X ⟶ Y)
    [HasCoequalizer (ccrToFunctorMap X.fst) (ccrToFunctorMap X.snd)]
    [HasCoequalizer (ccrToFunctorMap Y.fst) (ccrToFunctorMap Y.snd)] :
    X.toCopresheaf ⟶ Y.toCopresheaf :=
  coequalizer.desc
    (ccrToFunctorMap f.tgtHom ≫ coequalizer.π _ _)
    (by
      rw [← Category.assoc, ← Category.assoc]
      rw [← ccrToFunctorMap_comp, ← ccrToFunctorMap_comp]
      rw [← f.fst_comm, ← f.snd_comm]
      rw [ccrToFunctorMap_comp, ccrToFunctorMap_comp]
      rw [Category.assoc, Category.assoc]
      congr 1
      exact coequalizer.condition _ _)

end Evaluation

end GebLean
