import GebLean.Paranatural
import GebLean.Utilities.Profunctors

/-!
# The hexagon category of endo-profunctor transformations

Given a category `C` and two endo-profunctors `P, Q : Cᵒᵖ × C ⥤ Type`,
we define the "hexagon category" whose:

- **Objects** are pairs `(c, f)` where `c : C` and `f : P(c,c) → Q(c,c)`

- **Morphisms** from `(c, f)` to `(d, g)` are morphisms `m : c → d` in `C`
  satisfying the hexagon condition:
  ```
  Q(1,m) ∘ f ∘ P(m,1) = Q(m,1) ∘ g ∘ P(1,m)
  ```
  Both sides are functions `P(d,c) → Q(c,d)`.

The name "hexagon" comes from the commutative diagram shape when drawn with
all six functions arranged around a hexagon.

-/

namespace GebLean

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C]

section HexagonCategory

variable (P Q : Cᵒᵖ × C ⥤ Type v)

/-- An object of the hexagon category: a pair `(c, f)` where `c : C` and
`f : P(c,c) → Q(c,c)`. -/
structure HexagonObj where
  /-- The underlying object of `C`. -/
  base : C
  /-- The diagonal transformation `P(c,c) → Q(c,c)`. -/
  diag : P.obj (Opposite.op base, base) → Q.obj (Opposite.op base, base)

variable {P Q}

/-- The hexagon condition for a morphism `m : c → d` between objects
`(c, f)` and `(d, g)`. This says that the two paths around the hexagon
from `P(d,c)` to `Q(c,d)` are equal. -/
def HexagonCondition (X Y : HexagonObj P Q) (m : X.base ⟶ Y.base) : Prop :=
  ∀ (p : P.obj (Opposite.op Y.base, X.base)),
    Prof.map₂ Q m (X.diag (Prof.map₁ P m p)) =
    Prof.map₁ Q m (Y.diag (Prof.map₂ P m p))

/-- A morphism in the hexagon category: a morphism `m : c → d` in `C`
satisfying the hexagon condition. -/
structure HexagonHom (X Y : HexagonObj P Q) where
  /-- The underlying morphism in `C`. -/
  hom : X.base ⟶ Y.base
  /-- The hexagon condition. -/
  condition : HexagonCondition X Y hom

@[ext]
theorem HexagonHom.ext' {X Y : HexagonObj P Q} {f g : HexagonHom X Y}
    (h : f.hom = g.hom) : f = g := by
  cases f; cases g; simp only [mk.injEq]; exact h

/-- The identity morphism in the hexagon category. -/
def HexagonHom.id (X : HexagonObj P Q) : HexagonHom X X where
  hom := 𝟙 X.base
  condition := fun p => by
    simp only [Prof.map₁, Prof.map₂]
    rfl

/-- Composition of morphisms in the hexagon category. -/
def HexagonHom.comp {X Y Z : HexagonObj P Q}
    (f : HexagonHom X Y) (g : HexagonHom Y Z) : HexagonHom X Z where
  hom := f.hom ≫ g.hom
  condition := fun p => by
    have fc := f.condition
    have gc := g.condition
    let p_gY := Prof.map₁ P g.hom p
    let p_fZ := Prof.map₂ P f.hom p
    have Pnat : Prof.map₂ P f.hom p_gY = Prof.map₁ P g.hom p_fZ :=
      Prof.map_comm P g.hom f.hom p
    have Qnat : ∀ q, Prof.map₂ Q g.hom (Prof.map₁ Q f.hom q) =
                     Prof.map₁ Q f.hom (Prof.map₂ Q g.hom q) :=
      fun q => Prof.map_comm Q f.hom g.hom q
    calc Prof.map₂ Q (f.hom ≫ g.hom) (X.diag (Prof.map₁ P (f.hom ≫ g.hom) p))
        = Prof.map₂ Q g.hom (Prof.map₂ Q f.hom
            (X.diag (Prof.map₁ P f.hom (Prof.map₁ P g.hom p)))) := by
          simp only [Prof.map₁_comp, Prof.map₂_comp]
        _ = Prof.map₂ Q g.hom
              (Prof.map₁ Q f.hom (Y.diag (Prof.map₂ P f.hom p_gY))) := by
          simp only [p_gY]; exact congrArg (Prof.map₂ Q g.hom) (fc p_gY)
        _ = Prof.map₂ Q g.hom
              (Prof.map₁ Q f.hom (Y.diag (Prof.map₁ P g.hom p_fZ))) := by
          rw [Pnat]
        _ = Prof.map₁ Q f.hom
              (Prof.map₂ Q g.hom (Y.diag (Prof.map₁ P g.hom p_fZ))) := by
          rw [Qnat]
        _ = Prof.map₁ Q f.hom
              (Prof.map₁ Q g.hom (Z.diag (Prof.map₂ P g.hom p_fZ))) := by
          simp only [p_fZ]; exact congrArg (Prof.map₁ Q f.hom) (gc p_fZ)
        _ = Prof.map₁ Q (f.hom ≫ g.hom) (Z.diag (Prof.map₂ P (f.hom ≫ g.hom) p)) := by
          change Prof.map₁ Q f.hom (Prof.map₁ Q g.hom
                   (Z.diag (Prof.map₂ P g.hom (Prof.map₂ P f.hom p)))) = _
          simp only [Prof.map₁_comp, Prof.map₂_comp]

/-- The hexagon category as a category instance. -/
instance : Category (HexagonObj P Q) where
  Hom := HexagonHom
  id := HexagonHom.id
  comp := HexagonHom.comp
  id_comp f := HexagonHom.ext' (Category.id_comp f.hom)
  comp_id f := HexagonHom.ext' (Category.comp_id f.hom)
  assoc f g h := HexagonHom.ext' (Category.assoc f.hom g.hom h.hom)

end HexagonCategory

end GebLean
