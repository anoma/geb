import GebLean.Paranatural
import GebLean.Utilities.Profunctors

/-!
# The hexagon category of endo-profunctor transformations

Given a category `C` and two endo-profunctors `P, Q : Cᵒᵖ × C ⥤ Type`,
we define the "hexagon category" whose:

- **Objects** are pairs `(c, f)` where `c : C` and `f : P(c,c) ⟶ Q(c,c)`

- **Morphisms** from `(c, f)` to `(d, g)` are morphisms `m : c ⟶ d` in `C`
  satisfying the hexagon condition:
  ```
  P(m,1) ≫ f ≫ Q(1,m) = P(1,m) ≫ g ≫ Q(m,1)
  ```
  Both sides are morphisms `P(d,c) ⟶ Q(c,d)`.

The name "hexagon" comes from the commutative diagram shape when drawn with
all six morphisms arranged around a hexagon.

-/

namespace GebLean

open CategoryTheory

universe v u


variable {C : Type u} [Category.{v} C]

section HexagonCategory

variable (P Q : Cᵒᵖ × C ⥤ Type v)

/-- An object of the hexagon category: a pair `(c, f)` where `c : C` and
`f : P(c,c) ⟶ Q(c,c)`. -/
structure HexagonObj where
  /-- The underlying object of `C`. -/
  base : C
  /-- The diagonal transformation `P(c,c) ⟶ Q(c,c)`. -/
  diag : P.obj (Opposite.op base, base) ⟶ Q.obj (Opposite.op base, base)

variable {P Q}

/-- The hexagon condition for a morphism `m : c ⟶ d` between objects
`(c, f)` and `(d, g)`. This says that the two paths around the hexagon
from `P(d,c)` to `Q(c,d)` are equal. -/
def HexagonCondition (X Y : HexagonObj P Q) (m : X.base ⟶ Y.base) : Prop :=
  Prof.map₁ P m ≫ X.diag ≫ Prof.map₂ Q m =
  Prof.map₂ P m ≫ Y.diag ≫ Prof.map₁ Q m

/-- A morphism in the hexagon category: a morphism `m : c ⟶ d` in `C`
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
  condition := by
    ext p
    simp only [Prof.map₁, Prof.map₂]
    rfl

/-- Composition of morphisms in the hexagon category. -/
def HexagonHom.comp {X Y Z : HexagonObj P Q}
    (f : HexagonHom X Y) (g : HexagonHom Y Z) : HexagonHom X Z where
  hom := f.hom ≫ g.hom
  condition := by
    ext p
    have fc := f.condition
    have gc := g.condition
    let p_gY := Prof.map₁ P g.hom p
    let p_fZ := Prof.map₂ P f.hom p
    have Pnat : Prof.map₂ P f.hom p_gY = Prof.map₁ P g.hom p_fZ :=
      Prof.map_comm P g.hom f.hom p
    have Qnat : ∀ q, Prof.map₂ Q g.hom (Prof.map₁ Q f.hom q) =
                     Prof.map₁ Q f.hom (Prof.map₂ Q g.hom q) :=
      fun q => Prof.map_comm Q f.hom g.hom q
    calc (Prof.map₂ Q (f.hom ≫ g.hom) ∘ X.diag ∘ Prof.map₁ P (f.hom ≫ g.hom)) p
        = Prof.map₂ Q g.hom (Prof.map₂ Q f.hom
            (X.diag (Prof.map₁ P f.hom (Prof.map₁ P g.hom p)))) := by
          simp only [Function.comp_apply, Prof.map₁_comp, Prof.map₂_comp]
        _ = Prof.map₂ Q g.hom
              (Prof.map₁ Q f.hom (Y.diag (Prof.map₂ P f.hom p_gY))) := by
          simp only [p_gY]
          exact congrArg (Prof.map₂ Q g.hom) (congrFun fc p_gY)
        _ = Prof.map₂ Q g.hom
              (Prof.map₁ Q f.hom (Y.diag (Prof.map₁ P g.hom p_fZ))) := by
          rw [Pnat]
        _ = Prof.map₁ Q f.hom
              (Prof.map₂ Q g.hom (Y.diag (Prof.map₁ P g.hom p_fZ))) := by
          rw [Qnat]
        _ = Prof.map₁ Q f.hom
              (Prof.map₁ Q g.hom (Z.diag (Prof.map₂ P g.hom p_fZ))) := by
          simp only [p_fZ]
          exact congrArg (Prof.map₁ Q f.hom) (congrFun gc p_fZ)
        _ = Prof.map₁ Q f.hom (Prof.map₁ Q g.hom
              (Z.diag (Prof.map₂ P g.hom (Prof.map₂ P f.hom p)))) := by
          simp only [p_fZ]
        _ = (Prof.map₁ Q (f.hom ≫ g.hom) ∘ Z.diag ∘ Prof.map₂ P (f.hom ≫ g.hom)) p := by
          simp only [Function.comp_apply, Prof.map₁_comp, Prof.map₂_comp]

/-- The hexagon category as a category instance. -/
instance : Category (HexagonObj P Q) where
  Hom := HexagonHom
  id := HexagonHom.id
  comp := HexagonHom.comp
  id_comp f := HexagonHom.ext' (Category.id_comp f.hom)
  comp_id f := HexagonHom.ext' (Category.comp_id f.hom)
  assoc f g h := HexagonHom.ext' (Category.assoc f.hom g.hom h.hom)

end HexagonCategory

section ProfunctorDialgebraProfunctor

/-!
### The profunctor-dialgebra profunctor

For endo-profunctors `P, Q : Cᵒᵖ × C ⥤ Type v`, we define the "profunctor-dialgebra
profunctor" `ProfDialgebraProf P Q : Cᵒᵖ ⥤ C ⥤ Type v` by:

```
(ProfDialgebraProf P Q)(a, b) = (P(b, a) ⟶ Q(a, b))
```

This is the profunctor-level analogue of the dialgebra profunctor for functors:
- Dialgebra profunctor for `F, G : C ⥤ D`: `(x, y) ↦ Hom_D(F(x), G(y))`
- Profunctor-dialgebra for `P, Q : Cᵒᵖ × C ⥤ Type`: `(a, b) ↦ (P(b, a) ⟶ Q(a, b))`

The "twist" in P's arguments (using `P(b, a)` instead of `P(a, b)`) accounts for
the mixed variance of profunctors.

The diagonal elements of this profunctor are exactly the objects of the hexagon
category, and the diagonal compatibility condition becomes the hexagon condition.
-/

variable (P Q : Cᵒᵖ × C ⥤ Type v)

/-- The profunctor-dialgebra profunctor for endo-profunctors `P` and `Q`.
At objects `(a, b)`, this is the morphism type `P(b, a) ⟶ Q(a, b)`.
Contravariant in `a` via `Q.map₁ ≫ _ ≫ P.map₂`, covariant in `b` via
`Q.map₂ ≫ _ ≫ P.map₁`. -/
@[simps]
def ProfDialgebraProf : Cᵒᵖ ⥤ C ⥤ Type v where
  obj a := {
    obj := fun b => P.obj (Opposite.op b, a.unop) → Q.obj (Opposite.op a.unop, b)
    map := fun {b b'} g φ p =>
      Prof.map₂ Q g (φ (Prof.map₁ P g p))
    map_id := fun b => by
      ext φ p
      simp only [Prof.map₁, Prof.map₂, types_id_apply, Opposite.op_unop, op_id]
      -- The goal has (𝟙 a, 𝟙 b) which equals 𝟙 (a, b) definitionally
      change Q.map (𝟙 (a, b)) (φ (P.map (𝟙 (Opposite.op b, Opposite.unop a)) p)) = φ p
      simp only [Functor.map_id, types_id_apply]
    map_comp := fun {b₁ b₂ b₃} g₁ g₂ => by
      ext φ p
      simp only [Prof.map₁, Prof.map₂, types_comp_apply]
      simp only [← FunctorToTypes.map_comp_apply, prod_comp, Category.id_comp, op_comp]
  }
  map {a₁ a₂} f := {
    app := fun b φ p =>
      Prof.map₁ Q f.unop (φ (Prof.map₂ P f.unop p))
    naturality := fun {b₁ b₂} g => by
      ext φ p
      simp only [types_comp_apply, Prof.map₁, Prof.map₂]
      simp only [← FunctorToTypes.map_comp_apply, prod_comp, Category.id_comp, Category.comp_id]
  }
  map_id a := by
    ext b φ p
    simp only [Prof.map₁, Prof.map₂, NatTrans.id_app, types_id_apply,
      Opposite.op_unop, unop_id, op_id]
    change Q.map (𝟙 (a, b)) (φ (P.map (𝟙 (Opposite.op b, Opposite.unop a)) p)) = φ p
    simp only [Functor.map_id, types_id_apply]
  map_comp {a₁ a₂ a₃} f g := by
    ext b φ p
    simp only [Prof.map₁, Prof.map₂, NatTrans.comp_app, types_comp_apply,
      ← FunctorToTypes.map_comp_apply, prod_comp, Category.id_comp,
      unop_comp, op_comp]

end ProfunctorDialgebraProfunctor

section HexagonDiagElemEquiv

/-!
### Hexagon category as diagonal elements

The hexagon category `HexagonObj P Q` is equivalent to the category of diagonal
elements of the profunctor-dialgebra profunctor `ProfDialgebraProf P Q`.

- Objects: A diagonal element `(c, φ)` where `φ ∈ (ProfDialgebraProf P Q)(c, c)`
  corresponds to `φ : P(c, c) ⟶ Q(c, c)`, which is exactly a hexagon object.

- Morphisms: The diagonal compatibility condition for `m : c ⟶ d` is:
  ```
  (ProfDialgebraProf P Q).map₂(m)(φ) = (ProfDialgebraProf P Q).map₁(m)(ψ)
  ```
  which expands to: for all `p : P(d, c)`,
  ```
  Q.map₂(m)(φ(P.map₁(m)(p))) = Q.map₁(m)(ψ(P.map₂(m)(p)))
  ```
  This is exactly the hexagon condition.
-/

variable (P Q : Cᵒᵖ × C ⥤ Type v)

/-- Convert a hexagon object to a diagonal element of the profunctor-dialgebra
profunctor. -/
@[simps]
def hexagonObjToDiagElem (x : HexagonObj P Q) : DiagElem (ProfDialgebraProf P Q) where
  base := x.base
  elem := x.diag

/-- Convert a diagonal element of the profunctor-dialgebra profunctor to a
hexagon object. -/
@[simps]
def diagElemToHexagonObj (x : DiagElem (ProfDialgebraProf P Q)) : HexagonObj P Q where
  base := x.base
  diag := x.elem

/-- Convert a hexagon morphism to a diagonal element morphism. -/
@[simps]
def hexagonHomToDiagElemHom {x y : HexagonObj P Q} (f : x ⟶ y) :
    hexagonObjToDiagElem P Q x ⟶ hexagonObjToDiagElem P Q y where
  base := f.hom
  compat := by
    simp only [DiagCompat, hexagonObjToDiagElem_base, ProfDialgebraProf_obj_obj]
    exact f.condition

/-- Convert a diagonal element morphism to a hexagon morphism. -/
@[simps]
def diagElemHomToHexagonHom {x y : DiagElem (ProfDialgebraProf P Q)}
    (f : x ⟶ y) : diagElemToHexagonObj P Q x ⟶ diagElemToHexagonObj P Q y where
  hom := f.base
  condition := by
    have hcompat := f.compat
    simp only [DiagCompat, ProfDialgebraProf_obj_obj] at hcompat
    exact hcompat

/-- The functor from the hexagon category to diagonal elements. -/
@[simps]
def hexagonToDiagElemFunctor : HexagonObj P Q ⥤ DiagElem (ProfDialgebraProf P Q) where
  obj := hexagonObjToDiagElem P Q
  map := hexagonHomToDiagElemHom P Q
  map_id _ := DiagElem.Hom.ext rfl
  map_comp _ _ := DiagElem.Hom.ext rfl

/-- The functor from diagonal elements to the hexagon category. -/
@[simps]
def diagElemToHexagonFunctor : DiagElem (ProfDialgebraProf P Q) ⥤ HexagonObj P Q where
  obj := diagElemToHexagonObj P Q
  map := diagElemHomToHexagonHom P Q
  map_id _ := HexagonHom.ext' rfl
  map_comp _ _ := HexagonHom.ext' rfl

/-- The hexagon category is isomorphic (as a category) to the diagonal elements
of the profunctor-dialgebra profunctor. -/
def hexagonDiagElemIsoCat :
    HexagonObj P Q ≅Cat DiagElem (ProfDialgebraProf P Q) where
  hom := (hexagonToDiagElemFunctor P Q).toCatHom
  inv := (diagElemToHexagonFunctor P Q).toCatHom
  hom_inv_id := by
    apply Cat.Hom.ext
    unfold Cat.Hom.toFunctor Functor.toCatHom
    simp only [Cat.Hom.comp_toFunctor, Cat.Hom.id_toFunctor]
    apply Functor.ext
    case h_obj => intro x; rfl
    case h_map =>
      intro x y f
      simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
      apply HexagonHom.ext'
      rfl
  inv_hom_id := by
    apply Cat.Hom.ext
    unfold Cat.Hom.toFunctor Functor.toCatHom
    simp only [Cat.Hom.comp_toFunctor, Cat.Hom.id_toFunctor]
    apply Functor.ext
    case h_obj => intro x; apply DiagElem.ext <;> rfl
    case h_map =>
      intro x y f
      simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
      apply DiagElem.Hom.ext
      rfl

/-- The equivalence between the hexagon category and diagonal elements of the
profunctor-dialgebra profunctor, derived from the categorical isomorphism. -/
def hexagonDiagElemEquiv :
    HexagonObj P Q ≌ DiagElem (ProfDialgebraProf P Q) :=
  Cat.equivOfIso (hexagonDiagElemIsoCat P Q)

end HexagonDiagElemEquiv

end GebLean
