import GebLean.PshRelDouble

/-!
# Type Expressions for Presheaf Categories

Generalization of `TypeExpr` (in `ParanaturalTopos.lean`)
from `Type` to presheaf categories `PSh(C) = Cᵒᵖ ⥤ Type v`.
Each `PshTypeExpr` describes a type constructor
built from a variable using arrows and functor
applications.

- `interp T P Q` interprets `T` as a profunctor on
  `PSh(C)`, assigning a presheaf to each pair
  `(P, Q)` (with `P` contravariant and `Q` covariant).

- `relInterp T α` lifts a morphism `α : P ⟶ Q` to a
  relation on `T.interp P P` and `T.interp Q Q` via
  Barr extension for functor application and the
  arrow relation for function spaces.
-/

namespace GebLean

open CategoryTheory

universe v

variable {C : Type v} [Category.{v} C]

/-- A type expression for presheaf categories. Each
constructor describes how a type is built from a
variable:
- `var`: the variable itself
- `app G T`: apply a presheaf endofunctor `G` to `T`
- `arrow T₁ T₂`: the internal hom `T₁ → T₂` -/
inductive PshTypeExpr
    (C : Type v) [Category.{v} C] :
    Type (v + 1) where
  | var : PshTypeExpr C
  | app :
    ((Cᵒᵖ ⥤ Type v) ⥤ (Cᵒᵖ ⥤ Type v)) →
    PshTypeExpr C → PshTypeExpr C
  | arrow :
    PshTypeExpr C →
    PshTypeExpr C → PshTypeExpr C

/-- A covariant endofunctor applied to the bare
variable. Equivalent to `.app G .var`. -/
abbrev PshTypeExpr.leaf
    (G : (Cᵒᵖ ⥤ Type v) ⥤
         (Cᵒᵖ ⥤ Type v)) :
    PshTypeExpr C :=
  .app G .var

/-- The interpretation of a type expression as a
profunctor on `PSh(C)`: `interp T P Q` assigns a
presheaf to each pair `(P, Q)`, where `P` is
contravariant and `Q` is covariant.
- `var` returns `Q`
- `app G T` applies `G` to the interpretation of `T`
- `arrow T₁ T₂` forms the internal hom from `T₁`
  (with swapped variance) to `T₂` -/
def PshTypeExpr.interp :
    PshTypeExpr C →
    (Cᵒᵖ ⥤ Type v) → (Cᵒᵖ ⥤ Type v) →
    (Cᵒᵖ ⥤ Type v)
  | .var, _, Q => Q
  | .app G T, P, Q => G.obj (T.interp P Q)
  | .arrow T₁ T₂, P, Q =>
    pshIhom (T₁.interp Q P) (T₂.interp P Q)

/-- The relational interpretation of a type
expression. Given a morphism `α : P ⟶ Q`, lifts it
to a relation between `T.interp P P` and
`T.interp Q Q`:
- `var` gives the graph relation of `α`
- `app G T` applies Barr extension of `G` to the
  relational interpretation of `T`
- `arrow T₁ T₂` uses the arrow relation on the
  relational interpretations of `T₁` and `T₂` -/
def PshTypeExpr.relInterp :
    (T : PshTypeExpr C) →
    {P Q : Cᵒᵖ ⥤ Type v} →
    (α : P ⟶ Q) →
    PshRel (T.interp P P) (T.interp Q Q)
  | .var, _, _, α => pshRelGraph α
  | .app G T, _, _, α =>
    pshBarrLiftSkel G (T.relInterp α)
  | .arrow T₁ T₂, _, _, α =>
    pshArrowRelSkel
      (T₁.relInterp α)
      (T₂.relInterp α)

/-- The profunctor map for a type expression:
given `f : P' ⟶ P` (contravariant) and
`g : Q ⟶ Q'` (covariant), maps
`T.interp P Q ⟶ T.interp P' Q'`. -/
def PshTypeExpr.profMap :
    (T : PshTypeExpr C) →
    {P P' Q Q' : Cᵒᵖ ⥤ Type v} →
    (f : P' ⟶ P) → (g : Q ⟶ Q') →
    T.interp P Q ⟶ T.interp P' Q'
  | .var, _, _, _, _, _, g => g
  | .app G T, _, _, _, _, f, g =>
    G.map (T.profMap f g)
  | .arrow T₁ T₂, _, _, _, _, f, g =>
    pshIhomProfMap
      (T₁.profMap g f)
      (T₂.profMap f g)

/-- Identity law for `PshTypeExpr.profMap`. -/
@[simp]
theorem PshTypeExpr.profMap_id
    (T : PshTypeExpr C)
    (P Q : Cᵒᵖ ⥤ Type v) :
    T.profMap (𝟙 P) (𝟙 Q) =
      𝟙 (T.interp P Q) := by
  induction T generalizing P Q with
  | var => rfl
  | app G T ih =>
    change G.map (T.profMap (𝟙 P) (𝟙 Q)) = _
    rw [ih]
    exact G.map_id _
  | arrow T₁ T₂ ih₁ ih₂ =>
    change pshIhomProfMap
      (T₁.profMap (𝟙 Q) (𝟙 P))
      (T₂.profMap (𝟙 P) (𝟙 Q)) = _
    rw [ih₁, ih₂, pshIhomProfMap_id]
    rfl

/-- Composition law for `PshTypeExpr.profMap`. -/
theorem PshTypeExpr.profMap_comp
    (T : PshTypeExpr C)
    {P P' P'' Q Q' Q'' : Cᵒᵖ ⥤ Type v}
    (f : P' ⟶ P) (f' : P'' ⟶ P')
    (g : Q ⟶ Q') (g' : Q' ⟶ Q'') :
    T.profMap (f' ≫ f) (g ≫ g') =
      T.profMap f g ≫ T.profMap f' g' := by
  induction T generalizing P P' P'' Q Q' Q'' with
  | var => rfl
  | app G T ih =>
    change G.map (T.profMap (f' ≫ f) (g ≫ g')) =
      G.map (T.profMap f g) ≫
        G.map (T.profMap f' g')
    rw [ih, G.map_comp]
  | arrow T₁ T₂ ih₁ ih₂ =>
    change pshIhomProfMap
        (T₁.profMap (g ≫ g') (f' ≫ f))
        (T₂.profMap (f' ≫ f) (g ≫ g')) =
      pshIhomProfMap
        (T₁.profMap g f)
        (T₂.profMap f g) ≫
      pshIhomProfMap
        (T₁.profMap g' f')
        (T₂.profMap f' g')
    rw [ih₁ (P := Q'') (P' := Q')
        (P'' := Q) (Q := P'') (Q' := P')
        (Q'' := P) g' g f' f,
      ih₂ f f' g g',
      pshIhomProfMap_comp]

/-- The profunctor associated to a type expression:
a functor
`(Cᵒᵖ ⥤ Type v)ᵒᵖ × (Cᵒᵖ ⥤ Type v) ⥤ (Cᵒᵖ ⥤ Type v)`
defined by `T.interp` on objects and `T.profMap`
on morphisms. -/
def PshTypeExpr.toProfunctor
    (T : PshTypeExpr C) :
    (Cᵒᵖ ⥤ Type v)ᵒᵖ × (Cᵒᵖ ⥤ Type v) ⥤
      (Cᵒᵖ ⥤ Type v) where
  obj p := T.interp p.1.unop p.2
  map {p q} fg := T.profMap fg.1.unop fg.2
  map_id p := by
    change T.profMap (𝟙 _) (𝟙 _) = _
    exact T.profMap_id p.1.unop p.2
  map_comp {_p _q _r} fg gh := by
    simp only [prod_comp, unop_comp]
    exact T.profMap_comp fg.1.unop gh.1.unop
      fg.2 gh.2

/-- The relational interpretation of a leaf
`app G var` reduces to `pshBarrLiftSkel G` applied
to the graph relation of `α`. -/
@[simp]
theorem PshTypeExpr.leaf_relInterp
    (G : (Cᵒᵖ ⥤ Type v) ⥤
         (Cᵒᵖ ⥤ Type v))
    {P Q : Cᵒᵖ ⥤ Type v}
    (α : P ⟶ Q) :
    (PshTypeExpr.leaf G).relInterp α =
      pshBarrLiftSkel G (pshRelGraph α) :=
  rfl

end GebLean
