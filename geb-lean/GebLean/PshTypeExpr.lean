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

/-- The profunctor map for `pshIhom`. Given
`f : A' ⟶ A` and `g : B ⟶ B'`, produces
`pshIhom A B ⟶ pshIhom A' B'` by precomposing
with `f` and postcomposing with `g`. -/
def pshIhomProfMap
    {A A' B B' : Cᵒᵖ ⥤ Type v}
    (f : A' ⟶ A) (g : B ⟶ B') :
    pshIhom A B ⟶ pshIhom A' B' where
  app c φ :=
    ⟨fun d h a' => g.app d (φ.val d h (f.app d a')),
     fun d e k h a' => by
       dsimp only
       have hg : g.app e
           (B.map k (φ.val d h (f.app d a')))
           = B'.map k
             (g.app d (φ.val d h (f.app d a')))
           := congr_fun (g.naturality k) _
       have hf : A.map k (f.app d a')
           = f.app e (A'.map k a')
           := (congr_fun (f.naturality k) a').symm
       rw [← hg, φ.property d e k h, hf]⟩
  naturality c₁ c₂ k := by
    funext φ
    exact Subtype.ext (by funext d h a'; rfl)

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
