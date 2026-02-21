import GebLean.PshRelDouble
import GebLean.ParanaturalTopos
import Mathlib.CategoryTheory.Monoidal.Closed.Types

/-!
# Type Expressions for Presheaf Categories

Generalization of `TypeExpr` (in `ParanaturalTopos.lean`)
from `Type` to presheaf categories
`PSh(C) = Cᵒᵖ ⥤ Type (max u v)`.
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

- `fullRelInterp T R` generalizes `relInterp` to
  accept an arbitrary `PshRel P Q` (not just a
  morphism graph). This is the full relational
  interpretation from Wadler's "Theorems for free!".

- `PshTypeAbs T` is the type of presheaf-level type
  abstractions: families assigning to each presheaf
  `P` a section of `T.interp P P`.

- `pshTypeAbsRel T t₀ t₁` is Wadler's relational
  interpretation of `∀X. T(X)`: type abstractions
  are related if they map related presheaves to
  related sections.

- `TypeExpr.toPshTypeExpr` embeds the universe-0
  type expressions into `PshTypeExpr (Type 0)` via
  the Yoneda extension.
-/

namespace GebLean

open CategoryTheory

universe u v

variable {C : Type u} [Category.{v} C]

/-- A type expression for presheaf categories. Each
constructor describes how a type is built from a
variable:
- `var`: the variable itself
- `app G T`: apply a presheaf endofunctor `G` to `T`
- `arrow T₁ T₂`: the internal hom `T₁ → T₂` -/
inductive PshTypeExpr
    (C : Type u) [Category.{v} C] :
    Type (max (u + 1) (v + 1)) where
  | var : PshTypeExpr C
  | app :
    ((Cᵒᵖ ⥤ Type (max u v)) ⥤
      (Cᵒᵖ ⥤ Type (max u v))) →
    PshTypeExpr C → PshTypeExpr C
  | arrow :
    PshTypeExpr C →
    PshTypeExpr C → PshTypeExpr C

/-- A covariant endofunctor applied to the bare
variable. Equivalent to `.app G .var`. -/
abbrev PshTypeExpr.leaf
    (G : (Cᵒᵖ ⥤ Type (max u v)) ⥤
         (Cᵒᵖ ⥤ Type (max u v))) :
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
    (Cᵒᵖ ⥤ Type (max u v)) →
    (Cᵒᵖ ⥤ Type (max u v)) →
    (Cᵒᵖ ⥤ Type (max u v))
  | .var, _, Q => Q
  | .app G T, P, Q => G.obj (T.interp P Q)
  | .arrow T₁ T₂, P, Q =>
    (T₁.interp Q P).functorHom (T₂.interp P Q)

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
    {P Q : Cᵒᵖ ⥤ Type (max u v)} →
    (α : P ⟶ Q) →
    PshRel (T.interp P P) (T.interp Q Q)
  | .var, _, _, α => pshRelGraph α
  | .app G T, _, _, α =>
    pshBarrLiftSkel G (T.relInterp α)
  | .arrow T₁ T₂, _, _, α =>
    pshArrowRelSkel
      (T₁.relInterp α)
      (T₂.relInterp α)

/-- The full relational interpretation of a
presheaf type expression at an arbitrary relation
`R : PshRel P Q`. This generalizes `relInterp`,
which only accepts morphism graphs
(`pshRelGraph α`). Each `var` contributes `R`
itself, each `app G T` contributes
`pshBarrLiftSkel G (T.fullRelInterp R)`, and each
`arrow` contributes `pshArrowRelSkel`.

This is the presheaf-category generalization of
`TypeExpr.fullRelInterp`. -/
def PshTypeExpr.fullRelInterp :
    (T : PshTypeExpr C) →
    {P Q : Cᵒᵖ ⥤ Type (max u v)} →
    (R : PshRel P Q) →
    PshRel (T.interp P P) (T.interp Q Q)
  | .var, _, _, R => R
  | .app G T, _, _, R =>
    pshBarrLiftSkel G (T.fullRelInterp R)
  | .arrow T₁ T₂, _, _, R =>
    pshArrowRelSkel
      (T₁.fullRelInterp R)
      (T₂.fullRelInterp R)

/-- `fullRelInterp` applied to the graph of a
morphism `α` coincides with `relInterp α`. -/
theorem PshTypeExpr.fullRelInterp_graph
    (T : PshTypeExpr C)
    {P Q : Cᵒᵖ ⥤ Type (max u v)}
    (α : P ⟶ Q) :
    T.fullRelInterp (pshRelGraph α) =
      T.relInterp α := by
  induction T with
  | var => rfl
  | app G T ih =>
    simp only [fullRelInterp, relInterp, ih]
  | arrow T₁ T₂ ih₁ ih₂ =>
    simp only [fullRelInterp, relInterp, ih₁, ih₂]

/-- The profunctor map for a type expression:
given `f : P' ⟶ P` (contravariant) and
`g : Q ⟶ Q'` (covariant), maps
`T.interp P Q ⟶ T.interp P' Q'`. -/
def PshTypeExpr.profMap :
    (T : PshTypeExpr C) →
    {P P' Q Q' : Cᵒᵖ ⥤ Type (max u v)} →
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
    (P Q : Cᵒᵖ ⥤ Type (max u v)) :
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
    {P P' P'' Q Q' Q'' :
      Cᵒᵖ ⥤ Type (max u v)}
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
`(Cᵒᵖ ⥤ Type (max u v))ᵒᵖ × (Cᵒᵖ ⥤ Type (max u v))
⥤ (Cᵒᵖ ⥤ Type (max u v))`
defined by `T.interp` on objects and `T.profMap`
on morphisms. -/
def PshTypeExpr.toProfunctor
    (T : PshTypeExpr C) :
    (Cᵒᵖ ⥤ Type (max u v))ᵒᵖ ×
      (Cᵒᵖ ⥤ Type (max u v)) ⥤
      (Cᵒᵖ ⥤ Type (max u v)) where
  obj p := T.interp p.1.unop p.2
  map {p q} fg := T.profMap fg.1.unop fg.2
  map_id p := by
    change T.profMap (𝟙 _) (𝟙 _) = _
    exact T.profMap_id p.1.unop p.2
  map_comp {_p _q _r} fg gh := by
    simp only [prod_comp, unop_comp]
    exact T.profMap_comp fg.1.unop gh.1.unop
      fg.2 gh.2

/-- Two sections of presheaves `F` and `G` are
related by `R : PshProdOver F G` if there exists a
section of `R` that projects to the given sections
at each stage. -/
def PshProdOver.sectionsRelated
    {F G : Cᵒᵖ ⥤ Type (max u v)}
    (R : PshProdOver F G)
    (s₀ : F.sections) (s₁ : G.sections) : Prop :=
  ∃ (r : R.left.sections),
    ∀ (c : Cᵒᵖ),
      (R.hom.app c (r.val c)).1 = s₀.val c ∧
      (R.hom.app c (r.val c)).2 = s₁.val c

/-- Transporting `sectionsRelated` along an
isomorphism of over-objects: if `R ≅ R'` in
`Over (F × G)`, then a witness in `R` transfers to
one in `R'`, and conversely. -/
private theorem PshProdOver.sectionsRelated_iso
    {F G : Cᵒᵖ ⥤ Type (max u v)}
    {R R' : PshProdOver F G}
    (iso : R ≅ R')
    (s₀ : F.sections) (s₁ : G.sections) :
    R.sectionsRelated s₀ s₁ ↔
      R'.sectionsRelated s₀ s₁ := by
  suffices ∀ {A B : PshProdOver F G}
      (_ : A ≅ B),
      A.sectionsRelated s₀ s₁ →
      B.sectionsRelated s₀ s₁ from
    ⟨this iso, this iso.symm⟩
  intro A B φ ⟨r, hr⟩
  refine ⟨⟨fun c => φ.hom.left.app c (r.val c),
    fun {c c'} f => ?_⟩, fun c => ?_⟩
  · have h := congr_fun
      (φ.hom.left.naturality f) (r.val c)
    simp only [types_comp_apply] at h
    rw [r.property f] at h; exact h.symm
  · have comm : B.hom.app c
        (φ.hom.left.app c (r.val c)) =
        A.hom.app c (r.val c) :=
      congr_fun (congr_app (Over.w φ.hom) c)
        (r.val c)
    constructor
    · rw [comm]; exact (hr c).1
    · rw [comm]; exact (hr c).2

/-- Two sections of presheaves are related by a
`PshRel` if they are related by some representative
of the isomorphism class. -/
def pshRelSectionsRelated
    {F G : Cᵒᵖ ⥤ Type (max u v)}
    (R : PshRel F G)
    (s₀ : F.sections) (s₁ : G.sections) : Prop :=
  R.lift
    (fun (R : PshProdOver F G) =>
      R.sectionsRelated s₀ s₁)
    (fun _ _ ⟨iso⟩ => propext
      (PshProdOver.sectionsRelated_iso iso s₀ s₁))

/-- A type abstraction for a presheaf type
expression `T` is a family assigning to each
presheaf `P` a section of the diagonal presheaf
`T.interp P P`. This is the presheaf-category
generalization of `TypeAbs`. -/
abbrev PshTypeAbs (T : PshTypeExpr C) :=
  (P : Cᵒᵖ ⥤ Type (max u v)) →
    (T.interp P P).sections

/-- Relatedness of presheaf type abstractions
under the full relational interpretation. Two
type abstractions `t₀` and `t₁` for `T` are
related if for every pair of presheaves `P`, `Q`
and every relation `R : PshRel P Q`, the sections
`t₀ P` and `t₁ Q` are related by
`T.fullRelInterp R`.

This is the presheaf-category generalization of
`typeAbsRel`, implementing Wadler's relational
interpretation of `∀X. T(X)` in arbitrary presheaf
categories. -/
def pshTypeAbsRel (T : PshTypeExpr C)
    (t₀ t₁ : PshTypeAbs T) : Prop :=
  ∀ (P Q : Cᵒᵖ ⥤ Type (max u v))
    (R : PshRel P Q),
    pshRelSectionsRelated
      (T.fullRelInterp R) (t₀ P) (t₁ Q)

/-- The relational interpretation of a leaf
`app G var` reduces to `pshBarrLiftSkel G` applied
to the graph relation of `α`. -/
@[simp]
theorem PshTypeExpr.leaf_relInterp
    (G : (Cᵒᵖ ⥤ Type (max u v)) ⥤
         (Cᵒᵖ ⥤ Type (max u v)))
    {P Q : Cᵒᵖ ⥤ Type (max u v)}
    (α : P ⟶ Q) :
    (PshTypeExpr.leaf G).relInterp α =
      pshBarrLiftSkel G (pshRelGraph α) :=
  rfl

/-- Embeds a universe-0 type expression into the
presheaf type expression `PshTypeExpr (Type 0)`.
The `.app F T` case lifts `F : Type ⥤ Type` to an
endofunctor on `(Type 0)ᵒᵖ ⥤ Type 1` presheaves
via the Yoneda extension `yonedaExt F`. -/
def TypeExpr.toPshTypeExpr :
    TypeExpr → PshTypeExpr (Type 0)
  | .var => .var
  | .app F T => .app (yonedaExt F) T.toPshTypeExpr
  | .arrow T₁ T₂ =>
    .arrow T₁.toPshTypeExpr T₂.toPshTypeExpr

@[simp]
theorem TypeExpr.toPshTypeExpr_var :
    (TypeExpr.var).toPshTypeExpr =
      (PshTypeExpr.var : PshTypeExpr (Type 0)) :=
  rfl

@[simp]
theorem TypeExpr.toPshTypeExpr_app
    (F : Type ⥤ Type) (T : TypeExpr) :
    (TypeExpr.app F T).toPshTypeExpr =
      PshTypeExpr.app (yonedaExt F)
        T.toPshTypeExpr :=
  rfl

@[simp]
theorem TypeExpr.toPshTypeExpr_arrow
    (T₁ T₂ : TypeExpr) :
    (TypeExpr.arrow T₁ T₂).toPshTypeExpr =
      PshTypeExpr.arrow T₁.toPshTypeExpr
        T₂.toPshTypeExpr :=
  rfl

open MonoidalClosed

/-- The interpretation of a `TypeExpr` via
`toPshTypeExpr` at ULift-Yoneda representables
recovers the original interpretation via the
ULift-Yoneda embedding. -/
def TypeExpr.toPshTypeExpr_interp_iso
    (T : TypeExpr) (A B : Type) :
    T.toPshTypeExpr.interp
      (yonedaULift A) (yonedaULift B) ≅
      yonedaULift (T.interp A B) :=
  match T with
  | .var => Iso.refl _
  | .app F T' =>
    (yonedaExt F).mapIso
      (T'.toPshTypeExpr_interp_iso A B) ≪≫
    yonedaExtRepresentableULiftIso F
      (T'.interp A B)
  | .arrow T₁ T₂ =>
    { hom := pshIhomProfMap
        (T₁.toPshTypeExpr_interp_iso B A).inv
        (T₂.toPshTypeExpr_interp_iso A B).hom
      inv := pshIhomProfMap
        (T₁.toPshTypeExpr_interp_iso B A).hom
        (T₂.toPshTypeExpr_interp_iso A B).inv
      hom_inv_id := by
        rw [← pshIhomProfMap_comp]
        simp only [Iso.hom_inv_id]
        exact pshIhomProfMap_id
      inv_hom_id := by
        rw [← pshIhomProfMap_comp]
        simp only [Iso.inv_hom_id]
        exact pshIhomProfMap_id } ≪≫
    (pshIhomYonedaULiftIso
      (T₁.interp B A)
      (T₂.interp A B)).symm

end GebLean
