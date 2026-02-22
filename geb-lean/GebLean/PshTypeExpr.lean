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

/-- Lift a morphism `f : A → B` in `Type 0` to a
natural transformation
`yonedaULift A ⟶ yonedaULift B` in
`(Type 0)ᵒᵖ ⥤ Type 1`, given by post-composition
with `f`. -/
def yonedaULiftMap {A B : Type} (f : A → B) :
    yonedaULift A ⟶ yonedaULift B :=
  CategoryTheory.Functor.whiskerRight
    (yoneda.map f) uliftFunctor

/-- `yonedaULiftMap` at stage `T` sends
`⟨g⟩ : ULift (T → A)` to `⟨f ∘ g⟩`. -/
@[simp]
theorem yonedaULiftMap_app
    {A B : Type} (f : A → B) (T : (Type 0)ᵒᵖ)
    (x : (yonedaULift A).obj T) :
    (yonedaULiftMap f).app T x =
      ⟨f ∘ x.down⟩ := by
  simp only [yonedaULiftMap,
    CategoryTheory.Functor.whiskerRight_app]
  rfl

/-- Presheaf of related pairs for a binary
relation `R : A → B → Prop`, living over
`yonedaULift A × yonedaULift B`. At stage `T`,
elements are `ULift`-wrapped pairs of functions
`(f : T → A, g : T → B)` satisfying `R` pointwise,
with functorial action by precomposition. -/
def yonedaULiftRelPsh {A B : Type}
    (R : A → B → Prop) :
    (Type 0)ᵒᵖ ⥤ Type 1 where
  obj T := ULift
    { p : (T.unop → A) × (T.unop → B) //
      ∀ t, R (p.1 t) (p.2 t) }
  map f x := ⟨⟨(x.down.val.1 ∘ f.unop,
    x.down.val.2 ∘ f.unop),
    fun t => x.down.property (f.unop t)⟩⟩
  map_id _ := by
    ext ⟨⟨⟨_, _⟩, _⟩⟩ <;> simp [Function.comp]
  map_comp _ _ := by
    ext ⟨⟨⟨_, _⟩, _⟩⟩ <;> simp [Function.comp]

/-- The projection from the relation presheaf
`yonedaULiftRelPsh R` into the product presheaf
`yonedaULift A × yonedaULift B`, extracting the
two components. -/
def yonedaULiftRelProj {A B : Type}
    (R : A → B → Prop) :
    yonedaULiftRelPsh R ⟶
      pshProdPresheaf (yonedaULift A)
        (yonedaULift B) :=
  pshProdLift
    { app := fun T x => ⟨x.down.val.1⟩
      naturality := fun _ _ _ => by
        ext ⟨⟨⟨_, _⟩, _⟩⟩; rfl }
    { app := fun T x => ⟨x.down.val.2⟩
      naturality := fun _ _ _ => by
        ext ⟨⟨⟨_, _⟩, _⟩⟩; rfl }

/-- A binary relation `R : A → B → Prop` as an
over-object of the product of ULift-Yoneda
representables. -/
def yonedaULiftRelOver {A B : Type}
    (R : A → B → Prop) :
    PshProdOver (yonedaULift A) (yonedaULift B) :=
  Over.mk (yonedaULiftRelProj R)

/-- A binary relation `R : A → B → Prop` lifted to
a presheaf relation `PshRel` between ULift-Yoneda
representables. -/
def yonedaULiftRel {A B : Type}
    (R : A → B → Prop) :
    PshRel (yonedaULift A) (yonedaULift B) :=
  toSkeleton _ (yonedaULiftRelOver R)

/-- Convert an element `a : X` into a section of
`yonedaULift X`. At each stage `T`, the section
returns the constant function `fun _ => a`. -/
def yonedaULiftSection {X : Type} (a : X) :
    (yonedaULift X).sections :=
  ⟨fun _ => ⟨fun _ => a⟩,
   fun _ => rfl⟩

/-- Convert a section of `P` to a section of `Q`
along a natural transformation `P ⟶ Q`. -/
def sectionMap
    {P Q : (Type 0)ᵒᵖ ⥤ Type 1}
    (α : P ⟶ Q) (s : P.sections) :
    Q.sections :=
  ⟨fun c => α.app c (s.val c),
   fun {c c'} f => by
    change Q.map f (α.app c (s.val c)) =
      α.app c' (s.val c')
    have nat := congr_fun (α.naturality f)
      (s.val c)
    simp only [types_comp_apply] at nat
    rw [← nat, s.property f]⟩

/-- An element `a : T.interp X X` gives rise to a
section of `T.toPshTypeExpr.interp (yonedaULift X)
(yonedaULift X)` via the inverse of the bridge
isomorphism `toPshTypeExpr_interp_iso`. -/
def TypeExpr.toInterpSection
    (T : TypeExpr) {X : Type} (a : T.interp X X) :
    (T.toPshTypeExpr.interp
      (yonedaULift X) (yonedaULift X)).sections :=
  sectionMap
    (T.toPshTypeExpr_interp_iso X X).inv
    (yonedaULiftSection a)

/-- Reduction lemma: `pshRelSectionsRelated` at a
concrete `toSkeleton` reduces to `sectionsRelated`
of the underlying over-object. -/
@[simp]
theorem sectionMap_id
    {P : (Type 0)ᵒᵖ ⥤ Type 1}
    (s : P.sections) :
    sectionMap (𝟙 P) s = s := by
  ext c
  simp [sectionMap]

@[simp]
theorem sectionMap_comp
    {P Q R : (Type 0)ᵒᵖ ⥤ Type 1}
    (α : P ⟶ Q) (β : Q ⟶ R) (s : P.sections) :
    sectionMap (α ≫ β) s =
      sectionMap β (sectionMap α s) := by
  ext c
  simp [sectionMap]

@[simp]
theorem pshRelSectionsRelated_toSkeleton
    {F G : (Type 0)ᵒᵖ ⥤ Type 1}
    (R : PshProdOver F G)
    (s₀ : F.sections) (s₁ : G.sections) :
    pshRelSectionsRelated (toSkeleton _ R) s₀ s₁ ↔
      R.sectionsRelated s₀ s₁ := by
  constructor
  · exact id
  · exact id

/-- A binary relation `R` holds at `(a₀, a₁)` iff
the corresponding sections of the ULift-Yoneda
representables are related by
`yonedaULiftRelOver R`. -/
theorem yonedaULiftRelOver_sectionsRelated_iff
    {A B : Type} (R : A → B → Prop)
    (a₀ : A) (a₁ : B) :
    (yonedaULiftRelOver R).sectionsRelated
      (yonedaULiftSection a₀)
      (yonedaULiftSection a₁) ↔
    R a₀ a₁ := by
  constructor
  · rintro ⟨r, hr⟩
    set rPU := (r.val (Opposite.op PUnit)).down
    have rel := rPU.property PUnit.unit
    have h₁ := (hr (Opposite.op PUnit)).1
    have h₂ := (hr (Opposite.op PUnit)).2
    simp only [yonedaULiftRelOver, Over.mk_hom,
      yonedaULiftRelProj, pshProdLift,
      yonedaULiftSection] at h₁ h₂
    have eq₁ : rPU.val.1 = fun _ => a₀ :=
      congr_arg ULift.down h₁
    have eq₂ : rPU.val.2 = fun _ => a₁ :=
      congr_arg ULift.down h₂
    rw [congr_fun eq₁ PUnit.unit,
      congr_fun eq₂ PUnit.unit] at rel
    exact rel
  · intro h
    exact ⟨⟨fun c => ⟨⟨(fun _ => a₀, fun _ => a₁),
      fun _ => h⟩⟩, fun _ => rfl⟩,
      fun c => ⟨rfl, rfl⟩⟩

/-- In the `var` case, `toInterpSection` reduces to
`yonedaULiftSection`. -/
@[simp]
theorem TypeExpr.toInterpSection_var
    {X : Type} (a : X) :
    TypeExpr.var.toInterpSection a =
      yonedaULiftSection a := by
  simp only [toInterpSection,
    toPshTypeExpr_interp_iso]
  exact sectionMap_id _

/-- Bridge for the `var` case: the Type-level
relational interpretation at `var` agrees with the
presheaf-level relational interpretation at `var`
through the ULift-Yoneda embedding. -/
theorem TypeExpr.fullRelInterp_bridge_var
    {A B : Type} (R : A → B → Prop)
    (a₀ : A) (a₁ : B) :
    TypeExpr.var.fullRelInterp R a₀ a₁ ↔
      pshRelSectionsRelated
        (TypeExpr.var.toPshTypeExpr.fullRelInterp
          (yonedaULiftRel R))
        (TypeExpr.var.toInterpSection a₀)
        (TypeExpr.var.toInterpSection a₁) := by
  simp only [TypeExpr.fullRelInterp,
    TypeExpr.toPshTypeExpr_var,
    PshTypeExpr.fullRelInterp,
    toInterpSection_var]
  exact (yonedaULiftRelOver_sectionsRelated_iff
    R a₀ a₁).symm

/-- The presheaf `yonedaULiftRelPsh R` is
isomorphic to `yonedaULift { p // R p.1 p.2 }`
via currying/uncurrying the product structure.
At each stage `T`, this sends
`⟨⟨(f, g), proof⟩⟩` to `⟨fun t => ⟨(f t, g t),
proof t⟩⟩` and conversely. -/
def yonedaULiftRelPshIso
    {A B : Type} (R : A → B → Prop) :
    yonedaULiftRelPsh R ≅
      yonedaULift { p : A × B // R p.1 p.2 } where
  hom := {
    app := fun T x =>
      ⟨fun t => ⟨(x.down.val.1 t,
        x.down.val.2 t),
        x.down.property t⟩⟩
    naturality := fun _ _ _ => by
      ext ⟨⟨⟨_, _⟩, _⟩⟩; rfl }
  inv := {
    app := fun T x =>
      ⟨⟨(fun t => (x.down t).val.1,
        fun t => (x.down t).val.2),
        fun t => (x.down t).property⟩⟩
    naturality := fun _ _ _ => by
      ext ⟨_⟩; rfl }
  hom_inv_id := by
    ext T ⟨⟨⟨_, _⟩, _⟩⟩; rfl
  inv_hom_id := by
    ext T ⟨_⟩
    simp only [NatTrans.comp_app, types_comp_apply,
      NatTrans.id_app, types_id_apply]

/-- The Barr lift of `yonedaULiftRelOver R` via
`yonedaExt F` faithfully reflects `functorRelLift`
at constant sections. -/
theorem functorRelLift_yonedaULift_bridge
    (F : Type ⥤ Type) {A B : Type}
    (R : A → B → Prop)
    (a₀ : F.obj A) (a₁ : F.obj B) :
    functorRelLift F R a₀ a₁ ↔
      (pshBarrLift (yonedaExt F)
        (yonedaULiftRelOver R)).sectionsRelated
        (sectionMap
          (yonedaExtRepresentableULiftIso F A).inv
          (yonedaULiftSection a₀))
        (sectionMap
          (yonedaExtRepresentableULiftIso F B).inv
          (yonedaULiftSection a₁)) := by
  constructor
  · rintro ⟨w, hw₁, hw₂⟩
    refine ⟨⟨fun c =>
      Quot.mk _ ⟨{ p : A × B // R p.1 p.2 },
        ⟨⟨(fun s => s.val.1,
          fun s => s.val.2),
          fun s => s.property⟩⟩,
        fun _ => w⟩,
      fun {c c'} f => rfl⟩, fun c => ⟨?_, ?_⟩⟩
    · exact (Quot.sound
        ⟨fun s => s.val.1, rfl,
          funext (fun _ => hw₁)⟩).symm
    · exact (Quot.sound
        ⟨fun s => s.val.2, rfl,
          funext (fun _ => hw₂)⟩).symm
  · rintro ⟨r, hr⟩
    have spec₁ := (hr (Opposite.op PUnit)).1
    have spec₂ := (hr (Opposite.op PUnit)).2
    revert spec₁ spec₂
    refine Quot.inductionOn
      (r.val (Opposite.op PUnit))
      (fun ⟨S, p, h⟩ spec₁ spec₂ => ?_)
    set h₀ := h PUnit.unit with h₀_def
    set q := p.down with q_def
    set g : S → { p : A × B // R p.1 p.2 } :=
      fun s => ⟨(q.val.1 s, q.val.2 s),
        q.property s⟩ with g_def
    refine ⟨F.map g h₀, ?_, ?_⟩
    · change (F.map g ≫ F.map
        (fun s : { p : A × B // R p.1 p.2 } =>
          s.val.1)) h₀ = a₀
      rw [← CategoryTheory.Functor.map_comp]
      change F.map q.val.1 h₀ = a₀
      have comm₁ := spec₁
      dsimp [pshBarrLift, pshProdLift,
        sectionMap, yonedaULiftSection,
        yonedaExtRepresentableULiftIso] at comm₁
      have comm₁' := congr_arg
        (fun x =>
          ((yonedaExtCounitULift F A).app
            (Opposite.op PUnit) x).down
            PUnit.unit) comm₁
      simp only [yonedaExtCounitULift,
        yonedaExtUnitULift,
        CategoryTheory.Functor.map_id,
        Category.comp_id] at comm₁'
      exact comm₁'
    · change (F.map g ≫ F.map
        (fun s : { p : A × B // R p.1 p.2 } =>
          s.val.2)) h₀ = a₁
      rw [← CategoryTheory.Functor.map_comp]
      change F.map q.val.2 h₀ = a₁
      have comm₂ := spec₂
      dsimp [pshBarrLift, pshProdLift,
        sectionMap, yonedaULiftSection,
        yonedaExtRepresentableULiftIso] at comm₂
      have comm₂' := congr_arg
        (fun x =>
          ((yonedaExtCounitULift F B).app
            (Opposite.op PUnit) x).down
            PUnit.unit) comm₂
      simp only [yonedaExtCounitULift,
        yonedaExtUnitULift,
        CategoryTheory.Functor.map_id,
        Category.comp_id] at comm₂'
      exact comm₂'

/-- Canonical representative of the full relational
interpretation at `yonedaULiftRel R`: a concrete
`PshProdOver` (before the Skeleton quotient) for
each type expression. -/
def TypeExpr.fullRelInterpPshRep
    (T : TypeExpr) {A B : Type}
    (R : A → B → Prop) :
    PshProdOver
      (T.toPshTypeExpr.interp
        (yonedaULift A) (yonedaULift A))
      (T.toPshTypeExpr.interp
        (yonedaULift B) (yonedaULift B)) :=
  match T with
  | .var => yonedaULiftRelOver R
  | .app F T' =>
    pshBarrLift (yonedaExt F)
      (T'.fullRelInterpPshRep R)
  | .arrow T₁ T₂ =>
    pshArrowRel
      (T₁.fullRelInterpPshRep R)
      (T₂.fullRelInterpPshRep R)

/-- The presheaf-level full relational interpretation
at `yonedaULiftRel R` equals the Skeleton class of
the canonical representative `fullRelInterpPshRep`. -/
theorem TypeExpr.fullRelInterp_pshRep_eq
    (T : TypeExpr) {A B : Type}
    (R : A → B → Prop) :
    T.toPshTypeExpr.fullRelInterp
      (yonedaULiftRel R) =
      toSkeleton _ (T.fullRelInterpPshRep R) := by
  induction T with
  | var => rfl
  | app F T' ih =>
    change pshBarrLiftSkel (yonedaExt F)
      (T'.toPshTypeExpr.fullRelInterp
        (yonedaULiftRel R)) =
      toSkeleton _ (pshBarrLift (yonedaExt F)
        (T'.fullRelInterpPshRep R))
    simp only [ih, pshBarrLiftSkel, Skeleton.lift,
      toSkeleton]; rfl
  | arrow T₁ T₂ ih₁ ih₂ =>
    change pshArrowRelSkel
      (T₁.toPshTypeExpr.fullRelInterp
        (yonedaULiftRel R))
      (T₂.toPshTypeExpr.fullRelInterp
        (yonedaULiftRel R)) =
      toSkeleton _ (pshArrowRel
        (T₁.fullRelInterpPshRep R)
        (T₂.fullRelInterpPshRep R))
    simp only [ih₁, ih₂, pshArrowRelSkel,
      Skeleton.lift₂, toSkeleton]; rfl

/-- Two stage-level elements of the presheaf
interpretation are related at stage `d` if there
exists a witness in the relation presheaf at that
stage. -/
def TypeExpr.stageRelated
    (T : TypeExpr) {A B : Type}
    (R : A → B → Prop)
    (d : (Type 0)ᵒᵖ)
    (x : (T.toPshTypeExpr.interp
      (yonedaULift A) (yonedaULift A)).obj d)
    (y : (T.toPshTypeExpr.interp
      (yonedaULift B) (yonedaULift B)).obj d) :
    Prop :=
  ∃ w : (T.fullRelInterpPshRep R).left.obj d,
    ((T.fullRelInterpPshRep R).hom.app d w).1 =
      x ∧
    ((T.fullRelInterpPshRep R).hom.app d w).2 =
      y

/-- Combined bridge theorem relating the Type-level
full relational interpretation to the presheaf-level
interpretation through the ULift-Yoneda embedding.

Part 1 (stage-level): pointwise Type-level
relatedness at functions `f₀, f₁ : d.unop → ...`
is equivalent to stage-level relatedness at `d`.

Part 2 (section-level): Type-level relatedness of
elements `a₀, a₁` is equivalent to section-level
relatedness of their presheaf representatives.

These results are proved simultaneously because
the arrow case of the section-level bridge requires
the stage-level bridge for its subterms. -/
theorem TypeExpr.relInterp_bridges
    (T : TypeExpr) {A B : Type}
    (R : A → B → Prop)
    (choice : ∀ {α : Type}, Nonempty α → α) :
    (∀ (d : (Type 0)ᵒᵖ)
      (f₀ : d.unop → T.interp A A)
      (f₁ : d.unop → T.interp B B),
      (∀ t, T.fullRelInterp R (f₀ t) (f₁ t)) ↔
        T.stageRelated R d
          ((T.toPshTypeExpr_interp_iso A A
            ).inv.app d ⟨f₀⟩)
          ((T.toPshTypeExpr_interp_iso B B
            ).inv.app d ⟨f₁⟩))
    ∧
    (∀ (a₀ : T.interp A A) (a₁ : T.interp B B),
      T.fullRelInterp R a₀ a₁ ↔
        (T.fullRelInterpPshRep R
          ).sectionsRelated
          (T.toInterpSection a₀)
          (T.toInterpSection a₁)) := by
  induction T with
  | var =>
    exact ⟨fun d f₀ f₁ => by
      constructor
      · intro h
        exact ⟨⟨⟨(f₀, f₁), h⟩⟩, rfl, rfl⟩
      · rintro ⟨w, h₁, h₂⟩ t
        convert w.down.property t using 1
        · exact congr_fun
            (congr_arg ULift.down h₁.symm) t
        · exact congr_fun
            (congr_arg ULift.down h₂.symm) t,
    fun a₀ a₁ => by
      simp only [TypeExpr.fullRelInterp,
        TypeExpr.fullRelInterpPshRep,
        TypeExpr.toInterpSection,
        TypeExpr.toPshTypeExpr_interp_iso]
      dsimp only [PshTypeExpr.interp,
        TypeExpr.toPshTypeExpr, Iso.refl,
        sectionMap]
      exact (yonedaULiftRelOver_sectionsRelated_iff
        R a₀ a₁).symm⟩
  | app F T' ih =>
    exact ⟨fun d f₀ f₁ => by
      constructor
      · intro H
        set S := { q : T'.interp A A ×
          T'.interp B B //
          T'.fullRelInterp R q.1 q.2 }
        have hne : ∀ t : d.unop, Nonempty
            { wt : F.obj S //
              F.map (fun s => s.val.1)
                wt = f₀ t ∧
              F.map (fun s => s.val.2)
                wt = f₁ t } :=
          fun t => by
            obtain ⟨wt, hwt₁, hwt₂⟩ := H t
            exact ⟨⟨wt, hwt₁, hwt₂⟩⟩
        obtain ⟨p₀, hp₀_1, hp₀_2⟩ :=
          (ih.1 (Opposite.op S)
            (fun s => s.val.1)
            (fun s => s.val.2)).mp
            (fun s => s.property)
        refine ⟨Quot.mk _
          ⟨S, p₀, fun t =>
            (choice (hne t)).val⟩,
          ?_, ?_⟩
        · -- fst projection via Quot.sound
          set P₁ := T'.toPshTypeExpr.interp
            (yonedaULift A) (yonedaULift A)
          set g : S → T'.interp A A :=
            fun s => s.val.1
          change Quot.mk _
            (yonedaExtSigmaMapNat F
              ((T'.fullRelInterpPshRep R
                ).hom ≫
                pshProdFst _ _) d
              ⟨S, p₀, fun t =>
                (choice (hne t)).val⟩) =
            Quot.mk _
              (yonedaExtSigmaMapNat F
                (T'.toPshTypeExpr_interp_iso
                  A A).inv d
                ⟨T'.interp A A,
                  ⟨𝟙 _⟩, f₀⟩)
          dsimp only [yonedaExtSigmaMapNat]
          have psh_cond :
              P₁.map (Quiver.Hom.op g)
              ((T'.toPshTypeExpr_interp_iso
                A A).inv.app
                (Opposite.op (T'.interp A A))
                ⟨𝟙 _⟩) =
              ((T'.fullRelInterpPshRep R
                ).hom.app
                (Opposite.op S) p₀).1 := by
            have nat := congr_fun
              ((T'.toPshTypeExpr_interp_iso
                A A).inv.naturality
                (Quiver.Hom.op g)) ⟨𝟙 _⟩
            simp only [types_comp_apply]
              at nat
            simp only [Opposite.unop_op]
            rw [← nat, hp₀_1]
            congr 1
          exact (Quot.sound
            ⟨g, psh_cond,
              funext fun t =>
                (choice (hne t)
                  ).property.1⟩).symm
        · -- snd projection via Quot.sound
          set P₂ := T'.toPshTypeExpr.interp
            (yonedaULift B) (yonedaULift B)
          set g₂ : S → T'.interp B B :=
            fun s => s.val.2
          change Quot.mk _
            (yonedaExtSigmaMapNat F
              ((T'.fullRelInterpPshRep R
                ).hom ≫
                pshProdSnd _ _) d
              ⟨S, p₀, fun t =>
                (choice (hne t)).val⟩) =
            Quot.mk _
              (yonedaExtSigmaMapNat F
                (T'.toPshTypeExpr_interp_iso
                  B B).inv d
                ⟨T'.interp B B,
                  ⟨𝟙 _⟩, f₁⟩)
          dsimp only [yonedaExtSigmaMapNat]
          have psh_cond₂ :
              P₂.map (Quiver.Hom.op g₂)
              ((T'.toPshTypeExpr_interp_iso
                B B).inv.app
                (Opposite.op (T'.interp B B))
                ⟨𝟙 _⟩) =
              ((T'.fullRelInterpPshRep R
                ).hom.app
                (Opposite.op S) p₀).2 := by
            have nat := congr_fun
              ((T'.toPshTypeExpr_interp_iso
                B B).inv.naturality
                (Quiver.Hom.op g₂)) ⟨𝟙 _⟩
            simp only [types_comp_apply]
              at nat
            simp only [Opposite.unop_op]
            rw [← nat, hp₀_2]
            congr 1
          exact (Quot.sound
            ⟨g₂, psh_cond₂,
              funext fun t =>
                (choice (hne t)
                  ).property.2⟩).symm
      · intro ⟨w, hw₁, hw₂⟩
        revert hw₁ hw₂
        refine Quot.inductionOn w
          (fun ⟨S₀, p₀, t₀⟩
            hw₁ hw₂ => ?_)
        set q₁ := ((T'.fullRelInterpPshRep R
          ).hom.app
          (Opposite.op S₀) p₀).1
        set q₂ := ((T'.fullRelInterpPshRep R
          ).hom.app
          (Opposite.op S₀) p₀).2
        set f₀' :=
          ((T'.toPshTypeExpr_interp_iso
            A A).hom.app
            (Opposite.op S₀) q₁).down
        set f₁' :=
          ((T'.toPshTypeExpr_interp_iso
            B B).hom.app
            (Opposite.op S₀) q₂).down
        have round₁ :
            (T'.toPshTypeExpr_interp_iso
              A A).inv.app
              (Opposite.op S₀) ⟨f₀'⟩ =
              q₁ := by
          have := congr_fun
            ((T'.toPshTypeExpr_interp_iso
              A A).hom_inv_id_app
              (Opposite.op S₀)) q₁
          simp only [types_comp_apply,
            types_id_apply] at this
          exact this
        have round₂ :
            (T'.toPshTypeExpr_interp_iso
              B B).inv.app
              (Opposite.op S₀) ⟨f₁'⟩ =
              q₂ := by
          have := congr_fun
            ((T'.toPshTypeExpr_interp_iso
              B B).hom_inv_id_app
              (Opposite.op S₀)) q₂
          simp only [types_comp_apply,
            types_id_apply] at this
          exact this
        have hrel : ∀ s,
            T'.fullRelInterp R
              (f₀' s) (f₁' s) :=
          (ih.1 (Opposite.op S₀)
            f₀' f₁').mpr
            ⟨p₀, round₁.symm,
              round₂.symm⟩
        set gs : S₀ →
            { p : T'.interp A A ×
              T'.interp B B //
              T'.fullRelInterp R
                p.1 p.2 } :=
          fun s =>
            ⟨(f₀' s, f₁' s), hrel s⟩
        intro t
        refine ⟨F.map gs (t₀ t), ?_, ?_⟩
        · change (F.map gs ≫ F.map
            (fun s => s.val.1))
              (t₀ t) = f₀ t
          rw [←
            CategoryTheory.Functor.map_comp]
          change F.map f₀' (t₀ t) = f₀ t
          have comm₁ := hw₁
          dsimp [pshBarrLift, pshProdLift,
            TypeExpr.fullRelInterpPshRep,
            yonedaExtRepresentableULiftIso]
            at comm₁
          set iso :=
            (TypeExpr.app F T'
              ).toPshTypeExpr_interp_iso
              A A
          have comm₁' := congr_arg
            (fun x =>
              (iso.hom.app d x).down t)
            comm₁
          simp only [FunctorToTypes.inv_hom_id_app_apply]
            at comm₁'
          dsimp [iso,
            TypeExpr.toPshTypeExpr_interp_iso,
            Iso.trans,
            CategoryTheory.Functor.mapIso,
            yonedaExtRepresentableULiftIso,
            yonedaExt, yonedaExtMap,
            yonedaExtSigmaMapNat,
            yonedaExtCounitULift,
            Quot.map] at comm₁'
          exact comm₁'
        · change (F.map gs ≫ F.map
            (fun s => s.val.2))
              (t₀ t) = f₁ t
          rw [←
            CategoryTheory.Functor.map_comp]
          change F.map f₁' (t₀ t) = f₁ t
          have comm₂ := hw₂
          dsimp [pshBarrLift, pshProdLift,
            TypeExpr.fullRelInterpPshRep,
            yonedaExtRepresentableULiftIso]
            at comm₂
          set iso₂ :=
            (TypeExpr.app F T'
              ).toPshTypeExpr_interp_iso
              B B
          have comm₂' := congr_arg
            (fun x =>
              (iso₂.hom.app d x).down t)
            comm₂
          simp only [FunctorToTypes.inv_hom_id_app_apply]
            at comm₂'
          dsimp [iso₂,
            TypeExpr.toPshTypeExpr_interp_iso,
            Iso.trans,
            CategoryTheory.Functor.mapIso,
            yonedaExtRepresentableULiftIso,
            yonedaExt, yonedaExtMap,
            yonedaExtSigmaMapNat,
            yonedaExtCounitULift,
            Quot.map] at comm₂'
          exact comm₂',
    fun a₀ a₁ => by
      constructor
      · intro h
        set S := { q : T'.interp A A ×
          T'.interp B B //
          T'.fullRelInterp R q.1 q.2 }
        obtain ⟨w, hw₁, hw₂⟩ := h
        obtain ⟨p₀, hp₀_1, hp₀_2⟩ :=
          (ih.1 (Opposite.op S)
            (fun s => s.val.1)
            (fun s => s.val.2)).mp
            (fun s => s.property)
        refine ⟨⟨fun c => Quot.mk _
          ⟨S, p₀, fun _ => w⟩,
          fun {_c _c'} _f => ?_⟩,
          fun c => ⟨?_, ?_⟩⟩
        · rfl
        · -- fst projection via Quot.sound
          set P₁ := T'.toPshTypeExpr.interp
            (yonedaULift A) (yonedaULift A)
          set g : S → T'.interp A A :=
            fun s => s.val.1
          change Quot.mk _ (yonedaExtSigmaMapNat
            F ((T'.fullRelInterpPshRep R).hom ≫
              pshProdFst _ _) c
            ⟨S, p₀, fun _ => w⟩) =
            Quot.mk _ (yonedaExtSigmaMapNat
              F (T'.toPshTypeExpr_interp_iso A A
                ).inv c
              ⟨T'.interp A A, ⟨𝟙 _⟩,
                fun _ => a₀⟩)
          dsimp only [yonedaExtSigmaMapNat]
          have psh_cond : P₁.map (Quiver.Hom.op g)
              ((T'.toPshTypeExpr_interp_iso A A
                ).inv.app
                (Opposite.op (T'.interp A A))
                ⟨𝟙 _⟩) =
              ((T'.fullRelInterpPshRep R
                ).hom.app (Opposite.op S) p₀
                ).1 := by
            have nat := congr_fun
              ((T'.toPshTypeExpr_interp_iso A A
                ).inv.naturality
                  (Quiver.Hom.op g)) ⟨𝟙 _⟩
            simp only [types_comp_apply] at nat
            simp only [Opposite.unop_op]
            rw [← nat, hp₀_1]
            congr 1
          exact (Quot.sound
            ⟨g, psh_cond,
              funext fun _ => hw₁⟩).symm
        · -- snd projection via Quot.sound
          set P₂ := T'.toPshTypeExpr.interp
            (yonedaULift B) (yonedaULift B)
          set g₂ : S → T'.interp B B :=
            fun s => s.val.2
          change Quot.mk _ (yonedaExtSigmaMapNat
            F ((T'.fullRelInterpPshRep R).hom ≫
              pshProdSnd _ _) c
            ⟨S, p₀, fun _ => w⟩) =
            Quot.mk _ (yonedaExtSigmaMapNat
              F (T'.toPshTypeExpr_interp_iso B B
                ).inv c
              ⟨T'.interp B B, ⟨𝟙 _⟩,
                fun _ => a₁⟩)
          dsimp only [yonedaExtSigmaMapNat]
          have psh_cond₂ :
              P₂.map (Quiver.Hom.op g₂)
              ((T'.toPshTypeExpr_interp_iso B B
                ).inv.app
                (Opposite.op (T'.interp B B))
                ⟨𝟙 _⟩) =
              ((T'.fullRelInterpPshRep R
                ).hom.app (Opposite.op S) p₀
                ).2 := by
            have nat := congr_fun
              ((T'.toPshTypeExpr_interp_iso B B
                ).inv.naturality
                  (Quiver.Hom.op g₂)) ⟨𝟙 _⟩
            simp only [types_comp_apply] at nat
            simp only [Opposite.unop_op]
            rw [← nat, hp₀_2]
            congr 1
          exact (Quot.sound
            ⟨g₂, psh_cond₂,
              funext fun _ => hw₂⟩).symm
      · intro ⟨r, hr⟩
        have spec₁ := (hr (Opposite.op PUnit)).1
        have spec₂ := (hr (Opposite.op PUnit)).2
        revert spec₁ spec₂
        refine Quot.inductionOn
          (r.val (Opposite.op PUnit))
          (fun ⟨S₀, p₀, t₀⟩ spec₁ spec₂ => ?_)
        set h₀ := t₀ PUnit.unit
        set q₁ := ((T'.fullRelInterpPshRep R
          ).hom.app (Opposite.op S₀) p₀).1
        set q₂ := ((T'.fullRelInterpPshRep R
          ).hom.app (Opposite.op S₀) p₀).2
        set f₀' := ((T'.toPshTypeExpr_interp_iso
          A A).hom.app (Opposite.op S₀) q₁).down
        set f₁' := ((T'.toPshTypeExpr_interp_iso
          B B).hom.app (Opposite.op S₀) q₂).down
        have round₁ :
            (T'.toPshTypeExpr_interp_iso A A
            ).inv.app (Opposite.op S₀)
            ((T'.toPshTypeExpr_interp_iso A A
            ).hom.app (Opposite.op S₀) q₁) =
              q₁ := by
          have := congr_fun
            ((T'.toPshTypeExpr_interp_iso A A
              ).hom_inv_id_app
              (Opposite.op S₀)) q₁
          simp only [types_comp_apply,
            types_id_apply] at this
          exact this
        have round₂ :
            (T'.toPshTypeExpr_interp_iso B B
            ).inv.app (Opposite.op S₀)
            ((T'.toPshTypeExpr_interp_iso B B
            ).hom.app (Opposite.op S₀) q₂) =
              q₂ := by
          have := congr_fun
            ((T'.toPshTypeExpr_interp_iso B B
              ).hom_inv_id_app
              (Opposite.op S₀)) q₂
          simp only [types_comp_apply,
            types_id_apply] at this
          exact this
        have hrel :
            ∀ s, T'.fullRelInterp R (f₀' s)
              (f₁' s) :=
          (ih.1 (Opposite.op S₀) f₀' f₁').mpr
            ⟨p₀, round₁.symm, round₂.symm⟩
        set g : S₀ → { p : T'.interp A A ×
            T'.interp B B //
            T'.fullRelInterp R p.1 p.2 } :=
          fun s => ⟨(f₀' s, f₁' s), hrel s⟩
        refine ⟨F.map g h₀, ?_, ?_⟩
        · change (F.map g ≫ F.map
            (fun s : { p : T'.interp A A ×
              T'.interp B B //
              T'.fullRelInterp R p.1 p.2 } =>
              s.val.1)) h₀ = a₀
          rw [← CategoryTheory.Functor.map_comp]
          change F.map f₀' h₀ = a₀
          have comm₁ := spec₁
          dsimp [pshBarrLift, pshProdLift,
            TypeExpr.toInterpSection,
            sectionMap, yonedaULiftSection,
            TypeExpr.fullRelInterpPshRep,
            yonedaExtRepresentableULiftIso
            ] at comm₁
          set iso := (TypeExpr.app F T'
            ).toPshTypeExpr_interp_iso A A
          have comm₁' := congr_arg
            (fun x =>
              (iso.hom.app
                (Opposite.op PUnit) x).down
                PUnit.unit) comm₁
          simp only [
            FunctorToTypes.inv_hom_id_app_apply
            ] at comm₁'
          dsimp [iso,
            TypeExpr.toPshTypeExpr_interp_iso,
            Iso.trans,
            CategoryTheory.Functor.mapIso,
            yonedaExtRepresentableULiftIso,
            yonedaExt, yonedaExtMap,
            yonedaExtSigmaMapNat,
            yonedaExtCounitULift,
            Quot.map] at comm₁'
          exact comm₁'
        · change (F.map g ≫ F.map
            (fun s : { p : T'.interp A A ×
              T'.interp B B //
              T'.fullRelInterp R p.1 p.2 } =>
              s.val.2)) h₀ = a₁
          rw [← CategoryTheory.Functor.map_comp]
          change F.map f₁' h₀ = a₁
          have comm₂ := spec₂
          dsimp [pshBarrLift, pshProdLift,
            TypeExpr.toInterpSection,
            sectionMap, yonedaULiftSection,
            TypeExpr.fullRelInterpPshRep,
            yonedaExtRepresentableULiftIso
            ] at comm₂
          set iso₂ := (TypeExpr.app F T'
            ).toPshTypeExpr_interp_iso B B
          have comm₂' := congr_arg
            (fun x =>
              (iso₂.hom.app
                (Opposite.op PUnit) x).down
                PUnit.unit) comm₂
          simp only [
            FunctorToTypes.inv_hom_id_app_apply
            ] at comm₂'
          dsimp [iso₂,
            TypeExpr.toPshTypeExpr_interp_iso,
            Iso.trans,
            CategoryTheory.Functor.mapIso,
            yonedaExtRepresentableULiftIso,
            yonedaExt, yonedaExtMap,
            yonedaExtSigmaMapNat,
            yonedaExtCounitULift,
            Quot.map] at comm₂'
          exact comm₂'⟩
  | arrow T₁ T₂ ih₁ ih₂ =>
    exact ⟨fun d f₀ f₁ => by
      constructor
      · intro H
        refine ⟨⟨(_, _),
          fun e h w_R => ?_⟩, rfl, rfl⟩
        set p₁ := ((T₁.fullRelInterpPshRep R
          ).hom.app e w_R).1
        set p₂ := ((T₁.fullRelInterpPshRep R
          ).hom.app e w_R).2
        set a₁ := ((T₁.toPshTypeExpr_interp_iso
          A A).hom.app e p₁).down
        set a₂ := ((T₁.toPshTypeExpr_interp_iso
          B B).hom.app e p₂).down
        have h_T₁ :
            ∀ t', T₁.fullRelInterp R
              (a₁ t') (a₂ t') :=
          (ih₁.1 e a₁ a₂).mpr ⟨w_R,
            (congr_fun (Iso.hom_inv_id_app
              (T₁.toPshTypeExpr_interp_iso A A)
              e) p₁).symm,
            (congr_fun (Iso.hom_inv_id_app
              (T₁.toPshTypeExpr_interp_iso B B)
              e) p₂).symm⟩
        have h_T₂ : ∀ t',
            T₂.fullRelInterp R
              (f₀ (h.unop t') (a₁ t'))
              (f₁ (h.unop t') (a₂ t')) :=
          fun t' => H (h.unop t') _ _ (h_T₁ t')
        obtain ⟨s, hs₁, hs₂⟩ :=
          (ih₂.1 e _ _).mp h_T₂
        exact ⟨s, Prod.ext
          (hs₁.trans (by rfl))
          (hs₂.trans (by rfl))⟩
      · intro ⟨w, hw₁, hw₂⟩ t a₀ a₁ hR
        set e₀ := Opposite.op PUnit
        set const_a₀ :
            e₀.unop → T₁.interp A A :=
          fun _ => a₀
        set const_a₁ :
            e₀.unop → T₁.interp B B :=
          fun _ => a₁
        have h₁ : ∀ u, T₁.fullRelInterp R
            (const_a₀ u) (const_a₁ u) :=
          fun _ => hR
        obtain ⟨w_R, hw_R₁, hw_R₂⟩ :=
          (ih₁.1 e₀ const_a₀ const_a₁).mp h₁
        set h_t : d ⟶ e₀ :=
          Quiver.Hom.op (fun (_ : PUnit) => t)
        obtain ⟨s_T₂, hs_T₂⟩ :=
          w.property e₀ h_t w_R
        set x₁ := ((T₂.toPshTypeExpr_interp_iso
          A A).hom.app e₀
            (Prod.fst
              (((T₂.fullRelInterpPshRep R
                ).hom.app e₀ s_T₂)))).down
        set x₂ := ((T₂.toPshTypeExpr_interp_iso
          B B).hom.app e₀
            (Prod.snd
              (((T₂.fullRelInterpPshRep R
                ).hom.app e₀ s_T₂)))).down
        have h₂ : ∀ u, T₂.fullRelInterp R
            (x₁ u) (x₂ u) :=
          (ih₂.1 e₀ x₁ x₂).mpr ⟨s_T₂,
            (congr_fun (Iso.hom_inv_id_app
              (T₂.toPshTypeExpr_interp_iso A A)
              e₀) _).symm,
            (congr_fun (Iso.hom_inv_id_app
              (T₂.toPshTypeExpr_interp_iso B B)
              e₀) _).symm⟩
        have wval₁_eq : w.val.1 =
            ((T₁.arrow T₂
              ).toPshTypeExpr_interp_iso A A
              ).inv.app d ⟨f₀⟩ := hw₁
        have wval₂_eq : w.val.2 =
            ((T₁.arrow T₂
              ).toPshTypeExpr_interp_iso B B
              ).inv.app d ⟨f₁⟩ := hw₂
        suffices heq₁ :
            x₁ PUnit.unit = f₀ t a₀ by
          suffices heq₂ :
              x₂ PUnit.unit = f₁ t a₁ by
            exact heq₁ ▸ heq₂ ▸ h₂ PUnit.unit
          simp only [x₂,
            congr_arg Prod.snd hs_T₂,
            wval₂_eq, hw_R₂,
            TypeExpr.toPshTypeExpr_interp_iso,
            Iso.trans_inv, Iso.symm_inv,
            NatTrans.comp_app,
            types_comp_apply,
            pshIhomProfMap,
            FunctorToTypes.inv_hom_id_app_apply]
          rfl
        simp only [x₁,
          congr_arg Prod.fst hs_T₂,
          wval₁_eq, hw_R₁,
          TypeExpr.toPshTypeExpr_interp_iso,
          Iso.trans_inv, Iso.symm_inv,
          NatTrans.comp_app,
          types_comp_apply,
          pshIhomProfMap,
          FunctorToTypes.inv_hom_id_app_apply]
        rfl,
    fun a₀ a₁ => by
      set s₀ := (T₁.arrow T₂).toInterpSection a₀
      set s₁ := (T₁.arrow T₂).toInterpSection a₁
      constructor
      · intro H
        refine ⟨⟨fun c =>
          ⟨(s₀.val c, s₁.val c),
           fun d h w_R => ?_⟩,
          ?_⟩, fun c => ?_⟩
        · -- Predicate: construct T₂ witness
          set p₁ := ((T₁.fullRelInterpPshRep R
            ).hom.app d w_R).1
          set p₂ := ((T₁.fullRelInterpPshRep R
            ).hom.app d w_R).2
          set f₀_T₁ :=
            ((T₁.toPshTypeExpr_interp_iso A A
              ).hom.app d p₁).down
          set f₁_T₁ :=
            ((T₁.toPshTypeExpr_interp_iso B B
              ).hom.app d p₂).down
          have h_T₁ : ∀ t',
              T₁.fullRelInterp R
                (f₀_T₁ t') (f₁_T₁ t') :=
            (ih₁.1 d f₀_T₁ f₁_T₁).mpr
              ⟨w_R,
               (congr_fun (Iso.hom_inv_id_app
                 (T₁.toPshTypeExpr_interp_iso
                   A A) d) p₁).symm,
               (congr_fun (Iso.hom_inv_id_app
                 (T₁.toPshTypeExpr_interp_iso
                   B B) d) p₂).symm⟩
          set f₀_T₂ : d.unop → T₂.interp A A :=
            fun t' => a₀ (f₀_T₁ t')
          set f₁_T₂ : d.unop → T₂.interp B B :=
            fun t' => a₁ (f₁_T₁ t')
          have h_T₂ : ∀ t',
              T₂.fullRelInterp R
                (f₀_T₂ t') (f₁_T₂ t') :=
            fun t' => H _ _ (h_T₁ t')
          obtain ⟨s_T₂, hs_T₂_1, hs_T₂_2⟩ :=
            (ih₂.1 d f₀_T₂ f₁_T₂).mp h_T₂
          exact ⟨s_T₂, Prod.ext
            (hs_T₂_1.trans (by rfl))
            (hs_T₂_2.trans (by rfl))⟩
        · -- Section compatibility
          intro c c' f
          apply Subtype.ext
          exact Prod.ext
            (s₀.property f) (s₁.property f)
        · -- Projections
          exact ⟨rfl, rfl⟩
      · -- Backward: sectionsRelated → arrowRel
        intro ⟨r, hr⟩ x₀ x₁ hR
        set e₀ := Opposite.op PUnit
        -- T₁ section-level relatedness
        obtain ⟨r₁, hr₁⟩ :=
          (ih₁.2 x₀ x₁).mp hR
        -- Evaluate at op PUnit
        set w_R₁ := r₁.val e₀
        -- Apply arrow predicate at e₀
        have hr_e₀ := (hr e₀).1
        have hr_e₀_2 := (hr e₀).2
        set h_id : e₀ ⟶ e₀ := 𝟙 e₀
        obtain ⟨s_T₂, hs_T₂⟩ :=
          (r.val e₀).property e₀ h_id w_R₁
        -- Decode T₂ witness at op PUnit
        set q₁ := ((T₂.fullRelInterpPshRep R
          ).hom.app e₀ s_T₂).1
        set q₂ := ((T₂.fullRelInterpPshRep R
          ).hom.app e₀ s_T₂).2
        set g₀ := ((T₂.toPshTypeExpr_interp_iso
          A A).hom.app e₀ q₁).down
        set g₁ := ((T₂.toPshTypeExpr_interp_iso
          B B).hom.app e₀ q₂).down
        have h_T₂ : ∀ u,
            T₂.fullRelInterp R
              (g₀ u) (g₁ u) :=
          (ih₂.1 e₀ g₀ g₁).mpr ⟨s_T₂,
            (congr_fun (Iso.hom_inv_id_app
              (T₂.toPshTypeExpr_interp_iso A A)
              e₀) _).symm,
            (congr_fun (Iso.hom_inv_id_app
              (T₂.toPshTypeExpr_interp_iso B B)
              e₀) _).symm⟩
        -- Show g₀ PUnit.unit = a₀ x₀
        suffices heq₁ :
            g₀ PUnit.unit = a₀ x₀ by
          suffices heq₂ :
              g₁ PUnit.unit = a₁ x₁ by
            exact heq₁ ▸ heq₂ ▸
              h_T₂ PUnit.unit
          have hr_val₂ :
              (r.val e₀).val.2 =
                s₁.val e₀ :=
            hr_e₀_2
          have hr₁_val₂ :
              ((T₁.fullRelInterpPshRep R
                ).hom.app e₀ w_R₁).2 =
              (T₁.toInterpSection x₁
                ).val e₀ :=
            (hr₁ e₀).2
          simp only [g₁, q₂,
            congr_arg Prod.snd hs_T₂,
            hr_val₂, hr₁_val₂,
            TypeExpr.toInterpSection,
            sectionMap, s₁,
            TypeExpr.toPshTypeExpr_interp_iso,
            Iso.trans_inv, Iso.symm_inv,
            NatTrans.comp_app,
            types_comp_apply,
            pshIhomProfMap,
            FunctorToTypes.inv_hom_id_app_apply]
          dsimp only [pshIhomYonedaULiftIso,
            NatIso.ofComponents,
            pshIhomYonedaULiftFwd,
            yonedaULiftSection, h_id, e₀]
          simp only [types_comp_apply,
            CartesianMonoidalCategory.lift_apply]
          dsimp only [ihom.ev, ihom.adjunction,
            Closed.adj,
            Types.tensorProductAdjunction]
        have hr_val₁ :
            (r.val e₀).val.1 =
              s₀.val e₀ :=
          hr_e₀
        have hr₁_val₁ :
            ((T₁.fullRelInterpPshRep R
              ).hom.app e₀ w_R₁).1 =
            (T₁.toInterpSection x₀
              ).val e₀ :=
          (hr₁ e₀).1
        simp only [g₀, q₁,
          congr_arg Prod.fst hs_T₂,
          hr_val₁, hr₁_val₁,
          TypeExpr.toInterpSection,
          sectionMap, s₀,
          TypeExpr.toPshTypeExpr_interp_iso,
          Iso.trans_inv, Iso.symm_inv,
          NatTrans.comp_app,
          types_comp_apply,
          pshIhomProfMap,
          FunctorToTypes.inv_hom_id_app_apply]
        dsimp only [pshIhomYonedaULiftIso,
          NatIso.ofComponents,
          pshIhomYonedaULiftFwd,
          yonedaULiftSection, h_id, e₀]
        simp only [types_comp_apply,
          CartesianMonoidalCategory.lift_apply]
        dsimp only [ihom.ev, ihom.adjunction,
          Closed.adj,
          Types.tensorProductAdjunction]⟩

/-- Section-level bridge: Type-level relatedness
of elements is equivalent to section-level
relatedness of their presheaf representatives
through the ULift-Yoneda embedding. -/
theorem TypeExpr.fullRelInterp_bridge
    (T : TypeExpr) {A B : Type}
    (R : A → B → Prop)
    (choice : ∀ {α : Type}, Nonempty α → α)
    (a₀ : T.interp A A) (a₁ : T.interp B B) :
    T.fullRelInterp R a₀ a₁ ↔
      (T.fullRelInterpPshRep R
        ).sectionsRelated
        (T.toInterpSection a₀)
        (T.toInterpSection a₁) :=
  (T.relInterp_bridges R choice).2 a₀ a₁

/-- Stage-level bridge: pointwise Type-level
relatedness at functions `f₀, f₁ : d.unop → ...`
is equivalent to stage-level relatedness at `d`. -/
theorem TypeExpr.pointwise_bridge
    (T : TypeExpr) {A B : Type}
    (R : A → B → Prop)
    (choice : ∀ {α : Type}, Nonempty α → α)
    (d : (Type 0)ᵒᵖ)
    (f₀ : d.unop → T.interp A A)
    (f₁ : d.unop → T.interp B B) :
    (∀ t, T.fullRelInterp R (f₀ t) (f₁ t)) ↔
      T.stageRelated R d
        ((T.toPshTypeExpr_interp_iso A A
          ).inv.app d ⟨f₀⟩)
        ((T.toPshTypeExpr_interp_iso B B
          ).inv.app d ⟨f₁⟩) :=
  (T.relInterp_bridges R choice).1 d f₀ f₁

end GebLean
