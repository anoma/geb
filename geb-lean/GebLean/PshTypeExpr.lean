import GebLean.PshRelDouble
import GebLean.PshRelSpanDiagram
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
    pshBarrLiftRel G (T.relInterp α)
  | .arrow T₁ T₂, _, _, α =>
    pshArrowRel
      (T₁.relInterp α)
      (T₂.relInterp α)

/-- The full relational interpretation of a
presheaf type expression at an arbitrary relation
`R : PshRel P Q`. This generalizes `relInterp`,
which only accepts morphism graphs
(`pshRelGraph α`). Each `var` contributes `R`
itself, each `app G T` contributes
`pshBarrLiftRel G (T.fullRelInterp R)`, and each
`arrow` contributes `pshArrowRel`.

This is the presheaf-category generalization of
`TypeExpr.fullRelInterp`. -/
def PshTypeExpr.fullRelInterp :
    (T : PshTypeExpr C) →
    {P Q : Cᵒᵖ ⥤ Type (max u v)} →
    (R : PshRel P Q) →
    PshRel (T.interp P P) (T.interp Q Q)
  | .var, _, _, R => R
  | .app G T, _, _, R =>
    pshBarrLiftRel G (T.fullRelInterp R)
  | .arrow T₁ T₂, _, _, R =>
    pshArrowRel
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
`PshRel` if the pair of section values belongs
to the relation at every stage. -/
def pshRelSectionsRelated
    {F G : Cᵒᵖ ⥤ Type (max u v)}
    (R : PshRel F G)
    (s₀ : F.sections) (s₁ : G.sections) :
    Prop :=
  ∀ (c : Cᵒᵖ),
    (s₀.val c, s₁.val c) ∈ R.obj c

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
`app G var` reduces to `pshBarrLiftRel G` applied
to the graph relation of `α`. -/
@[simp]
theorem PshTypeExpr.leaf_relInterp
    (G : (Cᵒᵖ ⥤ Type (max u v)) ⥤
         (Cᵒᵖ ⥤ Type (max u v)))
    {P Q : Cᵒᵖ ⥤ Type (max u v)}
    (α : P ⟶ Q) :
    (PshTypeExpr.leaf G).relInterp α =
      pshBarrLiftRel G (pshRelGraph α) :=
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
  pshProdOverToRel (yonedaULiftRelOver R)

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

/-- If sections are related by a `PshProdOver`, they
are related by the corresponding `PshRel` obtained
via `pshProdOverToRel`. -/
theorem sectionsRelated_to_pshRelSectionsRelated
    {F G : (Type 0)ᵒᵖ ⥤ Type 1}
    (R : PshProdOver F G)
    (s₀ : F.sections) (s₁ : G.sections)
    (h : R.sectionsRelated s₀ s₁) :
    pshRelSectionsRelated
      (pshProdOverToRel R) s₀ s₁ := by
  obtain ⟨r, hr⟩ := h
  intro c
  exact ⟨r.val c, Prod.ext (hr c).1 (hr c).2⟩

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

/-- `pshRelSectionsRelated (yonedaULiftRel R)` at
constant sections is equivalent to `R`. -/
theorem yonedaULiftRel_sectionsRelated_iff
    {A B : Type} (R : A → B → Prop)
    (a₀ : A) (a₁ : B) :
    pshRelSectionsRelated (yonedaULiftRel R)
      (yonedaULiftSection a₀)
      (yonedaULiftSection a₁) ↔
    R a₀ a₁ := by
  simp only [pshRelSectionsRelated,
    yonedaULiftRel, pshProdOverToRel,
    Subfunctor.range, yonedaULiftRelOver,
    Over.mk_hom, yonedaULiftRelProj,
    pshProdLift, yonedaULiftSection,
    Set.mem_range]
  constructor
  · intro h
    obtain ⟨w, hw⟩ := h (Opposite.op PUnit)
    set wd := w.down
    have h₁ : wd.val.1 = fun _ => a₀ :=
      congr_arg ULift.down (congr_arg Prod.fst hw)
    have h₂ : wd.val.2 = fun _ => a₁ :=
      congr_arg ULift.down (congr_arg Prod.snd hw)
    have rel := wd.property PUnit.unit
    rw [congr_fun h₁ PUnit.unit,
      congr_fun h₂ PUnit.unit] at rel
    exact rel
  · intro h c
    exact ⟨⟨⟨(fun _ => a₀, fun _ => a₁),
      fun _ => h⟩⟩, rfl⟩

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
  exact (yonedaULiftRel_sectionsRelated_iff
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
`PshProdOver` (before the subfunctor projection) for
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
    pshArrowRelOver
      (T₁.fullRelInterpPshRep R)
      (T₂.fullRelInterpPshRep R)

/-- `fullRelInterp (yonedaULiftRel R)` equals
`pshProdOverToRel (fullRelInterpPshRep R)`. -/
theorem TypeExpr.fullRelInterp_pshRep_eq
    (T : TypeExpr) {A B : Type}
    (R : A → B → Prop) :
    T.toPshTypeExpr.fullRelInterp
      (yonedaULiftRel R) =
      pshProdOverToRel
        (T.fullRelInterpPshRep R) := by
  induction T with
  | var => rfl
  | app F T' ih =>
    simp only [TypeExpr.toPshTypeExpr,
      PshTypeExpr.fullRelInterp,
      TypeExpr.fullRelInterpPshRep, ih]
    exact le_antisymm
      (by
        simp only [pshBarrLiftRel,
          pshProdOverToRel]
        intro c x hx
        simp only [Subfunctor.range,
          Set.mem_range] at hx ⊢
        obtain ⟨w, hw⟩ := hx
        revert hw
        refine Quot.inductionOn w
          (fun ⟨E, p, h⟩ hw => ?_)
        obtain ⟨r, hr⟩ := p.property
        refine ⟨Quot.mk _ ⟨E, r, h⟩, ?_⟩
        rw [← hw]
        have heq1 :
          ((T'.fullRelInterpPshRep R
            ).hom.app
            (Opposite.op E) r).1 =
          p.val.1 := congr_arg Prod.fst hr
        have heq2 :
          ((T'.fullRelInterpPshRep R
            ).hom.app
            (Opposite.op E) r).2 =
          p.val.2 := congr_arg Prod.snd hr
        change (pshBarrLift (yonedaExt F)
            (T'.fullRelInterpPshRep R)
            ).hom.app c
            (Quot.mk _ ⟨E, r, h⟩) =
          (pshBarrLift (yonedaExt F)
            (Over.mk (Subfunctor.range
              (T'.fullRelInterpPshRep R
                ).hom).ι)
              ).hom.app c
            (Quot.mk _ ⟨E, p, h⟩)
        simp only [pshBarrLift, Over.mk_hom,
          pshProdLift]
        change ((yonedaExt F).map
            ((T'.fullRelInterpPshRep R
              ).hom ≫ pshProdFst _ _)
              |>.app c (Quot.mk _ ⟨E, r, h⟩),
          (yonedaExt F).map
            ((T'.fullRelInterpPshRep R
              ).hom ≫ pshProdSnd _ _)
              |>.app c (Quot.mk _ ⟨E, r, h⟩))
          =
          ((yonedaExt F).map
            ((Subfunctor.range
              (T'.fullRelInterpPshRep R
                ).hom).ι ≫ pshProdFst _ _)
              |>.app c (Quot.mk _ ⟨E, p, h⟩),
          (yonedaExt F).map
            ((Subfunctor.range
              (T'.fullRelInterpPshRep R
                ).hom).ι ≫ pshProdSnd _ _)
              |>.app c (Quot.mk _ ⟨E, p, h⟩))
        apply Prod.ext <;> {
          apply congr_arg (Quot.mk _)
          simp only [
            yonedaExtSigmaMapNat,
            NatTrans.comp_app,
            types_comp_apply]
          have h₁ := congr_arg Prod.fst hr
          have h₂ := congr_arg Prod.snd hr
          dsimp at h₁ h₂ ⊢
          congr 1
          first
          | exact congr_arg (·, h) h₁
          | exact congr_arg (·, h) h₂
        })
      (pshProdOverToRel_pshBarrLift_le
        (yonedaExt F)
        (T'.fullRelInterpPshRep R))
  | arrow T₁ T₂ ih₁ ih₂ =>
    simp only [TypeExpr.toPshTypeExpr,
      PshTypeExpr.fullRelInterp,
      TypeExpr.fullRelInterpPshRep, ih₁, ih₂]
    exact pshArrowRel_pshProdOverToRel
      (T₁.fullRelInterpPshRep R)
      (T₂.fullRelInterpPshRep R)

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

/-- Self-relatedness under `pshTypeAbsRel` is
equivalent to the `PshParametricFamily`
parametricity condition, since both quantify
over all `PshRel` with `fullRelInterp`. -/
theorem pshTypeAbsRel_self_implies_parametric
    {T : PshTypeExpr C}
    {t : PshTypeAbs T}
    (h : pshTypeAbsRel T t t) :
    ∀ (P Q : Cᵒᵖ ⥤ Type (max u v))
      (R : PshRel P Q),
    pshRelSectionsRelated
      (T.fullRelInterp R) (t P) (t Q) :=
  h

/-- A parametric family for a presheaf type
expression `T` is a family of sections
`app P : (T.interp P P).sections` indexed by
presheaves `P`, such that for every presheaf
relation `R : PshRel P Q`, the full relational
interpretation `T.fullRelInterp R` relates
`app P` to `app Q`.

This is Wadler's parametricity condition at
presheaf level, with arbitrary presheaf
relations (not restricted to morphism graphs).
This is the presheaf-category generalization of
`ParametricFamily`. -/
@[ext]
structure PshParametricFamily
    (T : PshTypeExpr C) where
  /-- The component at each presheaf -/
  app : (P : Cᵒᵖ ⥤ Type (max u v)) →
    (T.interp P P).sections
  /-- The parametricity condition -/
  parametric :
    ∀ (P Q : Cᵒᵖ ⥤ Type (max u v))
      (R : PshRel P Q),
    pshRelSectionsRelated
      (T.fullRelInterp R) (app P) (app Q)

/-- Specialization of
`PshParametricFamily.parametric` to the graph
of a morphism: `T.fullRelInterp` at
`pshRelGraph α` coincides with `T.relInterp α`.
-/
theorem PshParametricFamily.parametric_graphRel
    {T : PshTypeExpr C}
    (p : PshParametricFamily T)
    {P Q : Cᵒᵖ ⥤ Type (max u v)}
    (α : P ⟶ Q) :
    pshRelSectionsRelated
      (T.relInterp α) (p.app P) (p.app Q) :=
  T.fullRelInterp_graph α ▸
    p.parametric P Q (pshRelGraph α)

/-- A `PshParametricFamily` from a self-related
type abstraction under `pshTypeAbsRel`.
This is the presheaf-category generalization of
`ParametricFamily.ofTypeAbsRel`. -/
def PshParametricFamily.ofPshTypeAbsRel
    {T : PshTypeExpr C}
    (t : PshTypeAbs T)
    (h : pshTypeAbsRel T t t) :
    PshParametricFamily T where
  app := t
  parametric := h

/-- The two ways of lifting a function
`f : A → B` to a presheaf relation agree:
lifting the graph relation `graphRel f` via
`yonedaULiftRel` equals the graph of the
presheaf morphism `yonedaULiftMap f` via
`pshRelGraph`. -/
theorem yonedaULiftRel_graphRel
    {A B : Type} (f : A → B) :
    yonedaULiftRel (graphRel f) =
      pshRelGraph (yonedaULiftMap f) := by
  ext c ⟨p, q⟩
  simp only [yonedaULiftRel,
    pshProdOverToRel, Subfunctor.range,
    Set.mem_range, yonedaULiftRelOver,
    Over.mk_hom, yonedaULiftRelProj,
    pshProdLift, pshRelGraph,
    Set.mem_setOf_eq]
  constructor
  · rintro ⟨w, hw⟩
    have h₁ := congr_arg Prod.fst hw
    have h₂ := congr_arg Prod.snd hw
    dsimp at h₁ h₂
    rw [← h₁, ← h₂]
    simp only [yonedaULiftMap_app]
    exact congr_arg ULift.up
      (funext (w.down.property))
  · intro (h : (yonedaULiftMap f).app c p = q)
    exact ⟨⟨⟨(p.down, f ∘ p.down),
      fun _ => rfl⟩⟩,
      Prod.ext rfl (by
        simp only [yonedaULiftMap_app] at h
        exact h)⟩

/-- Bridge from Type-level parametricity to
presheaf-level relatedness at representable
presheaves: given a `ParametricFamily` for a
`TypeExpr`, the presheaf-level relational
interpretation at `yonedaULiftMap f` relates
the section representatives of the components
at `I₀` and `I₁`. -/
theorem ParametricFamily.toPshParametricAtRep
    (T : TypeExpr)
    (p : ParametricFamily T)
    (choice : ∀ {α : Type}, Nonempty α → α)
    {I₀ I₁ : Type} (f : I₀ → I₁) :
    pshRelSectionsRelated
      (T.toPshTypeExpr.relInterp
        (yonedaULiftMap f))
      (T.toInterpSection (p.app I₀))
      (T.toInterpSection (p.app I₁)) := by
  have h₁ : T.fullRelInterp (graphRel f)
      (p.app I₀) (p.app I₁) :=
    p.parametric I₀ I₁ (graphRel f)
  have h₂ := (T.fullRelInterp_bridge
    (graphRel f) choice
    (p.app I₀) (p.app I₁)).mp h₁
  rw [← T.toPshTypeExpr.fullRelInterp_graph,
    ← yonedaULiftRel_graphRel,
    T.fullRelInterp_pshRep_eq]
  exact sectionsRelated_to_pshRelSectionsRelated
    _ _ _ h₂

/-- Equivalence between `X` and
`(yonedaULift X).sections`. The forward direction
sends `a : X` to the constant section; the backward
direction evaluates at `op PUnit` and extracts the
underlying element. -/
def yonedaULiftSectionEquiv (X : Type) :
    X ≃ (yonedaULift X).sections where
  toFun := yonedaULiftSection
  invFun s :=
    (s.val (Opposite.op PUnit)).down PUnit.unit
  left_inv _ := rfl
  right_inv s := by
    ext c
    simp only [yonedaULiftSection, yonedaULift,
      Functor.comp_obj, yoneda_obj_obj,
      uliftFunctor_obj]
    ext t
    have h := congr_arg ULift.down
      (s.property
        (Quiver.Hom.op (fun _ : PUnit => t) :
          c ⟶ Opposite.op PUnit))
    simp only [yonedaULift, Functor.comp_map,
      yoneda_obj_map, uliftFunctor_map] at h
    exact (congr_fun h PUnit.unit).symm

/-- Equivalence between `T.interp I I` and
sections of `T.toPshTypeExpr.interp
(yonedaULift I) (yonedaULift I)`. The forward
direction is `toInterpSection`; the backward
direction maps sections through the bridge
isomorphism `toPshTypeExpr_interp_iso` and
then extracts via `yonedaULiftSectionEquiv`. -/
def TypeExpr.interpSectionEquiv
    (T : TypeExpr) (I : Type) :
    T.interp I I ≃
    (T.toPshTypeExpr.interp
      (yonedaULift I) (yonedaULift I)).sections :=
  (yonedaULiftSectionEquiv (T.interp I I)).trans
    (Equiv.mk
      (sectionMap
        (T.toPshTypeExpr_interp_iso I I).inv)
      (sectionMap
        (T.toPshTypeExpr_interp_iso I I).hom)
      (fun s => by
        rw [← sectionMap_comp,
          Iso.inv_hom_id]
        exact sectionMap_id s)
      (fun s => by
        rw [← sectionMap_comp,
          Iso.hom_inv_id]
        exact sectionMap_id s))

/-- Functor embedding `RelSpanObj` into
`PshRelSpanObj (Type 0)` via the ULift-Yoneda
embedding `yonedaULift` on types and
`yonedaULiftRel` on relations. -/
def yonRelSpanEmbed :
    RelSpanObj ⥤
    PshRelSpanObj.{1, 0, 1} (Type 0) where
  obj
    | .typeNode I =>
      .typeNode (yonedaULift I)
    | .relNode I₀ I₁ R =>
      .relNode _ _ (yonedaULiftRel R)
  map {X Y} f :=
    match X, Y, f with
    | _, _, .id _ => .id _
    | _, _, .fstProj I₀ I₁ R =>
      .fstProj _ _ (yonedaULiftRel R)
    | _, _, .sndProj I₀ I₁ R =>
      .sndProj _ _ (yonedaULiftRel R)
  map_id X := by cases X <;> rfl
  map_comp {X Y Z} f g := by
    cases f <;> cases g <;> rfl

/-- Backward direction of the section-level
bridge: presheaf-level section-relatedness
implies Type-level relatedness. Extracted from
`relInterp_bridges`. -/
theorem TypeExpr.fullRelInterp_bridge_rev
    (T : TypeExpr) {A B : Type}
    (R : A → B → Prop)
    (choice : ∀ {α : Type}, Nonempty α → α)
    (a₀ : T.interp A A) (a₁ : T.interp B B)
    (h : (T.fullRelInterpPshRep R).sectionsRelated
      (T.toInterpSection a₀)
      (T.toInterpSection a₁)) :
    T.fullRelInterp R a₀ a₁ :=
  (T.fullRelInterp_bridge R choice a₀ a₁).mpr h

/-- Backward bridge from presheaf-level to
type-level parametric families. Given a
`PshParametricFamily` for `T.toPshTypeExpr`,
restricts along the ULift-Yoneda embedding to
obtain a type-level `ParametricFamily` for `T`.
The `choice` parameter is used for the Barr lift
witnesses in the `app` case of the relational
bridge. -/
def PshParametricFamily.toParametricFamily
    (T : TypeExpr)
    (p : PshParametricFamily T.toPshTypeExpr)
    (choice : ∀ {α : Type}, Nonempty α → α) :
    ParametricFamily T where
  app I :=
    (T.interpSectionEquiv I).symm
      (p.app (yonedaULift I))
  parametric I₀ I₁ R := by
    set a₀ := (T.interpSectionEquiv I₀).symm
      (p.app (yonedaULift I₀))
    set a₁ := (T.interpSectionEquiv I₁).symm
      (p.app (yonedaULift I₁))
    have hrt₀ : T.toInterpSection a₀ =
        p.app (yonedaULift I₀) :=
      (T.interpSectionEquiv I₀).right_inv _
    have hrt₁ : T.toInterpSection a₁ =
        p.app (yonedaULift I₁) :=
      (T.interpSectionEquiv I₁).right_inv _
    have hp := p.parametric _ _
      (yonedaULiftRel R) (Opposite.op PUnit)
    rw [T.fullRelInterp_pshRep_eq] at hp
    rw [← hrt₀, ← hrt₁] at hp
    have hsr : T.stageRelated R
        (Opposite.op PUnit)
        ((T.toInterpSection a₀).val
          (Opposite.op PUnit))
        ((T.toInterpSection a₁).val
          (Opposite.op PUnit)) := by
      simp only [pshProdOverToRel,
        Subfunctor.range, Set.mem_range] at hp
      obtain ⟨w, hw⟩ := hp
      exact ⟨w, congr_arg Prod.fst hw,
        congr_arg Prod.snd hw⟩
    exact (T.pointwise_bridge
      R choice (Opposite.op PUnit)
      (fun _ => a₀)
      (fun _ => a₁)).mpr hsr PUnit.unit

/-- Mutual induction for the off-diagonal and
wedge properties of `relInterp`. The off-diagonal
component constructs related pairs from
off-diagonal profunctor maps; the wedge component
derives the profunctor wedge equation from
relatedness. -/
private theorem PshTypeExpr.pshRelInterp_wedge_aux
    (T : PshTypeExpr.{u, v} C) :
    (∀ {P Q : Cᵒᵖ ⥤ Type (max u v)}
      (α : P ⟶ Q) (c : Cᵒᵖ)
      (x : (T.interp Q P).obj c),
      ((T.profMap α (𝟙 P)).app c x,
       (T.profMap (𝟙 Q) α).app c x) ∈
        (T.relInterp α).obj c) ∧
    (∀ {P Q : Cᵒᵖ ⥤ Type (max u v)}
      (α : P ⟶ Q) (c : Cᵒᵖ)
      (x₀ : (T.interp P P).obj c)
      (x₁ : (T.interp Q Q).obj c),
      (x₀, x₁) ∈ (T.relInterp α).obj c →
      (T.profMap (𝟙 P) α).app c x₀ =
        (T.profMap α (𝟙 Q)).app c x₁) := by
  induction T with
  | var =>
    exact ⟨fun _ _ _ => rfl,
      fun _ _ _ _ h => h⟩
  | app G T ih =>
    obtain ⟨ih_od, ih_w⟩ := ih
    constructor
    · intro P Q α c x
      change
        ((G.map (T.profMap α (𝟙 P))).app c x,
         (G.map (T.profMap (𝟙 Q) α)).app c x)
          ∈ (pshBarrLiftRel G
            (T.relInterp α)).obj c
      simp only [pshBarrLiftRel,
        pshProdOverToRel, Subfunctor.range_obj,
        Set.mem_range]
      let lift : T.interp Q P ⟶
          (T.relInterp α).toFunctor :=
        { app := fun c' y =>
            ⟨((T.profMap α (𝟙 P)).app c' y,
              (T.profMap (𝟙 Q) α).app c' y),
             ih_od α c' y⟩
          naturality := fun {_c₁ _c₂} f => by
            ext y; apply Subtype.ext
            exact Prod.ext
              (congr_fun
                ((T.profMap α
                  (𝟙 P)).naturality f) y)
              (congr_fun
                ((T.profMap (𝟙 Q)
                  α).naturality f) y) }
      have h_fst :
          lift ≫ (T.relInterp α).ι ≫
            pshProdFst (T.interp P P)
              (T.interp Q Q) =
            T.profMap α (𝟙 P) := by
        ext c' y; rfl
      have h_snd :
          lift ≫ (T.relInterp α).ι ≫
            pshProdSnd (T.interp P P)
              (T.interp Q Q) =
            T.profMap (𝟙 Q) α := by
        ext c' y; rfl
      refine ⟨(G.map lift).app c x,
        Prod.ext ?_ ?_⟩
      · change ((G.map lift ≫
            G.map ((T.relInterp α).ι ≫
              pshProdFst _ _)).app c) x = _
        rw [← G.map_comp, h_fst]
      · change ((G.map lift ≫
            G.map ((T.relInterp α).ι ≫
              pshProdSnd _ _)).app c) x = _
        rw [← G.map_comp, h_snd]
    · intro P Q α c x₀ x₁ hrel
      change (G.map (T.profMap (𝟙 P) α)).app c
        x₀ =
        (G.map (T.profMap α (𝟙 Q))).app c x₁
      change (x₀, x₁) ∈ (pshBarrLiftRel G
        (T.relInterp α)).obj c at hrel
      simp only [pshBarrLiftRel,
        pshProdOverToRel, Subfunctor.range_obj,
        Set.mem_range] at hrel
      obtain ⟨w, hw⟩ := hrel
      have hw₁ :
          (G.map ((T.relInterp α).ι ≫
            pshProdFst (T.interp P P)
              (T.interp Q Q))).app c w = x₀ :=
        congr_arg Prod.fst hw
      have hw₂ :
          (G.map ((T.relInterp α).ι ≫
            pshProdSnd (T.interp P P)
              (T.interp Q Q))).app c w = x₁ :=
        congr_arg Prod.snd hw
      have h_wedge :
          (T.relInterp α).ι ≫
            pshProdFst (T.interp P P)
              (T.interp Q Q) ≫
            T.profMap (𝟙 P) α =
          (T.relInterp α).ι ≫
            pshProdSnd (T.interp P P)
              (T.interp Q Q) ≫
            T.profMap α (𝟙 Q) := by
        ext c' ⟨⟨a₀, a₁⟩, ha⟩
        exact ih_w α c' a₀ a₁ ha
      rw [← hw₁, ← hw₂]
      change ((G.map ((T.relInterp α).ι ≫
              pshProdFst _ _) ≫
            G.map (T.profMap (𝟙 P) α)).app c)
            w =
          ((G.map ((T.relInterp α).ι ≫
              pshProdSnd _ _) ≫
            G.map (T.profMap α (𝟙 Q))).app c)
            w
      rw [← G.map_comp, ← G.map_comp,
        Category.assoc, Category.assoc, h_wedge]
  | arrow T₁ T₂ ih₁ ih₂ =>
    obtain ⟨ih₁_od, ih₁_w⟩ := ih₁
    obtain ⟨ih₂_od, ih₂_w⟩ := ih₂
    constructor
    · intro P Q α c x
      change _ ∈ (pshArrowRel
        (T₁.relInterp α)
        (T₂.relInterp α)).obj c
      simp only [pshArrowRel,
        pshProdOverToRel, Subfunctor.range_obj,
        Set.mem_range]
      refine ⟨⟨(((T₁.arrow T₂).profMap α
        (𝟙 P)).app c x,
        ((T₁.arrow T₂).profMap (𝟙 Q)
          α).app c x),
        fun d h w' => ?_⟩, rfl⟩
      dsimp [PshTypeExpr.profMap,
        pshIhomProfMap]
      rw [ih₁_w α d _ _ w'.property]
      exact ⟨⟨_, ih₂_od α d _⟩, rfl⟩
    · intro P Q α c x₀ x₁ hrel
      change (x₀, x₁) ∈ (pshArrowRel
        (T₁.relInterp α)
        (T₂.relInterp α)).obj c at hrel
      simp only [pshArrowRel,
        pshProdOverToRel, Subfunctor.range_obj,
        Set.mem_range] at hrel
      obtain ⟨wrel, hwrel⟩ := hrel
      have hwrel₁ : wrel.val.1 = x₀ :=
        congr_arg Prod.fst hwrel
      have hwrel₂ : wrel.val.2 = x₁ :=
        congr_arg Prod.snd hwrel
      dsimp [PshTypeExpr.profMap]
      apply Functor.functorHom_ext
      intro d h; funext a
      dsimp [pshIhomProfMap]
      let w_in :
          (T₁.relInterp α).toFunctor.obj d :=
        ⟨((T₁.profMap α (𝟙 P)).app d a,
          (T₁.profMap (𝟙 Q) α).app d a),
         ih₁_od α d a⟩
      obtain ⟨s, hs⟩ :=
        wrel.property d h w_in
      have hs₁ : s.val.1 =
          wrel.val.1.app d h
            ((T₁.profMap α (𝟙 P)).app d a) :=
        congr_arg Prod.fst hs
      have hs₂ : s.val.2 =
          wrel.val.2.app d h
            ((T₁.profMap (𝟙 Q) α).app d a) :=
        congr_arg Prod.snd hs
      rw [hwrel₁] at hs₁
      rw [hwrel₂] at hs₂
      rw [← hs₁, ← hs₂]
      exact ih₂_w α d _ _ s.property

/-- Off-diagonal profunctor maps produce related
pairs under `relInterp`. Extraction of the first
conjunct from `pshRelInterp_wedge_aux`. -/
theorem PshTypeExpr.pshRelInterp_of_offDiag
    (T : PshTypeExpr.{u, v} C)
    {P Q : Cᵒᵖ ⥤ Type (max u v)}
    (α : P ⟶ Q) (c : Cᵒᵖ)
    (x : (T.interp Q P).obj c) :
    ((T.profMap α (𝟙 P)).app c x,
     (T.profMap (𝟙 Q) α).app c x) ∈
      (T.relInterp α).obj c :=
  T.pshRelInterp_wedge_aux.1 α c x

/-- Relatedness under `relInterp` implies the
profunctor wedge equation. Extraction of the
second conjunct from
`pshRelInterp_wedge_aux`. -/
theorem PshTypeExpr.pshRelInterp_implies_wedge
    (T : PshTypeExpr.{u, v} C)
    {P Q : Cᵒᵖ ⥤ Type (max u v)}
    (α : P ⟶ Q) (c : Cᵒᵖ)
    (x₀ : (T.interp P P).obj c)
    (x₁ : (T.interp Q Q).obj c)
    (hrel : (x₀, x₁) ∈
      (T.relInterp α).obj c) :
    (T.profMap (𝟙 P) α).app c x₀ =
      (T.profMap α (𝟙 Q)).app c x₁ :=
  T.pshRelInterp_wedge_aux.2 α c x₀ x₁ hrel

/-- Every `PshParametricFamily` satisfies the
presheaf profunctor wedge condition: for any
morphism `α : P ⟶ Q`, the two composites
through `T.profMap` agree at each stage. -/
theorem PshParametricFamily.wedge
    {T : PshTypeExpr.{u, v} C}
    (p : PshParametricFamily T)
    {P Q : Cᵒᵖ ⥤ Type (max u v)}
    (α : P ⟶ Q) (c : Cᵒᵖ) :
    (T.profMap (𝟙 P) α).app c
      ((p.app P).val c) =
    (T.profMap α (𝟙 Q)).app c
      ((p.app Q).val c) :=
  T.pshRelInterp_implies_wedge α c _ _
    (p.parametric_graphRel α c)

section PshTypeExprCategory

variable {C : Type u} [Category.{v} C]

/-- A morphism between presheaf type expressions:
a family of natural transformations
`T₁.interp P P ⟶ T₂.interp P P` indexed by
presheaves `P`, satisfying a pointwise
parametricity condition. This is the
presheaf-level generalization of
`ParametricFamily (.arrow T₁ T₂)`. -/
@[ext]
structure PshTypeExprHom
    (T₁ T₂ : PshTypeExpr.{u, v} C) where
  /-- The natural transformation component at
  each presheaf. -/
  app : ∀ (P : Cᵒᵖ ⥤ Type (max u v)),
    T₁.interp P P ⟶ T₂.interp P P
  /-- Parametricity: for each relation `R`,
  the components preserve
  `fullRelInterp R` pointwise. -/
  parametric :
    ∀ (P Q : Cᵒᵖ ⥤ Type (max u v))
      (R : PshRel P Q) (c : Cᵒᵖ)
      (p : (T₁.interp P P).obj c)
      (q : (T₁.interp Q Q).obj c),
      (p, q) ∈ (T₁.fullRelInterp R).obj c →
      ((app P).app c p,
        (app Q).app c q) ∈
        (T₂.fullRelInterp R).obj c

/-- The identity morphism for presheaf type
expressions: the identity natural transformation
at each presheaf. -/
def pshTypeExprId
    (T : PshTypeExpr.{u, v} C) :
    PshTypeExprHom T T where
  app _ := 𝟙 _
  parametric _ _ _ _ _ _ h := by
    simp only [NatTrans.id_app, types_id_apply]
    exact h

/-- Composition of presheaf type expression
morphisms: pointwise composition of natural
transformations. -/
def pshTypeExprComp
    {T₁ T₂ T₃ : PshTypeExpr.{u, v} C}
    (η : PshTypeExprHom T₁ T₂)
    (μ : PshTypeExprHom T₂ T₃) :
    PshTypeExprHom T₁ T₃ where
  app P := η.app P ≫ μ.app P
  parametric P Q R c p q h := by
    simp only [NatTrans.comp_app,
      types_comp_apply]
    exact μ.parametric P Q R c _ _
      (η.parametric P Q R c p q h)

/-- Wrapper around `PshTypeExpr` to serve as
the object type for the category of presheaf
type expressions with parametric morphisms. -/
@[ext]
structure PshTypeExprCat
    (C : Type u) [Category.{v} C] where
  /-- The underlying presheaf type expression. -/
  expr : PshTypeExpr.{u, v} C

/-- The category of presheaf type expressions,
with morphisms given by `PshTypeExprHom`:
families of natural transformations satisfying
the full parametricity condition. -/
instance : Category (PshTypeExprCat C) where
  Hom T₁ T₂ := PshTypeExprHom T₁.expr T₂.expr
  id T := pshTypeExprId T.expr
  comp η μ := pshTypeExprComp η μ
  id_comp _ := PshTypeExprHom.ext
    (funext fun _ => Category.id_comp _)
  comp_id _ := PshTypeExprHom.ext
    (funext fun _ => Category.comp_id _)
  assoc _ _ _ := PshTypeExprHom.ext
    (funext fun _ => Category.assoc _ _ _)

end PshTypeExprCategory

section PshRelSpanDiagram

variable {C : Type u} [Category.{v} C]

/-- The relational span diagram for a presheaf
type expression `T`. Maps type-nodes to
`T.interp P P` and relation-nodes to the
subfunctor `(T.fullRelInterp R).toFunctor`.
Projection morphisms extract the first and
second components of the subfunctor. -/
def pshRelSpanDiagram
    (T : PshTypeExpr.{u, v} C) :
    PshRelSpanObj.{u, v, max u v} C ⥤
    (Cᵒᵖ ⥤ Type (max u v)) where
  obj X :=
    match X with
    | .typeNode P => T.interp P P
    | .relNode P Q R =>
      (T.fullRelInterp R).toFunctor
  map {X Y} f :=
    match X, Y, f with
    | _, _, .id _ => 𝟙 _
    | _, _, .fstProj P Q R =>
      (T.fullRelInterp R).ι ≫
        pshProdFst (T.interp P P)
          (T.interp Q Q)
    | _, _, .sndProj P Q R =>
      (T.fullRelInterp R).ι ≫
        pshProdSnd (T.interp P P)
          (T.interp Q Q)
  map_id := by intro X; cases X <;> rfl
  map_comp := by
    intro X Y Z f g
    cases f <;> cases g <;> rfl

/-- The presheaf diagram `pshRelSpanDiagram
T.toPshTypeExpr` restricted to `yonRelSpanEmbed`
at a type node recovers the type-level diagonal
interpretation up to `ULift`, via the section
equivalence `interpSectionEquiv`. -/
def yonRelSpanEmbed_typeNode_sections
    (T : TypeExpr) (I : Type) :
    ((pshRelSpanDiagram
      T.toPshTypeExpr).obj
      (yonRelSpanEmbed.obj
        (.typeNode I))).sections ≃
    ULift.{1} (T.interp I I) :=
  (T.interpSectionEquiv I).symm.trans
    Equiv.ulift.symm

/-- The presheaf-level fstProj, when applied to
a section of the relation-node presheaf and
restricted via `yonRelSpanEmbed_typeNode_sections`,
recovers the first component of the pair at
`PUnit` through the bridge isomorphism. -/
theorem yonRelSpanEmbed_fstProj_compat
    (T : TypeExpr) {I₀ I₁ : Type}
    (R : I₀ → I₁ → Prop)
    (s : ((pshRelSpanDiagram
      T.toPshTypeExpr).obj
      (yonRelSpanEmbed.obj
        (.relNode I₀ I₁ R))).sections) :
    (yonRelSpanEmbed_typeNode_sections T I₀)
      (sectionMap
        ((pshRelSpanDiagram T.toPshTypeExpr).map
          (yonRelSpanEmbed.map
            (RelSpanHom.fstProj I₀ I₁ R)))
        s) =
    ⟨((T.toPshTypeExpr_interp_iso I₀ I₀).hom.app
        (Opposite.op PUnit)
        (s.val (Opposite.op PUnit)).val.1
      ).down PUnit.unit⟩ := by
  rfl

/-- The presheaf-level sndProj, when applied to
a section of the relation-node presheaf and
restricted via `yonRelSpanEmbed_typeNode_sections`,
recovers the second component of the pair at
`PUnit` through the bridge isomorphism. -/
theorem yonRelSpanEmbed_sndProj_compat
    (T : TypeExpr) {I₀ I₁ : Type}
    (R : I₀ → I₁ → Prop)
    (s : ((pshRelSpanDiagram
      T.toPshTypeExpr).obj
      (yonRelSpanEmbed.obj
        (.relNode I₀ I₁ R))).sections) :
    (yonRelSpanEmbed_typeNode_sections T I₁)
      (sectionMap
        ((pshRelSpanDiagram T.toPshTypeExpr).map
          (yonRelSpanEmbed.map
            (RelSpanHom.sndProj I₀ I₁ R)))
        s) =
    ⟨((T.toPshTypeExpr_interp_iso I₁ I₁).hom.app
        (Opposite.op PUnit)
        (s.val (Opposite.op PUnit)).val.2
      ).down PUnit.unit⟩ := by
  rfl

/-- A `PshTypeExprHom` induces a natural
transformation between the corresponding
relational span diagrams. At type-nodes,
the morphism applies the natural transformation
component; at relation-nodes, it maps the
subfunctor using the parametricity condition. -/
def pshRelSpanDiagramMap
    {T₁ T₂ : PshTypeExpr.{u, v} C}
    (η : PshTypeExprHom T₁ T₂) :
    pshRelSpanDiagram T₁ ⟶
    pshRelSpanDiagram T₂ where
  app j :=
    match j with
    | .typeNode P => η.app P
    | .relNode P Q R =>
      { app := fun c ⟨⟨p, q⟩, h⟩ =>
          ⟨⟨(η.app P).app c p,
            (η.app Q).app c q⟩,
            η.parametric P Q R c p q h⟩
        naturality := fun {c d} k => by
          ext ⟨⟨p, q⟩, h⟩
          simp only [types_comp_apply]
          apply Subtype.ext
          apply Prod.ext
          · exact congr_fun
              ((η.app P).naturality k) p
          · exact congr_fun
              ((η.app Q).naturality k) q }
  naturality := by
    intro X Y f
    cases f <;> rfl

theorem pshRelSpanDiagramMap_id
    (T : PshTypeExpr.{u, v} C) :
    pshRelSpanDiagramMap (pshTypeExprId T) =
    𝟙 (pshRelSpanDiagram T) := by
  apply NatTrans.ext; funext j
  cases j with
  | typeNode P => rfl
  | relNode P Q R =>
    apply NatTrans.ext; funext c ⟨⟨_, _⟩, _⟩
    rfl

theorem pshRelSpanDiagramMap_comp
    {T₁ T₂ T₃ : PshTypeExpr.{u, v} C}
    (η : PshTypeExprHom T₁ T₂)
    (μ : PshTypeExprHom T₂ T₃) :
    pshRelSpanDiagramMap (pshTypeExprComp η μ) =
    pshRelSpanDiagramMap η ≫
      pshRelSpanDiagramMap μ := by
  apply NatTrans.ext; funext j
  cases j with
  | typeNode P => rfl
  | relNode P Q R =>
    apply NatTrans.ext; funext c ⟨⟨_, _⟩, _⟩
    rfl

/-- The relational span diagram construction
is functorial: a functor from the category
of presheaf type expressions to the functor
category `PshRelSpanObj C ⥤ (Cᵒᵖ ⥤ Type w)`. -/
def pshRelSpanDiagramFunctor :
    PshTypeExprCat.{u, v} C ⥤
    PshParametricFunctor.{u, v, max u v}
      C (Cᵒᵖ ⥤ Type (max u v)) where
  obj T := pshRelSpanDiagram T.expr
  map η := pshRelSpanDiagramMap η
  map_id T := pshRelSpanDiagramMap_id T.expr
  map_comp η μ := pshRelSpanDiagramMap_comp η μ

/-- `pshRelSpanDiagramFunctor` is fully faithful.
The preimage extracts type-node components;
parametricity follows from `β.naturality` at
relation-node projection morphisms. -/
def pshRelSpanDiagramFunctor_fullyFaithful :
    (pshRelSpanDiagramFunctor
      (C := C)).FullyFaithful where
  preimage {T₁ T₂} β :=
    { app := fun P =>
        β.app (.typeNode P)
      parametric := fun P Q R c p q h => by
        let fiber :
            (T₁.expr.fullRelInterp R
              ).toFunctor.obj c :=
          ⟨⟨p, q⟩, h⟩
        let m := (β.app (.relNode P Q R)).app
          c fiber
        have hfst :=
          congr_fun (NatTrans.congr_app
            (β.naturality
              (PshRelSpanHom.fstProj P Q R))
            c) fiber
        have hsnd :=
          congr_fun (NatTrans.congr_app
            (β.naturality
              (PshRelSpanHom.sndProj P Q R))
            c) fiber
        simp only [NatTrans.comp_app,
          types_comp_apply]
          at hfst hsnd
        change (β.app (.typeNode P)).app c p =
          m.val.1 at hfst
        change (β.app (.typeNode Q)).app c q =
          m.val.2 at hsnd
        rw [hfst, hsnd, Prod.mk.eta]
        exact m.property
    }
  map_preimage {T₁ T₂} β := by
    apply NatTrans.ext; funext X
    cases X with
    | typeNode P => rfl
    | relNode P Q R =>
      apply NatTrans.ext; funext c ⟨⟨p, q⟩, h⟩
      apply Subtype.ext
      have nf := congr_fun
        (NatTrans.congr_app (β.naturality
          (PshRelSpanHom.fstProj P Q R)) c)
        ⟨⟨p, q⟩, h⟩
      have ns := congr_fun
        (NatTrans.congr_app (β.naturality
          (PshRelSpanHom.sndProj P Q R)) c)
        ⟨⟨p, q⟩, h⟩
      dsimp [pshRelSpanDiagramFunctor,
        pshRelSpanDiagramMap,
        pshRelSpanDiagram] at nf ns ⊢
      apply Prod.ext <;> assumption

instance pshRelSpanDiagramFunctor_faithful :
    (pshRelSpanDiagramFunctor
      (C := C)).Faithful :=
  pshRelSpanDiagramFunctor_fullyFaithful.faithful

instance pshRelSpanDiagramFunctor_full :
    (pshRelSpanDiagramFunctor
      (C := C)).Full :=
  pshRelSpanDiagramFunctor_fullyFaithful.full

end PshRelSpanDiagram

end GebLean
