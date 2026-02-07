import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.ConnectedComponents
import Mathlib.CategoryTheory.Limits.Final
import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import Mathlib.CategoryTheory.Limits.IsConnected
import GebLean.Utilities.Elements

/-!
# Comprehensive factorization of a functor

Given a functor `F : C ⥤ D`, the comprehensive factorization
(Street-Walters 1973) factors `F` as `F = m ≫ e` where:

- `e` is a final functor
- `m` is a discrete fibration

The factorization goes through the category of elements of
the presheaf `K : Dᵒᵖ ⥤ Type` defined by
`K(d) = ConnectedComponents (StructuredArrow d F)`.

A dual factorization exists where `e'` is initial and `m'`
is a discrete opfibration, using the copresheaf
`K'(d) = ConnectedComponents (CostructuredArrow F d)`.
-/

namespace GebLean

open CategoryTheory

universe v₁ u₁ v₂ u₂

variable {E : Type u₁} [Category.{v₁} E]
  {B : Type u₂} [Category.{v₂} B]

section DiscreteFibration

/-- A functor `p : E ⥤ B` is a discrete fibration if for
every object `e : E` and morphism `f : b ⟶ p.obj e` in `B`,
there exists a unique lift: a pair `(e', g : e' ⟶ e)` in `E`
such that `p.obj e' = b` and `p.map g` equals `f` (up to the
transport `eqToHom`). -/
class IsDiscreteFibration (p : E ⥤ B) : Prop where
  unique_lift : ∀ (e : E) {b : B} (f : b ⟶ p.obj e),
    ∃! (g : (e' : E) × (e' ⟶ e)),
      ∃ (h : p.obj g.1 = b),
        p.map g.2 = eqToHom h ≫ f

/-- A functor `p : E ⥤ B` is a discrete opfibration if for
every object `e : E` and morphism `f : p.obj e ⟶ b` in `B`,
there exists a unique lift: a pair `(e', g : e ⟶ e')` in `E`
such that `p.obj e' = b` and `p.map g` equals
`f ≫ eqToHom h.symm`. -/
class IsDiscreteOpfibration (p : E ⥤ B) : Prop where
  unique_lift :
    ∀ (e : E) {b : B} (f : p.obj e ⟶ b),
      ∃! (g : (e' : E) × (e ⟶ e')),
        ∃ (h : p.obj g.1 = b),
          p.map g.2 = f ≫ eqToHom h.symm

end DiscreteFibration

section ElementsProperties

universe w

variable {C : Type u₂} [Category.{v₂} C]

/-- The forgetful functor from the (covariant) category of
elements of `F : C ⥤ Type w` is a discrete opfibration.
Given `⟨c, x⟩ : F.Elements` and `f : c ⟶ d`, the unique
lift is `⟨d, F.map f x⟩` with morphism `⟨f, rfl⟩`. -/
instance elements_π_isDiscreteOpfibration
    (F : C ⥤ Type w) :
    IsDiscreteOpfibration (CategoryOfElements.π F) where
  unique_lift := by
    intro ⟨c, x⟩ d f
    refine ⟨⟨⟨_, F.map f x⟩, ⟨f, rfl⟩⟩,
      ⟨rfl, by simp⟩, ?_⟩
    intro ⟨⟨d', y⟩, g⟩ ⟨h, hg⟩
    simp only [CategoryOfElements.π] at h hg
    subst h
    simp only [eqToHom_refl, Category.comp_id] at hg
    have hval : g.val = f := hg
    have hprop : F.map f x = y := by
      rw [← hval]; exact g.property
    subst hprop
    exact Sigma.ext rfl (heq_of_eq (Subtype.ext hval))

/-- The forgetful functor from the contravariant category
of elements of a presheaf `F : Cᵒᵖ ⥤ Type w` is a
discrete fibration. Given `op ⟨op c, x⟩ : F.ElementsPre`
and `f : b ⟶ c` in `C`, the unique lift is
`op ⟨op b, F.map f.op x⟩` with underlying morphism
`(⟨f.op, rfl⟩).op`. -/
private def elementsPre_lift
    (F : Cᵒᵖ ⥤ Type w)
    (e : F.ElementsPre) {b : C}
    (f : b ⟶ (elementsPre_π F).obj e) :
    (e' : F.ElementsPre) × (e' ⟶ e) :=
  ⟨Opposite.op
      ⟨Opposite.op b, F.map f.op e.unop.snd⟩,
    Quiver.Hom.op
      (⟨f.op, rfl⟩ :
        e.unop ⟶ ⟨Opposite.op b,
          F.map f.op e.unop.snd⟩)⟩

instance elementsPre_π_isDiscreteFibration
    (F : Cᵒᵖ ⥤ Type w) :
    IsDiscreteFibration (elementsPre_π F) where
  unique_lift := by
    intro e b f
    refine ⟨elementsPre_lift F e f,
      ⟨rfl, by simp only [eqToHom_refl,
        Category.id_comp]; rfl⟩, ?_⟩
    rintro ⟨⟨⟨c_op, x⟩⟩, g⟩ ⟨h, hg⟩
    simp only [elementsPre_π_obj] at h
    subst h
    simp only [eqToHom_refl, Category.id_comp,
      elementsPre_π_map] at hg
    have hval : g.unop.val = f.op := by
      rw [← Quiver.Hom.op_unop g.unop.val, hg]
    have hprop : F.map f.op e.unop.snd = x := by
      rw [← hval]; exact g.unop.property
    subst hprop
    exact Sigma.ext rfl
      (heq_of_eq (Quiver.Hom.unop_inj
        (Subtype.ext hval)))

end ElementsProperties

section ComprehensiveFactorization

variable {C : Type u₁} [Category.{v₁} C]
  {D : Type u₂} [Category.{v₂} D]

/-- The comprehensive copresheaf of a functor `F : C ⥤ D`.
At `d : D`, this is the set of connected components of the
comma category `CostructuredArrow F d` (the category of
objects of `C` equipped with a morphism to `d`).

Functoriality in `d` uses `CostructuredArrow.map`. -/
@[simps]
def comprehensiveCopresheaf (F : C ⥤ D) : D ⥤ Type _ where
  obj d := ConnectedComponents (CostructuredArrow F d)
  map f :=
    Functor.mapConnectedComponents (CostructuredArrow.map f)
  map_id d := by
    ext x
    exact Quotient.inductionOn x fun σ => by
      simp [Functor.mapConnectedComponents_mk,
        CostructuredArrow.map_id]
  map_comp f g := by
    ext x
    exact Quotient.inductionOn x fun σ => by
      simp [Functor.mapConnectedComponents_mk,
        CostructuredArrow.map_comp]

/-- The comprehensive presheaf of a functor `F : C ⥤ D`.
At `d : Dᵒᵖ`, this is the set of connected components of
the comma category `StructuredArrow d.unop F` (the category
of objects of `C` equipped with a morphism from `d`).

Functoriality in `d` uses `StructuredArrow.map`. -/
@[simps]
def comprehensivePresheaf (F : C ⥤ D) :
    Dᵒᵖ ⥤ Type _ where
  obj d :=
    ConnectedComponents (StructuredArrow d.unop F)
  map f :=
    Functor.mapConnectedComponents
      (StructuredArrow.map f.unop)
  map_id d := by
    ext x
    exact Quotient.inductionOn x fun σ => by
      simp [Functor.mapConnectedComponents_mk,
        StructuredArrow.map_id]
  map_comp f g := by
    ext x
    exact Quotient.inductionOn x fun σ => by
      simp [Functor.mapConnectedComponents_mk,
        StructuredArrow.map_comp]

variable (F : C ⥤ D)

/-- The initial functor in the copresheaf comprehensive
factorization. Sends `c : C` to
`(F.obj c, [id_{F(c)}]) : (comprehensiveCopresheaf F).Elements`.

The connected component `[id_{F(c)}]` is the class of the
identity costructured arrow `CostructuredArrow.mk (𝟙 (F.obj c))`
in `CostructuredArrow F (F.obj c)`. -/
def comprehensiveE' :
    C ⥤ (comprehensiveCopresheaf F).Elements where
  obj c :=
    ⟨F.obj c,
      Quotient.mk _
        (CostructuredArrow.mk (𝟙 (F.obj c)))⟩
  map {c₁ c₂} f :=
    ⟨F.map f, by
      simp only [comprehensiveCopresheaf_map,
        Functor.mapConnectedComponents_mk,
        CostructuredArrow.map_mk, Category.id_comp]
      exact Quotient.sound
        (Zigzag.of_hom
          (CostructuredArrow.homMk f (by simp)))⟩
  map_id c := by
    ext
    change F.map (𝟙 c) = 𝟙 (F.obj c)
    exact F.map_id c
  map_comp f g := by
    ext
    change F.map (f ≫ g) = F.map f ≫ F.map g
    exact F.map_comp f g

/-- The discrete opfibration in the copresheaf comprehensive
factorization. This is the forgetful functor from the
category of elements of `comprehensiveCopresheaf F`,
projecting `(d, [σ])` to `d`. -/
abbrev comprehensiveM' :
    (comprehensiveCopresheaf F).Elements ⥤ D :=
  CategoryOfElements.π (comprehensiveCopresheaf F)

/-- The copresheaf discrete opfibration: the forgetful
functor from elements of `comprehensiveCopresheaf F` is a
discrete opfibration. -/
instance comprehensiveM'_isDiscreteOpfibration :
    IsDiscreteOpfibration (comprehensiveM' F) :=
  elements_π_isDiscreteOpfibration _

/-- The copresheaf comprehensive factorization commutes:
`comprehensiveE' F ⋙ comprehensiveM' F = F`. -/
theorem comprehensiveFactorization'_comm :
    comprehensiveE' F ⋙ comprehensiveM' F = F := by
  apply CategoryTheory.Functor.ext
  case h_obj => intro c; rfl
  case h_map =>
    intro c₁ c₂ f
    simp [comprehensiveE', comprehensiveM',
      eqToHom_refl]

/-- Lift a costructured arrow `τ : CostructuredArrow F d`
with `⟦τ⟧ = ⟦σ₀⟧` to an element of
`CostructuredArrow (comprehensiveE' F) ⟨d, ⟦σ₀⟧⟩`.
The underlying morphism is `τ.hom : F.obj τ.left ⟶ d`,
and the copresheaf condition holds because
`CostructuredArrow.mk τ.hom` is isomorphic to `τ` (by
`CostructuredArrow.eta`), hence in the same connected
component. -/
private def liftCostArrow
    {d : D} {σ₀ : CostructuredArrow F d}
    (τ : CostructuredArrow F d)
    (hτ : (⟦τ⟧ :
      ConnectedComponents (CostructuredArrow F d)) =
      ⟦σ₀⟧) :
    CostructuredArrow (comprehensiveE' F)
      (⟨d, ⟦σ₀⟧⟩ :
        (comprehensiveCopresheaf F).Elements) :=
  CostructuredArrow.mk (Y := τ.left)
    ⟨τ.hom, by
      simp only [comprehensiveCopresheaf_map]
      dsimp [comprehensiveE']
      simp only [Category.id_comp]
      rw [← hτ]
      exact Quotient.sound
        (Zigzag.of_inv (CostructuredArrow.eta τ).hom)⟩

/-- Lift a morphism `φ : τ₁ ⟶ τ₂` in `CostructuredArrow F d`
to a morphism between the corresponding lifted costructured
arrows in `CostructuredArrow (comprehensiveE' F) ⟨d, ⟦σ₀⟧⟩`.
The underlying morphism `φ.left : τ₁.left ⟶ τ₂.left` is
preserved, and the costructured arrow condition reduces to
`φ.w` (that `F.map φ.left ≫ τ₂.hom = τ₁.hom`). -/
private def liftCostArrowHom
    {d : D} {σ₀ : CostructuredArrow F d}
    {τ₁ τ₂ : CostructuredArrow F d}
    (hτ₁ : (⟦τ₁⟧ :
      ConnectedComponents (CostructuredArrow F d)) =
      ⟦σ₀⟧)
    (hτ₂ : (⟦τ₂⟧ :
      ConnectedComponents (CostructuredArrow F d)) =
      ⟦σ₀⟧)
    (φ : τ₁ ⟶ τ₂) :
    liftCostArrow F τ₁ hτ₁ ⟶ liftCostArrow F τ₂ hτ₂ :=
  CostructuredArrow.homMk φ.left (by
    ext
    simp only [liftCostArrow, comprehensiveE',
      CategoryOfElements.comp_val]
    dsimp
    simp only [CommaMorphism.w, Functor.const_obj_map]
    exact Category.comp_id _)

/-- Extract the component membership proof from a
costructured arrow over `⟨d, ⟦σ₀⟧⟩`: the costructured
arrow `CostructuredArrow.mk α.hom.val` lies in the
connected component of `σ₀`. -/
private lemma costArrowComponent
    {d : D} {σ₀ : CostructuredArrow F d}
    (α : CostructuredArrow (comprehensiveE' F)
      (⟨d, ⟦σ₀⟧⟩ :
        (comprehensiveCopresheaf F).Elements)) :
    (⟦CostructuredArrow.mk (S := F) (T := d)
      α.hom.val⟧ :
      ConnectedComponents (CostructuredArrow F d)) =
      ⟦σ₀⟧ := by
  have hp := α.hom.property
  simp only [comprehensiveCopresheaf_map] at hp
  dsimp [comprehensiveE'] at hp
  simp only [Category.id_comp] at hp
  exact hp

/-- Any costructured arrow `α` in
`CostructuredArrow (comprehensiveE' F) ⟨d, ⟦σ₀⟧⟩` equals
the lift of `CostructuredArrow.mk α.hom.val`. The
underlying data are identical, and the proof component
is propositionally irrelevant. -/
private lemma compE'CostArrow_eq_lift
    {d : D} {σ₀ : CostructuredArrow F d}
    (α : CostructuredArrow (comprehensiveE' F)
      (⟨d, ⟦σ₀⟧⟩ :
        (comprehensiveCopresheaf F).Elements)) :
    α = liftCostArrow F
      (CostructuredArrow.mk (S := F) (T := d)
        α.hom.val)
      (costArrowComponent F α) := by
  cases α
  simp only [liftCostArrow, CostructuredArrow.mk]
  congr 1

/-- Lift a `Zag` step from `CostructuredArrow F d` to
`CostructuredArrow (comprehensiveE' F) ⟨d, ⟦σ₀⟧⟩`. -/
private lemma liftZag
    {d : D} {σ₀ : CostructuredArrow F d}
    {τ₁ τ₂ : CostructuredArrow F d}
    (hτ₁ : (⟦τ₁⟧ :
      ConnectedComponents (CostructuredArrow F d)) =
      ⟦σ₀⟧)
    (hτ₂ : (⟦τ₂⟧ :
      ConnectedComponents (CostructuredArrow F d)) =
      ⟦σ₀⟧)
    (h : Zag τ₁ τ₂) :
    Zag (liftCostArrow F τ₁ hτ₁)
      (liftCostArrow F τ₂ hτ₂) := by
  rcases h with ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩
  · exact Or.inl
      ⟨liftCostArrowHom F hτ₁ hτ₂ φ⟩
  · exact Or.inr
      ⟨liftCostArrowHom F hτ₂ hτ₁ φ⟩

/-- Lift a `Zigzag` from `CostructuredArrow F d` to
`CostructuredArrow (comprehensiveE' F) ⟨d, ⟦σ₀⟧⟩`.
The proof proceeds by induction on the zigzag,
deriving component membership of intermediate objects
from transitivity of connected components. -/
private lemma liftZigzag
    {d : D} {σ₀ : CostructuredArrow F d}
    {τ₁ τ₂ : CostructuredArrow F d}
    (hτ₁ : (⟦τ₁⟧ :
      ConnectedComponents (CostructuredArrow F d)) =
      ⟦σ₀⟧)
    (hτ₂ : (⟦τ₂⟧ :
      ConnectedComponents (CostructuredArrow F d)) =
      ⟦σ₀⟧)
    (h : Zigzag τ₁ τ₂) :
    Zigzag (liftCostArrow F τ₁ hτ₁)
      (liftCostArrow F τ₂ hτ₂) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c hab hbc ih =>
    have hb : (⟦b⟧ :
        ConnectedComponents
          (CostructuredArrow F d)) =
        ⟦σ₀⟧ :=
      (Quotient.sound
        (Relation.ReflTransGen.single
          hbc)).trans hτ₂
    exact (ih hb).tail
      (liftZag F hb hτ₂ hbc)

/-- The copresheaf e-functor `comprehensiveE' F` is
initial. For each element `⟨d, ⟦σ₀⟧⟩`, the costructured
arrow category `CostructuredArrow (comprehensiveE' F) ⟨d, ⟦σ₀⟧⟩`
is connected: every object corresponds to a costructured
arrow `τ : CostructuredArrow F d` in the component of `σ₀`,
and the zigzag from the component lifts via
`liftCostArrowHom`. -/
instance comprehensiveE'_initial :
    Functor.Initial (comprehensiveE' F) where
  out := by
    intro ⟨d, x⟩
    induction x using Quotient.inductionOn with
    | h σ₀ =>
      haveI : Nonempty
          (CostructuredArrow (comprehensiveE' F)
            ⟨d, ⟦σ₀⟧⟩) :=
        ⟨liftCostArrow F σ₀ rfl⟩
      apply zigzag_isConnected
      intro α₁ α₂
      rw [compE'CostArrow_eq_lift F α₁,
        compE'CostArrow_eq_lift F α₂]
      exact liftZigzag F
        (costArrowComponent F α₁)
        (costArrowComponent F α₂)
        (Quotient.exact
          ((costArrowComponent F α₁).trans
            (costArrowComponent F α₂).symm))

end ComprehensiveFactorization

section ComprehensiveFactorizationPre

variable {C : Type u₁} [Category.{v₁} C]
  {D : Type u₂} [Category.{v₂} D]

variable (F : C ⥤ D)

/-- The final functor in the presheaf comprehensive
factorization. Sends `c : C` to `op (op (F.obj c),
[id_{F(c)}])` in `(comprehensivePresheaf F).ElementsPre`.

The connected component `[id_{F(c)}]` is the class of the
identity structured arrow
`StructuredArrow.mk (𝟙 (F.obj c))`
in `StructuredArrow (F.obj c) F`. -/
def comprehensiveE :
    C ⥤ (comprehensivePresheaf F).ElementsPre where
  obj c :=
    Opposite.op
      ⟨Opposite.op (F.obj c),
        Quotient.mk _
          (StructuredArrow.mk (𝟙 (F.obj c)))⟩
  map {c₁ c₂} f :=
    Quiver.Hom.op
      ⟨(F.map f).op, by
        simp only [comprehensivePresheaf_map,
          Functor.mapConnectedComponents_mk,
          StructuredArrow.map_mk, Category.comp_id]
        exact Quotient.sound
          (Zigzag.of_inv
            (StructuredArrow.homMk f (by simp)))⟩
  map_id c := by
    apply congrArg Quiver.Hom.op
    ext
    simp only [F.map_id, op_id]
    rfl
  map_comp f g := by
    apply congrArg Quiver.Hom.op
    ext
    simp only [F.map_comp, op_comp]
    rfl

/-- The discrete fibration in the presheaf comprehensive
factorization. This is the forgetful functor from the
contravariant category of elements of
`comprehensivePresheaf F`, projecting
`op (op d, [σ])` to `d`. -/
abbrev comprehensiveM :
    (comprehensivePresheaf F).ElementsPre ⥤ D :=
  elementsPre_π (comprehensivePresheaf F)

/-- The presheaf discrete fibration: the forgetful functor
from elements of `comprehensivePresheaf F` is a discrete
fibration. -/
instance comprehensiveM_isDiscreteFibration :
    IsDiscreteFibration (comprehensiveM F) :=
  elementsPre_π_isDiscreteFibration _

/-- The presheaf comprehensive factorization commutes:
`comprehensiveE F ⋙ comprehensiveM F = F`. -/
theorem comprehensiveFactorization_comm :
    comprehensiveE F ⋙ comprehensiveM F = F := by
  apply CategoryTheory.Functor.ext
  case h_obj => intro c; rfl
  case h_map =>
    intro c₁ c₂ f
    simp [comprehensiveE, comprehensiveM,
      eqToHom_refl]

/-- Lift a structured arrow `σ : StructuredArrow d F` with
`⟦σ⟧ = ⟦σ₀⟧` to an element of
`StructuredArrow (op ⟨op d, ⟦σ₀⟧⟩) (comprehensiveE F)`.
The structured arrow has `right := σ.right`, and its hom
encodes `σ.hom : d ⟶ F.obj σ.right` as a morphism in
`ElementsPre` (reversed through `op`). -/
private def liftStrArrow
    {d : D} {σ₀ : StructuredArrow d F}
    (σ : StructuredArrow d F)
    (hσ : (⟦σ⟧ :
      ConnectedComponents (StructuredArrow d F)) =
      ⟦σ₀⟧) :
    StructuredArrow
      (Opposite.op
        ⟨Opposite.op d, ⟦σ₀⟧⟩ :
        (comprehensivePresheaf F).ElementsPre)
      (comprehensiveE F) :=
  StructuredArrow.mk (Y := σ.right)
    (Quiver.Hom.op
      ⟨σ.hom.op, by
        simp only [comprehensivePresheaf_map]
        dsimp [comprehensiveE]
        simp only [Category.comp_id]
        rw [← hσ]
        exact Quotient.sound
          (Zigzag.of_inv
            (StructuredArrow.eta σ).hom)⟩)

/-- Lift a morphism `φ : σ₁ ⟶ σ₂` in `StructuredArrow d F`
to a morphism between the corresponding lifted structured
arrows in
`StructuredArrow (op ⟨op d, ⟦σ₀⟧⟩) (comprehensiveE F)`. -/
private def liftStrArrowHom
    {d : D} {σ₀ : StructuredArrow d F}
    {σ₁ σ₂ : StructuredArrow d F}
    (hσ₁ : (⟦σ₁⟧ :
      ConnectedComponents (StructuredArrow d F)) =
      ⟦σ₀⟧)
    (hσ₂ : (⟦σ₂⟧ :
      ConnectedComponents (StructuredArrow d F)) =
      ⟦σ₀⟧)
    (φ : σ₁ ⟶ σ₂) :
    liftStrArrow F σ₁ hσ₁ ⟶
      liftStrArrow F σ₂ hσ₂ :=
  StructuredArrow.homMk φ.right (by
    apply Quiver.Hom.unop_inj
    ext
    dsimp [liftStrArrow, comprehensiveE]
    change (F.map φ.right).op ≫ σ₁.hom.op =
      σ₂.hom.op
    simp only [← op_comp]
    exact congrArg Opposite.op
      ((CommaMorphism.w φ).symm.trans (by simp)))

/-- Extract the component membership proof from a
structured arrow over `op ⟨op d, ⟦σ₀⟧⟩`: the structured
arrow `StructuredArrow.mk` of the underlying morphism lies
in the connected component of `σ₀`. -/
private lemma strArrowComponent
    {d : D} {σ₀ : StructuredArrow d F}
    (α : StructuredArrow
      (Opposite.op
        ⟨Opposite.op d, ⟦σ₀⟧⟩ :
        (comprehensivePresheaf F).ElementsPre)
      (comprehensiveE F)) :
    (⟦StructuredArrow.mk (S := d) (T := F)
      α.hom.unop.val.unop⟧ :
      ConnectedComponents (StructuredArrow d F)) =
      ⟦σ₀⟧ := by
  have hp := α.hom.unop.property
  simp only [comprehensivePresheaf_map] at hp
  dsimp [comprehensiveE] at hp
  simp only [Category.comp_id] at hp
  exact hp

/-- Any structured arrow `α` in
`StructuredArrow (op ⟨op d, ⟦σ₀⟧⟩) (comprehensiveE F)`
equals the lift of `StructuredArrow.mk α.hom.unop.val.unop`.
The underlying data are identical, and the proof component
is propositionally irrelevant. -/
private lemma compEStrArrow_eq_lift
    {d : D} {σ₀ : StructuredArrow d F}
    (α : StructuredArrow
      (Opposite.op
        ⟨Opposite.op d, ⟦σ₀⟧⟩ :
        (comprehensivePresheaf F).ElementsPre)
      (comprehensiveE F)) :
    α = liftStrArrow F
      (StructuredArrow.mk (S := d) (T := F)
        α.hom.unop.val.unop)
      (strArrowComponent F α) := by
  cases α
  simp only [liftStrArrow, StructuredArrow.mk]
  congr 1

/-- Lift a `Zag` step from `StructuredArrow d F` to
`StructuredArrow (op ⟨op d, ⟦σ₀⟧⟩) (comprehensiveE F)`. -/
private lemma liftZagStr
    {d : D} {σ₀ : StructuredArrow d F}
    {τ₁ τ₂ : StructuredArrow d F}
    (hτ₁ : (⟦τ₁⟧ :
      ConnectedComponents (StructuredArrow d F)) =
      ⟦σ₀⟧)
    (hτ₂ : (⟦τ₂⟧ :
      ConnectedComponents (StructuredArrow d F)) =
      ⟦σ₀⟧)
    (h : Zag τ₁ τ₂) :
    Zag (liftStrArrow F τ₁ hτ₁)
      (liftStrArrow F τ₂ hτ₂) := by
  rcases h with ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩
  · exact Or.inl
      ⟨liftStrArrowHom F hτ₁ hτ₂ φ⟩
  · exact Or.inr
      ⟨liftStrArrowHom F hτ₂ hτ₁ φ⟩

/-- Lift a `Zigzag` from `StructuredArrow d F` to
`StructuredArrow (op ⟨op d, ⟦σ₀⟧⟩) (comprehensiveE F)`.
The proof proceeds by induction on the zigzag,
deriving component membership of intermediate objects
from transitivity of connected components. -/
private lemma liftZigzagStr
    {d : D} {σ₀ : StructuredArrow d F}
    {τ₁ τ₂ : StructuredArrow d F}
    (hτ₁ : (⟦τ₁⟧ :
      ConnectedComponents (StructuredArrow d F)) =
      ⟦σ₀⟧)
    (hτ₂ : (⟦τ₂⟧ :
      ConnectedComponents (StructuredArrow d F)) =
      ⟦σ₀⟧)
    (h : Zigzag τ₁ τ₂) :
    Zigzag (liftStrArrow F τ₁ hτ₁)
      (liftStrArrow F τ₂ hτ₂) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c hab hbc ih =>
    have hb : (⟦b⟧ :
        ConnectedComponents
          (StructuredArrow d F)) =
        ⟦σ₀⟧ :=
      (Quotient.sound
        (Relation.ReflTransGen.single
          hbc)).trans hτ₂
    exact (ih hb).tail
      (liftZagStr F hb hτ₂ hbc)

/-- The presheaf e-functor `comprehensiveE F` is final.
For each element `op ⟨op d, ⟦σ₀⟧⟩ : ElementsPre`, the
structured arrow category
`StructuredArrow (op ⟨op d, ⟦σ₀⟧⟩) (comprehensiveE F)` is
connected: every object corresponds to a structured arrow
`τ : StructuredArrow d F` in the component of `σ₀`, and the
zigzag from the component lifts via `liftStrArrowHom`. -/
instance comprehensiveE_final :
    Functor.Final (comprehensiveE F) where
  out := by
    intro ⟨⟨d_op, x⟩⟩
    induction x using Quotient.inductionOn with
    | h σ₀ =>
      haveI : Nonempty
          (StructuredArrow
            (Opposite.op
              ⟨d_op, ⟦σ₀⟧⟩ :
              (comprehensivePresheaf F).ElementsPre)
            (comprehensiveE F)) :=
        ⟨liftStrArrow F σ₀ rfl⟩
      apply zigzag_isConnected
      intro α₁ α₂
      rw [compEStrArrow_eq_lift F α₁,
        compEStrArrow_eq_lift F α₂]
      exact liftZigzagStr F
        (strArrowComponent F α₁)
        (strArrowComponent F α₂)
        (Quotient.exact
          ((strArrowComponent F α₁).trans
            (strArrowComponent F α₂).symm))

end ComprehensiveFactorizationPre

section ComprehensiveKanExtension

open Limits.Types

variable {C : Type u₁} [Category.{v₁} C]
  {D : Type u₂} [Category.{v₂} D]

variable (F : C ⥤ D)

/-- The unit of the copresheaf left extension. At `c : C`,
sends `PUnit.unit` to the connected component of the
identity costructured arrow `CostructuredArrow.mk (𝟙 _)`
in `CostructuredArrow F (F.obj c)`. -/
@[simps]
def comprehensiveCopresheafUnit :
    constPUnitFunctor.{max u₁ v₂} C ⟶
      F ⋙ comprehensiveCopresheaf F where
  app c _ :=
    Quotient.mk _
      (CostructuredArrow.mk (𝟙 (F.obj c)))
  naturality c₁ c₂ f := by
    ext ⟨⟩
    simp only [types_comp_apply, constPUnitFunctor,
      Functor.const_obj_map,
      Functor.comp_map, comprehensiveCopresheaf_map,
      Functor.mapConnectedComponents_mk,
      CostructuredArrow.map_mk, Category.id_comp]
    exact Quotient.sound
      (Zigzag.of_inv
        (CostructuredArrow.homMk f (by simp)))

/-- The copresheaf comprehensive factorization as a left
extension of the constant `PUnit` functor along `F`. -/
def comprehensiveCopresheafLeftExt :
    F.LeftExtension
      (constPUnitFunctor.{max u₁ v₂} C) :=
  Functor.LeftExtension.mk
    (comprehensiveCopresheaf F)
    (comprehensiveCopresheafUnit F)

/-- For the constant `PUnit` diagram on
`CostructuredArrow F d`, a morphism `φ : g₁ ⟶ g₂`
implies `s.ι.app g₁ = s.ι.app g₂` for any cocone `s`,
because the diagram maps are all `𝟙 PUnit`. -/
private lemma coconeAppEqOfHom
    {d : D}
    (s : Limits.Cocone
      (CostructuredArrow.proj F d ⋙
        constPUnitFunctor.{max u₁ v₂} C))
    {g₁ g₂ : CostructuredArrow F d}
    (φ : g₁ ⟶ g₂) :
    s.ι.app g₁ = s.ι.app g₂ := by
  have h := s.ι.naturality φ
  simp only [Functor.comp_map,
    Functor.const_obj_map] at h
  exact h.symm

/-- For the constant `PUnit` diagram, zigzag-connected
costructured arrows have equal cocone components. -/
private lemma coconeAppEqOfZigzag
    {d : D}
    (s : Limits.Cocone
      (CostructuredArrow.proj F d ⋙
        constPUnitFunctor.{max u₁ v₂} C))
    {g₁ g₂ : CostructuredArrow F d}
    (h : Zigzag g₁ g₂) :
    s.ι.app g₁ = s.ι.app g₂ := by
  induction h with
  | refl => rfl
  | tail _ hbc ih =>
    rw [ih]
    rcases hbc with ⟨⟨φ⟩⟩ | ⟨⟨ψ⟩⟩
    · exact coconeAppEqOfHom F s φ
    · exact (coconeAppEqOfHom F s ψ).symm

/-- The copresheaf comprehensive factorization is a
pointwise left Kan extension: for each `d : D`, the cocone
`(comprehensiveCopresheafLeftExt F).coconeAt d` is a colimit.

The colimit property holds because the cocone maps each
`g : CostructuredArrow F d` to its connected component
`⟦g⟧`, and zigzag-connected costructured arrows are
identified in `ConnectedComponents`. -/
def comprehensiveCopresheaf_isPointwiseLan :
    Functor.LeftExtension.IsPointwiseLeftKanExtension
      (comprehensiveCopresheafLeftExt F) := by
  intro d
  exact
    { desc := fun s =>
        Quotient.lift (fun g => s.ι.app g PUnit.unit)
          (fun g₁ g₂ h => by
            have := coconeAppEqOfZigzag F s
              (Quotient.exact (Quotient.sound h))
            exact congrFun this PUnit.unit)
      fac := fun s g => by
        ext ⟨⟩
        simp only [types_comp_apply]
        change Quotient.lift _ _ _ = _
        dsimp [Functor.LeftExtension.coconeAt,
          comprehensiveCopresheafLeftExt,
          Functor.LeftExtension.mk]
        rw [Category.id_comp]
        exact congrFun
          (coconeAppEqOfHom F s
            (CostructuredArrow.eta g).hom).symm _
      uniq := fun s m hm => by
        funext x
        exact Quotient.inductionOn x fun g => by
          rw [Quotient.lift_mk]
          have h := congrFun (hm g) PUnit.unit
          simp only [types_comp_apply] at h
          dsimp [Functor.LeftExtension.coconeAt,
            comprehensiveCopresheafLeftExt,
            Functor.LeftExtension.mk] at h
          rw [Category.id_comp] at h
          rw [← h]
          exact congrArg m
            (Quotient.sound
              (Zigzag.of_hom
                (CostructuredArrow.eta g).hom))
    }

/-- The unit of the presheaf left extension. At `c : Cᵒᵖ`,
sends `PUnit.unit` to the connected component of the
identity structured arrow `StructuredArrow.mk (𝟙 _)` in
`StructuredArrow c.unop F`. -/
@[simps]
def comprehensivePresheafUnit :
    constPUnitFunctor.{max u₁ v₂} Cᵒᵖ ⟶
      F.op ⋙ comprehensivePresheaf F where
  app c _ :=
    Quotient.mk _
      (StructuredArrow.mk (𝟙 (F.obj c.unop)))
  naturality c₁ c₂ f := by
    ext ⟨⟩
    simp only [types_comp_apply, constPUnitFunctor,
      Functor.const_obj_map,
      Functor.comp_map, Functor.op_map,
      comprehensivePresheaf_map,
      Functor.mapConnectedComponents_mk,
      StructuredArrow.map_mk]
    exact Quotient.sound
      (Zigzag.of_hom
        (StructuredArrow.homMk f.unop (by simp)))

/-- The presheaf comprehensive factorization as a left
extension of the constant `PUnit` functor along `F.op`. -/
def comprehensivePresheafLeftExt :
    F.op.LeftExtension
      (constPUnitFunctor.{max u₁ v₂} Cᵒᵖ) :=
  Functor.LeftExtension.mk
    (comprehensivePresheaf F)
    (comprehensivePresheafUnit F)

/-- For the constant `PUnit` diagram on
`CostructuredArrow F.op d`, a morphism `φ : g₁ ⟶ g₂`
implies `s.ι.app g₁ = s.ι.app g₂` for any cocone `s`. -/
private lemma coconeAppEqOfHomPre
    {d : Dᵒᵖ}
    (s : Limits.Cocone
      (CostructuredArrow.proj F.op d ⋙
        constPUnitFunctor.{max u₁ v₂} Cᵒᵖ))
    {g₁ g₂ : CostructuredArrow F.op d}
    (φ : g₁ ⟶ g₂) :
    s.ι.app g₁ = s.ι.app g₂ := by
  have h := s.ι.naturality φ
  simp only [Functor.comp_map,
    Functor.const_obj_map] at h
  exact h.symm

/-- Convert a structured arrow
`σ : StructuredArrow d.unop F` to the corresponding
costructured arrow `CostructuredArrow F.op d`. -/
private def strToCostArr
    {d : Dᵒᵖ}
    (σ : StructuredArrow d.unop F) :
    CostructuredArrow F.op d :=
  CostructuredArrow.mk
    (show F.op.obj (Opposite.op σ.right) ⟶ d
      from σ.hom.op)

/-- A morphism `φ : σ₁ ⟶ σ₂` in
`StructuredArrow d.unop F` induces a reverse morphism
`strToCostArr σ₂ ⟶ strToCostArr σ₁` in
`CostructuredArrow F.op d`. -/
private def strToCostArrHomRev
    {d : Dᵒᵖ}
    {σ₁ σ₂ : StructuredArrow d.unop F}
    (φ : σ₁ ⟶ σ₂) :
    strToCostArr F σ₂ ⟶ strToCostArr F σ₁ :=
  CostructuredArrow.homMk φ.right.op (by
    dsimp [strToCostArr]
    simp only [← op_comp]
    exact congrArg Opposite.op
      (StructuredArrow.w φ))

/-- The presheaf comprehensive factorization is a
pointwise left Kan extension: for each `d : Dᵒᵖ`, the
cocone `(comprehensivePresheafLeftExt F).coconeAt d` is a
colimit.

The diagram `CostructuredArrow.proj F.op d ⋙
constPUnitFunctor Cᵒᵖ` maps each `g : CostructuredArrow
F.op d` to `PUnit`. The cocone maps `g` to the connected
component of the corresponding structured arrow in
`StructuredArrow d.unop F`. -/
def comprehensivePresheaf_isPointwiseLan :
    Functor.LeftExtension.IsPointwiseLeftKanExtension
      (comprehensivePresheafLeftExt F) := by
  intro d
  exact
    { desc := fun s =>
        Quotient.lift
          (fun σ =>
            s.ι.app (strToCostArr F σ) PUnit.unit)
          (fun σ₁ σ₂ h => by
            induction h with
            | refl => rfl
            | tail _ hbc ih =>
              exact ih.trans (by
                rcases hbc with ⟨⟨φ⟩⟩ | ⟨⟨ψ⟩⟩
                · have hmor :=
                    strToCostArrHomRev F φ
                  exact congrFun
                    (coconeAppEqOfHomPre
                      F s hmor).symm _
                · have hmor :=
                    strToCostArrHomRev F ψ
                  have h := s.ι.naturality hmor
                  simp only [Functor.comp_map,
                    Functor.const_obj_map] at h
                  exact congrFun h.symm _))
      fac := fun s g => by
        ext ⟨⟩
        simp only [types_comp_apply]
        change Quotient.lift _ _ _ = _
        dsimp [Functor.LeftExtension.coconeAt,
          comprehensivePresheafLeftExt,
          Functor.LeftExtension.mk]
        rw [Category.comp_id]
        exact congrFun
          (coconeAppEqOfHomPre F s
            (CostructuredArrow.eta g).hom).symm _
      uniq := fun s m hm => by
        funext x
        exact Quotient.inductionOn x fun σ => by
          rw [Quotient.lift_mk]
          have h := congrFun
            (hm (strToCostArr F σ)) PUnit.unit
          simp only [types_comp_apply] at h
          dsimp [Functor.LeftExtension.coconeAt,
            comprehensivePresheafLeftExt,
            Functor.LeftExtension.mk] at h
          rw [Category.comp_id] at h
          rw [← h]
          exact congrArg m
            (Quotient.sound
              (Zigzag.of_hom
                (StructuredArrow.eta σ).hom)) }

end ComprehensiveKanExtension

end GebLean
