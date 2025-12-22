import GebLean.PolyAdjunctions
import GebLean.FreeCoequalizerCompletion
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers

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

/-! ## Coequalizer Data for Type

To compute coequalizers in functor categories (D ⥤ Type), we first need
coequalizers in Type. The coequalizer of f, g : X → Y is the quotient of Y
by the equivalence relation generated by f(x) ~ g(x) for all x : X.
-/

section CoequalizerType

universe t

/-- The relation for coequalizers in Type: y₁ ~ y₂ if ∃x, f(x) = y₁ ∧ g(x) = y₂. -/
def typeCoeqRel {X Y : Type t} (f g : X → Y) : Y → Y → Prop :=
  fun y₁ y₂ => ∃ x, f x = y₁ ∧ g x = y₂

/-- The coequalizer object in Type. -/
def typeCoeq {X Y : Type t} (f g : X → Y) : Type t :=
  Quot (typeCoeqRel f g)

/-- The projection to the coequalizer. -/
def typeCoeqπ {X Y : Type t} (f g : X → Y) : Y → typeCoeq f g :=
  Quot.mk _

/-- The coequalizer condition: π ∘ f = π ∘ g. -/
theorem typeCoeq_condition {X Y : Type t} (f g : X → Y) :
    typeCoeqπ f g ∘ f = typeCoeqπ f g ∘ g := by
  funext x
  apply Quot.sound
  exact ⟨x, rfl, rfl⟩

/-- Factorization through the coequalizer. -/
def typeCoeqDesc {X Y Z : Type t} (f g : X → Y) (h : Y → Z)
    (w : h ∘ f = h ∘ g) : typeCoeq f g → Z :=
  Quot.lift h (fun y₁ y₂ ⟨x, hf, hg⟩ => by
    rw [← hf, ← hg]
    exact congrFun w x)

/-- The factorization property: π ≫ desc = h. -/
theorem typeCoeq_fac {X Y Z : Type t} (f g : X → Y) (h : Y → Z)
    (w : h ∘ f = h ∘ g) : typeCoeqDesc f g h w ∘ typeCoeqπ f g = h := rfl

/-- Uniqueness of the factorization. -/
theorem typeCoeq_uniq {X Y Z : Type t} (f g : X → Y) (h : Y → Z)
    (w : h ∘ f = h ∘ g) (m : typeCoeq f g → Z)
    (hm : m ∘ typeCoeqπ f g = h) : m = typeCoeqDesc f g h w := by
  funext q
  revert q
  apply Quot.ind
  intro y
  exact congrFun hm y

/-- CoequalizerData instance for Type. -/
instance : CoequalizerData (Type t) where
  coeq := fun f g => typeCoeq f g
  π := fun f g => typeCoeqπ f g
  condition := fun f g => typeCoeq_condition f g
  desc := fun f g h w => typeCoeqDesc f g h w
  fac := fun f g h w => typeCoeq_fac f g h w
  uniq := fun f g h w m hm => typeCoeq_uniq f g h w m hm

/-- Pointwise factorization for coequalizers in Type. -/
@[simp]
theorem typeCoeqDesc_mk {X Y Z : Type t} (f g : X → Y) (h : Y → Z)
    (w : h ∘ f = h ∘ g) (y : Y) :
    typeCoeqDesc f g h w (Quot.mk (typeCoeqRel f g) y) = h y := rfl

end CoequalizerType

/-! ## Coequalizer Data for Functor Categories

Coequalizers in functor categories (C ⥤ Type) are computed pointwise.
-/

section CoequalizerFunctor

universe s t r

variable {C : Type s} [Category.{t} C]

/-- Helper to extract component equality from natural transformation equality. -/
theorem natTrans_comp_app_eq {F G H : C ⥤ Type r}
    (α β : F ⟶ G) (γ : G ⟶ H) (w : α ≫ γ = β ≫ γ) (c : C) :
    α.app c ≫ γ.app c = β.app c ≫ γ.app c := by
  have := congrArg (fun η => η.app c) w
  simp only [NatTrans.comp_app] at this
  exact this

/-- The coequalizer functor for two natural transformations. -/
def functorCoeq (F G : C ⥤ Type r) (α β : F ⟶ G) : C ⥤ Type r where
  obj c := CoequalizerData.coeq (α.app c) (β.app c)
  map {c d} f := CoequalizerData.desc (α.app c) (β.app c)
    (G.map f ≫ CoequalizerData.π (α.app d) (β.app d))
    (by
      ext x
      simp only [types_comp_apply]
      have hα := α.naturality f
      have hβ := β.naturality f
      have eq1 : G.map f (α.app c x) = α.app d (F.map f x) := (congrFun hα x).symm
      have eq2 : G.map f (β.app c x) = β.app d (F.map f x) := (congrFun hβ x).symm
      rw [eq1, eq2]
      exact congrFun (CoequalizerData.condition (α.app d) (β.app d)) (F.map f x))
  map_id c := by
    symm
    apply CoequalizerData.uniq
    rw [Category.comp_id, G.map_id, Category.id_comp]
  map_comp {c d e} f g := by
    symm
    apply CoequalizerData.uniq
    rw [← Category.assoc, CoequalizerData.fac, Category.assoc, CoequalizerData.fac,
        ← Category.assoc, ← G.map_comp]

/-- Helper for the proof that the map construction coequalizes. -/
theorem functorCoeq_map_coequalizes
    {F G : C ⥤ Type r} (α β : F ⟶ G) {c d : C} (f : c ⟶ d) :
    α.app c ≫ (G.map f ≫ CoequalizerData.π (α.app d) (β.app d)) =
    β.app c ≫ (G.map f ≫ CoequalizerData.π (α.app d) (β.app d)) := by
  ext x
  simp only [types_comp_apply]
  have hα := α.naturality f
  have hβ := β.naturality f
  have eq1 : G.map f (α.app c x) = α.app d (F.map f x) := (congrFun hα x).symm
  have eq2 : G.map f (β.app c x) = β.app d (F.map f x) := (congrFun hβ x).symm
  rw [eq1, eq2]
  exact congrFun (CoequalizerData.condition (α.app d) (β.app d)) (F.map f x)

/-- The projection natural transformation to the coequalizer. -/
def functorCoeqπ (F G : C ⥤ Type r) (α β : F ⟶ G) :
    G ⟶ functorCoeq F G α β where
  app c := CoequalizerData.π (α.app c) (β.app c)
  naturality {c d} f := by
    ext y
    simp only [types_comp_apply, functorCoeq]
    symm
    exact congrFun (CoequalizerData.fac (α.app c) (β.app c)
      (G.map f ≫ CoequalizerData.π (α.app d) (β.app d))
      (functorCoeq_map_coequalizes α β f)) y

/-- The coequalizer condition for natural transformations. -/
theorem functorCoeq_condition (F G : C ⥤ Type r) (α β : F ⟶ G) :
    α ≫ functorCoeqπ F G α β = β ≫ functorCoeqπ F G α β := by
  ext c x
  simp only [NatTrans.comp_app, types_comp_apply, functorCoeqπ]
  exact congrFun (CoequalizerData.condition (α.app c) (β.app c)) x

/-- Factorization through the functor coequalizer. -/
def functorCoeqDesc (F G H : C ⥤ Type r) (α β : F ⟶ G) (γ : G ⟶ H)
    (w : α ≫ γ = β ≫ γ) : functorCoeq F G α β ⟶ H where
  app c := CoequalizerData.desc (α.app c) (β.app c) (γ.app c)
    (natTrans_comp_app_eq α β γ w c)
  naturality {c d} f := by
    ext q
    revert q
    apply Quot.ind
    intro y
    simp only [types_comp_apply, functorCoeq]
    dsimp only [CoequalizerData.desc, CoequalizerData.π, typeCoeqπ]
    simp only [typeCoeqDesc_mk]
    have nat := congrFun (γ.naturality f) y
    simp only [types_comp_apply] at nat
    exact nat

/-- The factorization property for functor coequalizers. -/
theorem functorCoeq_fac (F G H : C ⥤ Type r) (α β : F ⟶ G) (γ : G ⟶ H)
    (w : α ≫ γ = β ≫ γ) :
    functorCoeqπ F G α β ≫ functorCoeqDesc F G H α β γ w = γ := by
  ext c y
  simp only [NatTrans.comp_app, types_comp_apply, functorCoeqπ, functorCoeqDesc]
  exact congrFun (CoequalizerData.fac (α.app c) (β.app c) (γ.app c)
    (natTrans_comp_app_eq α β γ w c)) y

/-- Uniqueness of factorization for functor coequalizers. -/
theorem functorCoeq_uniq (F G H : C ⥤ Type r) (α β : F ⟶ G) (γ : G ⟶ H)
    (w : α ≫ γ = β ≫ γ) (m : functorCoeq F G α β ⟶ H)
    (hm : functorCoeqπ F G α β ≫ m = γ) :
    m = functorCoeqDesc F G H α β γ w := by
  ext c q
  revert q
  apply Quot.ind
  intro y
  have hmComp := congrArg (fun η => η.app c) hm
  simp only [NatTrans.comp_app, functorCoeqπ] at hmComp
  simp only [functorCoeqDesc]
  exact congrFun (CoequalizerData.uniq (α.app c) (β.app c) (γ.app c)
    (natTrans_comp_app_eq α β γ w c) (m.app c) hmComp) (Quot.mk _ y)

/-- CoequalizerData instance for functor categories into Type. -/
instance functorCoequalizerData : CoequalizerData (C ⥤ Type r) where
  coeq := fun α β => functorCoeq _ _ α β
  π := fun α β => functorCoeqπ _ _ α β
  condition := fun α β => functorCoeq_condition _ _ α β
  desc := fun α β γ w => functorCoeqDesc _ _ _ α β γ w
  fac := fun α β γ w => functorCoeq_fac _ _ _ α β γ w
  uniq := fun α β γ w m hm => functorCoeq_uniq _ _ _ α β γ w m hm

end CoequalizerFunctor

/-! ## Evaluation Functor

The evaluation functor sends a polynomial presentation (P, Q, α, β) to the
coequalizer of the induced natural transformations eval(α), eval(β) between
the corresponding copresheaves.
-/

section Evaluation

variable {D}

/--
The copresheaf represented by a polynomial presentation. For a presentation
(P, Q, α, β), this is the coequalizer of the natural transformations
`ccrToFunctorMap α` and `ccrToFunctorMap β`.
-/
def PolyPresentation.toCopresheaf
    (X : PolyPresentation.{u, v, w} D) : D ⥤ Type (max w v) :=
  CoequalizerData.coeq (ccrToFunctorMap X.fst) (ccrToFunctorMap X.snd)

/--
The projection from the target polynomial functor to the copresheaf.
-/
def PolyPresentation.toCopresheafπ
    (X : PolyPresentation.{u, v, w} D) :
    ccrToFunctor X.tgt ⟶ X.toCopresheaf :=
  CoequalizerData.π (ccrToFunctorMap X.fst) (ccrToFunctorMap X.snd)

/--
The coequalizer condition: the two parallel morphisms become equal after
composing with the projection.
-/
theorem PolyPresentation.toCopresheaf_condition
    (X : PolyPresentation.{u, v, w} D) :
    ccrToFunctorMap X.fst ≫ X.toCopresheafπ =
    ccrToFunctorMap X.snd ≫ X.toCopresheafπ :=
  CoequalizerData.condition (ccrToFunctorMap X.fst) (ccrToFunctorMap X.snd)

/--
For a morphism of polynomial presentations, the induced morphism on coequalizers.

Given f : X → Y where X = (P, Q, α, β) and Y = (P', Q', α', β'), the morphism
`ccrToFunctorMap f.tgtHom` coequalizes the parallel pair for Y (when composed
appropriately), so it factors through the coequalizer of X.
-/
def PolyPresentation.Hom.toCopresheafHom
    {X Y : PolyPresentation.{u, v, w} D}
    (f : X ⟶ Y) : X.toCopresheaf ⟶ Y.toCopresheaf :=
  CoequalizerData.desc
    (ccrToFunctorMap X.fst) (ccrToFunctorMap X.snd)
    (ccrToFunctorMap f.tgtHom ≫ Y.toCopresheafπ)
    (by
      rw [← Category.assoc, ← Category.assoc]
      rw [← ccrToFunctorMap_comp, ← ccrToFunctorMap_comp]
      rw [← f.fst_comm, ← f.snd_comm]
      rw [ccrToFunctorMap_comp, ccrToFunctorMap_comp]
      rw [Category.assoc, Category.assoc]
      congr 1
      exact Y.toCopresheaf_condition)

/--
The factorization property: π ≫ toCopresheafHom = tgtHom ≫ π.
-/
theorem PolyPresentation.Hom.toCopresheafHom_fac
    {X Y : PolyPresentation.{u, v, w} D} (f : X ⟶ Y) :
    X.toCopresheafπ ≫ f.toCopresheafHom =
    ccrToFunctorMap f.tgtHom ≫ Y.toCopresheafπ :=
  CoequalizerData.fac _ _ _ _

end Evaluation

/-! ## Functor Category Representation

A polynomial presentation is equivalent to a functor from the walking parallel
pair category to the category of polynomial functors. This provides access to
mathlib's functor category machinery.
-/

section FunctorCategoryEquiv

open Limits
open WalkingParallelPair
open WalkingParallelPairHom

variable {D}

/--
Convert a polynomial presentation to a functor from WalkingParallelPair.
-/
def PolyPresentation.toParallelPair (X : PolyPresentation.{u, v, w} D) :
    WalkingParallelPair ⥤ CoprodCovarRepCat.{u, v, w} D :=
  parallelPair X.fst X.snd

@[simp]
theorem PolyPresentation.toParallelPair_obj_zero (X : PolyPresentation.{u, v, w} D) :
    X.toParallelPair.obj zero = X.src := rfl

@[simp]
theorem PolyPresentation.toParallelPair_obj_one (X : PolyPresentation.{u, v, w} D) :
    X.toParallelPair.obj one = X.tgt := rfl

@[simp]
theorem PolyPresentation.toParallelPair_map_left (X : PolyPresentation.{u, v, w} D) :
    X.toParallelPair.map left = X.fst := rfl

@[simp]
theorem PolyPresentation.toParallelPair_map_right (X : PolyPresentation.{u, v, w} D) :
    X.toParallelPair.map right = X.snd := rfl

/--
Convert a functor from WalkingParallelPair to a polynomial presentation.
-/
def PolyPresentation.ofParallelPair
    (F : WalkingParallelPair ⥤ CoprodCovarRepCat.{u, v, w} D) :
    PolyPresentation.{u, v, w} D where
  src := F.obj zero
  tgt := F.obj one
  fst := F.map left
  snd := F.map right

@[simp]
theorem PolyPresentation.ofParallelPair_src
    (F : WalkingParallelPair ⥤ CoprodCovarRepCat.{u, v, w} D) :
    (ofParallelPair F).src = F.obj zero := rfl

@[simp]
theorem PolyPresentation.ofParallelPair_tgt
    (F : WalkingParallelPair ⥤ CoprodCovarRepCat.{u, v, w} D) :
    (ofParallelPair F).tgt = F.obj one := rfl

@[simp]
theorem PolyPresentation.ofParallelPair_fst
    (F : WalkingParallelPair ⥤ CoprodCovarRepCat.{u, v, w} D) :
    (ofParallelPair F).fst = F.map left := rfl

@[simp]
theorem PolyPresentation.ofParallelPair_snd
    (F : WalkingParallelPair ⥤ CoprodCovarRepCat.{u, v, w} D) :
    (ofParallelPair F).snd = F.map right := rfl

/--
Round-trip: toParallelPair ∘ ofParallelPair = id on functors.
-/
theorem PolyPresentation.toParallelPair_ofParallelPair_eq
    (F : WalkingParallelPair ⥤ CoprodCovarRepCat.{u, v, w} D) :
    (ofParallelPair F).toParallelPair = F := by
  have hobj : ∀ j, (ofParallelPair F).toParallelPair.obj j = F.obj j := by
    intro j; cases j <;> rfl
  have hmap : ∀ j k (f : j ⟶ k), (ofParallelPair F).toParallelPair.map f =
      eqToHom (hobj j) ≫ F.map f ≫ eqToHom (hobj k).symm := by
    intro j k f
    cases f <;> simp [ofParallelPair, toParallelPair, parallelPair]
  exact CategoryTheory.Functor.ext hobj hmap

/--
Round-trip: ofParallelPair ∘ toParallelPair = id on presentations.
-/
theorem PolyPresentation.ofParallelPair_toParallelPair
    (X : PolyPresentation.{u, v, w} D) :
    ofParallelPair X.toParallelPair = X := rfl

/--
Convert a morphism of polynomial presentations to a natural transformation.
-/
def PolyPresentation.Hom.toNatTrans {X Y : PolyPresentation.{u, v, w} D} (f : X ⟶ Y) :
    X.toParallelPair ⟶ Y.toParallelPair :=
  parallelPairHom X.fst X.snd Y.fst Y.snd f.srcHom f.tgtHom
    (f.fst_comm.symm) (f.snd_comm.symm)

@[simp]
theorem PolyPresentation.Hom.toNatTrans_app_zero
    {X Y : PolyPresentation.{u, v, w} D} (f : X ⟶ Y) :
    f.toNatTrans.app zero = f.srcHom := rfl

@[simp]
theorem PolyPresentation.Hom.toNatTrans_app_one
    {X Y : PolyPresentation.{u, v, w} D} (f : X ⟶ Y) :
    f.toNatTrans.app one = f.tgtHom := rfl

/--
Convert a natural transformation between parallel pair functors to a morphism
of polynomial presentations.
-/
def PolyPresentation.Hom.ofNatTrans
    {F G : WalkingParallelPair ⥤ CoprodCovarRepCat.{u, v, w} D}
    (η : F ⟶ G) : ofParallelPair F ⟶ ofParallelPair G where
  srcHom := η.app zero
  tgtHom := η.app one
  fst_comm := (η.naturality left).symm
  snd_comm := (η.naturality right).symm

@[simp]
theorem PolyPresentation.Hom.ofNatTrans_srcHom
    {F G : WalkingParallelPair ⥤ CoprodCovarRepCat.{u, v, w} D}
    (η : F ⟶ G) : (Hom.ofNatTrans η).srcHom = η.app zero := rfl

@[simp]
theorem PolyPresentation.Hom.ofNatTrans_tgtHom
    {F G : WalkingParallelPair ⥤ CoprodCovarRepCat.{u, v, w} D}
    (η : F ⟶ G) : (Hom.ofNatTrans η).tgtHom = η.app one := rfl

/--
Round-trip: toNatTrans ∘ ofNatTrans = id on natural transformations
(up to the functor isomorphism).
-/
theorem PolyPresentation.Hom.toNatTrans_ofNatTrans
    {X Y : PolyPresentation.{u, v, w} D} (f : X ⟶ Y) :
    Hom.ofNatTrans f.toNatTrans = f :=
  Hom.ext _ _ rfl rfl

/--
The functor from PolyPresentation to the functor category.
-/
@[simps]
def polyPresentationToFunctorCat :
    PolyPresentation.{u, v, w} D ⥤
    (WalkingParallelPair ⥤ CoprodCovarRepCat.{u, v, w} D) where
  obj := PolyPresentation.toParallelPair
  map := PolyPresentation.Hom.toNatTrans
  map_id X := by
    apply NatTrans.ext
    funext j
    cases j
    · exact ccrHom_ext _ _ rfl (by simp)
    · exact ccrHom_ext _ _ rfl (by simp)
  map_comp f g := by
    apply NatTrans.ext
    funext j
    cases j
    · exact ccrHom_ext _ _ rfl (by simp)
    · exact ccrHom_ext _ _ rfl (by simp)

/--
The functor from the functor category to PolyPresentation.
-/
@[simps]
def functorCatToPolyPresentation :
    (WalkingParallelPair ⥤ CoprodCovarRepCat.{u, v, w} D) ⥤
    PolyPresentation.{u, v, w} D where
  obj := PolyPresentation.ofParallelPair
  map := PolyPresentation.Hom.ofNatTrans
  map_id _ := PolyPresentation.Hom.ext _ _ rfl rfl
  map_comp _ _ := PolyPresentation.Hom.ext _ _ rfl rfl

/--
The unit of the equivalence: Id ≅ functorCatToPolyPresentation ⋙ polyPresentationToFunctorCat.
-/
def polyPresentationEquivUnit :
    𝟭 (WalkingParallelPair ⥤ CoprodCovarRepCat.{u, v, w} D) ≅
    functorCatToPolyPresentation ⋙ polyPresentationToFunctorCat :=
  NatIso.ofComponents
    (fun F => eqToIso (PolyPresentation.toParallelPair_ofParallelPair_eq F).symm)
    (fun {F G} η => by
      simp only [Functor.comp_obj, functorCatToPolyPresentation_obj,
        polyPresentationToFunctorCat_obj, Functor.id_obj, eqToIso.hom,
        Functor.comp_map, functorCatToPolyPresentation_map,
        polyPresentationToFunctorCat_map, Functor.id_map]
      apply NatTrans.ext
      funext j
      simp only [NatTrans.comp_app, eqToHom_app, PolyPresentation.Hom.toNatTrans]
      cases j
      · simp only [parallelPairHom_app_zero, PolyPresentation.Hom.ofNatTrans_srcHom,
          eqToHom_refl, Category.id_comp, Category.comp_id]
      · simp only [parallelPairHom_app_one, PolyPresentation.Hom.ofNatTrans_tgtHom,
          eqToHom_refl, Category.id_comp, Category.comp_id])

/--
The counit of the equivalence: polyPresentationToFunctorCat ⋙ functorCatToPolyPresentation ≅ Id.
-/
def polyPresentationEquivCounit :
    polyPresentationToFunctorCat ⋙ functorCatToPolyPresentation ≅
    𝟭 (PolyPresentation.{u, v, w} D) :=
  NatIso.ofComponents
    (fun X => eqToIso (PolyPresentation.ofParallelPair_toParallelPair X))
    (fun {X Y} f => by
      simp only [Functor.comp_obj, polyPresentationToFunctorCat_obj,
        functorCatToPolyPresentation_obj, Functor.id_obj, eqToIso.hom,
        Functor.comp_map, polyPresentationToFunctorCat_map,
        functorCatToPolyPresentation_map, Functor.id_map,
        PolyPresentation.ofParallelPair_toParallelPair]
      simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
      exact PolyPresentation.Hom.ext _ _ rfl rfl)

/--
The equivalence between polynomial presentations and the functor category.
-/
def polyPresentationFunctorCatEquiv :
    PolyPresentation.{u, v, w} D ≌
    (WalkingParallelPair ⥤ CoprodCovarRepCat.{u, v, w} D) where
  functor := polyPresentationToFunctorCat
  inverse := functorCatToPolyPresentation
  unitIso := polyPresentationEquivCounit.symm
  counitIso := polyPresentationEquivUnit.symm
  functor_unitIso_comp X := by
    simp only [polyPresentationEquivCounit, polyPresentationEquivUnit,
      Iso.symm_hom, NatIso.ofComponents_inv_app,
      polyPresentationToFunctorCat_obj, polyPresentationToFunctorCat_map,
      functorCatToPolyPresentation_obj, eqToIso.inv, Functor.comp_obj,
      Functor.id_obj]
    apply NatTrans.ext
    funext j
    simp only [NatTrans.comp_app, eqToHom_app]
    cases j
    · simp only [PolyPresentation.Hom.toNatTrans, parallelPairHom_app_zero,
        eqToHom_refl, Category.comp_id, NatTrans.id_app,
        PolyPresentation.id_srcHom', PolyPresentation.toParallelPair_obj_zero]
    · simp only [PolyPresentation.Hom.toNatTrans, parallelPairHom_app_one,
        eqToHom_refl, Category.comp_id, NatTrans.id_app,
        PolyPresentation.id_tgtHom', PolyPresentation.toParallelPair_obj_one]

end FunctorCategoryEquiv

end GebLean
