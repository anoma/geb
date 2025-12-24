import GebLean.PolyAdjunctions
import GebLean.FreeCoequalizerCompletion
import GebLean.Utilities.SetoidCat
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.Logic.Relation

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

/--
The identity morphism on a presentation induces the identity on the coequalizer.
-/
theorem PolyPresentation.Hom.toCopresheafHom_id
    (X : PolyPresentation.{u, v, w} D) :
    (𝟙 X : X ⟶ X).toCopresheafHom = 𝟙 X.toCopresheaf := by
  symm
  apply CoequalizerData.uniq
  simp only [id_tgtHom', ccrToFunctorMap_id, Category.id_comp]
  rfl

/--
Composition of presentation morphisms induces composition on coequalizers.
-/
theorem PolyPresentation.Hom.toCopresheafHom_comp
    {X Y Z : PolyPresentation.{u, v, w} D}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).toCopresheafHom = f.toCopresheafHom ≫ g.toCopresheafHom := by
  symm
  apply CoequalizerData.uniq
  calc X.toCopresheafπ ≫ f.toCopresheafHom ≫ g.toCopresheafHom
      = (X.toCopresheafπ ≫ f.toCopresheafHom) ≫ g.toCopresheafHom := by
          rw [Category.assoc]
    _ = (ccrToFunctorMap f.tgtHom ≫ Y.toCopresheafπ) ≫ g.toCopresheafHom := by
          rw [toCopresheafHom_fac]
    _ = ccrToFunctorMap f.tgtHom ≫ (Y.toCopresheafπ ≫ g.toCopresheafHom) := by
          rw [Category.assoc]
    _ = ccrToFunctorMap f.tgtHom ≫ (ccrToFunctorMap g.tgtHom ≫ Z.toCopresheafπ) := by
          rw [toCopresheafHom_fac]
    _ = (ccrToFunctorMap f.tgtHom ≫ ccrToFunctorMap g.tgtHom) ≫ Z.toCopresheafπ := by
          rw [← Category.assoc]
    _ = ccrToFunctorMap (f.tgtHom ≫ g.tgtHom) ≫ Z.toCopresheafπ := by
          rw [← ccrToFunctorMap_comp]
    _ = ccrToFunctorMap (f ≫ g).tgtHom ≫ Z.toCopresheafπ := rfl

/--
The evaluation functor from polynomial presentations to copresheaves.
Maps a presentation (P, Q, α, β) to coeq(eval(α), eval(β)).
-/
@[simps]
def polyPresentationEvalFunctor :
    PolyPresentation.{u, v, w} D ⥤ (D ⥤ Type (max w v)) where
  obj := PolyPresentation.toCopresheaf
  map := PolyPresentation.Hom.toCopresheafHom
  map_id := PolyPresentation.Hom.toCopresheafHom_id
  map_comp := PolyPresentation.Hom.toCopresheafHom_comp

/-! ## Properties of the Evaluation Functor

The evaluation functor has some properties related to the full faithfulness
of `ccrEvalFunctor`. The induced map on coequalizers is determined by the
target component `tgtHom` of a presentation morphism.
-/

/--
Two presentation morphisms with equal target components induce the same
map on coequalizers.
-/
theorem PolyPresentation.Hom.toCopresheafHom_eq_of_tgtHom_eq
    {X Y : PolyPresentation.{u, v, w} D}
    (f g : X ⟶ Y) (h : f.tgtHom = g.tgtHom) :
    f.toCopresheafHom = g.toCopresheafHom := by
  apply CoequalizerData.uniq
  have := toCopresheafHom_fac f
  unfold toCopresheafπ at this ⊢
  rw [this, h]

/--
If two presentation morphisms induce the same map on coequalizers, then their
target components induce the same map after applying `ccrToFunctorMap`.
-/
theorem PolyPresentation.Hom.ccrToFunctorMap_tgtHom_eq_of_toCopresheafHom_eq
    {X Y : PolyPresentation.{u, v, w} D}
    (f g : X ⟶ Y) (h : f.toCopresheafHom = g.toCopresheafHom) :
    ccrToFunctorMap f.tgtHom ≫ Y.toCopresheafπ =
    ccrToFunctorMap g.tgtHom ≫ Y.toCopresheafπ := by
  rw [← toCopresheafHom_fac f, ← toCopresheafHom_fac g, h]

end Evaluation

/-! ## Setoid-Valued Copresheaves

A polynomial presentation gives rise not only to a Type-valued copresheaf
(via coequalizers), but also to a Setoid-valued copresheaf where the setoid
structure tracks the coequalizer equivalence relation without quotienting.

This preserves more structure and is useful for constructive development of
the equivalence between presentations and copresheaves.
-/

section SetoidEvaluation

variable {D}

/--
The coequalizer relation on the target polynomial evaluation at an object A.
Two elements y₁, y₂ : ccrEval X.tgt A are related if there exists
x : ccrEval X.src A such that X.fst maps x to y₁ and X.snd maps x to y₂.
-/
def PolyPresentation.coeqRelAt (X : PolyPresentation.{u, v, w} D) (A : D) :
    ccrEval X.tgt A → ccrEval X.tgt A → Prop :=
  fun y₁ y₂ => ∃ x : ccrEval X.src A,
    ccrToFunctorMapApp X.fst A x = y₁ ∧ ccrToFunctorMapApp X.snd A x = y₂

/--
The setoid on the target polynomial evaluation at an object A.
This is the equivalence relation generated by the coequalizer relation.
-/
def PolyPresentation.coeqSetoidAt (X : PolyPresentation.{u, v, w} D) (A : D) :
    Setoid (ccrEval X.tgt A) :=
  Relation.EqvGen.setoid (X.coeqRelAt A)

/--
The setoid bundle for a presentation at an object A.
-/
def PolyPresentation.toSetoidBundleAt (X : PolyPresentation.{u, v, w} D) (A : D) :
    SetoidBundle :=
  ⟨ccrEval X.tgt A, X.coeqSetoidAt A⟩

/--
The map on carrier types induced by a morphism f : A ⟶ B is ccrEvalMap f.
This is just the functorial action of the target polynomial.
-/
def PolyPresentation.toSetoidCopresheafMapFun
    (X : PolyPresentation.{u, v, w} D) {A B : D} (f : A ⟶ B) :
    (X.toSetoidBundleAt A).carrier → (X.toSetoidBundleAt B).carrier :=
  ccrEvalMap f

/--
The coequalizer relation is preserved by the map ccrEvalMap.
If (y₁, y₂) are related via x at A, then (ccrEvalMap f y₁, ccrEvalMap f y₂)
are related via ccrEvalMap f x at B.
-/
theorem PolyPresentation.coeqRelAt_map
    (X : PolyPresentation.{u, v, w} D) {A B : D} (f : A ⟶ B)
    {y₁ y₂ : ccrEval X.tgt A} (h : X.coeqRelAt A y₁ y₂) :
    X.coeqRelAt B (ccrEvalMap f y₁) (ccrEvalMap f y₂) := by
  obtain ⟨x, hfst, hsnd⟩ := h
  use ccrEvalMap f x
  constructor
  · rw [← hfst]
    exact congrFun (ccrToFunctorMapApp_natural X.fst f) x
  · rw [← hsnd]
    exact congrFun (ccrToFunctorMapApp_natural X.snd f) x

/--
The equivalence relation generated by the coequalizer relation is also
preserved by ccrEvalMap.
-/
theorem PolyPresentation.coeqSetoidAt_map
    (X : PolyPresentation.{u, v, w} D) {A B : D} (f : A ⟶ B)
    {y₁ y₂ : ccrEval X.tgt A}
    (h : (X.coeqSetoidAt A).r y₁ y₂) :
    (X.coeqSetoidAt B).r (ccrEvalMap f y₁) (ccrEvalMap f y₂) := by
  unfold coeqSetoidAt at h ⊢
  simp only [Relation.EqvGen.setoid] at h ⊢
  induction h with
  | rel _ _ hr => exact Relation.EqvGen.rel _ _ (X.coeqRelAt_map f hr)
  | refl _ => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2

/--
The setoid morphism induced by a morphism f : A ⟶ B.
-/
def PolyPresentation.toSetoidCopresheafMap
    (X : PolyPresentation.{u, v, w} D) {A B : D} (f : A ⟶ B) :
    X.toSetoidBundleAt A ⟶ X.toSetoidBundleAt B where
  toFun := X.toSetoidCopresheafMapFun f
  map_rel := fun _ _ h => X.coeqSetoidAt_map f h

/--
The identity morphism maps to the identity setoid morphism.
-/
theorem PolyPresentation.toSetoidCopresheafMap_id
    (X : PolyPresentation.{u, v, w} D) (A : D) :
    X.toSetoidCopresheafMap (𝟙 A) = 𝟙 (X.toSetoidBundleAt A) := by
  apply SetoidHom.ext
  intro ⟨i, h⟩
  simp only [toSetoidCopresheafMap, toSetoidCopresheafMapFun, ccrEvalMap,
    Category.comp_id]
  rfl

/--
Composition is preserved by toSetoidCopresheafMap.
-/
theorem PolyPresentation.toSetoidCopresheafMap_comp
    (X : PolyPresentation.{u, v, w} D) {A B C : D} (f : A ⟶ B) (g : B ⟶ C) :
    X.toSetoidCopresheafMap (f ≫ g) =
    X.toSetoidCopresheafMap f ≫ X.toSetoidCopresheafMap g := by
  apply SetoidHom.ext
  intro ⟨i, h⟩
  change (⟨i, h ≫ f ≫ g⟩ : ccrEval X.tgt C) =
       (X.toSetoidCopresheafMap g).toFun ((X.toSetoidCopresheafMap f).toFun ⟨i, h⟩)
  simp only [toSetoidCopresheafMap, toSetoidCopresheafMapFun, ccrEvalMap,
    Category.assoc]

/--
The setoid-valued copresheaf represented by a polynomial presentation.
For a presentation (P, Q, α, β), this gives a functor D ⥤ SetoidBundle where:
- obj A is (ccrEval Q A, equivalence relation from coequalizer)
- map f preserves the equivalence relation
-/
def PolyPresentation.toSetoidCopresheaf
    (X : PolyPresentation.{u, v, w} D) : D ⥤ SetoidBundle where
  obj := X.toSetoidBundleAt
  map := X.toSetoidCopresheafMap
  map_id := X.toSetoidCopresheafMap_id
  map_comp := X.toSetoidCopresheafMap_comp

end SetoidEvaluation

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

/-! ## Quotient Category Structure

The original `PolyPresentation.Hom` requires both `srcHom` and `tgtHom`, but
the evaluation functor only depends on `tgtHom`. This makes the evaluation
functor not faithful.

We define a wrapper type `PolyPresentationQ` with a new morphism type where
only `tgtHom` is data, with a propositional condition that it "respects
coequalization". This condition says that composing with the target's
coequalizer projection coequalizes the source's parallel pair.
-/

section QuotientCategory

variable {D}

/--
The condition that a morphism `f : X.tgt ⟶ Y.tgt` between target polynomials
"respects coequalization": when composed with Y's coequalizer projection,
the result coequalizes X's parallel pair.

This is equivalent to saying that `ccrToFunctorMap f ≫ Y.toCopresheafπ` factors
through X's coequalizer.
-/
def PolyPresentation.RespectsCoequalization
    (X Y : PolyPresentation.{u, v, w} D)
    (f : X.tgt ⟶ Y.tgt) : Prop :=
  ccrToFunctorMap X.fst ≫ ccrToFunctorMap f ≫ Y.toCopresheafπ =
  ccrToFunctorMap X.snd ≫ ccrToFunctorMap f ≫ Y.toCopresheafπ

namespace PolyPresentation.RespectsCoequalization

variable {X Y Z : PolyPresentation.{u, v, w} D}

/--
The identity morphism respects coequalization.
-/
theorem id (X : PolyPresentation.{u, v, w} D) :
    X.RespectsCoequalization X (𝟙 X.tgt) := by
  unfold RespectsCoequalization
  simp only [ccrToFunctorMap_id]
  exact X.toCopresheaf_condition

/--
Composition preserves the respects coequalization property.
-/
theorem comp {f : X.tgt ⟶ Y.tgt} {g : Y.tgt ⟶ Z.tgt}
    (hf : X.RespectsCoequalization Y f) (hg : Y.RespectsCoequalization Z g) :
    X.RespectsCoequalization Z (f ≫ g) := by
  unfold RespectsCoequalization at *
  simp only [ccrToFunctorMap_comp]
  -- The induced map from Y's coequalizer to Z's coequalizer
  let induced := CoequalizerData.desc (ccrToFunctorMap Y.fst) (ccrToFunctorMap Y.snd)
    (ccrToFunctorMap g ≫ Z.toCopresheafπ) hg
  have fac : Y.toCopresheafπ ≫ induced = ccrToFunctorMap g ≫ Z.toCopresheafπ :=
    CoequalizerData.fac _ _ _ _
  calc ccrToFunctorMap X.fst ≫ ccrToFunctorMap f ≫ ccrToFunctorMap g ≫ Z.toCopresheafπ
    _ = ccrToFunctorMap X.fst ≫ ccrToFunctorMap f ≫ (Y.toCopresheafπ ≫ induced) := by
        simp only [fac]
    _ = (ccrToFunctorMap X.fst ≫ ccrToFunctorMap f ≫ Y.toCopresheafπ) ≫ induced := by
        simp only [Category.assoc]
    _ = (ccrToFunctorMap X.snd ≫ ccrToFunctorMap f ≫ Y.toCopresheafπ) ≫ induced := by
        rw [hf]
    _ = ccrToFunctorMap X.snd ≫ ccrToFunctorMap f ≫ (Y.toCopresheafπ ≫ induced) := by
        simp only [Category.assoc]
    _ = ccrToFunctorMap X.snd ≫ ccrToFunctorMap f ≫ ccrToFunctorMap g ≫ Z.toCopresheafπ := by
        simp only [fac]

end PolyPresentation.RespectsCoequalization

/--
Any morphism in `PolyPresentation.Hom` respects coequalization.
This follows from the commutativity conditions `fst_comm` and `snd_comm`.
-/
theorem PolyPresentation.Hom.respectsCoequalization
    {X Y : PolyPresentation.{u, v, w} D} (f : Hom X Y) :
    X.RespectsCoequalization Y f.tgtHom := by
  unfold PolyPresentation.RespectsCoequalization
  calc ccrToFunctorMap X.fst ≫ ccrToFunctorMap f.tgtHom ≫ Y.toCopresheafπ
      = (ccrToFunctorMap X.fst ≫ ccrToFunctorMap f.tgtHom) ≫ Y.toCopresheafπ := by
          simp only [Category.assoc]
    _ = ccrToFunctorMap (X.fst ≫ f.tgtHom) ≫ Y.toCopresheafπ := by
          simp only [ccrToFunctorMap_comp]
    _ = ccrToFunctorMap (f.srcHom ≫ Y.fst) ≫ Y.toCopresheafπ := by
          rw [f.fst_comm]
    _ = (ccrToFunctorMap f.srcHom ≫ ccrToFunctorMap Y.fst) ≫ Y.toCopresheafπ := by
          simp only [ccrToFunctorMap_comp]
    _ = ccrToFunctorMap f.srcHom ≫ (ccrToFunctorMap Y.fst ≫ Y.toCopresheafπ) := by
          simp only [Category.assoc]
    _ = ccrToFunctorMap f.srcHom ≫ (ccrToFunctorMap Y.snd ≫ Y.toCopresheafπ) := by
          rw [Y.toCopresheaf_condition]
    _ = (ccrToFunctorMap f.srcHom ≫ ccrToFunctorMap Y.snd) ≫ Y.toCopresheafπ := by
          simp only [Category.assoc]
    _ = ccrToFunctorMap (f.srcHom ≫ Y.snd) ≫ Y.toCopresheafπ := by
          simp only [ccrToFunctorMap_comp]
    _ = ccrToFunctorMap (X.snd ≫ f.tgtHom) ≫ Y.toCopresheafπ := by
          rw [f.snd_comm]
    _ = (ccrToFunctorMap X.snd ≫ ccrToFunctorMap f.tgtHom) ≫ Y.toCopresheafπ := by
          simp only [ccrToFunctorMap_comp]
    _ = ccrToFunctorMap X.snd ≫ ccrToFunctorMap f.tgtHom ≫ Y.toCopresheafπ := by
          simp only [Category.assoc]

/--
A wrapper type for polynomial presentations with the quotient category structure.

This is the same underlying data as `PolyPresentation`, but with a different
category structure where morphisms only track the target component.
-/
def PolyPresentationQ.{u', v', w'} (D' : Type u') [Category.{v'} D'] :=
  PolyPresentation.{u', v', w'} D'

variable (D) in
/-- Coerce a polynomial presentation to the quotient category type. -/
def PolyPresentation.toQ (X : PolyPresentation.{u, v, w} D) : PolyPresentationQ.{u, v, w} D := X

variable (D) in
/-- Coerce a quotient category object back to a polynomial presentation. -/
def PolyPresentationQ.toPres (X : PolyPresentationQ.{u, v, w} D) : PolyPresentation.{u, v, w} D := X

/--
A morphism in the quotient category of polynomial presentations.

Unlike `PolyPresentation.Hom`, this has only the target component `tgtHom`,
with a propositional condition that it respects coequalization.
-/
structure PolyPresentationQ.Hom (X Y : PolyPresentationQ.{u, v, w} D) where
  /-- The morphism on target polynomial functors -/
  tgtHom : (PolyPresentationQ.toPres D X).tgt ⟶ (PolyPresentationQ.toPres D Y).tgt
  /-- The morphism respects the coequalization structure -/
  respects : (PolyPresentationQ.toPres D X).RespectsCoequalization
    (PolyPresentationQ.toPres D Y) tgtHom

/--
Convert a `PolyPresentation.Hom` to a `PolyPresentationQ.Hom`.
This forgets the source component and uses the fact that any morphism
of polynomial presentations respects coequalization.
-/
def PolyPresentation.Hom.toQHom {X Y : PolyPresentation.{u, v, w} D}
    (f : PolyPresentation.Hom X Y) :
    PolyPresentationQ.Hom X.toQ Y.toQ where
  tgtHom := f.tgtHom
  respects := f.respectsCoequalization

namespace PolyPresentationQ.Hom

variable {X Y Z : PolyPresentationQ.{u, v, w} D}

/--
Extensionality for quotient presentation morphisms: two morphisms are equal
iff their `tgtHom` components are equal. The `respects` field is a proposition,
so it's proof-irrelevant.
-/
@[ext]
theorem ext (f g : PolyPresentationQ.Hom X Y) (h : f.tgtHom = g.tgtHom) :
    f = g := by
  cases f
  cases g
  simp only [mk.injEq]
  exact h

/-- The identity morphism in the quotient category. -/
def id (X : PolyPresentationQ.{u, v, w} D) : PolyPresentationQ.Hom X X where
  tgtHom := 𝟙 (PolyPresentationQ.toPres D X).tgt
  respects := PolyPresentation.RespectsCoequalization.id (PolyPresentationQ.toPres D X)

/-- Composition of morphisms in the quotient category. -/
def comp (f : PolyPresentationQ.Hom X Y) (g : PolyPresentationQ.Hom Y Z) :
    PolyPresentationQ.Hom X Z where
  tgtHom := f.tgtHom ≫ g.tgtHom
  respects := PolyPresentation.RespectsCoequalization.comp f.respects g.respects

@[simp]
theorem id_tgtHom (X : PolyPresentationQ.{u, v, w} D) :
    (id X).tgtHom = 𝟙 (PolyPresentationQ.toPres D X).tgt := rfl

@[simp]
theorem comp_tgtHom (f : PolyPresentationQ.Hom X Y) (g : PolyPresentationQ.Hom Y Z) :
    (comp f g).tgtHom = f.tgtHom ≫ g.tgtHom := rfl

end PolyPresentationQ.Hom

/-- The quotient category structure on polynomial presentations. -/
instance PolyPresentationQ.category : Category (PolyPresentationQ.{u, v, w} D) where
  Hom := PolyPresentationQ.Hom
  id := PolyPresentationQ.Hom.id
  comp := PolyPresentationQ.Hom.comp
  id_comp f := by
    apply PolyPresentationQ.Hom.ext
    exact ccrHom_ext _ _ rfl (by simp)
  comp_id f := by
    apply PolyPresentationQ.Hom.ext
    exact ccrHom_ext _ _ rfl (by simp)
  assoc f g h := by
    apply PolyPresentationQ.Hom.ext
    exact ccrHom_ext _ _ rfl (by simp [Category.assoc])

/-- Category identity tgtHom unfolds to CCR identity. -/
@[simp]
theorem PolyPresentationQ.Hom.id_tgtHom' (X : PolyPresentationQ.{u, v, w} D) :
    (𝟙 X : X ⟶ X).tgtHom = 𝟙 (PolyPresentationQ.toPres D X).tgt := rfl

/-! ### Evaluation Functor for PolyPresentationQ

The evaluation functor maps each presentation to its coequalizer, and each
morphism to the induced map on coequalizers.
-/

/--
The induced map on coequalizers for a morphism in PolyPresentationQ.
Since f.respects says that `ccrToFunctorMap f.tgtHom ≫ Y.toCopresheafπ`
coequalizes X's parallel pair, the universal property gives a unique
factorization through X's coequalizer.
-/
def PolyPresentationQ.Hom.toInducedMap
    {X Y : PolyPresentationQ.{u, v, w} D} (f : X ⟶ Y) :
    (toPres D X).toCopresheaf ⟶ (toPres D Y).toCopresheaf :=
  CoequalizerData.desc
    (ccrToFunctorMap (toPres D X).fst)
    (ccrToFunctorMap (toPres D X).snd)
    (ccrToFunctorMap f.tgtHom ≫ (toPres D Y).toCopresheafπ)
    f.respects

/--
The factorization property: π ≫ toInducedMap = tgtHom ≫ π.
-/
theorem PolyPresentationQ.Hom.toInducedMap_fac
    {X Y : PolyPresentationQ.{u, v, w} D} (f : X ⟶ Y) :
    (toPres D X).toCopresheafπ ≫ f.toInducedMap =
    ccrToFunctorMap f.tgtHom ≫ (toPres D Y).toCopresheafπ :=
  CoequalizerData.fac _ _ _ _

/--
The identity morphism induces the identity on coequalizers.
-/
theorem PolyPresentationQ.Hom.toInducedMap_id
    (X : PolyPresentationQ.{u, v, w} D) :
    (𝟙 X : X ⟶ X).toInducedMap = 𝟙 (PolyPresentationQ.toPres D X).toCopresheaf := by
  symm
  apply CoequalizerData.uniq
  simp only [id_tgtHom', ccrToFunctorMap_id, Category.id_comp]
  rfl

/--
Composition of morphisms induces composition on coequalizers.
-/
theorem PolyPresentationQ.Hom.toInducedMap_comp
    {X Y Z : PolyPresentationQ.{u, v, w} D}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).toInducedMap = f.toInducedMap ≫ g.toInducedMap := by
  symm
  apply CoequalizerData.uniq
  calc (toPres D X).toCopresheafπ ≫ f.toInducedMap ≫ g.toInducedMap
      = ((toPres D X).toCopresheafπ ≫ f.toInducedMap) ≫ g.toInducedMap := by
          rw [Category.assoc]
    _ = (ccrToFunctorMap f.tgtHom ≫ (toPres D Y).toCopresheafπ) ≫ g.toInducedMap := by
          rw [toInducedMap_fac]
    _ = ccrToFunctorMap f.tgtHom ≫ ((toPres D Y).toCopresheafπ ≫ g.toInducedMap) := by
          rw [Category.assoc]
    _ = ccrToFunctorMap f.tgtHom ≫
          (ccrToFunctorMap g.tgtHom ≫ (toPres D Z).toCopresheafπ) := by
          rw [toInducedMap_fac]
    _ = (ccrToFunctorMap f.tgtHom ≫ ccrToFunctorMap g.tgtHom) ≫
          (toPres D Z).toCopresheafπ := by
          rw [← Category.assoc]
    _ = ccrToFunctorMap (f.tgtHom ≫ g.tgtHom) ≫ (toPres D Z).toCopresheafπ := by
          rw [← ccrToFunctorMap_comp]
    _ = ccrToFunctorMap (f ≫ g).tgtHom ≫ (toPres D Z).toCopresheafπ := rfl

/--
The evaluation functor from the quotient category to copresheaves.
Maps a presentation to its coequalizer and a morphism to the induced map.
-/
@[simps]
def polyPresentationQEvalFunctor :
    PolyPresentationQ.{u, v, w} D ⥤ (D ⥤ Type (max w v)) where
  obj X := (PolyPresentationQ.toPres D X).toCopresheaf
  map f := f.toInducedMap
  map_id := PolyPresentationQ.Hom.toInducedMap_id
  map_comp := PolyPresentationQ.Hom.toInducedMap_comp

/-!
### Non-Faithfulness of the Evaluation Functor

The evaluation functor `polyPresentationQEvalFunctor` is NOT faithful in general.

Given morphisms `f, g : X ⟶ Y` in `PolyPresentationQ`, if `f.toInducedMap = g.toInducedMap`,
we can deduce that:
  `ccrToFunctorMap f.tgtHom ≫ Y.toCopresheafπ = ccrToFunctorMap g.tgtHom ≫ Y.toCopresheafπ`

To conclude `f.tgtHom = g.tgtHom`, we would need to cancel `Y.toCopresheafπ` on the right.
However, coequalizer projections are epimorphisms (can be cancelled on the left), not
monomorphisms (would need to be cancelled on the right). Two different morphisms into
`ccrToFunctor Y.tgt` can compose to the same map when followed by `Y.toCopresheafπ` if
their difference lies in the kernel of the coequalization.

This means `PolyPresentationQ` is not the correct formulation for an equivalence with
copresheaves. A proper equivalence would require either:
1. Working with a localization or quotient that identifies morphisms inducing the same
   map on coequalizers
2. Using a different category structure where morphisms are defined as maps between
   coequalizers rather than as `tgtHom` with a `respects` condition
-/

/-! ### Localized Category (PolyPresentationLoc)

The localized category quotients morphisms by the relation "induces the same map
on coequalizers". This makes the evaluation functor faithful by construction.

The equivalence relation is: `f ≈ g iff f.toInducedMap = g.toInducedMap`.
-/

/--
The equivalence relation on morphisms: two morphisms are equivalent iff they
induce the same map on coequalizers.
-/
def PolyPresentationQ.Hom.equiv
    {X Y : PolyPresentationQ.{u, v, w} D}
    (f g : PolyPresentationQ.Hom X Y) : Prop :=
  f.toInducedMap = g.toInducedMap

/-- Reflexivity of the equivalence relation. -/
theorem PolyPresentationQ.Hom.equiv_refl
    {X Y : PolyPresentationQ.{u, v, w} D}
    (f : PolyPresentationQ.Hom X Y) : f.equiv f :=
  rfl

/-- Symmetry of the equivalence relation. -/
theorem PolyPresentationQ.Hom.equiv_symm
    {X Y : PolyPresentationQ.{u, v, w} D}
    {f g : PolyPresentationQ.Hom X Y}
    (h : f.equiv g) : g.equiv f :=
  h.symm

/-- Transitivity of the equivalence relation. -/
theorem PolyPresentationQ.Hom.equiv_trans
    {X Y : PolyPresentationQ.{u, v, w} D}
    {f g h : PolyPresentationQ.Hom X Y}
    (hfg : f.equiv g) (hgh : g.equiv h) : f.equiv h :=
  hfg.trans hgh

/--
The Setoid instance for morphisms in PolyPresentationQ.
-/
def PolyPresentationQ.Hom.setoidInst
    (X Y : PolyPresentationQ.{u, v, w} D) :
    Setoid (PolyPresentationQ.Hom X Y) where
  r := equiv
  iseqv := {
    refl := equiv_refl
    symm := equiv_symm
    trans := equiv_trans
  }

/--
Composition respects the equivalence relation: if f₁ ≈ f₂ and g₁ ≈ g₂,
then (f₁ ≫ g₁) ≈ (f₂ ≫ g₂).
-/
theorem PolyPresentationQ.Hom.equiv_comp
    {X Y Z : PolyPresentationQ.{u, v, w} D}
    {f₁ f₂ : X ⟶ Y} {g₁ g₂ : Y ⟶ Z}
    (hf : f₁.equiv f₂) (hg : g₁.equiv g₂) :
    (f₁ ≫ g₁).equiv (f₂ ≫ g₂) := by
  unfold equiv at *
  simp only [PolyPresentationQ.Hom.toInducedMap_comp]
  rw [hf, hg]

/--
The localized presentation category. Objects are the same as PolyPresentation,
but morphisms are equivalence classes of PolyPresentationQ.Hom under the
relation "induces same map on coequalizers".
-/
@[ext]
structure PolyPresentationLoc.{u', v', w'} (D' : Type u') [Category.{v'} D'] where
  /-- The underlying presentation -/
  toPres : PolyPresentation.{u', v', w'} D'

namespace PolyPresentationLoc

variable {D : Type u} [Category.{v} D]

/-- Convert a presentation to the localized category. -/
def ofPres (X : PolyPresentation.{u, v, w} D) : PolyPresentationLoc.{u, v, w} D :=
  ⟨X⟩

/-- Helper: the PolyPresentationQ version of an object. -/
abbrev toQ (X : PolyPresentationLoc.{u, v, w} D) : PolyPresentationQ.{u, v, w} D :=
  X.toPres.toQ

/--
Morphisms in the localized category are equivalence classes of
PolyPresentationQ.Hom under the "same induced map" relation.
Uses `Quot` with the raw `equiv` relation rather than `Quotient` with a
`Setoid` instance to avoid typeclass resolution issues.
-/
def Hom (X Y : PolyPresentationLoc.{u, v, w} D) : Type (max w v) :=
  Quot (fun (f g : PolyPresentationQ.Hom X.toQ Y.toQ) => f.equiv g)

/-- Create a morphism in the localized category from a PolyPresentationQ morphism. -/
def Hom.mk' {X Y : PolyPresentationLoc.{u, v, w} D}
    (f : PolyPresentationQ.Hom X.toQ Y.toQ) : Hom X Y :=
  Quot.mk _ f

/-- The equivalence relation used for localizing. -/
abbrev Hom.rel (X Y : PolyPresentationLoc.{u, v, w} D) :
    PolyPresentationQ.Hom X.toQ Y.toQ → PolyPresentationQ.Hom X.toQ Y.toQ → Prop :=
  fun f g => f.equiv g

/-- Composition of representatives. -/
private def Hom.compRep {X Y Z : PolyPresentationLoc.{u, v, w} D}
    (f : PolyPresentationQ.Hom X.toQ Y.toQ)
    (g : PolyPresentationQ.Hom Y.toQ Z.toQ) : Hom X Z :=
  Hom.mk' (X := X) (Y := Z) (PolyPresentationQ.Hom.comp f g)

/-- Composition respects the relation in the second argument. -/
private theorem Hom.compRep_resp_snd {X Y Z : PolyPresentationLoc.{u, v, w} D}
    (f : PolyPresentationQ.Hom X.toQ Y.toQ)
    (g₁ g₂ : PolyPresentationQ.Hom Y.toQ Z.toQ)
    (hg : g₁.equiv g₂) :
    Hom.compRep f g₁ = Hom.compRep f g₂ := by
  unfold compRep mk'
  apply Quot.sound
  exact PolyPresentationQ.Hom.equiv_comp (PolyPresentationQ.Hom.equiv_refl f) hg

/-- Lift composition over the second argument. -/
private def Hom.compLift2 {X Y Z : PolyPresentationLoc.{u, v, w} D}
    (f : PolyPresentationQ.Hom X.toQ Y.toQ) (g : Hom Y Z) : Hom X Z :=
  Quot.lift (Hom.compRep f) (Hom.compRep_resp_snd f) g

/-- Composition respects the relation in the first argument. -/
private theorem Hom.compLift2_resp_fst {X Y Z : PolyPresentationLoc.{u, v, w} D}
    (f₁ f₂ : PolyPresentationQ.Hom X.toQ Y.toQ) (hf : f₁.equiv f₂)
    (g : Hom Y Z) :
    Hom.compLift2 f₁ g = Hom.compLift2 f₂ g := by
  induction g using Quot.ind with
  | _ g' =>
    unfold compLift2 compRep mk'
    apply Quot.sound
    exact PolyPresentationQ.Hom.equiv_comp hf (PolyPresentationQ.Hom.equiv_refl g')

/-- Composition in the localized category. -/
def Hom.comp' {X Y Z : PolyPresentationLoc.{u, v, w} D}
    (f : Hom X Y) (g : Hom Y Z) : Hom X Z :=
  Quot.lift (fun f' => Hom.compLift2 f' g) (fun f₁ f₂ hf => Hom.compLift2_resp_fst f₁ f₂ hf g) f

/-- The identity morphism in the localized category. -/
def Hom.id' (X : PolyPresentationLoc.{u, v, w} D) : Hom X X :=
  Hom.mk' (PolyPresentationQ.Hom.id X.toQ)

/-- Identity composed on the left. -/
theorem Hom.id_comp' {X Y : PolyPresentationLoc.{u, v, w} D}
    (f : Hom X Y) : (Hom.id' X).comp' f = f := by
  induction f using Quot.ind with
  | _ f' =>
    unfold id' comp' compLift2 compRep mk'
    apply Quot.sound
    show ((PolyPresentationQ.Hom.id X.toQ).comp f').equiv f'
    unfold PolyPresentationQ.Hom.equiv PolyPresentationQ.Hom.toInducedMap
    simp only [PolyPresentationQ.Hom.comp_tgtHom, PolyPresentationQ.Hom.id_tgtHom,
      Category.id_comp]

/-- Identity composed on the right. -/
theorem Hom.comp_id' {X Y : PolyPresentationLoc.{u, v, w} D}
    (f : Hom X Y) : f.comp' (Hom.id' Y) = f := by
  induction f using Quot.ind with
  | _ f' =>
    unfold id' comp' compLift2 compRep mk'
    apply Quot.sound
    show (f'.comp (PolyPresentationQ.Hom.id Y.toQ)).equiv f'
    unfold PolyPresentationQ.Hom.equiv PolyPresentationQ.Hom.toInducedMap
    simp only [PolyPresentationQ.Hom.comp_tgtHom, PolyPresentationQ.Hom.id_tgtHom,
      Category.comp_id]

/-- Associativity of composition. -/
theorem Hom.comp_assoc' {W X Y Z : PolyPresentationLoc.{u, v, w} D}
    (f : Hom W X) (g : Hom X Y) (h : Hom Y Z) :
    (f.comp' g).comp' h = f.comp' (g.comp' h) := by
  induction f using Quot.ind with
  | _ f' =>
    induction g using Quot.ind with
    | _ g' =>
      induction h using Quot.ind with
      | _ h' =>
        unfold comp' compLift2 compRep mk'
        apply Quot.sound
        show ((f'.comp g').comp h').equiv (f'.comp (g'.comp h'))
        unfold PolyPresentationQ.Hom.equiv PolyPresentationQ.Hom.toInducedMap
        simp only [PolyPresentationQ.Hom.comp_tgtHom, Category.assoc]

/-- The localized category structure on polynomial presentations. -/
instance category : Category (PolyPresentationLoc.{u, v, w} D) where
  Hom := Hom
  id := Hom.id'
  comp := Hom.comp'
  id_comp := Hom.id_comp'
  comp_id := Hom.comp_id'
  assoc := Hom.comp_assoc'

/--
The induced map on coequalizers for a morphism in the localized category.
This is well-defined because equivalent morphisms induce the same map.
-/
def Hom.toInducedMap' {X Y : PolyPresentationLoc.{u, v, w} D} (f : Hom X Y) :
    X.toPres.toCopresheaf ⟶ Y.toPres.toCopresheaf :=
  Quot.lift
    (fun (f' : PolyPresentationQ.Hom X.toQ Y.toQ) => f'.toInducedMap)
    (fun _ _ h => h)
    f

/-- The identity morphism induces the identity map. -/
theorem Hom.toInducedMap_id' (X : PolyPresentationLoc.{u, v, w} D) :
    (Hom.id' X).toInducedMap' = 𝟙 X.toPres.toCopresheaf :=
  PolyPresentationQ.Hom.toInducedMap_id X.toQ

/-- Composition induces composition of maps. -/
theorem Hom.toInducedMap_comp' {X Y Z : PolyPresentationLoc.{u, v, w} D}
    (f : Hom X Y) (g : Hom Y Z) :
    (f.comp' g).toInducedMap' = f.toInducedMap' ≫ g.toInducedMap' := by
  induction f using Quot.ind with
  | _ f' =>
    induction g using Quot.ind with
    | _ g' =>
      unfold comp' compLift2 compRep mk' toInducedMap'
      exact PolyPresentationQ.Hom.toInducedMap_comp f' g'

end PolyPresentationLoc

/--
The evaluation functor from the localized category to copresheaves.
This maps a presentation to its coequalizer and a morphism equivalence class
to the induced map (which is the same for all representatives).
-/
def polyPresentationLocEvalFunctor :
    PolyPresentationLoc.{u, v, w} D ⥤ (D ⥤ Type (max w v)) where
  obj X := X.toPres.toCopresheaf
  map f := PolyPresentationLoc.Hom.toInducedMap' f
  map_id X := PolyPresentationLoc.Hom.toInducedMap_id' X
  map_comp f g := PolyPresentationLoc.Hom.toInducedMap_comp' f g

/--
The evaluation functor on the localized category is faithful.
This is automatic from the construction: two morphisms are equal iff their
representatives are equivalent, which happens iff they induce the same map.
-/
theorem polyPresentationLocEvalFunctor_faithful :
    Functor.Faithful (polyPresentationLocEvalFunctor (D := D)) where
  map_injective {X Y} f g h := by
    change (f : PolyPresentationLoc.Hom X Y) = g
    induction f using Quot.ind with
    | _ f' =>
      induction g using Quot.ind with
      | _ g' =>
        apply Quot.sound
        simp only [polyPresentationLocEvalFunctor,
          PolyPresentationLoc.Hom.toInducedMap'] at h
        exact h

end QuotientCategory

end GebLean
