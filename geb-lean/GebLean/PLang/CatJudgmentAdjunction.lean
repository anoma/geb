import GebLean.PLang.CatJudgment
import GebLean.Utilities.Category
import GebLean.Utilities.Equalities
import GebLean.Utilities.OverCategoryEquiv
import GebLean.CatJudgmentAdjunction
import Mathlib.CategoryTheory.Category.Cat

/-!
# PLang Category-Copresheaf Adjunction

This file implements the adjunction between the category of small categories
(`Cat`) and the category of category-judgment copresheaves (`CatJudgCopr`).

The adjunction consists of:
- An embedding functor `PhiFunctor_PLang : Cat ⥤ CatJudgCopr` that sends a
  category to its associated category-judgment data
- A reflection functor `LFunctor_PLang : CatJudgCopr ⥤ Cat` that sends
  category-judgment data to the free category on its quiver, quotiented by
  identity and composition relations

## Main definitions

### Embedding Functor Phi

- `catToCatJudgCopr`: Convert a category to a CatJudgCopr
- `catFunToCatJudgNatTrans`: Convert a functor to a CatJudgNatTrans
- `PhiFunctor_PLang`: The embedding functor Cat ⥤ CatJudgCopr

## References

See `docs/plang-category-judgments-old.md` for mathematical background.
-/

namespace GebLean

namespace PLang

open CategoryTheory

universe v u

/-! ## Bundled Morphism Type

For a category C, we bundle morphisms with their domain and codomain. -/

/-- Bundled morphism in a category: a triple (a, b, f) where f : a ⟶ b. -/
def BundledHom (C : Type u) [Category.{v} C] : Type (max u v) :=
  Σ (a b : C), (a ⟶ b)

/-- The domain of a bundled morphism. -/
def BundledHom.dom {C : Type u} [Category.{v} C] (m : BundledHom C) : C := m.1

/-- The codomain of a bundled morphism. -/
def BundledHom.cod {C : Type u} [Category.{v} C] (m : BundledHom C) : C := m.2.1

/-- The underlying morphism of a bundled morphism. -/
def BundledHom.hom {C : Type u} [Category.{v} C] (m : BundledHom C) :
    m.dom ⟶ m.cod := m.2.2

/-- Construct a bundled morphism from domain, codomain, and morphism. -/
def BundledHom.mk {C : Type u} [Category.{v} C] (a b : C) (f : a ⟶ b) :
    BundledHom C := ⟨a, b, f⟩

/-- Extensionality for BundledHom with heterogeneous morphism equality.

Given equality of domains, equality of codomains, and heterogeneous equality
of morphisms (accounting for the type change), the bundled morphisms are equal. -/
theorem BundledHom.ext {C : Type u} [Category.{v} C]
    {a₁ a₂ b₁ b₂ : C} (f₁ : a₁ ⟶ b₁) (f₂ : a₂ ⟶ b₂)
    (ha : a₁ = a₂) (hb : b₁ = b₂) (hf : f₁ ≍ f₂) :
    BundledHom.mk a₁ b₁ f₁ = BundledHom.mk a₂ b₂ f₂ := by
  cases ha
  cases hb
  cases eq_of_heq hf
  rfl

/-- From an equality of BundledHom values, extract the relationship between
.hom components via eqToHom transports.

Given `m₁ = m₂` for BundledHom values, the .hom of m₁ equals the .hom of m₂
conjugated by eqToHom transports accounting for the domain/codomain differences. -/
theorem BundledHom.hom_eq_of_eq {C : Type u} [Category.{v} C]
    {m₁ m₂ : BundledHom C} (h : m₁ = m₂) :
    m₁.hom = eqToHom (congrArg BundledHom.dom h) ≫ m₂.hom ≫
      eqToHom (congrArg BundledHom.cod h).symm := by
  cases h
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

/-! ## Composable Pair Type

For a category C, we bundle composable pairs of morphisms. -/

/-- Composable pair in a category: (a, b, c, f, g) where f : a ⟶ b and g : b ⟶ c. -/
def ComposablePair (C : Type u) [Category.{v} C] : Type (max u v) :=
  Σ (a b c : C), (a ⟶ b) × (b ⟶ c)

/-- The source object of a composable pair. -/
def ComposablePair.src {C : Type u} [Category.{v} C]
    (p : ComposablePair C) : C := p.1

/-- The middle object of a composable pair. -/
def ComposablePair.mid {C : Type u} [Category.{v} C]
    (p : ComposablePair C) : C := p.2.1

/-- The target object of a composable pair. -/
def ComposablePair.tgt {C : Type u} [Category.{v} C]
    (p : ComposablePair C) : C := p.2.2.1

/-- The first (right) morphism of a composable pair. -/
def ComposablePair.fstMor {C : Type u} [Category.{v} C]
    (p : ComposablePair C) : p.src ⟶ p.mid := p.2.2.2.1

/-- The second (left) morphism of a composable pair. -/
def ComposablePair.sndMor {C : Type u} [Category.{v} C]
    (p : ComposablePair C) : p.mid ⟶ p.tgt := p.2.2.2.2

/-- The right morphism as a bundled morphism. -/
def ComposablePair.right {C : Type u} [Category.{v} C]
    (p : ComposablePair C) : BundledHom C :=
  BundledHom.mk p.src p.mid p.fstMor

/-- The left morphism as a bundled morphism. -/
def ComposablePair.left {C : Type u} [Category.{v} C]
    (p : ComposablePair C) : BundledHom C :=
  BundledHom.mk p.mid p.tgt p.sndMor

/-- The composite morphism as a bundled morphism. -/
def ComposablePair.composite {C : Type u} [Category.{v} C]
    (p : ComposablePair C) : BundledHom C :=
  BundledHom.mk p.src p.tgt (p.fstMor ≫ p.sndMor)

/-- Construct a composable pair. -/
def ComposablePair.mk {C : Type u} [Category.{v} C]
    (a b c : C) (f : a ⟶ b) (g : b ⟶ c) : ComposablePair C :=
  ⟨a, b, c, f, g⟩

/-! ## Embedding: Category to CatJudgCopr

We construct a CatJudgCopr from a category by bundling morphisms and
composable pairs.

Universe note: CatJudgObjMor.{u, v, w, x} contains CatJudgObj.{u+1, v+1, w+1, x+1},
so `.obj : Type u`, `.mor : Type v`, etc. For a category C : Type u with
Category.{v} C, we use CatJudgObjMor.{u, max u v, u, max u v}. -/

section CatToCatJudgCopr

variable (C : Type u) [Category.{v} C]

/-- Domain function for bundled morphisms. -/
def catToBundledDom : BundledHom C → C := BundledHom.dom

/-- Codomain function for bundled morphisms. -/
def catToBundledCod : BundledHom C → C := BundledHom.cod

/-- Identity morphism function: maps each object to its identity. -/
def catToIdMor : C → BundledHom C := fun a => BundledHom.mk a a (𝟙 a)

/-- Left morphism projection from composable pairs. -/
def catToLeft : ComposablePair C → BundledHom C := ComposablePair.left

/-- Right morphism projection from composable pairs. -/
def catToRight : ComposablePair C → BundledHom C := ComposablePair.right

/-- Composite morphism projection from composable pairs. -/
def catToComposite : ComposablePair C → BundledHom C := ComposablePair.composite

/-- The category judgment object data for a category C.

This uses shifted universe levels: CatJudgObj.{u+1, (max u v)+1, u+1, (max u v)+1}
so that the resulting .obj : Sort (u+1) = Type u matches C : Type u. -/
def catToCatJudgObj : Obj.CatJudgObj.{u + 1, (max u v) + 1, u + 1, (max u v) + 1} :=
  ((C, BundledHom C), (C, ComposablePair C))

/-- The category judgment morphism data (functions) for a category C. -/
def catToCatJudgMor :
    Obj.CatJudgMor.{u, max u v, u, max u v} (catToCatJudgObj C) :=
  ((catToBundledDom C, catToBundledCod C), catToIdMor C,
   (catToLeft C, catToRight C, catToComposite C))

/-- The bundled category judgment object-morphism data. -/
def catToCatJudgObjMor : Obj.CatJudgObjMor.{u, max u v, u, max u v} :=
  ⟨catToCatJudgObj C, catToCatJudgMor C⟩

/-- Identity morphisms are endomorphisms (domain = codomain). -/
theorem catToIdEndo :
    Obj.ObjMorIdObjMorEndo (catToCatJudgObjMor C).toObjMorIdObjMor := by
  unfold Obj.ObjMorIdObjMorEndo catToCatJudgObjMor catToCatJudgMor catToCatJudgObj
  funext a
  rfl

/-- Composable pairs have matching middle object. -/
theorem catToCompMatch :
    Obj.ObjMorCompObjMorMatch (catToCatJudgObjMor C).toObjMorCompObjMor := by
  unfold Obj.ObjMorCompObjMorMatch catToCatJudgObjMor catToCatJudgMor catToCatJudgObj
  funext p
  rfl

/-- Domain of composite equals domain of right morphism. -/
theorem catToCompDom :
    Obj.ObjMorCompObjMorCompDom (catToCatJudgObjMor C).toObjMorCompObjMor := by
  unfold Obj.ObjMorCompObjMorCompDom catToCatJudgObjMor catToCatJudgMor catToCatJudgObj
  funext p
  rfl

/-- Codomain of composite equals codomain of left morphism. -/
theorem catToCompCod :
    Obj.ObjMorCompObjMorCompCod (catToCatJudgObjMor C).toObjMorCompObjMor := by
  unfold Obj.ObjMorCompObjMorCompCod catToCatJudgObjMor catToCatJudgMor catToCatJudgObj
  funext p
  rfl

/-- The composition conditions for a category. -/
theorem catToCompCond :
    Obj.ObjMorCompObjMorCond (catToCatJudgObjMor C).toObjMorCompObjMor :=
  ⟨catToCompMatch C, catToCompDom C, catToCompCod C⟩

/-- The full conditions for a category judgment. -/
theorem catToCatJudgCond : Obj.CatJudgObjMorCond (catToCatJudgObjMor C) :=
  ⟨catToIdEndo C, catToCompCond C⟩

/-- Convert a category to a CatJudgCopr.

For a category `C : Type u` with `Category.{v} C`, this produces a
`CatJudgCopr.{u, max u v, u, max u v}` where:
- Objects type = C : Type u
- Morphisms type = bundled morphisms (Σ (a b : C), a ⟶ b) : Type (max u v)
- Identity type = C : Type u (each object witnesses its identity)
- Composition type = composable pairs : Type (max u v) -/
def catToCatJudgCopr : Obj.CatJudgCopr.{u, max u v, u, max u v} :=
  ⟨catToCatJudgObjMor C, catToCatJudgCond C⟩

end CatToCatJudgCopr

/-! ## Functoriality: Functor to CatJudgNatTrans

Given a functor F : C ⥤ D, we construct a natural transformation between
their CatJudgCopr representations. -/

section FunctorToCatJudgNatTrans

variable {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
variable (F : C ⥤ D)

/-- Map bundled morphisms through a functor. -/
def functorMapBundledHom : BundledHom C → BundledHom D :=
  fun m => BundledHom.mk (F.obj m.dom) (F.obj m.cod) (F.map m.hom)

/-- Map composable pairs through a functor. -/
def functorMapComposablePair : ComposablePair C → ComposablePair D :=
  fun p => ComposablePair.mk (F.obj p.src) (F.obj p.mid) (F.obj p.tgt)
    (F.map p.fstMor) (F.map p.sndMor)

/-- The full CatJudgMap for a functor.

The map consists of:
- objMorMap: (F.obj, functorMapBundledHom F)
- idCompMap: (F.obj, functorMapComposablePair F) -/
def functorToCatJudgMap :
    Mor.CatJudgMap (catToCatJudgCopr C) (catToCatJudgCopr D) :=
  ((F.obj, functorMapBundledHom F), (F.obj, functorMapComposablePair F))

/-- Domain naturality: F preserves domains. -/
theorem functorNaturalityDom :
    Mor.CatJudgNaturalityDom (functorToCatJudgMap F) := by
  unfold Mor.CatJudgNaturalityDom functorToCatJudgMap catToCatJudgCopr
         catToCatJudgObjMor catToCatJudgMor catToCatJudgObj functorMapBundledHom
  funext m
  rfl

/-- Codomain naturality: F preserves codomains. -/
theorem functorNaturalityCod :
    Mor.CatJudgNaturalityCod (functorToCatJudgMap F) := by
  unfold Mor.CatJudgNaturalityCod functorToCatJudgMap catToCatJudgCopr
         catToCatJudgObjMor catToCatJudgMor catToCatJudgObj functorMapBundledHom
  funext m
  rfl

/-- Identity morphism naturality: F preserves identity morphisms. -/
theorem functorNaturalityIdMor :
    Mor.CatJudgNaturalityIdMor (functorToCatJudgMap F) := by
  unfold Mor.CatJudgNaturalityIdMor functorToCatJudgMap catToCatJudgCopr
         catToCatJudgObjMor catToCatJudgMor catToCatJudgObj catToIdMor
         functorMapBundledHom Mor.CatJudgMap.morMap Mor.ObjMorMap.morMap
         Obj.CatJudgCopr.idMor Obj.CatJudgObjMor.idMor Mor.CatJudgMap.idMap
         Mor.CatJudgMap.idCompMap BundledHom.dom BundledHom.cod BundledHom.hom
         BundledHom.mk
  funext a
  simp only [Function.comp_apply, F.map_id]

/-- Left morphism naturality: F preserves left projections. -/
theorem functorNaturalityLeft :
    Mor.CatJudgNaturalityLeft (functorToCatJudgMap F) := by
  unfold Mor.CatJudgNaturalityLeft functorToCatJudgMap catToCatJudgCopr
         catToCatJudgObjMor catToCatJudgMor catToCatJudgObj catToLeft
         functorMapBundledHom functorMapComposablePair
  funext p
  rfl

/-- Right morphism naturality: F preserves right projections. -/
theorem functorNaturalityRight :
    Mor.CatJudgNaturalityRight (functorToCatJudgMap F) := by
  unfold Mor.CatJudgNaturalityRight functorToCatJudgMap catToCatJudgCopr
         catToCatJudgObjMor catToCatJudgMor catToCatJudgObj catToRight
         functorMapBundledHom functorMapComposablePair
  funext p
  rfl

/-- Composite naturality: F preserves composites. -/
theorem functorNaturalityComposite :
    Mor.CatJudgNaturalityComposite (functorToCatJudgMap F) := by
  unfold Mor.CatJudgNaturalityComposite functorToCatJudgMap catToCatJudgCopr
         catToCatJudgObjMor catToCatJudgMor catToCatJudgObj catToComposite
         functorMapBundledHom functorMapComposablePair ComposablePair.composite
         Mor.CatJudgMap.morMap Mor.ObjMorMap.morMap Obj.CatJudgCopr.composite
         Obj.CatJudgObjMor.composite Mor.CatJudgMap.compMap
         Mor.CatJudgMap.idCompMap BundledHom.dom BundledHom.cod BundledHom.hom
         BundledHom.mk ComposablePair.mk ComposablePair.src ComposablePair.mid
         ComposablePair.tgt ComposablePair.fstMor ComposablePair.sndMor
  funext p
  simp only [Function.comp_apply, F.map_comp]

/-- All naturality conditions hold for a functor. -/
theorem functorNaturalityAll :
    Mor.CatJudgNaturalityAll (functorToCatJudgMap F) :=
  ⟨⟨functorNaturalityDom F, functorNaturalityCod F⟩,
   functorNaturalityIdMor F,
   ⟨functorNaturalityLeft F, functorNaturalityRight F, functorNaturalityComposite F⟩⟩

/-- Convert a functor to a CatJudgNatTrans between CatJudgCopr values. -/
def functorToCatJudgNatTrans :
    Mor.CatJudgNatTrans (catToCatJudgCopr C) (catToCatJudgCopr D) :=
  ⟨functorToCatJudgMap F, functorNaturalityAll F⟩

end FunctorToCatJudgNatTrans

/-! ## Functoriality: Identity and Composition

We prove that the mapping from functors to CatJudgNatTrans respects
identity and composition, making it a functor. -/

section Functoriality

variable (C : Type u) [Category.{v} C]
variable {D : Type u} [Category.{v} D]
variable {E : Type u} [Category.{v} E]

/-- Helper: reconstruction of BundledHom is identity. -/
theorem bundledHom_eta {C : Type u} [Category.{v} C] (m : BundledHom C) :
    BundledHom.mk m.dom m.cod m.hom = m := rfl

/-- Helper: reconstruction of ComposablePair is identity. -/
theorem composablePair_eta {C : Type u} [Category.{v} C] (p : ComposablePair C) :
    ComposablePair.mk p.src p.mid p.tgt p.fstMor p.sndMor = p := rfl

/-- The identity functor maps to the identity CatJudgNatTrans. -/
theorem functorToCatJudgNatTrans_id :
    functorToCatJudgNatTrans (𝟭 C) =
    PLang.Cat.CatJudgNatTrans.id (catToCatJudgCopr C) := by
  unfold functorToCatJudgNatTrans functorToCatJudgMap functorMapBundledHom
         functorMapComposablePair PLang.Cat.CatJudgNatTrans.id
         PLang.Cat.CatJudgMap.id
  congr 1

/-- Functor composition maps to CatJudgNatTrans composition. -/
theorem functorToCatJudgNatTrans_comp (F : C ⥤ D) (G : D ⥤ E) :
    functorToCatJudgNatTrans (F ⋙ G) =
    PLang.Cat.CatJudgNatTrans.comp (functorToCatJudgNatTrans F)
                                   (functorToCatJudgNatTrans G) := by
  unfold functorToCatJudgNatTrans functorToCatJudgMap functorMapBundledHom
         functorMapComposablePair PLang.Cat.CatJudgNatTrans.comp
         PLang.Cat.CatJudgMap.comp Cat.ObjMap.comp Mor.CatJudgNatTrans.map
         Mor.CatJudgMap.objMorMap Mor.ObjMorMap.objMap Mor.ObjMorMap.morMap
         Mor.CatJudgMap.idMap Mor.CatJudgMap.compMap Mor.CatJudgMap.idCompMap
  congr 1

end Functoriality

/-! ## The Embedding Functor Phi

We package the object and morphism mappings into a functor from Cat to CatJudgCopr.

Universe note: For `Cat.{v, u}` (categories `C : Type u` with `Category.{v} C`),
we produce `CatJudgCopr.{u, max u v, u, max u v}`. The category structure on
CatJudgCopr requires shifted universes, so we work with `Cat.{v+1, u+1}`. -/

section PhiFunctor

/-- The embedding functor from Cat to CatJudgCopr.

For a category `C : Type (u+1)` with `Category.{v+1} C`, this produces a
`CatJudgCopr.{u+1, max (u+1) (v+1), u+1, max (u+1) (v+1)}` with:
- Objects = C
- Morphisms = bundled morphisms of C
- Composition witnesses = composable pairs in C

The functor is faithful: distinct functors induce distinct natural transformations. -/
def PhiFunctor_PLang.{u', v'} : CategoryTheory.Cat.{v' + 1, u' + 1} ⥤
    Obj.CatJudgCopr.{u' + 1, (max (u' + 1) (v' + 1)), u' + 1, (max (u' + 1) (v' + 1))} where
  obj C := catToCatJudgCopr C.α
  map F := functorToCatJudgNatTrans F
  map_id C := by
    rw [CategoryTheory.Cat.id_eq_id]
    exact functorToCatJudgNatTrans_id C.α
  map_comp {X Y Z} F G := by
    rw [CategoryTheory.Cat.comp_eq_comp]
    exact functorToCatJudgNatTrans_comp X.α F G

end PhiFunctor

/-! ## Reflection: CatJudgCopr to Category

We construct a category from a CatJudgCopr by:
1. Extracting an OverQuiver from the obj/mor/dom/cod components
2. Building CategoryQuotientData from the identity and composition witnesses
3. Constructing FreeMor trees and quotienting by FreeMorEquiv

The resulting category has:
- Objects = s.obj
- Morphisms a → b = Quot (FreeMorEquiv between a and b)
- Identity and composition from FreeMor constructors -/

section LFunctor

universe u' v' w' x'

/-! ### OverQuiver extraction

Extract an OverQuiver from a CatJudgCopr using its object, morphism, domain,
and codomain components. -/

variable (s : Obj.CatJudgCopr.{u', v', w', x'})

/-- Extract an OverQuiver from a CatJudgCopr.

The quiver has:
- Objects = s.obj
- Morphisms = s.mor
- src = s.dom
- tgt = s.cod -/
def catJudgCoprToOverQuiver : OverQuiver.{v', u'} where
  Obj := s.obj
  MorType := s.mor
  src := s.dom
  tgt := s.cod

/-- The object that an identity witness is for.

From the endoProof, we know dom ∘ idMor = cod ∘ idMor, so either gives
the object. We use dom ∘ idMor. -/
def catJudgCoprIdObj : s.idType → s.obj := s.dom ∘ s.idMor

/-- The identity morphism is an endomorphism: its source equals the id object. -/
theorem catJudgCoprIdSrc (i : s.idType) :
    (catJudgCoprToOverQuiver s).src (s.idMor i) = catJudgCoprIdObj s i := by
  rfl

/-- The identity morphism is an endomorphism: its target equals the id object. -/
theorem catJudgCoprIdTgt (i : s.idType) :
    (catJudgCoprToOverQuiver s).tgt (s.idMor i) = catJudgCoprIdObj s i := by
  unfold catJudgCoprToOverQuiver catJudgCoprIdObj
  simp only [Function.comp_apply]
  have h := s.endoProof
  unfold Obj.ObjMorIdObjMorEndo at h
  exact (congrFun h i).symm

/-! ### Composition condition proofs

Convert function equalities from CatJudgCopr to pointwise equalities needed
by CategoryQuotientData. -/

/-- Composable morphisms: target of right equals source of left.

This is the pointwise version of compMatchProof. -/
theorem catJudgCoprCompMatch (c : s.compType) :
    (catJudgCoprToOverQuiver s).tgt (s.right c) =
    (catJudgCoprToOverQuiver s).src (s.left c) := by
  have h := s.compMatchProof
  unfold Obj.ObjMorCompObjMorMatch at h
  exact congrFun h c

/-- Domain of composite equals domain of right morphism. -/
theorem catJudgCoprCompDom (c : s.compType) :
    (catJudgCoprToOverQuiver s).src (s.composite c) =
    (catJudgCoprToOverQuiver s).src (s.right c) := by
  have h := s.compDomProof
  unfold Obj.ObjMorCompObjMorCompDom at h
  exact congrFun h c

/-- Codomain of composite equals codomain of left morphism. -/
theorem catJudgCoprCompCod (c : s.compType) :
    (catJudgCoprToOverQuiver s).tgt (s.composite c) =
    (catJudgCoprToOverQuiver s).tgt (s.left c) := by
  have h := s.compCodProof
  unfold Obj.ObjMorCompObjMorCompCod at h
  exact congrFun h c

/-! ### CategoryQuotientData construction

Package the CatJudgCopr as a CategoryQuotientData for use with FreeMor/FreeMorEquiv.

Note: CategoryQuotientData.{v, u} requires IdWitness and CompWitness to have the
same universe as objects. For a general CatJudgCopr.{u, v, w, x}, we restrict to
the case where w = u and x = u (which holds for the output of catToCatJudgCopr). -/

variable (t : Obj.CatJudgCopr.{u', v', u', u'})

/-- Convert a compatible CatJudgCopr to CategoryQuotientData.

This works for CatJudgCopr.{u, v, u, u} where the identity type and composition
type match the object universe. This is the case for CatJudgCopr values produced
by catToCatJudgCopr. -/
def catJudgCoprToCategoryQuotientData' : GebLean.CategoryQuotientData.{v', u'} where
  quiver := catJudgCoprToOverQuiver t
  IdWitness := t.idType
  idObj := catJudgCoprIdObj t
  idMor := t.idMor
  id_src := catJudgCoprIdSrc t
  id_tgt := catJudgCoprIdTgt t
  CompWitness := t.compType
  compRight := t.right
  compLeft := t.left
  compComposite := t.composite
  comp_match := catJudgCoprCompMatch t
  comp_dom := catJudgCoprCompDom t
  comp_cod := catJudgCoprCompCod t

/-! ### Conversion to Category

Using FreeMor quotient, convert a CatJudgCopr to a category object in Cat. -/

/-- The OverCategoryData derived from a compatible CatJudgCopr.

This uses FreeMor and FreeMorEquiv to quotient the free morphisms into
a category. -/
def catJudgCoprToOverCategoryData' :
    OverCategoryData (catJudgCoprToCategoryQuotientData' t).quotQuiver :=
  (catJudgCoprToCategoryQuotientData' t).toOverCategoryData

/-- Bundle the OverCategoryData with its quiver. -/
def catJudgCoprToBundledOverCategoryData' :
    BundledOverCategoryData.{max v' u', u'} where
  quiver := (catJudgCoprToCategoryQuotientData' t).quotQuiver
  data := catJudgCoprToOverCategoryData' t

/-- Convert a compatible CatJudgCopr to BundledCategoryData. -/
def catJudgCoprToBundledCategoryData' : BundledCategoryData.{max v' u', u'} :=
  (catJudgCoprToBundledOverCategoryData' t).toBundledCategoryData

/-- Convert a compatible CatJudgCopr to a category (Cat object).

This is the L functor on objects: CatJudgCopr.{u, v, u, u} → Cat.{max v u, u} -/
def catJudgCoprToCat' : Cat.{max v' u', u'} :=
  BundledCategoryData.toCatObj (catJudgCoprToBundledCategoryData' t)

/-! ### Morphism Mapping for L Functor

Given a CatJudgNatTrans, construct the induced functor between the
corresponding categories. -/

variable {t₁ t₂ : Obj.CatJudgCopr.{u', v', u', u'}}
variable (f : Mor.CatJudgNatTrans t₁ t₂)

/-- Build an OverQuiverMorphism from a CatJudgNatTrans.

The quiver morphism uses objMap on objects and morMap on morphisms. -/
def catJudgNatTransToOverQuiverMor :
    OverQuiverMorphism (catJudgCoprToOverQuiver t₁) (catJudgCoprToOverQuiver t₂) where
  objFn := f.objMap
  morFn := f.morMap
  src_comm := fun m => by
    have h := f.domProof
    unfold Mor.CatJudgNaturalityDom at h
    exact (congrFun h m).symm
  tgt_comm := fun m => by
    have h := f.codProof
    unfold Mor.CatJudgNaturalityCod at h
    exact (congrFun h m).symm

/-- Build a CategoryQuotientMorphism from a CatJudgNatTrans.

This packages the object/morphism maps with identity and composition
witness maps and their coherence proofs. -/
def catJudgNatTransToCategoryQuotientMorphism :
    GebLean.CategoryQuotientMorphism
      (catJudgCoprToCategoryQuotientData' t₁)
      (catJudgCoprToCategoryQuotientData' t₂) where
  quiverMor := catJudgNatTransToOverQuiverMor f
  idWitMap := f.idMap
  compWitMap := f.compMap
  idObj_comm := fun i => by
    unfold catJudgCoprToCategoryQuotientData' catJudgCoprIdObj
        catJudgNatTransToOverQuiverMor
    simp only [Function.comp_apply]
    have h := f.idMorProof
    unfold Mor.CatJudgNaturalityIdMor at h
    have heq := congrFun h i
    simp only [Function.comp_apply] at heq
    have hdom := f.domProof
    unfold Mor.CatJudgNaturalityDom at hdom
    rw [← heq]
    exact congrFun hdom (t₁.idMor i)
  idMor_comm := fun i => by
    unfold catJudgCoprToCategoryQuotientData' catJudgNatTransToOverQuiverMor
    simp only
    have h := f.idMorProof
    unfold Mor.CatJudgNaturalityIdMor at h
    exact congrFun h i
  compRight_comm := fun c => by
    unfold catJudgCoprToCategoryQuotientData' catJudgNatTransToOverQuiverMor
    simp only
    have h := f.rightProof
    unfold Mor.CatJudgNaturalityRight at h
    exact congrFun h c
  compLeft_comm := fun c => by
    unfold catJudgCoprToCategoryQuotientData' catJudgNatTransToOverQuiverMor
    simp only
    have h := f.leftProof
    unfold Mor.CatJudgNaturalityLeft at h
    exact congrFun h c
  compComposite_comm := fun c => by
    unfold catJudgCoprToCategoryQuotientData' catJudgNatTransToOverQuiverMor
    simp only
    have h := f.compositeProof
    unfold Mor.CatJudgNaturalityComposite at h
    exact congrFun h c

/-- Build an OverQuiverMorphism between the quotient quivers from a CatJudgNatTrans.

This uses bundleQuotMor to wrap quotient morphisms with their source/target. -/
def catJudgNatTransToQuotQuiverMor :
    OverQuiverMorphism
      (catJudgCoprToCategoryQuotientData' t₁).quotQuiver
      (catJudgCoprToCategoryQuotientData' t₂).quotQuiver where
  objFn := f.objMap
  morFn := fun m =>
    (catJudgCoprToCategoryQuotientData' t₂).bundleQuotMor
      ((catJudgNatTransToCategoryQuotientMorphism f).quotMapMor m.2.2)
  src_comm := fun _ => rfl
  tgt_comm := fun _ => rfl

/-- Build an OverFunctorData from a CatJudgNatTrans.

This is the L functor on morphisms: CatJudgNatTrans → functor between Cat objects. -/
def catJudgNatTransToOverFunctorData :
    OverFunctorData
      (catJudgCoprToOverCategoryData' t₁)
      (catJudgCoprToOverCategoryData' t₂) where
  toOverQuiverMorphism := catJudgNatTransToQuotQuiverMor f
  map_id := fun a => by
    simp only [catJudgNatTransToQuotQuiverMor, catJudgCoprToOverCategoryData',
      CategoryQuotientData.toOverCategoryData, CategoryQuotientData.bundleQuotMor]
    rfl
  map_comp := fun p => by
    rcases p with ⟨⟨⟨g_src, g_tgt, g_qm⟩, ⟨f_src, f_tgt, f_qm⟩⟩, hcomp⟩
    have heq : g_tgt = f_src := hcomp
    simp only [catJudgNatTransToQuotQuiverMor, catJudgCoprToOverCategoryData',
      CategoryQuotientData.toOverCategoryData, CategoryQuotientData.quotCategoryOps,
      CategoryQuotientData.quotCompFn, CategoryQuotientData.bundleQuotMor,
      CategoryQuotientData.quotQuiver]
    cases heq
    simp only [CategoryQuotientMorphism.quotMapMor_comp]
    rfl

/-- Convert a CatJudgNatTrans to a FunctorData between the BundledCategoryData values. -/
def catJudgNatTransToFunctorData :
    FunctorData
      (catJudgCoprToBundledCategoryData' t₁).data
      (catJudgCoprToBundledCategoryData' t₂).data :=
  toBundledCategoryData_map (catJudgNatTransToOverFunctorData f)

/-- Convert a CatJudgNatTrans to a morphism in Cat. -/
def catJudgNatTransToCatMor :
    catJudgCoprToCat' t₁ ⟶ catJudgCoprToCat' t₂ :=
  BundledCategoryData.functorToCat.map (catJudgNatTransToFunctorData f)

/-! ### L Functor Functoriality -/

/-- L preserves identity at the OverFunctorData level. -/
theorem catJudgNatTransToOverFunctorData_id (t : Obj.CatJudgCopr.{u', v', u', u'}) :
    catJudgNatTransToOverFunctorData (PLang.Cat.CatJudgNatTrans.id t) =
    OverFunctorData.id (catJudgCoprToOverCategoryData' t) := by
  apply OverFunctorData.ext
  · rfl
  · funext m
    simp only [catJudgNatTransToOverFunctorData, catJudgNatTransToQuotQuiverMor,
      catJudgNatTransToCategoryQuotientMorphism, catJudgCoprToOverCategoryData',
      CategoryQuotientData.toOverCategoryData, CategoryQuotientData.bundleQuotMor,
      PLang.Cat.CatJudgNatTrans.id, PLang.Cat.CatJudgMap.id,
      OverFunctorData.id, OverQuiverMorphism.id]
    congr 1
    congr 1
    exact CategoryQuotientMorphism.quotMapMor_id_self m.2.2

/-- L preserves identity at the FunctorData level. -/
theorem catJudgNatTransToFunctorData_id (t : Obj.CatJudgCopr.{u', v', u', u'}) :
    catJudgNatTransToFunctorData (PLang.Cat.CatJudgNatTrans.id t) =
    BundledCategoryData.idFunctorData (catJudgCoprToBundledCategoryData' t) := by
  simp only [catJudgNatTransToFunctorData, toBundledCategoryData_map]
  rw [catJudgNatTransToOverFunctorData_id]
  rfl

/-- L preserves identity: L(id) = id. -/
theorem catJudgNatTransToCatMor_id (t : Obj.CatJudgCopr.{u', v', u', u'}) :
    catJudgNatTransToCatMor (PLang.Cat.CatJudgNatTrans.id t) =
    𝟙 (catJudgCoprToCat' t) := by
  simp only [catJudgNatTransToCatMor]
  rw [catJudgNatTransToFunctorData_id]
  rfl

/-- L preserves composition at the OverFunctorData level. -/
theorem catJudgNatTransToOverFunctorData_comp
    {t₁ t₂ t₃ : Obj.CatJudgCopr.{u', v', u', u'}}
    (f : Mor.CatJudgNatTrans t₁ t₂)
    (g : Mor.CatJudgNatTrans t₂ t₃) :
    catJudgNatTransToOverFunctorData (PLang.Cat.CatJudgNatTrans.comp f g) =
    (catJudgNatTransToOverFunctorData f).comp (catJudgNatTransToOverFunctorData g) := by
  apply OverFunctorData.ext
  · rfl
  · funext m
    simp only [catJudgNatTransToOverFunctorData, catJudgNatTransToQuotQuiverMor,
      catJudgNatTransToCategoryQuotientMorphism,
      PLang.Cat.CatJudgNatTrans.comp, PLang.Cat.CatJudgMap.comp,
      Cat.ObjMap.comp, OverFunctorData.comp, OverQuiverMorphism.comp,
      catJudgCoprToOverCategoryData', CategoryQuotientData.toOverCategoryData,
      CategoryQuotientData.bundleQuotMor, Function.comp_apply]
    congr 1
    congr 1
    induction m.2.2 using Quotient.ind with
    | _ fm =>
      simp only [CategoryQuotientMorphism.quotMapMor, CategoryQuotientData.quotMor]
      exact congrArg Quotient.mk''
        (FreeMor.mapQuiver_quiverComp
          (catJudgNatTransToCategoryQuotientMorphism f).quiverMor
          (catJudgNatTransToCategoryQuotientMorphism g).quiverMor fm)

/-- L preserves composition at the FunctorData level. -/
theorem catJudgNatTransToFunctorData_comp
    {t₁ t₂ t₃ : Obj.CatJudgCopr.{u', v', u', u'}}
    (f : Mor.CatJudgNatTrans t₁ t₂)
    (g : Mor.CatJudgNatTrans t₂ t₃) :
    catJudgNatTransToFunctorData (PLang.Cat.CatJudgNatTrans.comp f g) =
    BundledCategoryData.compFunctorData
      (catJudgNatTransToFunctorData f)
      (catJudgNatTransToFunctorData g) := by
  simp only [catJudgNatTransToFunctorData]
  rw [catJudgNatTransToOverFunctorData_comp]
  rfl

/-- L preserves composition: L(f ≫ g) = L(f) ≫ L(g). -/
theorem catJudgNatTransToCatMor_comp
    {t₁ t₂ t₃ : Obj.CatJudgCopr.{u', v', u', u'}}
    (f : Mor.CatJudgNatTrans t₁ t₂)
    (g : Mor.CatJudgNatTrans t₂ t₃) :
    catJudgNatTransToCatMor (PLang.Cat.CatJudgNatTrans.comp f g) =
    catJudgNatTransToCatMor f ≫ catJudgNatTransToCatMor g := by
  simp only [catJudgNatTransToCatMor]
  rw [catJudgNatTransToFunctorData_comp]
  rfl

/-- The reflection functor L : CatJudgCopr → Cat.

Sends a CatJudgCopr to the free category on its quiver, quotiented by
identity and composition witness relations.

Universe constraint: We use `{uL + 1, vL + 1, uL + 1, uL + 1}` to match the
CategoryQuotientData requirement that `IdWitness` and `CompWitness` are
both `Type uL`. The category instance on CatJudgCopr uses the same pattern. -/
def LFunctor_PLang.{uL, vL} :
    Obj.CatJudgCopr.{uL + 1, vL + 1, uL + 1, uL + 1} ⥤
    CategoryTheory.Cat.{max (vL + 1) (uL + 1), uL + 1} where
  obj := catJudgCoprToCat'
  map := catJudgNatTransToCatMor
  map_id t := catJudgNatTransToCatMor_id t
  map_comp f g := catJudgNatTransToCatMor_comp f g

end LFunctor

/-! ## Adjunction Structure

The adjunction L ⊣ Φ between CatJudgCopr and Cat.

Universe note: For the composition L ∘ Φ to be well-typed, we need Φ's output to
match L's input. Φ produces `CatJudgCopr.{u+1, max (u+1) (v+1), u+1, max (u+1) (v+1)}`,
but L requires `CatJudgCopr.{u+1, v+1, u+1, u+1}`. These match when `v ≤ u`.

For simplicity, we work at a single universe level (u = v), matching the original
adjunction's approach. -/

section AdjunctionStructure

open CategoryTheory

universe uAdj

/-! ### Unit: id → Phi ∘ L

The unit η sends each CatJudgCopr s to Phi(L(s)). Since L(s) is built by quotienting
FreeMor on s's quiver, Phi(L(s)) has:
- Objects: s.obj (same as s)
- Morphisms: bundled morphisms in the quotient category
- Identity type: s.obj
- Composition type: composable pairs in the quotient

The unit embeds s's morphisms into the quotient via FreeMor.var. -/

variable (s : Obj.CatJudgCopr.{uAdj + 1, uAdj + 1, uAdj + 1, uAdj + 1})

/-- The CategoryQuotientData for s at aligned universes. -/
abbrev adjCQD := catJudgCoprToCategoryQuotientData' s

/-- The quotient quiver for a CatJudgCopr at aligned universes. -/
abbrev adjQuotQuiver := (adjCQD s).quotQuiver

/-- The quotient morphism type between two objects. -/
abbrev adjQuotMor (a b : s.obj) := (adjCQD s).QuotMor a b

/-- The OverQuiver underlying the quotient construction for s. -/
abbrev adjBaseQuiver := catJudgCoprToOverQuiver s

/-- Embed a morphism from s.mor into the quotient category.

This sends f : s.mor to the equivalence class [var f] in L(s).
We explicitly provide the FreeMor type arguments to help type inference. -/
def unitMorEmbed (f : s.mor) : adjQuotMor s (s.dom f) (s.cod f) :=
  (adjCQD s).quotMor (@FreeMor.var (adjBaseQuiver s) f)

/-- The HomSet for morphisms in catJudgCoprToCat' s.

This is the fiber of the quotient quiver at (a, b). -/
abbrev adjHomSet (a b : s.obj) :=
  (adjQuotQuiver s).toHomSet a b

/-- Embed a quotient morphism into the HomSet.

This wraps a QuotMor with source/target proofs to get an element of toHomSet. -/
def embedQuotMorAsHom {a b : s.obj} (qm : adjQuotMor s a b) : adjHomSet s a b :=
  ⟨(adjCQD s).bundleQuotMor qm, rfl, rfl⟩

/-- The category instance on catJudgCoprToCat' s comes from CategoryOfData. -/
abbrev adjCatInst : Category (catJudgCoprToCat' s) :=
  CategoryOfData (catJudgCoprToBundledCategoryData' s).data

/-- Embed a morphism from s.mor into the category L(s) as a morphism a ⟶ b.

This sends f : s.mor to its equivalence class [var f] in the category. -/
def unitMorAsHom (f : s.mor) :
    @Quiver.Hom (catJudgCoprToCat' s)
      (@CategoryStruct.toQuiver _ (adjCatInst s).toCategoryStruct)
      (s.dom f) (s.cod f) :=
  embedQuotMorAsHom s (unitMorEmbed s f)

/-- The .val of unitMorAsHom equals bundleQuotMor applied to the quotient class. -/
theorem unitMorAsHom_val (f : s.mor) :
    (unitMorAsHom s f).val = (adjCQD s).bundleQuotMor ((adjCQD s).quotMor (FreeMor.var f)) :=
  rfl

/-- The .snd.snd of unitMorAsHom.val is the quotient morphism. -/
theorem unitMorAsHom_val_snd_snd (f : s.mor) :
    (unitMorAsHom s f).val.snd.snd = (adjCQD s).quotMor (FreeMor.var f) :=
  rfl

/-- Transport on unitMorAsHom preserves the bundleQuotMor structure.

When we transport unitMorAsHom along an equality of dom indices, the .val
remains the same bundleQuotMor applied to the quotMor of the original morphism. -/
theorem unitMorAsHom_transport_val
    {a a' : s.obj} {b : s.obj} (h : a = a') (f : s.mor)
    (hdom : s.dom f = a) (hcod : s.cod f = b) :
    ((h ▸ (hdom ▸ hcod ▸ unitMorAsHom s f : adjHomSet s a b)) : adjHomSet s a' b).val =
    (adjCQD s).bundleQuotMor ((adjCQD s).quotMor (FreeMor.var f)) := by
  subst h hdom hcod
  rfl

/-- The target CatJudgCopr for the unit: Phi(L(s)).

This is the CatJudgCopr of the category L(s). For aligned universes, this
matches the universe structure of s. -/
abbrev unitTarget : Obj.CatJudgCopr.{uAdj + 1, uAdj + 1, uAdj + 1, uAdj + 1} :=
  catToCatJudgCopr (catJudgCoprToCat' s)

/-- The morphism component of the unit: s.mor → BundledHom (L(s)).

This sends each morphism f to the bundled morphism (dom f, cod f, [var f]). -/
def unitMorMap (f : s.mor) : BundledHom (catJudgCoprToCat' s) :=
  ⟨s.dom f, s.cod f, unitMorAsHom s f⟩

/-- The identity component of the unit: s.idType → (L(s)).α.

Since L(s).α = s.obj and s.idType = s.obj (from id witnesses), this is
essentially s.dom ∘ s.idMor which gives the object an identity is for. -/
def unitIdMap (i : s.idType) : (catJudgCoprToCat' s).α :=
  catJudgCoprIdObj s i

/-- The composition component of the unit: s.compType → ComposablePair (L(s)).

Given a composition witness c, we embed the right and left morphisms into
L(s) to form a composable pair. The comp_match condition ensures the
embedded morphisms are composable. -/
def unitCompMap (c : s.compType) : ComposablePair (catJudgCoprToCat' s) := by
  refine ⟨s.dom (s.right c), s.cod (s.right c), s.cod (s.left c), ?_, ?_⟩
  · exact unitMorAsHom s (s.right c)
  · have h : s.cod (s.right c) = s.dom (s.left c) :=
      congrFun s.compMatchProof c
    exact h ▸ unitMorAsHom s (s.left c)

/-- The object map for the unit is the identity. -/
def unitObjMap : s.obj → (unitTarget s).obj := id

/-- The CatJudgMap for the unit: (objMap, morMap, idMap, compMap). -/
def unitCatJudgMap : Mor.CatJudgMap s (unitTarget s) :=
  ((unitObjMap s, unitMorMap s), (unitIdMap s, unitCompMap s))

/-- Domain naturality for the unit.

For any f : s.mor, we have:
  unitObjMap (s.dom f) = (unitTarget s).dom (unitMorMap s f)

Both sides equal s.dom f by definition. -/
theorem unitNaturalityDom : Mor.CatJudgNaturalityDom (unitCatJudgMap s) := by
  unfold Mor.CatJudgNaturalityDom unitCatJudgMap unitObjMap unitMorMap
  unfold unitTarget catToCatJudgCopr catToCatJudgObjMor catToCatJudgMor
  unfold catToCatJudgObj catToBundledDom BundledHom.dom
  funext f
  rfl

/-- Codomain naturality for the unit.

For any f : s.mor, we have:
  unitObjMap (s.cod f) = (unitTarget s).cod (unitMorMap s f)

Both sides equal s.cod f by definition. -/
theorem unitNaturalityCod : Mor.CatJudgNaturalityCod (unitCatJudgMap s) := by
  unfold Mor.CatJudgNaturalityCod unitCatJudgMap unitObjMap unitMorMap
  unfold unitTarget catToCatJudgCopr catToCatJudgObjMor catToCatJudgMor
  unfold catToCatJudgObj catToBundledCod BundledHom.cod
  funext f
  rfl

/-- The endomorphism condition for identities, stated with standard accessors.
    This converts from the ObjMorIdObjMorEndo form to the form using s.dom/cod/idMor. -/
theorem unitIdEndo (i : s.idType) : s.cod (s.idMor i) = s.dom (s.idMor i) := by
  have h := s.endoProof
  unfold Obj.ObjMorIdObjMorEndo at h
  have h' := congrFun h i
  exact h'.symm

/-- Identity naturality for the unit.

For any i : s.idType, unitMorMap (s.idMor i) = (unitTarget s).idMor (unitIdMap i).

The LHS is (dom, cod, [var (idMor i)]).
The RHS is (a, a, 𝟙 a) where a = unitIdMap i.

These are equal because:
- dom = cod = a (identity is endomorphism)
- [var (idMor i)] = 𝟙 a in the quotient (by FreeMorEquiv.id) -/
theorem unitNaturalityIdMor : Mor.CatJudgNaturalityIdMor (unitCatJudgMap s) := by
  unfold Mor.CatJudgNaturalityIdMor unitCatJudgMap unitMorMap unitIdMap
  unfold unitTarget catToCatJudgCopr catToCatJudgObjMor catToCatJudgMor
  unfold catToCatJudgObj catToIdMor BundledHom.mk unitObjMap
  funext i
  unfold catJudgCoprIdObj
  simp only [Function.comp_apply]
  have h_endo : s.cod (s.idMor i) = s.dom (s.idMor i) := unitIdEndo s i
  let D := adjCQD s
  have h_wit := CategoryQuotientData.FreeMorEquivGen.id_witness (D := D) i
  have h_quot_eq : D.quotMor (cast (congrArg₂ (FreeMor D.quiver)
        (D.id_src i) (D.id_tgt i))
      (FreeMor.var (D.idMor i))) = D.quotMor (FreeMor.id (D.idObj i)) :=
    Quotient.sound (CategoryQuotientData.FreeMorEquiv.rel h_wit)
  simp only [unitMorAsHom, embedQuotMorAsHom, unitMorEmbed]
  have h_goal : ∀ (a b : s.obj) (h : b = a)
      (m1 : adjHomSet s a b) (m2 : adjHomSet s a a),
      m1.val = m2.val →
      HEq (Sigma.mk b m1 : Σ b, adjHomSet s a b) (Sigma.mk a m2) := by
    intro a b h m1 m2 hval
    subst h
    congr 1
    exact Subtype.ext hval
  refine Sigma.ext rfl ?_
  apply h_goal _ _ h_endo
  simp only [adjQuotQuiver, CategoryQuotientData.bundleQuotMor]
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  refine Sigma.ext h_endo ?_
  apply HEq.trans (cast_heq _ _).symm
  · apply heq_of_eq
    rw [D.quotMor_cast rfl h_endo]
    exact h_quot_eq

/-- Left naturality for the unit.

For any c : s.compType, unitMorMap (s.left c) = (unitTarget s).left (unitCompMap c).

Both sides are the left morphism of a composition witness, embedded into the quotient.
The LHS is ⟨dom (left c), cod (left c), unitMorAsHom (left c)⟩.
The RHS is ⟨cod (right c), cod (left c), cast ... (unitMorAsHom (left c))⟩.
These are equal via comp_match: cod (right c) = dom (left c). -/
theorem unitNaturalityLeft : Mor.CatJudgNaturalityLeft (unitCatJudgMap s) := by
  unfold Mor.CatJudgNaturalityLeft unitCatJudgMap unitMorMap unitCompMap
  unfold unitTarget catToCatJudgCopr catToCatJudgObjMor catToCatJudgMor
  unfold catToCatJudgObj catToLeft ComposablePair.left BundledHom.mk
  unfold Mor.CatJudgMap.morMap Mor.CatJudgMap.compMap Mor.CatJudgMap.objMorMap
  unfold Mor.ObjMorMap.morMap
  funext c
  simp only [Function.comp_apply]
  have h_match : s.cod (s.right c) = s.dom (s.left c) := congrFun s.compMatchProof c
  simp only [unitMorAsHom, embedQuotMorAsHom, unitMorEmbed]
  let D := adjCQD s
  let C := catJudgCoprToCat' s
  have h_bundled_eq : ∀ (a b : s.obj) (h : a = b)
      (cod_val : s.obj) (m : adjHomSet s a cod_val),
      (⟨a, ⟨cod_val, m⟩⟩ : BundledHom C) = ⟨b, ⟨cod_val, h ▸ m⟩⟩ := by
    intro a b h cod_val m
    subst h
    rfl
  exact h_bundled_eq (s.dom (s.left c)) (s.cod (s.right c)) h_match.symm
    (s.cod (s.left c))
    ⟨D.bundleQuotMor (D.quotMor (FreeMor.var (s.left c))), rfl, rfl⟩

/-- Right naturality for the unit.

For any c : s.compType, unitMorMap (s.right c) = (unitTarget s).right (unitCompMap c).

Both sides are the right morphism of a composition witness, embedded into the quotient. -/
theorem unitNaturalityRight : Mor.CatJudgNaturalityRight (unitCatJudgMap s) := by
  unfold Mor.CatJudgNaturalityRight unitCatJudgMap unitMorMap unitCompMap
  unfold unitTarget catToCatJudgCopr catToCatJudgObjMor catToCatJudgMor
  unfold catToCatJudgObj catToRight ComposablePair.right
  funext c
  simp only [Function.comp_apply]
  rfl

/-- Composition in the adjoint category, explicitly computed.

When we compose morphisms in the adjoint category where both are embedded
quotMors, the result's underlying BundledQuotMor has the quotComp of the
underlying QuotMors. Note: quotComp takes (g : b → c) then (f : a → b). -/
theorem adjHomSet_comp_val_eq {a b c : s.obj}
    (qm1 : (adjCQD s).QuotMor a b) (qm2 : (adjCQD s).QuotMor b c) :
    (@CategoryStruct.comp (catJudgCoprToCat' s) (adjCatInst s).toCategoryStruct
      a b c (embedQuotMorAsHom s qm1) (embedQuotMorAsHom s qm2)).val =
    ⟨a, c, (adjCQD s).quotComp qm2 qm1⟩ := by
  unfold adjCatInst catJudgCoprToCat' BundledCategoryData.toCatObj
  simp only [CategoryOfData]
  unfold catJudgCoprToBundledCategoryData'
  simp only [BundledOverCategoryData.toBundledCategoryData]
  unfold catJudgCoprToBundledOverCategoryData' catJudgCoprToOverCategoryData'
  simp only [CategoryQuotientData.toOverCategoryData, OverCategoryData.toCategoryData,
    OverCategoryData.toCategoryOps, OverCategoryData.extractComp]
  simp only [CategoryQuotientData.quotCategoryOps, CategoryQuotientData.quotCompFn,
    CategoryQuotientData.bundleQuotMor, CategoryQuotientData.quotQuiver,
    embedQuotMorAsHom]

/-- Transport swap for quotComp.

For quotient composition, transporting the domain of the second argument is
equivalent to transporting the codomain of the first argument (in the opposite
direction). This follows from the FreeMor level fact that:
  g.comp (h ▸ f) = (cast h.symm g).comp f -/
theorem quotComp_transport_swap {D : CategoryQuotientData} {a b b' c : D.quiver.Obj}
    (h : b' = b) (g : D.QuotMor b c) (f : D.QuotMor a b') :
    D.quotComp g (h ▸ f) = D.quotComp (h.symm ▸ g) f := by
  induction g using Quotient.inductionOn with
  | h g_repr =>
    induction f using Quotient.inductionOn with
    | h f_repr =>
      simp only [CategoryQuotientData.quotComp]
      cases h
      rfl

/-- Transport along an equality preserves HEq with the original value.

    For `h : a = b` and `x : P b`, we have `(h ▸ x) ≍ x`.
    This is because transport only changes the type indexing, not the value. -/
theorem transport_heq {α : Sort*} {a b : α} {P : α → Sort*}
    (h : a = b) (x : P b) : HEq (h ▸ x) x := by
  cases h
  rfl

/-- Transport in the first index of a two-indexed family preserves HEq.

    For a two-indexed family `P : α → β → Sort*`, transporting in the first
    index gives a value HEq to the original. -/
theorem transport_heq_fst {α : Sort*} {a b : α} {β : Sort*} {y : β}
    {P : α → β → Sort*} (h : a = b) (x : P b y) : HEq (h ▸ x) x := by
  cases h
  rfl

/-- Transport in the second index of a two-indexed family preserves HEq.

    For a two-indexed family `P : α → β → Sort*`, transporting in the second
    index gives a value HEq to the original. When `h : a = b` and `v : P x a`,
    we have `h ▸ v : P x b` and `(h ▸ v) ≍ v`. -/
theorem transport_heq_snd {α : Sort*} {x : α} {β : Sort*} {a b : β}
    {P : α → β → Sort*} (h : a = b) (v : P x a) : HEq (h ▸ v) v := by
  cases h
  rfl

/-- HEq version of quotComp equality.

    When the type parameters (a, b, c) are propositionally equal and the
    arguments are HEq, the quotComp results are HEq. This handles the case
    where casts/transports change the type indices but not the underlying
    quotient values. -/
theorem quotComp_heq {D : CategoryQuotientData}
    {a a' b b' c c' : D.quiver.Obj}
    (ha : a = a') (hb : b = b') (hc : c = c')
    {g : D.QuotMor b c} {g' : D.QuotMor b' c'}
    {f : D.QuotMor a b} {f' : D.QuotMor a' b'}
    (hg : g ≍ g') (hf : f ≍ f') :
    D.quotComp g f ≍ D.quotComp g' f' := by
  cases ha; cases hb; cases hc
  cases (eq_of_heq hg)
  cases (eq_of_heq hf)
  rfl

/-- The codomain of a composition in the adjoint category equals the second
    operand's codomain.

    When composing `m ≫ (h ▸ n)` where `n : adjHomSet s b' c` is transported by
    a predicate equality `h` to match the composability requirement, the result's
    codomain (`.val.snd.fst`) equals `n.val.snd.fst = c`.

    This follows from `quotCompFn` returning `⟨g.1, f.2.1, quotComp ...⟩` where
    `f` is the second operand, and subtype transport preserving `.val`. -/
theorem adjHomSet_comp_cod_eq {a b c : s.obj}
    (m : adjHomSet s a b) (n : adjHomSet s b c) :
    (@CategoryStruct.comp (catJudgCoprToCat' s) (adjCatInst s).toCategoryStruct
      a b c m n).val.snd.fst = c := by
  unfold adjCatInst catJudgCoprToCat' BundledCategoryData.toCatObj
  simp only [CategoryOfData]
  unfold catJudgCoprToBundledCategoryData'
  simp only [BundledOverCategoryData.toBundledCategoryData]
  unfold catJudgCoprToBundledOverCategoryData' catJudgCoprToOverCategoryData'
  simp only [CategoryQuotientData.toOverCategoryData, OverCategoryData.toCategoryData,
    OverCategoryData.toCategoryOps, OverCategoryData.extractComp]
  simp only [CategoryQuotientData.quotCategoryOps, CategoryQuotientData.quotCompFn,
    CategoryQuotientData.quotQuiver]
  exact n.property.2

/-- The QuotMor of a composition in the adjoint category.

    The composition's `.val.snd.snd` (the QuotMor) equals
    `quotComp n.snd.snd (composable ▸ m.snd.snd)` where `composable` is
    the proof that `m.snd.fst = n.fst`. -/
theorem adjHomSet_comp_quotMor_eq {a b c : s.obj}
    (m : adjHomSet s a b) (n : adjHomSet s b c) :
    let D := catJudgCoprToCategoryQuotientData' s
    let composable : m.val.snd.fst = n.val.fst :=
      m.property.2.trans n.property.1.symm
    (@CategoryStruct.comp (catJudgCoprToCat' s) (adjCatInst s).toCategoryStruct
      a b c m n).val.snd.snd =
    D.quotComp n.val.snd.snd (composable ▸ m.val.snd.snd) := by
  unfold adjCatInst catJudgCoprToCat' BundledCategoryData.toCatObj
  simp only [CategoryOfData]
  unfold catJudgCoprToBundledCategoryData'
  simp only [BundledOverCategoryData.toBundledCategoryData]
  unfold catJudgCoprToBundledOverCategoryData' catJudgCoprToOverCategoryData'
  simp only [CategoryQuotientData.toOverCategoryData, OverCategoryData.toCategoryData,
    OverCategoryData.toCategoryOps, OverCategoryData.extractComp]
  simp only [CategoryQuotientData.quotCategoryOps, CategoryQuotientData.quotCompFn,
    CategoryQuotientData.quotQuiver]

/-- Subtype transport on adjHomSet preserves `.val`.

    When transporting `m : adjHomSet s a b` along `h : a' = a`, the underlying
    `BundledQuotMor` value is unchanged because transport only affects the proof
    component, not the value.

    Note: In Lean 4, `h ▸ m` where `h : a' = a` and `m : P a` gives `P a'`. -/
theorem adjHomSet_transport_val_eq {a b a' : s.obj}
    (h : a' = a) (m : adjHomSet s a b) :
    ((h ▸ m) : adjHomSet s a' b).val = m.val := by
  cases h
  rfl

/-- Subtype transport on adjHomSet preserves `.val` (codomain version). -/
theorem adjHomSet_transport_cod_val_eq {a b b' : s.obj}
    (h : b' = b) (m : adjHomSet s a b) :
    ((h ▸ m) : adjHomSet s a b').val = m.val := by
  cases h
  rfl

/-- Subtype transport on adjHomSet preserves the QuotMor component (HEq version).

    Since the QuotMor type depends on domain/codomain, we get HEq, not Eq.
    But combined with `adjHomSet_transport_val_eq`, we know the underlying
    values are the same. -/
theorem adjHomSet_transport_quotMor_heq {a b a' : s.obj}
    (h : a' = a) (m : adjHomSet s a b) :
    ((h ▸ m) : adjHomSet s a' b).val.snd.snd ≍ m.val.snd.snd := by
  cases h
  rfl

/-- The quotient morphism for composite equals the quotComp of left and right.

This is the essential equality at the quotient level, derived from comp_witness.

The proof uses the fact that h_wit provides an equivalence between the
composition of transported morphism variables and the transported composite. -/
theorem unitCompositeQuotMorEq (c : s.compType) :
    let D := adjCQD s
    let h_match : s.cod (s.right c) = s.dom (s.left c) := congrFun s.compMatchProof c
    let h_dom : s.dom (s.composite c) = s.dom (s.right c) := congrFun s.compDomProof c
    let h_cod : s.cod (s.composite c) = s.cod (s.left c) := congrFun s.compCodProof c
    let qm_left := D.quotMor (@FreeMor.var D.quiver (s.left c))
    let qm_right := D.quotMor (@FreeMor.var D.quiver (s.right c))
    let qm_comp := D.quotMor (@FreeMor.var D.quiver (s.composite c))
    let qm_left_transported : D.QuotMor (s.cod (s.right c)) (s.cod (s.left c)) :=
      h_match ▸ qm_left
    (h_dom ▸ h_cod ▸ qm_comp : D.QuotMor (s.dom (s.right c)) (s.cod (s.left c))) =
    D.quotComp qm_left_transported qm_right := by
  simp only
  let D := adjCQD s
  have h_wit := CategoryQuotientData.FreeMorEquivGen.comp_witness (D := D) c
  have h_dom := congrFun s.compDomProof c
  have h_cod := congrFun s.compCodProof c
  have h_match := congrFun s.compMatchProof c
  apply eq_of_heq
  simp only [eqRec_eq_cast]
  apply heq_of_eq
  rw [cast_cast]
  rw [D.quotMor_cast h_dom h_cod]
  simp only [CategoryQuotientData.quotMor, CategoryQuotientData.quotComp]
  apply Eq.symm
  have cast_quot_eq_quot_cast :
      ∀ {a a' b : D.quiver.Obj} (h : a = a')
        (f : FreeMor D.quiver a b)
        (p : Quotient (D.freeMorSetoid a b) = Quotient (D.freeMorSetoid a' b)),
        cast p (⟦f⟧ : Quotient (D.freeMorSetoid a b)) =
        (⟦cast (congrArg₂ (FreeMor D.quiver) h rfl) f⟧ :
          Quotient (D.freeMorSetoid a' b)) := by
    intro a a' b h f p
    subst h
    rfl
  simp only [Quotient.lift₂]
  erw [cast_quot_eq_quot_cast h_match.symm (FreeMor.var (Q := D.quiver) (s.left c)) _]
  erw [Quotient.lift_mk]
  erw [Quotient.lift_mk]
  apply Quotient.sound
  exact CategoryQuotientData.FreeMorEquiv.rel h_wit

/-- Composite naturality for the unit.

For any c : s.compType, unitMorMap (s.composite c) =
  (unitTarget s).composite (unitCompMap c).

The LHS is [var (composite c)] in the quotient.
The RHS is the composition of [var (left c)] and [var (right c)] in the quotient.

These are equal by the comp_witness relation in FreeMorEquiv. -/
theorem unitNaturalityComposite : Mor.CatJudgNaturalityComposite (unitCatJudgMap s) := by
  unfold Mor.CatJudgNaturalityComposite unitCatJudgMap
  funext c
  simp only [Function.comp_apply]
  let D := adjCQD s
  have h_wit := CategoryQuotientData.FreeMorEquivGen.comp_witness (D := D) c
  have h_dom : s.dom (s.composite c) = s.dom (s.right c) :=
    congrFun s.compDomProof c
  have h_cod : s.cod (s.composite c) = s.cod (s.left c) :=
    congrFun s.compCodProof c
  have h_match : s.cod (s.right c) = s.dom (s.left c) := congrFun s.compMatchProof c
  unfold unitMorMap unitMorAsHom embedQuotMorAsHom unitMorEmbed
  unfold unitTarget catToCatJudgCopr catToCatJudgObjMor catToCatJudgMor catToCatJudgObj
  unfold catToComposite unitCompMap
  unfold Mor.CatJudgMap.morMap Mor.CatJudgMap.compMap
  unfold Mor.CatJudgMap.objMorMap Mor.CatJudgMap.idCompMap
  unfold Mor.ObjMorMap.morMap
  dsimp only [adjCQD]
  conv_rhs =>
    unfold Obj.CatJudgCopr.composite Obj.CatJudgCopr.data
    unfold Obj.CatJudgObjMor.composite Obj.ObjMorCompProj.composite
    unfold Obj.CatJudgObjMor.compProj Obj.CatJudgObjMor.catJudgMor Obj.CatJudgMor.compProj
    simp only [ComposablePair.composite]
  simp only [ComposablePair.src, ComposablePair.tgt, ComposablePair.fstMor, ComposablePair.sndMor]
  simp only [unitMorAsHom, embedQuotMorAsHom, unitMorEmbed]
  unfold catJudgCoprToCat' BundledCategoryData.toCatObj
  simp only [CategoryOfData]
  unfold catJudgCoprToBundledCategoryData'
  simp only [BundledOverCategoryData.toBundledCategoryData]
  unfold catJudgCoprToBundledOverCategoryData' catJudgCoprToOverCategoryData'
  simp only [CategoryQuotientData.toOverCategoryData, OverCategoryData.toCategoryData,
    OverCategoryData.toCategoryOps, OverCategoryData.extractComp]
  simp only [CategoryQuotientData.quotCategoryOps, CategoryQuotientData.quotCompFn,
    CategoryQuotientData.bundleQuotMor, CategoryQuotientData.quotQuiver]
  simp only [catJudgCoprToCategoryQuotientData', catJudgCoprToOverQuiver]
  simp only [BundledHom.mk]
  let qm_right := D.quotMor (@FreeMor.var D.quiver (s.right c))
  let qm_left := D.quotMor (@FreeMor.var D.quiver (s.left c))
  let qm_left_transported : D.QuotMor (s.cod (s.right c)) (s.cod (s.left c)) :=
    h_match ▸ qm_left
  let qm_comp := D.quotMor (@FreeMor.var D.quiver (s.composite c))
  have h_comp_val := adjHomSet_comp_val_eq s qm_right qm_left_transported
  refine Sigma.ext h_dom ?_
  refine @sigma_heq_of_fst_eq_snd_heq s.obj s.obj
    (fun src cod => adjHomSet s src cod)
    (s.dom (s.composite c)) (s.dom (s.right c)) h_dom
    (s.cod (s.composite c)) (s.cod (s.left c)) h_cod
    _ _ ?_
  have h_pred : (fun f : (adjQuotQuiver s).MorType =>
        f.1 = s.dom (s.composite c) ∧ f.2.1 = s.cod (s.composite c)) =
      (fun f : (adjQuotQuiver s).MorType =>
        f.1 = s.dom (s.right c) ∧ f.2.1 = s.cod (s.left c)) := by
    funext f; rw [h_dom, h_cod]
  apply subtype_heq_of_val_eq h_pred
  dsimp only [adjCQD]
  let m_right_val : (adjQuotQuiver s).MorType :=
    ⟨s.dom (s.right c), s.cod (s.right c), qm_right⟩
  let m_left_val : (adjQuotQuiver s).MorType :=
    ⟨s.dom (s.left c), s.cod (s.left c), qm_left⟩
  rw [Sigma.ext_iff]
  constructor
  · exact h_dom
  · dsimp only [Sigma.snd]
    have h_comp_move : ∀ {a b b' c : D.quiver.Obj} (h : b = b')
        (g : FreeMor D.quiver b' c) (f : FreeMor D.quiver a b),
        g.comp (h ▸ f) = (cast (congrArg₂ (FreeMor D.quiver) h.symm rfl) g).comp f := by
      intro a b b' c h g f
      cases h
      rfl
    let middle : (cod : s.obj) × D.QuotMor (s.dom (s.right c)) cod :=
      ⟨s.cod (s.left c), D.quotComp qm_left_transported qm_right⟩
    have h_lhs_middle : (⟨s.cod (s.composite c),
        D.quotMor (@FreeMor.var D.quiver (s.composite c))⟩ :
        (cod : s.obj) × D.QuotMor (s.dom (s.composite c)) cod) ≍ middle := by
      refine @sigma_heq_of_fst_eq_snd_heq s.obj s.obj (fun src cod => D.QuotMor src cod)
        (s.dom (s.composite c)) (s.dom (s.right c)) h_dom
        (s.cod (s.composite c)) (s.cod (s.left c)) h_cod
        (D.quotMor (@FreeMor.var D.quiver (s.composite c)))
        (D.quotComp qm_left_transported qm_right) ?_
      apply heq_of_cast_eq (congrArg₂ D.QuotMor h_dom h_cod)
      rw [D.quotMor_cast h_dom h_cod]
      simp only [CategoryQuotientData.quotMor, CategoryQuotientData.quotComp]
      have h_transport_src : ∀ {a a' b : D.quiver.Obj} (h : a' = a)
          (f : FreeMor D.quiver a b),
          (h ▸ (⟦f⟧ : Quotient (D.freeMorSetoid a b))) =
          (⟦h ▸ f⟧ : Quotient (D.freeMorSetoid a' b)) := by
        intro a a' b h f
        cases h
        rfl
      have h_qm_left_eq : qm_left_transported =
          (⟦h_match ▸ @FreeMor.var D.quiver (s.left c)⟧ :
            Quotient (D.freeMorSetoid (s.cod (s.right c)) (s.cod (s.left c)))) := by
        simp only [qm_left_transported, qm_left, CategoryQuotientData.quotMor]
        exact h_transport_src h_match (@FreeMor.var D.quiver (s.left c))
      rw [h_qm_left_eq]
      simp only [qm_right, CategoryQuotientData.quotMor]
      rw [Quotient.lift₂_mk]
      next =>
        apply Quotient.sound
        apply CategoryQuotientData.FreeMorEquiv.symm
        convert CategoryQuotientData.FreeMorEquiv.rel h_wit using 2
        · simp only [eqRec_eq_cast]
          congr 1
      next =>
        intro a₁ a₂ b₁ b₂ h1 h2
        apply Quotient.sound
        exact CategoryQuotientData.comp_respects D h2 h1
    apply HEq.trans h_lhs_middle
    simp only [middle]
    simp only [heq_eq_eq]
    have h_middle_eq : middle = ⟨s.cod (s.left c), D.quotComp qm_left_transported qm_right⟩ := rfl
    let m_right : adjHomSet s (s.dom (s.right c)) (s.cod (s.right c)) :=
      embedQuotMorAsHom s qm_right
    let m_left : adjHomSet s (s.dom (s.left c)) (s.cod (s.left c)) :=
      embedQuotMorAsHom s qm_left
    simp only [catJudgCoprToCategoryQuotientData',
               CategoryQuotientData.quotComp, CategoryQuotientData.quotMor] at *
    symm
    unfold adjCatInst catJudgCoprToCat' BundledCategoryData.toCatObj at *
    simp only [CategoryOfData] at *
    unfold catJudgCoprToBundledCategoryData' at *
    simp only [BundledOverCategoryData.toBundledCategoryData] at *
    unfold catJudgCoprToBundledOverCategoryData' catJudgCoprToOverCategoryData' at *
    simp only [CategoryQuotientData.toOverCategoryData, OverCategoryData.toCategoryData,
      OverCategoryData.toCategoryOps, OverCategoryData.extractComp] at *
    simp only [CategoryQuotientData.quotCategoryOps, CategoryQuotientData.quotCompFn,
      CategoryQuotientData.bundleQuotMor, CategoryQuotientData.quotQuiver,
      embedQuotMorAsHom] at *
    let qm_right_transported : D.QuotMor (s.dom (s.right c)) (s.dom (s.left c)) :=
      h_match ▸ qm_right
    have h_quotComp_eq : D.quotComp qm_left qm_right_transported =
        D.quotComp qm_left_transported qm_right := by
      exact quotComp_transport_swap h_match qm_left qm_right
    apply Sigma.ext
    · exact @adjHomSet_comp_cod_eq s _ _ _ m_right _
    · have h_comp_qm := @adjHomSet_comp_quotMor_eq s _ _ _ m_right
        (h_match ▸ m_left)
      simp only
      change (@CategoryStruct.comp (catJudgCoprToCat' s) (adjCatInst s).toCategoryStruct
              _ _ _ m_right (h_match ▸ m_left)).val.snd.snd ≍
           D.quotComp qm_left_transported qm_right
      simp only [h_comp_qm]
      have h_val_eq := adjHomSet_transport_val_eq s h_match m_left
      have hb : (h_match ▸ m_left).val.fst = s.cod (s.right c) := by
        rw [h_val_eq]
        exact h_match.symm
      have hc : (h_match ▸ m_left).val.snd.fst = s.cod (s.left c) := by
        rw [h_val_eq]
        rfl
      have hg : (h_match ▸ m_left).val.snd.snd ≍ qm_left_transported := by
        have h1 := adjHomSet_transport_quotMor_heq s h_match m_left
        have h2 : qm_left_transported ≍ qm_left := by
          exact transport_heq_fst h_match qm_left
        exact h1.trans h2.symm
      refine quotComp_heq ?ha hb hc hg ?hf
      case ha => rfl
      case hf =>
        have heq_mr : m_right.val.snd.snd = qm_right := rfl
        rw [← heq_mr]
        exact transport_heq_snd _ _

/-- All naturality conditions for the unit. -/
theorem unitNaturalityAll : Mor.CatJudgNaturalityAll (unitCatJudgMap s) :=
  ⟨⟨unitNaturalityDom s, unitNaturalityCod s⟩,
   unitNaturalityIdMor s,
   ⟨unitNaturalityLeft s, unitNaturalityRight s, unitNaturalityComposite s⟩⟩

/-- The unit natural transformation η : s → Phi(L(s)).
    For each CatJudgCopr s, this embeds s into Phi(L(s)) by:
    - objMap: identity (objects are unchanged)
    - morMap: embed each f : s.mor as [var f] in the quotient category
    - idMap, compMap: similarly embed via FreeMor.var -/
def unitCatJudgNatTrans : Mor.CatJudgNatTrans s (unitTarget s) :=
  ⟨unitCatJudgMap s, unitNaturalityAll s⟩

/-! ### Counit: L ∘ Phi → id

The counit ε sends each category C to L(Phi(C)). For any C, L(Phi(C)) has:
- Objects: C (same as the original category)
- Morphisms: quotients of FreeMor on the quiver from Phi(C)

The counit interprets FreeMor trees as actual morphisms in C. -/

/-- The CatJudgCopr for category C (at aligned universes). -/
abbrev counitSource (C : Type (uAdj + 1)) [Category.{uAdj + 1} C] :
    Obj.CatJudgCopr.{uAdj + 1, uAdj + 1, uAdj + 1, uAdj + 1} :=
  catToCatJudgCopr C

/-- The OverQuiver underlying Phi(C). -/
abbrev counitQuiver (C : Type (uAdj + 1)) [Category.{uAdj + 1} C] :
    OverQuiver.{uAdj + 1, uAdj + 1} :=
  catJudgCoprToOverQuiver (counitSource C)

/-- The CategoryQuotientData for Phi(C). -/
abbrev counitCQD (C : Type (uAdj + 1)) [Category.{uAdj + 1} C] :
    CategoryQuotientData.{uAdj + 1, uAdj + 1} :=
  catJudgCoprToCategoryQuotientData' (counitSource C)

/-- Evaluate a FreeMor from Phi(C) back to an actual morphism in C.

This recursively interprets:
- var f ↦ f (the bundled morphism)
- id a ↦ BundledHom.mk a a (𝟙 a)
- comp g f ↦ composition of evaluated morphisms

Returns the morphism bundled with proofs that source/target match. -/
def counitEvalAux (C : Type (uAdj + 1)) [Category.{uAdj + 1} C] :
    {a b : C} → FreeMor (counitQuiver C) a b →
    { f : BundledHom C // f.dom = a ∧ f.cod = b }
  | _, _, .var f => ⟨f, rfl, rfl⟩
  | a, _, .id _ => ⟨BundledHom.mk a a (𝟙 a), rfl, rfl⟩
  | _, _, .comp g f =>
    let ⟨fVal, fSrc, fTgt⟩ := counitEvalAux C f
    let ⟨gVal, gSrc, gTgt⟩ := counitEvalAux C g
    let composable : fVal.cod = gVal.dom := by rw [fTgt, gSrc]
    let compHom := fVal.hom ≫ (composable ▸ gVal.hom)
    ⟨BundledHom.mk fVal.dom gVal.cod compHom, fSrc, gTgt⟩

/-- Evaluate a FreeMor to an actual morphism in C. -/
def counitEval (C : Type (uAdj + 1)) [Category.{uAdj + 1} C]
    {a b : C} (m : FreeMor (counitQuiver C) a b) : a ⟶ b :=
  let h := counitEvalAux C m
  let hsrc := h.property.1
  let htgt := h.property.2
  eqToHom hsrc.symm ≫ h.val.hom ≫ eqToHom htgt

/-- Source of counitEvalAux matches FreeMor source. -/
theorem counitEvalAux_src (C : Type (uAdj + 1)) [Category.{uAdj + 1} C]
    {a b : C} (m : FreeMor (counitQuiver C) a b) :
    (counitEvalAux C m).val.dom = a :=
  (counitEvalAux C m).property.1

/-- Target of counitEvalAux matches FreeMor target. -/
theorem counitEvalAux_tgt (C : Type (uAdj + 1)) [Category.{uAdj + 1} C]
    {a b : C} (m : FreeMor (counitQuiver C) a b) :
    (counitEvalAux C m).val.cod = b :=
  (counitEvalAux C m).property.2

/-- counitEval of a variable is the underlying morphism. -/
theorem counitEval_var (C : Type (uAdj + 1)) [Category.{uAdj + 1} C]
    (f : BundledHom C) :
    counitEval C (FreeMor.var (Q := counitQuiver C) f) = f.hom := by
  simp only [counitEval, counitEvalAux, eqToHom_refl, Category.id_comp, Category.comp_id]

/-- counitEval of identity is the identity morphism. -/
theorem counitEval_id (C : Type (uAdj + 1)) [Category.{uAdj + 1} C] (a : C) :
    counitEval C (FreeMor.id (Q := counitQuiver C) a) = 𝟙 a := by
  simp only [counitEval, counitEvalAux, BundledHom.mk, BundledHom.hom, eqToHom_refl,
    Category.id_comp, Category.comp_id]

/-- The morphism from counitEvalAux equals the underlying hom transported.
This lemma states that accessing the hom of counitEvalAux gives the
morphism that goes between the actual source and target. -/
theorem counitEvalAux_hom_eq (C : Type (uAdj + 1)) [Category.{uAdj + 1} C]
    {a b : C} (m : FreeMor (counitQuiver C) a b) :
    (counitEvalAux C m).val.hom =
      eqToHom (counitEvalAux_src C m) ≫
      (eqToHom (counitEvalAux_src C m).symm ≫ (counitEvalAux C m).val.hom ≫
        eqToHom (counitEvalAux_tgt C m)) ≫
      eqToHom (counitEvalAux_tgt C m).symm := by
  simp only [eqToHom_trans_assoc, eqToHom_trans, eqToHom_refl,
    Category.id_comp, Category.comp_id, Category.assoc]

/-- The `.dom` of `counitEvalAux` for `comp` equals the `.dom` of f's evaluation. -/
theorem counitEvalAux_comp_dom_eq (C : Type (uAdj + 1)) [Category.{uAdj + 1} C]
    {a b c : C} (g : FreeMor (counitQuiver C) b c) (f : FreeMor (counitQuiver C) a b) :
    (counitEvalAux C (FreeMor.comp g f)).val.dom = (counitEvalAux C f).val.dom := by
  match hf : counitEvalAux C f, hg : counitEvalAux C g with
  | ⟨fVal, fSrc, fTgt⟩, ⟨gVal, gSrc, gTgt⟩ =>
    simp only [counitEvalAux, BundledHom.mk, BundledHom.dom, hf, hg]

/-- The `.cod` of `counitEvalAux` for `comp` equals the `.cod` of g's evaluation. -/
theorem counitEvalAux_comp_cod_eq (C : Type (uAdj + 1)) [Category.{uAdj + 1} C]
    {a b c : C} (g : FreeMor (counitQuiver C) b c) (f : FreeMor (counitQuiver C) a b) :
    (counitEvalAux C (FreeMor.comp g f)).val.cod = (counitEvalAux C g).val.cod := by
  match hf : counitEvalAux C f, hg : counitEvalAux C g with
  | ⟨fVal, fSrc, fTgt⟩, ⟨gVal, gSrc, gTgt⟩ =>
    simp only [counitEvalAux, BundledHom.mk, BundledHom.cod]
    rw [hf, hg]

/-- The subtype value of counitEvalAux on comp relates to components. -/
theorem counitEvalAux_comp_val (C : Type (uAdj + 1)) [Category.{uAdj + 1} C]
    {a b c : C} (g : FreeMor (counitQuiver C) b c) (f : FreeMor (counitQuiver C) a b) :
    (counitEvalAux C (FreeMor.comp g f)).val =
    ⟨(counitEvalAux C f).val.dom, (counitEvalAux C g).val.cod,
     (counitEvalAux C f).val.hom ≫
      eqToHom ((counitEvalAux C f).property.2.trans (counitEvalAux C g).property.1.symm) ≫
      (counitEvalAux C g).val.hom⟩ := by
  match hf : counitEvalAux C f, hg : counitEvalAux C g with
  | ⟨fVal, fSrc, fTgt⟩, ⟨gVal, gSrc, gTgt⟩ =>
    simp only [counitEvalAux, BundledHom.mk, hf, hg]
    congr 1
    congr 1
    have h_composable : fVal.cod = gVal.dom := fTgt.trans gSrc.symm
    rw [transport_hom_dom_rev_eq_eqToHom_comp' h_composable]

/-- counitEval respects composition: eval(g ∘ f) = eval(f) ≫ eval(g).

The proof shows that evaluating a composed FreeMor gives the same result as
composing the evaluations. Both sides evaluate to the underlying morphism
composition in C, up to transport by equality proofs. -/
theorem counitEval_comp (C : Type (uAdj + 1)) [Category.{uAdj + 1} C]
    {a b c : C} (g : FreeMor (counitQuiver C) b c) (f : FreeMor (counitQuiver C) a b) :
    counitEval C (FreeMor.comp g f) = counitEval C f ≫ counitEval C g := by
  have hval := counitEvalAux_comp_val C g f
  simp only [counitEval]
  simp only [Category.assoc]
  have hhom := BundledHom.hom_eq_of_eq hval
  rw [hhom]
  simp only [BundledHom.hom, BundledHom.dom, BundledHom.cod]
  simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc]

/-- Congruence left for counitEval. -/
theorem counitEval_cong_left (C : Type (uAdj + 1)) [Category.{uAdj + 1} C]
    {a b c : C} {f g : FreeMor (counitQuiver C) a b} (h : FreeMor (counitQuiver C) b c)
    (heq : counitEval C f = counitEval C g) :
    counitEval C (FreeMor.comp h f) = counitEval C (FreeMor.comp h g) := by
  simp only [counitEval_comp]
  congr 1

/-- Congruence right for counitEval. -/
theorem counitEval_cong_right (C : Type (uAdj + 1)) [Category.{uAdj + 1} C]
    {a b c : C} {f g : FreeMor (counitQuiver C) b c} (k : FreeMor (counitQuiver C) a b)
    (heq : counitEval C f = counitEval C g) :
    counitEval C (FreeMor.comp f k) = counitEval C (FreeMor.comp g k) := by
  simp only [counitEval_comp]
  rw [heq]

/-- counitEval respects the generating relation FreeMorEquivGen. -/
theorem counitEval_resp_gen (C : Type (uAdj + 1)) [Category.{uAdj + 1} C]
    {a b : C} {f g : FreeMor (counitQuiver C) a b}
    (h : CategoryQuotientData.FreeMorEquivGen (counitCQD C) f g) :
    counitEval C f = counitEval C g := by
  match h with
  | .id_left f =>
    simp only [counitEval_comp, counitEval_id, Category.comp_id]
  | .id_right f =>
    simp only [counitEval_comp, counitEval_id, Category.id_comp]
  | .assoc h g f =>
    simp only [counitEval_comp, Category.assoc]
  | .id_witness i =>
    simp only [cast_eq]
    simp only [PLang.counitEval_var, PLang.counitEval_id]
    rfl
  | .comp_witness c =>
    simp only [cast_eq]
    simp only [PLang.counitEval_comp, PLang.counitEval_var]
    rfl
  | .cong_left h' hfg =>
    exact counitEval_cong_left C h' (counitEval_resp_gen C hfg)
  | .cong_right k hfg =>
    exact counitEval_cong_right C k (counitEval_resp_gen C hfg)

/-- counitEval respects the equivalence relation FreeMorEquiv. -/
theorem counitEval_resp (C : Type (uAdj + 1)) [Category.{uAdj + 1} C]
    {a b : C} {f g : FreeMor (counitQuiver C) a b}
    (h : CategoryQuotientData.FreeMorEquiv (counitCQD C) f g) :
    counitEval C f = counitEval C g :=
  match h with
  | .rel hr => counitEval_resp_gen C hr
  | .refl _ => rfl
  | .symm heq => (counitEval_resp C heq).symm
  | .trans heq1 heq2 => (counitEval_resp C heq1).trans (counitEval_resp C heq2)

/-! ### Counit Functor Construction

The counit ε_C : L(Phi(C)) ⥤ C is constructed by lifting counitEval through
the quotient. -/

/-- The morphism map for the counit functor, lifted from counitEval. -/
def counitFunctorMap (C : Type (uAdj + 1)) [Category.{uAdj + 1} C]
    {a b : C} (qm : (counitCQD C).QuotMor a b) : (a ⟶ b) :=
  Quotient.lift (counitEval C) (fun _ _ h => counitEval_resp C h) qm

/-- counitFunctorMap sends the identity quotient to the identity morphism. -/
theorem counitFunctorMap_id (C : Type (uAdj + 1)) [Category.{uAdj + 1} C]
    (a : C) : counitFunctorMap C ((counitCQD C).quotId a) = 𝟙 a := by
  simp only [counitFunctorMap, CategoryQuotientData.quotId,
    CategoryQuotientData.quotMor]
  simp only [Quotient.lift_mk]
  exact counitEval_id C a

/-- counitFunctorMap preserves composition. -/
theorem counitFunctorMap_comp (C : Type (uAdj + 1)) [Category.{uAdj + 1} C]
    {a b c : C} (qg : (counitCQD C).QuotMor b c) (qf : (counitCQD C).QuotMor a b) :
    counitFunctorMap C ((counitCQD C).quotComp qg qf) =
    counitFunctorMap C qf ≫ counitFunctorMap C qg := by
  induction qf using Quotient.ind with
  | _ f =>
    induction qg using Quotient.ind with
    | _ g =>
      simp only [counitFunctorMap, CategoryQuotientData.quotComp,
        CategoryQuotientData.quotMor]
      simp only [Quotient.lift_mk]
      exact counitEval_comp C g f

/-- Extract the QuotMor from an adjHomSet element. -/
def extractQuotMor (C : Type (uAdj + 1)) [Category.{uAdj + 1} C]
    {a b : (counitSource C).obj}
    (f : adjHomSet (counitSource C) a b) :
    (counitCQD C).QuotMor a b :=
  cast (congrArg₂ (counitCQD C).QuotMor f.property.1 f.property.2) f.val.2.2

/-- The counit morphism map on HomSet elements. -/
def counitHomMap (C : Type (uAdj + 1)) [Category.{uAdj + 1} C]
    {a b : C} (f : adjHomSet (counitSource C) a b) : (a ⟶ b) :=
  counitFunctorMap C (extractQuotMor C f)

/-- The identity morphism in catJudgCoprToCat' has the form quotIdFn. -/
theorem extractQuotMor_id (C : Type (uAdj + 1)) [Category.{uAdj + 1} C]
    (a : (counitSource C).obj) :
    extractQuotMor C (@CategoryStruct.id (catJudgCoprToCat' (counitSource C))
      (adjCatInst (counitSource C)).toCategoryStruct a) =
    (counitCQD C).quotId a := by
  simp only [extractQuotMor]
  unfold adjCatInst catJudgCoprToCat' BundledCategoryData.toCatObj
  simp only [CategoryOfData, CategoryStruct.id]
  unfold catJudgCoprToBundledCategoryData'
  simp only [BundledOverCategoryData.toBundledCategoryData]
  unfold catJudgCoprToBundledOverCategoryData' catJudgCoprToOverCategoryData'
  simp only [CategoryQuotientData.toOverCategoryData, OverCategoryData.toCategoryData,
    OverCategoryData.toCategoryOps]
  simp only [CategoryQuotientData.quotCategoryOps, CategoryQuotientData.quotQuiver]
  rfl

/-- Composition in catJudgCoprToCat' relates to quotComp. -/
theorem extractQuotMor_comp (C : Type (uAdj + 1)) [Category.{uAdj + 1} C]
    {a b c : (counitSource C).obj}
    (f : adjHomSet (counitSource C) a b)
    (g : adjHomSet (counitSource C) b c) :
    extractQuotMor C (@CategoryStruct.comp (catJudgCoprToCat' (counitSource C))
      (adjCatInst (counitSource C)).toCategoryStruct a b c f g) =
    (counitCQD C).quotComp (extractQuotMor C g) (extractQuotMor C f) := by
  simp only [extractQuotMor]
  unfold adjCatInst catJudgCoprToCat' BundledCategoryData.toCatObj at *
  simp only [CategoryOfData, CategoryStruct.comp] at *
  unfold catJudgCoprToBundledCategoryData' at *
  simp only [BundledOverCategoryData.toBundledCategoryData] at *
  unfold catJudgCoprToBundledOverCategoryData' catJudgCoprToOverCategoryData' at *
  simp only [CategoryQuotientData.toOverCategoryData, OverCategoryData.toCategoryData,
    OverCategoryData.toCategoryOps, OverCategoryData.extractComp] at *
  simp only [CategoryQuotientData.quotCategoryOps, CategoryQuotientData.quotQuiver] at *
  unfold CategoryQuotientData.quotCompFn counitCQD at *
  simp only [CategoryQuotientData.quotComp]
  rcases f with ⟨⟨fa, fb, fqm⟩, hfa, hfb⟩
  rcases g with ⟨⟨ga, gb, gqm⟩, hga, hgb⟩
  dsimp only at hfa hfb hga hgb ⊢
  cases hfa
  cases hfb
  cases hgb
  cases hga
  rfl

/-- The counit functor ε_C : L(Phi(C)) ⥤ C.

This evaluates formal morphisms in the quotient category back to actual
morphisms in C. The object map is identity (both categories have objects C). -/
def counitFunctor (C : Type (uAdj + 1)) [Category.{uAdj + 1} C] :
    catJudgCoprToCat' (counitSource C) ⥤ C where
  obj := id
  map := counitHomMap C
  map_id := fun a => by
    simp only [counitHomMap]
    rw [extractQuotMor_id]
    exact counitFunctorMap_id C a
  map_comp := fun {a b c} f g => by
    simp only [counitHomMap]
    rw [extractQuotMor_comp]
    exact counitFunctorMap_comp C (extractQuotMor C g) (extractQuotMor C f)

/-! ### Counit Naturality

The counit ε : L ∘ Phi → id is a natural transformation. For any functor F : C ⥤ D,
the following diagram commutes:
```
L(Phi(C)) --ε_C--> C
    |              |
L(Phi(F))          F
    |              |
    v              v
L(Phi(D)) --ε_D--> D
```
That is: F ∘ ε_C = ε_D ∘ L(Phi(F))
-/

/-- The target of L(Phi(C)) is the same as C's object type. -/
abbrev LPhiObj (C : Type (uAdj + 1)) [Category.{uAdj + 1} C] :=
  catJudgCoprToCat' (counitSource C)

/-- The functor L(Phi(F)) induced by F : C ⥤ D. -/
abbrev LPhiFunctor {C D : Type (uAdj + 1)} [Category.{uAdj + 1} C]
    [Category.{uAdj + 1} D] (F : C ⥤ D) : LPhiObj C ⥤ LPhiObj D :=
  catJudgNatTransToCatMor (functorToCatJudgNatTrans F)

/-- counitEval commutes with functor application on FreeMor.var. -/
theorem counitEval_var_functor_map {C D : Type (uAdj + 1)} [Category.{uAdj + 1} C]
    [Category.{uAdj + 1} D] (F : C ⥤ D) (f : BundledHom C) :
    F.map (counitEval C (FreeMor.var (Q := counitQuiver C) f)) =
    counitEval D (FreeMor.var (Q := counitQuiver D) (functorMapBundledHom F f)) := by
  simp only [counitEval_var, functorMapBundledHom, BundledHom.mk, BundledHom.hom]

/-- counitEval commutes with functor application on FreeMor.id. -/
theorem counitEval_id_functor_map {C D : Type (uAdj + 1)} [Category.{uAdj + 1} C]
    [Category.{uAdj + 1} D] (F : C ⥤ D) (a : C) :
    F.map (counitEval C (FreeMor.id (Q := counitQuiver C) a)) =
    counitEval D (FreeMor.id (Q := counitQuiver D) (F.obj a)) := by
  simp only [counitEval_id]
  exact F.map_id a

/-- Map a FreeMor in C to a FreeMor in D by applying F to each component.

This is the morphism-level action of L(Phi(F)), transforming formal morphisms
in C to formal morphisms in D. -/
def freeMorMapPhi {C D : Type (uAdj + 1)} [Category.{uAdj + 1} C]
    [Category.{uAdj + 1} D] (F : C ⥤ D) :
    {a b : C} → FreeMor (counitQuiver C) a b →
      FreeMor (counitQuiver D) (F.obj a) (F.obj b)
  | _, _, .var f => FreeMor.var (Q := counitQuiver D) (functorMapBundledHom F f)
  | a, _, .id _ => FreeMor.id (Q := counitQuiver D) (F.obj a)
  | _, _, .comp g fm => FreeMor.comp (freeMorMapPhi F g) (freeMorMapPhi F fm)

/-- counitEval commutes with freeMorMapPhi: evaluating after mapping equals
mapping then evaluating. This is the main naturality lemma for counitEval. -/
theorem counitEval_freeMorMapPhi {C D : Type (uAdj + 1)} [Category.{uAdj + 1} C]
    [Category.{uAdj + 1} D] (F : C ⥤ D) :
    {a b : C} → (m : FreeMor (counitQuiver C) a b) →
      counitEval D (freeMorMapPhi F m) = F.map (counitEval C m)
  | _, _, .var f => (counitEval_var_functor_map F f).symm
  | a, _, .id _ => by simp only [freeMorMapPhi, counitEval_id, F.map_id]
  | _, _, .comp g f => by
    simp only [freeMorMapPhi, counitEval_comp]
    rw [counitEval_freeMorMapPhi F f, counitEval_freeMorMapPhi F g]
    exact (F.map_comp _ _).symm

/-! ### Counit Naturality

The counit ε : L ∘ Φ → Id is natural: for any functor F : C ⥤ D,
  L(Φ(F)) ≫ ε_D = ε_C ≫ F

We prove this by showing the morphism-level equality using counitEval_freeMorMapPhi,
then lifting through the quotient. -/

/-- The quiver morphism underlying functorToCatJudgNatTrans. -/
abbrev functorToQuiverMor {C D : Type (uAdj + 1)} [Category.{uAdj + 1} C]
    [Category.{uAdj + 1} D] (F : C ⥤ D) :
    OverQuiverMorphism (counitQuiver C) (counitQuiver D) :=
  catJudgNatTransToOverQuiverMor (functorToCatJudgNatTrans F)

/-- freeMorMapPhi agrees with FreeMor.mapQuiver for the functor case. -/
theorem freeMorMapPhi_eq_mapQuiver {C D : Type (uAdj + 1)} [Category.{uAdj + 1} C]
    [Category.{uAdj + 1} D] (F : C ⥤ D) :
    {a b : C} → (m : FreeMor (counitQuiver C) a b) →
      freeMorMapPhi F m = FreeMor.mapQuiver (functorToQuiverMor F) m
  | _, _, .var f => by
    simp only [freeMorMapPhi, FreeMor.mapQuiver,
      catJudgNatTransToOverQuiverMor, functorToCatJudgNatTrans,
      functorToCatJudgMap]
  | _, _, .id _ => rfl
  | _, _, .comp g f => by
    simp only [freeMorMapPhi, FreeMor.mapQuiver]
    rw [freeMorMapPhi_eq_mapQuiver F f, freeMorMapPhi_eq_mapQuiver F g]

/-- The functor L(Phi(F)) applied to counitFunctor maps. -/
abbrev LPhiFunctor' (C D : Type (uAdj + 1)) [Category.{uAdj + 1} C]
    [Category.{uAdj + 1} D] (F : C ⥤ D) :
    (LPhiObj C) ⥤ (LPhiObj D) :=
  catJudgNatTransToCatMor (functorToCatJudgNatTrans F)

/-- The counit naturality at the morphism level for FreeMor. -/
theorem counit_naturality_freeMor {C D : Type (uAdj + 1)} [Category.{uAdj + 1} C]
    [Category.{uAdj + 1} D] (F : C ⥤ D) {a b : C}
    (m : FreeMor (counitQuiver C) a b) :
    counitEval D (FreeMor.mapQuiver (functorToQuiverMor F) m) =
    F.map (counitEval C m) := by
  rw [← freeMorMapPhi_eq_mapQuiver F m]
  exact counitEval_freeMorMapPhi F m

/-- The CategoryQuotientMorphism for a functor F between categories. -/
abbrev functorToCategoryQuotientMorphism {C D : Type (uAdj + 1)}
    [Category.{uAdj + 1} C] [Category.{uAdj + 1} D] (F : C ⥤ D) :
    CategoryQuotientMorphism (counitCQD C) (counitCQD D) :=
  catJudgNatTransToCategoryQuotientMorphism (functorToCatJudgNatTrans F)

/-- Counit naturality at the quotient level: applying L(Phi(F)) then ε_D
equals applying ε_C then F. -/
theorem counit_naturality_quot {C D : Type (uAdj + 1)} [Category.{uAdj + 1} C]
    [Category.{uAdj + 1} D] (F : C ⥤ D) {a b : C}
    (qm : (counitCQD C).QuotMor a b) :
    counitFunctorMap D ((functorToCategoryQuotientMorphism F).quotMapMor qm) =
    F.map (counitFunctorMap C qm) := by
  induction qm using Quotient.ind with
  | _ m =>
    simp only [CategoryQuotientMorphism.quotMapMor, CategoryQuotientData.quotMor,
      counitFunctorMap, Quotient.lift_mk]
    exact counit_naturality_freeMor F m

/-- The composition L(Phi(F)) ≫ ε_D maps morphisms correctly on adjHomSet. -/
theorem LPhiFunctor_counit_map {C D : Type (uAdj + 1)} [Category.{uAdj + 1} C]
    [Category.{uAdj + 1} D] (F : C ⥤ D) {a b : C}
    (m : adjHomSet (counitSource C) a b) :
    (counitFunctor D).map ((LPhiFunctor' C D F).map m) =
    F.map ((counitFunctor C).map m) := by
  rcases m with ⟨⟨ma, mb, qm⟩, ha, hb⟩
  subst ha hb
  simp only [counitFunctor, counitHomMap, extractQuotMor, cast_eq, counitFunctorMap]
  -- Unfold the functor layers
  simp only [catJudgNatTransToCatMor, BundledCategoryData.functorToCat,
    catJudgNatTransToFunctorData, toBundledCategoryData_map,
    catJudgNatTransToOverFunctorData, catJudgNatTransToQuotQuiverMor,
    catJudgCoprToOverCategoryData', CategoryQuotientData.toOverCategoryData,
    catJudgNatTransToCategoryQuotientMorphism,
    CategoryQuotientData.bundleQuotMor, CategoryQuotientData.quotQuiver]
  exact counit_naturality_quot F qm

/-- The composition Φ ⋙ L : Cat → Cat at matched universe levels. -/
abbrev PhiL : CategoryTheory.Cat.{uAdj + 1, uAdj + 1} ⥤
    CategoryTheory.Cat.{uAdj + 1, uAdj + 1} :=
  PhiFunctor_PLang.{uAdj, uAdj} ⋙ LFunctor_PLang.{uAdj, uAdj}

/-- The counit natural transformation ε : Φ ⋙ L → 𝟭 Cat.

For each category C, the component ε_C : L(Φ(C)) ⥤ C evaluates the free
category on C's quiver (with category condition witnesses) back to C itself. -/
def counitNT : PhiL.{uAdj} ⟶ 𝟭 (CategoryTheory.Cat.{uAdj + 1, uAdj + 1}) where
  app := fun C => counitFunctor C.α
  naturality := fun {C D} F => by
    simp only [CategoryTheory.Cat.comp_eq_comp, CategoryTheory.Functor.id_obj,
      CategoryTheory.Functor.id_map]
    have h_obj : ∀ x, (PhiL.map F ⋙ counitFunctor ↑D).obj x =
        (counitFunctor ↑C ⋙ F).obj x := fun _ => rfl
    refine CategoryTheory.Functor.ext h_obj ?_
    intro x y f
    simp only [CategoryTheory.Functor.comp_obj, CategoryTheory.Functor.comp_map,
      eqToHom_refl, Category.id_comp, Category.comp_id]
    exact LPhiFunctor_counit_map F f

/-! ### Unit Natural Transformation

The unit η : 𝟭 CatJudgCopr → L ⋙ Φ embeds each CatJudgCopr into Φ(L(s)). -/

/-- The composition L ⋙ Φ : CatJudgCopr → CatJudgCopr at matched universe levels. -/
abbrev LPhi : Obj.CatJudgCopr.{uAdj + 1, uAdj + 1, uAdj + 1, uAdj + 1} ⥤
    Obj.CatJudgCopr.{uAdj + 1, uAdj + 1, uAdj + 1, uAdj + 1} :=
  LFunctor_PLang.{uAdj, uAdj} ⋙ PhiFunctor_PLang.{uAdj, uAdj}

/-- LPhi.obj s equals unitTarget s. -/
theorem LPhi_obj_eq_unitTarget (s : Obj.CatJudgCopr.{uAdj + 1, uAdj + 1, uAdj + 1, uAdj + 1}) :
    LPhi.obj s = unitTarget s := rfl

/-- Lemma for unit naturality: .fst equality for the left morphism component.

Shows that unitMorAsHom values have equal .fst after bundleQuotMor and quotMapMor.
Uses naturality of f to establish the domain equality. -/
theorem unit_naturality_left_fst_eq
    (s t : Obj.CatJudgCopr.{uAdj + 1, uAdj + 1, uAdj + 1, uAdj + 1})
    (f : Mor.CatJudgNatTrans s t)
    (c : s.data.catJudgObj.toObjMorCompObj.compType)
    (h_left : f.morMap (s.left c) = t.left (f.compMap c))
    (h_dom_l : f.objMap (s.dom (s.left c)) = t.dom (f.morMap (s.left c))) :
    (unitMorAsHom t (t.left (f.compMap c))).val.fst =
      ((catJudgCoprToCategoryQuotientData' t).bundleQuotMor
        ((catJudgNatTransToCategoryQuotientMorphism f).quotMapMor
          (unitMorAsHom s (s.left c)).val.snd.snd)).fst := by
  -- LHS: t.dom (t.left (f.compMap c))
  -- RHS: f.objMap (s.dom (s.left c))
  -- By h_left and h_dom_l, these are equal
  simp only [unitMorAsHom_val, CategoryQuotientData.bundleQuotMor,
    catJudgNatTransToCategoryQuotientMorphism, CategoryQuotientMorphism.quotMapMor,
    CategoryQuotientData.quotMor, Quotient.lift_mk]
  -- Goal: t.dom (t.left (f.compMap c)) = f.objMap (s.dom (s.left c))
  rw [← h_left]
  exact h_dom_l.symm

end AdjunctionStructure

end PLang

end GebLean
