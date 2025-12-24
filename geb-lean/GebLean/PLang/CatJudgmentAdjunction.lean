import GebLean.PLang.CatJudgment
import GebLean.Utilities.Category
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

See `docs/plang-category-judgments.md` for mathematical background.
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

end PLang

end GebLean
