import GebLean.PLang.CatJudgment
import GebLean.CatJudgmentAdjunction
import GebLean.Utilities.Category
import GebLean.Utilities.Equalities
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Adjunction.Reflective

/-!
# Category-Copresheaf Adjunction for PLang

This file implements the adjunction between small categories and category-
judgment copresheaves in PLang form with flexible universe levels.

The adjunction consists of:
- An embedding functor Phi : Cat.{v,u} → CatJudgCopr that sends a category
  to its associated copresheaf
- A reflection functor L : CatJudgCopr → Cat that sends a copresheaf to the
  free category on its quiver, quotiented by identity and composition relations

## Universe flexibility

The PLang formulation allows flexible universe levels:
- Cat.{v, u} has objects in Type u and morphisms in Type v
- CatJudgCopr.{u, v, w, x} has four independent universe parameters for
  element levels (the types themselves are at u+1, v+1, w+1, x+1)

The embedding Phi : Cat.{u, u} → CatJudgCopr.{u, u, u, u} maps a category
with objects and morphisms at level u to a copresheaf where all component
types have elements at level u.

## Main definitions

### Embedding Functor Phi

- `toPLangCatJudgCopr`: Convert a category (as OverCategoryData) to a PLang
  CatJudgCopr

### Reflection Functor L

(Defined in future phases)
-/

namespace GebLean

open CategoryTheory PLang

universe v u

/-! ## Embedding Functor Phi: OverCategoryData → CatJudgCopr

Given a category (as OverCategoryData), we construct a CatJudgCopr. -/

section EmbeddingPhi

/-- Construct the CatJudgObj from an OverCategoryData.
    - Object type: Q.Obj
    - Morphism type: Q.MorType
    - Identity witness type: Q.Obj (each object witnesses its identity)
    - Composition witness type: Q.ComposablePairsType -/
def toPLangCatJudgObj (Q : OverQuiver.{u, u}) :
    Obj.CatJudgObj.{u + 1, u + 1, u + 1, u + 1} :=
  ((Q.Obj, Q.MorType), (Q.Obj, Q.ComposablePairsType))

/-- Construct the CatJudgMor from an OverCategoryData.
    This provides the domain/codomain functions, identity morphism function,
    and composition projections. -/
def toPLangCatJudgMor {Q : OverQuiver.{u, u}} (C : OverCategoryData Q) :
    Obj.CatJudgMor.{u, u, u, u} (toPLangCatJudgObj Q) :=
  -- domCod: (dom, cod)
  ((Q.src, Q.tgt),
   -- idMor: object → identity morphism
   (C.idFn,
    -- compProj: (left, right, composite)
    (fun p => p.val.2,  -- left morphism (applied second)
     fun p => p.val.1,  -- right morphism (applied first)
     fun p => C.compFn p)))  -- composite

/-- Construct the CatJudgObjMor from an OverCategoryData.
    This bundles the object and morphism data. -/
def toPLangCatJudgObjMor {Q : OverQuiver.{u, u}} (C : OverCategoryData Q) :
    Obj.CatJudgObjMor.{u, u, u, u} :=
  ⟨toPLangCatJudgObj Q, toPLangCatJudgMor C⟩

/-- Prove the identity endomorphism condition: dom ∘ idMor = cod ∘ idMor.
    This holds because identity morphisms are endomorphisms. -/
theorem toPLang_endo {Q : OverQuiver.{u, u}} (C : OverCategoryData Q) :
    Obj.ObjMorIdObjMorEndo.{u, u, u} (toPLangCatJudgObjMor C).toObjMorIdObjMor := by
  unfold Obj.ObjMorIdObjMorEndo
  funext a
  simp only [Function.comp_apply]
  unfold toPLangCatJudgObjMor toPLangCatJudgMor toPLangCatJudgObj
  simp only [Obj.CatJudgObjMor.toObjMorIdObjMor, Obj.CatJudgObjMor.catJudgObj,
    Obj.CatJudgObj.toObjMorIdObj, Obj.ObjMorIdObjMor.dom, Obj.ObjMorIdMor.dom,
    Obj.ObjMorMor.dom, Obj.ObjMorIdObjMor.idMor, Obj.ObjMorIdMor.idMor,
    Obj.CatJudgMor.idMor, Obj.ObjMorIdObjMor.cod, Obj.ObjMorIdMor.cod,
    Obj.ObjMorMor.cod]
  exact (C.id_src a).trans (C.id_tgt a).symm

/-- Prove the composability condition: cod ∘ right = dom ∘ left.
    This holds by definition of composable pairs. -/
theorem toPLang_compMatch {Q : OverQuiver.{u, u}} (C : OverCategoryData Q) :
    Obj.ObjMorCompObjMorMatch.{u, u, u}
      (toPLangCatJudgObjMor C).toObjMorCompObjMor := by
  unfold Obj.ObjMorCompObjMorMatch
  funext p
  simp only [Function.comp_apply]
  unfold toPLangCatJudgObjMor toPLangCatJudgMor toPLangCatJudgObj
  simp only [Obj.CatJudgObjMor.toObjMorCompObjMor, Obj.ObjMorCompObjMor.cod,
    Obj.ObjMorCompMor.cod, Obj.ObjMorMor.cod, Obj.ObjMorCompObjMor.right,
    Obj.ObjMorCompMor.right, Obj.ObjMorCompProj.right,
    Obj.ObjMorCompObjMor.dom, Obj.ObjMorCompMor.dom, Obj.ObjMorMor.dom,
    Obj.ObjMorCompObjMor.left, Obj.ObjMorCompMor.left,
    Obj.ObjMorCompProj.left, Obj.CatJudgObjMor.catJudgObj,
    Obj.CatJudgObj.toObjMorCompObj]
  exact p.property

/-- Prove the domain preservation condition: dom ∘ composite = dom ∘ right.
    This holds because the composite has the same domain as the first
    morphism applied. -/
theorem toPLang_compDom {Q : OverQuiver.{u, u}} (C : OverCategoryData Q) :
    Obj.ObjMorCompObjMorCompDom.{u, u, u}
      (toPLangCatJudgObjMor C).toObjMorCompObjMor := by
  unfold Obj.ObjMorCompObjMorCompDom
  funext p
  simp only [Function.comp_apply]
  unfold toPLangCatJudgObjMor toPLangCatJudgMor toPLangCatJudgObj
  simp only [Obj.CatJudgObjMor.toObjMorCompObjMor, Obj.ObjMorCompObjMor.dom,
    Obj.ObjMorCompMor.dom, Obj.ObjMorMor.dom, Obj.ObjMorCompObjMor.composite,
    Obj.ObjMorCompMor.composite, Obj.ObjMorCompProj.composite,
    Obj.ObjMorCompObjMor.right, Obj.ObjMorCompMor.right,
    Obj.ObjMorCompProj.right, Obj.CatJudgObjMor.catJudgObj,
    Obj.CatJudgObj.toObjMorCompObj]
  exact C.comp_src p

/-- Prove the codomain preservation condition: cod ∘ composite = cod ∘ left.
    This holds because the composite has the same codomain as the second
    morphism applied. -/
theorem toPLang_compCod {Q : OverQuiver.{u, u}} (C : OverCategoryData Q) :
    Obj.ObjMorCompObjMorCompCod.{u, u, u}
      (toPLangCatJudgObjMor C).toObjMorCompObjMor := by
  unfold Obj.ObjMorCompObjMorCompCod
  funext p
  simp only [Function.comp_apply]
  unfold toPLangCatJudgObjMor toPLangCatJudgMor toPLangCatJudgObj
  simp only [Obj.CatJudgObjMor.toObjMorCompObjMor, Obj.ObjMorCompObjMor.cod,
    Obj.ObjMorCompMor.cod, Obj.ObjMorMor.cod, Obj.ObjMorCompObjMor.composite,
    Obj.ObjMorCompMor.composite, Obj.ObjMorCompProj.composite,
    Obj.ObjMorCompObjMor.left, Obj.ObjMorCompMor.left,
    Obj.ObjMorCompProj.left, Obj.CatJudgObjMor.catJudgObj,
    Obj.CatJudgObj.toObjMorCompObj]
  exact C.comp_tgt p

/-- Prove all composition conditions. -/
theorem toPLang_compCond {Q : OverQuiver.{u, u}} (C : OverCategoryData Q) :
    Obj.ObjMorCompObjMorCond.{u, u, u}
      (toPLangCatJudgObjMor C).toObjMorCompObjMor :=
  ⟨toPLang_compMatch C, toPLang_compDom C, toPLang_compCod C⟩

/-- Prove all category judgment conditions. -/
theorem toPLang_cond {Q : OverQuiver.{u, u}} (C : OverCategoryData Q) :
    Obj.CatJudgObjMorCond.{u, u, u, u} (toPLangCatJudgObjMor C) :=
  ⟨toPLang_endo C, toPLang_compCond C⟩

/-- Convert an OverCategoryData to a PLang CatJudgCopr.
    This is the embedding functor Phi on objects. -/
def toPLangCatJudgCopr {Q : OverQuiver.{u, u}} (C : OverCategoryData Q) :
    Obj.CatJudgCopr.{u, u, u, u} :=
  ⟨toPLangCatJudgObjMor C, toPLang_cond C⟩

end EmbeddingPhi

/-! ## Functoriality of Phi

The embedding extends to a functor from OverCategoryData to CatJudgCopr. -/

section PhiFunctoriality

variable {Q₁ Q₂ : OverQuiver.{u, u}}
variable {C₁ : OverCategoryData Q₁} {C₂ : OverCategoryData Q₂}

/-- Construct the CatJudgMap from an OverFunctorData.
    This maps all components (objects, morphisms, identity witnesses,
    composition witnesses) through the functor. -/
def toPLangCatJudgMap (F : OverFunctorData C₁ C₂) :
    Mor.CatJudgMap (toPLangCatJudgCopr C₁) (toPLangCatJudgCopr C₂) :=
  -- objMorMap: (objMap, morMap)
  ((F.objFn, F.morFn),
   -- idCompMap: (idMap, compMap)
   (F.objFn,
    fun p =>
      let composableProof : Q₂.tgt (F.morFn p.val.1) = Q₂.src (F.morFn p.val.2) :=
        (F.tgt_comm p.val.1).trans
          ((congrArg F.objFn p.property).trans (F.src_comm p.val.2).symm)
      ⟨(F.morFn p.val.1, F.morFn p.val.2), composableProof⟩))

/-- Prove the domain naturality condition. -/
theorem toPLang_dom (F : OverFunctorData C₁ C₂) :
    Mor.CatJudgNaturalityDom (toPLangCatJudgMap F) := by
  unfold Mor.CatJudgNaturalityDom
  funext f
  simp only [Function.comp_apply, Mor.CatJudgMap.objMap,
    Mor.CatJudgMap.objMorMap, Mor.ObjMorMap.objMap, Mor.CatJudgMap.morMap,
    Mor.ObjMorMap.morMap]
  unfold toPLangCatJudgMap
  simp only [Obj.CatJudgCopr.dom, Obj.CatJudgObjMor.dom,
    toPLangCatJudgCopr, toPLangCatJudgObjMor,
    toPLangCatJudgMor, toPLangCatJudgObj, Obj.ObjMorMor.dom]
  exact (F.src_comm f).symm

/-- Prove the codomain naturality condition. -/
theorem toPLang_cod (F : OverFunctorData C₁ C₂) :
    Mor.CatJudgNaturalityCod (toPLangCatJudgMap F) := by
  unfold Mor.CatJudgNaturalityCod
  funext f
  simp only [Function.comp_apply, Mor.CatJudgMap.objMap,
    Mor.CatJudgMap.objMorMap, Mor.ObjMorMap.objMap, Mor.CatJudgMap.morMap,
    Mor.ObjMorMap.morMap]
  unfold toPLangCatJudgMap
  simp only [Obj.CatJudgCopr.cod, Obj.CatJudgObjMor.cod,
    toPLangCatJudgCopr, toPLangCatJudgObjMor,
    toPLangCatJudgMor, toPLangCatJudgObj, Obj.ObjMorMor.cod]
  exact (F.tgt_comm f).symm

/-- Prove the identity morphism naturality condition. -/
theorem toPLang_idMor (F : OverFunctorData C₁ C₂) :
    Mor.CatJudgNaturalityIdMor (toPLangCatJudgMap F) := by
  unfold Mor.CatJudgNaturalityIdMor
  funext a
  simp only [Function.comp_apply, Mor.CatJudgMap.morMap,
    Mor.CatJudgMap.objMorMap, Mor.ObjMorMap.morMap, Mor.CatJudgMap.idMap,
    Mor.CatJudgMap.idCompMap]
  unfold toPLangCatJudgMap
  simp only [Obj.CatJudgCopr.idMor, Obj.CatJudgObjMor.idMor,
    toPLangCatJudgCopr, toPLangCatJudgObjMor,
    toPLangCatJudgMor, toPLangCatJudgObj,
    Obj.CatJudgMor.idMor, Obj.CatJudgMor.idMorCompProj]
  exact F.map_id a

/-- Prove the left naturality condition. -/
theorem toPLang_left (F : OverFunctorData C₁ C₂) :
    Mor.CatJudgNaturalityLeft (toPLangCatJudgMap F) := by
  unfold Mor.CatJudgNaturalityLeft
  funext p
  simp only [Function.comp_apply, Mor.CatJudgMap.morMap,
    Mor.CatJudgMap.objMorMap, Mor.ObjMorMap.morMap, Mor.CatJudgMap.compMap,
    Mor.CatJudgMap.idCompMap]
  unfold toPLangCatJudgMap
  simp only [Obj.CatJudgCopr.left, Obj.CatJudgObjMor.left,
    toPLangCatJudgCopr, toPLangCatJudgObjMor,
    toPLangCatJudgMor, toPLangCatJudgObj, Obj.ObjMorCompProj.left]

/-- Prove the right naturality condition. -/
theorem toPLang_right (F : OverFunctorData C₁ C₂) :
    Mor.CatJudgNaturalityRight (toPLangCatJudgMap F) := by
  unfold Mor.CatJudgNaturalityRight
  funext p
  simp only [Function.comp_apply, Mor.CatJudgMap.morMap,
    Mor.CatJudgMap.objMorMap, Mor.ObjMorMap.morMap, Mor.CatJudgMap.compMap,
    Mor.CatJudgMap.idCompMap]
  unfold toPLangCatJudgMap
  simp only [Obj.CatJudgCopr.right, Obj.CatJudgObjMor.right,
    toPLangCatJudgCopr, toPLangCatJudgObjMor,
    toPLangCatJudgMor, toPLangCatJudgObj, Obj.ObjMorCompProj.right]

/-- Prove the composite naturality condition. -/
theorem toPLang_composite (F : OverFunctorData C₁ C₂) :
    Mor.CatJudgNaturalityComposite (toPLangCatJudgMap F) := by
  unfold Mor.CatJudgNaturalityComposite
  funext p
  simp only [Function.comp_apply, Mor.CatJudgMap.morMap,
    Mor.CatJudgMap.objMorMap, Mor.ObjMorMap.morMap, Mor.CatJudgMap.compMap,
    Mor.CatJudgMap.idCompMap]
  unfold toPLangCatJudgMap
  simp only [Obj.CatJudgCopr.composite, Obj.CatJudgObjMor.composite,
    toPLangCatJudgCopr, toPLangCatJudgObjMor,
    toPLangCatJudgMor, toPLangCatJudgObj, Obj.ObjMorCompProj.composite]
  exact F.map_comp p

/-- Prove all naturality conditions for the CatJudgMap. -/
theorem toPLang_naturality (F : OverFunctorData C₁ C₂) :
    Mor.CatJudgNaturalityAll (toPLangCatJudgMap F) :=
  ⟨⟨toPLang_dom F, toPLang_cod F⟩,
   toPLang_idMor F,
   ⟨toPLang_left F, toPLang_right F, toPLang_composite F⟩⟩

/-- Convert an OverFunctorData to a PLang CatJudgNatTrans.
    This is the embedding functor Phi on morphisms. -/
def toPLangCatJudgNatTrans (F : OverFunctorData C₁ C₂) :
    Mor.CatJudgNatTrans (toPLangCatJudgCopr C₁) (toPLangCatJudgCopr C₂) :=
  ⟨toPLangCatJudgMap F, toPLang_naturality F⟩

/-- Φ preserves identity: Φ(id_C) = id_{Φ(C)}. -/
theorem toPLangCatJudgNatTrans_id {Q : OverQuiver.{u, u}} (C : OverCategoryData Q) :
    toPLangCatJudgNatTrans (OverFunctorData.id C) =
    Cat.CatJudgNatTrans.id (toPLangCatJudgCopr C) := by
  apply Subtype.ext
  rfl

/-- Φ preserves composition: Φ(G ∘ F) = Φ(G) ∘ Φ(F). -/
theorem toPLangCatJudgNatTrans_comp {Q₁ Q₂ Q₃ : OverQuiver.{u, u}}
    {C₁ : OverCategoryData Q₁} {C₂ : OverCategoryData Q₂} {C₃ : OverCategoryData Q₃}
    (F : OverFunctorData C₁ C₂) (G : OverFunctorData C₂ C₃) :
    toPLangCatJudgNatTrans (F.comp G) =
    Cat.CatJudgNatTrans.comp (toPLangCatJudgNatTrans F) (toPLangCatJudgNatTrans G) := by
  apply Subtype.ext
  rfl

end PhiFunctoriality

/-! ## Reflection Functor L: CatJudgCopr → OverCategoryData

Given a PLang CatJudgCopr, we construct a category by:
1. Extracting the quiver (Obj, Mor with dom/cod)
2. Forming free morphisms (binary trees of compositions)
3. Quotienting by category laws and the copresheaf relations -/

section ReflectionL

/-- Data for constructing the free category from a CatJudgCopr. This bundles
    the underlying quiver with the identity and composition witness data needed
    to define the quotient equivalence relation. -/
structure PLangQuotientData.{w} where
  /-- The underlying quiver with objects and morphisms. -/
  quiver : OverQuiver.{w, w}
  /-- The type of identity witnesses. -/
  IdWitness : Type w
  /-- The type of composition witnesses. -/
  CompWitness : Type w
  /-- Get the identity morphism for a witness. -/
  idMor : IdWitness → quiver.MorType
  /-- Identity morphisms are endomorphisms. -/
  idEndo : ∀ i, quiver.src (idMor i) = quiver.tgt (idMor i)
  /-- Get the left morphism of a composition witness. -/
  left : CompWitness → quiver.MorType
  /-- Get the right morphism of a composition witness. -/
  right : CompWitness → quiver.MorType
  /-- Get the composite morphism. -/
  composite : CompWitness → quiver.MorType
  /-- Left and right are composable. -/
  compMatch : ∀ c, quiver.tgt (right c) = quiver.src (left c)
  /-- Domain of composite equals domain of right. -/
  compDom : ∀ c, quiver.src (composite c) = quiver.src (right c)
  /-- Codomain of composite equals codomain of left. -/
  compCod : ∀ c, quiver.tgt (composite c) = quiver.tgt (left c)

/-- Convert a CatJudgCopr to PLangQuotientData. -/
def toPLangQuotientData (C : Obj.CatJudgCopr.{u, u, u, u}) :
    PLangQuotientData.{u} where
  quiver := {
    Obj := C.obj
    MorType := C.mor
    src := C.dom
    tgt := C.cod
  }
  IdWitness := C.idType
  CompWitness := C.compType
  idMor := C.idMor
  idEndo := fun i => congrFun C.endoProof i
  left := C.left
  right := C.right
  composite := C.composite
  compMatch := fun c => congrFun C.compMatchProof c
  compDom := fun c => congrFun C.compDomProof c
  compCod := fun c => congrFun C.compCodProof c

/-- Free morphisms in a quiver for PLang quotient construction.
    These form binary trees where:
    - `var f` injects a base morphism from the quiver
    - `id a` is an identity morphism at object a
    - `comp g f` is the composition g . f (f first, then g)

    The source and target are tracked in the type indices. -/
inductive PFreeMor (Q : OverQuiver.{u, u}) : Q.Obj → Q.Obj → Type u where
  /-- Inject a morphism from the base quiver. -/
  | var (f : Q.MorType) : PFreeMor Q (Q.src f) (Q.tgt f)
  /-- Identity morphism at an object. -/
  | id (a : Q.Obj) : PFreeMor Q a a
  /-- Composition: g . f (f first, then g). -/
  | comp {a b c : Q.Obj} (g : PFreeMor Q b c) (f : PFreeMor Q a b) : PFreeMor Q a c

namespace PFreeMor

variable {Q : OverQuiver.{u, u}}

/-- The size of a free morphism (number of constructors). -/
def size : {a b : Q.Obj} → PFreeMor Q a b → Nat
  | _, _, var _ => 1
  | _, _, id _ => 1
  | _, _, comp g f => 1 + g.size + f.size

/-- Casting the target of the right morphism in a composition.
    Composition with a target-cast right morphism can be rewritten by
    moving the cast to the left morphism's source:
    comp g (h ▸ f) = comp (h.symm ▸ g) f
    where the cast on f changes its target from b to b', and the
    cast on g changes its source from b' to b. -/
theorem comp_cast_tgt_right {a b b' c : Q.Obj} (h : b = b')
    (f : PFreeMor Q a b) (g : PFreeMor Q b' c) :
    comp g (cast (congrArg (PFreeMor Q a) h) f) =
    comp (cast (congrArg (fun x => PFreeMor Q x c) h.symm) g) f := by
  subst h
  rfl

/-- Casting the target of the right morphism using ▸ notation.
    This is equivalent to comp_cast_tgt_right but uses ▸ instead of cast. -/
@[simp]
theorem comp_subst_tgt_right {a b b' c : Q.Obj} (h : b = b')
    (f : PFreeMor Q a b) (g : PFreeMor Q b' c) :
    comp g (h ▸ f) = comp (h.symm ▸ g) f := by
  subst h
  rfl

/-- Casting the source of the left morphism in a composition.
    Composition with a source-cast left morphism can be rewritten by
    moving the cast to the right morphism's target:
    comp (h ▸ g) f = comp g (h.symm ▸ f)
    where the cast on g changes its source from b to b', and the
    cast on f changes its target from b' to b. -/
theorem comp_cast_src_left {a b b' c : Q.Obj} (h : b = b')
    (f : PFreeMor Q a b') (g : PFreeMor Q b c) :
    comp (cast (congrArg (fun x => PFreeMor Q x c) h) g) f =
    comp g (cast (congrArg (PFreeMor Q a) h.symm) f) := by
  subst h
  rfl

/-- A subst on source equals a cast for PFreeMor.
    h ▸ f = cast (congrArg (fun s => PFreeMor Q s b) h) f -/
theorem subst_src_eq_cast {a a' b : Q.Obj} (h : a = a')
    (f : PFreeMor Q a b) :
    (h ▸ f : PFreeMor Q a' b) = cast (congrArg (fun s => PFreeMor Q s b) h) f := by
  subst h
  rfl

/-- Subst of var equals cast of var when the proofs are compatible.
    This handles converting between ▸ and cast for PFreeMor.var. -/
theorem subst_var_eq_cast_var {m : Q.MorType} {a' : Q.Obj}
    (h : Q.src m = a') :
    (h ▸ var m : PFreeMor Q a' (Q.tgt m)) =
    cast (congrArg (fun s => PFreeMor Q s (Q.tgt m)) h) (var m) := by
  subst h
  rfl

end PFreeMor

/-! ## Equivalence Relations on Free Morphisms

The equivalence relation on free morphisms is generated by:
1. Category axioms: left identity, right identity, associativity
2. Copresheaf relations: identity and composition witnesses
3. Congruence: equivalence propagates through composition -/

namespace PLangQuotientData

variable (D : PLangQuotientData.{u})

/-- Generating relations for equivalence on free morphisms.
    These include category axioms, copresheaf-specified relations, and
    congruence through composition. -/
inductive FreeMorEquivGen : {a b : D.quiver.Obj} →
    PFreeMor D.quiver a b → PFreeMor D.quiver a b → Prop where
  /-- Left identity: id . f ~ f -/
  | id_left {a b : D.quiver.Obj} (f : PFreeMor D.quiver a b) :
      FreeMorEquivGen (PFreeMor.comp (PFreeMor.id b) f) f
  /-- Right identity: f . id ~ f -/
  | id_right {a b : D.quiver.Obj} (f : PFreeMor D.quiver a b) :
      FreeMorEquivGen (PFreeMor.comp f (PFreeMor.id a)) f
  /-- Associativity: h . (g . f) ~ (h . g) . f -/
  | assoc {a b c d : D.quiver.Obj}
      (h : PFreeMor D.quiver c d) (g : PFreeMor D.quiver b c)
      (f : PFreeMor D.quiver a b) :
      FreeMorEquivGen (PFreeMor.comp h (PFreeMor.comp g f))
                      (PFreeMor.comp (PFreeMor.comp h g) f)
  /-- Identity witness: var(idMor i) ~ id(dom(idMor i))
      The variable morphism for an identity witness is equivalent to the
      identity at that object. -/
  | id_witness (i : D.IdWitness) :
      FreeMorEquivGen
        (cast (by rw [D.idEndo i]) (PFreeMor.var (D.idMor i)))
        (PFreeMor.id (D.quiver.src (D.idMor i)))
  /-- Composition witness: var(left c) . var(right c) ~ var(composite c)
      The composition of the left and right variable morphisms is equivalent
      to the variable morphism for the composite. -/
  | comp_witness (c : D.CompWitness) :
      FreeMorEquivGen
        (PFreeMor.comp
          (cast (by rw [D.compMatch c]) (PFreeMor.var (D.left c)))
          (PFreeMor.var (D.right c)))
        (cast (by rw [D.compDom c, D.compCod c]) (PFreeMor.var (D.composite c)))
  /-- Left congruence: if f ~ g then h . f ~ h . g -/
  | cong_left {a b c : D.quiver.Obj}
      {f g : PFreeMor D.quiver a b} (h : PFreeMor D.quiver b c) :
      FreeMorEquivGen f g →
      FreeMorEquivGen (PFreeMor.comp h f) (PFreeMor.comp h g)
  /-- Right congruence: if f ~ g then f . k ~ g . k -/
  | cong_right {a b c : D.quiver.Obj}
      {f g : PFreeMor D.quiver b c} (k : PFreeMor D.quiver a b) :
      FreeMorEquivGen f g →
      FreeMorEquivGen (PFreeMor.comp f k) (PFreeMor.comp g k)

/-- The full equivalence relation on free morphisms, defined as the
    equivalence closure of FreeMorEquivGen. -/
inductive FreeMorEquiv : {a b : D.quiver.Obj} →
    PFreeMor D.quiver a b → PFreeMor D.quiver a b → Prop where
  /-- Include the generating relation. -/
  | rel {a b : D.quiver.Obj} {f g : PFreeMor D.quiver a b} :
      FreeMorEquivGen D f g → FreeMorEquiv f g
  /-- Reflexivity. -/
  | refl {a b : D.quiver.Obj} (f : PFreeMor D.quiver a b) : FreeMorEquiv f f
  /-- Symmetry. -/
  | symm {a b : D.quiver.Obj} {f g : PFreeMor D.quiver a b} :
      FreeMorEquiv f g → FreeMorEquiv g f
  /-- Transitivity. -/
  | trans {a b : D.quiver.Obj} {f g h : PFreeMor D.quiver a b} :
      FreeMorEquiv f g → FreeMorEquiv g h → FreeMorEquiv f h

/-- FreeMorEquiv is an equivalence relation. -/
theorem FreeMorEquiv.isEquivalence {a b : D.quiver.Obj} :
    Equivalence (FreeMorEquiv D (a := a) (b := b)) where
  refl := FreeMorEquiv.refl
  symm := FreeMorEquiv.symm
  trans := FreeMorEquiv.trans

/-- FreeMorEquiv is preserved by casting indices. -/
theorem FreeMorEquiv.cast {a b a' b' : D.quiver.Obj}
    {f g : PFreeMor D.quiver a b}
    (ha : a = a') (hb : b = b')
    (eq : FreeMorEquiv D f g) :
    FreeMorEquiv D
      (cast (congrArg₂ (PFreeMor D.quiver) ha hb) f)
      (cast (congrArg₂ (PFreeMor D.quiver) ha hb) g) := by
  subst ha hb
  simp only [congrArg₂, cast_eq]
  exact eq

/-- Left congruence for FreeMorEquiv. -/
theorem FreeMorEquiv.cong_left {a b c : D.quiver.Obj}
    {f g : PFreeMor D.quiver a b} (h : PFreeMor D.quiver b c)
    (eq : FreeMorEquiv D f g) :
    FreeMorEquiv D (PFreeMor.comp h f) (PFreeMor.comp h g) := by
  induction eq with
  | rel hr => exact FreeMorEquiv.rel (FreeMorEquivGen.cong_left h hr)
  | refl _ => exact FreeMorEquiv.refl _
  | symm _ ih => exact FreeMorEquiv.symm ih
  | trans _ _ ih1 ih2 => exact FreeMorEquiv.trans ih1 ih2

/-- Right congruence for FreeMorEquiv. -/
theorem FreeMorEquiv.cong_right {a b c : D.quiver.Obj}
    {f g : PFreeMor D.quiver b c} (k : PFreeMor D.quiver a b)
    (eq : FreeMorEquiv D f g) :
    FreeMorEquiv D (PFreeMor.comp f k) (PFreeMor.comp g k) := by
  induction eq with
  | rel hr => exact FreeMorEquiv.rel (FreeMorEquivGen.cong_right k hr)
  | refl _ => exact FreeMorEquiv.refl _
  | symm _ ih => exact FreeMorEquiv.symm ih
  | trans _ _ ih1 ih2 => exact FreeMorEquiv.trans ih1 ih2

/-- The setoid on free morphisms induced by FreeMorEquiv. -/
def freeMorSetoid (a b : D.quiver.Obj) : Setoid (PFreeMor D.quiver a b) where
  r := FreeMorEquiv D
  iseqv := FreeMorEquiv.isEquivalence D

/-- The quotient type of free morphisms. -/
def QuotMor (a b : D.quiver.Obj) : Type u :=
  Quotient (freeMorSetoid D a b)

/-- Lift a free morphism to the quotient. -/
def quotMor {a b : D.quiver.Obj} (f : PFreeMor D.quiver a b) : QuotMor D a b :=
  Quotient.mk (freeMorSetoid D a b) f

/-- The quotient notation equals quotMor. -/
@[simp]
theorem quotMk_eq_quotMor {a b : D.quiver.Obj} (f : PFreeMor D.quiver a b) :
    (⟦f⟧ : QuotMor D a b) = quotMor D f := rfl

/-- Quotient.lift applied to quotMor equals the function applied to the element. -/
@[simp]
theorem Quotient_lift_quotMor {a b : D.quiver.Obj}
    {β : Sort*} (f : PFreeMor D.quiver a b → β)
    (h : ∀ x y, FreeMorEquiv D x y → f x = f y)
    (x : PFreeMor D.quiver a b) :
    Quotient.lift f h (quotMor D x) = f x := rfl

/-- Composition respects the equivalence relation. -/
theorem comp_respects {a b c : D.quiver.Obj}
    {f₁ f₂ : PFreeMor D.quiver a b} {g₁ g₂ : PFreeMor D.quiver b c}
    (hf : FreeMorEquiv D f₁ f₂) (hg : FreeMorEquiv D g₁ g₂) :
    FreeMorEquiv D (PFreeMor.comp g₁ f₁) (PFreeMor.comp g₂ f₂) :=
  FreeMorEquiv.trans (FreeMorEquiv.cong_left D g₁ hf)
                     (FreeMorEquiv.cong_right D f₂ hg)

/-- Composition descends to the quotient. -/
def quotComp {a b c : D.quiver.Obj} :
    QuotMor D b c → QuotMor D a b → QuotMor D a c :=
  Quotient.lift₂ (fun g f => quotMor D (PFreeMor.comp g f))
    (fun _ _ _ _ hg hf => Quotient.sound (comp_respects D hf hg))

/-- The identity quotient morphism. -/
def quotId (a : D.quiver.Obj) : QuotMor D a a :=
  quotMor D (PFreeMor.id a)

/-- Left identity law for quotient composition. -/
theorem quotComp_id_left {a b : D.quiver.Obj} (f : QuotMor D a b) :
    quotComp D (quotId D b) f = f := by
  induction f using Quotient.ind with
  | _ f => exact Quotient.sound (FreeMorEquiv.rel (FreeMorEquivGen.id_left f))

/-- Right identity law for quotient composition. -/
theorem quotComp_id_right {a b : D.quiver.Obj} (f : QuotMor D a b) :
    quotComp D f (quotId D a) = f := by
  induction f using Quotient.ind with
  | _ f => exact Quotient.sound (FreeMorEquiv.rel (FreeMorEquivGen.id_right f))

/-- Associativity law for quotient composition. -/
theorem quotComp_assoc {a b c d : D.quiver.Obj}
    (h : QuotMor D c d) (g : QuotMor D b c) (f : QuotMor D a b) :
    quotComp D h (quotComp D g f) = quotComp D (quotComp D h g) f := by
  induction h using Quotient.ind with
  | _ h =>
    induction g using Quotient.ind with
    | _ g =>
      induction f using Quotient.ind with
      | _ f =>
        exact Quotient.sound (FreeMorEquiv.rel (FreeMorEquivGen.assoc h g f))

/-- Cast commutes with quotMor: casting a quotient element equals
    the quotient of the casted underlying element. -/
theorem quotMor_cast {a b c : D.quiver.Obj} (h : b = c)
    (f : PFreeMor D.quiver a b) :
    cast (congrArg (QuotMor D a) h) (quotMor D f) =
    quotMor D (cast (congrArg (PFreeMor D.quiver a) h) f) := by
  subst h
  rfl

/-- HEq for quotMor when targets differ by equality and underlying terms
    are related via cast and FreeMorEquiv. -/
theorem quotMor_heq_of_cast_equiv {a b c : D.quiver.Obj} (hbc : b = c)
    (f : PFreeMor D.quiver a b) (g : PFreeMor D.quiver a c)
    (hfg : FreeMorEquiv D (cast (congrArg (PFreeMor D.quiver a) hbc) f) g) :
    HEq (quotMor D f) (quotMor D g) := by
  subst hbc
  simp only [cast_eq] at hfg
  exact heq_of_eq (Quotient.sound hfg)

/-- HEq for quotMor when both source and target differ by equalities and
    underlying terms are related via double cast and FreeMorEquiv.
    This generalizes quotMor_heq_of_cast_equiv to handle changes in both
    endpoints. -/
theorem quotMor_heq_of_both_cast_equiv {a a' b b' : D.quiver.Obj}
    (ha : a = a') (hb : b = b')
    (f : PFreeMor D.quiver a b) (g : PFreeMor D.quiver a' b')
    (hfg : FreeMorEquiv D (ha ▸ hb ▸ f) g) :
    HEq (quotMor D f) (quotMor D g) := by
  subst ha hb
  exact heq_of_eq (Quotient.sound hfg)

/-- Casting at the quotient level equals quotient of cast.
    Version using ▸ notation. -/
@[simp]
theorem quotMor_subst_eq {a b c : D.quiver.Obj} (h : b = c)
    (f : PFreeMor D.quiver a b) :
    h ▸ (quotMor D f) = quotMor D (h ▸ f) := by
  subst h
  rfl

/-- quotComp of quotMor values equals quotMor of composition. -/
@[simp]
theorem quotComp_quotMor {a b c : D.quiver.Obj}
    (f : PFreeMor D.quiver a b) (g : PFreeMor D.quiver b c) :
    quotComp D (quotMor D g) (quotMor D f) = quotMor D (PFreeMor.comp g f) := rfl

/-- The OverQuiver for the quotient category. Objects are the same as the
    original quiver, but morphisms are bundled quotient morphisms. -/
def quotQuiver : OverQuiver.{u, u} where
  Obj := D.quiver.Obj
  MorType := Σ (a b : D.quiver.Obj), QuotMor D a b
  src := fun m => m.1
  tgt := fun m => m.2.1

/-- Bundle a quotient morphism into the sigma type. -/
def bundleQuotMor {a b : D.quiver.Obj} (f : QuotMor D a b) :
    D.quotQuiver.MorType :=
  ⟨a, b, f⟩

/-- The identity function for quotient morphisms. -/
def quotIdFn : D.quiver.Obj → D.quotQuiver.MorType :=
  fun a => ⟨a, a, quotId D a⟩

/-- The composition function for quotient morphisms.
    Given a composable pair (g, f) where tgt g = src f, compose as f . g
    (first g, then f), returning a morphism from src g to tgt f. -/
def quotCompFn : D.quotQuiver.ComposablePairsType → D.quotQuiver.MorType :=
  fun ⟨⟨g, f⟩, heq⟩ =>
    let g' : QuotMor D g.1 g.2.1 := g.2.2
    let f' : QuotMor D f.1 f.2.1 := f.2.2
    let heq' : g.2.1 = f.1 := heq
    let g'' : QuotMor D g.1 f.1 := heq' ▸ g'
    ⟨g.1, f.2.1, quotComp D f' g''⟩

/-- Identity morphism has same source and target. -/
theorem quotIdFn_src (a : D.quiver.Obj) :
    D.quotQuiver.src (quotIdFn D a) = a := rfl

/-- Identity morphism has same source and target. -/
theorem quotIdFn_tgt (a : D.quiver.Obj) :
    D.quotQuiver.tgt (quotIdFn D a) = a := rfl

/-- Composition has source = source of right morphism. -/
theorem quotCompFn_src (p : D.quotQuiver.ComposablePairsType) :
    D.quotQuiver.src (quotCompFn D p) = D.quotQuiver.src p.val.1 := rfl

/-- Composition has target = target of left morphism. -/
theorem quotCompFn_tgt (p : D.quotQuiver.ComposablePairsType) :
    D.quotQuiver.tgt (quotCompFn D p) = D.quotQuiver.tgt p.val.2 := rfl

/-- The quotient category operations. -/
def quotCategoryOps : OverCategoryOps D.quotQuiver where
  idFn := quotIdFn D
  compFn := quotCompFn D
  id_src := quotIdFn_src D
  id_tgt := quotIdFn_tgt D
  comp_src := quotCompFn_src D
  comp_tgt := quotCompFn_tgt D

/-- Left identity law for the quotient category: id . f = f -/
theorem quot_id_comp (f : D.quotQuiver.MorType) :
    quotCompFn D ⟨(quotIdFn D (D.quotQuiver.src f), f),
      (quotCategoryOps D).id_tgt (D.quotQuiver.src f)⟩ = f := by
  obtain ⟨a, b, qf⟩ := f
  simp only [quotIdFn, quotCompFn, quotQuiver]
  congr 2
  exact quotComp_id_right D qf

/-- Right identity law for the quotient category: f . id = f -/
theorem quot_comp_id (f : D.quotQuiver.MorType) :
    quotCompFn D ⟨(f, quotIdFn D (D.quotQuiver.tgt f)),
      ((quotCategoryOps D).id_src (D.quotQuiver.tgt f)).symm⟩ = f := by
  obtain ⟨a, b, qf⟩ := f
  simp only [quotIdFn, quotCompFn, quotQuiver]
  congr 2
  exact quotComp_id_left D qf

/-- Associativity for the quotient category: (h . g) . f = h . (g . f) -/
theorem quot_assoc (t : D.quotQuiver.ComposableTriplesType) :
    let fg := quotCompFn D ⟨(t.val.1, t.val.2.1), t.property.1⟩
    let gh := quotCompFn D ⟨(t.val.2.1, t.val.2.2), t.property.2⟩
    quotCompFn D ⟨(fg, t.val.2.2),
      ((quotCategoryOps D).comp_tgt ⟨(t.val.1, t.val.2.1), t.property.1⟩).trans
        t.property.2⟩ =
    quotCompFn D ⟨(t.val.1, gh),
      t.property.1.trans
        ((quotCategoryOps D).comp_src ⟨(t.val.2.1, t.val.2.2), t.property.2⟩).symm⟩
        := by
  obtain ⟨⟨h, g, f⟩, heq1, heq2⟩ := t
  obtain ⟨ah, bh, qh⟩ := h
  obtain ⟨ag, bg, qg⟩ := g
  obtain ⟨af, bf, qf⟩ := f
  cases heq1
  cases heq2
  simp only [quotCompFn, quotQuiver]
  congr 2
  exact quotComp_assoc D qf qg qh

/-- The quotient forms an OverCategoryData. This is the reflection functor L
    on objects. -/
def toOverCategoryData : OverCategoryData D.quotQuiver where
  toOverCategoryOps := quotCategoryOps D
  id_comp := quot_id_comp D
  comp_id := quot_comp_id D
  assoc := quot_assoc D

end PLangQuotientData

/-- The reflection functor L on objects: take a CatJudgCopr to an
    OverCategoryData via free morphisms and quotient. -/
def reflectionL (C : Obj.CatJudgCopr.{u, u, u, u}) :
    OverCategoryData (toPLangQuotientData C).quotQuiver :=
  (toPLangQuotientData C).toOverCategoryData

/-! ## Free Morphism Mapping

When we have a quiver morphism, we can lift it to map free morphisms. -/

/-- Map a free morphism through a quiver morphism.
    This is the functor from PFreeMor Q₁ to PFreeMor Q₂ induced by a
    quiver morphism. -/
def PFreeMor.mapQuiver {Q₁ Q₂ : OverQuiver.{u, u}} (F : OverQuiverMorphism Q₁ Q₂)
    {a b : Q₁.Obj} (m : PFreeMor Q₁ a b) :
    PFreeMor Q₂ (F.objFn a) (F.objFn b) :=
  match m with
  | .var f => F.src_comm f ▸ F.tgt_comm f ▸ .var (F.morFn f)
  | .id _ => .id _
  | .comp g f => .comp (mapQuiver F g) (mapQuiver F f)

namespace PFreeMor

variable {Q₁ Q₂ : OverQuiver.{u, u}}

/-- mapQuiver preserves identity morphisms. -/
theorem mapQuiver_id (F : OverQuiverMorphism Q₁ Q₂) (a : Q₁.Obj) :
    mapQuiver F (.id a) = .id (F.objFn a) := rfl

/-- mapQuiver preserves composition. -/
theorem mapQuiver_comp (F : OverQuiverMorphism Q₁ Q₂)
    {a b c : Q₁.Obj}
    (g : PFreeMor Q₁ b c) (f : PFreeMor Q₁ a b) :
    mapQuiver F (.comp g f) = .comp (mapQuiver F g) (mapQuiver F f) := rfl

/-- mapQuiver with identity OverQuiverMorphism is identity. -/
theorem mapQuiver_overQuiverId {Q : OverQuiver.{u, u}} {a b : Q.Obj}
    (fm : PFreeMor Q a b) :
    mapQuiver (OverQuiverMorphism.id Q) fm = fm := by
  induction fm with
  | var f => rfl
  | id x => rfl
  | comp g f ihg ihf =>
    simp only [mapQuiver] at ihg ihf ⊢
    rw [ihg, ihf]

/-- mapQuiver applied to a casted var equals a cast of a var.
    This is used for proving functoriality of mapQuiver. -/
theorem mapQuiver_cast_var_overQuiver {Q₁ Q₂ : OverQuiver.{u, u}}
    (F : OverQuiverMorphism Q₁ Q₂)
    (m : Q₁.MorType)
    {a' b' : Q₁.Obj} (ha : Q₁.src m = a') (hb : Q₁.tgt m = b') :
    mapQuiver F (cast (congrArg₂ (PFreeMor Q₁) ha hb) (.var m)) =
    cast (congrArg₂ (PFreeMor Q₂)
      ((F.src_comm m).trans (congrArg F.objFn ha))
      ((F.tgt_comm m).trans (congrArg F.objFn hb)))
      (.var (F.morFn m)) := by
  subst ha hb
  simp only [congrArg₂, cast_eq, mapQuiver, subst_subst_eq_cast]

/-- mapQuiver with composed OverQuiverMorphisms equals composition of
    mapQuiver applications. -/
theorem mapQuiver_quiverMorComp {Q₁ Q₂ Q₃ : OverQuiver.{u, u}}
    (F : OverQuiverMorphism Q₁ Q₂) (G : OverQuiverMorphism Q₂ Q₃)
    {a b : Q₁.Obj}
    (fm : PFreeMor Q₁ a b) :
    mapQuiver (F.comp G) fm = mapQuiver G (mapQuiver F fm) := by
  induction fm with
  | var f =>
    simp only [mapQuiver, OverQuiverMorphism.comp, Function.comp_apply,
      subst_subst_eq_cast]
    rw [mapQuiver_cast_var_overQuiver G (F.morFn f) (F.src_comm f) (F.tgt_comm f)]
  | id x => rfl
  | comp g f ihg ihf =>
    simp only [mapQuiver] at ihg ihf ⊢
    rw [ihg, ihf]

/-- Two OverQuiverMorphisms with the same functions are equal. -/
theorem OverQuiverMorphism.eq_of_objFn_morFn {Q₁ Q₂ : OverQuiver.{u, u}}
    (F G : OverQuiverMorphism Q₁ Q₂)
    (hobjFn : F.objFn = G.objFn)
    (hmorFn : F.morFn = G.morFn) : F = G := by
  ext
  · exact congrFun hobjFn _
  · exact congrFun hmorFn _

end PFreeMor

/-! ## Morphisms between PLangQuotientData

A morphism between PLangQuotientData structures is compatible with
the id and comp witnesses. This is the structure induced by a
CatJudgNatTrans between the corresponding copresheaves. -/

/-- A morphism between PLangQuotientData structures that is compatible with
    the id and comp witnesses. -/
structure PLangQuotientMorphism (D₁ D₂ : PLangQuotientData.{u}) where
  /-- The underlying quiver morphism. -/
  quiverMor : OverQuiverMorphism D₁.quiver D₂.quiver
  /-- Map on identity witnesses. -/
  idWitMap : D₁.IdWitness → D₂.IdWitness
  /-- Map on composition witnesses. -/
  compWitMap : D₁.CompWitness → D₂.CompWitness
  /-- Identity morphisms are preserved. -/
  idMor_comm : ∀ i, quiverMor.morFn (D₁.idMor i) = D₂.idMor (idWitMap i)
  /-- Right components of composition are preserved. -/
  compRight_comm : ∀ c, quiverMor.morFn (D₁.right c) = D₂.right (compWitMap c)
  /-- Left components of composition are preserved. -/
  compLeft_comm : ∀ c, quiverMor.morFn (D₁.left c) = D₂.left (compWitMap c)
  /-- Composite morphisms are preserved. -/
  compComposite_comm :
    ∀ c, quiverMor.morFn (D₁.composite c) = D₂.composite (compWitMap c)

namespace PLangQuotientMorphism

variable {D₁ D₂ : PLangQuotientData.{u}}

/-- Identity PLangQuotientMorphism. -/
def id (D : PLangQuotientData.{u}) : PLangQuotientMorphism D D where
  quiverMor := OverQuiverMorphism.id D.quiver
  idWitMap := _root_.id
  compWitMap := _root_.id
  idMor_comm := fun _ => rfl
  compRight_comm := fun _ => rfl
  compLeft_comm := fun _ => rfl
  compComposite_comm := fun _ => rfl

variable (F : PLangQuotientMorphism D₁ D₂)

/-- Two substs (▸) equal one cast for two-argument types. -/
theorem subst_subst_eq_cast {A : Type*} {G : A → A → Type*}
    {a a' b b' : A} (ha : a = a') (hb : b = b') (x : G a b) :
    ha ▸ hb ▸ x = cast (congrArg₂ G ha hb) x := by
  subst ha hb
  rfl

/-- A subst on target equals a cast for PFreeMor.
    h ▸ f = cast (congrArg (PFreeMor Q a) h) f -/
theorem subst_tgt_eq_cast {Q : OverQuiver.{u, u}} {a b b' : Q.Obj} (h : b = b')
    (f : PFreeMor Q a b) :
    (h ▸ f : PFreeMor Q a b') = cast (congrArg (PFreeMor Q a) h) f := by
  subst h
  rfl

/-- mapQuiver of a casted var. -/
theorem mapQuiver_cast_var
    (m : D₁.quiver.MorType)
    {a' b' : D₁.quiver.Obj} (ha : D₁.quiver.src m = a') (hb : D₁.quiver.tgt m = b') :
    PFreeMor.mapQuiver F.quiverMor
      (cast (congrArg₂ (PFreeMor D₁.quiver) ha hb) (.var m)) =
    cast (congrArg₂ (PFreeMor D₂.quiver)
      ((F.quiverMor.src_comm m).trans (congrArg F.quiverMor.objFn ha))
      ((F.quiverMor.tgt_comm m).trans (congrArg F.quiverMor.objFn hb)))
      (.var (F.quiverMor.morFn m)) := by
  subst ha hb
  simp only [congrArg₂, cast_eq, PFreeMor.mapQuiver, subst_subst_eq_cast]

/-- mapQuiver of a casted var using explicit index equalities.
    This works with any cast proof (by proof irrelevance). -/
theorem mapQuiver_cast_var_gen
    (m : D₁.quiver.MorType)
    {a' b' : D₁.quiver.Obj}
    (ha : D₁.quiver.src m = a')
    (hb : D₁.quiver.tgt m = b')
    (h : PFreeMor D₁.quiver (D₁.quiver.src m) (D₁.quiver.tgt m) =
         PFreeMor D₁.quiver a' b') :
    PFreeMor.mapQuiver F.quiverMor (cast h (.var m)) =
    cast (congrArg₂ (PFreeMor D₂.quiver)
      ((F.quiverMor.src_comm m).trans (congrArg F.quiverMor.objFn ha))
      ((F.quiverMor.tgt_comm m).trans (congrArg F.quiverMor.objFn hb)))
      (.var (F.quiverMor.morFn m)) := by
  subst ha hb
  simp only [congrArg₂, cast_eq, PFreeMor.mapQuiver, subst_subst_eq_cast]

/-- If two morphisms are equal, their vars under cast are equal. -/
theorem cast_var_eq {Q : OverQuiver.{u, u}} {a b : Q.Obj}
    {m₁ m₂ : Q.MorType} (hm : m₁ = m₂)
    (h₁ : Q.src m₁ = a) (h₁' : Q.tgt m₁ = b)
    (h₂ : Q.src m₂ = a) (h₂' : Q.tgt m₂ = b) :
    cast (congrArg₂ (PFreeMor Q) h₁ h₁') (.var m₁) =
    cast (congrArg₂ (PFreeMor Q) h₂ h₂') (.var m₂) := by
  subst hm
  rfl

/-- FreeMor.id x equals FreeMor.id y when x = y. -/
theorem id_eq {Q : OverQuiver.{u, u}} {x y : Q.Obj} (h : x = y) :
    (PFreeMor.id x : PFreeMor Q x x) =
    cast (congrArg₂ (PFreeMor Q) h.symm h.symm) (PFreeMor.id y) := by
  subst h
  rfl

/-- Composition distributes over casts: (cast h g).comp (cast h' f) = cast h'' (g.comp f). -/
theorem comp_cast_eq {Q : OverQuiver.{u, u}}
    {a b c a' b' c' : Q.Obj}
    (f : PFreeMor Q a b) (g : PFreeMor Q b c)
    (ha : a = a') (hb : b = b') (hc : c = c') :
    (cast (congrArg₂ (PFreeMor Q) hb hc) g).comp
      (cast (congrArg₂ (PFreeMor Q) ha hb) f) =
    cast (congrArg₂ (PFreeMor Q) ha hc) (g.comp f) := by
  subst ha hb hc
  rfl

/-- mapQuiver of a cast term equals a cast of mapQuiver. -/
theorem mapQuiver_cast
    {a b a' b' : D₁.quiver.Obj}
    (m : PFreeMor D₁.quiver a b)
    (ha : a = a') (hb : b = b') :
    PFreeMor.mapQuiver F.quiverMor (cast (congrArg₂ (PFreeMor D₁.quiver) ha hb) m) =
    cast (congrArg₂ (PFreeMor D₂.quiver)
      (congrArg F.quiverMor.objFn ha) (congrArg F.quiverMor.objFn hb))
      (PFreeMor.mapQuiver F.quiverMor m) := by
  subst ha hb
  rfl

/-- mapQuiver of a casted term using any cast proof.
    Works with any cast proof via proof irrelevance. -/
theorem mapQuiver_cast'
    {a b a' b' : D₁.quiver.Obj}
    (m : PFreeMor D₁.quiver a b)
    (ha : a = a') (hb : b = b')
    (hcast : PFreeMor D₁.quiver a b = PFreeMor D₁.quiver a' b') :
    PFreeMor.mapQuiver F.quiverMor (cast hcast m) =
    cast (congrArg₂ (PFreeMor D₂.quiver)
      (congrArg F.quiverMor.objFn ha) (congrArg F.quiverMor.objFn hb))
      (PFreeMor.mapQuiver F.quiverMor m) := by
  subst ha hb
  rfl

/-- mapQuiver of var using explicit source/target facts. -/
theorem mapQuiver_var_cast
    (m : D₁.quiver.MorType)
    {a' b' : D₁.quiver.Obj}
    (ha : D₁.quiver.src m = a') (hb : D₁.quiver.tgt m = b')
    (hcast : PFreeMor D₁.quiver (D₁.quiver.src m) (D₁.quiver.tgt m) =
             PFreeMor D₁.quiver a' b') :
    PFreeMor.mapQuiver F.quiverMor (cast hcast (PFreeMor.var m)) =
    cast (congrArg₂ (PFreeMor D₂.quiver)
      (F.quiverMor.src_comm m |>.trans (congrArg F.quiverMor.objFn ha))
      (F.quiverMor.tgt_comm m |>.trans (congrArg F.quiverMor.objFn hb)))
      (PFreeMor.var (F.quiverMor.morFn m)) := by
  subst ha hb
  simp only [cast_eq, PFreeMor.mapQuiver, subst_subst_eq_cast]

/-- mapQuiver respects the generating equivalence relation. -/
theorem mapQuiver_respects_gen
    {a b : D₁.quiver.Obj}
    {f g : PFreeMor D₁.quiver a b}
    (h : D₁.FreeMorEquivGen f g) :
    D₂.FreeMorEquiv
      (PFreeMor.mapQuiver F.quiverMor f)
      (PFreeMor.mapQuiver F.quiverMor g) := by
  induction h with
  | id_left fm =>
    simp only [PFreeMor.mapQuiver]
    exact .rel (.id_left _)
  | id_right fm =>
    simp only [PFreeMor.mapQuiver]
    exact .rel (.id_right _)
  | assoc h' g' f' =>
    simp only [PFreeMor.mapQuiver]
    exact .rel (.assoc _ _ _)
  | id_witness i =>
    -- D₂ witness at mapped index gives the corresponding relation
    have h_wit := PLangQuotientData.FreeMorEquivGen.id_witness (D := D₂) (F.idWitMap i)
    -- Index equality: D₂.src (D₂.idMor (F.idWitMap i)) = F.objFn (D₁.src (D₁.idMor i))
    have h_idx : D₂.quiver.src (D₂.idMor (F.idWitMap i)) =
        F.quiverMor.objFn (D₁.quiver.src (D₁.idMor i)) := by
      rw [← F.idMor_comm, F.quiverMor.src_comm]
    -- Transport the D₂ witness to match our indices
    have h_wit' := PLangQuotientData.FreeMorEquiv.cast (D := D₂)
      h_idx h_idx (.rel h_wit)
    simp only [PFreeMor.mapQuiver]
    convert h_wit' using 1
    · -- LHS: mapQuiver (cast _ (var idMor_D₁)) = cast _ (cast _ (var idMor_D₂))
      rw [mapQuiver_var_cast F (D₁.idMor i) rfl (D₁.idEndo i).symm]
      simp only [cast_cast]
      -- h_idx gives src equality; for tgt we use D₂.idEndo to get tgt = src = target
      have h_idx_tgt : D₂.quiver.tgt (D₂.idMor (F.idWitMap i)) =
          F.quiverMor.objFn (D₁.quiver.src (D₁.idMor i)) :=
        (D₂.idEndo (F.idWitMap i)).symm.trans h_idx
      exact cast_var_eq (F.idMor_comm i)
        (F.quiverMor.src_comm (D₁.idMor i) |>.trans rfl)
        (F.quiverMor.tgt_comm (D₁.idMor i) |>.trans
          (congrArg F.quiverMor.objFn (D₁.idEndo i).symm))
        h_idx
        h_idx_tgt
    · -- RHS: id (F.objFn ...) = cast _ (id (D₂.src ...))
      exact id_eq h_idx.symm
  | comp_witness c =>
    -- D₂ witness at mapped index gives the corresponding relation
    have h_wit := PLangQuotientData.FreeMorEquivGen.comp_witness (D := D₂) (F.compWitMap c)
    -- Index equalities relating D₂ indices to F.objFn D₁ indices
    have h_src : D₂.quiver.src (D₂.right (F.compWitMap c)) =
        F.quiverMor.objFn (D₁.quiver.src (D₁.right c)) := by
      rw [← F.compRight_comm, F.quiverMor.src_comm]
    have h_tgt : D₂.quiver.tgt (D₂.left (F.compWitMap c)) =
        F.quiverMor.objFn (D₁.quiver.tgt (D₁.left c)) := by
      rw [← F.compLeft_comm, F.quiverMor.tgt_comm]
    -- Transport the D₂ witness to match our indices
    have h_wit' := PLangQuotientData.FreeMorEquiv.cast (D := D₂)
      h_src h_tgt (.rel h_wit)
    simp only [PFreeMor.mapQuiver]
    convert h_wit' using 1
    · -- LHS: composition of mapped vars equals casted composition of D₂ vars
      -- First simplify the left var using mapQuiver_var_cast
      rw [mapQuiver_var_cast F (D₁.left c) (D₁.compMatch c).symm rfl]
      simp only [subst_subst_eq_cast]
      -- Use morphism equalities
      have hL := F.compLeft_comm c
      have hR := F.compRight_comm c
      -- Use HEq for vars with dependent types (via Eq.rec)
      have hvarL_heq : HEq (PFreeMor.var (F.quiverMor.morFn (D₁.left c)))
          (PFreeMor.var (D₂.left (F.compWitMap c))) :=
        hL ▸ HEq.refl _
      have hvarR_heq : HEq (PFreeMor.var (F.quiverMor.morFn (D₁.right c)))
          (PFreeMor.var (D₂.right (F.compWitMap c))) :=
        hR ▸ HEq.refl _
      -- Source/target equalities for objects
      have hsrc_L := F.quiverMor.src_comm (D₁.left c)
      have htgt_L := F.quiverMor.tgt_comm (D₁.left c)
      have hsrc_R := F.quiverMor.src_comm (D₁.right c)
      have htgt_R := F.quiverMor.tgt_comm (D₁.right c)
      -- All objects are related
      grind
    · -- RHS: composite equality
      rw [mapQuiver_var_cast F (D₁.composite c) (D₁.compDom c) (D₁.compCod c)]
      simp only [cast_cast]
      have hsrc : D₂.quiver.src (F.quiverMor.morFn (D₁.composite c)) =
          F.quiverMor.objFn (D₁.quiver.src (D₁.right c)) :=
        (F.quiverMor.src_comm _).trans (congrArg _ (D₁.compDom c))
      have htgt : D₂.quiver.tgt (F.quiverMor.morFn (D₁.composite c)) =
          F.quiverMor.objFn (D₁.quiver.tgt (D₁.left c)) :=
        (F.quiverMor.tgt_comm _).trans (congrArg _ (D₁.compCod c))
      have hsrc' : D₂.quiver.src (D₂.composite (F.compWitMap c)) =
          F.quiverMor.objFn (D₁.quiver.src (D₁.right c)) :=
        (congrArg D₂.quiver.src (F.compComposite_comm c).symm).trans hsrc
      have htgt' : D₂.quiver.tgt (D₂.composite (F.compWitMap c)) =
          F.quiverMor.objFn (D₁.quiver.tgt (D₁.left c)) :=
        (congrArg D₂.quiver.tgt (F.compComposite_comm c).symm).trans htgt
      exact cast_var_eq (F.compComposite_comm c) hsrc htgt hsrc' htgt'
  | cong_left h' _ ih =>
    simp only [PFreeMor.mapQuiver]
    exact PLangQuotientData.FreeMorEquiv.cong_left D₂
      (PFreeMor.mapQuiver F.quiverMor h') ih
  | cong_right k _ ih =>
    simp only [PFreeMor.mapQuiver]
    exact PLangQuotientData.FreeMorEquiv.cong_right D₂
      (PFreeMor.mapQuiver F.quiverMor k) ih

/-- mapQuiver respects the full equivalence relation. -/
theorem mapQuiver_respects_equiv
    {a b : D₁.quiver.Obj}
    {f g : PFreeMor D₁.quiver a b}
    (h : D₁.FreeMorEquiv f g) :
    D₂.FreeMorEquiv
      (PFreeMor.mapQuiver F.quiverMor f)
      (PFreeMor.mapQuiver F.quiverMor g) := by
  induction h with
  | rel hr => exact mapQuiver_respects_gen F hr
  | refl _ => exact .refl _
  | symm _ ih => exact .symm ih
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2

/-- mapQuiver descends to the quotient. -/
def quotMapMor
    {a b : D₁.quiver.Obj} (m : D₁.QuotMor a b) :
    D₂.QuotMor (F.quiverMor.objFn a) (F.quiverMor.objFn b) :=
  Quotient.lift
    (fun fm => D₂.quotMor (PFreeMor.mapQuiver F.quiverMor fm))
    (fun _ _ h => Quotient.sound (mapQuiver_respects_equiv F h))
    m

/-- quotMapMor preserves identity. -/
theorem quotMapMor_id (a : D₁.quiver.Obj) :
    F.quotMapMor (D₁.quotId a) = D₂.quotId (F.quiverMor.objFn a) := rfl

/-- quotMapMor preserves composition. -/
theorem quotMapMor_comp
    {a b c : D₁.quiver.Obj}
    (g : D₁.QuotMor b c) (f : D₁.QuotMor a b) :
    F.quotMapMor (D₁.quotComp g f) =
    D₂.quotComp (F.quotMapMor g) (F.quotMapMor f) := by
  induction g using Quotient.ind with
  | _ g' =>
    induction f using Quotient.ind with
    | _ f' => rfl

end PLangQuotientMorphism

/-! ## L Functor on Morphisms

Given a CatJudgNatTrans between CatJudgCoprs, we construct the induced
functor between the quotient categories. -/

section LFunctorMorphisms

universe uL

variable {C₁ C₂ : Obj.CatJudgCopr.{uL + 1, uL + 1, uL + 1, uL + 1}}

/-- Convert a CatJudgNatTrans to a PLangQuotientMorphism between the
    corresponding quotient data. This provides L on morphisms. -/
def toPLangQuotientMorphism (α : Mor.CatJudgNatTrans C₁ C₂) :
    PLangQuotientMorphism (toPLangQuotientData C₁) (toPLangQuotientData C₂) where
  quiverMor := {
    objFn := α.objMap
    morFn := α.morMap
    -- domProof says: objMap ∘ C₁.dom = C₂.dom ∘ morMap
    -- We need: C₂.dom (morMap m) = objMap (C₁.dom m)
    src_comm := fun m => (congrFun α.domProof m).symm
    tgt_comm := fun m => (congrFun α.codProof m).symm
  }
  idWitMap := α.idMap
  compWitMap := α.compMap
  idMor_comm := fun i => congrFun α.idMorProof i
  compRight_comm := fun c => congrFun α.rightProof c
  compLeft_comm := fun c => congrFun α.leftProof c
  compComposite_comm := fun c => congrFun α.compositeProof c

/-- The quiver morphism from the identity CatJudgNatTrans equals
    the identity OverQuiverMorphism. -/
theorem toPLangQuotientMorphism_id_quiverMor
    (C : Obj.CatJudgCopr.{uL + 1, uL + 1, uL + 1, uL + 1}) :
    (toPLangQuotientMorphism (Cat.CatJudgNatTrans.id C)).quiverMor =
    OverQuiverMorphism.id (toPLangQuotientData C).quiver := by
  ext <;> rfl

/-- mapQuiver with the identity CatJudgNatTrans quiver morphism is identity. -/
theorem mapQuiver_toPLangQuotientMorphism_id
    (C : Obj.CatJudgCopr.{uL + 1, uL + 1, uL + 1, uL + 1})
    {a b : (toPLangQuotientData C).quiver.Obj}
    (fm : PFreeMor (toPLangQuotientData C).quiver a b) :
    PFreeMor.mapQuiver (toPLangQuotientMorphism (Cat.CatJudgNatTrans.id C)).quiverMor
      fm = fm := by
  induction fm with
  | var f =>
    simp only [PFreeMor.mapQuiver, toPLangQuotientMorphism, Cat.CatJudgNatTrans.id,
      Mor.CatJudgNatTrans.morMap, Cat.CatJudgMap.id, Mor.CatJudgMap.morMap,
      Mor.ObjMorMap.morMap]
    rfl
  | id x => rfl
  | comp g f ihg ihf =>
    simp only [PFreeMor.mapQuiver]
    rw [ihg, ihf]

/-- The objMap of the identity CatJudgNatTrans is _root_.id. -/
@[simp]
theorem CatJudgNatTrans_id_objMap
    (C : Obj.CatJudgCopr.{uL + 1, uL + 1, uL + 1, uL + 1}) :
    (Cat.CatJudgNatTrans.id C).objMap = _root_.id := rfl

/-- The morMap of the identity CatJudgNatTrans is _root_.id. -/
@[simp]
theorem CatJudgNatTrans_id_morMap
    (C : Obj.CatJudgCopr.{uL + 1, uL + 1, uL + 1, uL + 1}) :
    (Cat.CatJudgNatTrans.id C).morMap = _root_.id := rfl

/-- Map a bundled quotient morphism through a PLangQuotientMorphism. -/
def mapBundledQuotMor (α : Mor.CatJudgNatTrans C₁ C₂)
    (m : (toPLangQuotientData C₁).quotQuiver.MorType) :
    (toPLangQuotientData C₂).quotQuiver.MorType :=
  let F := toPLangQuotientMorphism α
  ⟨α.objMap m.1, α.objMap m.2.1, F.quotMapMor m.2.2⟩

/-- Source preservation for bundled morphism mapping. -/
theorem mapBundledQuotMor_src (α : Mor.CatJudgNatTrans C₁ C₂)
    (m : (toPLangQuotientData C₁).quotQuiver.MorType) :
    (toPLangQuotientData C₂).quotQuiver.src (mapBundledQuotMor α m) =
    α.objMap ((toPLangQuotientData C₁).quotQuiver.src m) := rfl

/-- Target preservation for bundled morphism mapping. -/
theorem mapBundledQuotMor_tgt (α : Mor.CatJudgNatTrans C₁ C₂)
    (m : (toPLangQuotientData C₁).quotQuiver.MorType) :
    (toPLangQuotientData C₂).quotQuiver.tgt (mapBundledQuotMor α m) =
    α.objMap ((toPLangQuotientData C₁).quotQuiver.tgt m) := rfl

/-- The L functor on morphisms: given α : C₁ ⟶ C₂, produce
    L(α) : L(C₁) ⟶ L(C₂) as an OverFunctorData. -/
def reflectionL_map (α : Mor.CatJudgNatTrans C₁ C₂) :
    OverFunctorData (reflectionL C₁) (reflectionL C₂) where
  toOverQuiverMorphism := {
    objFn := α.objMap
    morFn := mapBundledQuotMor α
    src_comm := mapBundledQuotMor_src α
    tgt_comm := mapBundledQuotMor_tgt α
  }
  map_id := fun a => by
    simp only [mapBundledQuotMor, toPLangQuotientMorphism]
    rfl
  map_comp := fun ⟨⟨⟨ag, bg, qg⟩, ⟨_, bf, qf⟩⟩, heq⟩ => by
    cases heq
    simp only [mapBundledQuotMor, toPLangQuotientMorphism]
    congr 2
    exact (toPLangQuotientMorphism α).quotMapMor_comp qf qg

/-- The quiver morphism from identity CatJudgNatTrans has identity functions. -/
theorem toPLangQuotientMorphism_id_objFn
    (C : Obj.CatJudgCopr.{uL + 1, uL + 1, uL + 1, uL + 1}) :
    (toPLangQuotientMorphism (Cat.CatJudgNatTrans.id C)).quiverMor.objFn =
    _root_.id := rfl

theorem toPLangQuotientMorphism_id_morFn
    (C : Obj.CatJudgCopr.{uL + 1, uL + 1, uL + 1, uL + 1}) :
    (toPLangQuotientMorphism (Cat.CatJudgNatTrans.id C)).quiverMor.morFn =
    _root_.id := rfl

/-- mapQuiver with identity quiver morphism is identity on PFreeMor. -/
theorem mapQuiver_id_eq {Q : OverQuiver.{uL, uL}} {a b : Q.Obj}
    (fm : PFreeMor Q a b) :
    PFreeMor.mapQuiver (OverQuiverMorphism.id Q) fm = fm :=
  PFreeMor.mapQuiver_overQuiverId fm

/-- L preserves identity morphisms. -/
theorem reflectionL_map_id
    (C : Obj.CatJudgCopr.{uL + 1, uL + 1, uL + 1, uL + 1}) :
    reflectionL_map (Cat.CatJudgNatTrans.id C) =
    OverFunctorData.id (reflectionL C) := by
  apply OverFunctorData.ext
  · rfl
  · funext m
    obtain ⟨a, b, qm⟩ := m
    induction qm using Quotient.ind with
    | _ fm =>
      simp only [reflectionL_map, mapBundledQuotMor, CatJudgNatTrans_id_objMap,
        _root_.id, PLangQuotientMorphism.quotMapMor, Quotient.lift_mk,
        mapQuiver_toPLangQuotientMorphism_id]
      rfl

/-- L preserves composition of morphisms. -/
theorem reflectionL_map_comp
    {C₁ C₂ C₃ : Obj.CatJudgCopr.{uL + 1, uL + 1, uL + 1, uL + 1}}
    (α : Mor.CatJudgNatTrans C₁ C₂) (β : Mor.CatJudgNatTrans C₂ C₃) :
    reflectionL_map (Cat.CatJudgNatTrans.comp α β) =
    (reflectionL_map α).comp (reflectionL_map β) := by
  apply OverFunctorData.ext
  · rfl
  · funext m
    obtain ⟨a, b, qm⟩ := m
    induction qm using Quotient.ind with
    | _ fm =>
      simp only [reflectionL_map, OverFunctorData.comp, mapBundledQuotMor,
        toPLangQuotientMorphism, PLangQuotientMorphism.quotMapMor,
        OverQuiverMorphism.comp, Quotient.lift_mk, Cat.CatJudgNatTrans.comp,
        Function.comp_apply, PLangQuotientData.Quotient_lift_quotMor,
        Mor.CatJudgNatTrans.objMap, Mor.CatJudgNatTrans.morMap,
        Cat.CatJudgMap.comp, Mor.CatJudgMap.objMap, Mor.ObjMorMap.objMap,
        Mor.CatJudgMap.morMap, Mor.ObjMorMap.morMap]
      unfold Cat.ObjMap.comp
      simp only [Function.comp_apply]
      congr 1
      congr 1
      -- LHS: mapQuiver {objFn := β ∘ α, ...} fm
      -- RHS: mapQuiver β (mapQuiver α fm)
      -- Use mapQuiver_quiverMorComp to transform RHS into mapQuiver (α.comp β) fm
      rw [← PFreeMor.mapQuiver_quiverMorComp]
      -- After rewrite, congr finishes since structures are defeq by OverQuiverMorphism.comp
      congr 1

end LFunctorMorphisms

/-! ## Mathlib Functor Instances

Define L and Φ as mathlib Functors, then construct the adjunction. -/

section MathlibFunctors

universe uMF

/-- Bundle an OverCategoryData with its quiver to form a BundledOverCategoryData.
    Used for L on objects. -/
def bundleQuotientCategory
    (C : Obj.CatJudgCopr.{uMF + 1, uMF + 1, uMF + 1, uMF + 1}) :
    BundledOverCategoryData.{uMF + 1, uMF + 1} where
  quiver := (toPLangQuotientData C).quotQuiver
  data := reflectionL C

/-- The L functor from CatJudgCopr to BundledOverCategoryData. -/
def LFunctorPLang :
    CategoryTheory.Functor Obj.CatJudgCopr.{uMF + 1, uMF + 1, uMF + 1, uMF + 1}
    BundledOverCategoryData.{uMF + 1, uMF + 1} where
  obj := bundleQuotientCategory
  map := fun α => reflectionL_map α
  map_id := fun C => reflectionL_map_id C
  map_comp := fun α β => reflectionL_map_comp α β

/-- The Φ functor from BundledOverCategoryData to CatJudgCopr. -/
def PhiFunctorPLang :
    CategoryTheory.Functor BundledOverCategoryData.{uMF + 1, uMF + 1}
    Obj.CatJudgCopr.{uMF + 1, uMF + 1, uMF + 1, uMF + 1} where
  obj := fun C => toPLangCatJudgCopr C.data
  map := fun F => toPLangCatJudgNatTrans F
  map_id := fun C => toPLangCatJudgNatTrans_id C.data
  map_comp := fun F G => toPLangCatJudgNatTrans_comp F G

end MathlibFunctors

/-! ## Unit of the Adjunction

The unit η : Id → Φ ∘ L embeds the original copresheaf into the copresheaf
of the free quotient category. On morphisms, this embeds quiver morphisms
as generators (variables) in the free category. -/

section UnitAdjunction

variable (C : Obj.CatJudgCopr.{u, u, u, u})

/-- The PLangQuotientData for C. -/
abbrev unitQuotData : PLangQuotientData.{u} := toPLangQuotientData C

/-- The quiver for the unit construction. This is the quiver extracted from C
    with objects = C.obj, morphisms = C.mor, src = C.dom, tgt = C.cod. -/
abbrev unitQuiver : OverQuiver.{u, u} := (unitQuotData C).quiver

/-- The target CatJudgCopr for the unit: Φ(L(C)).
    Objects are C.obj, morphisms are bundled quotient morphisms. -/
abbrev unitTarget : Obj.CatJudgCopr.{u, u, u, u} :=
  toPLangCatJudgCopr (reflectionL C)

/-- Embed a C-morphism as a variable in the free morphism type. -/
def unitVar (m : C.mor) : PFreeMor (unitQuiver C) (C.dom m) (C.cod m) :=
  PFreeMor.var (Q := unitQuiver C) m

/-- The object map for the unit is the identity. -/
abbrev unitObjMap : C.obj → (unitTarget C).obj := id

/-- The morphism map for the unit sends a morphism to its quotient class
    as a variable in the free category. -/
def unitMorMap (m : C.mor) : (unitTarget C).mor :=
  ⟨C.dom m, C.cod m, (unitQuotData C).quotMor (unitVar C m)⟩

/-- The identity witness map sends an identity witness to the corresponding
    object (where the identity is located). -/
abbrev unitIdMap : C.idType → (unitTarget C).idType := fun i => C.dom (C.idMor i)

/-- The composition witness map constructs the composable pair of variables
    from a composition witness. -/
def unitCompMap (c : C.compType) : (unitTarget C).compType :=
  let D := unitQuotData C
  let rightMor : (unitTarget C).mor :=
    ⟨C.dom (C.right c), C.cod (C.right c), D.quotMor (unitVar C (C.right c))⟩
  let leftMor : (unitTarget C).mor :=
    ⟨C.dom (C.left c), C.cod (C.left c), D.quotMor (unitVar C (C.left c))⟩
  ⟨(rightMor, leftMor), D.compMatch c⟩

/-- The CatJudgMap for the unit. -/
def unitCatJudgMap : Mor.CatJudgMap C (unitTarget C) :=
  ((unitObjMap C, unitMorMap C), (unitIdMap C, unitCompMap C))

/-- Domain naturality for the unit. -/
theorem unit_dom : Mor.CatJudgNaturalityDom (unitCatJudgMap C) := rfl

/-- Codomain naturality for the unit. -/
theorem unit_cod : Mor.CatJudgNaturalityCod (unitCatJudgMap C) := rfl

/-- Identity morphism naturality for the unit: mapping the identity morphism
    through unit equals the identity at the mapped object. -/
theorem unit_idMor : Mor.CatJudgNaturalityIdMor (unitCatJudgMap C) := by
  unfold Mor.CatJudgNaturalityIdMor
  funext i
  simp only [Function.comp_apply, Mor.CatJudgMap.morMap, Mor.CatJudgMap.idMap,
    Mor.CatJudgMap.objMorMap, Mor.ObjMorMap.morMap, Mor.CatJudgMap.idCompMap]
  simp only [unitCatJudgMap, unitMorMap, unitIdMap, unitTarget, unitObjMap]
  simp only [Obj.CatJudgCopr.idMor, toPLangCatJudgCopr, toPLangCatJudgObjMor,
    toPLangCatJudgMor, Obj.CatJudgObjMor.idMor, Obj.CatJudgMor.idMor,
    Obj.CatJudgMor.idMorCompProj, reflectionL, PLangQuotientData.toOverCategoryData,
    PLangQuotientData.quotCategoryOps, PLangQuotientData.quotIdFn,
    PLangQuotientData.quotQuiver, PLangQuotientData.quotId]
  -- Goal: ⟨dom, ⟨cod, quotMor (var m)⟩⟩ = ⟨dom, ⟨dom, quotMor (id dom)⟩⟩
  -- where m = C.idMor i and cod = dom by C.endoProof
  let D := toPLangQuotientData C
  -- id_witness relates: cast (id_endo) (var (idMor i)) ~ id dom
  have h_wit := PLangQuotientData.FreeMorEquivGen.id_witness (D := D) i
  -- endoProof gives dom ∘ idMor = cod ∘ idMor, so for each i: dom = cod
  have hendo : C.cod (C.idMor i) = C.dom (C.idMor i) := (D.idEndo i).symm
  -- The quotient elements have HEq via quotMor_heq_of_cast_equiv
  have hquot : HEq (D.quotMor (unitVar C (C.idMor i)))
      (D.quotMor (PFreeMor.id (Q := D.quiver) (C.dom (C.idMor i)))) :=
    PLangQuotientData.quotMor_heq_of_cast_equiv D hendo
      (unitVar C (C.idMor i))
      (PFreeMor.id (Q := D.quiver) (C.dom (C.idMor i)))
      (.rel h_wit)
  -- Build the sigma type equality using HEq
  refine Sigma.ext rfl ?_
  refine heq_of_eq (Sigma.ext hendo ?_)
  exact hquot

/-- Left projection naturality for the unit: mapping the left component
    through unit equals the left component of the mapped composable pair. -/
theorem unit_left : Mor.CatJudgNaturalityLeft (unitCatJudgMap C) := rfl

/-- Right projection naturality for the unit: mapping the right component
    through unit equals the right component of the mapped composable pair. -/
theorem unit_right : Mor.CatJudgNaturalityRight (unitCatJudgMap C) := rfl

/-- Composite naturality for the unit: mapping the composite morphism
    through unit equals the composite in the target category.

    Requires showing that:
    1. Domain matches: dom(composite) = dom(right)
    2. Codomain matches: cod(composite) = cod(left)
    3. The quotient of the composite variable equals the quotient
       composition of the left and right variables
    The third point uses the comp_witness generating relation.

    The main technical difficulty is handling the nested sigma types with
    dependent casts. The comp_witness relation states that
    comp(cast(var left), var right) ~ cast(var composite), which after
    taking quotients gives the desired equality. -/
theorem unit_composite : Mor.CatJudgNaturalityComposite (unitCatJudgMap C) := by
  unfold Mor.CatJudgNaturalityComposite
  funext c
  simp only [Function.comp_apply, Mor.CatJudgMap.morMap,
    Mor.CatJudgMap.objMorMap, Mor.ObjMorMap.morMap, Mor.CatJudgMap.compMap,
    Mor.CatJudgMap.idCompMap]
  simp only [unitCatJudgMap, unitMorMap, unitCompMap, unitTarget, unitObjMap]
  let D := toPLangQuotientData C
  have h_dom : C.dom (C.composite c) = C.dom (C.right c) :=
    congrFun C.compDomProof c
  have h_cod : C.cod (C.composite c) = C.cod (C.left c) :=
    congrFun C.compCodProof c
  simp only [Obj.CatJudgCopr.composite, Obj.CatJudgObjMor.composite,
    Obj.ObjMorCompProj.composite, toPLangCatJudgCopr, toPLangCatJudgObjMor,
    toPLangCatJudgMor, reflectionL, PLangQuotientData.toOverCategoryData,
    PLangQuotientData.quotCategoryOps, PLangQuotientData.quotCompFn,
    PLangQuotientData.quotQuiver, PLangQuotientData.quotMor]
  have h_wit := PLangQuotientData.FreeMorEquivGen.comp_witness (D := D) c
  have h_match : C.cod (C.right c) = C.dom (C.left c) := D.compMatch c
  -- Goal: nested sigma equality
  -- LHS: ⟨dom composite, ⟨cod composite, quotMor (var composite)⟩⟩
  -- RHS: ⟨dom right, ⟨cod left, quotComp (quotMor left) (h_match ▸ quotMor right)⟩⟩
  -- Outer Sigma.ext with h_dom
  refine Sigma.ext h_dom ?_
  -- Goal: inner sigma HEq
  -- LHS type: (cod : C.obj) × QuotMor D (dom composite) cod
  -- RHS type: (cod : C.obj) × QuotMor D (dom right) cod
  -- Use sigma_heq_of_fst_eq_snd_heq with explicit type parameters
  refine sigma_heq_of_fst_eq_snd_heq
    (α := C.obj) (I := C.obj) (β := fun dom cod => D.QuotMor dom cod)
    h_dom h_cod ?_
  -- Goal: ⟦var composite⟧ ≍ quotComp ⟦left⟧ (h_match ▸ ⟦right⟧)
  -- Convert quotient notation to quotMor
  simp only [PLangQuotientData.quotMk_eq_quotMor, unitQuotData]
  -- Now: quotMor (var composite) ≍ quotComp (quotMor left) (h_match ▸ quotMor right)
  -- Replace `toPLangQuotientData C` with `D` to help pattern matching
  change D.quotMor (unitVar C (C.composite c)) ≍
         D.quotComp (D.quotMor (unitVar C (C.left c)))
           (h_match ▸ D.quotMor (unitVar C (C.right c)))
  -- First push transport inside quotMor using conv
  -- In quotComp g f: arg 1 = quotComp, arg 2 = g, arg 3 = f
  conv_rhs => arg 3; rw [PLangQuotientData.quotMor_subst_eq (D := D)]
  -- Now: quotMor (var composite) ≍ quotComp (quotMor left) (quotMor (h_match ▸ right))
  -- Apply quotComp_quotMor
  rw [PLangQuotientData.quotComp_quotMor]
  -- Now: quotMor (var composite) ≍ quotMor (comp left (h_match ▸ right))
  -- Use quotMor_heq_of_both_cast_equiv with the comp_witness relation
  apply PLangQuotientData.quotMor_heq_of_both_cast_equiv D h_dom h_cod
  -- Need: FreeMorEquiv (h_dom ▸ h_cod ▸ var composite) (comp left (h_match ▸ right))
  apply PLangQuotientData.FreeMorEquiv.symm
  -- Need: FreeMorEquiv (comp left (h_match ▸ right)) (h_dom ▸ h_cod ▸ var composite)
  -- Convert double subst on RHS to cast
  rw [PLangQuotientMorphism.subst_subst_eq_cast h_dom h_cod]
  -- Now RHS: cast (congrArg₂ ...) (var composite)
  -- Apply the generator relation
  apply PLangQuotientData.FreeMorEquiv.rel
  -- Now need: FreeMorEquivGen (comp left (h_match ▸ right)) (cast ... (var composite))
  -- comp_witness has: FreeMorEquivGen (comp (cast left) right) (cast var composite)
  -- Need to convert our form to match comp_witness
  -- The issue is: our form has `h_match ▸ right` but witness has `cast left`
  -- These are morally equivalent up to rearrangement
  simp only [unitVar]
  -- Goal: FreeMorEquivGen (left.comp (h_match ▸ right)) (cast composite)
  -- h_wit: FreeMorEquivGen ((cast left).comp right) (cast composite)
  convert h_wit using 1
  -- Subgoal: (left.comp (h_match ▸ right)) = ((cast left).comp right)
  -- Use comp_subst_tgt_right to rewrite LHS to (h_match.symm ▸ left).comp right
  rw [PFreeMor.comp_subst_tgt_right h_match]
  -- Now goal: (h_match.symm ▸ left).comp right = (cast left).comp right
  -- Split into component equalities
  congr 1
  -- Goal: ⋯ ▸ PFreeMor.var (C.left c) = cast ⋯ (PFreeMor.var (D.left c))
  -- D.left = C.left definitionally, so both sides are transports of the same term
  -- The ▸ is on source, so use subst_src_eq_cast
  -- Annotate with D.quiver to get correct types
  convert @PFreeMor.subst_src_eq_cast D.quiver _ _ _ h_match.symm (PFreeMor.var (D.left c))

/-- All naturality conditions for the unit. -/
theorem unitNaturalityAll : Mor.CatJudgNaturalityAll (unitCatJudgMap C) :=
  ⟨⟨unit_dom C, unit_cod C⟩, unit_idMor C, ⟨unit_left C, unit_right C, unit_composite C⟩⟩

/-- The unit natural transformation η : C → Φ(L(C)) for the L ⊣ Φ adjunction.
    This embeds the original copresheaf into the copresheaf of the quotient
    category, sending each morphism to its equivalence class as a variable. -/
def unit : Mor.CatJudgNatTrans C (unitTarget C) :=
  ⟨unitCatJudgMap C, unitNaturalityAll C⟩

end UnitAdjunction

/-! ## Counit of the Adjunction

The counit ε : L ∘ Φ → Id evaluates free morphisms back in the original category.
For a category C:
- Φ(C) is the CatJudgCopr representation of C
- L(Φ(C)) is the quotient category of free morphisms
- ε_C : L(Φ(C)) → C evaluates each quotient class by composing in C -/

section CounitAdjunction

namespace Counit

variable {Q : OverQuiver.{u, u}} (C : OverCategoryData Q)

/-- The PLangQuotientData derived from an OverCategoryData.
    This is Φ(C) viewed as quotient data. -/
abbrev derivedQuotData : PLangQuotientData.{u} :=
  toPLangQuotientData (toPLangCatJudgCopr C)

/-- Evaluate a PFreeMor in the category C, returning the morphism value
    along with proofs of source/target. -/
def counitEvalAux : {a b : Q.Obj} → PFreeMor Q a b →
    { f : Q.MorType // Q.src f = a ∧ Q.tgt f = b }
  | _, _, .var f => ⟨f, rfl, rfl⟩
  | _, _, .id x => ⟨C.idFn x, C.id_src x, C.id_tgt x⟩
  | _, _, .comp g f =>
    let ⟨fVal, fSrc, fTgt⟩ := counitEvalAux f
    let ⟨gVal, gSrc, gTgt⟩ := counitEvalAux g
    let composable : Q.tgt fVal = Q.src gVal := by rw [fTgt, gSrc]
    let comp := C.compFn ⟨(fVal, gVal), composable⟩
    ⟨comp, by rw [C.comp_src]; exact fSrc, by rw [C.comp_tgt]; exact gTgt⟩

/-- Evaluate a PFreeMor in the category C. -/
def counitEval {a b : Q.Obj} (m : PFreeMor Q a b) : Q.MorType :=
  (counitEvalAux C m).val

/-- Source of counitEvalAux matches PFreeMor source. -/
theorem counitEvalAux_src {a b : Q.Obj} (m : PFreeMor Q a b) :
    Q.src (counitEvalAux C m).val = a :=
  (counitEvalAux C m).property.1

/-- Target of counitEvalAux matches PFreeMor target. -/
theorem counitEvalAux_tgt {a b : Q.Obj} (m : PFreeMor Q a b) :
    Q.tgt (counitEvalAux C m).val = b :=
  (counitEvalAux C m).property.2

/-- counitEval of a composition. -/
theorem counitEval_comp {a b c : Q.Obj}
    (g : PFreeMor Q b c) (f : PFreeMor Q a b) :
    counitEval C (PFreeMor.comp g f) =
    C.compFn ⟨(counitEval C f, counitEval C g),
      (counitEvalAux C f).property.2.trans (counitEvalAux C g).property.1.symm⟩ := by
  conv_lhs => unfold counitEval counitEvalAux
  conv_rhs => unfold counitEval
  let ⟨fVal, fSrc, fTgt⟩ := counitEvalAux C f
  let ⟨gVal, gSrc, gTgt⟩ := counitEvalAux C g
  rfl

/-- counitEval of identity. -/
theorem counitEval_id {a : Q.Obj} :
    counitEval C (PFreeMor.id a) = C.idFn a := by
  simp only [counitEval, counitEvalAux]

/-- counitEval of a variable (without cast). -/
theorem counitEval_var_eq (f : Q.MorType) :
    counitEval C (PFreeMor.var f) = f := rfl

/-- Left identity: counitEval (comp (id b) f) = counitEval f -/
theorem counitEval_id_left {a b : Q.Obj} (f : PFreeMor Q a b) :
    counitEval C (PFreeMor.comp (PFreeMor.id b) f) = counitEval C f := by
  simp only [counitEval_comp, counitEval_id]
  have h_tgt : Q.tgt (counitEval C f) = b := counitEvalAux_tgt C f
  have h := C.comp_id (counitEval C f)
  convert h using 1
  simp only [h_tgt]

/-- Right identity: counitEval (comp f (id a)) = counitEval f -/
theorem counitEval_id_right {a b : Q.Obj} (f : PFreeMor Q a b) :
    counitEval C (PFreeMor.comp f (PFreeMor.id a)) = counitEval C f := by
  simp only [counitEval_comp, counitEval_id]
  have h_src : Q.src (counitEval C f) = a := counitEvalAux_src C f
  have h := C.id_comp (counitEval C f)
  convert h using 1
  simp only [h_src]

/-- Associativity: counitEval (comp h (comp g f)) =
    counitEval (comp (comp h g) f) -/
theorem counitEval_assoc {a b c d : Q.Obj}
    (h : PFreeMor Q c d) (g : PFreeMor Q b c) (f : PFreeMor Q a b) :
    counitEval C (PFreeMor.comp h (PFreeMor.comp g f)) =
    counitEval C (PFreeMor.comp (PFreeMor.comp h g) f) := by
  simp only [counitEval_comp]
  let fVal := counitEval C f
  let gVal := counitEval C g
  let hVal := counitEval C h
  have h_fg : Q.tgt fVal = Q.src gVal :=
    (counitEvalAux_tgt C f).trans (counitEvalAux_src C g).symm
  have h_gh : Q.tgt gVal = Q.src hVal :=
    (counitEvalAux_tgt C g).trans (counitEvalAux_src C h).symm
  let t : Q.ComposableTriplesType := ⟨(fVal, gVal, hVal), h_fg, h_gh⟩
  have assoc_law := C.assoc t
  convert assoc_law using 1

/-- Congruence left: if counitEval f = counitEval g, then
    counitEval (comp h f) = counitEval (comp h g). -/
theorem counitEval_cong_left {a b c : Q.Obj}
    {f g : PFreeMor Q a b} (h : PFreeMor Q b c)
    (heq : counitEval C f = counitEval C g) :
    counitEval C (PFreeMor.comp h f) = counitEval C (PFreeMor.comp h g) := by
  simp only [counitEval_comp]
  congr 1
  ext
  · exact heq
  · rfl

/-- Congruence right: if counitEval f = counitEval g, then
    counitEval (comp f k) = counitEval (comp g k). -/
theorem counitEval_cong_right {a b c : Q.Obj}
    {f g : PFreeMor Q b c} (k : PFreeMor Q a b)
    (heq : counitEval C f = counitEval C g) :
    counitEval C (PFreeMor.comp f k) = counitEval C (PFreeMor.comp g k) := by
  simp only [counitEval_comp]
  congr 1
  ext
  · rfl
  · exact heq

/-- counitEval of a cast morphism. The cast only affects types, not values. -/
theorem counitEval_cast {a b a' b' : Q.Obj}
    (ha : a = a') (hb : b = b')
    (m : PFreeMor Q a b) :
    counitEval C (cast (by rw [ha, hb]) m) = counitEval C m := by
  subst ha hb
  rfl

/-- counitEval of a variable equals that variable (directly). -/
theorem counitEval_var (f : Q.MorType) :
    counitEval C (PFreeMor.var f) = f := rfl

/-- counitEval of a cast variable. -/
theorem counitEval_var_cast {a b : Q.Obj} (f : Q.MorType)
    (hsrc : Q.src f = a) (htgt : Q.tgt f = b) :
    counitEval C (cast (by rw [hsrc, htgt]) (PFreeMor.var f)) = f := by
  subst hsrc htgt
  rfl

/-- The derivedQuotData idMor is just C.idFn. -/
theorem derivedQuotData_idMor (i : Q.Obj) :
    (derivedQuotData C).idMor i = C.idFn i := rfl

/-- The derivedQuotData left is the second component of the pair. -/
theorem derivedQuotData_left (c : Q.ComposablePairsType) :
    (derivedQuotData C).left c = c.val.2 := rfl

/-- The derivedQuotData right is the first component of the pair. -/
theorem derivedQuotData_right (c : Q.ComposablePairsType) :
    (derivedQuotData C).right c = c.val.1 := rfl

/-- The derivedQuotData composite is C.compFn. -/
theorem derivedQuotData_composite (c : Q.ComposablePairsType) :
    (derivedQuotData C).composite c = C.compFn c := rfl

/-- counitEval respects the generating equivalence relation FreeMorEquivGen.
    This is where the category axioms of C ensure that the free category
    quotient is consistent with evaluation.

    The theorem requires D = derivedQuotData C, which encodes that:
    - D.idMor i = C.idFn i (identity morphisms match)
    - D.composite c = C.compFn c (composition matches)
    - D.left/right are the projections from composable pairs -/
theorem counitEval_respects_gen
    {a b : Q.Obj} {f g : PFreeMor Q a b}
    (h : (derivedQuotData C).FreeMorEquivGen f g) :
    counitEval C f = counitEval C g := by
  match h with
  | .id_left f => exact counitEval_id_left C f
  | .id_right f => exact counitEval_id_right C f
  | .assoc h g f => exact counitEval_assoc C h g f
  | .id_witness i =>
    have htgt : Q.tgt (C.idFn i) = Q.src (C.idFn i) :=
      (C.id_tgt i).trans (C.id_src i).symm
    have h_src : (derivedQuotData C).quiver.src (C.idFn i) = i := C.id_src i
    simp only [derivedQuotData_idMor,
      counitEval_var_cast C (C.idFn i) rfl htgt, counitEval_id, h_src]
  | .comp_witness c =>
    simp only [derivedQuotData_left, derivedQuotData_right, derivedQuotData_composite,
      counitEval_comp, counitEval_var,
      counitEval_var_cast C c.val.2 c.property.symm rfl,
      counitEval_var_cast C (C.compFn c) (C.comp_src c) (C.comp_tgt c)]
    rfl
  | .cong_left h ih =>
    exact counitEval_cong_left C h (counitEval_respects_gen ih)
  | .cong_right k ih =>
    exact counitEval_cong_right C k (counitEval_respects_gen ih)

/-- counitEval respects the full equivalence relation FreeMorEquiv. -/
theorem counitEval_respects
    {a b : Q.Obj} {f g : PFreeMor Q a b}
    (h : (derivedQuotData C).FreeMorEquiv f g) :
    counitEval C f = counitEval C g :=
  match h with
  | .rel hr => counitEval_respects_gen C hr
  | .refl _ => rfl
  | .symm h' => (counitEval_respects h').symm
  | .trans h1 h2 => (counitEval_respects h1).trans (counitEval_respects h2)

/-- Evaluate a quotient of free morphisms in the category C. -/
def counitEvalQuot {a b : Q.Obj} :
    Quotient ((derivedQuotData C).freeMorSetoid a b) → Q.MorType :=
  Quotient.lift (counitEval C) (fun _ _ h => counitEval_respects C h)

/-- counitEvalQuot of a quotient identity. -/
theorem counitEvalQuot_quotId (a : Q.Obj) :
    counitEvalQuot C ((derivedQuotData C).quotId a) = C.idFn a := by
  simp only [counitEvalQuot, PLangQuotientData.quotId, PLangQuotientData.quotMor,
    Quotient.lift_mk, counitEval_id]

/-- counitEvalQuot of a quotient composition. -/
theorem counitEvalQuot_quotComp {a b c : Q.Obj}
    (g : Quotient ((derivedQuotData C).freeMorSetoid b c))
    (f : Quotient ((derivedQuotData C).freeMorSetoid a b)) :
    counitEvalQuot C ((derivedQuotData C).quotComp g f) =
    C.compFn ⟨(counitEvalQuot C f, counitEvalQuot C g),
      by
        -- Need: tgt (counitEvalQuot f) = src (counitEvalQuot g)
        induction f using Quotient.ind with | _ f' =>
        induction g using Quotient.ind with | _ g' =>
        simp only [counitEvalQuot, Quotient.lift_mk]
        exact (counitEvalAux_tgt C f').trans (counitEvalAux_src C g').symm⟩ := by
  induction f using Quotient.ind with | _ f' =>
  induction g using Quotient.ind with | _ g' =>
  simp only [PLangQuotientData.quotComp, Quotient.lift_mk, counitEvalQuot,
    PLangQuotientData.quotMor, counitEval_comp]

/-- Source of counitEvalQuot on a quotient. -/
theorem counitEvalQuot_src {a b : Q.Obj}
    (qm : Quotient ((derivedQuotData C).freeMorSetoid a b)) :
    Q.src (counitEvalQuot C qm) = a := by
  induction qm using Quotient.ind with | _ m =>
  simp only [counitEvalQuot, Quotient.lift_mk]
  exact counitEvalAux_src C m

/-- Target of counitEvalQuot on a quotient. -/
theorem counitEvalQuot_tgt {a b : Q.Obj}
    (qm : Quotient ((derivedQuotData C).freeMorSetoid a b)) :
    Q.tgt (counitEvalQuot C qm) = b := by
  induction qm using Quotient.ind with | _ m =>
  simp only [counitEvalQuot, Quotient.lift_mk]
  exact counitEvalAux_tgt C m

/-- The counit as a quiver morphism from the quotient quiver to Q.
    Objects are identity, morphisms are evaluated via counitEvalQuot. -/
def counitQuiverMor :
    OverQuiverMorphism (derivedQuotData C).quotQuiver Q where
  objFn := id
  morFn := fun ⟨a, b, qm⟩ => counitEvalQuot C qm
  src_comm := fun ⟨a, b, qm⟩ => by
    simp only [PLangQuotientData.quotQuiver, id]
    exact counitEvalQuot_src C qm
  tgt_comm := fun ⟨a, b, qm⟩ => by
    simp only [PLangQuotientData.quotQuiver, id]
    exact counitEvalQuot_tgt C qm

/-- Abbreviation for the quotient category data. -/
abbrev quotCatData : OverCategoryData (derivedQuotData C).quotQuiver :=
  (derivedQuotData C).toOverCategoryData

/-- The counit preserves identity:
    counitQuiverMor (quotIdFn a) = idFn a. -/
theorem counit_map_id (a : Q.Obj) :
    (counitQuiverMor C).morFn ((quotCatData C).idFn a) =
    C.idFn ((counitQuiverMor C).objFn a) := by
  simp only [counitQuiverMor, quotCatData, PLangQuotientData.toOverCategoryData,
    PLangQuotientData.quotCategoryOps, PLangQuotientData.quotIdFn, id]
  simp only [counitEvalQuot_quotId]

/-- The counit preserves composition. -/
theorem counit_map_comp (p : (derivedQuotData C).quotQuiver.ComposablePairsType) :
    (counitQuiverMor C).morFn ((quotCatData C).compFn p) =
    C.compFn ⟨((counitQuiverMor C).morFn p.val.1, (counitQuiverMor C).morFn p.val.2),
      ((counitQuiverMor C).tgt_comm p.val.1).trans
        ((congrArg (counitQuiverMor C).objFn p.property).trans
          ((counitQuiverMor C).src_comm p.val.2).symm)⟩ := by
  obtain ⟨⟨⟨a, b, qf⟩, ⟨b', c, qg⟩⟩, h_composable⟩ := p
  have h_eq : b = b' := h_composable
  subst h_eq
  simp only [counitQuiverMor, quotCatData, PLangQuotientData.toOverCategoryData,
    PLangQuotientData.quotCategoryOps, PLangQuotientData.quotCompFn,
    PLangQuotientData.quotQuiver, counitEvalQuot_quotComp]
  have h_rfl : h_composable = rfl := rfl
  rw [h_rfl]

/-- The counit as a functor from L(Φ(C)) to C.
    For a category C, ε_C : L(Φ(C)) → C evaluates quotient morphisms. -/
def counitFunctorData :
    OverFunctorData (derivedQuotData C).toOverCategoryData C where
  toOverQuiverMorphism := counitQuiverMor C
  map_id := counit_map_id C
  map_comp := counit_map_comp C

end Counit

/-! ## Counit Naturality

The counit is natural: for any functor F : C → D, we have
ε_D ∘ L(Φ(F)) = F ∘ ε_C. -/

section CounitNaturality

variable {Q₁ Q₂ : OverQuiver.{u, u}}
variable (C : OverCategoryData Q₁) (D : OverCategoryData Q₂)
variable (F : OverFunctorData C D)

/-- Helper to evaluate a casted var. When mapQuiver is applied to a var,
    we get casts from src_comm/tgt_comm. -/
theorem counitEval_var_subst {Q : OverQuiver.{u, u}} (C' : OverCategoryData Q)
    (f : Q.MorType) {a b : Q.Obj} (hsrc : Q.src f = a) (htgt : Q.tgt f = b) :
    Counit.counitEval C' (hsrc ▸ htgt ▸ PFreeMor.var f) = f := by
  subst hsrc htgt
  rfl

/-- Naturality of counitEval at the PFreeMor level:
    F.morFn (counitEval C m) = counitEval D (mapQuiver F m). -/
theorem counitEval_naturality {a b : Q₁.Obj} (m : PFreeMor Q₁ a b) :
    F.morFn (Counit.counitEval C m) =
    Counit.counitEval D (PFreeMor.mapQuiver F.toOverQuiverMorphism m) := by
  induction m with
  | var f =>
    simp only [Counit.counitEval, Counit.counitEvalAux, PFreeMor.mapQuiver]
    exact (counitEval_var_subst D (F.morFn f) (F.src_comm f) (F.tgt_comm f)).symm
  | id x =>
    simp only [Counit.counitEval, Counit.counitEvalAux, PFreeMor.mapQuiver]
    exact F.map_id x
  | comp g f ihg ihf =>
    simp only [PFreeMor.mapQuiver, Counit.counitEval_comp C g f,
      Counit.counitEval_comp D]
    have hcomp : Q₁.tgt (Counit.counitEval C f) = Q₁.src (Counit.counitEval C g) :=
      (Counit.counitEvalAux C f).property.2.trans
        (Counit.counitEvalAux C g).property.1.symm
    have map_comp_eq := F.map_comp ⟨(Counit.counitEval C f, Counit.counitEval C g),
      hcomp⟩
    rw [map_comp_eq]
    congr 1
    ext
    · exact ihf
    · exact ihg

/-- Helper: An OverFunctorData induces a PLangQuotientMorphism on
    derived quotient data. -/
def toPLangQuotientMorphism' :
    PLangQuotientMorphism (Counit.derivedQuotData C) (Counit.derivedQuotData D) where
  quiverMor := F.toOverQuiverMorphism
  idWitMap := F.objFn
  compWitMap := fun p =>
    ⟨(F.morFn p.val.1, F.morFn p.val.2),
     (F.tgt_comm p.val.1).trans
       ((congrArg F.objFn p.property).trans (F.src_comm p.val.2).symm)⟩
  idMor_comm := fun i => F.map_id i
  compRight_comm := fun _ => rfl
  compLeft_comm := fun _ => rfl
  compComposite_comm := fun p => F.map_comp p

/-- The induced quotient functor on morphisms: maps quotient morphisms
    via mapQuiver. Uses the respects-equiv theorem to define on quotient. -/
def pLangInducedQuotMorFn {a b : Q₁.Obj}
    (qm : (Counit.derivedQuotData C).QuotMor a b) :
    (Counit.derivedQuotData D).QuotMor (F.objFn a) (F.objFn b) :=
  Quotient.lift
    (fun fm => (Counit.derivedQuotData D).quotMor
      (PFreeMor.mapQuiver F.toOverQuiverMorphism fm))
    (fun _ _ h => Quotient.sound (PLangQuotientMorphism.mapQuiver_respects_equiv
      (toPLangQuotientMorphism' C D F) h))
    qm

/-- Naturality of counitEvalQuot at the quotient level. -/
theorem counitEvalQuot_naturality {a b : Q₁.Obj}
    (qm : (Counit.derivedQuotData C).QuotMor a b) :
    F.morFn (Counit.counitEvalQuot C qm) =
    Counit.counitEvalQuot D (pLangInducedQuotMorFn C D F qm) := by
  induction qm using Quotient.ind with | _ fm =>
  simp only [Counit.counitEvalQuot, Quotient.lift_mk, pLangInducedQuotMorFn,
    PLangQuotientData.quotMor, Quotient.lift_mk]
  exact counitEval_naturality C D F fm

end CounitNaturality

end CounitAdjunction

/-! ## Triangle Identities

For the adjunction L ⊣ Φ, the triangle identities are:
1. For X : CatJudgCopr: ε_{L(X)} ∘ L(η_X) = id_{L(X)}
2. For C : Cat: Φ(ε_C) ∘ η_{Φ(C)} = id_{Φ(C)}

Here we prove the second identity: the composition of unit with Φ(counit)
is the identity natural transformation on Φ(C). -/

section TriangleIdentities

variable {Q : OverQuiver.{u, u}} (C : OverCategoryData Q)

/-- Abbreviation for Φ(C) as a CatJudgCopr. -/
abbrev trianglePhiC : Obj.CatJudgCopr.{u, u, u, u} := toPLangCatJudgCopr C

/-- The unit applied to Φ(C): η_{Φ(C)} : Φ(C) → Φ(L(Φ(C))). -/
abbrev triangleUnitPhiC :
    Mor.CatJudgNatTrans (trianglePhiC C) (unitTarget (trianglePhiC C)) :=
  unit (trianglePhiC C)

/-- Φ(L(Φ(C))) is definitionally equal to unitTarget (trianglePhiC C).
    This expands the definitions to show they match. -/
theorem phiLPhiC_eq_unitTarget :
    toPLangCatJudgCopr (Counit.derivedQuotData C).toOverCategoryData =
    unitTarget (trianglePhiC C) := rfl

/-- The counit as a CatJudgNatTrans via the embedding functor Φ.
    This is Φ(ε_C) : Φ(L(Φ(C))) → Φ(C).
    Note: derivedQuotData C = toPLangQuotientData (trianglePhiC C). -/
def phiCounit :
    Mor.CatJudgNatTrans (unitTarget (trianglePhiC C)) (trianglePhiC C) :=
  phiLPhiC_eq_unitTarget C ▸
    toPLangCatJudgNatTrans (Counit.counitFunctorData C)

/-- The composition η ≫ Φ(ε): the unit followed by the embedded counit.
    This should equal id_{Φ(C)} by the triangle identity. -/
def unitThenPhiCounit :
    Mor.CatJudgNatTrans (trianglePhiC C) (trianglePhiC C) :=
  Cat.CatJudgNatTrans.comp (triangleUnitPhiC C) (phiCounit C)

/-- The idMap for the unit on Φ(C) is the identity. -/
theorem unitIdMap_toPLang_eq_id :
    unitIdMap (toPLangCatJudgCopr C) = id := by
  funext i
  simp only [unitIdMap, toPLangCatJudgCopr, toPLangCatJudgObjMor,
    toPLangCatJudgMor, id]
  exact C.id_src i

/-- The right triangle identity: Φ(ε_C) ∘ η_{Φ(C)} = id_{Φ(C)}.
    This states that applying unit then counit to Φ(C) gives the identity. -/
theorem rightTriangle :
    unitThenPhiCounit C = Cat.CatJudgNatTrans.id (trianglePhiC C) := by
  unfold unitThenPhiCounit Cat.CatJudgNatTrans.comp Cat.CatJudgNatTrans.id
  apply Subtype.ext
  unfold Cat.CatJudgMap.comp Cat.CatJudgMap.id Cat.ObjMap.comp
  unfold triangleUnitPhiC trianglePhiC phiCounit
  unfold unit unitCatJudgMap toPLangCatJudgNatTrans toPLangCatJudgMap
  simp only [Counit.counitFunctorData, Counit.counitQuiverMor, unitObjMap,
    Mor.CatJudgMap.objMorMap]
  -- We now have:
  -- ((id ∘ id, counitMorFn ∘ unitMorFn), id ∘ unitIdMap, counitCompFn ∘ unitCompMap)
  -- = ((id, id), id, id)
  -- Split into components
  apply Prod.ext
  -- Goal 1 (fst): ObjMorMap equality ((objMap, morMap))
  · apply Prod.ext
    · rfl -- objMap = id ∘ id = id
    · -- morMap: (counitMorFn ∘ unitMorFn) = id
      simp only [Mor.ObjMorMap.morMap]
      funext m
      simp only [Function.comp_apply, unitMorMap, unitVar, PLangQuotientData.quotMor,
        toPLangQuotientData, Counit.counitEvalQuot,
        Quotient.lift_mk, Counit.counitEval, Counit.counitEvalAux,
        toPLangCatJudgCopr, toPLangCatJudgObjMor, toPLangCatJudgMor, id]
  -- Goal 2 (snd): (idMap, compMap) equality
  · apply Prod.ext
    · -- idMap: id ∘ unitIdMap = id
      simp only [Mor.CatJudgMap.idMap, unitIdMap_toPLang_eq_id, Function.comp_id]
    · -- compMap: show the composition map is identity
      funext p
      simp only [Function.comp_apply, Counit.counitEvalQuot, toPLangCatJudgCopr,
        toPLangCatJudgObjMor, toPLangCatJudgMor, toPLangQuotientData]
      rfl

end TriangleIdentities

/-! ## Left Triangle Identity

For X : CatJudgCopr, the left triangle identity states:
  ε_{L(X)} ∘ L(η_X) = id_{L(X)}

This operates at the category level (OverFunctorData), not the copresheaf level. -/

section LeftTriangle

variable (X : Obj.CatJudgCopr.{u, u, u, u})

/-- L(X): the quotient category from a CatJudgCopr. -/
abbrev triangleLX : OverCategoryData (toPLangQuotientData X).quotQuiver :=
  (toPLangQuotientData X).toOverCategoryData

/-- The quiver of L(X). -/
abbrev triangleLXQuiver : OverQuiver.{u, u} := (toPLangQuotientData X).quotQuiver

/-- Φ(L(X)): embedding L(X) back to CatJudgCopr. -/
abbrev trianglePhiLX : Obj.CatJudgCopr.{u, u, u, u} :=
  toPLangCatJudgCopr (triangleLX X)

/-- L(Φ(L(X))): applying L to Φ(L(X)).
    This is the quotient of the free category on the morphisms of L(X). -/
abbrev triangleLPhiLX :
    OverCategoryData (toPLangQuotientData (trianglePhiLX X)).quotQuiver :=
  (toPLangQuotientData (trianglePhiLX X)).toOverCategoryData

/-- The unit η_X : X → Φ(L(X)) as a CatJudgNatTrans. -/
abbrev unitX : Mor.CatJudgNatTrans X (unitTarget X) := unit X

/-- Type of bundled morphisms in L(X). These become the "generators" in L(Φ(L(X))). -/
abbrev bundledLXMor : Type u := triangleLXQuiver X |>.MorType

/-- Bundle a quotient morphism as a morphism of L(X)'s quiver. -/
def bundleQuotMorLX {a b : X.obj}
    (qm : (toPLangQuotientData X).QuotMor a b) : bundledLXMor X :=
  ⟨a, b, qm⟩

/-- The quotient type of Φ(L(X)) = toPLangQuotientData (trianglePhiLX X). -/
abbrev quotDataPhiLX : PLangQuotientData.{u} :=
  toPLangQuotientData (trianglePhiLX X)

/-- Embed a morphism of L(X) as a variable in the free category over Φ(L(X)).
    This is the morphism component of L(η_X). -/
def embedLXMorAsVar {a b : X.obj}
    (qm : (toPLangQuotientData X).QuotMor a b) :
    (quotDataPhiLX X).QuotMor a b :=
  (quotDataPhiLX X).quotMor (PFreeMor.var (bundleQuotMorLX X qm))

/-- The counit ε_{L(X)} : L(Φ(L(X))) → L(X) as an OverFunctorData.
    This evaluates free morphisms over L(X) back into L(X). -/
def counitAtLX :
    OverFunctorData (triangleLPhiLX X) (triangleLX X) :=
  Counit.counitFunctorData (triangleLX X)

/-- The left triangle identity on objects: ε_{L(X)}.objFn = id. -/
theorem leftTriangle_obj (a : X.obj) :
    (counitAtLX X).objFn a = a := rfl

/-- The left triangle identity on morphisms: for a quotient morphism qm in L(X),
    embedding it as a variable and evaluating gives back the bundled qm. -/
theorem leftTriangle_mor {a b : X.obj}
    (qm : (toPLangQuotientData X).QuotMor a b) :
    Counit.counitEvalQuot (triangleLX X) (embedLXMorAsVar X qm) =
    bundleQuotMorLX X qm := by
  simp only [embedLXMorAsVar, Counit.counitEvalQuot, PLangQuotientData.quotMor,
    Quotient.lift_mk, Counit.counitEval, Counit.counitEvalAux, bundleQuotMorLX]

/-! ### Factored Lemmas for L(η_X) Construction

These lemmas establish the structural properties needed to construct L(η_X)
as an OverFunctorData. The approach factors the proof into small lemmas,
each handling one type manipulation. -/

/-- The identity morphism in quotDataPhiLX X is the bundled identity from L(X). -/
theorem quotDataPhiLX_idMor (a : X.obj) :
    (quotDataPhiLX X).idMor a =
      bundleQuotMorLX X ((toPLangQuotientData X).quotId a) := rfl

/-- The source of an identity morphism in quotDataPhiLX is the object itself. -/
theorem quotDataPhiLX_idMor_src (a : X.obj) :
    (quotDataPhiLX X).quiver.src ((quotDataPhiLX X).idMor a) = a := rfl

/-- The target of an identity morphism in quotDataPhiLX is the object itself. -/
theorem quotDataPhiLX_idMor_tgt (a : X.obj) :
    (quotDataPhiLX X).quiver.tgt ((quotDataPhiLX X).idMor a) = a := rfl

/-- The idEndo condition for quotDataPhiLX is reflexivity. -/
theorem quotDataPhiLX_idEndo_eq (a : X.obj) :
    (quotDataPhiLX X).idEndo a = rfl := by
  rfl

/-- Embedding the identity quotient morphism as a variable equals the formal
    identity in the quotient category of Φ(L(X)).

    This is the first main factored lemma, using id_witness. -/
theorem embedLXMorAsVar_quotId (a : X.obj) :
    embedLXMorAsVar X ((toPLangQuotientData X).quotId a) =
      (quotDataPhiLX X).quotId a := by
  unfold embedLXMorAsVar bundleQuotMorLX
  unfold PLangQuotientData.quotId PLangQuotientData.quotMor
  -- Goal: ⟦var ⟨a, a, ⟦id a⟧⟩⟧ = ⟦id a⟧
  -- Need FreeMorEquiv (var ⟨a, a, ⟦id a⟧⟩) (id a)
  apply Quotient.sound
  -- id_witness gives: FreeMorEquivGen (cast (idEndo a) (var (idMor a))) (id (src (idMor a)))
  apply PLangQuotientData.FreeMorEquiv.rel
  -- Goal: FreeMorEquivGen (var ⟨a, a, ⟦id a⟧⟩) (id a)
  -- id_witness provides exactly this direction (after showing cast is trivial)
  have h := PLangQuotientData.FreeMorEquivGen.id_witness (D := quotDataPhiLX X) a
  -- h : FreeMorEquivGen (cast (idEndo a) (var (idMor a))) (id (src (idMor a)))
  -- idMor a = ⟨a, a, quotId a⟩, src (idMor a) = a
  -- So h : FreeMorEquivGen (cast ... (var ⟨a, a, quotId a⟩)) (id a)
  -- Need to show the cast is trivial (idEndo a = rfl)
  simp only [quotDataPhiLX_idMor, bundleQuotMorLX] at h
  convert h using 2

/-- Helper: compMatch for quotDataPhiLX is reflexivity.
    The tgt of the first morphism equals the src of the second, both being b. -/
theorem quotDataPhiLX_compMatch {a b c : X.obj}
    (qm₁ : (toPLangQuotientData X).QuotMor a b)
    (qm₂ : (toPLangQuotientData X).QuotMor b c) :
    (quotDataPhiLX X).compMatch
      ⟨(bundleQuotMorLX X qm₁, bundleQuotMorLX X qm₂), rfl⟩ = rfl := rfl

/-- Helper: compDom for quotDataPhiLX is reflexivity. -/
theorem quotDataPhiLX_compDom {a b c : X.obj}
    (qm₁ : (toPLangQuotientData X).QuotMor a b)
    (qm₂ : (toPLangQuotientData X).QuotMor b c) :
    (quotDataPhiLX X).compDom
      ⟨(bundleQuotMorLX X qm₁, bundleQuotMorLX X qm₂), rfl⟩ = rfl := rfl

/-- Helper: compCod for quotDataPhiLX is reflexivity. -/
theorem quotDataPhiLX_compCod {a b c : X.obj}
    (qm₁ : (toPLangQuotientData X).QuotMor a b)
    (qm₂ : (toPLangQuotientData X).QuotMor b c) :
    (quotDataPhiLX X).compCod
      ⟨(bundleQuotMorLX X qm₁, bundleQuotMorLX X qm₂), rfl⟩ = rfl := rfl

/-- Embedding the composite of two quotient morphisms equals the composite of
    their embeddings. This is the second main factored lemma, using comp_witness.

    This shows that L(η_X) preserves composition. -/
theorem embedLXMorAsVar_quotComp {a b c : X.obj}
    (qm₁ : (toPLangQuotientData X).QuotMor a b)
    (qm₂ : (toPLangQuotientData X).QuotMor b c) :
    embedLXMorAsVar X ((toPLangQuotientData X).quotComp qm₂ qm₁) =
      (quotDataPhiLX X).quotComp (embedLXMorAsVar X qm₂) (embedLXMorAsVar X qm₁)
    := by
  unfold embedLXMorAsVar bundleQuotMorLX
  unfold PLangQuotientData.quotComp PLangQuotientData.quotMor
  -- Goal: ⟦var ⟨a, c, quotComp qm₂ qm₁⟩⟧ = quotComp ⟦var ⟨b, c, qm₂⟩⟧ ⟦var ⟨a, b, qm₁⟩⟧
  -- RHS = ⟦comp (var ⟨b, c, qm₂⟩) (var ⟨a, b, qm₁⟩)⟧
  apply Quotient.sound
  apply PLangQuotientData.FreeMorEquiv.symm
  apply PLangQuotientData.FreeMorEquiv.rel
  -- Goal: FreeMorEquivGen (comp (var ...) (var ...)) (var (composite))
  -- comp_witness provides exactly this
  let p : (quotDataPhiLX X).CompWitness :=
    ⟨(bundleQuotMorLX X qm₁, bundleQuotMorLX X qm₂), rfl⟩
  have h := PLangQuotientData.FreeMorEquivGen.comp_witness (D := quotDataPhiLX X) p
  -- h relates comp (cast (compMatch p) (var (left p))) (var (right p))
  --          to cast (compDom p, compCod p) (var (composite p))
  simp only [cast_eq] at h
  convert h using 2

/-! ### Construction of L(η_X) as OverFunctorData

Using the factored lemmas, we now construct L(η_X) : L(X) → L(Φ(L(X))).
This maps each morphism in L(X) to its embedding as a variable in L(Φ(L(X))). -/

/-- The morphism map for L(η_X): embed each bundled morphism as a variable. -/
def LUnitX_morFn : (triangleLXQuiver X).MorType →
    (quotDataPhiLX X).quotQuiver.MorType :=
  fun m => ⟨m.1, m.2.1, embedLXMorAsVar X m.2.2⟩

/-- L(η_X) respects sources: trivial since objFn = id. -/
theorem LUnitX_src_comm (m : (triangleLXQuiver X).MorType) :
    (quotDataPhiLX X).quotQuiver.src (LUnitX_morFn X m) = m.1 := rfl

/-- L(η_X) respects targets: trivial since objFn = id. -/
theorem LUnitX_tgt_comm (m : (triangleLXQuiver X).MorType) :
    (quotDataPhiLX X).quotQuiver.tgt (LUnitX_morFn X m) = m.2.1 := rfl

/-- The quiver morphism component of L(η_X). -/
def LUnitX_quiverMor : OverQuiverMorphism (triangleLXQuiver X)
    (quotDataPhiLX X).quotQuiver where
  objFn := id
  morFn := LUnitX_morFn X
  src_comm := fun m => LUnitX_src_comm X m
  tgt_comm := fun m => LUnitX_tgt_comm X m

/-- L(η_X) preserves identities. -/
theorem LUnitX_map_id (a : X.obj) :
    LUnitX_morFn X ((triangleLX X).idFn a) =
      (triangleLPhiLX X).idFn a := by
  simp only [LUnitX_morFn, triangleLPhiLX, quotDataPhiLX,
    PLangQuotientData.toOverCategoryData, PLangQuotientData.quotCategoryOps,
    PLangQuotientData.quotIdFn]
  congr 2
  exact embedLXMorAsVar_quotId X a

/-- L(η_X) preserves composition. -/
theorem LUnitX_map_comp (p : (triangleLXQuiver X).ComposablePairsType) :
    LUnitX_morFn X ((triangleLX X).compFn p) =
      (triangleLPhiLX X).compFn ⟨(LUnitX_morFn X p.val.1, LUnitX_morFn X p.val.2),
        (LUnitX_tgt_comm X p.val.1).trans
          ((congrArg id p.property).trans
            (LUnitX_src_comm X p.val.2).symm)⟩ := by
  obtain ⟨⟨⟨a, b, qm₁⟩, ⟨b', c, qm₂⟩⟩, heq⟩ := p
  -- heq : b = b' (composability condition)
  cases heq
  simp only [LUnitX_morFn, triangleLPhiLX, quotDataPhiLX,
    PLangQuotientData.toOverCategoryData, PLangQuotientData.quotCategoryOps,
    PLangQuotientData.quotCompFn, PLangQuotientData.quotQuiver]
  congr 2
  simp only [embedLXMorAsVar_quotComp]

/-- L(η_X) : L(X) → L(Φ(L(X))) as a functor between OverCategoryData.
    This is the image of the unit η_X under the reflection functor L. -/
def LUnitX : OverFunctorData (triangleLX X) (triangleLPhiLX X) where
  toOverQuiverMorphism := LUnitX_quiverMor X
  map_id := LUnitX_map_id X
  map_comp := LUnitX_map_comp X

/-! ### Left Triangle Identity

The left triangle identity states that ε_{L(X)} ∘ L(η_X) = id_{L(X)}.
This follows from leftTriangle_obj and leftTriangle_mor. -/

/-- The composition ε_{L(X)} ∘ L(η_X) on objects is the identity. -/
theorem leftTriangle_comp_objFn (a : X.obj) :
    (counitAtLX X).objFn ((LUnitX X).objFn a) = a := rfl

/-- The composition ε_{L(X)} ∘ L(η_X) on morphisms is the identity.
    This is the essence of the left triangle identity. -/
theorem leftTriangle_comp_morFn (m : (triangleLXQuiver X).MorType) :
    (counitAtLX X).morFn ((LUnitX X).morFn m) = m := by
  obtain ⟨a, b, qm⟩ := m
  simp only [LUnitX, LUnitX_quiverMor, LUnitX_morFn, counitAtLX,
    Counit.counitFunctorData, Counit.counitQuiverMor]
  simp only [leftTriangle_mor, bundleQuotMorLX]

/-- The left triangle identity: ε_{L(X)} ∘ L(η_X) = id_{L(X)}.

    This is one of the two triangle identities for the adjunction L ⊣ Φ.
    Together with the right triangle, it establishes the adjunction. -/
theorem leftTriangle :
    (LUnitX X).comp (counitAtLX X) = OverFunctorData.id (triangleLX X) := by
  have h_obj : ∀ a, (counitAtLX X).objFn ((LUnitX X).objFn a) = a :=
    leftTriangle_comp_objFn X
  have h_mor : ∀ m, (counitAtLX X).morFn ((LUnitX X).morFn m) = m :=
    leftTriangle_comp_morFn X
  apply OverFunctorData.ext
  · ext a
    exact h_obj a
  · funext m
    exact h_mor m

end LeftTriangle

/-! ## Adjunction Bundle

With both triangle identities proven, we can bundle the adjunction data
L ⊣ Φ into a single structure. The adjunction L ⊣ Φ relates:

- Φ : Cat → CatJudgCopr (embedding functor, via toPLangCatJudgCopr)
- L : CatJudgCopr → Cat (reflection functor, via PLangQuotientData.toOverCategoryData)

For any X : CatJudgCopr, we have:
- Unit η_X : X → Φ(L(X))
- Counit ε_{L(X)} : L(Φ(L(X))) → L(X)
- Right triangle: Φ(ε_{L(X)}) ∘ η_{Φ(L(X))} = id_{Φ(L(X))}
- Left triangle: ε_{L(X)} ∘ L(η_X) = id_{L(X)}
-/

section AdjunctionBundle

variable (X : Obj.CatJudgCopr.{u, u, u, u})

/-- The full adjunction data for L ⊣ Φ at a CatJudgCopr X.
    This bundles both triangle identities at X. -/
structure AdjunctionDataAt where
  /-- The source CatJudgCopr. -/
  source : Obj.CatJudgCopr.{u, u, u, u}
  /-- The unit η_X : X → Φ(L(X)) at the copresheaf level. -/
  unitNatTrans : Mor.CatJudgNatTrans source (unitTarget source)
  /-- The right triangle: Φ(ε_{L(X)}) ∘ η_{Φ(L(X))} = id. -/
  rightTriangleId :
    unitThenPhiCounit (triangleLX source) = Cat.CatJudgNatTrans.id (trianglePhiLX source)
  /-- L(η_X) : L(X) → L(Φ(L(X))) at the category level. -/
  unitFunctor : OverFunctorData (triangleLX source) (triangleLPhiLX source)
  /-- The counit ε_{L(X)} : L(Φ(L(X))) → L(X). -/
  counitFunctor : OverFunctorData (triangleLPhiLX source) (triangleLX source)
  /-- The left triangle: ε_{L(X)} ∘ L(η_X) = id_{L(X)}. -/
  leftTriangleId : unitFunctor.comp counitFunctor =
    OverFunctorData.id (triangleLX source)

/-- Construct the adjunction data for any CatJudgCopr X. -/
def mkAdjunctionDataAt : AdjunctionDataAt where
  source := X
  unitNatTrans := unit X
  rightTriangleId := rightTriangle (triangleLX X)
  unitFunctor := LUnitX X
  counitFunctor := counitAtLX X
  leftTriangleId := leftTriangle X

/-- The L ⊣ Φ adjunction data at X. -/
def adjunctionAt : AdjunctionDataAt :=
  mkAdjunctionDataAt X

end AdjunctionBundle

/-! ## Mathlib Adjunction L ⊣ Φ

We construct the mathlib adjunction using `Adjunction.mkOfUnitCounit`. This
requires the unit and counit as natural transformations, plus the triangle
identities expressed as equations of morphisms.

For the unit: `𝟭 CatJudgCopr ⟶ LFunctorPLang ⋙ PhiFunctorPLang`
For the counit: `PhiFunctorPLang ⋙ LFunctorPLang ⟶ 𝟭 BundledOverCategoryData`
-/

section MathlibAdjunctionPLang

universe uAdj

variable {X Y : Obj.CatJudgCopr.{uAdj + 1, uAdj + 1, uAdj + 1, uAdj + 1}}

/-- The composition L ⋙ Φ applied to an object X. -/
abbrev LPhiObj (X : Obj.CatJudgCopr.{uAdj + 1, uAdj + 1, uAdj + 1, uAdj + 1}) :
    Obj.CatJudgCopr.{uAdj + 1, uAdj + 1, uAdj + 1, uAdj + 1} :=
  (LFunctorPLang ⋙ PhiFunctorPLang).obj X

/-- The target of the unit at X equals L ⋙ Φ applied to X. -/
theorem unitTarget_eq_LPhiObj :
    unitTarget X = LPhiObj X := rfl

/-- The unit component at X, with type adjusted for the NatTrans. -/
def unitApp (X : Obj.CatJudgCopr.{uAdj + 1, uAdj + 1, uAdj + 1, uAdj + 1}) :
    X ⟶ (LFunctorPLang ⋙ PhiFunctorPLang).obj X :=
  unit X

/-- The unit morphism map is natural: embedding α(m) as a variable equals
    applying (L ⋙ Φ)(α) to the embedded variable for m.

    This is the morphism-level naturality: `unit_Y(α_m) = (L ⋙ Φ)(α)(unit_X(m))`. -/
theorem unit_morMap_natural
    {X Y : Obj.CatJudgCopr.{uAdj + 1, uAdj + 1, uAdj + 1, uAdj + 1}}
    (α : Mor.CatJudgNatTrans X Y) (m : X.mor) :
    unitMorMap Y (α.morMap m) = mapBundledQuotMor α (unitMorMap X m) := by
  simp only [unitMorMap, mapBundledQuotMor, toPLangQuotientMorphism,
    PLangQuotientMorphism.quotMapMor, Quotient.lift_mk, unitVar,
    toPLangQuotientData, PLangQuotientData.quotMor, PFreeMor.mapQuiver]
  have hdom : Y.dom (α.morMap m) = α.objMap (X.dom m) :=
    (congrFun α.domProof m).symm
  have hcod : Y.cod (α.morMap m) = α.objMap (X.cod m) :=
    (congrFun α.codProof m).symm
  let D := toPLangQuotientData Y
  refine Sigma.ext hdom ?_
  refine sigma_heq_of_fst_eq_snd_heq
    (α := Y.obj) (I := Y.obj) (β := fun dom cod => D.QuotMor dom cod)
    hdom hcod ?_
  apply PLangQuotientData.quotMor_heq_of_both_cast_equiv D hdom hcod
  apply PLangQuotientData.FreeMorEquiv.refl

/-- Unit naturality: for any morphism α : X → Y, the unit components commute
    with the induced morphism on L ⋙ Φ. -/
theorem unit_naturality_PLang
    {X Y : Obj.CatJudgCopr.{uAdj + 1, uAdj + 1, uAdj + 1, uAdj + 1}}
    (α : X ⟶ Y) :
    α ≫ unitApp Y = unitApp X ≫ (LFunctorPLang ⋙ PhiFunctorPLang).map α := by
  apply Subtype.ext
  simp only [unitApp, CategoryStruct.comp, Cat.CatJudgNatTrans.comp,
    Cat.CatJudgMap.comp, Cat.ObjMap.comp, Functor.comp_obj, Functor.comp_map,
    LFunctorPLang, PhiFunctorPLang, bundleQuotientCategory, reflectionL_map,
    toPLangCatJudgNatTrans, unit, unitCatJudgMap]
  apply Prod.ext
  · apply Prod.ext
    · rfl
    · funext m
      exact unit_morMap_natural α m
  · apply Prod.ext
    · -- idMap component: unitIdMap Y ∘ α.idMap = α.objMap ∘ unitIdMap X
      funext i
      simp only [Mor.CatJudgMap.idMap, Mor.CatJudgNatTrans.map, Function.comp_apply,
        toPLangCatJudgMap, unitIdMap, Mor.CatJudgNatTrans.objMap]
      change Y.dom (Y.idMor (α.idMap i)) = α.objMap (X.dom (X.idMor i))
      have h : Y.idMor (α.idMap i) = α.morMap (X.idMor i) :=
        (congrFun α.idMorProof i).symm
      rw [h]
      exact (congrFun α.domProof (X.idMor i)).symm
    · -- compMap component
      funext c
      simp only [Mor.CatJudgMap.compMap, Mor.CatJudgNatTrans.map, Function.comp_apply,
        toPLangCatJudgMap, unitCompMap, mapBundledQuotMor, Mor.CatJudgNatTrans.objMap]
      apply Subtype.ext
      simp only [Prod.ext_iff]
      constructor
      · change unitMorMap Y (Y.right (α.compMap c)) =
          mapBundledQuotMor α (unitMorMap X (X.right c))
        have h : Y.right (α.compMap c) = α.morMap (X.right c) :=
          (congrFun α.rightProof c).symm
        rw [h]
        exact unit_morMap_natural α (X.right c)
      · change unitMorMap Y (Y.left (α.compMap c)) =
          mapBundledQuotMor α (unitMorMap X (X.left c))
        have h : Y.left (α.compMap c) = α.morMap (X.left c) :=
          (congrFun α.leftProof c).symm
        rw [h]
        exact unit_morMap_natural α (X.left c)

/-- The unit as a natural transformation for the PLang adjunction. -/
def unitNatTransPLang :
    𝟭 Obj.CatJudgCopr.{uAdj + 1, uAdj + 1, uAdj + 1, uAdj + 1} ⟶
    LFunctorPLang ⋙ PhiFunctorPLang where
  app := unitApp
  naturality := fun _ _ α => unit_naturality_PLang α

end MathlibAdjunctionPLang

end ReflectionL

/-! # Universe-Flexible Adjunction

This section constructs the adjunction L ⊣ Φ with independent universe levels.
The goal is to define:
- `Φ : Cat.{v, u} ⥤ CatJudgCopr.{u, v, w, x}`
- `L : CatJudgCopr.{u, v, w, x} ⥤ Cat.{v, u}`

The generalization is `PLangQuotientDataFlex` which separates the four
universe levels instead of using a single level for all components. -/

section FlexibleUniverseAdjunction

universe uF vF wF xF

/-! ## Generalized Quotient Data

`PLangQuotientDataFlex` has four independent universe levels for:
- Objects (uF)
- Morphisms (vF)
- Identity witnesses (wF)
- Composition witnesses (xF) -/

/-- Generalized quotient data with four independent universe levels.
    This separates object, morphism, identity witness, and composition witness
    universes. -/
structure PLangQuotientDataFlex where
  /-- The underlying quiver with objects at uF and morphisms at vF. -/
  quiver : OverQuiver.{vF, uF}
  /-- The type of identity witnesses. -/
  IdWitness : Type wF
  /-- The type of composition witnesses. -/
  CompWitness : Type xF
  /-- Get the identity morphism for a witness. -/
  idMor : IdWitness → quiver.MorType
  /-- Identity morphisms are endomorphisms. -/
  idEndo : ∀ i, quiver.src (idMor i) = quiver.tgt (idMor i)
  /-- Get the left morphism of a composition witness. -/
  left : CompWitness → quiver.MorType
  /-- Get the right morphism of a composition witness. -/
  right : CompWitness → quiver.MorType
  /-- Get the composite morphism. -/
  composite : CompWitness → quiver.MorType
  /-- Left and right are composable. -/
  compMatch : ∀ c, quiver.tgt (right c) = quiver.src (left c)
  /-- Domain of composite equals domain of right. -/
  compDom : ∀ c, quiver.src (composite c) = quiver.src (right c)
  /-- Codomain of composite equals codomain of left. -/
  compCod : ∀ c, quiver.tgt (composite c) = quiver.tgt (left c)

namespace PLangQuotientDataFlex

/-- Convert a CatJudgCopr with flexible universe levels to quotient data. -/
def ofCatJudgCopr (C : Obj.CatJudgCopr.{uF, vF, wF, xF}) :
    PLangQuotientDataFlex.{uF, vF, wF, xF} where
  quiver := {
    Obj := C.obj
    MorType := C.mor
    src := C.dom
    tgt := C.cod
  }
  IdWitness := C.idType
  CompWitness := C.compType
  idMor := C.idMor
  idEndo := fun i => congrFun C.endoProof i
  left := C.left
  right := C.right
  composite := C.composite
  compMatch := fun c => congrFun C.compMatchProof c
  compDom := fun c => congrFun C.compDomProof c
  compCod := fun c => congrFun C.compCodProof c

end PLangQuotientDataFlex

/-! ## Free Morphisms with Flexible Universes

Free morphisms over a quiver with independent object and morphism universes. -/

/-- Free morphisms in a quiver with flexible universe levels.
    Objects at universe uF, morphisms at universe vF. -/
inductive PFreeMorFlex (Q : OverQuiver.{vF, uF}) : Q.Obj → Q.Obj → Type (max uF vF) where
  /-- Inject a morphism from the base quiver. -/
  | var (f : Q.MorType) : PFreeMorFlex Q (Q.src f) (Q.tgt f)
  /-- Identity morphism at an object. -/
  | id (a : Q.Obj) : PFreeMorFlex Q a a
  /-- Composition: g . f (f first, then g). -/
  | comp {a b c : Q.Obj} (g : PFreeMorFlex Q b c) (f : PFreeMorFlex Q a b) :
      PFreeMorFlex Q a c

namespace PFreeMorFlex

variable {Q : OverQuiver.{vF, uF}}

/-- The size of a free morphism (number of constructors). -/
def size : {a b : Q.Obj} → PFreeMorFlex Q a b → Nat
  | _, _, var _ => 1
  | _, _, id _ => 1
  | _, _, comp g f => 1 + g.size + f.size

end PFreeMorFlex

/-! ## Quotient Equivalence Relation

The equivalence relation on free morphisms for the flexible-universe case. -/

namespace PLangQuotientDataFlex

variable (D : PLangQuotientDataFlex.{uF, vF, wF, xF})

/-- The generators for the equivalence relation on free morphisms.
    This includes:
    - Category axioms (identity laws, associativity)
    - Witness relations (identity and composition witnesses) -/
inductive FreeMorEquivGenFlex : {a b : D.quiver.Obj} →
    PFreeMorFlex D.quiver a b → PFreeMorFlex D.quiver a b → Prop where
  /-- Left identity: id ∘ f ~ f -/
  | id_left {a b : D.quiver.Obj} (f : PFreeMorFlex D.quiver a b) :
      FreeMorEquivGenFlex (.comp (.id b) f) f
  /-- Right identity: f ∘ id ~ f -/
  | id_right {a b : D.quiver.Obj} (f : PFreeMorFlex D.quiver a b) :
      FreeMorEquivGenFlex (.comp f (.id a)) f
  /-- Associativity: (h ∘ g) ∘ f ~ h ∘ (g ∘ f) -/
  | assoc {a b c d : D.quiver.Obj}
      (h : PFreeMorFlex D.quiver c d)
      (g : PFreeMorFlex D.quiver b c)
      (f : PFreeMorFlex D.quiver a b) :
      FreeMorEquivGenFlex (.comp (.comp h g) f) (.comp h (.comp g f))
  /-- Identity witness: cast(var(idMor i)) ~ id (src (idMor i))
      The variable morphism for an identity witness is equivalent to the
      identity at that object. -/
  | id_witness (i : D.IdWitness) :
      FreeMorEquivGenFlex
        (cast (by rw [D.idEndo i]) (PFreeMorFlex.var (D.idMor i)))
        (PFreeMorFlex.id (D.quiver.src (D.idMor i)))
  /-- Composition witness: comp (cast(var left)) (var right) ~ cast(var composite)
      The composition of the left and right variable morphisms is equivalent
      to the variable morphism for the composite. -/
  | comp_witness (c : D.CompWitness) :
      FreeMorEquivGenFlex
        (PFreeMorFlex.comp
          (cast (by rw [D.compMatch c]) (PFreeMorFlex.var (D.left c)))
          (PFreeMorFlex.var (D.right c)))
        (cast (by rw [D.compDom c, D.compCod c]) (PFreeMorFlex.var (D.composite c)))

/-- The equivalence relation on free morphisms: reflexive-symmetric-transitive
    closure of the generators, extended to congruence under composition. -/
inductive FreeMorEquivFlex : {a b : D.quiver.Obj} →
    PFreeMorFlex D.quiver a b → PFreeMorFlex D.quiver a b → Prop where
  /-- Base case: from generators -/
  | gen {a b : D.quiver.Obj} {f g : PFreeMorFlex D.quiver a b} :
      D.FreeMorEquivGenFlex f g → FreeMorEquivFlex f g
  /-- Reflexivity -/
  | refl {a b : D.quiver.Obj} (f : PFreeMorFlex D.quiver a b) :
      FreeMorEquivFlex f f
  /-- Symmetry -/
  | symm {a b : D.quiver.Obj} {f g : PFreeMorFlex D.quiver a b} :
      FreeMorEquivFlex f g → FreeMorEquivFlex g f
  /-- Transitivity -/
  | trans {a b : D.quiver.Obj} {f g h : PFreeMorFlex D.quiver a b} :
      FreeMorEquivFlex f g → FreeMorEquivFlex g h → FreeMorEquivFlex f h
  /-- Left congruence: f ~ g implies h ∘ f ~ h ∘ g -/
  | cong_left {a b c : D.quiver.Obj}
      {f g : PFreeMorFlex D.quiver a b}
      (h : PFreeMorFlex D.quiver b c) :
      FreeMorEquivFlex f g → FreeMorEquivFlex (.comp h f) (.comp h g)
  /-- Right congruence: f ~ g implies f ∘ h ~ g ∘ h -/
  | cong_right {a b c : D.quiver.Obj}
      {f g : PFreeMorFlex D.quiver b c}
      (h : PFreeMorFlex D.quiver a b) :
      FreeMorEquivFlex f g → FreeMorEquivFlex (.comp f h) (.comp g h)

theorem FreeMorEquivFlex.isEquivalence {a b : D.quiver.Obj} :
    Equivalence (FreeMorEquivFlex D (a := a) (b := b)) where
  refl := FreeMorEquivFlex.refl
  symm := FreeMorEquivFlex.symm
  trans := FreeMorEquivFlex.trans

/-- The setoid on free morphisms induced by the equivalence relation. -/
def freeMorSetoidFlex (a b : D.quiver.Obj) :
    Setoid (PFreeMorFlex D.quiver a b) where
  r := FreeMorEquivFlex D
  iseqv := FreeMorEquivFlex.isEquivalence D

/-- Quotient morphisms: free morphisms modulo the equivalence relation. -/
def QuotMorFlex (a b : D.quiver.Obj) : Type (max uF vF) :=
  Quotient (D.freeMorSetoidFlex a b)

/-- The quotient map from free morphisms to quotient morphisms. -/
def quotMorFlex {a b : D.quiver.Obj} (f : PFreeMorFlex D.quiver a b) :
    D.QuotMorFlex a b :=
  Quotient.mk (D.freeMorSetoidFlex a b) f

/-- Composition respects the equivalence relation. -/
theorem comp_respects_flex {a b c : D.quiver.Obj}
    {f₁ f₂ : PFreeMorFlex D.quiver a b}
    {g₁ g₂ : PFreeMorFlex D.quiver b c}
    (hf : FreeMorEquivFlex D f₁ f₂) (hg : FreeMorEquivFlex D g₁ g₂) :
    FreeMorEquivFlex D (.comp g₁ f₁) (.comp g₂ f₂) :=
  FreeMorEquivFlex.trans
    (FreeMorEquivFlex.cong_left g₁ hf)
    (FreeMorEquivFlex.cong_right f₂ hg)

/-- Composition of quotient morphisms. -/
def quotCompFlex {a b c : D.quiver.Obj} :
    D.QuotMorFlex a b → D.QuotMorFlex b c → D.QuotMorFlex a c :=
  Quotient.lift₂
    (fun f g => D.quotMorFlex (.comp g f))
    (fun _ _ _ _ hf hg => Quotient.sound (D.comp_respects_flex hf hg))

/-- Identity quotient morphism. -/
def quotIdFlex (a : D.quiver.Obj) : D.QuotMorFlex a a :=
  D.quotMorFlex (.id a)

/-- Left identity law for quotient morphisms. -/
theorem quotCompFlex_id_left {a b : D.quiver.Obj} (f : D.QuotMorFlex a b) :
    D.quotCompFlex f (D.quotIdFlex b) = f := by
  induction f using Quotient.inductionOn with
  | h fm =>
    simp only [quotCompFlex, quotIdFlex, quotMorFlex, Quotient.lift₂_mk]
    apply Quotient.sound
    exact FreeMorEquivFlex.gen (FreeMorEquivGenFlex.id_left fm)

/-- Right identity law for quotient morphisms. -/
theorem quotCompFlex_id_right {a b : D.quiver.Obj} (f : D.QuotMorFlex a b) :
    D.quotCompFlex (D.quotIdFlex a) f = f := by
  induction f using Quotient.inductionOn with
  | h fm =>
    simp only [quotCompFlex, quotIdFlex, quotMorFlex, Quotient.lift₂_mk]
    apply Quotient.sound
    exact FreeMorEquivFlex.gen (FreeMorEquivGenFlex.id_right fm)

/-- Associativity law for quotient morphisms.
    Note: assoc generator gives (h ∘ g) ∘ f ~ h ∘ (g ∘ f), but quotCompFlex f g = ⟦g ∘ f⟧,
    so the equation quotCompFlex (quotCompFlex f g) h = quotCompFlex f (quotCompFlex g h)
    becomes ⟦h ∘ (g ∘ f)⟧ = ⟦(h ∘ g) ∘ f⟧, requiring the symmetric direction. -/
theorem quotCompFlex_assoc {a b c d : D.quiver.Obj}
    (f : D.QuotMorFlex a b) (g : D.QuotMorFlex b c) (h : D.QuotMorFlex c d) :
    D.quotCompFlex (D.quotCompFlex f g) h =
      D.quotCompFlex f (D.quotCompFlex g h) := by
  induction f using Quotient.inductionOn with
  | h fm =>
    induction g using Quotient.inductionOn with
    | h gm =>
      induction h using Quotient.inductionOn with
      | h hm =>
        simp only [quotCompFlex, quotMorFlex, Quotient.lift₂_mk]
        apply Quotient.sound
        exact FreeMorEquivFlex.symm
          (FreeMorEquivFlex.gen (FreeMorEquivGenFlex.assoc hm gm fm))

/-- The quotient quiver with flexible universes. -/
def quotQuiverFlex : OverQuiver.{max uF vF, uF} where
  Obj := D.quiver.Obj
  MorType := Σ (a b : D.quiver.Obj), D.QuotMorFlex a b
  src := fun m => m.1
  tgt := fun m => m.2.1

/-- Bundle a quotient morphism with its source and target. -/
def bundleQuotMorFlex {a b : D.quiver.Obj} (f : D.QuotMorFlex a b) :
    D.quotQuiverFlex.MorType :=
  ⟨a, b, f⟩

/-- Identity function on the quotient quiver. -/
def quotIdFnFlex : D.quotQuiverFlex.Obj → D.quotQuiverFlex.MorType :=
  fun a => D.bundleQuotMorFlex (D.quotIdFlex a)

/-- Composition function on the quotient quiver.
    Given composable pair (m1, m2) where m1.tgt = m2.src, compose their morphisms. -/
def quotCompFnFlex :
    D.quotQuiverFlex.ComposablePairsType → D.quotQuiverFlex.MorType :=
  fun p =>
    let ⟨⟨m1, m2⟩, hcomp⟩ := p
    -- m1 = ⟨a, b, f⟩ : src=a, tgt=b, mor=f : QuotMorFlex a b
    -- m2 = ⟨c, d, g⟩ : src=c, tgt=d, mor=g : QuotMorFlex c d
    -- hcomp : Composable m1 m2 = (tgt m1 = src m2) = (b = c)
    let f := m1.2.2  -- f : QuotMorFlex m1.1 m1.2.1
    let g := m2.2.2  -- g : QuotMorFlex m2.1 m2.2.1
    -- Extract the equality from hcomp: m1.2.1 = m2.1
    have heq : m1.2.1 = m2.1 := hcomp
    -- Cast g to have source m1.2.1 instead of m2.1
    -- g : QuotMorFlex m2.1 m2.2.1, need QuotMorFlex m1.2.1 m2.2.1
    -- heq.symm : m2.1 = m1.2.1 lets us substitute
    let g' : D.QuotMorFlex m1.2.1 m2.2.1 :=
      cast (congrArg (D.QuotMorFlex · m2.2.1) heq.symm) g
    -- Result: composition from m1.1 to m2.2.1
    D.bundleQuotMorFlex (D.quotCompFlex f g')

/-- Left identity: compFn (id, f) = f when tgt id = src f -/
theorem quotCompFnFlex_id_comp {a b : D.quiver.Obj} (f : D.QuotMorFlex a b) :
    D.quotCompFnFlex ⟨(D.bundleQuotMorFlex (D.quotIdFlex a),
                       D.bundleQuotMorFlex f), rfl⟩ = D.bundleQuotMorFlex f := by
  simp only [quotCompFnFlex, bundleQuotMorFlex, quotIdFlex]
  -- Goal: ⟨a, ⟨b, quotCompFlex (quotMorFlex (id a)) (cast _ f)⟩⟩ = ⟨a, ⟨b, f⟩⟩
  -- Cast from (a = a) is identity
  simp only [cast_eq]
  -- Goal: ⟨a, ⟨b, quotCompFlex (quotMorFlex (id a)) f⟩⟩ = ⟨a, ⟨b, f⟩⟩
  congr 2
  exact D.quotCompFlex_id_right f

/-- Right identity: compFn (f, id) = f when tgt f = src id -/
theorem quotCompFnFlex_comp_id {a b : D.quiver.Obj} (f : D.QuotMorFlex a b) :
    D.quotCompFnFlex ⟨(D.bundleQuotMorFlex f,
                       D.bundleQuotMorFlex (D.quotIdFlex b)), rfl⟩ = D.bundleQuotMorFlex f := by
  simp only [quotCompFnFlex, bundleQuotMorFlex, quotIdFlex]
  simp only [cast_eq]
  congr 2
  exact D.quotCompFlex_id_left f

/-- The quotient forms an OverCategoryData. -/
def toOverCategoryDataFlex : OverCategoryData D.quotQuiverFlex where
  idFn := D.quotIdFnFlex
  compFn := D.quotCompFnFlex
  id_src := fun _ => rfl
  id_tgt := fun _ => rfl
  comp_src := fun _ => rfl
  comp_tgt := fun _ => rfl
  id_comp := fun f => by
    obtain ⟨a, b, fm⟩ := f
    exact D.quotCompFnFlex_id_comp fm
  comp_id := fun f => by
    obtain ⟨a, b, fm⟩ := f
    exact D.quotCompFnFlex_comp_id fm
  assoc := fun t => by
    obtain ⟨⟨⟨a, b, fm⟩, ⟨b', c, gm⟩, ⟨c', d, hm⟩⟩, hcomp1, hcomp2⟩ := t
    -- hcomp1 : b = b', hcomp2 : c = c'
    simp only [quotQuiverFlex, OverQuiver.Composable] at hcomp1 hcomp2
    subst hcomp1 hcomp2
    simp only [quotCompFnFlex, bundleQuotMorFlex]
    simp only [cast_eq]
    congr 2
    exact D.quotCompFlex_assoc fm gm hm

end PLangQuotientDataFlex

/-! ## Reflection Functor L with Flexible Universes -/

/-- The reflection functor L on objects: takes a CatJudgCopr and produces
    its quotient category as OverCategoryData. -/
def reflectionLFlex (C : Obj.CatJudgCopr.{uF, vF, wF, xF}) :
    OverCategoryData (PLangQuotientDataFlex.ofCatJudgCopr C).quotQuiverFlex :=
  (PLangQuotientDataFlex.ofCatJudgCopr C).toOverCategoryDataFlex

end FlexibleUniverseAdjunction

end GebLean
