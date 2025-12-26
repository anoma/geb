import GebLean.PLang.CatJudgment
import GebLean.Utilities.Category
import GebLean.Utilities.Equalities
import Mathlib.CategoryTheory.Category.Cat

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

end ReflectionL

end GebLean
