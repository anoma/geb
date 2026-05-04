import GebLean.CategoryJudgments
import GebLean.Utilities.Category
import GebLean.Utilities.OverCategoryEquiv
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Adjunction.Reflective

/-!
# Category-Copresheaf Adjunction

This file implements the adjunction between the category of small categories
(represented via `OverCategoryData`) and the category of copresheaves on
`CategoryJudgments` (represented via `CategoryJudgments.FunctorData`).

The adjunction consists of:
- An embedding functor Phi : Cat -> [J, Type] that sends a category to its
  associated copresheaf
- A reflection functor L : [J, Type] -> Cat that sends a copresheaf to the
  free category on its quiver, quotiented by identity and composition relations

## Main definitions

### Free Morphisms

- `FreeMor`: Free morphisms in a quiver, represented as binary trees of
  compositions. This is the free category on a quiver before quotienting.
- `FreeMor.var`: Inject a base morphism
- `FreeMor.id`: Identity morphism
- `FreeMor.comp`: Composition of free morphisms

### Equivalence Relations

- `FreeMorEquivGen`: Generating relations for equivalence (category axioms,
  copresheaf relations, and congruence)
- `FreeMorEquiv`: Full equivalence relation (closure under refl/symm/trans)

### Embedding Functor Phi

- `OverCategoryData.toJudgmentFunctorData`: Convert a category to a copresheaf

### Reflection Functor L

- `CategoryJudgments.FunctorData.toOverCategoryData`: Convert a copresheaf to
  a category via the quotient of free morphisms

## References

See `docs/categories-as-copresheaves.md` for mathematical background.
-/

namespace GebLean

open CategoryTheory

universe v u

/-! ## Embedding Functor Phi: OverCategoryData -> FunctorData

Given a category (as OverCategoryData), we construct a copresheaf on
CategoryJudgments. -/

section EmbeddingPhi

variable {Q : OverQuiver.{u, u}} (C : OverCategoryData Q)

/-- The copresheaf on CategoryJudgments corresponding to a category.
    We use Q.ComposablePairsType directly for the composition type. -/
def OverCategoryData.toJudgmentFunctorData :
    CategoryJudgments.FunctorData (Type u) where
  objC := Q.Obj
  morC := Q.MorType
  idC := Q.Obj
  compC := Q.ComposablePairsType
  dom := Q.src
  cod := Q.tgt
  idMor := C.idFn
  left := fun p => p.val.2
  right := fun p => p.val.1
  composite := fun p => C.compFn p
  h_id_endo := by
    funext a
    exact (C.id_src a).trans (C.id_tgt a).symm
  h_comp_match := by
    funext p
    exact p.property
  h_comp_dom := by
    funext p
    exact C.comp_src p
  h_comp_cod := by
    funext p
    exact C.comp_tgt p

end EmbeddingPhi

/-! ## Category Quotient Data

A structure representing a quiver with identity and composition witnesses,
which will be used to form a category via quotienting free morphisms. -/

/-- Data for quotienting free morphisms to form a category. This includes:
    - A base quiver
    - Identity witnesses (which morphisms should behave as identities)
    - Composition witnesses (which triples should satisfy g . f = h)
-/
structure CategoryQuotientData where
  /-- The underlying quiver. -/
  quiver : OverQuiver.{v, u}
  /-- The type of identity witnesses. -/
  IdWitness : Type u
  /-- Which object each identity witness is for. -/
  idObj : IdWitness → quiver.Obj
  /-- Which morphism is the declared identity. -/
  idMor : IdWitness → quiver.MorType
  /-- The identity morphism is an endomorphism on the witnessed object. -/
  id_src : ∀ i, quiver.src (idMor i) = idObj i
  id_tgt : ∀ i, quiver.tgt (idMor i) = idObj i
  /-- The type of composition witnesses. -/
  CompWitness : Type u
  /-- The right (first) morphism of a composition. -/
  compRight : CompWitness → quiver.MorType
  /-- The left (second) morphism of a composition. -/
  compLeft : CompWitness → quiver.MorType
  /-- The declared composite. -/
  compComposite : CompWitness → quiver.MorType
  /-- The morphisms are composable. -/
  comp_match : ∀ c, quiver.tgt (compRight c) = quiver.src (compLeft c)
  /-- Domain of composite matches domain of right. -/
  comp_dom : ∀ c, quiver.src (compComposite c) = quiver.src (compRight c)
  /-- Codomain of composite matches codomain of left. -/
  comp_cod : ∀ c, quiver.tgt (compComposite c) = quiver.tgt (compLeft c)

/-! ## Free Morphisms

Free morphisms in a quiver, represented as binary trees of compositions.
This is the free category on a quiver (before quotienting by category laws). -/

/-- Free morphisms in a quiver. These form binary trees where:
    - `var f` injects a base morphism from the quiver
    - `id a` is an identity morphism at object a
    - `comp g f` is the composition g . f (f first, then g)

    The source and target are tracked in the type indices. -/
inductive FreeMor (Q : OverQuiver.{v, u}) : Q.Obj → Q.Obj → Type (max v u) where
  /-- Inject a morphism from the base quiver. -/
  | var (f : Q.MorType) : FreeMor Q (Q.src f) (Q.tgt f)
  /-- Identity morphism at an object. -/
  | id (a : Q.Obj) : FreeMor Q a a
  /-- Composition: g . f (f first, then g). -/
  | comp {a b c : Q.Obj} (g : FreeMor Q b c) (f : FreeMor Q a b) : FreeMor Q a c

namespace FreeMor

variable {Q : OverQuiver.{v, u}}

/-- The size of a free morphism (number of constructors). -/
def size : {a b : Q.Obj} → FreeMor Q a b → Nat
  | _, _, var _ => 1
  | _, _, id _ => 1
  | _, _, comp g f => 1 + g.size + f.size

/-- Map a free morphism through a quiver morphism. -/
def map {Q₁ Q₂ : OverQuiver.{v, u}} (F : OverQuiverMorphism Q₁ Q₂)
    {a b : Q₁.Obj} : FreeMor Q₁ a b → FreeMor Q₂ (F.objFn a) (F.objFn b)
  | var f => F.src_comm f ▸ F.tgt_comm f ▸ var (F.morFn f)
  | id _ => id _
  | comp g f => comp (map F g) (map F f)

end FreeMor

namespace CategoryQuotientData

variable (D : CategoryQuotientData.{v, u})

/-! ## Equivalence Relations on Free Morphisms

The equivalence relation on free morphisms is generated by:
1. Category axioms: left identity, right identity, associativity
2. Copresheaf relations: identity and composition witnesses
3. Congruence: equivalence propagates through composition -/

/-- Generating relations for equivalence on free morphisms.
    These include category axioms, copresheaf-specified relations, and
    congruence through composition. -/
inductive FreeMorEquivGen : {a b : D.quiver.Obj} →
    FreeMor D.quiver a b → FreeMor D.quiver a b → Prop where
  /-- Left identity: id . f ~ f -/
  | id_left {a b : D.quiver.Obj} (f : FreeMor D.quiver a b) :
      FreeMorEquivGen (FreeMor.comp (FreeMor.id b) f) f
  /-- Right identity: f . id ~ f -/
  | id_right {a b : D.quiver.Obj} (f : FreeMor D.quiver a b) :
      FreeMorEquivGen (FreeMor.comp f (FreeMor.id a)) f
  /-- Associativity: h . (g . f) ~ (h . g) . f -/
  | assoc {a b c d : D.quiver.Obj}
      (h : FreeMor D.quiver c d) (g : FreeMor D.quiver b c)
      (f : FreeMor D.quiver a b) :
      FreeMorEquivGen (FreeMor.comp h (FreeMor.comp g f))
                      (FreeMor.comp (FreeMor.comp h g) f)
  /-- Identity witness: var(idMor i) ~ id(idObj i)
      The variable morphism for an identity witness is equivalent to the
      identity at that object. We cast the variable to have the correct
      source and target indices. -/
  | id_witness (i : D.IdWitness) :
      FreeMorEquivGen
        (cast (by rw [D.id_src i, D.id_tgt i]) (FreeMor.var (D.idMor i)))
        (FreeMor.id (D.idObj i))
  /-- Composition witness: var(left c) . var(right c) ~ var(composite c)
      The composition of the left and right variable morphisms is equivalent
      to the variable morphism for the composite. -/
  | comp_witness (c : D.CompWitness) :
      FreeMorEquivGen
        (FreeMor.comp
          (cast (by rw [D.comp_match c]) (FreeMor.var (D.compLeft c)))
          (FreeMor.var (D.compRight c)))
        (cast (by rw [D.comp_dom c, D.comp_cod c])
          (FreeMor.var (D.compComposite c)))
  /-- Left congruence: if f ~ g then h . f ~ h . g -/
  | cong_left {a b c : D.quiver.Obj}
      {f g : FreeMor D.quiver a b} (h : FreeMor D.quiver b c) :
      FreeMorEquivGen f g →
      FreeMorEquivGen (FreeMor.comp h f) (FreeMor.comp h g)
  /-- Right congruence: if f ~ g then f . k ~ g . k -/
  | cong_right {a b c : D.quiver.Obj}
      {f g : FreeMor D.quiver b c} (k : FreeMor D.quiver a b) :
      FreeMorEquivGen f g →
      FreeMorEquivGen (FreeMor.comp f k) (FreeMor.comp g k)

/-- The full equivalence relation on free morphisms, defined as the
    equivalence closure of FreeMorEquivGen. -/
inductive FreeMorEquiv : {a b : D.quiver.Obj} →
    FreeMor D.quiver a b → FreeMor D.quiver a b → Prop where
  /-- Include the generating relation. -/
  | rel {a b : D.quiver.Obj} {f g : FreeMor D.quiver a b} :
      FreeMorEquivGen D f g → FreeMorEquiv f g
  /-- Reflexivity. -/
  | refl {a b : D.quiver.Obj} (f : FreeMor D.quiver a b) : FreeMorEquiv f f
  /-- Symmetry. -/
  | symm {a b : D.quiver.Obj} {f g : FreeMor D.quiver a b} :
      FreeMorEquiv f g → FreeMorEquiv g f
  /-- Transitivity. -/
  | trans {a b : D.quiver.Obj} {f g h : FreeMor D.quiver a b} :
      FreeMorEquiv f g → FreeMorEquiv g h → FreeMorEquiv f h

/-- FreeMorEquivGen implies FreeMorEquiv. -/
theorem FreeMorEquivGen.toFreeMorEquiv {a b : D.quiver.Obj}
    {f g : FreeMor D.quiver a b} (h : FreeMorEquivGen D f g) :
    FreeMorEquiv D f g :=
  FreeMorEquiv.rel h

/-- FreeMorEquiv is an equivalence relation. -/
theorem FreeMorEquiv.isEquivalence {a b : D.quiver.Obj} :
    Equivalence (FreeMorEquiv D (a := a) (b := b)) where
  refl := FreeMorEquiv.refl
  symm := FreeMorEquiv.symm
  trans := FreeMorEquiv.trans

/-- Left congruence for FreeMorEquiv. -/
theorem FreeMorEquiv.cong_left {a b c : D.quiver.Obj}
    {f g : FreeMor D.quiver a b} (h : FreeMor D.quiver b c)
    (eq : FreeMorEquiv D f g) :
    FreeMorEquiv D (FreeMor.comp h f) (FreeMor.comp h g) := by
  induction eq with
  | rel hr => exact FreeMorEquiv.rel (FreeMorEquivGen.cong_left h hr)
  | refl _ => exact FreeMorEquiv.refl _
  | symm _ ih => exact FreeMorEquiv.symm ih
  | trans _ _ ih1 ih2 => exact FreeMorEquiv.trans ih1 ih2

/-- Right congruence for FreeMorEquiv. -/
theorem FreeMorEquiv.cong_right {a b c : D.quiver.Obj}
    {f g : FreeMor D.quiver b c} (k : FreeMor D.quiver a b)
    (eq : FreeMorEquiv D f g) :
    FreeMorEquiv D (FreeMor.comp f k) (FreeMor.comp g k) := by
  induction eq with
  | rel hr => exact FreeMorEquiv.rel (FreeMorEquivGen.cong_right k hr)
  | refl _ => exact FreeMorEquiv.refl _
  | symm _ ih => exact FreeMorEquiv.symm ih
  | trans _ _ ih1 ih2 => exact FreeMorEquiv.trans ih1 ih2

/-- Cast preserves FreeMorEquiv: if f ~ g at indices (a, b), then
    cast f ~ cast g at indices (a', b'). -/
theorem FreeMorEquiv.cast {a b a' b' : D.quiver.Obj}
    {f g : FreeMor D.quiver a b}
    (ha : a = a') (hb : b = b')
    (eq : FreeMorEquiv D f g) :
    FreeMorEquiv D
      (cast (congrArg₂ (FreeMor D.quiver) ha hb) f)
      (cast (congrArg₂ (FreeMor D.quiver) ha hb) g) := by
  subst ha hb
  simp only [congrArg₂, cast_eq]
  exact eq

/-- Casts distribute over FreeMor.comp: casting the components gives the same result
    as casting the composite. -/
theorem FreeMor.cast_comp {a a' b b' c c' : D.quiver.Obj}
    (ha : a = a') (hb : b = b') (hc : c = c')
    (g : FreeMor D.quiver b c) (f : FreeMor D.quiver a b) :
    (cast (congrArg₂ (FreeMor D.quiver) hb hc) g).comp
      (cast (congrArg₂ (FreeMor D.quiver) ha hb) f) =
    cast (congrArg₂ (FreeMor D.quiver) ha hc) (g.comp f) := by
  subst ha hb hc
  rfl

/-- The setoid on free morphisms induced by FreeMorEquiv. -/
def freeMorSetoid (a b : D.quiver.Obj) : Setoid (FreeMor D.quiver a b) where
  r := FreeMorEquiv D
  iseqv := FreeMorEquiv.isEquivalence D

/-- The quotient type of free morphisms. -/
def QuotMor (a b : D.quiver.Obj) : Type (max v u) :=
  Quotient (D.freeMorSetoid a b)

/-- Lift a free morphism to the quotient. -/
def quotMor {a b : D.quiver.Obj} (f : FreeMor D.quiver a b) :
    D.QuotMor a b :=
  Quotient.mk (D.freeMorSetoid a b) f

/-- The OverQuiver for the quotient category. -/
def quotQuiver : OverQuiver.{max v u, u} where
  Obj := D.quiver.Obj
  MorType := Σ (a b : D.quiver.Obj), D.QuotMor a b
  src := fun m => m.1
  tgt := fun m => m.2.1

/-- Bundle a quotient morphism into the sigma type. -/
def bundleQuotMor {a b : D.quiver.Obj} (f : D.QuotMor a b) :
    D.quotQuiver.MorType :=
  ⟨a, b, f⟩

/-- Composition respects the equivalence relation. -/
theorem comp_respects {a b c : D.quiver.Obj}
    {f₁ f₂ : FreeMor D.quiver a b} {g₁ g₂ : FreeMor D.quiver b c}
    (hf : FreeMorEquiv D f₁ f₂) (hg : FreeMorEquiv D g₁ g₂) :
    FreeMorEquiv D (FreeMor.comp g₁ f₁) (FreeMor.comp g₂ f₂) :=
  FreeMorEquiv.trans (FreeMorEquiv.cong_left D g₁ hf)
                     (FreeMorEquiv.cong_right D f₂ hg)

/-- Composition descends to the quotient. -/
def quotComp {a b c : D.quiver.Obj} :
    D.QuotMor b c → D.QuotMor a b → D.QuotMor a c :=
  Quotient.lift₂ (fun g f => D.quotMor (FreeMor.comp g f))
    (fun _ _ _ _ hg hf => Quotient.sound (comp_respects D hf hg))

/-- The identity quotient morphism. -/
def quotId (a : D.quiver.Obj) : D.QuotMor a a :=
  D.quotMor (FreeMor.id a)

/-- Left identity law for quotient composition. -/
theorem quotComp_id_left {a b : D.quiver.Obj} (f : D.QuotMor a b) :
    D.quotComp (D.quotId b) f = f := by
  induction f using Quotient.ind with
  | _ f => exact Quotient.sound (FreeMorEquiv.rel (FreeMorEquivGen.id_left f))

/-- Right identity law for quotient composition. -/
theorem quotComp_id_right {a b : D.quiver.Obj} (f : D.QuotMor a b) :
    D.quotComp f (D.quotId a) = f := by
  induction f using Quotient.ind with
  | _ f => exact Quotient.sound (FreeMorEquiv.rel (FreeMorEquivGen.id_right f))

/-- Associativity law for quotient composition. -/
theorem quotComp_assoc {a b c d : D.quiver.Obj}
    (h : D.QuotMor c d) (g : D.QuotMor b c) (f : D.QuotMor a b) :
    D.quotComp h (D.quotComp g f) = D.quotComp (D.quotComp h g) f := by
  induction h using Quotient.ind with
  | _ h =>
    induction g using Quotient.ind with
    | _ g =>
      induction f using Quotient.ind with
      | _ f =>
        exact Quotient.sound (FreeMorEquiv.rel (FreeMorEquivGen.assoc h g f))

/-- The identity function for quotient morphisms. -/
def quotIdFn : D.quiver.Obj → D.quotQuiver.MorType :=
  fun a => ⟨a, a, D.quotId a⟩

/-- The composition function for quotient morphisms.
    Given a composable pair (g, f) where tgt g = src f, compose as f . g
    (first g, then f), returning a morphism from src g to tgt f. -/
def quotCompFn : D.quotQuiver.ComposablePairsType → D.quotQuiver.MorType :=
  fun ⟨⟨g, f⟩, heq⟩ =>
    -- g : ⟨ag, bg, qg⟩ with qg : QuotMor ag bg
    -- f : ⟨af, bf, qf⟩ with qf : QuotMor af bf
    -- heq : Composable g f, i.e., tgt g = src f, i.e., g.2.1 = f.1
    -- Composition f . g goes: ag →g→ bg = af →f→ bf
    let g' : D.QuotMor g.1 g.2.1 := g.2.2
    let f' : D.QuotMor f.1 f.2.1 := f.2.2
    -- Cast g' to have target f.1 using heq
    -- heq : D.quotQuiver.Composable g f = (D.quotQuiver.tgt g = D.quotQuiver.src f)
    --     = (g.2.1 = f.1) by definition of quotQuiver
    let heq' : g.2.1 = f.1 := heq
    let g'' : D.QuotMor g.1 f.1 := heq' ▸ g'
    ⟨g.1, f.2.1, D.quotComp f' g''⟩

/-- The quotient category operations. -/
def quotCategoryOps : OverCategoryOps D.quotQuiver where
  idFn := D.quotIdFn
  compFn := D.quotCompFn
  id_src := fun _ => rfl
  id_tgt := fun _ => rfl
  comp_src := fun _ => rfl
  comp_tgt := fun _ => rfl

/-- Left identity law for the quotient category: id . f = f -/
theorem quot_id_comp (f : D.quotQuiver.MorType) :
    D.quotCompFn ⟨(D.quotIdFn (D.quotQuiver.src f), f),
      D.quotCategoryOps.id_tgt (D.quotQuiver.src f)⟩ = f := by
  obtain ⟨a, b, qf⟩ := f
  simp only [quotIdFn, quotCompFn, quotQuiver]
  congr 2
  exact D.quotComp_id_right qf

/-- Right identity law for the quotient category: f . id = f -/
theorem quot_comp_id (f : D.quotQuiver.MorType) :
    D.quotCompFn ⟨(f, D.quotIdFn (D.quotQuiver.tgt f)),
      (D.quotCategoryOps.id_src (D.quotQuiver.tgt f)).symm⟩ = f := by
  obtain ⟨a, b, qf⟩ := f
  simp only [quotIdFn, quotCompFn, quotQuiver]
  congr 2
  exact D.quotComp_id_left qf

/-- Associativity for the quotient category: (h . g) . f = h . (g . f) -/
theorem quot_assoc (t : D.quotQuiver.ComposableTriplesType) :
    let fg := D.quotCompFn ⟨(t.val.1, t.val.2.1), t.property.1⟩
    let gh := D.quotCompFn ⟨(t.val.2.1, t.val.2.2), t.property.2⟩
    D.quotCompFn ⟨(fg, t.val.2.2),
      (D.quotCategoryOps.comp_tgt ⟨(t.val.1, t.val.2.1), t.property.1⟩).trans
        t.property.2⟩ =
    D.quotCompFn ⟨(t.val.1, gh),
      t.property.1.trans
        (D.quotCategoryOps.comp_src ⟨(t.val.2.1, t.val.2.2), t.property.2⟩).symm⟩ := by
  obtain ⟨⟨h, g, f⟩, heq1, heq2⟩ := t
  obtain ⟨ah, bh, qh⟩ := h
  obtain ⟨ag, bg, qg⟩ := g
  obtain ⟨af, bf, qf⟩ := f
  -- heq1 : Composable h g, which is bh = ag
  -- heq2 : Composable g f, which is bg = af
  -- Substitute to identify the objects
  cases heq1
  cases heq2
  -- Now ah = ah, bh = ag = bh, bg = af = bg, bf = bf
  simp only [quotCompFn, quotQuiver]
  congr 2
  exact D.quotComp_assoc qf qg qh

/-- The quotient forms an OverCategoryData. -/
def toOverCategoryData : OverCategoryData D.quotQuiver where
  toOverCategoryOps := D.quotCategoryOps
  id_comp := D.quot_id_comp
  comp_id := D.quot_comp_id
  assoc := D.quot_assoc

/-- Casting a QuotMor equals taking the quotMor of a casted FreeMor.
    This lemma captures that the quotient construction commutes with
    type transport along index equalities. -/
theorem quotMor_cast {a b a' b' : D.quiver.Obj}
    (ha : a = a') (hb : b = b') (f : FreeMor D.quiver a b) :
    cast (congrArg₂ D.QuotMor ha hb) (D.quotMor f) =
    D.quotMor (cast (congrArg₂ (FreeMor D.quiver) ha hb) f) := by
  subst ha hb
  rfl

/-- HEq of nested sigma types for quotient morphisms.
    Given equalities on indices and an equality of the underlying QuotMor
    at the target indices, we get HEq of nested sigma elements. -/
theorem quotMorSigma_heq {a a' b b' : D.quiver.Obj}
    (ha : a = a') (hb : b = b')
    (q : D.QuotMor a b) (q' : D.QuotMor a' b')
    (hq : cast (congrArg₂ D.QuotMor ha hb) q = q') :
    HEq (⟨b, q⟩ : Σ c : D.quiver.Obj, D.QuotMor a c)
        (⟨b', q'⟩ : Σ c : D.quiver.Obj, D.QuotMor a' c) := by
  subst ha hb
  simp only [cast_eq] at hq
  subst hq
  rfl

/-- Transport on QuotMor via index equality.
    When we transport a QuotMor via an equality h : b = b', we get
    the quotMor of the transported FreeMor. -/
theorem quotMor_subst_tgt {a b b' : D.quiver.Obj} (h : b = b')
    (f : FreeMor D.quiver a b) :
    h ▸ D.quotMor f = D.quotMor (h ▸ f) := by
  subst h
  rfl


end CategoryQuotientData

/-! ## Reflection Functor L: FunctorData -> OverCategoryData

Given a copresheaf on CategoryJudgments, we construct a category by:
1. Extracting the quiver (Obj, Mor with dom/cod)
2. Forming free morphisms (binary trees of compositions)
3. Quotienting by category laws and the copresheaf relations -/

section ReflectionL

/-- Extract the quiver from a copresheaf. -/
def CategoryJudgments.FunctorData.toQuiver
    (F : CategoryJudgments.FunctorData (Type u)) :
    OverQuiver.{u, u} where
  Obj := F.objC
  MorType := F.morC
  src := F.dom
  tgt := F.cod

/-- Construct the CategoryQuotientData from a copresheaf. -/
def CategoryJudgments.FunctorData.toCategoryQuotientData
    (F : CategoryJudgments.FunctorData (Type u)) : CategoryQuotientData.{u, u} where
  quiver := F.toQuiver
  IdWitness := F.idC
  idObj := fun i => F.idMor i |> F.dom
  idMor := F.idMor
  id_src := fun _ => rfl
  id_tgt := fun i => by
    have h := congrFun F.h_id_endo i
    exact h.symm
  CompWitness := F.compC
  compRight := F.right
  compLeft := F.left
  compComposite := F.composite
  comp_match := fun c => by
    have h := congrFun F.h_comp_match c
    exact h
  comp_dom := fun c => by
    have h := congrFun F.h_comp_dom c
    exact h
  comp_cod := fun c => by
    have h := congrFun F.h_comp_cod c
    exact h

/-- Convert a copresheaf to an OverCategoryData via the quotient of free
    morphisms. -/
def CategoryJudgments.FunctorData.toOverCategoryData
    (F : CategoryJudgments.FunctorData (Type u)) :
    OverCategoryData F.toCategoryQuotientData.quotQuiver :=
  F.toCategoryQuotientData.toOverCategoryData

end ReflectionL

/-! ## Functoriality

The conversions Phi and L extend to functors between the appropriate categories.
-/

section Functoriality

variable {Q₁ Q₂ : OverQuiver.{u, u}}
variable {C₁ : OverCategoryData Q₁} {C₂ : OverCategoryData Q₂}

/-- A functor between categories induces a natural transformation between the
    corresponding copresheaves. This is the functorial action of Phi on
    morphisms. -/
def OverFunctorData.toJudgmentNatTrans (F : OverFunctorData C₁ C₂) :
    CategoryJudgments.NatTransData
      C₁.toJudgmentFunctorData
      C₂.toJudgmentFunctorData where
  appObj := F.objFn
  appMor := F.morFn
  appId := F.objFn
  appComp := fun p =>
    let composableProof : Q₂.tgt (F.morFn p.val.1) = Q₂.src (F.morFn p.val.2) :=
      (F.tgt_comm p.val.1).trans
        ((congrArg F.objFn p.property).trans (F.src_comm p.val.2).symm)
    ⟨(F.morFn p.val.1, F.morFn p.val.2), composableProof⟩
  naturality_dom := by funext f; exact (F.src_comm f).symm
  naturality_cod := by funext f; exact (F.tgt_comm f).symm
  naturality_idMor := by funext a; exact F.map_id a
  naturality_left := by funext _; rfl
  naturality_right := by funext _; rfl
  naturality_composite := by funext p; exact F.map_comp p

end Functoriality

/-! ## Free morphism mapping

When we have a quiver morphism, we can lift it to map free morphisms. -/

section FreeMorMapping

variable {Q₁ Q₂ : OverQuiver.{v, u}}

/-- Map a free morphism through a quiver morphism (extended version).
    This is the functor from FreeMor Q₁ to FreeMor Q₂ induced by a
    quiver morphism. -/
def FreeMor.mapQuiver (F : OverQuiverMorphism Q₁ Q₂)
    {a b : Q₁.Obj} (m : FreeMor Q₁ a b) :
    FreeMor Q₂ (F.objFn a) (F.objFn b) :=
  match m with
  | .var f => F.src_comm f ▸ F.tgt_comm f ▸ .var (F.morFn f)
  | .id _ => .id _
  | .comp g f => .comp (mapQuiver F g) (mapQuiver F f)

end FreeMorMapping

/-! ## Morphisms between CategoryQuotientData

For L to be functorial, we need to show that morphisms between copresheaves
(NatTransData) induce well-defined functors between quotient categories.
A NatTransData preserves the witness structure needed for the equivalence
relation. -/

section QuotientMorphisms

variable {D₁ D₂ : CategoryQuotientData.{v, u}}

/-- A morphism between CategoryQuotientData structures that is compatible with
    the id and comp witnesses. This is the structure induced by a NatTransData
    between the corresponding copresheaves. -/
structure CategoryQuotientMorphism (D₁ D₂ : CategoryQuotientData.{v, u}) where
  /-- The underlying quiver morphism. -/
  quiverMor : OverQuiverMorphism D₁.quiver D₂.quiver
  /-- Map on identity witnesses. -/
  idWitMap : D₁.IdWitness → D₂.IdWitness
  /-- Map on composition witnesses. -/
  compWitMap : D₁.CompWitness → D₂.CompWitness
  /-- Identity objects are preserved. -/
  idObj_comm : ∀ i, quiverMor.objFn (D₁.idObj i) = D₂.idObj (idWitMap i)
  /-- Identity morphisms are preserved. -/
  idMor_comm : ∀ i, quiverMor.morFn (D₁.idMor i) = D₂.idMor (idWitMap i)
  /-- Right components of composition are preserved. -/
  compRight_comm : ∀ c, quiverMor.morFn (D₁.compRight c) = D₂.compRight (compWitMap c)
  /-- Left components of composition are preserved. -/
  compLeft_comm : ∀ c, quiverMor.morFn (D₁.compLeft c) = D₂.compLeft (compWitMap c)
  /-- Composite morphisms are preserved. -/
  compComposite_comm :
    ∀ c, quiverMor.morFn (D₁.compComposite c) = D₂.compComposite (compWitMap c)

/-- Identity CategoryQuotientMorphism. -/
def CategoryQuotientMorphism.id (D : CategoryQuotientData) :
    CategoryQuotientMorphism D D where
  quiverMor := OverQuiverMorphism.id D.quiver
  idWitMap := _root_.id
  compWitMap := _root_.id
  idObj_comm := fun _ => rfl
  idMor_comm := fun _ => rfl
  compRight_comm := fun _ => rfl
  compLeft_comm := fun _ => rfl
  compComposite_comm := fun _ => rfl

variable (F : CategoryQuotientMorphism D₁ D₂)

/-- Helper: mapQuiver of a var is a transported var.
    mapQuiver F (var m) = h₁ ▸ h₂ ▸ var (F.morFn m)
    where h₁, h₂ are the source/target preservation proofs. -/
theorem FreeMor.mapQuiver_var (m : D₁.quiver.MorType) :
    FreeMor.mapQuiver F.quiverMor (.var m) =
      F.quiverMor.src_comm m ▸ F.quiverMor.tgt_comm m ▸ .var (F.quiverMor.morFn m) := rfl

/-- mapQuiver commutes with cast on the FreeMor type. -/
theorem FreeMor.mapQuiver_cast {a a' b b' : D₁.quiver.Obj}
    (ha : a = a') (hb : b = b')
    (m : FreeMor D₁.quiver a b) :
    FreeMor.mapQuiver F.quiverMor
      (cast (congrArg₂ (FreeMor D₁.quiver) ha hb) m) =
    cast (congrArg₂ (FreeMor D₂.quiver)
      (congrArg F.quiverMor.objFn ha)
      (congrArg F.quiverMor.objFn hb))
      (FreeMor.mapQuiver F.quiverMor m) := by
  subst ha hb
  simp only [congrArg₂, cast_eq]

/-- Two substs (▸) equal one cast for two-argument types. -/
theorem subst_subst_eq_cast {A : Type*} {F : A → A → Type*}
    {a a' b b' : A} (ha : a = a') (hb : b = b') (x : F a b) :
    ha ▸ hb ▸ x = cast (congrArg₂ F ha hb) x := by
  subst ha hb
  rfl

/-- Cast of a substed var equals cast of the var when the final types are the same. -/
theorem cast_subst_var {Q : OverQuiver.{v, u}} {m₁ m₂ : Q.MorType}
    {a b : Q.Obj} (hm : m₁ = m₂)
    (h₁ : Q.src m₁ = a) (h₁' : Q.tgt m₁ = b)
    (h₂ : Q.src m₂ = a) (h₂' : Q.tgt m₂ = b) :
    cast (congrArg₂ (FreeMor Q) h₁ h₁')
      (hm.symm.rec (motive := fun m _ => FreeMor Q (Q.src m) (Q.tgt m))
        (FreeMor.var m₂)) =
    cast (congrArg₂ (FreeMor Q) h₂ h₂') (FreeMor.var m₂) := by
  subst hm
  rfl

/-- If two morphisms are equal, their vars under cast are equal. -/
theorem FreeMor.cast_var_eq {Q : OverQuiver.{v, u}} {a b : Q.Obj}
    {m₁ m₂ : Q.MorType} (hm : m₁ = m₂)
    (h₁ : Q.src m₁ = a) (h₁' : Q.tgt m₁ = b)
    (h₂ : Q.src m₂ = a) (h₂' : Q.tgt m₂ = b) :
    cast (congrArg₂ (FreeMor Q) h₁ h₁') (.var m₁) =
    cast (congrArg₂ (FreeMor Q) h₂ h₂') (.var m₂) := by
  subst hm
  rfl

/-- FreeMor.id x equals FreeMor.id y when x = y. -/
theorem FreeMor.id_eq {Q : OverQuiver.{v, u}} {x y : Q.Obj} (h : x = y) :
    (FreeMor.id x : FreeMor Q x x) =
    cast (congrArg₂ (FreeMor Q) h.symm h.symm) (FreeMor.id y) := by
  subst h
  rfl

/-- Equality of compositions when components are equal under appropriate casts.
    This handles the case where we need to show
    (cast _ g).comp (cast _ f) = cast _ (g'.comp f')
    when g and f are equal to g' and f' under casts. -/
theorem FreeMor.comp_cast_eq {Q : OverQuiver.{v, u}}
    {a a' b b' c c' : Q.Obj}
    {g : FreeMor Q b c} {f : FreeMor Q a b}
    {g' : FreeMor Q b' c'} {f' : FreeMor Q a' b'}
    (ha : a' = a) (hb : b' = b) (hc : c' = c)
    (hg : cast (congrArg₂ (FreeMor Q) hb hc) g' = g)
    (hf : cast (congrArg₂ (FreeMor Q) ha hb) f' = f) :
    g.comp f = cast (congrArg₂ (FreeMor Q) ha hc) (g'.comp f') := by
  subst ha hb hc
  simp only [congrArg₂, cast_eq] at hg hf ⊢
  subst hg hf
  rfl

/-- Composition of casted morphisms can be expressed as a cast of composition
    when all the indices properly align. -/
theorem FreeMor.comp_cast_outer {Q : OverQuiver.{v, u}}
    {a a' b₁ b₂ c c' : Q.Obj}
    (ha : a = a') (hb_g : b₁ = b₂) (hc : c = c')
    (g : FreeMor Q b₁ c) (f : FreeMor Q a b₁) :
    (cast (congrArg₂ (FreeMor Q) hb_g hc) g).comp (cast (congrArg₂ (FreeMor Q) ha hb_g) f) =
    cast (congrArg₂ (FreeMor Q) ha hc) (g.comp f) := by
  subst ha hb_g hc
  simp only [congrArg₂, cast_eq]

/-- When composing casted morphisms, if the two casts share a middle index
    (via a composability proof), the composition equals a cast of a composition
    where one morphism is cast and one uses its natural index.
    This handles: (cast _ g).comp (cast _ f) = cast _ ((cast _ g).comp f)
    when tgt f = src g. -/
theorem FreeMor.comp_cast_eq_cast_comp_partial {Q : OverQuiver.{v, u}}
    {af bf bg a' b' : Q.Obj}
    (ha : af = a') (hb : bg = b')
    (g : FreeMor Q bf bg) (f : FreeMor Q af bf) :
    (cast (congrArg₂ (FreeMor Q) rfl hb) g).comp (cast (congrArg₂ (FreeMor Q) ha rfl) f) =
    cast (congrArg₂ (FreeMor Q) ha hb) (g.comp f) := by
  subst ha hb
  simp only [congrArg₂, cast_eq]

/-- HEq congruence for FreeMor.comp:
    if the index equalities hold and g₁ ≅ g₂, f₁ ≅ f₂,
    then g₁.comp f₁ ≅ g₂.comp f₂. -/
theorem FreeMor.heq_comp {Q : OverQuiver.{v, u}}
    {a₁ b₁ c₁ a₂ b₂ c₂ : Q.Obj}
    (ha : a₁ = a₂) (hb : b₁ = b₂) (hc : c₁ = c₂)
    {g₁ : FreeMor Q b₁ c₁} {g₂ : FreeMor Q b₂ c₂}
    {f₁ : FreeMor Q a₁ b₁} {f₂ : FreeMor Q a₂ b₂}
    (hg : HEq g₁ g₂) (hf : HEq f₁ f₂) :
    HEq (g₁.comp f₁) (g₂.comp f₂) := by
  subst ha hb hc
  rw [eq_of_heq hg, eq_of_heq hf]

/-- mapQuiver of a casted var. When we map a casted variable through F,
    the result is a cast of var applied to the mapped morphism. -/
theorem FreeMor.mapQuiver_cast_var
    (m : D₁.quiver.MorType)
    {a' b' : D₁.quiver.Obj} (ha : D₁.quiver.src m = a') (hb : D₁.quiver.tgt m = b') :
    FreeMor.mapQuiver F.quiverMor
      (cast (congrArg₂ (FreeMor D₁.quiver) ha hb) (.var m)) =
    cast (congrArg₂ (FreeMor D₂.quiver)
      ((F.quiverMor.src_comm m).trans (congrArg F.quiverMor.objFn ha))
      ((F.quiverMor.tgt_comm m).trans (congrArg F.quiverMor.objFn hb)))
      (.var (F.quiverMor.morFn m)) := by
  subst ha hb
  simp only [congrArg₂, cast_eq]
  -- After subst: congrArg _ rfl = rfl, so both trans _ rfl simplify
  -- LHS: mapQuiver F.quiverMor (.var m) = src_comm ▸ tgt_comm ▸ .var (...)
  -- RHS: cast (congrArg₂ ... src_comm.trans rfl tgt_comm.trans rfl) (.var (...))
  --    = cast (congrArg₂ ... src_comm tgt_comm) (.var (...)) by trans_refl
  -- By subst_subst_eq_cast, src_comm ▸ tgt_comm ▸ x = cast (congrArg₂ ...) x
  rw [mapQuiver_var, subst_subst_eq_cast]

/-- mapQuiver preserves identity morphisms in FreeMor. -/
theorem FreeMor.mapQuiver_id (F : CategoryQuotientMorphism D₁ D₂)
    (a : D₁.quiver.Obj) :
    FreeMor.mapQuiver F.quiverMor (.id a) = .id (F.quiverMor.objFn a) := rfl

/-- mapQuiver preserves composition in FreeMor. -/
theorem FreeMor.mapQuiver_comp (F : CategoryQuotientMorphism D₁ D₂)
    {a b c : D₁.quiver.Obj}
    (g : FreeMor D₁.quiver b c) (f : FreeMor D₁.quiver a b) :
    FreeMor.mapQuiver F.quiverMor (.comp g f) =
      .comp (FreeMor.mapQuiver F.quiverMor g) (FreeMor.mapQuiver F.quiverMor f) := rfl

/-- mapQuiver respects the generating equivalence relation.
    If f ~gen g in D₁, then mapQuiver F f ~gen mapQuiver F g in D₂. -/
theorem FreeMor.mapQuiver_respects_gen
    {a b : D₁.quiver.Obj}
    {f g : FreeMor D₁.quiver a b}
    (h : D₁.FreeMorEquivGen f g) :
    D₂.FreeMorEquiv
      (FreeMor.mapQuiver F.quiverMor f)
      (FreeMor.mapQuiver F.quiverMor g) := by
  induction h with
  | id_left fm =>
    simp only [mapQuiver]
    exact .rel (.id_left _)
  | id_right fm =>
    simp only [mapQuiver]
    exact .rel (.id_right _)
  | assoc h' g' f' =>
    simp only [mapQuiver]
    exact .rel (.assoc _ _ _)
  | id_witness i =>
    -- Goal: mapQuiver (cast _ (var (D₁.idMor i))) ~ id (F.objFn (D₁.idObj i))
    simp only [mapQuiver]
    -- The D₂ witness gives: cast _ (var idMor') ~ id (idObj')
    have h_wit := CategoryQuotientData.FreeMorEquivGen.id_witness (D := D₂) (F.idWitMap i)
    -- We'll build the proof by showing our LHS equals a cast of the D₂ witness LHS,
    -- and our RHS equals a cast of the D₂ witness RHS.
    -- Then use FreeMorEquiv.cast to transport the equivalence.
    -- Equalities:
    -- F.idMor_comm i : F.quiverMor.morFn (D₁.idMor i) = D₂.idMor (F.idWitMap i)
    -- F.idObj_comm i : F.quiverMor.objFn (D₁.idObj i) = D₂.idObj (F.idWitMap i)
    -- Use the preservation properties to build the cast proofs:
    -- Our LHS has cast proof based on (src_comm m).trans (congrArg _ (id_src i))
    -- D₂ witness has cast proof based on D₂.id_src and D₂.id_tgt
    -- We transport through F.idObj_comm i
    have h_wit' := CategoryQuotientData.FreeMorEquiv.cast (D := D₂)
      (F.idObj_comm i).symm (F.idObj_comm i).symm (.rel h_wit)
    -- h_wit' : FreeMorEquiv
    --   (cast (F.idObj_comm i).symm ... (cast ... (var (D₂.idMor ...))))
    --   (cast (F.idObj_comm i).symm ... (id (D₂.idObj ...)))
    -- Now we need to show our actual goal terms match h_wit''s terms
    -- LHS term: mapQuiver_cast_var gives us cast _ (var (F.morFn (D₁.idMor i)))
    --         = cast _ (var (D₂.idMor (F.idWitMap i))) by F.idMor_comm
    -- RHS term: id (F.objFn (D₁.idObj i))
    --         = id (D₂.idObj ...) by F.idObj_comm, which cast _ simplifies to
    convert h_wit' using 1
    · -- LHS: mapQuiver (cast _ (var idMor_D₁)) = cast _ (cast _ (var idMor_D₂))
      rw [mapQuiver_cast_var F (D₁.idMor i) (D₁.id_src i) (D₁.id_tgt i)]
      -- Goal: cast _ (var (F.morFn idMor)) = cast _ (cast _ (var idMor'))
      simp only [cast_cast]
      -- Goal: cast _ (var (F.morFn idMor)) = cast _ (var idMor')
      -- Build the cast proofs needed for cast_var_eq:
      -- For m₁ = F.morFn (D₁.idMor i):
      --   h₁: D₂.src (F.morFn ...) = F.objFn (D₁.idObj i)
      --     = (src_comm (D₁.idMor i)).trans (congrArg objFn (D₁.id_src i))
      --   h₁': D₂.tgt (F.morFn ...) = F.objFn (D₁.idObj i)
      --     = (tgt_comm (D₁.idMor i)).trans (congrArg objFn (D₁.id_tgt i))
      -- For m₂ = D₂.idMor (F.idWitMap i):
      --   h₂: D₂.src (D₂.idMor ...) = F.objFn (D₁.idObj i)
      --     = (D₂.id_src (F.idWitMap i)).trans (F.idObj_comm i).symm
      --   h₂': D₂.tgt (D₂.idMor ...) = F.objFn (D₁.idObj i)
      --     = (D₂.id_tgt (F.idWitMap i)).trans (F.idObj_comm i).symm
      exact cast_var_eq (F.idMor_comm i)
        ((F.quiverMor.src_comm (D₁.idMor i)).trans (congrArg F.quiverMor.objFn (D₁.id_src i)))
        ((F.quiverMor.tgt_comm (D₁.idMor i)).trans (congrArg F.quiverMor.objFn (D₁.id_tgt i)))
        ((D₂.id_src (F.idWitMap i)).trans (F.idObj_comm i).symm)
        ((D₂.id_tgt (F.idWitMap i)).trans (F.idObj_comm i).symm)
    · -- RHS: id (F.objFn (D₁.idObj i)) = cast _ (id (D₂.idObj ...))
      -- F.idObj_comm i : F.objFn (D₁.idObj i) = D₂.idObj (F.idWitMap i)
      -- Use id_eq to show the ids are equal under cast
      exact id_eq (F.idObj_comm i)
  | comp_witness c =>
    have h_wit := CategoryQuotientData.FreeMorEquivGen.comp_witness (D := D₂) (F.compWitMap c)
    -- h_wit has type at D₂.quiver.src/tgt of D₂ witness morphisms
    -- Our goal is at F.quiverMor.objFn applied to D₁ witness objects
    simp only [mapQuiver]
    -- Goal: (mapQuiver (cast _ (var L))).comp (mapQuiver (var R)) ~ mapQuiver (cast _ (var C))
    -- The goal type is at (F.objFn (D₁.src compRight), F.objFn (D₁.tgt compLeft))
    -- The h_wit type is at (D₂.src compRight', D₂.tgt compLeft')
    -- where compRight' = D₂.compRight (F.compWitMap c), etc.
    -- We use the preservation commutation:
    -- F.objFn (D₁.src compRight) = D₂.src (F.morFn compRight) = D₂.src compRight' by compRight_comm
    -- Cast proofs from (F.objFn D₁.xxx) to (D₂.xxx')
    -- Build cast proofs: FreeMorEquiv.cast needs ha : a = a', hb : b = b'
    -- where the original equiv is at (a, b) and we cast to (a', b')
    -- h_wit is at (D₂.src compRight', D₂.tgt compLeft')
    -- Our goal is at (F.objFn (D₁.src compRight), F.objFn (D₁.tgt compLeft))
    -- So we need ha : D₂.src compRight' = F.objFn (D₁.src compRight)
    have ha : D₂.quiver.src (D₂.compRight (F.compWitMap c)) =
        F.quiverMor.objFn (D₁.quiver.src (D₁.compRight c)) :=
      (congrArg D₂.quiver.src (F.compRight_comm c)).symm.trans
        (F.quiverMor.src_comm (D₁.compRight c))
    have hb : D₂.quiver.tgt (D₂.compLeft (F.compWitMap c)) =
        F.quiverMor.objFn (D₁.quiver.tgt (D₁.compLeft c)) :=
      (congrArg D₂.quiver.tgt (F.compLeft_comm c)).symm.trans
        (F.quiverMor.tgt_comm (D₁.compLeft c))
    have h_wit' := CategoryQuotientData.FreeMorEquiv.cast (D := D₂) ha hb (.rel h_wit)
    convert h_wit' using 1
    · -- LHS: composition equality
      -- Expand the mapQuiver terms
      rw [mapQuiver_cast_var F (D₁.compLeft c) (D₁.comp_match c).symm rfl]
      simp only [subst_subst_eq_cast]
      -- Goal: (cast A (var g₁)).comp (cast B (var f₁)) = cast C ((cast D (var g₂)).comp (var f₂))
      -- where g₁ = g₂ and f₁ = f₂ by _comm lemmas
      -- Try native_decide or decide for this goal
      have h := F.compLeft_comm c
      have h' := F.compRight_comm c
      have var_eq_L : FreeMor.var (F.quiverMor.morFn (D₁.compLeft c)) =
          h ▸ FreeMor.var (D₂.compLeft (F.compWitMap c)) :=
        h.symm.rec rfl
      have var_eq_R : FreeMor.var (F.quiverMor.morFn (D₁.compRight c)) =
          h' ▸ FreeMor.var (D₂.compRight (F.compWitMap c)) :=
        h'.symm.rec rfl
      simp only [var_eq_L, var_eq_R]
      rw [cast_subst_var h _ _ _ _, cast_subst_var h' _ _ _ _]
      on_goal 1 =>
        apply eq_of_heq
        refine (FreeMor.heq_comp ?ha ?hb ?hc
          ((cast_heq _ _).trans (cast_heq _ _).symm)
          (cast_heq _ _)).trans (cast_heq _ _).symm
      all_goals first
          | exact F.quiverMor.src_comm _
          | exact F.quiverMor.tgt_comm _
          | exact ha
          | exact hb
          | exact ha.symm
          | exact hb.symm
          | exact (F.quiverMor.tgt_comm _).symm.trans
              (congrArg D₂.quiver.tgt (F.compRight_comm c))
          | exact (D₂.comp_match _).symm
          | exact (D₂.comp_match _).trans
              ((congrArg D₂.quiver.tgt
                (F.compRight_comm c).symm).trans
                (F.quiverMor.tgt_comm _))
          | exact ((congrArg D₂.quiver.src
                (F.compLeft_comm c).symm).trans
                (F.quiverMor.src_comm _)).trans
              (congrArg _ (D₁.comp_match c).symm)
          | exact (congrArg D₂.quiver.tgt
              (F.compRight_comm c).symm).trans
              (F.quiverMor.tgt_comm _)
          | exact (F.quiverMor.src_comm _).trans
              (congrArg _ (D₁.comp_match c).symm)
    · -- RHS: composite equality
      rw [mapQuiver_cast_var F (D₁.compComposite c) (D₁.comp_dom c) (D₁.comp_cod c)]
      simp only [cast_cast]
      -- Need source/target preservation proofs for mapQuiver of composite
      have hsrc : D₂.quiver.src (F.quiverMor.morFn (D₁.compComposite c)) =
          F.quiverMor.objFn (D₁.quiver.src (D₁.compRight c)) :=
        (F.quiverMor.src_comm _).trans (congrArg _ (D₁.comp_dom c))
      have htgt : D₂.quiver.tgt (F.quiverMor.morFn (D₁.compComposite c)) =
          F.quiverMor.objFn (D₁.quiver.tgt (D₁.compLeft c)) :=
        (F.quiverMor.tgt_comm _).trans (congrArg _ (D₁.comp_cod c))
      -- Proofs for the D₂ version (via compComposite_comm)
      have hsrc' : D₂.quiver.src (D₂.compComposite (F.compWitMap c)) =
          F.quiverMor.objFn (D₁.quiver.src (D₁.compRight c)) :=
        (congrArg D₂.quiver.src (F.compComposite_comm c).symm).trans hsrc
      have htgt' : D₂.quiver.tgt (D₂.compComposite (F.compWitMap c)) =
          F.quiverMor.objFn (D₁.quiver.tgt (D₁.compLeft c)) :=
        (congrArg D₂.quiver.tgt (F.compComposite_comm c).symm).trans htgt
      exact cast_var_eq (F.compComposite_comm c) hsrc htgt hsrc' htgt'
  | cong_left h' _ ih =>
    simp only [mapQuiver]
    exact CategoryQuotientData.FreeMorEquiv.cong_left D₂
      (mapQuiver F.quiverMor h') ih
  | cong_right k _ ih =>
    simp only [mapQuiver]
    exact CategoryQuotientData.FreeMorEquiv.cong_right D₂
      (mapQuiver F.quiverMor k) ih

/-- mapQuiver respects the full equivalence relation.
    If f ~ g in D₁, then mapQuiver F f ~ mapQuiver F g in D₂. -/
theorem FreeMor.mapQuiver_respects_equiv
    {a b : D₁.quiver.Obj}
    {f g : FreeMor D₁.quiver a b}
    (h : D₁.FreeMorEquiv f g) :
    D₂.FreeMorEquiv
      (FreeMor.mapQuiver F.quiverMor f)
      (FreeMor.mapQuiver F.quiverMor g) := by
  induction h with
  | rel hr => exact mapQuiver_respects_gen F hr
  | refl _ => exact .refl _
  | symm _ ih => exact .symm ih
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2

/-- mapQuiver descends to the quotient. -/
def CategoryQuotientMorphism.quotMapMor
    {a b : D₁.quiver.Obj} (m : D₁.QuotMor a b) :
    D₂.QuotMor (F.quiverMor.objFn a) (F.quiverMor.objFn b) :=
  Quotient.lift
    (fun fm => D₂.quotMor (FreeMor.mapQuiver F.quiverMor fm))
    (fun _ _ h => Quotient.sound (FreeMor.mapQuiver_respects_equiv F h))
    m

/-- quotMapMor preserves identity. -/
theorem CategoryQuotientMorphism.quotMapMor_id (a : D₁.quiver.Obj) :
    F.quotMapMor (D₁.quotId a) = D₂.quotId (F.quiverMor.objFn a) := rfl

/-- quotMapMor preserves composition. -/
theorem CategoryQuotientMorphism.quotMapMor_comp
    {a b c : D₁.quiver.Obj}
    (g : D₁.QuotMor b c) (f : D₁.QuotMor a b) :
    F.quotMapMor (D₁.quotComp g f) = D₂.quotComp (F.quotMapMor g) (F.quotMapMor f) := by
  induction g using Quotient.ind with
  | _ g' =>
    induction f using Quotient.ind with
    | _ f' => rfl

end QuotientMorphisms

/-! ## L Functor on Morphisms

Given a natural transformation α : F → G between copresheaves, we construct
a functor L(α) : L(F) → L(G) between the corresponding quotient categories. -/

section LFunctorMorphisms

variable {F G : CategoryJudgments.FunctorData (Type u)}

/-- Build a CategoryQuotientMorphism from a NatTransData. -/
def CategoryJudgments.NatTransData.toCategoryQuotientMorphism
    (α : CategoryJudgments.NatTransData F G) :
    CategoryQuotientMorphism F.toCategoryQuotientData G.toCategoryQuotientData where
  quiverMor := {
    objFn := α.appObj
    morFn := α.appMor
    src_comm := fun f => by
      have h := congrFun α.naturality_dom f
      exact h.symm
    tgt_comm := fun f => by
      have h := congrFun α.naturality_cod f
      exact h.symm
  }
  idWitMap := α.appId
  compWitMap := α.appComp
  idObj_comm := fun i => by
    simp only [CategoryJudgments.FunctorData.toCategoryQuotientData]
    have h : α.appMor (F.idMor i) = G.idMor (α.appId i) :=
      congrFun α.naturality_idMor i
    have hdom : α.appObj (F.dom (F.idMor i)) = G.dom (α.appMor (F.idMor i)) :=
      congrFun α.naturality_dom (F.idMor i)
    calc α.appObj (F.dom (F.idMor i)) = G.dom (α.appMor (F.idMor i)) := hdom
      _ = G.dom (G.idMor (α.appId i)) := congrArg G.dom h
  idMor_comm := fun i => congrFun α.naturality_idMor i
  compRight_comm := fun c => congrFun α.naturality_right c
  compLeft_comm := fun c => congrFun α.naturality_left c
  compComposite_comm := fun c => congrFun α.naturality_composite c

/-- The quiver morphism on quotient quivers induced by a NatTransData. -/
def CategoryJudgments.NatTransData.toQuotQuiverMor
    (α : CategoryJudgments.NatTransData F G) :
    OverQuiverMorphism
      F.toCategoryQuotientData.quotQuiver
      G.toCategoryQuotientData.quotQuiver where
  objFn := α.appObj
  morFn := fun m =>
    G.toCategoryQuotientData.bundleQuotMor
      (α.toCategoryQuotientMorphism.quotMapMor m.2.2)
  src_comm := fun m => by
    simp only [CategoryQuotientData.quotQuiver, CategoryQuotientData.bundleQuotMor]
    rfl
  tgt_comm := fun m => by
    simp only [CategoryQuotientData.quotQuiver, CategoryQuotientData.bundleQuotMor]
    rfl

/-- The L functor acts on morphisms: NatTransData to OverFunctorData. -/
def CategoryJudgments.NatTransData.toOverFunctorData
    (α : CategoryJudgments.NatTransData F G) :
    OverFunctorData F.toOverCategoryData G.toOverCategoryData where
  toOverQuiverMorphism := α.toQuotQuiverMor
  map_id := fun a => by
    simp only [toQuotQuiverMor, CategoryJudgments.FunctorData.toOverCategoryData,
      CategoryQuotientData.toOverCategoryData, CategoryQuotientData.bundleQuotMor]
    rfl
  map_comp := fun p => by
    -- We proceed by cases on p, using the composability proof directly.
    rcases p with ⟨⟨⟨g_src, g_tgt, g_qm⟩, ⟨f_src, f_tgt, f_qm⟩⟩, hcomp⟩
    -- hcomp : Composable g f, which is definitionally g_tgt = f_src
    -- Convert hcomp to an explicit equality for pattern matching.
    have heq : g_tgt = f_src := hcomp
    -- We unfold definitions and simplify.
    simp only [toQuotQuiverMor, CategoryJudgments.FunctorData.toOverCategoryData,
      CategoryQuotientData.toOverCategoryData, CategoryQuotientData.quotCategoryOps,
      CategoryQuotientData.quotCompFn, CategoryQuotientData.bundleQuotMor,
      CategoryQuotientData.quotQuiver]
    -- Both sides are now sigma types ⟨src, ⟨tgt, qm⟩⟩
    -- The src and tgt components agree definitionally.
    -- For the qm component, we need quotMapMor_comp plus transport handling.
    -- Use cases on the equality to reduce to the rfl case.
    cases heq
    -- After cases, f_src = g_tgt, so transports become trivial.
    simp only [CategoryQuotientMorphism.quotMapMor_comp]
    -- Now we need: quotMapMor (hcomp ▸ g_qm) = quotMapMor g_qm
    -- Since hcomp is now definitionally rfl, the transport is trivial.
    rfl

set_option backward.isDefEq.respectTransparency false in
/-- FreeMor.mapQuiver with identity OverQuiverMorphism is identity. -/
theorem FreeMor.mapQuiver_overQuiverId {Q : OverQuiver} {a b : Q.Obj}
    (fm : FreeMor Q a b) :
    FreeMor.mapQuiver (OverQuiverMorphism.id Q) fm = fm := by
  induction fm with
  | var f => rfl
  | id x => rfl
  | comp g f ihg ihf =>
    simp only [FreeMor.mapQuiver] at ihg ihf ⊢
    rw [ihg, ihf]

/-- quotMapMor with identity CategoryQuotientMorphism is identity. -/
theorem CategoryQuotientMorphism.quotMapMor_id_self
    {D : CategoryQuotientData} {a b : D.quiver.Obj}
    (qm : D.QuotMor a b) :
    CategoryQuotientMorphism.quotMapMor
      (CategoryQuotientMorphism.id D) qm = qm := by
  induction qm using Quotient.ind with
  | _ fm =>
    simp only [CategoryQuotientMorphism.quotMapMor, CategoryQuotientMorphism.id,
      CategoryQuotientData.quotMor]
    exact congrArg Quotient.mk'' (FreeMor.mapQuiver_overQuiverId fm)

/-- L preserves identity: L(id_F) = id_{L(F)}. -/
theorem toOverFunctorData_id :
    (CategoryJudgments.NatTransData.id F).toOverFunctorData =
    OverFunctorData.id F.toOverCategoryData := by
  -- First, show that the objFn components are equal.
  -- NatTransData.id uses 𝟙 which for Type is definitionally id.
  have h_obj : (CategoryJudgments.NatTransData.id F).toOverFunctorData.objFn =
               (OverFunctorData.id F.toOverCategoryData).objFn := rfl
  -- Next, show morFn components are equal.
  have h_mor : (CategoryJudgments.NatTransData.id F).toOverFunctorData.morFn =
               (OverFunctorData.id F.toOverCategoryData).morFn := by
    funext m
    simp only [CategoryJudgments.NatTransData.toOverFunctorData,
      CategoryJudgments.NatTransData.toQuotQuiverMor,
      CategoryJudgments.NatTransData.id, OverFunctorData.id,
      OverQuiverMorphism.id,
      CategoryJudgments.NatTransData.toCategoryQuotientMorphism,
      CategoryQuotientData.bundleQuotMor]
    congr 1
    congr 1
    exact CategoryQuotientMorphism.quotMapMor_id_self m.2.2
  -- Use ext to reduce to component equality.
  ext x
  · exact congrFun h_obj x
  · exact congrFun h_mor x

/-- mapQuiver on OverQuiverMorphism commutes with cast. -/
theorem FreeMor.mapQuiver_cast_overQuiv {Q₁ Q₂ : OverQuiver}
    (F : OverQuiverMorphism Q₁ Q₂)
    {a a' b b' : Q₁.Obj} (ha : a = a') (hb : b = b')
    (m : FreeMor Q₁ a b) :
    FreeMor.mapQuiver F (cast (congrArg₂ (FreeMor Q₁) ha hb) m) =
    cast (congrArg₂ (FreeMor Q₂) (congrArg F.objFn ha) (congrArg F.objFn hb))
      (FreeMor.mapQuiver F m) := by
  subst ha hb
  simp only [congrArg₂, cast_eq]

set_option backward.isDefEq.respectTransparency false in
/-- FreeMor.mapQuiver respects composition of OverQuiverMorphisms. -/
theorem FreeMor.mapQuiver_quiverComp {Q₁ Q₂ Q₃ : OverQuiver}
    (F : OverQuiverMorphism Q₁ Q₂) (G : OverQuiverMorphism Q₂ Q₃)
    {a b : Q₁.Obj} (fm : FreeMor Q₁ a b) :
    FreeMor.mapQuiver (F.comp G) fm =
      FreeMor.mapQuiver G (FreeMor.mapQuiver F fm) := by
  induction fm with
  | var f =>
    -- Both sides are transported .var (G.morFn (F.morFn f)) values.
    -- Convert all transports to casts and use cast_eq (proof irrelevance).
    simp only [FreeMor.mapQuiver, OverQuiverMorphism.comp,
      subst_subst_eq_cast, Function.comp_apply]
    -- LHS: cast _ (var (G.morFn (F.morFn f)))
    -- RHS: mapQuiver G (cast _ (var (F.morFn f)))
    -- Apply mapQuiver_cast_overQuiv with explicit src/tgt proofs.
    rw [FreeMor.mapQuiver_cast_overQuiv G (F.src_comm f) (F.tgt_comm f)]
    simp only [FreeMor.mapQuiver, subst_subst_eq_cast]
    simp only [cast_cast]
  | id x => rfl
  | comp g f ihg ihf =>
    simp only [FreeMor.mapQuiver] at ihg ihf ⊢
    rw [ihg, ihf]

/-- quotMapMor respects composition of CategoryQuotientMorphisms (via quiverMor comp). -/
theorem CategoryQuotientMorphism.quotMapMor_quiverComp
    {D₁ D₂ D₃ : CategoryQuotientData}
    (F : CategoryQuotientMorphism D₁ D₂) (G : CategoryQuotientMorphism D₂ D₃)
    {a b : D₁.quiver.Obj} (qm : D₁.QuotMor a b) :
    CategoryQuotientMorphism.quotMapMor
      ⟨F.quiverMor.comp G.quiverMor, G.idWitMap ∘ F.idWitMap,
        G.compWitMap ∘ F.compWitMap, fun i => by
          simp only [OverQuiverMorphism.comp, Function.comp_apply]
          rw [F.idObj_comm, G.idObj_comm],
        fun i => by
          simp only [OverQuiverMorphism.comp, Function.comp_apply]
          rw [F.idMor_comm, G.idMor_comm],
        fun c => by
          simp only [OverQuiverMorphism.comp, Function.comp_apply]
          rw [F.compRight_comm, G.compRight_comm],
        fun c => by
          simp only [OverQuiverMorphism.comp, Function.comp_apply]
          rw [F.compLeft_comm, G.compLeft_comm],
        fun c => by
          simp only [OverQuiverMorphism.comp, Function.comp_apply]
          rw [F.compComposite_comm, G.compComposite_comm]⟩ qm =
    G.quotMapMor (F.quotMapMor qm) := by
  induction qm using Quotient.ind with
  | _ fm =>
    simp only [CategoryQuotientMorphism.quotMapMor, CategoryQuotientData.quotMor]
    exact congrArg Quotient.mk'' (FreeMor.mapQuiver_quiverComp F.quiverMor G.quiverMor fm)

variable {H : CategoryJudgments.FunctorData (Type u)}

/-- L preserves composition: L(α ∘ β) = L(α) ∘ L(β). -/
theorem toOverFunctorData_comp (α : CategoryJudgments.NatTransData F G)
    (β : CategoryJudgments.NatTransData G H) :
    (α.comp β).toOverFunctorData =
    α.toOverFunctorData.comp β.toOverFunctorData := by
  -- First, show that the objFn components are equal.
  -- (α.comp β).appObj = β.appObj ∘ α.appObj = (α.comp β).toOverFunctorData.objFn
  -- and α.toOverFunctorData.comp β.toOverFunctorData has objFn = β.objFn ∘ α.objFn
  have h_obj : (α.comp β).toOverFunctorData.objFn =
               (α.toOverFunctorData.comp β.toOverFunctorData).objFn := rfl
  -- Next, show morFn components are equal.
  have h_mor : (α.comp β).toOverFunctorData.morFn =
               (α.toOverFunctorData.comp β.toOverFunctorData).morFn := by
    funext m
    simp only [CategoryJudgments.NatTransData.toOverFunctorData,
      CategoryJudgments.NatTransData.toQuotQuiverMor,
      CategoryJudgments.NatTransData.comp, OverFunctorData.comp,
      OverQuiverMorphism.comp,
      CategoryJudgments.NatTransData.toCategoryQuotientMorphism,
      CategoryQuotientData.bundleQuotMor, Function.comp_apply]
    congr 1
    congr 1
    -- Need to show quotMapMor of (α.comp β) equals composition of quotMapMors
    --   (α.comp β).toCategoryQuotientMorphism.quiverMor =
    --   α.toCategoryQuotientMorphism.quiverMor.comp β.toCategoryQuotientMorphism.quiverMor
    -- and quotMapMor respects this composition.
    induction m.2.2 using Quotient.ind with
    | _ fm =>
      simp only [CategoryQuotientMorphism.quotMapMor, CategoryQuotientData.quotMor]
      exact congrArg Quotient.mk''
        (FreeMor.mapQuiver_quiverComp
          α.toCategoryQuotientMorphism.quiverMor
          β.toCategoryQuotientMorphism.quiverMor fm)
  -- Use ext to reduce to component equality.
  ext x
  · exact congrFun h_obj x
  · exact congrFun h_mor x

end LFunctorMorphisms

/-! ## Adjunction Structure

The adjunction L ⊣ Φ between Cat and [CategoryJudgments, Type].

The unit η : Id → Φ ∘ L takes a copresheaf F to its quotient category's
copresheaf representation.

The counit ε : L ∘ Φ → Id evaluates free morphisms in a category.
-/

section AdjunctionStructure

/-- The unit of the adjunction sends a morphism in a copresheaf to its
    equivalence class in the free category.
    η_F : F → Φ(L(F)) sends each morphism f to [var f]. -/
def unitComponent (F : CategoryJudgments.FunctorData (Type u))
    (f : F.morC) :
    F.toCategoryQuotientData.QuotMor (F.dom f) (F.cod f) :=
  F.toCategoryQuotientData.quotMor (FreeMor.var (Q := F.toQuiver) f)

/-- For a category C, the counit evaluates free morphisms, returning
    a morphism in the bundled sigma type. -/
def counitEvalAux {Q : OverQuiver.{u, u}} (C : OverCategoryData Q)
    {a b : Q.Obj} (m : FreeMor Q a b) :
    { f : Q.MorType // Q.src f = a ∧ Q.tgt f = b } :=
  match m with
  | .var f => ⟨f, rfl, rfl⟩
  | .id x => ⟨C.idFn x, C.id_src x, C.id_tgt x⟩
  | .comp g f =>
    let ⟨fVal, fSrc, fTgt⟩ := counitEvalAux C f
    let ⟨gVal, gSrc, gTgt⟩ := counitEvalAux C g
    let composable : Q.tgt fVal = Q.src gVal := by rw [fTgt, gSrc]
    let comp := C.compFn ⟨(fVal, gVal), composable⟩
    ⟨comp, by rw [C.comp_src]; exact fSrc, by rw [C.comp_tgt]; exact gTgt⟩

/-- For a category C, the counit evaluates free morphisms.
    ε_C : L(Φ(C)) → C sends [var f] to f, [id a] to id a, and
    [comp g f] to g ∘ f. -/
def counitEval {Q : OverQuiver.{u, u}} (C : OverCategoryData Q)
    {a b : Q.Obj} (m : FreeMor Q a b) : Q.MorType :=
  (counitEvalAux C m).val

end AdjunctionStructure

/-! ## Counit Respects Equivalence

For the round-trip L(Φ(C)) → C to be well-defined, we need to show that
`counitEval` respects the equivalence relation on free morphisms. -/

section CounitRespects

variable {Q : OverQuiver.{u, u}} (C : OverCategoryData Q)

/-- Abbreviation for the CategoryQuotientData derived from C. -/
abbrev derivedQuotientData : CategoryQuotientData.{u, u} :=
  C.toJudgmentFunctorData.toCategoryQuotientData

/-- Source of counitEvalAux matches FreeMor source. -/
theorem counitEvalAux_src {a b : Q.Obj} (m : FreeMor Q a b) :
    Q.src (counitEvalAux C m).val = a :=
  (counitEvalAux C m).property.1

/-- Target of counitEvalAux matches FreeMor target. -/
theorem counitEvalAux_tgt {a b : Q.Obj} (m : FreeMor Q a b) :
    Q.tgt (counitEvalAux C m).val = b :=
  (counitEvalAux C m).property.2

/-- counitEval of a composition. -/
theorem counitEval_comp {a b c : Q.Obj}
    (g : FreeMor Q b c) (f : FreeMor Q a b) :
    counitEval C (FreeMor.comp g f) =
    C.compFn ⟨(counitEval C f, counitEval C g),
      (counitEvalAux C f).property.2.trans (counitEvalAux C g).property.1.symm⟩ := by
  conv_lhs => unfold counitEval counitEvalAux
  conv_rhs => unfold counitEval
  let ⟨fVal, fSrc, fTgt⟩ := counitEvalAux C f
  let ⟨gVal, gSrc, gTgt⟩ := counitEvalAux C g
  rfl

/-- counitEval of identity. -/
theorem counitEval_id {a : Q.Obj} :
    counitEval C (FreeMor.id a) = C.idFn a := by
  simp only [counitEval, counitEvalAux]

/-- Left identity: counitEval (comp (id b) f) = counitEval f -/
theorem counitEval_id_left {a b : Q.Obj} (f : FreeMor Q a b) :
    counitEval C (FreeMor.comp (FreeMor.id b) f) = counitEval C f := by
  simp only [counitEval_comp, counitEval_id]
  have h_tgt : Q.tgt (counitEval C f) = b := counitEvalAux_tgt C f
  have h := C.comp_id (counitEval C f)
  convert h using 1
  simp only [h_tgt]

/-- Right identity: counitEval (comp f (id a)) = counitEval f -/
theorem counitEval_id_right {a b : Q.Obj} (f : FreeMor Q a b) :
    counitEval C (FreeMor.comp f (FreeMor.id a)) = counitEval C f := by
  simp only [counitEval_comp, counitEval_id]
  have h_src : Q.src (counitEval C f) = a := counitEvalAux_src C f
  have h := C.id_comp (counitEval C f)
  convert h using 1
  simp only [h_src]

/-- Associativity: counitEval (comp h (comp g f)) =
    counitEval (comp (comp h g) f) -/
theorem counitEval_assoc {a b c d : Q.Obj}
    (h : FreeMor Q c d) (g : FreeMor Q b c) (f : FreeMor Q a b) :
    counitEval C (FreeMor.comp h (FreeMor.comp g f)) =
    counitEval C (FreeMor.comp (FreeMor.comp h g) f) := by
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
    {f g : FreeMor Q a b} (h : FreeMor Q b c)
    (heq : counitEval C f = counitEval C g) :
    counitEval C (FreeMor.comp h f) = counitEval C (FreeMor.comp h g) := by
  simp only [counitEval_comp]
  congr 1
  ext
  · exact heq
  · rfl

/-- Congruence right: if counitEval f = counitEval g, then
    counitEval (comp f k) = counitEval (comp g k). -/
theorem counitEval_cong_right {a b c : Q.Obj}
    {f g : FreeMor Q b c} (k : FreeMor Q a b)
    (heq : counitEval C f = counitEval C g) :
    counitEval C (FreeMor.comp f k) = counitEval C (FreeMor.comp g k) := by
  simp only [counitEval_comp]
  congr 1
  ext
  · rfl
  · exact heq

/-- counitEval respects cast on FreeMor. -/
theorem counitEval_cast {a b a' b' : Q.Obj}
    (ha : a = a') (hb : b = b') (m : FreeMor Q a b) :
    counitEval C (cast (by rw [ha, hb]) m) = counitEval C m := by
  subst ha hb
  rfl

/-- counitEval of a variable. -/
theorem counitEval_var {a b : Q.Obj} (f : Q.MorType)
    (hsrc : Q.src f = a) (htgt : Q.tgt f = b) :
    counitEval C (cast (by rw [hsrc, htgt]) (FreeMor.var f)) = f := by
  subst hsrc htgt
  rfl

/-- The derivedQuotientData idObj is just the identity on Q.Obj. -/
theorem derivedQuotientData_idObj (i : Q.Obj) :
    (derivedQuotientData C).idObj i = i :=
  C.id_src i

/-- The derivedQuotientData idMor is just C.idFn. -/
theorem derivedQuotientData_idMor (i : Q.Obj) :
    (derivedQuotientData C).idMor i = C.idFn i :=
  rfl

/-- The derivedQuotientData compRight is the first component of the pair. -/
theorem derivedQuotientData_compRight (c : Q.ComposablePairsType) :
    (derivedQuotientData C).compRight c = c.val.1 :=
  rfl

/-- The derivedQuotientData compLeft is the second component of the pair. -/
theorem derivedQuotientData_compLeft (c : Q.ComposablePairsType) :
    (derivedQuotientData C).compLeft c = c.val.2 :=
  rfl

/-- The derivedQuotientData compComposite is the composition. -/
theorem derivedQuotientData_compComposite (c : Q.ComposablePairsType) :
    (derivedQuotientData C).compComposite c = C.compFn c :=
  rfl

/-- The quiver of derivedQuotientData is definitionally equal to Q. -/
theorem derivedQuotientData_quiver : (derivedQuotientData C).quiver = Q := rfl

/-- counitEval of a variable (without cast). -/
theorem counitEval_var_eq (f : Q.MorType) :
    counitEval C (FreeMor.var f) = f := rfl

/-- counitEvalAux commutes with cast on index equality. -/
theorem counitEvalAux_cast_idx {a b a' b' : Q.Obj}
    (ha : a = a') (hb : b = b') (m : FreeMor Q a b) :
    (counitEvalAux C (cast (by rw [ha, hb]) m)).val = (counitEvalAux C m).val := by
  subst ha hb
  rfl

/-- counitEval commutes with cast on index equality. -/
theorem counitEval_cast_idx {a b a' b' : Q.Obj}
    (ha : a = a') (hb : b = b') (m : FreeMor Q a b) :
    counitEval C (cast (by rw [ha, hb]) m) = counitEval C m := by
  subst ha hb
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Helper: counitEval respects the generating relations. -/
theorem counitEval_respects_gen {a b : Q.Obj}
    {f g : FreeMor Q a b}
    (r : CategoryQuotientData.FreeMorEquivGen (derivedQuotientData C) f g) :
    counitEval C f = counitEval C g := by
  match r with
  | .id_left f' => exact counitEval_id_left C f'
  | .id_right f' => exact counitEval_id_right C f'
  | .assoc h' g' f' => exact counitEval_assoc C h' g' f'
  | .id_witness i =>
    have htgt : Q.tgt (C.idFn i) = Q.src (C.idFn i) :=
      (C.id_tgt i).trans (C.id_src i).symm
    simp only [CategoryJudgments.FunctorData.toCategoryQuotientData,
      OverCategoryData.toJudgmentFunctorData,
      counitEval_var C (C.idFn i) rfl htgt, counitEval_id, C.id_src i]
  | .comp_witness c =>
    simp only [CategoryJudgments.FunctorData.toCategoryQuotientData,
      OverCategoryData.toJudgmentFunctorData,
      counitEval_comp, counitEval_var_eq,
      counitEval_var C c.val.2 c.property.symm rfl,
      counitEval_var C (C.compFn c) (C.comp_src c) (C.comp_tgt c)]
    rfl
  | .cong_left h' hfg => exact counitEval_cong_left C h' (counitEval_respects_gen hfg)
  | .cong_right k hfg => exact counitEval_cong_right C k (counitEval_respects_gen hfg)

/-- counitEval respects the full equivalence relation. -/
theorem counitEval_respects {a b : Q.Obj}
    {f g : FreeMor Q a b}
    (h : CategoryQuotientData.FreeMorEquiv (derivedQuotientData C) f g) :
    counitEval C f = counitEval C g :=
  match h with
  | .rel hr => counitEval_respects_gen C hr
  | .refl _ => rfl
  | .symm h' => (counitEval_respects h').symm
  | .trans h1 h2 => (counitEval_respects h1).trans (counitEval_respects h2)

end CounitRespects

/-! ## Round-trip Properties

The relationship between L and Φ:
- L(Φ(C)) ≃ C for any category C
- Φ(L(F)) contains F as a subcategory for any copresheaf F
-/

section RoundTrip

variable {Q : OverQuiver.{u, u}} (C : OverCategoryData Q)

/-- The morphism type over objects a, b in the quiver. -/
abbrev MorOver' (Q : OverQuiver.{u, u}) (a b : Q.Obj) :=
  { f : Q.MorType // Q.src f = a ∧ Q.tgt f = b }

/-- The counit induces a function on the quotient. -/
def counitEvalQuot {a b : Q.Obj} :
    (derivedQuotientData C).QuotMor a b → MorOver' Q a b :=
  Quotient.lift
    (fun m => ⟨counitEval C m, counitEvalAux_src C m, counitEvalAux_tgt C m⟩)
    (fun _ _ h => Subtype.ext (counitEval_respects C h))

/-- Embedding a morphism into the quotient of free morphisms. -/
def embedQuot {a b : Q.Obj} (f : MorOver' Q a b) :
    (derivedQuotientData C).QuotMor a b :=
  let m : FreeMor Q (Q.src f.val) (Q.tgt f.val) := .var f.val
  let m' : FreeMor Q a b := cast (by rw [f.property.1, f.property.2]) m
  (derivedQuotientData C).quotMor m'

/-- The counit evaluation of an embedded variable is the original morphism. -/
theorem counitEval_embed {a b : Q.Obj} (f : MorOver' Q a b) :
    counitEvalQuot C (embedQuot C f) = f := by
  simp only [counitEvalQuot, embedQuot, CategoryQuotientData.quotMor]
  rw [Quotient.lift_mk]
  simp only [counitEval_var C f.val f.property.1 f.property.2]

/-- Source of counitEval as a direct equality. -/
theorem counitEval_src {a b : Q.Obj} (m : FreeMor Q a b) :
    Q.src (counitEval C m) = a := counitEvalAux_src C m

/-- Target of counitEval as a direct equality. -/
theorem counitEval_tgt {a b : Q.Obj} (m : FreeMor Q a b) :
    Q.tgt (counitEval C m) = b := counitEvalAux_tgt C m

set_option backward.isDefEq.respectTransparency false in
/-- Auxiliary: [var (counitEval m)] ~ m as FreeMor equivalence.
    This is the substance of the round-trip proof. -/
theorem var_counitEval_equiv {a b : Q.Obj} (fm : FreeMor Q a b) :
    (derivedQuotientData C).FreeMorEquiv
      (cast (congrArg₂ (FreeMor Q) (counitEval_src C fm) (counitEval_tgt C fm))
        (FreeMor.var (counitEval C fm)))
      fm := by
  induction fm with
  | var f =>
    exact .refl _
  | id x =>
    let D := derivedQuotientData C
    -- id_witness x gives: [var (C.idFn x)] ~ id (D.idObj x)
    -- D.idObj x = Q.src (C.idFn x)
    -- We need: [var (C.idFn x)] ~ id x
    -- So we need to show id (Q.src (C.idFn x)) = id x via the cast
    -- Since C.id_src x : Q.src (C.idFn x) = x, we have FreeMor.id (D.idObj x) = FreeMor.id x
    have idObj_eq : D.idObj x = x := C.id_src x
    -- The LHS of id_witness is:
    --   cast (by rw [D.id_src x, D.id_tgt x]) (FreeMor.var (D.idMor x))
    -- D.id_src x = rfl (definitionally)
    -- D.id_tgt x proves Q.tgt (C.idFn x) = D.idObj x = Q.src (C.idFn x)
    -- So LHS is: cast (by rfl; exact (C.id_tgt x).trans (C.id_src x).symm) (var (C.idFn x))
    --
    -- Our goal is: (cast _ (var (C.idFn x))) ~ (id x)
    -- The cast proof in our goal uses C.id_src and C.id_tgt directly
    --
    -- id_witness gives: lhs_witness ~ FreeMor.id (D.idObj x) = FreeMor.id (Q.src (C.idFn x))
    -- We need: our_lhs ~ FreeMor.id x
    --
    -- Strategy: both LHS terms are the same (after unfolding), and we rewrite the RHS
    have h_id_witness := CategoryQuotientData.FreeMorEquivGen.id_witness (D := D) x
    -- h_id_witness : D.FreeMorEquivGen
    --   (cast _ (FreeMor.var (D.idMor x)))
    --   (FreeMor.id (D.idObj x))
    -- Now we need to convert FreeMor.id (D.idObj x) to FreeMor.id x
    -- Since D.idObj x = x (by idObj_eq), we can cast the RHS
    have h' : D.FreeMorEquivGen
        (cast (congrArg₂ (FreeMor Q) (C.id_src x) (C.id_tgt x)) (FreeMor.var (C.idFn x)))
        (FreeMor.id x) := by
      convert h_id_witness using 2 <;> simp only [idObj_eq]
    exact .rel h'
  | @comp a b c g f ihg ihf =>
    let D := derivedQuotientData C
    let fVal := counitEval C f
    let gVal := counitEval C g
    have srcf_eq : Q.src fVal = a := counitEval_src C f
    have tgtf_eq : Q.tgt fVal = b := counitEval_tgt C f
    have srcg_eq : Q.src gVal = b := counitEval_src C g
    have tgtg_eq : Q.tgt gVal = c := counitEval_tgt C g
    have composable : Q.tgt fVal = Q.src gVal := tgtf_eq.trans srcg_eq.symm
    let hpair : Q.ComposablePairsType := ⟨(fVal, gVal), composable⟩
    have pair_eq : counitEval C (FreeMor.comp g f) = C.compFn hpair := counitEval_comp C g f
    -- Work at "natural" indices (Q.src fVal, Q.tgt fVal) and (Q.src gVal, Q.tgt gVal)
    -- Define casted versions of f and g at natural indices
    let f_nat : FreeMor Q (Q.src fVal) (Q.tgt fVal) :=
      cast (congrArg₂ (FreeMor Q) srcf_eq.symm tgtf_eq.symm) f
    let g_nat : FreeMor Q (Q.src gVal) (Q.tgt gVal) :=
      cast (congrArg₂ (FreeMor Q) srcg_eq.symm tgtg_eq.symm) g
    -- Transform ihf: cast (srcf_eq, tgtf_eq) (var fVal) ~ f
    -- to: var fVal ~ f_nat
    have ihf_nat : D.FreeMorEquiv (.var fVal) f_nat := by
      have h := CategoryQuotientData.FreeMorEquiv.cast (D := D) srcf_eq.symm tgtf_eq.symm ihf
      simp only [cast_cast] at h
      convert h using 2
    -- Transform ihg: cast (srcg_eq, tgtg_eq) (var gVal) ~ g
    -- to: var gVal ~ g_nat
    have ihg_nat : D.FreeMorEquiv (.var gVal) g_nat := by
      have h := CategoryQuotientData.FreeMorEquiv.cast (D := D) srcg_eq.symm tgtg_eq.symm ihg
      simp only [cast_cast] at h
      convert h using 2
    -- comp_witness: comp (cast composable.symm (var gVal)) (var fVal)
    --             ~ cast (comp_dom, comp_cod) (var compComposite)
    -- This is at type FreeMor Q (Q.src fVal) (Q.tgt gVal)
    have h_cw := CategoryQuotientData.FreeMorEquivGen.comp_witness (D := D) hpair
    have step1 := CategoryQuotientData.FreeMorEquiv.symm (.rel h_cw)
    -- step1: cast _ (var compComposite) ~ comp (cast _ (var gVal)) (var fVal)
    -- Need to relate (cast _ (var gVal)) to g_nat cast to (Q.tgt fVal, Q.tgt gVal)
    let g_shifted : FreeMor Q (Q.tgt fVal) (Q.tgt gVal) :=
      cast (congrArg₂ (FreeMor Q) composable.symm rfl) (.var gVal)
    let g_nat_shifted : FreeMor Q (Q.tgt fVal) (Q.tgt gVal) :=
      cast (congrArg₂ (FreeMor Q) composable.symm rfl) g_nat
    -- Show: g_shifted ~ g_nat_shifted
    have ihg_shifted : D.FreeMorEquiv g_shifted g_nat_shifted :=
      CategoryQuotientData.FreeMorEquiv.cast (D := D) composable.symm rfl ihg_nat
    -- comp_respects: comp g_shifted (var fVal) ~ comp g_nat_shifted f_nat
    have step2 : D.FreeMorEquiv (.comp g_shifted (.var fVal)) (.comp g_nat_shifted f_nat) :=
      CategoryQuotientData.comp_respects D ihf_nat ihg_shifted
    -- Combine step1 and step2
    have step3 : D.FreeMorEquiv
        (cast (congrArg₂ (FreeMor Q) (D.comp_dom hpair) (D.comp_cod hpair))
          (.var (D.compComposite hpair)))
        (.comp g_nat_shifted f_nat) :=
      CategoryQuotientData.FreeMorEquiv.trans step1 step2
    -- Show comp g_nat_shifted f_nat ~ comp g f via equivalence relation
    -- We prove this by relating g_nat_shifted to g and f_nat to f
    -- g_nat = cast ... g, g_nat_shifted = cast ... g_nat = cast ... (cast ... g)
    -- The double cast on g simplifies when we use FreeMorEquiv.cast
    --
    -- Alternative approach: prove comp g_nat_shifted f_nat ~ comp g f directly
    -- by relating both to intermediate terms
    --
    -- First relate g_nat_shifted to g via casting
    -- g_nat_shifted : FreeMor Q (Q.tgt fVal) (Q.tgt gVal)
    -- We need to show g_nat_shifted ~ cast ... g at type FreeMor Q (Q.tgt fVal) (Q.tgt gVal)
    -- where the cast goes from (b, c) to (Q.tgt fVal, Q.tgt gVal)
    let g_casted : FreeMor Q (Q.tgt fVal) (Q.tgt gVal) :=
      cast (congrArg₂ (FreeMor Q) tgtf_eq.symm tgtg_eq.symm) g
    -- Show g_nat_shifted = g_casted (both are casts of g to the same type)
    have g_shifted_eq_casted : g_nat_shifted = g_casted := by
      simp only [g_nat_shifted, g_nat, g_casted]
      rw [cast_cast]
    -- Now we can use g_shifted_eq_casted
    have step4 : D.FreeMorEquiv (.comp g_nat_shifted f_nat) (.comp g_casted f_nat) := by
      rw [g_shifted_eq_casted]
      exact .refl _
    -- Show comp g_casted f_nat = cast ... (comp g f) at FreeMor Q (Q.src fVal) (Q.tgt gVal)
    -- g_casted : FreeMor Q (Q.tgt fVal) (Q.tgt gVal) = cast (tgtf_eq.symm, tgtg_eq.symm) g
    -- f_nat : FreeMor Q (Q.src fVal) (Q.tgt fVal) = cast (srcf_eq.symm, tgtf_eq.symm) f
    -- comp g_casted f_nat : FreeMor Q (Q.src fVal) (Q.tgt gVal)
    -- We want this to equal cast (srcf_eq.symm, tgtg_eq.symm) (comp g f)
    have comp_casted_eq : FreeMor.comp g_casted f_nat =
        cast (congrArg₂ (FreeMor Q) srcf_eq.symm tgtg_eq.symm) (.comp g f) := by
      simp only [g_casted, f_nat]
      exact CategoryQuotientData.FreeMor.cast_comp (D := D)
        srcf_eq.symm tgtf_eq.symm tgtg_eq.symm g f
    have step5 : D.FreeMorEquiv (.comp g_casted f_nat)
        (cast (congrArg₂ (FreeMor Q) srcf_eq.symm tgtg_eq.symm) (.comp g f)) := by
      rw [comp_casted_eq]
      exact .refl _
    have step6 : D.FreeMorEquiv (.comp g_nat_shifted f_nat)
        (cast (congrArg₂ (FreeMor Q) srcf_eq.symm tgtg_eq.symm) (.comp g f)) :=
      CategoryQuotientData.FreeMorEquiv.trans step4 step5
    have step7 : D.FreeMorEquiv
        (cast (congrArg₂ (FreeMor Q) (D.comp_dom hpair) (D.comp_cod hpair))
          (.var (D.compComposite hpair)))
        (cast (congrArg₂ (FreeMor Q) srcf_eq.symm tgtg_eq.symm) (.comp g f)) :=
      CategoryQuotientData.FreeMorEquiv.trans step3 step6
    -- Cast to final indices (a, c)
    have step8 := CategoryQuotientData.FreeMorEquiv.cast (D := D) srcf_eq tgtg_eq step7
    simp only [cast_cast] at step8
    convert step8 using 2
    · exact pair_eq ▸ HEq.rfl

/-- Embedding the counit evaluation gives back the original quotient element.
    This requires showing that [var (counitEval m)] ~ m. -/
theorem embed_counitEval {a b : Q.Obj} (m : (derivedQuotientData C).QuotMor a b) :
    embedQuot C (counitEvalQuot C m) = m := by
  induction m using Quotient.ind with
  | _ fm =>
    simp only [counitEvalQuot, embedQuot, CategoryQuotientData.quotMor, Quotient.lift_mk]
    exact Quotient.sound (var_counitEval_equiv C fm)

/-- The isomorphism between the quotient morphisms and the original morphisms. -/
def roundtripEquiv {a b : Q.Obj} :
    (derivedQuotientData C).QuotMor a b ≃ MorOver' Q a b where
  toFun := counitEvalQuot C
  invFun := embedQuot C
  left_inv := embed_counitEval C
  right_inv := counitEval_embed C

end RoundTrip

/-! ## Unit Natural Transformation

The unit η : Id → Φ ∘ L sends a copresheaf F to the quotient category's
copresheaf. For each morphism f in F, it maps to [var f] in the quotient. -/

section UnitNatTrans

variable (F : CategoryJudgments.FunctorData (Type u))

/-- The quotient category L(F) viewed as an OverCategoryData. -/
abbrev quotCatData := F.toOverCategoryData

/-- The copresheaf Φ(L(F)) corresponding to the quotient category. -/
abbrev phiOfL := F.toOverCategoryData.toJudgmentFunctorData

/-- The morphism component of the unit: embed f as ⟨dom f, cod f, [var f]⟩. -/
def unitAppMor : F.morC → (phiOfL F).morC :=
  fun f => ⟨F.dom f, F.cod f, unitComponent F f⟩

/-- The identity component of the unit: map identity witness to the object it
    provides identity for. F.idC is the set of identity witnesses, and
    (phiOfL F).idC = quotQuiver.Obj = F.objC.
    The map extracts the object: i ↦ dom(idMor i). -/
def unitAppId : F.idC → (phiOfL F).idC := fun i => F.dom (F.idMor i)

/-- The composition component of the unit: embed composable pairs.
    A composable pair (g, f) in F maps to a composable pair
    ([var g], [var f]) in the quotient category. -/
def unitAppComp : F.compC → (phiOfL F).compC :=
  fun c =>
    let f := F.right c
    let g := F.left c
    let fQuot : (phiOfL F).morC := unitAppMor F f
    let gQuot : (phiOfL F).morC := unitAppMor F g
    -- Need to show they are composable: cod fQuot = dom gQuot
    -- cod fQuot = F.cod f, dom gQuot = F.dom g
    -- F.h_comp_match says F.cod (F.right c) = F.dom (F.left c)
    let composable : (phiOfL F).cod fQuot = (phiOfL F).dom gQuot := by
      simp only [OverCategoryData.toJudgmentFunctorData]
      exact congrFun F.h_comp_match c
    ⟨(fQuot, gQuot), composable⟩

/-- The object component of the unit: identity on objects.
    F.objC = (phiOfL F).objC since both equal the object type. -/
def unitAppObj : F.objC ⟶ (phiOfL F).objC := 𝟙 F.objC

set_option backward.isDefEq.respectTransparency false in
/-- The unit natural transformation η_F : F → Φ(L(F)).
    This embeds F's data into the free category on F then extracts back. -/
def unitNatTrans : CategoryJudgments.NatTransData F (phiOfL F) where
  appObj := unitAppObj F
  appMor := unitAppMor F
  appId := unitAppId F
  appComp := unitAppComp F
  naturality_dom := by
    ext m
    simp only [CategoryStruct.comp, unitAppObj]
    rfl
  naturality_cod := by
    ext m
    simp only [CategoryStruct.comp, unitAppObj]
    rfl
  naturality_idMor := by
    ext i
    change unitAppMor F (F.idMor i) = (phiOfL F).idMor (unitAppId F i)
    simp only [unitAppMor, unitAppId,
      OverCategoryData.toJudgmentFunctorData,
      CategoryJudgments.FunctorData.toOverCategoryData,
      CategoryQuotientData.toOverCategoryData,
      CategoryQuotientData.quotCategoryOps,
      CategoryQuotientData.quotIdFn,
      unitComponent, CategoryQuotientData.quotId,
      CategoryJudgments.FunctorData.toCategoryQuotientData]
    -- Goal: ⟨dom, ⟨cod, [var (idMor i)]⟩⟩ = ⟨dom, ⟨dom, [id dom]⟩⟩
    -- h_id_endo gives: dom (idMor i) = cod (idMor i)
    -- So h_id_endo.symm : cod (idMor i) = dom (idMor i)
    have h_endo : F.dom (F.idMor i) = F.cod (F.idMor i) := congrFun F.h_id_endo i
    -- For outer sigma: first components are both dom (idMor i), so rfl
    refine Sigma.ext rfl ?_
    -- Now HEq of inner sigmas, which have the same type Σ b, QuotMor (dom _) b
    refine heq_of_eq ?_
    -- For inner sigma: first components are cod vs dom, use h_endo.symm
    refine Sigma.ext h_endo.symm ?_
    -- Now HEq of quotient types: QuotMor dom cod vs QuotMor dom dom
    -- LHS: quotMor (var (idMor i)) at type QuotMor dom cod
    -- RHS: quotMor (id dom) at type QuotMor dom dom
    let D := F.toCategoryQuotientData
    -- Use id_witness which relates cast(var) ~ id at the FreeMor level
    have h_wit := CategoryQuotientData.FreeMorEquivGen.id_witness (D := D) i
    -- h_wit : FreeMorEquivGen (cast _ (var (D.idMor i))) (id (D.idObj i))
    -- Quotient.sound gives: quotMor(cast(var)) = quotMor(id)
    have h_quot_eq : D.quotMor (cast (congrArg₂ (FreeMor D.quiver)
          (D.id_src i) (D.id_tgt i))
        (FreeMor.var (D.idMor i))) = D.quotMor (FreeMor.id (D.idObj i)) :=
      Quotient.sound (CategoryQuotientData.FreeMorEquiv.rel h_wit)
    -- We need: quotMor(var(idMor)) ≍ quotMor(id(idObj))
    -- where LHS : QuotMor dom cod and RHS : QuotMor dom dom
    -- Strategy: use the fact that after casting LHS to type QuotMor dom dom,
    -- it equals RHS, and cast preserves HEq
    -- Use the equivalence: x ≍ y ↔ ∃ h : A = B, cast h x = y
    apply HEq.trans (cast_heq (congrArg₂ D.QuotMor (D.id_src i) (D.id_tgt i)) _).symm
    -- Goal: cast _ (quotMor (var (idMor i))) ≍ quotMor (id (idObj i))
    apply heq_of_eq
    -- Goal: cast _ (quotMor (var (idMor i))) = quotMor (id (idObj i))
    -- Unfold the .snd.snd projections
    simp only []
    -- Restate goal in terms of D instead of the expanded structure
    change cast (congrArg₂ D.QuotMor (D.id_src i) (D.id_tgt i))
        (D.quotMor (FreeMor.var (D.idMor i))) =
      D.quotMor (FreeMor.id (D.idObj i))
    -- Use quotMor_cast lemma to show cast on QuotMor = quotMor of cast
    rw [D.quotMor_cast (D.id_src i) (D.id_tgt i)]
    -- Now both sides are quotMor of something, use h_quot_eq
    exact h_quot_eq
  naturality_left := by
    ext c
    simp only [CategoryStruct.comp, OverCategoryData.toJudgmentFunctorData]
    rfl
  naturality_right := by
    ext c
    simp only [CategoryStruct.comp, OverCategoryData.toJudgmentFunctorData]
    rfl
  naturality_composite := by
    ext c
    change unitAppMor F (F.composite c) = F.toOverCategoryData.compFn (unitAppComp F c)
    simp only [unitAppMor, unitAppComp,
      OverCategoryData.toJudgmentFunctorData,
      CategoryJudgments.FunctorData.toOverCategoryData,
      CategoryQuotientData.toOverCategoryData,
      CategoryQuotientData.quotCategoryOps,
      CategoryQuotientData.quotCompFn,
      unitComponent]
    -- Goal: ⟨dom(composite c), ⟨cod(composite c), [var (composite c)]⟩⟩ =
    --       ⟨dom(right c), ⟨cod(left c), [left c] ∘ [right c]⟩⟩
    -- comp_witness gives: (cast _ (var left)).comp (var right) ~ cast _ (var composite)
    let D := F.toCategoryQuotientData
    have h_wit := CategoryQuotientData.FreeMorEquivGen.comp_witness (D := D) c
    have hquot := Quotient.sound (s := D.freeMorSetoid _ _)
      (CategoryQuotientData.FreeMorEquiv.rel h_wit)
    -- Need to prove nested sigma equality where indices differ
    -- LHS: ⟨dom composite, ⟨cod composite, quotMor (var composite)⟩⟩
    -- RHS: ⟨dom right, ⟨cod left, quotComp (quotMor left) (cast _ (quotMor right))⟩⟩
    have h_dom : F.dom (F.composite c) = F.dom (F.right c) := congrFun F.h_comp_dom c
    have h_cod : F.cod (F.composite c) = F.cod (F.left c) := congrFun F.h_comp_cod c
    -- hquot relates quotients at (dom right, cod left)
    -- Build the equality term directly
    refine Sigma.ext h_dom ?_
    -- Goal: HEq of ⟨cod composite, quotMor (var composite)⟩
    --       vs ⟨cod left, quotComp (quotMor left) (cast _ (quotMor right))⟩
    -- Use the helper lemma quotMorSigma_heq
    apply D.quotMorSigma_heq h_dom h_cod
    -- Now need: cast (congrArg₂ QuotMor h_dom h_cod) (quotMor (var composite))
    --         = quotComp (quotMor left) (cast _ (quotMor right))
    rw [D.quotMor_cast h_dom h_cod]
    -- Now need: quotMor (cast _ (var composite))
    --         = quotComp (quotMor left) (cast _ (quotMor right))
    -- Use hquot which says the composition equals cast _ (var composite)
    -- hquot : ⟦(cast _ (var left)).comp (var right)⟧ = ⟦cast _ (var composite)⟧
    -- quotComp lifts comp on FreeMor through quotMor
    -- The RHS has quotComp with a transported argument.
    -- The transport uses comp_match : cod(right) = dom(left).
    -- We'll unfold to ⟦...⟧ level and use Quotient.sound.
    --
    -- Step 1: Unfold quotMor and quotComp to get to ⟦...⟧ level
    simp only [CategoryQuotientData.quotMor, CategoryQuotientData.quotComp]
    -- Now goal: ⟦cast _ (var composite)⟧ = Quotient.lift₂ ... ⟦var left⟧ (⋯ ▸ ⟦var right⟧)
    --
    -- Step 2: Simplify Quotient.lift₂ by eliminating the transport
    -- The transport ⋯ ▸ uses congrFun F.h_comp_match c = D.comp_match c
    -- We can generalize it, substitute, and use Quotient.lift₂_mk.
    --
    -- First, let's prove that h ▸ ⟦f⟧ = ⟦h ▸ f⟧ for the specific indices
    -- Using the general lemma for transport commuting with quotient formation:
    -- h ▸ ⟦f⟧ = ⟦h ▸ f⟧ holds by cases on h
    have h_transport_eq : ∀ {a b b' : D.quiver.Obj} (h : b = b') (f : FreeMor D.quiver a b),
        (h ▸ (⟦f⟧ : Quotient (D.freeMorSetoid a b))) =
        (⟦h ▸ f⟧ : Quotient (D.freeMorSetoid a b')) := by
      intro a b b' h f
      cases h
      rfl
    conv_rhs => arg 4; rw [h_transport_eq]
    -- Now goal: ⟦cast _ (var composite)⟧ = Quotient.lift₂ ... ⟦var left⟧ ⟦_ ▸ var right⟧
    rw [Quotient.lift₂_mk]
    -- Now goal: ⟦cast _ (var composite)⟧ = ⟦(var left).comp (_ ▸ var right)⟧
    --
    -- Step 3: Use Quotient.sound
    apply Quotient.sound
    apply CategoryQuotientData.FreeMorEquiv.symm
    -- Goal: FreeMorEquiv ((var left).comp (_ ▸ var right)) (cast _ (var composite))
    --
    -- Step 4: The LHS and RHS are both FreeMorEquiv to (cast _ (var composite))
    -- We need to show they're equivalent.
    -- h_wit : FreeMorEquivGen ((cast _ (var left)).comp (var right)) (cast _ (var composite))
    -- Goal: FreeMorEquiv ((var left).comp (_ ▸ var right)) (cast _ (var composite))
    -- (var left).comp (h ▸ var right) = (cast h.symm (var left)).comp (var right)
    -- Both involve the same comp_match equality, just represented differently.
    -- Prove a general lemma about transport in FreeMor.comp.
    have h_comp_move : ∀ {Q : OverQuiver} {a b b' c : Q.Obj} (h : b = b')
        (g : FreeMor Q b' c) (f : FreeMor Q a b),
        g.comp (h ▸ f) = (cast (congrArg₂ (FreeMor Q) h.symm rfl) g).comp f := by
      intro Q a b b' c h g f
      cases h
      rfl
    rw [h_comp_move]
    exact CategoryQuotientData.FreeMorEquiv.rel h_wit

end UnitNatTrans

/-! ## Counit Natural Transformation

The counit ε : L ∘ Φ → Id evaluates quotient morphisms back in the original
category. For a category C, ε_C : L(Φ(C)) → C maps quotient classes of
free morphisms to their evaluations. -/

section CounitNatTrans

variable {Q : OverQuiver.{u, u}} (C : OverCategoryData Q)

/-- The counit as a quiver morphism from the quotient quiver to the original
    quiver. Objects are identity, morphisms are evaluated via counitEvalQuot. -/
def counitQuiverMor : OverQuiverMorphism (derivedQuotientData C).quotQuiver Q
    where
  objFn := id
  morFn := fun ⟨a, b, qm⟩ => (counitEvalQuot C qm).val
  src_comm := fun ⟨a, b, qm⟩ => by
    simp only [CategoryQuotientData.quotQuiver, id]
    exact (counitEvalQuot C qm).property.1
  tgt_comm := fun ⟨a, b, qm⟩ => by
    simp only [CategoryQuotientData.quotQuiver, id]
    exact (counitEvalQuot C qm).property.2

set_option backward.isDefEq.respectTransparency false in
/-- Helper: counitEvalQuot on quotId gives idFn. -/
theorem counitEvalQuot_quotId (a : Q.Obj) :
    counitEvalQuot C ((derivedQuotientData C).quotId a) =
    ⟨C.idFn a, C.id_src a, C.id_tgt a⟩ := by
  simp only [counitEvalQuot, CategoryQuotientData.quotId, CategoryQuotientData.quotMor,
    Quotient.lift_mk, counitEval_id]

set_option backward.isDefEq.respectTransparency false in
/-- Helper: counitEvalQuot on quotComp gives compFn. -/
theorem counitEvalQuot_quotComp {a b c : Q.Obj}
    (g : (derivedQuotientData C).QuotMor b c)
    (f : (derivedQuotientData C).QuotMor a b) :
    counitEvalQuot C ((derivedQuotientData C).quotComp g f) =
    ⟨C.compFn ⟨((counitEvalQuot C f).val, (counitEvalQuot C g).val),
      (counitEvalQuot C f).property.2.trans (counitEvalQuot C g).property.1.symm⟩,
      (C.comp_src _).trans (counitEvalQuot C f).property.1,
      (C.comp_tgt _).trans (counitEvalQuot C g).property.2⟩ := by
  induction f using Quotient.ind with
  | _ fm =>
    induction g using Quotient.ind with
    | _ gm =>
      simp only [counitEvalQuot, CategoryQuotientData.quotComp,
        CategoryQuotientData.quotMor, Quotient.lift_mk, counitEval_comp]

/-- The counit preserves identity:
    counitEvalQuot (quotId a) = idFn a. -/
theorem counit_map_id (a : Q.Obj) :
    (counitQuiverMor C).morFn ((derivedQuotientData C).toOverCategoryData.idFn a) =
    C.idFn ((counitQuiverMor C).objFn a) := by
  simp only [counitQuiverMor, CategoryQuotientData.toOverCategoryData,
    CategoryQuotientData.quotCategoryOps, CategoryQuotientData.quotIdFn, id]
  exact congrArg Subtype.val (counitEvalQuot_quotId C a)

/-- The counit preserves composition:
    counitEvalQuot (quotComp g f) = compFn (counitEvalQuot f, counitEvalQuot g). -/
theorem counit_map_comp (p : (derivedQuotientData C).quotQuiver.ComposablePairsType) :
    (counitQuiverMor C).morFn ((derivedQuotientData C).toOverCategoryData.compFn p) =
    C.compFn ⟨((counitQuiverMor C).morFn p.val.1, (counitQuiverMor C).morFn p.val.2),
      ((counitQuiverMor C).tgt_comm p.val.1).trans
        ((congrArg (counitQuiverMor C).objFn p.property).trans
          ((counitQuiverMor C).src_comm p.val.2).symm)⟩ := by
  obtain ⟨⟨⟨a, b, qf⟩, ⟨b', c, qg⟩⟩, h_composable⟩ := p
  simp only [CategoryQuotientData.quotQuiver] at h_composable
  simp only [counitQuiverMor, CategoryQuotientData.toOverCategoryData,
    CategoryQuotientData.quotCategoryOps, CategoryQuotientData.quotCompFn,
    CategoryQuotientData.quotQuiver]
  have h_eq : b = b' := h_composable
  subst h_eq
  have h_eval := counitEvalQuot_quotComp C qg qf
  exact congrArg Subtype.val h_eval

/-- The counit as a functor from L(Φ(C)) to C.
    For a category C, ε_C : L(Φ(C)) → C evaluates quotient morphisms. -/
def counitFunctorData :
    OverFunctorData (derivedQuotientData C).toOverCategoryData C where
  toOverQuiverMorphism := counitQuiverMor C
  map_id := counit_map_id C
  map_comp := counit_map_comp C

end CounitNatTrans

/-! ## Counit Naturality

The counit is natural: for any functor F : C → D, we have F ∘ ε_C = ε_D ∘ L(Φ(F)).
We prove this at the FreeMor level first, then lift to quotients. -/

section CounitNaturality

variable {Q₁ Q₂ : OverQuiver.{u, u}}
variable {C : OverCategoryData Q₁} {D : OverCategoryData Q₂}
variable (F : OverFunctorData C D)

/-- Helper: counitEval on a transported var gives back the morphism. -/
theorem counitEval_var_transport' {Q : OverQuiver.{u, u}} (C' : OverCategoryData Q)
    {a b : Q.Obj} (f : Q.MorType) (hsrc : Q.src f = a) (htgt : Q.tgt f = b) :
    counitEval C' (hsrc ▸ htgt ▸ FreeMor.var f) = f := by
  subst hsrc htgt
  rfl

/-- Naturality of counitEval at the FreeMor level:
    F.morFn (counitEval C m) = counitEval D (mapQuiver F m). -/
theorem counitEval_natural {a b : Q₁.Obj} (m : FreeMor Q₁ a b) :
    F.morFn (counitEval C m) =
    counitEval D (FreeMor.mapQuiver F.toOverQuiverMorphism m) := by
  induction m with
  | var f =>
    simp only [counitEval, counitEvalAux, FreeMor.mapQuiver]
    -- Goal: F.morFn f = counitEval D (F.src_comm f ▸ F.tgt_comm f ▸ var (F.morFn f))
    symm
    exact counitEval_var_transport' D (F.morFn f) (F.src_comm f) (F.tgt_comm f)
  | id x =>
    simp only [counitEval, counitEvalAux, FreeMor.mapQuiver]
    exact F.map_id x
  | comp g f ihg ihf =>
    -- Rewrite using counitEval_comp on both sides
    rw [FreeMor.mapQuiver, counitEval_comp C g f, counitEval_comp D]
    -- Now we need F.morFn (C.compFn ⟨(counitEval C f, counitEval C g), ...⟩) =
    --             D.compFn ⟨(counitEval D (mapQuiver F f), counitEval D (mapQuiver F g)), ...⟩
    -- Use F.map_comp
    have hcomp : Q₁.tgt (counitEval C f) = Q₁.src (counitEval C g) :=
      (counitEvalAux C f).property.2.trans (counitEvalAux C g).property.1.symm
    have map_comp_eq := F.map_comp ⟨(counitEval C f, counitEval C g), hcomp⟩
    rw [map_comp_eq]
    -- Now both sides are D.compFn, so we need to show the pairs are equal
    congr 1
    ext
    · exact ihf
    · exact ihg

/-- The CategoryQuotientMorphism induced by a functor F : C → D. -/
def inducedCategoryQuotientMorphism :
    CategoryQuotientMorphism (derivedQuotientData C) (derivedQuotientData D) where
  quiverMor := F.toOverQuiverMorphism
  idWitMap := F.objFn
  compWitMap := fun p =>
    ⟨(F.morFn p.val.1, F.morFn p.val.2),
      (F.tgt_comm p.val.1).trans
        ((congrArg F.objFn p.property).trans (F.src_comm p.val.2).symm)⟩
  idObj_comm := fun i => by
    -- Goal: F.objFn (D₁.idObj i) = D₂.idObj (F.objFn i)
    -- D₁.idObj i = Q₁.src (C.idFn i)
    -- D₂.idObj (F.objFn i) = Q₂.src (D.idFn (F.objFn i))
    simp only [CategoryJudgments.FunctorData.toCategoryQuotientData,
      OverCategoryData.toJudgmentFunctorData]
    -- F.objFn (Q₁.src (C.idFn i)) = Q₂.src (D.idFn (F.objFn i))
    rw [congrArg F.objFn (C.id_src i)]
    rw [D.id_src (F.objFn i)]
  idMor_comm := fun i => F.map_id i
  compRight_comm := fun _ => rfl
  compLeft_comm := fun _ => rfl
  compComposite_comm := fun c => F.map_comp c

/-- The induced functor L(Φ(F)) on quotient categories maps quotient morphisms
    via mapQuiver. -/
def inducedQuotFunctor_morFn {a b : Q₁.Obj}
    (qm : (derivedQuotientData C).QuotMor a b) :
    (derivedQuotientData D).QuotMor (F.objFn a) (F.objFn b) :=
  (inducedCategoryQuotientMorphism F).quotMapMor qm

/-- Naturality of counitEvalQuot at the quotient level. -/
theorem counitEvalQuot_natural {a b : Q₁.Obj}
    (qm : (derivedQuotientData C).QuotMor a b) :
    F.morFn (counitEvalQuot C qm).val =
    (counitEvalQuot D (inducedQuotFunctor_morFn F qm)).val := by
  induction qm using Quotient.ind with
  | _ fm =>
    simp only [counitEvalQuot, Quotient.lift_mk, inducedQuotFunctor_morFn,
      CategoryQuotientMorphism.quotMapMor, CategoryQuotientData.quotMor]
    exact counitEval_natural F fm

/-- The induced quiver morphism L(Φ(F)) on quotient quivers. -/
def inducedQuiverMor :
    OverQuiverMorphism (derivedQuotientData C).quotQuiver
      (derivedQuotientData D).quotQuiver where
  objFn := F.objFn
  morFn := fun ⟨a, b, qm⟩ => ⟨F.objFn a, F.objFn b, inducedQuotFunctor_morFn F qm⟩
  src_comm := fun ⟨_, _, _⟩ => rfl
  tgt_comm := fun ⟨_, _, _⟩ => rfl

set_option backward.isDefEq.respectTransparency false in
/-- The induced functor L(Φ(F)) : L(Φ(C)) → L(Φ(D)). -/
def inducedQuotFunctor :
    OverFunctorData (derivedQuotientData C).toOverCategoryData
      (derivedQuotientData D).toOverCategoryData where
  toOverQuiverMorphism := inducedQuiverMor F
  map_id := fun a => rfl
  map_comp := fun ⟨⟨f, g⟩, h_composable⟩ => by
    obtain ⟨a, b, qf⟩ := f
    obtain ⟨b', c, qg⟩ := g
    simp only [CategoryQuotientData.quotQuiver] at h_composable
    cases h_composable
    simp only [inducedQuiverMor, CategoryQuotientData.toOverCategoryData,
      CategoryQuotientData.quotCategoryOps, CategoryQuotientData.quotCompFn,
      CategoryQuotientData.quotQuiver, inducedQuotFunctor_morFn,
      CategoryQuotientMorphism.quotMapMor_comp]

/-- Naturality of counit on objects: F and L(Φ(F)) agree on objects. -/
theorem counitFunctor_natural_obj (a : (derivedQuotientData C).quotQuiver.Obj) :
    F.objFn ((counitFunctorData C).toOverQuiverMorphism.objFn a) =
    (counitFunctorData D).toOverQuiverMorphism.objFn
      ((inducedQuotFunctor F).toOverQuiverMorphism.objFn a) := by
  simp only [counitFunctorData, counitQuiverMor,
    inducedQuotFunctor, inducedQuiverMor, id]

/-- Naturality of counit on morphisms: F ∘ ε_C = ε_D ∘ L(Φ(F)) on morphisms. -/
theorem counitFunctor_natural_mor
    (m : (derivedQuotientData C).quotQuiver.MorType) :
    F.morFn ((counitFunctorData C).toOverQuiverMorphism.morFn m) =
    (counitFunctorData D).toOverQuiverMorphism.morFn
      ((inducedQuotFunctor F).toOverQuiverMorphism.morFn m) := by
  obtain ⟨a, b, qm⟩ := m
  simp only [counitFunctorData, counitQuiverMor,
    inducedQuotFunctor, inducedQuiverMor, inducedQuotFunctor_morFn]
  exact counitEvalQuot_natural F qm

end CounitNaturality

/-! ## Triangle Identities

The adjunction L ⊣ Φ requires two triangle identities:
1. (εL) ∘ (Lη) = id_L : For any copresheaf F, ε_{L(F)} ∘ L(η_F) = id_{L(F)}
2. (Φε) ∘ (ηΦ) = id_Φ : For any category C, Φ(ε_C) ∘ η_{Φ(C)} = id_{Φ(C)}

We prove these at the component level. -/

section TriangleIdentities

/-! ### Second Triangle Identity: (Φε) ∘ (ηΦ) = id_Φ

For any category C, the composite Φ(C) → Φ(L(Φ(C))) → Φ(C) is identity. -/

variable {Q : OverQuiver.{u, u}} (C : OverCategoryData Q)

/-- The second triangle identity on morphisms:
    Φ(ε_C) ∘ η_{Φ(C)} = id on morphisms.
    This follows from counitEval_embed: counitEvalQuot(embedQuot f) = f. -/
theorem triangle2_mor (f : Q.MorType) :
    (counitFunctorData C).morFn
      ((unitNatTrans C.toJudgmentFunctorData).appMor f) = f := by
  simp only [unitNatTrans, unitAppMor, counitFunctorData, counitQuiverMor,
    unitComponent, CategoryQuotientData.quotMor, counitEvalQuot, Quotient.lift_mk,
    counitEval, counitEvalAux]

/-- The second triangle identity on identity witnesses:
    Φ(ε_C) ∘ η_{Φ(C)} = id on identity witnesses.
    Since idC = Q.Obj and unitAppId sends i to Q.src (C.idFn i),
    and the counit on objects is id, we need C.id_src. -/
theorem triangle2_id (i : C.toJudgmentFunctorData.idC) :
    (counitFunctorData C).toOverQuiverMorphism.objFn
      ((unitNatTrans C.toJudgmentFunctorData).appId i) =
    i := by
  simp only [unitNatTrans, unitAppId, counitFunctorData, counitQuiverMor, id,
    OverCategoryData.toJudgmentFunctorData]
  exact C.id_src i

/-- The second triangle identity on composition witnesses. -/
theorem triangle2_comp (c : C.toJudgmentFunctorData.compC) :
    let η := unitNatTrans C.toJudgmentFunctorData
    let Φε := (counitFunctorData C).toJudgmentNatTrans
    Φε.appComp (η.appComp c) =
    c := by
  obtain ⟨⟨f, g⟩, h_comp⟩ := c
  simp only [unitNatTrans, unitAppComp, counitFunctorData,
    OverFunctorData.toJudgmentNatTrans, counitQuiverMor,
    OverCategoryData.toJudgmentFunctorData, unitAppMor, unitComponent,
    CategoryQuotientData.quotMor]
  -- Goal: ⟨(counitEvalQuot [var f].val, counitEvalQuot [var g].val), _⟩ = ⟨(f, g), h_comp⟩
  -- Show both components equal using that counitEvalQuot [var m] = m
  let D := derivedQuotientData C
  have hf : (counitEvalQuot C (D.quotMor (FreeMor.var f))).val = f := by
    unfold counitEvalQuot CategoryQuotientData.quotMor
    rw [Quotient.lift_mk]
    rfl
  have hg : (counitEvalQuot C (D.quotMor (FreeMor.var g))).val = g := by
    unfold counitEvalQuot CategoryQuotientData.quotMor
    rw [Quotient.lift_mk]
    rfl
  -- Now rewrite using hf and hg
  ext
  · exact hf
  · exact hg

/-! ### First Triangle Identity: (εL) ∘ (Lη) = id_L

For any copresheaf F, the composite L(F) → L(Φ(L(F))) → L(F) is identity.

The functor L(η_F) embeds each quotient morphism qm in L(F) as a variable
quotMor (var qm) in L(Φ(L(F))). The counit ε_{L(F)} evaluates this back to qm.
-/

variable (F : CategoryJudgments.FunctorData (Type u))

/-- The category L(F) constructed from a copresheaf F. -/
abbrev categoryL : OverCategoryData F.toCategoryQuotientData.quotQuiver :=
  F.toOverCategoryData

/-- The double quotient data L(Φ(L(F))) for the first triangle identity.
    This is the CategoryQuotientData derived from L(F) viewed as a category. -/
abbrev derivedFromL : CategoryQuotientData.{u, u} :=
  derivedQuotientData (categoryL F)

/-- The morphism type of L(F)'s quiver is bundled QuotMor. -/
abbrev bundledQuotMorType : Type u :=
  F.toCategoryQuotientData.quotQuiver.MorType

/-- Bundle a QuotMor as a morphism of the L(F) quiver. -/
def bundleQuotMorL {a b : F.objC}
    (qm : F.toCategoryQuotientData.QuotMor a b) : bundledQuotMorType F :=
  ⟨a, b, qm⟩

/-- Embed a morphism of L(F) as a variable in the free category over Φ(L(F)).
    This is the morphism component of L(η_F). -/
def embedMorAsVar {a b : F.objC}
    (qm : F.toCategoryQuotientData.QuotMor a b) :
    (derivedFromL F).QuotMor a b :=
  (derivedFromL F).quotMor (FreeMor.var (bundleQuotMorL F qm))

/-- The first triangle identity on objects:
    Both L(η_F) and ε_{L(F)} act as identity on objects, so their composition
    is identity. -/
theorem triangle1_obj (a : F.objC) :
    (counitFunctorData (categoryL F)).toOverQuiverMorphism.objFn a = a := by
  simp only [counitFunctorData, counitQuiverMor, id]

/-- The first triangle identity on morphisms:
    ε_{L(F)} ∘ L(η_F) = id on morphisms.
    For any quotient morphism qm in L(F), embedding it as a variable and then
    evaluating via ε gives back qm. -/
theorem triangle1_mor {a b : F.objC}
    (qm : F.toCategoryQuotientData.QuotMor a b) :
    counitEvalQuot (categoryL F) (embedMorAsVar F qm) =
    ⟨bundleQuotMorL F qm, rfl, rfl⟩ := by
  simp only [embedMorAsVar, counitEvalQuot, CategoryQuotientData.quotMor,
    Quotient.lift_mk, counitEval, counitEvalAux, bundleQuotMorL]

/-- The first triangle identity: for any QuotMor, ε ∘ L(η) returns the
    original bundled morphism's underlying value. -/
theorem triangle1_mor_val {a b : F.objC}
    (qm : F.toCategoryQuotientData.QuotMor a b) :
    (counitEvalQuot (categoryL F) (embedMorAsVar F qm)).val =
    bundleQuotMorL F qm := by
  rw [triangle1_mor F qm]

end TriangleIdentities

/-! ## Adjunction Structure

We formalize the adjunction L ⊣ Φ by bundling the functors, natural
transformations, and triangle identities into a single structure.

The adjunction relates:
- Categories (BundledOverCategoryData) via Φ to copresheaves (FunctorData Type)
- Copresheaves via L back to categories

The unit η : id → Φ ∘ L and counit ε : L ∘ Φ → id satisfy:
- (Φε) ∘ (ηΦ) = id_Φ (second triangle, proven for categories)
- (εL) ∘ (Lη) = id_L (first triangle, proven for copresheaves)
-/

section AdjunctionStructure

/-- Bundle an OverCategoryData with its quiver. -/
def bundleOverCategory {Q : OverQuiver.{u, u}} (C : OverCategoryData Q) :
    BundledOverCategoryData.{u, u} where
  quiver := Q
  data := C

/-- The L functor on objects: copresheaf to bundled category. -/
def LFunctorObj (F : CategoryJudgments.FunctorData (Type u)) :
    BundledOverCategoryData.{u, u} :=
  bundleOverCategory F.toOverCategoryData

/-- The Φ functor on objects: bundled category to copresheaf. -/
def PhiFunctorObj (C : BundledOverCategoryData.{u, u}) :
    CategoryJudgments.FunctorData (Type u) :=
  C.data.toJudgmentFunctorData

/-- The unit natural transformation component at F : F → Φ(L(F)). -/
def unitNatTransComponent (F : CategoryJudgments.FunctorData (Type u)) :
    CategoryJudgments.NatTransData F (PhiFunctorObj (LFunctorObj F)) :=
  unitNatTrans F

/-- The counit functor component at C : L(Φ(C)) → C.
    Note: This requires the quivers to match, which they do definitionally
    when C comes from bundleOverCategory. -/
def counitComponent {Q : OverQuiver.{u, u}} (C : OverCategoryData Q) :
    OverFunctorData (derivedQuotientData C).toOverCategoryData C :=
  counitFunctorData C

/-- The adjunction data bundling L, Φ, unit, counit, and triangle identities.
    This structure captures the mathematical content of the adjunction L ⊣ Φ. -/
structure CatCopresheafAdjunctionData where
  /-- The L functor maps copresheaves to categories. -/
  L_obj : CategoryJudgments.FunctorData (Type u) → BundledOverCategoryData.{u, u}
  /-- The Φ functor maps categories to copresheaves. -/
  Phi_obj : BundledOverCategoryData.{u, u} → CategoryJudgments.FunctorData (Type u)
  /-- Unit: F → Φ(L(F)) for each copresheaf F. -/
  unit : (F : CategoryJudgments.FunctorData (Type u)) →
    CategoryJudgments.NatTransData F (Phi_obj (L_obj F))
  /-- Counit component: L(Φ(C)) → C for categories in the image of L. -/
  counit_on_L : (F : CategoryJudgments.FunctorData (Type u)) →
    OverFunctorData
      (derivedQuotientData (L_obj F).data).toOverCategoryData
      (L_obj F).data
  /-- Second triangle: Φ(ε_C) ∘ η_{Φ(C)} = id on morphisms. -/
  triangle2_mor_eq : ∀ {Q : OverQuiver.{u, u}} (C : OverCategoryData Q)
    (f : Q.MorType),
    (counitFunctorData C).morFn
      ((unitNatTrans C.toJudgmentFunctorData).appMor f) = f
  /-- First triangle: ε_{L(F)} ∘ L(η_F) = id on morphisms.
      Given a QuotMor qm in L(F), embedding as variable and evaluating
      returns the bundled morphism. -/
  triangle1_mor_eq : ∀ (F : CategoryJudgments.FunctorData (Type u))
    {a b : F.objC} (qm : F.toCategoryQuotientData.QuotMor a b),
    counitEvalQuot (categoryL F) (embedMorAsVar F qm) =
    ⟨bundleQuotMorL F qm, rfl, rfl⟩

/-- The canonical Cat-Copresheaf adjunction data. -/
def catCopresheafAdjunction : CatCopresheafAdjunctionData.{u} where
  L_obj := LFunctorObj
  Phi_obj := PhiFunctorObj
  unit := unitNatTransComponent
  counit_on_L := fun F => counitFunctorData (categoryL F)
  triangle2_mor_eq := fun C f => triangle2_mor C f
  triangle1_mor_eq := fun F {_} {_} qm => triangle1_mor F qm

/-- Verification: The adjunction data is well-formed and the triangles hold. -/
theorem adjunction_triangles_hold :
    (∀ {Q : OverQuiver.{u, u}} (C : OverCategoryData Q) (f : Q.MorType),
      (counitFunctorData C).morFn
        ((unitNatTrans C.toJudgmentFunctorData).appMor f) = f) ∧
    (∀ (F : CategoryJudgments.FunctorData (Type u))
      {a b : F.objC} (qm : F.toCategoryQuotientData.QuotMor a b),
      counitEvalQuot (categoryL F) (embedMorAsVar F qm) =
      ⟨bundleQuotMorL F qm, rfl, rfl⟩) :=
  ⟨fun C f => catCopresheafAdjunction.triangle2_mor_eq C f,
   fun F {_} {_} qm => catCopresheafAdjunction.triangle1_mor_eq F qm⟩

end AdjunctionStructure

/-! ## Mathlib Category Instance for BundledOverCategoryData

We define a mathlib `Category` instance for `BundledOverCategoryData` using
`OverFunctorData` as morphisms. This allows us to use mathlib's adjunction
machinery.
-/

section MathlibCategoryInstance

/-- Mathlib Category instance for BundledOverCategoryData.
    Morphisms are OverFunctorData between the underlying categories.
    Uses general universe parameters `{v, u}` for flexibility. -/
instance : Category BundledOverCategoryData.{v, u} where
  Hom := fun C D => OverFunctorData C.data D.data
  id := fun C => OverFunctorData.id C.data
  comp := fun F G => F.comp G
  id_comp := fun _ => rfl
  comp_id := fun _ => rfl
  assoc := fun _ _ _ => rfl

end MathlibCategoryInstance

/-! ## Mathlib Functors L and Φ

We define mathlib `Functor` instances for L and Φ using the existing
`toOverFunctorData` and `toJudgmentNatTrans` conversions.
-/

section MathlibFunctors

universe uMF

/-- The L functor from copresheaves to categories, as a mathlib Functor.
    On objects: FunctorData F ↦ bundleOverCategory F.toOverCategoryData
    On morphisms: NatTransData α ↦ α.toOverFunctorData -/
def LFunctor : Functor (CategoryJudgments.FunctorData (Type uMF))
    BundledOverCategoryData.{uMF, uMF} where
  obj := LFunctorObj
  map := fun α => α.toOverFunctorData
  map_id := fun _ => toOverFunctorData_id
  map_comp := fun α β => toOverFunctorData_comp α β

/-- Φ preserves identity: Φ(id_C) = id_{Φ(C)}. -/
theorem toJudgmentNatTrans_id {C : BundledOverCategoryData.{uMF, uMF}} :
    (OverFunctorData.id C.data).toJudgmentNatTrans =
    CategoryJudgments.NatTransData.id C.data.toJudgmentFunctorData := by
  simp only [OverFunctorData.toJudgmentNatTrans, OverFunctorData.id,
    OverQuiverMorphism.id, CategoryJudgments.NatTransData.id]
  rfl

/-- Φ preserves composition: Φ(G ∘ F) = Φ(G) ∘ Φ(F). -/
theorem toJudgmentNatTrans_comp {C D E : BundledOverCategoryData.{uMF, uMF}}
    (F : OverFunctorData C.data D.data) (G : OverFunctorData D.data E.data) :
    (F.comp G).toJudgmentNatTrans =
    F.toJudgmentNatTrans.comp G.toJudgmentNatTrans := by
  simp only [OverFunctorData.toJudgmentNatTrans, OverFunctorData.comp,
    OverQuiverMorphism.comp, CategoryJudgments.NatTransData.comp,
    Function.comp_apply]
  rfl

/-- The Φ functor from categories to copresheaves, as a mathlib Functor.
    On objects: BundledOverCategoryData C ↦ C.data.toJudgmentFunctorData
    On morphisms: OverFunctorData F ↦ F.toJudgmentNatTrans -/
def PhiFunctor : Functor BundledOverCategoryData.{uMF, uMF}
    (CategoryJudgments.FunctorData (Type uMF)) where
  obj := PhiFunctorObj
  map := fun F => F.toJudgmentNatTrans
  map_id := fun _ => toJudgmentNatTrans_id
  map_comp := fun F G => toJudgmentNatTrans_comp F G

end MathlibFunctors

/-! ## Mathlib Natural Transformations for Unit and Counit

We define the unit η : 𝟭 → L ⋙ Φ and counit ε : Φ ⋙ L → 𝟭 as mathlib NatTrans.
-/

section MathlibNatTrans

universe uNT

/-- Helper: the composition Φ ⋙ L equals derivedQuotientData on objects. -/
theorem phiLComp_obj_eq (C : BundledOverCategoryData.{uNT, uNT}) :
    (PhiFunctor ⋙ LFunctor).obj C =
    bundleOverCategory (derivedQuotientData C.data).toOverCategoryData := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Unit naturality: α ≫ η_G = η_F ≫ Φ(L(α)). -/
theorem unitNT_naturality {F G : CategoryJudgments.FunctorData (Type uNT)}
    (α : CategoryJudgments.NatTransData F G) :
    (unitNatTrans F).comp (α.toOverFunctorData.toJudgmentNatTrans) =
    α.comp (unitNatTrans G) := by
  apply CategoryJudgments.NatTransData.ext
  · -- appObj: id ≫ α.appObj = α.appObj ≫ id (both = α.appObj)
    simp only [CategoryJudgments.NatTransData.comp, unitNatTrans, unitAppObj,
      Category.id_comp, Category.comp_id]
    rfl
  · -- appMor: the non-trivial case
    simp only [CategoryJudgments.NatTransData.comp, unitNatTrans, unitAppObj,
      Category.id_comp, Category.comp_id]
    funext f
    -- LHS: (unitAppMor F ≫ α.toQuotQuiverMor.morFn) f
    -- RHS: (α.appMor ≫ unitAppMor G) f
    simp only [CategoryStruct.comp,
      CategoryJudgments.NatTransData.toOverFunctorData,
      OverFunctorData.toJudgmentNatTrans,
      CategoryJudgments.NatTransData.toQuotQuiverMor,
      CategoryJudgments.FunctorData.toCategoryQuotientData,
      CategoryQuotientData.bundleQuotMor,
      CategoryJudgments.NatTransData.toCategoryQuotientMorphism,
      CategoryQuotientMorphism.quotMapMor,
      CategoryQuotientData.quotMor,
      CategoryJudgments.FunctorData.toQuiver]
    -- Need to show nested sigma equality
    -- LHS: ⟨α.appObj (F.dom f), α.appObj (F.cod f), quotMapMor (quotMor (var f))⟩
    -- RHS: ⟨G.dom (α.appMor f), G.cod (α.appMor f), quotMor (var (α.appMor f))⟩
    simp only [Function.comp_apply, unitAppMor, unitComponent]
    -- Use naturality to establish the two index equalities
    have h_dom : α.appObj (F.dom f) = G.dom (α.appMor f) := congrFun α.naturality_dom f
    have h_cod : α.appObj (F.cod f) = G.cod (α.appMor f) := congrFun α.naturality_cod f
    -- The QuotMor equality after transport
    -- LHS quotMapMor result is at type QuotMor (α.appObj (F.dom f)) (α.appObj (F.cod f))
    -- RHS quotMor result is at type QuotMor (G.dom (α.appMor f)) (G.cod (α.appMor f))
    -- These become equal after cast by h_dom, h_cod
    have h_qm : cast (congrArg₂ G.toCategoryQuotientData.QuotMor h_dom h_cod)
        (α.toCategoryQuotientMorphism.quotMapMor
          (F.toCategoryQuotientData.quotMor (FreeMor.var (Q := F.toQuiver) f))) =
        (G.toCategoryQuotientData.quotMor (FreeMor.var (Q := G.toQuiver) (α.appMor f))) := by
      -- First unfold quotMapMor, but keep quotMor for the rewrite to work
      simp only [CategoryQuotientMorphism.quotMapMor]
      -- Now LHS is: cast _ (Quotient.lift ... (quotMor (var f)))
      -- Unfold inner quotMor so lift_mk applies
      simp only [CategoryQuotientData.quotMor, Quotient.lift_mk]
      -- Now: cast _ ⟦mapQuiver (var f)⟧ = ⟦var (α.appMor f)⟧
      simp only [FreeMor.mapQuiver_var]
      -- Now: cast _ ⟦src_comm ▸ tgt_comm ▸ var (α.appMor f)⟧ = ⟦var (α.appMor f)⟧
      -- Convert back to quotMor for the rewrite
      change cast _ (G.toCategoryQuotientData.quotMor _) =
           G.toCategoryQuotientData.quotMor (FreeMor.var (α.appMor f))
      rw [G.toCategoryQuotientData.quotMor_cast h_dom h_cod]
      congr 1
      simp only [CategoryJudgments.NatTransData.toCategoryQuotientMorphism]
      -- Goal: cast _ (h_dom.symm ▸ h_cod.symm ▸ var (α.appMor f)) = var (α.appMor f)
      -- Convert ▸ to cast using subst_subst_eq_cast
      rw [subst_subst_eq_cast h_dom.symm h_cod.symm]
      -- Now: cast _ (cast (congrArg₂ _ h_dom.symm h_cod.symm) (var (α.appMor f)))
      --    = var (α.appMor f)
      simp only [cast_cast, cast_eq]
    -- Build the nested sigma equality using quotMorSigma_heq for inner sigma,
    -- then Sigma.ext for outer sigma
    refine Sigma.ext h_dom ?_
    exact G.toCategoryQuotientData.quotMorSigma_heq h_dom h_cod _ _ h_qm
  · -- appId: unitAppId ≫ α.appObj = α.appId ≫ unitAppId
    simp only [CategoryJudgments.NatTransData.comp, unitNatTrans, unitAppObj,
      Category.id_comp, Category.comp_id]
    funext i
    simp only [CategoryJudgments.NatTransData.toOverFunctorData,
      OverFunctorData.toJudgmentNatTrans,
      CategoryJudgments.NatTransData.toQuotQuiverMor]
    -- Goal: α.appObj (F.idObj i) = G.idObj (α.appId i)
    -- This is the pointwise version of naturality_idObj:
    -- (F.idMor ≫ F.dom) ≫ α.appObj = α.appId ≫ (G.idMor ≫ G.dom)
    have h := congrFun α.naturality_idObj i
    simp only [CategoryStruct.comp, Function.comp_apply] at h
    exact h
  · -- appComp: show that transforming via α commutes with unitAppComp
    simp only [CategoryJudgments.NatTransData.comp, unitNatTrans, unitAppObj,
      Category.id_comp, Category.comp_id]
    funext c
    -- LHS: apply unitAppComp F to c, then transform via α's toQuotQuiverMor
    -- RHS: apply α.appComp to c, then apply unitAppComp G
    -- Use Subtype.ext to reduce to equality of underlying pairs
    apply Subtype.ext
    -- Unfold the composition and unitAppComp to expose the pair structure
    simp only [CategoryStruct.comp, Function.comp_apply]
    -- Now need equality of pairs (f₁, g₁) = (f₂, g₂)
    apply Prod.ext
    · -- First component: right morphism
      -- Unfold unitAppComp on both sides to expose the structure
      simp only [unitAppComp, unitAppMor, unitComponent]
      simp only [CategoryJudgments.NatTransData.toOverFunctorData,
        OverFunctorData.toJudgmentNatTrans,
        CategoryJudgments.NatTransData.toQuotQuiverMor,
        CategoryJudgments.FunctorData.toCategoryQuotientData,
        CategoryQuotientData.bundleQuotMor,
        CategoryJudgments.NatTransData.toCategoryQuotientMorphism,
        CategoryQuotientMorphism.quotMapMor]
      -- Use naturality_right: G.right ∘ α.appComp = α.appMor ∘ F.right
      have h_right : α.appMor (F.right c) = G.right (α.appComp c) :=
        congrFun α.naturality_right c
      -- Object equalities combining naturality_dom/cod with h_right
      have h_dom : α.appObj (F.dom (F.right c)) = G.dom (G.right (α.appComp c)) := by
        have h1 := congrFun α.naturality_dom (F.right c)
        simp only [CategoryStruct.comp, Function.comp_apply] at h1
        rw [h1, h_right]
      have h_cod : α.appObj (F.cod (F.right c)) = G.cod (G.right (α.appComp c)) := by
        have h1 := congrFun α.naturality_cod (F.right c)
        simp only [CategoryStruct.comp, Function.comp_apply] at h1
        rw [h1, h_right]
      -- The QuotMor equality
      -- Use naturality to get equalities in terms of α.appMor (F.right c)
      have h_dom' : α.appObj (F.dom (F.right c)) = G.dom (α.appMor (F.right c)) :=
        congrFun α.naturality_dom (F.right c)
      have h_cod' : α.appObj (F.cod (F.right c)) = G.cod (α.appMor (F.right c)) :=
        congrFun α.naturality_cod (F.right c)
      -- First prove the equality in terms of α.appMor (F.right c)
      have h_qm' : cast (congrArg₂ G.toCategoryQuotientData.QuotMor h_dom' h_cod')
          (α.toCategoryQuotientMorphism.quotMapMor
            (F.toCategoryQuotientData.quotMor
              (FreeMor.var (Q := F.toCategoryQuotientData.quiver) (F.right c)))) =
          (G.toCategoryQuotientData.quotMor
            (FreeMor.var (Q := G.toCategoryQuotientData.quiver) (α.appMor (F.right c)))) := by
        simp only [CategoryQuotientMorphism.quotMapMor]
        simp only [CategoryQuotientData.quotMor, Quotient.lift_mk]
        simp only [FreeMor.mapQuiver_var]
        change cast _ (G.toCategoryQuotientData.quotMor _) =
             G.toCategoryQuotientData.quotMor
               (FreeMor.var (Q := G.toCategoryQuotientData.quiver) (α.appMor (F.right c)))
        rw [G.toCategoryQuotientData.quotMor_cast h_dom' h_cod']
        congr 1
        simp only [CategoryJudgments.NatTransData.toCategoryQuotientMorphism,
          CategoryJudgments.FunctorData.toCategoryQuotientData]
        rw [subst_subst_eq_cast h_dom'.symm h_cod'.symm]
        simp only [cast_cast, cast_eq]
      -- Now convert h_qm' to h_qm using h_right
      have h_qm : cast (congrArg₂ G.toCategoryQuotientData.QuotMor h_dom h_cod)
          (α.toCategoryQuotientMorphism.quotMapMor
            (F.toCategoryQuotientData.quotMor
              (FreeMor.var (Q := F.toCategoryQuotientData.quiver) (F.right c)))) =
          (G.toCategoryQuotientData.quotMor
            (FreeMor.var (Q := G.toCategoryQuotientData.quiver) (G.right (α.appComp c)))) := by
        -- h_dom' uses (α.appMor (F.right c)), h_dom uses (G.right (α.appComp c))
        -- h_right : α.appMor (F.right c) = G.right (α.appComp c), so
        -- G.dom (α.appMor (F.right c)) = G.dom (G.right (α.appComp c))
        have h_dom_rel : G.dom (α.appMor (F.right c)) = G.dom (G.right (α.appComp c)) :=
          congrArg G.dom h_right
        have h_cod_rel : G.cod (α.appMor (F.right c)) = G.cod (G.right (α.appComp c)) :=
          congrArg G.cod h_right
        -- h_dom = h_dom' ▸ h_dom_rel (transitivity via h_dom_rel)
        have h_dom_eq : h_dom = h_dom'.trans h_dom_rel := rfl
        have h_cod_eq : h_cod = h_cod'.trans h_cod_rel := rfl
        -- Since h_dom and h_cod factor through h_dom'/h_cod', the casts are equal
        have h_cast_eq : congrArg₂ G.toCategoryQuotientData.QuotMor h_dom h_cod =
            congrArg₂ G.toCategoryQuotientData.QuotMor (h_dom'.trans h_dom_rel)
              (h_cod'.trans h_cod_rel) := by
          rw [h_dom_eq, h_cod_eq]
        rw [h_cast_eq]
        -- Now need: cast (congrArg₂ _ (h_dom'.trans h_dom_rel) (h_cod'.trans h_cod_rel)) (...) =
        --           quotMor (var (G.right (α.appComp c)))
        -- Use cast transitivity: cast (trans) = cast ∘ cast
        have cast_trans : cast (congrArg₂ G.toCategoryQuotientData.QuotMor
            (h_dom'.trans h_dom_rel) (h_cod'.trans h_cod_rel))
              (α.toCategoryQuotientMorphism.quotMapMor
                (F.toCategoryQuotientData.quotMor
                  (FreeMor.var (Q := F.toCategoryQuotientData.quiver) (F.right c)))) =
            cast (congrArg₂ G.toCategoryQuotientData.QuotMor h_dom_rel h_cod_rel)
              (cast (congrArg₂ G.toCategoryQuotientData.QuotMor h_dom' h_cod')
                (α.toCategoryQuotientMorphism.quotMapMor
                  (F.toCategoryQuotientData.quotMor
                    (FreeMor.var (Q := F.toCategoryQuotientData.quiver) (F.right c))))) := by
          simp only [cast_cast]
        rw [cast_trans, h_qm']
        -- Now: cast (congrArg₂ _ h_dom_rel h_cod_rel)
        --        (quotMor (var (α.appMor (F.right c)))) = quotMor (var (G.right (α.appComp c)))
        rw [G.toCategoryQuotientData.quotMor_cast h_dom_rel h_cod_rel]
        -- Now: quotMor (cast _ (var (α.appMor (F.right c)))) = quotMor (var (G.right ...))
        -- Use congruence on quotMor to get to FreeMor equality
        congr 1
        -- Goal: cast _ (var (α.appMor (F.right c))) = var (G.right (α.appComp c))
        -- Given h_right : α.appMor (F.right c) = G.right (α.appComp c), we transport
        -- Since h_dom_rel = congrArg G.dom h_right and h_cod_rel = congrArg G.cod h_right,
        -- the cast proof from FreeMor.var aligns with h_right
        have var_transport : ∀ (m₁ m₂ : G.morC) (h : m₁ = m₂),
            cast (congrArg₂ (FreeMor G.toQuiver)
              (congrArg G.dom h) (congrArg G.cod h))
              (FreeMor.var (Q := G.toQuiver) m₁) =
            FreeMor.var (Q := G.toQuiver) m₂ := by
          intro m₁ m₂ h
          cases h
          rfl
        -- Now apply, but G.toCategoryQuotientData.quiver = G.toQuiver
        simp only [CategoryJudgments.FunctorData.toCategoryQuotientData]
        exact var_transport _ _ h_right
      refine Sigma.ext h_dom ?_
      exact G.toCategoryQuotientData.quotMorSigma_heq h_dom h_cod _ _ h_qm
    · -- Second component: left morphism (same pattern as right)
      simp only [unitAppComp, unitAppMor, unitComponent]
      simp only [CategoryJudgments.NatTransData.toOverFunctorData,
        OverFunctorData.toJudgmentNatTrans,
        CategoryJudgments.NatTransData.toQuotQuiverMor,
        CategoryJudgments.FunctorData.toCategoryQuotientData,
        CategoryQuotientData.bundleQuotMor,
        CategoryJudgments.NatTransData.toCategoryQuotientMorphism,
        CategoryQuotientMorphism.quotMapMor]
      -- Use naturality_left: G.left ∘ α.appComp = α.appMor ∘ F.left
      have h_left : α.appMor (F.left c) = G.left (α.appComp c) :=
        congrFun α.naturality_left c
      -- Object equalities combining naturality_dom/cod with h_left
      have h_dom : α.appObj (F.dom (F.left c)) = G.dom (G.left (α.appComp c)) := by
        have h1 := congrFun α.naturality_dom (F.left c)
        simp only [CategoryStruct.comp, Function.comp_apply] at h1
        rw [h1, h_left]
      have h_cod : α.appObj (F.cod (F.left c)) = G.cod (G.left (α.appComp c)) := by
        have h1 := congrFun α.naturality_cod (F.left c)
        simp only [CategoryStruct.comp, Function.comp_apply] at h1
        rw [h1, h_left]
      -- The QuotMor equality
      -- Use naturality to get equalities in terms of α.appMor (F.left c)
      have h_dom' : α.appObj (F.dom (F.left c)) = G.dom (α.appMor (F.left c)) :=
        congrFun α.naturality_dom (F.left c)
      have h_cod' : α.appObj (F.cod (F.left c)) = G.cod (α.appMor (F.left c)) :=
        congrFun α.naturality_cod (F.left c)
      -- First prove the equality in terms of α.appMor (F.left c)
      have h_qm' : cast (congrArg₂ G.toCategoryQuotientData.QuotMor h_dom' h_cod')
          (α.toCategoryQuotientMorphism.quotMapMor
            (F.toCategoryQuotientData.quotMor
              (FreeMor.var (Q := F.toCategoryQuotientData.quiver) (F.left c)))) =
          (G.toCategoryQuotientData.quotMor
            (FreeMor.var (Q := G.toCategoryQuotientData.quiver) (α.appMor (F.left c)))) := by
        simp only [CategoryQuotientMorphism.quotMapMor]
        simp only [CategoryQuotientData.quotMor, Quotient.lift_mk]
        simp only [FreeMor.mapQuiver_var]
        change cast _ (G.toCategoryQuotientData.quotMor _) =
             G.toCategoryQuotientData.quotMor
               (FreeMor.var (Q := G.toCategoryQuotientData.quiver) (α.appMor (F.left c)))
        rw [G.toCategoryQuotientData.quotMor_cast h_dom' h_cod']
        congr 1
        simp only [CategoryJudgments.NatTransData.toCategoryQuotientMorphism,
          CategoryJudgments.FunctorData.toCategoryQuotientData]
        rw [subst_subst_eq_cast h_dom'.symm h_cod'.symm]
        simp only [cast_cast, cast_eq]
      -- Now convert h_qm' to h_qm using h_left
      have h_qm : cast (congrArg₂ G.toCategoryQuotientData.QuotMor h_dom h_cod)
          (α.toCategoryQuotientMorphism.quotMapMor
            (F.toCategoryQuotientData.quotMor
              (FreeMor.var (Q := F.toCategoryQuotientData.quiver) (F.left c)))) =
          (G.toCategoryQuotientData.quotMor
            (FreeMor.var (Q := G.toCategoryQuotientData.quiver) (G.left (α.appComp c)))) := by
        have h_dom_rel : G.dom (α.appMor (F.left c)) = G.dom (G.left (α.appComp c)) :=
          congrArg G.dom h_left
        have h_cod_rel : G.cod (α.appMor (F.left c)) = G.cod (G.left (α.appComp c)) :=
          congrArg G.cod h_left
        have h_dom_eq : h_dom = h_dom'.trans h_dom_rel := rfl
        have h_cod_eq : h_cod = h_cod'.trans h_cod_rel := rfl
        have h_cast_eq : congrArg₂ G.toCategoryQuotientData.QuotMor h_dom h_cod =
            congrArg₂ G.toCategoryQuotientData.QuotMor (h_dom'.trans h_dom_rel)
              (h_cod'.trans h_cod_rel) := by
          rw [h_dom_eq, h_cod_eq]
        rw [h_cast_eq]
        have cast_trans : cast (congrArg₂ G.toCategoryQuotientData.QuotMor
            (h_dom'.trans h_dom_rel) (h_cod'.trans h_cod_rel))
              (α.toCategoryQuotientMorphism.quotMapMor
                (F.toCategoryQuotientData.quotMor
                  (FreeMor.var (Q := F.toCategoryQuotientData.quiver) (F.left c)))) =
            cast (congrArg₂ G.toCategoryQuotientData.QuotMor h_dom_rel h_cod_rel)
              (cast (congrArg₂ G.toCategoryQuotientData.QuotMor h_dom' h_cod')
                (α.toCategoryQuotientMorphism.quotMapMor
                  (F.toCategoryQuotientData.quotMor
                    (FreeMor.var (Q := F.toCategoryQuotientData.quiver) (F.left c))))) := by
          simp only [cast_cast]
        rw [cast_trans, h_qm']
        rw [G.toCategoryQuotientData.quotMor_cast h_dom_rel h_cod_rel]
        congr 1
        have var_transport : ∀ (m₁ m₂ : G.morC) (h : m₁ = m₂),
            cast (congrArg₂ (FreeMor G.toQuiver)
              (congrArg G.dom h) (congrArg G.cod h))
              (FreeMor.var (Q := G.toQuiver) m₁) =
            FreeMor.var (Q := G.toQuiver) m₂ := by
          intro m₁ m₂ h
          cases h
          rfl
        simp only [CategoryJudgments.FunctorData.toCategoryQuotientData]
        exact var_transport _ _ h_left
      refine Sigma.ext h_dom ?_
      exact G.toCategoryQuotientData.quotMorSigma_heq h_dom h_cod _ _ h_qm

/-- The unit natural transformation η : 𝟭 → L ⋙ Φ.
    For each copresheaf F, η_F : F → Φ(L(F)) embeds F into its quotient. -/
def unitNT : NatTrans (Functor.id (CategoryJudgments.FunctorData (Type uNT)))
    (LFunctor ⋙ PhiFunctor) where
  app := fun F => unitNatTrans F
  naturality := fun {F G} α => by
    simp only [Functor.comp_map, Functor.id_map, LFunctor, PhiFunctor]
    exact (unitNT_naturality α).symm

/-- Counit naturality: inducedQuotFunctor ≫ ε_D = ε_C ≫ F. -/
theorem counitNT_naturality {C D : BundledOverCategoryData.{uNT, uNT}}
    (F : OverFunctorData C.data D.data) :
    (inducedQuotFunctor F).comp (counitFunctorData D.data) =
    (counitFunctorData C.data).comp F := by
  simp only [OverFunctorData.comp, OverQuiverMorphism.comp]
  ext
  · exact (counitFunctor_natural_obj F _).symm
  · exact (counitFunctor_natural_mor F _).symm

/-- The counit natural transformation ε : Φ ⋙ L → 𝟭.
    For each category C, ε_C : L(Φ(C)) → C evaluates quotient morphisms. -/
def counitNT : NatTrans (PhiFunctor ⋙ LFunctor)
    (Functor.id BundledOverCategoryData.{uNT, uNT}) where
  app := fun C => counitFunctorData C.data
  naturality := fun {C D} F => by
    simp only [Functor.comp_map, Functor.id_map, PhiFunctor, LFunctor]
    exact counitNT_naturality F

end MathlibNatTrans

/-! ## Mathlib Adjunction L ⊣ Φ

We construct the full mathlib Adjunction using the unit and counit natural
transformations together with the triangle identities.
-/

section MathlibAdjunction

open CategoryTheory

universe uAdj

/-- The core unit-counit data for the adjunction L ⊣ Φ.
    The triangle identities are proven using the existing component-wise proofs. -/
def adjunctionCoreUnitCounit :
    Adjunction.CoreUnitCounit LFunctor.{uAdj} PhiFunctor.{uAdj} where
  unit := unitNT
  counit := counitNT
  left_triangle := by
    ext F
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.associator_hom_app,
      Functor.whiskerLeft_app, Functor.comp_obj, Functor.id_obj]
    simp only [LFunctor, PhiFunctor, unitNT, counitNT]
    simp only [Category.id_comp]
    -- Goal: L(η_F) ≫ ε_{L(F)} = 𝟙_{L(F)}
    -- Use OverFunctorData extensionality explicitly
    apply OverFunctorData.ext
    · -- objFn: both map objects to themselves
      funext a
      exact triangle1_obj F a
    · -- morFn: L(η_F) embeds then ε evaluates back to original
      funext ⟨a, b, qm⟩
      -- First unfold the categorical composition and identity
      simp only [NatTrans.id_app', CategoryStruct.id, CategoryStruct.comp]
      simp only [OverFunctorData.comp, OverQuiverMorphism.comp, Function.comp_apply,
        OverFunctorData.id, OverQuiverMorphism.id, id]
      -- Unfold the unit and counit structures
      simp only [unitNatTrans, counitFunctorData, counitQuiverMor,
        CategoryJudgments.NatTransData.toOverFunctorData,
        CategoryJudgments.NatTransData.toQuotQuiverMor,
        CategoryJudgments.NatTransData.toCategoryQuotientMorphism,
        CategoryQuotientMorphism.quotMapMor, CategoryQuotientData.quotMor,
        CategoryJudgments.FunctorData.toCategoryQuotientData,
        CategoryJudgments.FunctorData.toQuiver,
        CategoryQuotientData.bundleQuotMor, LFunctorObj, bundleOverCategory]
      -- Induct on the quotient representative
      induction qm using Quotient.inductionOn with
      | h fm =>
        erw [Quotient.lift_mk]
        simp only [counitEvalQuot, counitEval]
        erw [Quotient.lift_mk]
        -- Now show counitEvalAux (mapQuiver fm) = bundle ⟦fm⟧
        induction fm with
        | var f =>
          simp only [FreeMor.mapQuiver, counitEvalAux, unitAppMor, unitComponent,
            CategoryJudgments.FunctorData.toCategoryQuotientData,
            CategoryJudgments.FunctorData.toQuiver,
            CategoryQuotientData.quotMor]
        | id x =>
          simp only [FreeMor.mapQuiver, counitEvalAux, unitAppObj,
            CategoryJudgments.FunctorData.toCategoryQuotientData,
            CategoryJudgments.FunctorData.toOverCategoryData,
            CategoryQuotientData.toOverCategoryData,
            CategoryQuotientData.quotCategoryOps,
            CategoryTheory.CategoryStruct.id]
          rfl
        | comp g f ihg ihf =>
          -- The comp case: use congrArg to rewrite the match results
          simp only [FreeMor.mapQuiver, counitEvalAux,
            CategoryJudgments.FunctorData.toCategoryQuotientData,
            CategoryJudgments.FunctorData.toOverCategoryData,
            CategoryQuotientData.toOverCategoryData,
            CategoryQuotientData.quotCategoryOps,
            CategoryQuotientData.quotCompFn,
            CategoryQuotientData.quotComp] at ihf ihg ⊢
          -- Try aesop for automated reasoning
          aesop
  right_triangle := by
    ext C
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.associator_inv_app,
      Functor.whiskerRight_app, Functor.comp_obj, Functor.id_obj]
    simp only [LFunctor, PhiFunctor, unitNT, counitNT]
    simp only [Category.id_comp]
    -- Goal: η_{Φ(C)} ≫ Φ(ε_C) = 𝟙_{Φ(C)}
    -- Use NatTransData extensionality
    apply CategoryJudgments.NatTransData.ext
    · -- appObj: both are identity on objects
      simp only [CategoryJudgments.NatTransData.comp, unitNatTrans, unitAppObj,
        OverFunctorData.toJudgmentNatTrans, counitFunctorData, counitQuiverMor,
        CategoryStruct.comp]
      rfl
    · -- appMor: use second triangle identity
      simp only [CategoryJudgments.NatTransData.comp, unitNatTrans,
        OverFunctorData.toJudgmentNatTrans, counitFunctorData,
        CategoryStruct.comp]
      funext f
      exact triangle2_mor C.data f
    · -- appId: use second triangle identity
      simp only [CategoryJudgments.NatTransData.comp, unitNatTrans,
        OverFunctorData.toJudgmentNatTrans, counitFunctorData,
        CategoryStruct.comp]
      funext i
      exact triangle2_id C.data i
    · -- appComp: use second triangle identity
      simp only [CategoryJudgments.NatTransData.comp, unitNatTrans,
        OverFunctorData.toJudgmentNatTrans, counitFunctorData,
        CategoryStruct.comp]
      funext c
      exact triangle2_comp C.data c

/-- The mathlib adjunction L ⊣ Φ between copresheaves and categories.
    This is the full adjunction constructed from the unit-counit data. -/
def catCopresheafMathlibAdjunction :
    LFunctor.{uAdj} ⊣ PhiFunctor.{uAdj} :=
  Adjunction.mkOfUnitCounit adjunctionCoreUnitCounit

end MathlibAdjunction

/-! ## Extended Adjunction with Mathlib Copresheaf Category

We extend the adjunction `catCopresheafMathlibAdjunction` by composing with
the categorical equivalence `functorDataEquivCat` on the right side. This
gives an adjunction where the copresheaf side uses mathlib's standard functor
category `(CategoryJudgments.Obj ⥤ Type u)` instead of our internal
`FunctorData (Type u)`.
-/

section ExtendedAdjunction

universe uExt

/-- The equivalence between our FunctorData and the mathlib functor category,
    specialized to Type. -/
abbrev copresheafEquiv :
    CategoryJudgments.FunctorData (Type uExt) ≌
    (CategoryJudgments.Obj ⥤ Type uExt) :=
  CategoryJudgments.functorDataEquivCat

/-- The adjunction from the equivalence:
    functorDataToFunctor ⊣ functorToFunctorData.
    This is the "forward" direction E.toAdjunction. -/
def copresheafEquivAdjunction :
    CategoryJudgments.functorDataToFunctor (C := Type uExt) ⊣
    CategoryJudgments.functorToFunctorData :=
  copresheafEquiv.toAdjunction

/-- The reversed equivalence gives the adjunction in the other direction:
    functorToFunctorData ⊣ functorDataToFunctor. -/
def copresheafEquivSymmAdjunction :
    CategoryJudgments.functorToFunctorData ⊣
    CategoryJudgments.functorDataToFunctor (C := Type uExt) :=
  copresheafEquiv.symm.toAdjunction

/-- The extended L functor: from mathlib copresheaves to categories.
    L' = functorToFunctorData ⋙ LFunctor :
    (Obj ⥤ Type u) ⥤ BundledOverCategoryData -/
def LFunctorExt :
    (CategoryJudgments.Obj ⥤ Type uExt) ⥤ BundledOverCategoryData.{uExt, uExt} :=
  CategoryJudgments.functorToFunctorData ⋙ LFunctor

/-- The extended Φ functor: from categories to mathlib copresheaves.
    Φ' = PhiFunctor ⋙ functorDataToFunctor :
    BundledOverCategoryData ⥤ (Obj ⥤ Type u) -/
def PhiFunctorExt :
    BundledOverCategoryData.{uExt, uExt} ⥤ (CategoryJudgments.Obj ⥤ Type uExt) :=
  PhiFunctor ⋙ CategoryJudgments.functorDataToFunctor

/-- The extended adjunction L' ⊣ Φ' where the copresheaf side uses mathlib's
    functor category.

    This is constructed by composing:
    - copresheafEquivSymmAdjunction : functorToFunctorData ⊣ functorDataToFunctor
    - catCopresheafMathlibAdjunction : LFunctor ⊣ PhiFunctor

    Using Adjunction.comp, we get:
    (functorToFunctorData ⋙ LFunctor) ⊣ (PhiFunctor ⋙ functorDataToFunctor) -/
def catCopresheafExtAdjunction :
    LFunctorExt.{uExt} ⊣ PhiFunctorExt.{uExt} :=
  copresheafEquivSymmAdjunction.comp catCopresheafMathlibAdjunction

end ExtendedAdjunction

/-! ## Left-Side Extension: BundledOverCategoryData to Cat

We extend the adjunction on the left side by composing with an equivalence
between `BundledOverCategoryData` and mathlib's `Cat`. This is done by:
1. Building a functor `BundledOverCategoryData ⥤ Cat` via `BundledCategoryData`
2. Building the inverse functor `Cat ⥤ BundledOverCategoryData`
3. Proving they form an equivalence
4. Composing with the adjunction from ExtendedAdjunction
-/

section LeftSideExtension

open BundledCategoryData (toCatObj ofCatObj functorToCat functorFromCat equivCat)

/-- The functor from BundledOverCategoryData to BundledCategoryData. -/
def overToBundledCatFunctor :
    BundledOverCategoryData.{u, u} ⥤ BundledCategoryData.{u, u} where
  obj := fun C => C.toBundledCategoryData
  map := toBundledCategoryData_map
  map_id := toBundledCategoryData_map_id
  map_comp := fun F G => toBundledCategoryData_map_comp F G

/-- The functor from BundledCategoryData to BundledOverCategoryData. -/
def bundledCatToOverFunctor :
    BundledCategoryData.{u, u} ⥤ BundledOverCategoryData.{u, u} where
  obj := fun C => C.toBundledOverCategoryData
  map := toBundledOverCategoryData_map
  map_id := toBundledOverCategoryData_map_id
  map_comp := fun F G => toBundledOverCategoryData_map_comp F G

/-! ### Building the equivalence BundledOverCategoryData ≌ BundledCategoryData

The round-trips `Over → BundledCat → Over` and `BundledCat → Over → BundledCat`
are NOT definitionally the identity due to the different morphism type encodings
(sigma types vs fiber types). However, they are naturally isomorphic to identity
via the equivalences `OverQuiver.sigma_equiv` and `HomSet.fiber_equiv`. -/

/-- The unit isomorphism component: an OverFunctorData from C to the round-trip
    C.toBundledCategoryData.toBundledOverCategoryData.
    Uses the sigma equivalence to map morphisms. -/
def overBundledCatUnit_app (C : BundledOverCategoryData.{u, u}) :
    C ⟶ (overToBundledCatFunctor ⋙ bundledCatToOverFunctor).obj C where
  toOverQuiverMorphism := {
    objFn := id
    morFn := fun f => C.quiver.sigma_equiv.toFun f
    src_comm := fun f => by
      simp only [Functor.comp_obj, overToBundledCatFunctor, bundledCatToOverFunctor,
        BundledOverCategoryData.toBundledCategoryData,
        BundledCategoryData.toBundledOverCategoryData,
        OverQuiver.sigma_equiv, HomSet.toOverQuiver, id_eq]
    tgt_comm := fun f => by
      simp only [Functor.comp_obj, overToBundledCatFunctor, bundledCatToOverFunctor,
        BundledOverCategoryData.toBundledCategoryData,
        BundledCategoryData.toBundledOverCategoryData,
        OverQuiver.sigma_equiv, HomSet.toOverQuiver, id_eq]
  }
  map_id := fun a => by
    simp only [Functor.comp_obj, overToBundledCatFunctor, bundledCatToOverFunctor,
      BundledOverCategoryData.toBundledCategoryData,
      BundledCategoryData.toBundledOverCategoryData,
      HomSet.toOverQuiver, CategoryData.toOverCategoryData, id_eq,
      OverCategoryData.toCategoryOps, CategoryData.toOverCategoryOps,
      OverCategoryData.toCategoryData]
    exact OverQuiver.sigma_equiv_id C.data a
  map_comp := fun p => by
    simp only [Functor.comp_obj, overToBundledCatFunctor, bundledCatToOverFunctor,
      BundledOverCategoryData.toBundledCategoryData,
      BundledCategoryData.toBundledOverCategoryData,
      HomSet.toOverQuiver, CategoryData.toOverCategoryOps,
      OverCategoryData.toCategoryData, CategoryData.toOverCategoryData,
      OverQuiver.sigma_equiv, OverCategoryData.toCategoryOps,
      OverCategoryData.extractComp]
    -- Both sides have compFn applied to pairs with the same underlying morphisms
    obtain ⟨⟨f, g⟩, hcomp⟩ := p
    simp only [Subtype.coe_mk]
    -- The transported g value equals g
    have hg_val : (hcomp.symm ▸ (⟨g, rfl, rfl⟩ :
        C.quiver.toHomSet (C.quiver.src g) (C.quiver.tgt g)) :
        C.quiver.toHomSet (C.quiver.tgt f) (C.quiver.tgt g)).val = g :=
      HomSet.val_eqRec hcomp.symm ⟨g, rfl, rfl⟩
    -- Use simp_all to apply the rewrite so both sides use the same compFn
    simp_all only
    -- Now use sigma_homset_eq with the composition (same morphism on both sides)
    apply OverQuiver.sigma_homset_eq
    · exact rfl -- src proof on LHS
    · exact C.data.comp_src ⟨(f, g), hcomp⟩ -- LHS a₁ = RHS a₂
    · exact rfl -- tgt proof on LHS
    · exact C.data.comp_tgt ⟨(f, g), hcomp⟩ -- LHS b₁ = RHS b₂

/-- The inverse of the unit: an OverFunctorData from the round-trip back to C.
    Uses the inverse of the sigma equivalence. -/
def overBundledCatUnit_inv (C : BundledOverCategoryData.{u, u}) :
    (overToBundledCatFunctor ⋙ bundledCatToOverFunctor).obj C ⟶ C where
  toOverQuiverMorphism := {
    objFn := id
    morFn := fun f => C.quiver.sigma_equiv.invFun f
    src_comm := fun f => by
      simp only [Functor.comp_obj, overToBundledCatFunctor, bundledCatToOverFunctor,
        BundledOverCategoryData.toBundledCategoryData,
        BundledCategoryData.toBundledOverCategoryData,
        OverQuiver.sigma_equiv, HomSet.toOverQuiver, id_eq]
      obtain ⟨a, b, ⟨g, ha, hb⟩⟩ := f
      exact ha
    tgt_comm := fun f => by
      simp only [Functor.comp_obj, overToBundledCatFunctor, bundledCatToOverFunctor,
        BundledOverCategoryData.toBundledCategoryData,
        BundledCategoryData.toBundledOverCategoryData,
        OverQuiver.sigma_equiv, HomSet.toOverQuiver, id_eq]
      obtain ⟨a, b, ⟨g, ha, hb⟩⟩ := f
      exact hb
  }
  map_id := fun a => by
    simp only [Functor.comp_obj, overToBundledCatFunctor, bundledCatToOverFunctor,
      BundledOverCategoryData.toBundledCategoryData,
      BundledCategoryData.toBundledOverCategoryData,
      OverQuiver.sigma_equiv, HomSet.toOverQuiver,
      CategoryData.toOverCategoryOps,
      OverCategoryData.toCategoryData, CategoryData.toOverCategoryData]
    rfl
  map_comp := fun p => by
    simp only [Functor.comp_obj, overToBundledCatFunctor, bundledCatToOverFunctor,
      BundledOverCategoryData.toBundledCategoryData,
      BundledCategoryData.toBundledOverCategoryData,
      OverQuiver.sigma_equiv, HomSet.toOverQuiver,
      OverCategoryData.toCategoryData, CategoryData.toOverCategoryData,
      OverCategoryData.toCategoryOps, OverCategoryData.extractComp]
    obtain ⟨⟨f, g⟩, hcomp⟩ := p
    -- Decompose f and g to access their components
    obtain ⟨a_f, b_f, ⟨m_f, ha_f, hb_f⟩⟩ := f
    obtain ⟨a_g, b_g, ⟨m_g, ha_g, hb_g⟩⟩ := g
    -- hcomp gives b_f = a_g (composability: target of f = source of g)
    -- Substitute to eliminate the transport
    cases hcomp
    -- Now both sides are definitionally equal
    rfl

/-- The unit isomorphism for the Over ≌ BundledCat equivalence. -/
def overBundledCatUnitIso :
    𝟭 BundledOverCategoryData.{u, u} ≅
      overToBundledCatFunctor ⋙ bundledCatToOverFunctor where
  hom := { app := overBundledCatUnit_app
           naturality := fun C D F => by
             apply OverFunctorData.ext
             · rfl
             · funext f
               -- Both sides compute to ⟨F.objFn (src f), F.objFn (tgt f), F.morFn f⟩
               -- LHS = sigma_embed(F.morFn f) = ⟨D.src(F.morFn f), D.tgt(F.morFn f), F.morFn f⟩
               --     = ⟨F.objFn(C.src f), F.objFn(C.tgt f), F.morFn f⟩ by src_comm/tgt_comm
               -- RHS = F_roundtrip(sigma_embed f) = F_roundtrip⟨C.src f, C.tgt f, f⟩
               --     = ⟨F.objFn(C.src f), F.objFn(C.tgt f), F.morFn f⟩
               simp only [CategoryStruct.comp, OverFunctorData.comp,
                 OverQuiverMorphism.comp, overBundledCatUnit_app,
                 OverQuiver.sigma_equiv, Function.comp_apply]
               -- Use sigma_homset_eq to equate the nested sigma types
               apply OverQuiver.sigma_homset_eq
               · rfl
               · exact F.toOverQuiverMorphism.src_comm f
               · rfl
               · exact F.toOverQuiverMorphism.tgt_comm f }
  inv := { app := overBundledCatUnit_inv
           naturality := fun C D F => by
             apply OverFunctorData.ext
             · rfl
             · funext f
               simp only [CategoryStruct.comp, OverFunctorData.comp,
                 OverQuiverMorphism.comp, overBundledCatUnit_inv,
                 OverQuiver.sigma_equiv, Function.comp_apply,
                 Equiv.invFun_as_coe]
               -- Destructure f to access its components
               obtain ⟨a, b, ⟨g, ha, hb⟩⟩ := f
               rfl }
  hom_inv_id := by
    ext C : 2
    simp only [NatTrans.comp_app, NatTrans.id_app, Functor.id_obj]
    apply OverFunctorData.ext
    · rfl
    · funext f
      simp only [CategoryStruct.comp, CategoryStruct.id, overBundledCatUnit_app,
        overBundledCatUnit_inv, OverFunctorData.comp, OverQuiverMorphism.comp,
        OverFunctorData.id, OverQuiverMorphism.id, OverQuiver.sigma_equiv,
        Function.comp_apply, Equiv.invFun_as_coe, Equiv.toFun_as_coe,
        Equiv.symm_apply_apply, id_eq]
  inv_hom_id := by
    ext C : 2
    simp only [NatTrans.comp_app, NatTrans.id_app, Functor.comp_obj]
    apply OverFunctorData.ext
    · rfl
    · funext f
      simp only [CategoryStruct.comp, CategoryStruct.id, overBundledCatUnit_app,
        overBundledCatUnit_inv, OverFunctorData.comp, OverQuiverMorphism.comp,
        OverFunctorData.id, OverQuiverMorphism.id, OverQuiver.sigma_equiv,
        Function.comp_apply, Equiv.invFun_as_coe, Equiv.toFun_as_coe,
        Equiv.apply_symm_apply, id_eq]

/-- The counit isomorphism component: a FunctorData from the round-trip
    C.toBundledOverCategoryData.toBundledCategoryData back to C.
    Uses the fiber equivalence to map morphisms. -/
def overBundledCatCounit_app (C : BundledCategoryData.{u, u}) :
    (bundledCatToOverFunctor ⋙ overToBundledCatFunctor).obj C ⟶ C where
  toFunctorOps := {
    obj := id
    map := fun f => C.roundtripEquiv _ _ f
  }
  laws := {
    map_id := fun a => by
      simp only [Functor.comp_obj, bundledCatToOverFunctor, overToBundledCatFunctor,
        BundledCategoryData.toBundledOverCategoryData,
        BundledOverCategoryData.toBundledCategoryData,
        BundledCategoryData.roundtripEquiv,
        OverCategoryData.toCategoryData, OverCategoryData.toCategoryOps]
      exact HomSet.fiber_equiv_extractId C.data a
    map_comp := fun f g => by
      simp only [Functor.comp_obj, bundledCatToOverFunctor, overToBundledCatFunctor,
        BundledCategoryData.toBundledOverCategoryData,
        BundledOverCategoryData.toBundledCategoryData,
        BundledCategoryData.roundtripEquiv,
        OverCategoryData.toCategoryData, OverCategoryData.toCategoryOps]
      rcases f with ⟨⟨a_f, b_f, m_f⟩, haf, hbf⟩
      rcases g with ⟨⟨a_g, b_g, m_g⟩, hag, hbg⟩
      cases haf
      cases hbf
      cases hag
      cases hbg
      exact HomSet.fiber_equiv_extractComp C.data m_f m_g
  }

/-- The inverse of the counit: a FunctorData from C to the round-trip. -/
def overBundledCatCounit_inv (C : BundledCategoryData.{u, u}) :
    C ⟶ (bundledCatToOverFunctor ⋙ overToBundledCatFunctor).obj C where
  toFunctorOps := {
    obj := id
    map := fun f => (C.roundtripEquiv _ _).symm f
  }
  laws := {
    map_id := fun a => by
      simp only [Functor.comp_obj, bundledCatToOverFunctor, overToBundledCatFunctor,
        BundledCategoryData.toBundledOverCategoryData,
        BundledOverCategoryData.toBundledCategoryData,
        BundledCategoryData.roundtripEquiv, HomSet.fiber_equiv,
        OverCategoryData.toCategoryData, CategoryData.toOverCategoryData,
        CategoryData.toOverCategoryOps]
      rfl
    map_comp := fun f g => by
      simp only [Functor.comp_obj, bundledCatToOverFunctor, overToBundledCatFunctor,
        BundledCategoryData.toBundledOverCategoryData,
        BundledOverCategoryData.toBundledCategoryData,
        BundledCategoryData.roundtripEquiv, HomSet.fiber_equiv,
        OverCategoryData.toCategoryData, CategoryData.toOverCategoryData,
        CategoryData.toOverCategoryOps]
      rfl
  }

set_option backward.isDefEq.respectTransparency false in
/-- The counit isomorphism for the Over ≌ BundledCat equivalence. -/
def overBundledCatCounitIso :
    bundledCatToOverFunctor ⋙ overToBundledCatFunctor ≅
      𝟭 BundledCategoryData.{u, u} where
  hom := { app := overBundledCatCounit_app
           naturality := fun C D F => by
             apply FunctorData.ext'
             apply FunctorOps.ext_map
             intro a b f
             rcases f with ⟨⟨a', b', m⟩, ⟨ha, hb⟩⟩
             subst ha hb
             dsimp only [Functor.comp_map, bundledCatToOverFunctor,
               overToBundledCatFunctor]
             simp only [Function.comp_apply, overBundledCatCounit_app,
               BundledCategoryData.toBundledOverCategoryData,
               BundledOverCategoryData.toBundledCategoryData,
               toBundledCategoryData_toBundledOverCategoryData_map,
               BundledCategoryData.roundtripEquiv, Functor.id_map, id_eq,
               HomSet.toOverQuiver_src, HomSet.toOverQuiver_tgt,
               FunctorData.roundtrip_obj_eq, FunctorData.roundtrip_map_fiber_equiv] }
  inv := { app := overBundledCatCounit_inv
           naturality := fun C D F => by
             apply FunctorData.ext'
             apply FunctorOps.ext_map
             intro a b f
             dsimp only [Functor.comp_map, bundledCatToOverFunctor,
               overToBundledCatFunctor]
             simp only [Function.comp_apply, overBundledCatCounit_inv,
               BundledCategoryData.toBundledOverCategoryData,
               BundledOverCategoryData.toBundledCategoryData,
               toBundledCategoryData_toBundledOverCategoryData_map,
               BundledCategoryData.roundtripEquiv, Functor.id_map, id_eq,
               FunctorData.roundtrip_obj_eq,
               FunctorData.roundtrip_map_fiber_equiv_symm]
             rfl }
  hom_inv_id := by
    ext C : 2
    simp only [NatTrans.comp_app, NatTrans.id_app, Functor.comp_obj]
    apply FunctorData.ext'
    apply FunctorOps.ext_map
    intro a b f
    rcases f with ⟨⟨a', b', m⟩, ⟨ha, hb⟩⟩
    subst ha hb
    simp only [Function.comp_apply, overBundledCatCounit_app, overBundledCatCounit_inv,
      BundledCategoryData.roundtripEquiv, id_eq, Equiv.symm_apply_apply]
  inv_hom_id := by
    ext C : 2
    simp only [NatTrans.comp_app, NatTrans.id_app, Functor.id_obj]
    apply FunctorData.ext'
    apply FunctorOps.ext_map
    intro a b f
    simp only [Function.comp_apply, overBundledCatCounit_app, overBundledCatCounit_inv,
      BundledCategoryData.roundtripEquiv, id_eq, Equiv.apply_symm_apply]

set_option backward.isDefEq.respectTransparency false in
/-- The triangle identity for the equivalence: composing the unit with the
    counit gives the identity on the functor side. -/
theorem overBundledCat_functor_unitIso_comp (X : BundledOverCategoryData.{u, u}) :
    overToBundledCatFunctor.map (overBundledCatUnitIso.hom.app X) ≫
        overBundledCatCounitIso.hom.app (overToBundledCatFunctor.obj X) =
      𝟙 (overToBundledCatFunctor.obj X) := by
  apply FunctorData.ext'
  apply FunctorOps.ext_map
  intro a b f
  rcases f with ⟨m, ⟨ha, hb⟩⟩
  cases ha
  cases hb
  apply Subtype.ext
  simp only [Functor.id_obj, Function.comp_apply, overToBundledCatFunctor,
    overBundledCatUnitIso, overBundledCatCounitIso, overBundledCatCounit_app,
    overBundledCatUnit_app, BundledOverCategoryData.toBundledCategoryData,
    OverFunctorData.toFunctorData, OverFunctorData.toFunctorOps,
    OverFunctorData.extractMap, OverFunctorData.extractObj,
    BundledCategoryData.toBundledOverCategoryData, BundledCategoryData.roundtripEquiv,
    toBundledCategoryData_map, Equiv.toFun_as_coe, id_eq]
  convert OverQuiver.fiber_equiv_sigma_equiv_val X.quiver m

/-- The equivalence between BundledOverCategoryData and BundledCategoryData.
    This uses the sigma and fiber equivalences to build the natural isomorphisms
    for the unit and counit. -/
def overBundledCatEquiv :
    BundledOverCategoryData.{u, u} ≌ BundledCategoryData.{u, u} where
  functor := overToBundledCatFunctor
  inverse := bundledCatToOverFunctor
  unitIso := overBundledCatUnitIso
  counitIso := overBundledCatCounitIso
  functor_unitIso_comp := overBundledCat_functor_unitIso_comp

/-- The equivalence between BundledOverCategoryData and Cat.
    This is the composition of overBundledCatEquiv and equivCat. -/
def overCatEquiv :
    BundledOverCategoryData.{u, u} ≌ Cat.{u, u} :=
  overBundledCatEquiv.trans equivCat

/-- The functor from BundledOverCategoryData to Cat (from the equivalence). -/
def overToCatFunctor :
    BundledOverCategoryData.{u, u} ⥤ Cat.{u, u} :=
  overCatEquiv.functor

/-- The functor from Cat to BundledOverCategoryData (from the equivalence). -/
def catToOverFunctor :
    Cat.{u, u} ⥤ BundledOverCategoryData.{u, u} :=
  overCatEquiv.inverse

/-- The adjunction overToCatFunctor ⊣ catToOverFunctor, derived from the
    equivalence overCatEquiv. -/
def overCatAdjunction :
    overToCatFunctor ⊣ catToOverFunctor :=
  overCatEquiv.toAdjunction

/-- The fully extended L functor: from mathlib copresheaves to Cat.
    L'' = LFunctorExt ⋙ overToCatFunctor :
    (Obj ⥤ Type u) ⥤ Cat -/
def LFunctorFull :
    (CategoryJudgments.Obj ⥤ Type u) ⥤ Cat.{u, u} :=
  LFunctorExt ⋙ overToCatFunctor

/-- The fully extended Φ functor: from Cat to mathlib copresheaves.
    Φ'' = catToOverFunctor ⋙ PhiFunctorExt :
    Cat ⥤ (Obj ⥤ Type u) -/
def PhiFunctorFull :
    Cat.{u, u} ⥤ (CategoryJudgments.Obj ⥤ Type u) :=
  catToOverFunctor ⋙ PhiFunctorExt

/-- The fully extended adjunction L'' ⊣ Φ'' where:
    - The copresheaf side uses mathlib's functor category (Obj ⥤ Type u)
    - The category side uses mathlib's Cat

    This is constructed by composing:
    - catCopresheafExtAdjunction : LFunctorExt ⊣ PhiFunctorExt
    - overCatAdjunction : overToCatFunctor ⊣ catToOverFunctor

    Using Adjunction.comp, we get:
    (LFunctorExt ⋙ overToCatFunctor) ⊣ (catToOverFunctor ⋙ PhiFunctorExt) -/
def catCopresheafFullAdjunction :
    LFunctorFull ⊣ PhiFunctorFull :=
  catCopresheafExtAdjunction.comp overCatAdjunction

end LeftSideExtension

/-! ## Reflectivity of the Adjunction

We prove that the adjunction L ⊣ Φ is reflective by showing that the counit
is a natural isomorphism. This follows from the `roundtripEquiv` which
establishes that the counit component at each category C is a bijection
on morphisms.

A reflective adjunction means the right adjoint Φ is fully faithful.
Mathlib provides `fullyFaithfulROfIsIsoCounit` which derives full faithfulness
from the counit being an isomorphism.
-/

section Reflectivity

universe uRefl

variable {Q : OverQuiver.{uRefl, uRefl}} (C : OverCategoryData Q)

/-- The inverse of the counit quiver morphism: embed each morphism of C as
    a variable in the quotient category L(Φ(C)). -/
def counitQuiverMor_inv : OverQuiverMorphism Q (derivedQuotientData C).quotQuiver where
  objFn := id
  morFn := fun f => ⟨Q.src f, Q.tgt f, (derivedQuotientData C).quotMor (.var f)⟩
  src_comm := fun _ => rfl
  tgt_comm := fun _ => rfl

set_option backward.isDefEq.respectTransparency false in
/-- The inverse of the counit preserves identity. -/
theorem counitInv_map_id (a : Q.Obj) :
    (counitQuiverMor_inv C).morFn (C.idFn a) =
    (derivedQuotientData C).toOverCategoryData.idFn ((counitQuiverMor_inv C).objFn a) := by
  simp only [counitQuiverMor_inv, CategoryQuotientData.toOverCategoryData,
    CategoryQuotientData.quotCategoryOps, CategoryQuotientData.quotIdFn, id]
  -- Goal: ⟨src(idFn a), tgt(idFn a), [var(idFn a)]⟩ = ⟨a, a, [id a]⟩
  let D := derivedQuotientData C
  have idObj_eq : D.idObj a = a := derivedQuotientData_idObj C a
  have h_id_witness := CategoryQuotientData.FreeMorEquivGen.id_witness (D := D) a
  have h_equiv : D.FreeMorEquivGen
      (cast (congrArg₂ (FreeMor Q) (C.id_src a) (C.id_tgt a)) (FreeMor.var (C.idFn a)))
      (FreeMor.id a) := by
    convert h_id_witness using 2 <;> simp only [idObj_eq]
  refine Sigma.ext (C.id_src a) ?_
  apply D.quotMorSigma_heq (C.id_src a) (C.id_tgt a)
  rw [D.quotMor_cast (C.id_src a) (C.id_tgt a)]
  simp only [CategoryQuotientData.quotMor, CategoryQuotientData.quotId]
  exact Quotient.sound (CategoryQuotientData.FreeMorEquiv.rel h_equiv)

set_option backward.isDefEq.respectTransparency false in
/-- The inverse of the counit preserves composition. -/
theorem counitInv_map_comp (p : Q.ComposablePairsType) :
    (counitQuiverMor_inv C).morFn (C.compFn p) =
    (derivedQuotientData C).toOverCategoryData.compFn
      ⟨((counitQuiverMor_inv C).morFn p.val.1, (counitQuiverMor_inv C).morFn p.val.2),
        by simp only [counitQuiverMor_inv, CategoryQuotientData.quotQuiver]; exact p.property⟩ := by
  rcases p with ⟨⟨f, g⟩, h_comp⟩
  simp only [counitQuiverMor_inv, CategoryQuotientData.toOverCategoryData,
    CategoryQuotientData.quotCategoryOps, CategoryQuotientData.quotCompFn,
    CategoryQuotientData.quotComp, CategoryQuotientData.quotQuiver]
  let D := derivedQuotientData C
  have h_wit := CategoryQuotientData.FreeMorEquivGen.comp_witness (D := D) ⟨(f, g), h_comp⟩
  refine Sigma.ext (C.comp_src ⟨(f, g), h_comp⟩) ?_
  apply D.quotMorSigma_heq (C.comp_src ⟨(f, g), h_comp⟩) (C.comp_tgt ⟨(f, g), h_comp⟩)
  rw [D.quotMor_cast (C.comp_src ⟨(f, g), h_comp⟩) (C.comp_tgt ⟨(f, g), h_comp⟩)]
  simp only [CategoryQuotientData.quotMor]
  -- Transport lemma: h ▸ ⟦f⟧ = ⟦h ▸ f⟧
  have h_transport_eq : ∀ {a b b' : D.quiver.Obj} (h : b = b') (fm : FreeMor D.quiver a b),
      (h ▸ (⟦fm⟧ : Quotient (D.freeMorSetoid a b))) =
      (⟦h ▸ fm⟧ : Quotient (D.freeMorSetoid a b')) := by
    intro a b b' h fm
    cases h
    rfl
  conv_rhs => arg 4; rw [h_transport_eq]
  rw [Quotient.lift₂_mk]
  apply Quotient.sound
  apply CategoryQuotientData.FreeMorEquiv.symm
  -- Move transport from right operand to left operand
  have h_comp_move : ∀ {Q' : OverQuiver} {a b b' c : Q'.Obj} (h : b = b')
      (gm : FreeMor Q' b' c) (fm : FreeMor Q' a b),
      gm.comp (h ▸ fm) = (cast (congrArg₂ (FreeMor Q') h.symm rfl) gm).comp fm := by
    intro Q' a b b' c h gm fm
    cases h
    rfl
  rw [h_comp_move]
  convert CategoryQuotientData.FreeMorEquiv.rel h_wit

/-- The inverse of the counit functor data. -/
def counitFunctorData_inv :
    OverFunctorData C (derivedQuotientData C).toOverCategoryData where
  toOverQuiverMorphism := counitQuiverMor_inv C
  map_id := counitInv_map_id C
  map_comp := counitInv_map_comp C

/-- The composition ε ∘ ε⁻¹ = id on morphisms. -/
theorem counit_comp_inv_mor (f : Q.MorType) :
    (counitFunctorData C).morFn ((counitFunctorData_inv C).morFn f) = f := by
  simp only [counitFunctorData, counitQuiverMor, counitFunctorData_inv,
    counitQuiverMor_inv, counitEvalQuot, CategoryQuotientData.quotMor,
    Quotient.lift_mk, counitEval, counitEvalAux]

/-- The composition ε⁻¹ ∘ ε = id on morphisms.
    This uses the round-trip equivalence embed_counitEval. -/
theorem inv_comp_counit_mor (m : (derivedQuotientData C).quotQuiver.MorType) :
    (counitFunctorData_inv C).morFn ((counitFunctorData C).morFn m) = m := by
  rcases m with ⟨a, b, qm⟩
  simp only [counitFunctorData, counitQuiverMor, counitFunctorData_inv,
    counitQuiverMor_inv, CategoryQuotientData.quotQuiver]
  simp only [counitEvalQuot]
  induction qm using Quotient.ind with
  | _ fm =>
    simp only [Quotient.lift_mk]
    have h_src : Q.src (counitEval C fm) = a := counitEvalAux_src C fm
    have h_tgt : Q.tgt (counitEval C fm) = b := counitEvalAux_tgt C fm
    have h_equiv := var_counitEval_equiv C fm
    let D := derivedQuotientData C
    refine Sigma.ext h_src ?_
    apply D.quotMorSigma_heq h_src h_tgt
    rw [D.quotMor_cast h_src h_tgt]
    exact Quotient.sound h_equiv

/-- The composition ε ∘ ε⁻¹ = id as functors. -/
theorem counit_comp_inv_eq_id :
    (counitFunctorData_inv C).comp (counitFunctorData C) = OverFunctorData.id C := by
  apply OverFunctorData.ext <;> funext
  · rfl
  · exact counit_comp_inv_mor C _

/-- The composition ε⁻¹ ∘ ε = id as functors. -/
theorem inv_comp_counit_eq_id :
    (counitFunctorData C).comp (counitFunctorData_inv C) =
    OverFunctorData.id (derivedQuotientData C).toOverCategoryData := by
  apply OverFunctorData.ext <;> funext
  · rfl
  · exact inv_comp_counit_mor C _

end Reflectivity

/-! ## Mathlib IsIso Instance for Counit

We show that each component of the counit natural transformation is an
isomorphism in the mathlib sense, which allows us to apply
`fullyFaithfulROfIsIsoCounit` to derive full faithfulness of Φ.
-/

section MathlibReflectivity

universe uMR

/-- The counit component at C is an isomorphism in BundledOverCategoryData.
    This lifts the OverFunctorData-level isomorphism to a mathlib Iso. -/
def counitComponentIso (C : BundledOverCategoryData.{uMR, uMR}) :
    (PhiFunctor ⋙ LFunctor).obj C ≅ C where
  hom := counitFunctorData C.data
  inv := counitFunctorData_inv C.data
  hom_inv_id := inv_comp_counit_eq_id C.data
  inv_hom_id := counit_comp_inv_eq_id C.data

/-- The counit at each object is an isomorphism (mathlib typeclass instance). -/
instance adjunctionCounit_app_isIso (C : BundledOverCategoryData.{uMR, uMR}) :
    IsIso (catCopresheafMathlibAdjunction.counit.app C) :=
  (counitComponentIso C).isIso_hom

/-- The counit of the adjunction is a natural isomorphism. -/
instance adjunctionCounit_isIso : IsIso catCopresheafMathlibAdjunction.{uMR}.counit :=
  NatIso.isIso_of_isIso_app _

/-- The natural isomorphism form of the counit. This shows that the counit is
    invertible, which is the standard characterization of a reflective adjunction.
-/
def catCopresheafCounitNatIso : (PhiFunctor ⋙ LFunctor) ≅ (Functor.id BundledOverCategoryData) :=
  NatIso.ofComponents counitComponentIso (fun {X Y} f => by
    simp only [Functor.id_obj, Functor.comp_obj, Functor.id_map, Functor.comp_map,
      counitComponentIso, LFunctor, PhiFunctor]
    exact counitNT_naturality f)

/-! ### Full Faithfulness of Φ

We prove that Φ (PhiFunctor) is fully faithful by constructing an explicit
preimage for morphisms. Given f : Φ(X) → Φ(Y), the preimage is:

  preimage(f) = ε_X⁻¹ ≫ L(f) ≫ ε_Y

where ε is the counit isomorphism. This is essentially the standard proof
that when the counit of an adjunction is an isomorphism, the right adjoint
is fully faithful, but done computationally. -/

/-- The preimage of a morphism f : Φ(X) → Φ(Y) under Φ.
    This is constructed as ε_X⁻¹ ≫ L(f) ≫ ε_Y where ε is the counit. -/
def phiPreimage {X Y : BundledOverCategoryData.{uMR, uMR}}
    (f : PhiFunctor.obj X ⟶ PhiFunctor.obj Y) : X ⟶ Y :=
  (counitComponentIso X).inv ≫ LFunctor.map f ≫ (counitComponentIso Y).hom

set_option backward.isDefEq.respectTransparency false in
/-- The unit of the adjunction at Φ(Z) is an isomorphism.
    This follows from the triangle identity: η_{Φ(Z)} ≫ Φ(ε_Z) = id,
    combined with the fact that ε_Z is an isomorphism. -/
instance adjunctionUnit_app_isIso (Z : BundledOverCategoryData.{uMR, uMR}) :
    IsIso (catCopresheafMathlibAdjunction.unit.app (PhiFunctor.obj Z)) := by
  -- The counit ε_Z is an isomorphism, so Φ(ε_Z) is also an iso
  have h_phi_counit_iso : IsIso (PhiFunctor.map (counitComponentIso Z).hom) :=
    Functor.map_isIso PhiFunctor (counitComponentIso Z).hom
  -- The triangle identity says η_{Φ(Z)} ≫ Φ(ε_Z) = id
  have triangle := catCopresheafMathlibAdjunction.right_triangle_components Z
  -- Rewrite to get the IsIso instance for the composition
  have h_comp_eq_id : catCopresheafMathlibAdjunction.unit.app (PhiFunctor.obj Z) ≫
      PhiFunctor.map (catCopresheafMathlibAdjunction.counit.app Z) = 𝟙 _ := triangle
  have h_comp_iso : IsIso (catCopresheafMathlibAdjunction.unit.app (PhiFunctor.obj Z) ≫
      PhiFunctor.map (catCopresheafMathlibAdjunction.counit.app Z)) := by
    rw [h_comp_eq_id]; infer_instance
  exact IsIso.of_isIso_comp_right
    (catCopresheafMathlibAdjunction.unit.app (PhiFunctor.obj Z))
    (PhiFunctor.map (catCopresheafMathlibAdjunction.counit.app Z))

set_option backward.isDefEq.respectTransparency false in
/-- Φ(ε⁻¹) = η: the image of the counit inverse under Φ equals the unit. -/
theorem phi_map_counit_inv_eq_unit (Z : BundledOverCategoryData.{uMR, uMR}) :
    PhiFunctor.map (counitComponentIso Z).inv =
    catCopresheafMathlibAdjunction.unit.app (PhiFunctor.obj Z) := by
  -- η ≫ Φ(ε) = id from the triangle identity
  -- Φ(ε⁻¹) ≫ Φ(ε) = id from Φ preserving isos
  -- Since Φ(ε) is an iso with unique inverse, η = inv(Φ(ε)) = Φ(ε⁻¹)
  have h_phi_counit_iso : IsIso (PhiFunctor.map (counitComponentIso Z).hom) :=
    Functor.map_isIso PhiFunctor (counitComponentIso Z).hom
  have triangle := catCopresheafMathlibAdjunction.right_triangle_components Z
  -- Φ(ε⁻¹) = inv(Φ(ε)) since Φ preserves isos
  have h_phi_inv : PhiFunctor.map (counitComponentIso Z).inv =
      inv (PhiFunctor.map (counitComponentIso Z).hom) := by
    symm
    apply IsIso.inv_eq_of_hom_inv_id
    simp only [← CategoryTheory.Functor.map_comp, Iso.hom_inv_id,
      CategoryTheory.Functor.map_id]
  -- η = inv(Φ(ε)) from the triangle
  have h_unit_eq_inv : catCopresheafMathlibAdjunction.unit.app (PhiFunctor.obj Z) =
      inv (PhiFunctor.map (counitComponentIso Z).hom) := by
    -- counitComponentIso.hom = adjunction.counit.app definitionally
    exact IsIso.eq_inv_of_inv_hom_id triangle
  rw [h_phi_inv, h_unit_eq_inv]

/-- Φ(ε) = inv(η): the image of the counit under Φ equals the inverse of the unit. -/
theorem phi_map_counit_eq_unit_inv (Z : BundledOverCategoryData.{uMR, uMR}) :
    PhiFunctor.map (counitComponentIso Z).hom =
    inv (catCopresheafMathlibAdjunction.unit.app (PhiFunctor.obj Z)) := by
  -- From phi_map_counit_inv_eq_unit: Φ(ε⁻¹) = η
  -- So Φ(ε) = inv(Φ(ε⁻¹)) = inv(η)
  have h := phi_map_counit_inv_eq_unit Z
  -- Φ(ε) is the inverse of Φ(ε⁻¹)
  -- inv_eq_of_inv_hom_id: g ≫ f = 𝟙 → inv f = g
  -- So we need Φ(ε) ≫ Φ(ε⁻¹) = 𝟙 to get inv(Φ(ε⁻¹)) = Φ(ε)
  have h_phi_hom_is_inv : PhiFunctor.map (counitComponentIso Z).hom =
      inv (PhiFunctor.map (counitComponentIso Z).inv) := by
    symm
    apply IsIso.inv_eq_of_inv_hom_id
    simp only [← CategoryTheory.Functor.map_comp, Iso.hom_inv_id,
      CategoryTheory.Functor.map_id]
  -- Using h: Φ(ε⁻¹) = η, so inv(Φ(ε⁻¹)) = inv(η)
  calc PhiFunctor.map (counitComponentIso Z).hom
      = inv (PhiFunctor.map (counitComponentIso Z).inv) := h_phi_hom_is_inv
    _ = inv (catCopresheafMathlibAdjunction.unit.app (PhiFunctor.obj Z)) := by
          congr 1

set_option backward.isDefEq.respectTransparency false in
/-- Φ applied to the preimage gives back the original morphism. -/
theorem phi_map_preimage {X Y : BundledOverCategoryData.{uMR, uMR}}
    (f : PhiFunctor.obj X ⟶ PhiFunctor.obj Y) :
    PhiFunctor.map (phiPreimage f) = f := by
  simp only [phiPreimage]
  simp only [Functor.map_comp]
  -- Use the relationships: Φ(ε⁻¹) = η and Φ(ε) = inv(η)
  rw [phi_map_counit_inv_eq_unit X, phi_map_counit_eq_unit_inv Y]
  -- Now: η_X ≫ Φ(L(f)) ≫ inv(η_Y) = f
  -- Using naturality of η: f ≫ η_Y = η_X ≫ Φ(L(f))
  have h_nat := catCopresheafMathlibAdjunction.unit.naturality f
  simp only [Functor.id_obj, Functor.id_map, Functor.comp_obj, Functor.comp_map] at h_nat
  -- h_nat : f ≫ η_Y = η_X ≫ Φ(L(f))
  -- Rewrite LHS using h_nat.symm: η_X ≫ Φ(L(f)) = f ≫ η_Y
  calc catCopresheafMathlibAdjunction.unit.app (PhiFunctor.obj X) ≫
        PhiFunctor.map (LFunctor.map f) ≫
        inv (catCopresheafMathlibAdjunction.unit.app (PhiFunctor.obj Y))
      = (catCopresheafMathlibAdjunction.unit.app (PhiFunctor.obj X) ≫
          PhiFunctor.map (LFunctor.map f)) ≫
        inv (catCopresheafMathlibAdjunction.unit.app (PhiFunctor.obj Y)) := by
          simp only [Category.assoc]
    _ = (f ≫ catCopresheafMathlibAdjunction.unit.app (PhiFunctor.obj Y)) ≫
        inv (catCopresheafMathlibAdjunction.unit.app (PhiFunctor.obj Y)) := by
          rw [← h_nat]
    _ = f := by simp only [Category.assoc, IsIso.hom_inv_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
/-- The preimage of Φ(g) is g. -/
theorem phi_preimage_map {X Y : BundledOverCategoryData.{uMR, uMR}}
    (g : X ⟶ Y) : phiPreimage (PhiFunctor.map g) = g := by
  simp only [phiPreimage]
  -- Use naturality of the counit natural transformation
  -- counitNT.naturality g says: (PhiFunctor ⋙ LFunctor).map g ≫ ε_Y = ε_X ≫ g
  have h_nat := counitNT.naturality g
  simp only [Functor.comp_map, Functor.id_map] at h_nat
  -- h_nat : LFunctor.map (PhiFunctor.map g) ≫ counitNT.app Y = counitNT.app X ≫ g
  -- counitNT.app Z = counitComponentIso.hom by definition
  -- ε_X⁻¹ ≫ L(Φ(g)) ≫ ε_Y = ε_X⁻¹ ≫ (ε_X ≫ g) = g
  have h_app_eq : ∀ (Z : BundledOverCategoryData.{uMR, uMR}),
      counitNT.app Z = (counitComponentIso Z).hom := fun _ => rfl
  rw [h_app_eq X, h_app_eq Y] at h_nat
  calc (counitComponentIso X).inv ≫ LFunctor.map (PhiFunctor.map g) ≫
        (counitComponentIso Y).hom
      = (counitComponentIso X).inv ≫ ((counitComponentIso X).hom ≫ g) := by rw [← h_nat]
    _ = g := by simp only [Iso.inv_hom_id_assoc]

/-- Φ (PhiFunctor) is fully faithful.
    This is a computational proof that the right adjoint of a reflective adjunction
    is fully faithful. -/
def phiFunctorFullyFaithful : PhiFunctor.{uMR}.FullyFaithful where
  preimage := phiPreimage
  map_preimage := phi_map_preimage
  preimage_map := phi_preimage_map

/-- PhiFunctor is full (has preimages for all morphisms in its image). -/
instance phiFunctor_full : PhiFunctor.{uMR}.Full :=
  phiFunctorFullyFaithful.full

/-- PhiFunctor is faithful (injective on hom-sets). -/
instance phiFunctor_faithful : PhiFunctor.{uMR}.Faithful :=
  phiFunctorFullyFaithful.faithful

/-- PhiFunctor is a right adjoint. This enables mathlib's automatic derivation
    of limit preservation. -/
instance phiFunctor_isRightAdjoint : PhiFunctor.{uMR}.IsRightAdjoint where
  exists_leftAdjoint := ⟨LFunctor, ⟨catCopresheafMathlibAdjunction⟩⟩

/-- LFunctor is a left adjoint. This enables mathlib's automatic derivation
    of colimit preservation. -/
instance lFunctor_isLeftAdjoint : LFunctor.{uMR}.IsLeftAdjoint where
  exists_rightAdjoint := ⟨PhiFunctor, ⟨catCopresheafMathlibAdjunction⟩⟩

/-- PhiFunctor is reflective: it is a fully faithful right adjoint.
    This is the standard characterization of the inclusion of a reflective
    subcategory. -/
instance phiFunctor_reflective : Reflective PhiFunctor.{uMR} where
  L := LFunctor
  adj := catCopresheafMathlibAdjunction

end MathlibReflectivity

/-! ## Limit and Colimit Preservation

The following instances are automatically derived from the adjunction:
- PhiFunctor preserves all limits (from being a right adjoint)
- LFunctor preserves all colimits (from being a left adjoint)

These are provided by mathlib's `Functor.instPreservesLimitsOfSizeOfIsRightAdjoint`
and `Functor.instPreservesColimitsOfSizeOfIsLeftAdjoint` instances.
-/

section PreservationInstances

universe uPI

/-- PhiFunctor preserves limits of any shape J. This is automatically derived
    from `phiFunctor_isRightAdjoint`. -/
example (J : Type uPI) [Category J] :
    Limits.PreservesLimitsOfShape J PhiFunctor.{uPI} := inferInstance

/-- LFunctor preserves colimits of any shape J. This is automatically derived
    from `lFunctor_isLeftAdjoint`. -/
example (J : Type uPI) [Category J] :
    Limits.PreservesColimitsOfShape J LFunctor.{uPI} := inferInstance

/-! ### Conjectured Additional Preservation Properties

The following preservation properties are conjectured based on the structure
of the adjunction, but proving them requires more detailed analysis:

1. **LFunctor preserves binary products**: For a left adjoint, this is not
   automatic but may follow from the specific structure of our adjunction.
   Binary products in the copresheaf category are computed pointwise, and
   L(F × G) should be isomorphic to L(F) × L(G) because:
   - Objects: (F × G)(Obj) = F(Obj) × G(Obj) ≅ L(F).Obj × L(G).Obj
   - Morphisms: Built componentwise from the product copresheaf

2. **PhiFunctor preserves binary coproducts**: For a right adjoint, this is
   not automatic but may follow from the specific structure of our adjunction.
   The coproduct of categories is their disjoint union, and
   Φ(C ⊔ D) should be isomorphic to Φ(C) ⊔ Φ(D) because both have:
   - Objects: disjoint union of objects
   - Morphisms: disjoint union of morphisms (no cross-morphisms)

3. **Exponential preservation**: Per nLab Theorem 4.1, if L preserves products,
   then Φ preserves exponentials, making the subcategory of categories
   cartesian closed.

These properties would need to be proven by constructing explicit isomorphisms
between the limit/colimit objects. -/

end PreservationInstances

/-! ## Binary Coproduct of Categories

We define the binary coproduct (disjoint union) of categories represented
as OverCategoryData, and show that PhiFunctor preserves this coproduct. -/

section BinaryCoproduct

universe uCoprod

variable (Q₁ Q₂ : OverQuiver.{uCoprod, uCoprod})

/-- The binary coproduct of two OverQuivers is their disjoint union. -/
def OverQuiver.sum : OverQuiver.{uCoprod, uCoprod} where
  Obj := Q₁.Obj ⊕ Q₂.Obj
  MorType := Q₁.MorType ⊕ Q₂.MorType
  src := Sum.map Q₁.src Q₂.src
  tgt := Sum.map Q₁.tgt Q₂.tgt

/-- In the sum quiver, composability is impossible across components because
    Sum.inl _ ≠ Sum.inr _. -/
theorem sum_composable_inl_inr_false {m₁ : Q₁.MorType} {m₂ : Q₂.MorType} :
    ¬(Q₁.sum Q₂).Composable (Sum.inl m₁) (Sum.inr m₂) := by
  simp [OverQuiver.sum, OverQuiver.Composable]

/-- In the sum quiver, composability is impossible across components. -/
theorem sum_composable_inr_inl_false {m₁ : Q₂.MorType} {m₂ : Q₁.MorType} :
    ¬(Q₁.sum Q₂).Composable (Sum.inr m₁) (Sum.inl m₂) := by
  simp [OverQuiver.sum, OverQuiver.Composable]

variable {Q₁ Q₂} (C₁ : OverCategoryData Q₁) (C₂ : OverCategoryData Q₂)

/-- Helper to compose morphisms in the sum category. -/
def sumCompFn (p : (Q₁.sum Q₂).ComposablePairsType) : Q₁.MorType ⊕ Q₂.MorType :=
  match hm₁ : p.val.1, hm₂ : p.val.2 with
  | Sum.inl m₁, Sum.inl m₂ =>
    Sum.inl (C₁.compFn ⟨(m₁, m₂), by
      have hp := p.property
      simp only [OverQuiver.sum, OverQuiver.Composable, hm₁, hm₂,
        Sum.map_inl] at hp
      exact Sum.inl.inj hp⟩)
  | Sum.inr m₁, Sum.inr m₂ =>
    Sum.inr (C₂.compFn ⟨(m₁, m₂), by
      have hp := p.property
      simp only [OverQuiver.sum, OverQuiver.Composable, hm₁, hm₂,
        Sum.map_inr] at hp
      exact Sum.inr.inj hp⟩)
  | Sum.inl m₁, Sum.inr m₂ => absurd p.property (by
      simp [OverQuiver.sum, OverQuiver.Composable, hm₁, hm₂])
  | Sum.inr m₁, Sum.inl m₂ => absurd p.property (by
      simp [OverQuiver.sum, OverQuiver.Composable, hm₁, hm₂])

theorem sumCompFn_inl_inl' (m₁ m₂ : Q₁.MorType)
    (hp : (Q₁.sum Q₂).Composable (Sum.inl m₁) (Sum.inl m₂)) :
    sumCompFn C₁ C₂ ⟨(Sum.inl m₁, Sum.inl m₂), hp⟩ =
    Sum.inl (C₁.compFn ⟨(m₁, m₂), Sum.inl.inj hp⟩) := rfl

theorem sumCompFn_inr_inr' (m₁ m₂ : Q₂.MorType)
    (hp : (Q₁.sum Q₂).Composable (Sum.inr m₁) (Sum.inr m₂)) :
    sumCompFn C₁ C₂ ⟨(Sum.inr m₁, Sum.inr m₂), hp⟩ =
    Sum.inr (C₂.compFn ⟨(m₁, m₂), Sum.inr.inj hp⟩) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The binary coproduct of two OverCategoryData is their disjoint union. -/
def OverCategoryData.sum : OverCategoryData (Q₁.sum Q₂) where
  idFn := Sum.elim (Sum.inl ∘ C₁.idFn) (Sum.inr ∘ C₂.idFn)
  compFn := sumCompFn C₁ C₂
  id_src a := by
    cases a <;> simp only [OverQuiver.sum, Sum.elim_inl, Sum.elim_inr,
      Function.comp_apply, Sum.map_inl, Sum.map_inr, C₁.id_src, C₂.id_src]
  id_tgt a := by
    cases a <;> simp only [OverQuiver.sum, Sum.elim_inl, Sum.elim_inr,
      Function.comp_apply, Sum.map_inl, Sum.map_inr, C₁.id_tgt, C₂.id_tgt]
  comp_src p := by
    rcases p with ⟨⟨m₁, m₂⟩, hp⟩
    cases m₁ with
    | inl m₁ =>
      cases m₂ with
      | inl m₂ =>
        simp only [OverQuiver.sum, OverQuiver.compPairFst]
        rw [sumCompFn_inl_inl' C₁ C₂ m₁ m₂ hp]
        simp only [Sum.map_inl, C₁.comp_src, OverQuiver.compPairFst]
      | inr m₂ => exact absurd hp (sum_composable_inl_inr_false Q₁ Q₂)
    | inr m₁ =>
      cases m₂ with
      | inl m₂ => exact absurd hp (sum_composable_inr_inl_false Q₁ Q₂)
      | inr m₂ =>
        simp only [OverQuiver.sum, OverQuiver.compPairFst]
        rw [sumCompFn_inr_inr' C₁ C₂ m₁ m₂ hp]
        simp only [Sum.map_inr, C₂.comp_src, OverQuiver.compPairFst]
  comp_tgt p := by
    rcases p with ⟨⟨m₁, m₂⟩, hp⟩
    cases m₁ with
    | inl m₁ =>
      cases m₂ with
      | inl m₂ =>
        simp only [OverQuiver.sum, OverQuiver.compPairSnd]
        rw [sumCompFn_inl_inl' C₁ C₂ m₁ m₂ hp]
        simp only [Sum.map_inl, C₁.comp_tgt, OverQuiver.compPairSnd]
      | inr m₂ => exact absurd hp (sum_composable_inl_inr_false Q₁ Q₂)
    | inr m₁ =>
      cases m₂ with
      | inl m₂ => exact absurd hp (sum_composable_inr_inl_false Q₁ Q₂)
      | inr m₂ =>
        simp only [OverQuiver.sum, OverQuiver.compPairSnd]
        rw [sumCompFn_inr_inr' C₁ C₂ m₁ m₂ hp]
        simp only [Sum.map_inr, C₂.comp_tgt, OverQuiver.compPairSnd]
  id_comp f := by
    cases f with
    | inl f₁ =>
      simp only [OverQuiver.sum, Sum.map_inl, Sum.elim_inl, Function.comp_apply]
      have hp : (Q₁.sum Q₂).Composable (Sum.inl (C₁.idFn (Q₁.src f₁)))
          (Sum.inl f₁) := by
        simp only [OverQuiver.sum, OverQuiver.Composable, Sum.map_inl,
          C₁.id_tgt]
      rw [sumCompFn_inl_inl' C₁ C₂ (C₁.idFn (Q₁.src f₁)) f₁ hp]
      simp only [C₁.id_comp]
    | inr f₂ =>
      simp only [OverQuiver.sum, Sum.map_inr, Sum.elim_inr, Function.comp_apply]
      have hp : (Q₁.sum Q₂).Composable (Sum.inr (C₂.idFn (Q₂.src f₂)))
          (Sum.inr f₂) := by
        simp only [OverQuiver.sum, OverQuiver.Composable, Sum.map_inr,
          C₂.id_tgt]
      rw [sumCompFn_inr_inr' C₁ C₂ (C₂.idFn (Q₂.src f₂)) f₂ hp]
      simp only [C₂.id_comp]
  comp_id f := by
    cases f with
    | inl f₁ =>
      simp only [OverQuiver.sum, Sum.map_inl, Sum.elim_inl, Function.comp_apply]
      have hp : (Q₁.sum Q₂).Composable (Sum.inl f₁)
          (Sum.inl (C₁.idFn (Q₁.tgt f₁))) := by
        simp only [OverQuiver.sum, OverQuiver.Composable, Sum.map_inl,
          C₁.id_src]
      rw [sumCompFn_inl_inl' C₁ C₂ f₁ (C₁.idFn (Q₁.tgt f₁)) hp]
      simp only [C₁.comp_id]
    | inr f₂ =>
      simp only [OverQuiver.sum, Sum.map_inr, Sum.elim_inr, Function.comp_apply]
      have hp : (Q₁.sum Q₂).Composable (Sum.inr f₂)
          (Sum.inr (C₂.idFn (Q₂.tgt f₂))) := by
        simp only [OverQuiver.sum, OverQuiver.Composable, Sum.map_inr,
          C₂.id_src]
      rw [sumCompFn_inr_inr' C₁ C₂ f₂ (C₂.idFn (Q₂.tgt f₂)) hp]
      simp only [C₂.comp_id]
  assoc t := by
    rcases t with ⟨⟨f, g, h⟩, ⟨hfg, hgh⟩⟩
    cases f with
    | inl f₁ =>
      cases g with
      | inl g₁ =>
        cases h with
        | inl h₁ =>
          simp only [OverQuiver.sum]
          have hfg' : Q₁.Composable f₁ g₁ := Sum.inl.inj hfg
          have hgh' : Q₁.Composable g₁ h₁ := Sum.inl.inj hgh
          have hcomp_fg_h : (Q₁.sum Q₂).Composable
              (Sum.inl (C₁.compFn ⟨(f₁, g₁), hfg'⟩)) (Sum.inl h₁) := by
            simp only [OverQuiver.sum, OverQuiver.Composable, Sum.map_inl,
              Sum.inl.injEq, C₁.comp_tgt, OverQuiver.compPairSnd]
            exact hgh'
          have hcomp_f_gh : (Q₁.sum Q₂).Composable (Sum.inl f₁)
              (Sum.inl (C₁.compFn ⟨(g₁, h₁), hgh'⟩)) := by
            simp only [OverQuiver.sum, OverQuiver.Composable, Sum.map_inl,
              Sum.inl.injEq, C₁.comp_src, OverQuiver.compPairFst]
            exact hfg'
          change sumCompFn C₁ C₂ ⟨(sumCompFn C₁ C₂ ⟨(Sum.inl f₁, Sum.inl g₁), hfg⟩,
            Sum.inl h₁), _⟩ = sumCompFn C₁ C₂ ⟨(Sum.inl f₁,
            sumCompFn C₁ C₂ ⟨(Sum.inl g₁, Sum.inl h₁), hgh⟩), _⟩
          simp only [sumCompFn_inl_inl' C₁ C₂ f₁ g₁ hfg,
            sumCompFn_inl_inl' C₁ C₂ g₁ h₁ hgh,
            sumCompFn_inl_inl' C₁ C₂ (C₁.compFn ⟨(f₁, g₁), hfg'⟩) h₁ hcomp_fg_h,
            sumCompFn_inl_inl' C₁ C₂ f₁ (C₁.compFn ⟨(g₁, h₁), hgh'⟩) hcomp_f_gh,
            Sum.inl.injEq]
          exact C₁.assoc ⟨(f₁, g₁, h₁), ⟨hfg', hgh'⟩⟩
        | inr h₂ =>
          have hgh' : (Q₁.sum Q₂).Composable (Sum.inl g₁) (Sum.inr h₂) := hgh
          exact absurd hgh' (sum_composable_inl_inr_false Q₁ Q₂)
      | inr g₂ =>
        have hfg' : (Q₁.sum Q₂).Composable (Sum.inl f₁) (Sum.inr g₂) := hfg
        exact absurd hfg' (sum_composable_inl_inr_false Q₁ Q₂)
    | inr f₂ =>
      cases g with
      | inl g₁ =>
        have hfg' : (Q₁.sum Q₂).Composable (Sum.inr f₂) (Sum.inl g₁) := hfg
        exact absurd hfg' (sum_composable_inr_inl_false Q₁ Q₂)
      | inr g₂ =>
        cases h with
        | inl h₁ =>
          have hgh' : (Q₁.sum Q₂).Composable (Sum.inr g₂) (Sum.inl h₁) := hgh
          exact absurd hgh' (sum_composable_inr_inl_false Q₁ Q₂)
        | inr h₂ =>
          simp only [OverQuiver.sum]
          have hfg' : Q₂.Composable f₂ g₂ := Sum.inr.inj hfg
          have hgh' : Q₂.Composable g₂ h₂ := Sum.inr.inj hgh
          have hcomp_fg_h : (Q₁.sum Q₂).Composable
              (Sum.inr (C₂.compFn ⟨(f₂, g₂), hfg'⟩)) (Sum.inr h₂) := by
            simp only [OverQuiver.sum, OverQuiver.Composable, Sum.map_inr,
              Sum.inr.injEq, C₂.comp_tgt, OverQuiver.compPairSnd]
            exact hgh'
          have hcomp_f_gh : (Q₁.sum Q₂).Composable (Sum.inr f₂)
              (Sum.inr (C₂.compFn ⟨(g₂, h₂), hgh'⟩)) := by
            simp only [OverQuiver.sum, OverQuiver.Composable, Sum.map_inr,
              Sum.inr.injEq, C₂.comp_src, OverQuiver.compPairFst]
            exact hfg'
          change sumCompFn C₁ C₂ ⟨(sumCompFn C₁ C₂ ⟨(Sum.inr f₂, Sum.inr g₂), hfg⟩,
            Sum.inr h₂), _⟩ = sumCompFn C₁ C₂ ⟨(Sum.inr f₂,
            sumCompFn C₁ C₂ ⟨(Sum.inr g₂, Sum.inr h₂), hgh⟩), _⟩
          simp only [sumCompFn_inr_inr' C₁ C₂ f₂ g₂ hfg,
            sumCompFn_inr_inr' C₁ C₂ g₂ h₂ hgh,
            sumCompFn_inr_inr' C₁ C₂ (C₂.compFn ⟨(f₂, g₂), hfg'⟩) h₂ hcomp_fg_h,
            sumCompFn_inr_inr' C₁ C₂ f₂ (C₂.compFn ⟨(g₂, h₂), hgh'⟩) hcomp_f_gh,
            Sum.inr.injEq]
          exact C₂.assoc ⟨(f₂, g₂, h₂), ⟨hfg', hgh'⟩⟩

/-- The equivalence between composable pairs in the sum quiver and the sum of
    composable pairs from each component. This underlies
    coproduct preservation. -/
def sumComposablePairsEquiv :
    (Q₁.sum Q₂).ComposablePairsType ≃
    Q₁.ComposablePairsType ⊕ Q₂.ComposablePairsType where
  toFun p :=
    match hm₁ : p.val.1, hm₂ : p.val.2 with
    | Sum.inl m₁, Sum.inl m₂ =>
      Sum.inl ⟨(m₁, m₂), by
        have hp := p.property
        simp only [OverQuiver.sum, OverQuiver.Composable, hm₁, hm₂,
          Sum.map_inl] at hp
        exact Sum.inl.inj hp⟩
    | Sum.inr m₁, Sum.inr m₂ =>
      Sum.inr ⟨(m₁, m₂), by
        have hp := p.property
        simp only [OverQuiver.sum, OverQuiver.Composable, hm₁, hm₂,
          Sum.map_inr] at hp
        exact Sum.inr.inj hp⟩
    | Sum.inl m₁, Sum.inr m₂ => absurd p.property (by
        simp [OverQuiver.sum, OverQuiver.Composable, hm₁, hm₂])
    | Sum.inr m₁, Sum.inl m₂ => absurd p.property (by
        simp [OverQuiver.sum, OverQuiver.Composable, hm₁, hm₂])
  invFun := Sum.elim
    (fun p => ⟨(Sum.inl p.val.1, Sum.inl p.val.2), by
      simp only [OverQuiver.sum, OverQuiver.Composable, Sum.map_inl,
        Sum.inl.injEq]
      exact p.property⟩)
    (fun p => ⟨(Sum.inr p.val.1, Sum.inr p.val.2), by
      simp only [OverQuiver.sum, OverQuiver.Composable, Sum.map_inr,
        Sum.inr.injEq]
      exact p.property⟩)
  left_inv p := by
    rcases p with ⟨⟨m₁, m₂⟩, hp⟩
    cases m₁ with
    | inl m₁ =>
      cases m₂ with
      | inl m₂ => simp only [Sum.elim_inl]
      | inr m₂ => exact absurd hp (sum_composable_inl_inr_false Q₁ Q₂)
    | inr m₁ =>
      cases m₂ with
      | inl m₂ => exact absurd hp (sum_composable_inr_inl_false Q₁ Q₂)
      | inr m₂ => simp only [Sum.elim_inr]
  right_inv x := by
    cases x with
    | inl p => simp only [Sum.elim_inl]
    | inr p => simp only [Sum.elim_inr]

/-- The binary coproduct of two FunctorData (Type u) is their pointwise sum. -/
def FunctorData.sum (F₁ F₂ : CategoryJudgments.FunctorData (Type u)) :
    CategoryJudgments.FunctorData (Type u) where
  objC := F₁.objC ⊕ F₂.objC
  morC := F₁.morC ⊕ F₂.morC
  idC := F₁.idC ⊕ F₂.idC
  compC := F₁.compC ⊕ F₂.compC
  dom := Sum.map F₁.dom F₂.dom
  cod := Sum.map F₁.cod F₂.cod
  idMor := Sum.map F₁.idMor F₂.idMor
  left := Sum.map F₁.left F₂.left
  right := Sum.map F₁.right F₂.right
  composite := Sum.map F₁.composite F₂.composite
  h_id_endo := by
    funext a
    cases a with
    | inl a =>
      simp only [types_comp_apply, Sum.map_inl]
      exact congrArg Sum.inl (congrFun F₁.h_id_endo a)
    | inr a =>
      simp only [types_comp_apply, Sum.map_inr]
      exact congrArg Sum.inr (congrFun F₂.h_id_endo a)
  h_comp_match := by
    funext p
    cases p with
    | inl p =>
      simp only [types_comp_apply, Sum.map_inl]
      exact congrArg Sum.inl (congrFun F₁.h_comp_match p)
    | inr p =>
      simp only [types_comp_apply, Sum.map_inr]
      exact congrArg Sum.inr (congrFun F₂.h_comp_match p)
  h_comp_dom := by
    funext p
    cases p with
    | inl p =>
      simp only [types_comp_apply, Sum.map_inl]
      exact congrArg Sum.inl (congrFun F₁.h_comp_dom p)
    | inr p =>
      simp only [types_comp_apply, Sum.map_inr]
      exact congrArg Sum.inr (congrFun F₂.h_comp_dom p)
  h_comp_cod := by
    funext p
    cases p with
    | inl p =>
      simp only [types_comp_apply, Sum.map_inl]
      exact congrArg Sum.inl (congrFun F₁.h_comp_cod p)
    | inr p =>
      simp only [types_comp_apply, Sum.map_inr]
      exact congrArg Sum.inr (congrFun F₂.h_comp_cod p)

/-- The isomorphism between Φ(C₁.sum C₂) and Φ(C₁).sum Φ(C₂) on the compC
    component, using the composable pairs equivalence. -/
def phiSumCompIso :
    (C₁.sum C₂).toJudgmentFunctorData.compC ≃
    (FunctorData.sum C₁.toJudgmentFunctorData C₂.toJudgmentFunctorData).compC :=
  sumComposablePairsEquiv (Q₁ := Q₁) (Q₂ := Q₂)

set_option backward.isDefEq.respectTransparency false in
/-- Φ preserves binary coproducts: Φ(C₁ ⊕ C₂) ≅ Φ(C₁) ⊕ Φ(C₂).
    The isomorphism is the identity on objects, morphisms, and identities,
    and uses the composable pairs equivalence on the compC component. -/
def phiFunctorPreservesCoproduct :
    CategoryJudgments.NatTransData
      (C₁.sum C₂).toJudgmentFunctorData
      (FunctorData.sum C₁.toJudgmentFunctorData C₂.toJudgmentFunctorData) where
  appObj := id
  appMor := id
  appId := id
  appComp := phiSumCompIso C₁ C₂
  naturality_dom := rfl
  naturality_cod := rfl
  naturality_idMor := by
    funext a
    cases a <;> simp [OverCategoryData.sum, FunctorData.sum,
      OverCategoryData.toJudgmentFunctorData]
  naturality_left := by
    funext p
    rcases p with ⟨⟨m₁, m₂⟩, hp⟩
    cases m₁ with
    | inl m₁ =>
      cases m₂ with
      | inl m₂ => simp [phiSumCompIso, sumComposablePairsEquiv,
          OverCategoryData.toJudgmentFunctorData, FunctorData.sum]
      | inr m₂ => exact absurd hp (sum_composable_inl_inr_false Q₁ Q₂)
    | inr m₁ =>
      cases m₂ with
      | inl m₂ => exact absurd hp (sum_composable_inr_inl_false Q₁ Q₂)
      | inr m₂ => simp [phiSumCompIso, sumComposablePairsEquiv,
          OverCategoryData.toJudgmentFunctorData, FunctorData.sum]
  naturality_right := by
    funext p
    rcases p with ⟨⟨m₁, m₂⟩, hp⟩
    cases m₁ with
    | inl m₁ =>
      cases m₂ with
      | inl m₂ => simp [phiSumCompIso, sumComposablePairsEquiv,
          OverCategoryData.toJudgmentFunctorData, FunctorData.sum]
      | inr m₂ => exact absurd hp (sum_composable_inl_inr_false Q₁ Q₂)
    | inr m₁ =>
      cases m₂ with
      | inl m₂ => exact absurd hp (sum_composable_inr_inl_false Q₁ Q₂)
      | inr m₂ => simp [phiSumCompIso, sumComposablePairsEquiv,
          OverCategoryData.toJudgmentFunctorData, FunctorData.sum]
  naturality_composite := by
    funext p
    rcases p with ⟨⟨m₁, m₂⟩, hp⟩
    cases m₁ with
    | inl m₁ =>
      cases m₂ with
      | inl m₂ => rfl
      | inr m₂ => exact absurd hp (sum_composable_inl_inr_false Q₁ Q₂)
    | inr m₁ =>
      cases m₂ with
      | inl m₂ => exact absurd hp (sum_composable_inr_inl_false Q₁ Q₂)
      | inr m₂ => rfl

/-- The inverse natural transformation: Φ(C₁) ⊕ Φ(C₂) → Φ(C₁ ⊕ C₂). -/
def phiFunctorPreservesCoproductInv :
    CategoryJudgments.NatTransData
      (FunctorData.sum C₁.toJudgmentFunctorData C₂.toJudgmentFunctorData)
      (C₁.sum C₂).toJudgmentFunctorData where
  appObj := id
  appMor := id
  appId := id
  appComp := (phiSumCompIso C₁ C₂).symm
  naturality_dom := rfl
  naturality_cod := rfl
  naturality_idMor := by
    funext a
    cases a <;> simp [OverCategoryData.sum, FunctorData.sum,
      OverCategoryData.toJudgmentFunctorData]
  naturality_left := by funext p; cases p <;> rfl
  naturality_right := by funext p; cases p <;> rfl
  naturality_composite := by funext p; cases p <;> rfl

/-- The composite of the forward and inverse is the identity. -/
theorem phiFunctorPreservesCoproduct_comp_inv :
    CategoryJudgments.NatTransData.comp
      (phiFunctorPreservesCoproduct C₁ C₂)
      (phiFunctorPreservesCoproductInv C₁ C₂) =
    CategoryJudgments.NatTransData.id _ := by
  ext <;> simp [CategoryJudgments.NatTransData.comp,
    CategoryJudgments.NatTransData.id, phiFunctorPreservesCoproduct,
    phiFunctorPreservesCoproductInv, phiSumCompIso]

/-- The composite of the inverse and forward is the identity. -/
theorem phiFunctorPreservesCoproduct_inv_comp :
    CategoryJudgments.NatTransData.comp
      (phiFunctorPreservesCoproductInv C₁ C₂)
      (phiFunctorPreservesCoproduct C₁ C₂) =
    CategoryJudgments.NatTransData.id _ := by
  ext
  · rfl
  · rfl
  · rfl
  · rename_i a
    simp only [CategoryJudgments.NatTransData.comp,
      CategoryJudgments.NatTransData.id, phiFunctorPreservesCoproduct,
      phiFunctorPreservesCoproductInv, phiSumCompIso, types_comp_apply]
    exact sumComposablePairsEquiv.apply_symm_apply a

end BinaryCoproduct

/-!
## Binary Products

Binary products for categories and copresheaves. The product of categories
has pairs of objects and pairs of morphisms, with componentwise composition.
We prove that LFunctor preserves binary products.
-/

section BinaryProduct

universe uProd

variable (Q₁ Q₂ : OverQuiver.{uProd, uProd})

/-- The binary product of two OverQuivers has pairs of objects and morphisms. -/
def OverQuiver.prod : OverQuiver.{uProd, uProd} where
  Obj := Q₁.Obj × Q₂.Obj
  MorType := Q₁.MorType × Q₂.MorType
  src := fun p => (Q₁.src p.1, Q₂.src p.2)
  tgt := fun p => (Q₁.tgt p.1, Q₂.tgt p.2)

/-- Composability in a product quiver requires both components to be composable. -/
theorem prod_composable_iff {m₁ m₂ : (Q₁.prod Q₂).MorType} :
    (Q₁.prod Q₂).Composable m₁ m₂ ↔
      Q₁.Composable m₁.1 m₂.1 ∧ Q₂.Composable m₁.2 m₂.2 := by
  simp only [OverQuiver.Composable, OverQuiver.prod, Prod.ext_iff]

variable {Q₁ Q₂} (C₁ : OverCategoryData Q₁) (C₂ : OverCategoryData Q₂)

/-- The binary product of two OverCategoryData structures with componentwise ops. -/
def OverCategoryData.prod : OverCategoryData (Q₁.prod Q₂) where
  idFn := fun p => (C₁.idFn p.1, C₂.idFn p.2)
  compFn := fun ⟨p, hp⟩ =>
    let hp' := prod_composable_iff Q₁ Q₂ |>.mp hp
    (C₁.compFn ⟨(p.1.1, p.2.1), hp'.1⟩, C₂.compFn ⟨(p.1.2, p.2.2), hp'.2⟩)
  id_src := by
    intro p
    simp only [OverQuiver.prod]
    ext
    · exact C₁.id_src p.1
    · exact C₂.id_src p.2
  id_tgt := by
    intro p
    simp only [OverQuiver.prod]
    ext
    · exact C₁.id_tgt p.1
    · exact C₂.id_tgt p.2
  comp_src := by
    intro ⟨p, hp⟩
    simp only [OverQuiver.prod, OverQuiver.compPairFst]
    ext
    · exact C₁.comp_src ⟨(p.1.1, p.2.1), _⟩
    · exact C₂.comp_src ⟨(p.1.2, p.2.2), _⟩
  comp_tgt := by
    intro ⟨p, hp⟩
    simp only [OverQuiver.prod, OverQuiver.compPairSnd]
    ext
    · exact C₁.comp_tgt ⟨(p.1.1, p.2.1), _⟩
    · exact C₂.comp_tgt ⟨(p.1.2, p.2.2), _⟩
  id_comp := by
    intro f
    simp only [OverQuiver.prod]
    simp only [Prod.ext_iff]
    refine ⟨?_, ?_⟩
    · exact C₁.id_comp f.1
    · exact C₂.id_comp f.2
  comp_id := by
    intro f
    simp only [OverQuiver.prod]
    simp only [Prod.ext_iff]
    refine ⟨?_, ?_⟩
    · exact C₁.comp_id f.1
    · exact C₂.comp_id f.2
  assoc := by
    intro t
    let ⟨⟨f, g, h⟩, hfg, hgh⟩ := t
    simp only [OverQuiver.prod, OverQuiver.Composable, Prod.ext_iff] at hfg hgh
    have ⟨hfg1, hfg2⟩ := hfg
    have ⟨hgh1, hgh2⟩ := hgh
    have hax1 := C₁.assoc ⟨⟨f.1, g.1, h.1⟩, hfg1, hgh1⟩
    have hax2 := C₂.assoc ⟨⟨f.2, g.2, h.2⟩, hfg2, hgh2⟩
    simp only [OverQuiver.prod]
    ext
    · convert hax1 using 2
    · convert hax2 using 2

/-- The binary product of two FunctorData structures is computed pointwise. -/
def FunctorData.prod (F₁ F₂ : CategoryJudgments.FunctorData (Type u)) :
    CategoryJudgments.FunctorData (Type u) where
  objC := F₁.objC × F₂.objC
  morC := F₁.morC × F₂.morC
  idC := F₁.idC × F₂.idC
  compC := F₁.compC × F₂.compC
  dom := Prod.map F₁.dom F₂.dom
  cod := Prod.map F₁.cod F₂.cod
  idMor := Prod.map F₁.idMor F₂.idMor
  left := Prod.map F₁.left F₂.left
  right := Prod.map F₁.right F₂.right
  composite := Prod.map F₁.composite F₂.composite
  h_id_endo := by
    funext ⟨a₁, a₂⟩
    simp only [types_comp_apply, Prod.map_apply]
    exact Prod.ext (congrFun F₁.h_id_endo a₁) (congrFun F₂.h_id_endo a₂)
  h_comp_match := by
    funext ⟨c₁, c₂⟩
    simp only [types_comp_apply, Prod.map_apply]
    exact Prod.ext (congrFun F₁.h_comp_match c₁) (congrFun F₂.h_comp_match c₂)
  h_comp_dom := by
    funext ⟨c₁, c₂⟩
    simp only [types_comp_apply, Prod.map_apply]
    exact Prod.ext (congrFun F₁.h_comp_dom c₁) (congrFun F₂.h_comp_dom c₂)
  h_comp_cod := by
    funext ⟨c₁, c₂⟩
    simp only [types_comp_apply, Prod.map_apply]
    exact Prod.ext (congrFun F₁.h_comp_cod c₁) (congrFun F₂.h_comp_cod c₂)

variable (F₁ F₂ : CategoryJudgments.FunctorData (Type uProd))

/-- Abbreviation for the product copresheaf's CategoryQuotientData. -/
abbrev prodQuotData : CategoryQuotientData.{uProd, uProd} :=
  (FunctorData.prod F₁ F₂).toCategoryQuotientData

/-- Abbreviation for F₁'s CategoryQuotientData. -/
abbrev quotData₁ : CategoryQuotientData.{uProd, uProd} :=
  F₁.toCategoryQuotientData

/-- Abbreviation for F₂'s CategoryQuotientData. -/
abbrev quotData₂ : CategoryQuotientData.{uProd, uProd} :=
  F₂.toCategoryQuotientData

/-- The product quiver's source projects to the first component's source. -/
theorem prodQuiver_src_fst (f₁ : F₁.morC) (f₂ : F₂.morC) :
    ((prodQuotData F₁ F₂).quiver.src (f₁, f₂)).1 = (quotData₁ F₁).quiver.src f₁ := rfl

/-- The product quiver's target projects to the first component's target. -/
theorem prodQuiver_tgt_fst (f₁ : F₁.morC) (f₂ : F₂.morC) :
    ((prodQuotData F₁ F₂).quiver.tgt (f₁, f₂)).1 = (quotData₁ F₁).quiver.tgt f₁ := rfl

/-- The product quiver's source projects to the second component's source. -/
theorem prodQuiver_src_snd (f₁ : F₁.morC) (f₂ : F₂.morC) :
    ((prodQuotData F₁ F₂).quiver.src (f₁, f₂)).2 = (quotData₂ F₂).quiver.src f₂ := rfl

/-- The product quiver's target projects to the second component's target. -/
theorem prodQuiver_tgt_snd (f₁ : F₁.morC) (f₂ : F₂.morC) :
    ((prodQuotData F₁ F₂).quiver.tgt (f₁, f₂)).2 = (quotData₂ F₂).quiver.tgt f₂ := rfl

/-- The product's idObj projects to the first component's idObj. -/
theorem prodQuotData_idObj_fst (i₁ : F₁.idC) (i₂ : F₂.idC) :
    ((prodQuotData F₁ F₂).idObj (i₁, i₂)).1 = (quotData₁ F₁).idObj i₁ := rfl

/-- The product's idObj projects to the second component's idObj. -/
theorem prodQuotData_idObj_snd (i₁ : F₁.idC) (i₂ : F₂.idC) :
    ((prodQuotData F₁ F₂).idObj (i₁, i₂)).2 = (quotData₂ F₂).idObj i₂ := rfl

/-- The product's idMor projects to the first component's idMor. -/
theorem prodQuotData_idMor_fst (i₁ : F₁.idC) (i₂ : F₂.idC) :
    ((prodQuotData F₁ F₂).idMor (i₁, i₂)).1 = (quotData₁ F₁).idMor i₁ := rfl

/-- The product's idMor projects to the second component's idMor. -/
theorem prodQuotData_idMor_snd (i₁ : F₁.idC) (i₂ : F₂.idC) :
    ((prodQuotData F₁ F₂).idMor (i₁, i₂)).2 = (quotData₂ F₂).idMor i₂ := rfl

/-- The id_src proof for product projects to component id_src (first component). -/
theorem prodQuotData_id_src_fst (i₁ : F₁.idC) (i₂ : F₂.idC) :
    (Prod.ext_iff.mp ((prodQuotData F₁ F₂).id_src (i₁, i₂))).1 =
    (quotData₁ F₁).id_src i₁ := rfl

/-- The id_tgt proof for product projects to component id_tgt (first component). -/
theorem prodQuotData_id_tgt_fst (i₁ : F₁.idC) (i₂ : F₂.idC) :
    (Prod.ext_iff.mp ((prodQuotData F₁ F₂).id_tgt (i₁, i₂))).1 =
    (quotData₁ F₁).id_tgt i₁ := by
  simp only [CategoryJudgments.FunctorData.toCategoryQuotientData,
    FunctorData.prod, Prod.map_apply]

/-- The product's compLeft projects to the first component's compLeft. -/
theorem prodQuotData_compLeft_fst (c₁ : F₁.compC) (c₂ : F₂.compC) :
    ((prodQuotData F₁ F₂).compLeft (c₁, c₂)).1 = (quotData₁ F₁).compLeft c₁ := rfl

/-- The product's compRight projects to the first component's compRight. -/
theorem prodQuotData_compRight_fst (c₁ : F₁.compC) (c₂ : F₂.compC) :
    ((prodQuotData F₁ F₂).compRight (c₁, c₂)).1 = (quotData₁ F₁).compRight c₁ := rfl

/-- The product's compComposite projects to the first component's compComposite. -/
theorem prodQuotData_compComposite_fst (c₁ : F₁.compC) (c₂ : F₂.compC) :
    ((prodQuotData F₁ F₂).compComposite (c₁, c₂)).1 =
    (quotData₁ F₁).compComposite c₁ := rfl

/-- The product's comp_match projects to the first component's comp_match. -/
theorem prodQuotData_comp_match_fst (c₁ : F₁.compC) (c₂ : F₂.compC) :
    (Prod.ext_iff.mp ((prodQuotData F₁ F₂).comp_match (c₁, c₂))).1 =
    (quotData₁ F₁).comp_match c₁ := by
  simp only [CategoryJudgments.FunctorData.toCategoryQuotientData,
    FunctorData.prod, Prod.map_apply]

/-- Project a free morphism in the product quiver to the first component. -/
def freeMorProj₁ {a b : (prodQuotData F₁ F₂).quiver.Obj}
    (m : FreeMor (prodQuotData F₁ F₂).quiver a b) :
    FreeMor (quotData₁ F₁).quiver a.1 b.1 :=
  match m with
  | .var (f₁, f₂) =>
    (prodQuiver_src_fst F₁ F₂ f₁ f₂) ▸ (prodQuiver_tgt_fst F₁ F₂ f₁ f₂) ▸
      FreeMor.var (Q := (quotData₁ F₁).quiver) f₁
  | .id _ => .id _
  | .comp g f => .comp (freeMorProj₁ g) (freeMorProj₁ f)

/-- Project a free morphism in the product quiver to the second component. -/
def freeMorProj₂ {a b : (prodQuotData F₁ F₂).quiver.Obj}
    (m : FreeMor (prodQuotData F₁ F₂).quiver a b) :
    FreeMor (quotData₂ F₂).quiver a.2 b.2 :=
  match m with
  | .var (f₁, f₂) =>
    (prodQuiver_src_snd F₁ F₂ f₁ f₂) ▸ (prodQuiver_tgt_snd F₁ F₂ f₁ f₂) ▸
      FreeMor.var (Q := (quotData₂ F₂).quiver) f₂
  | .id _ => .id _
  | .comp g f => .comp (freeMorProj₂ g) (freeMorProj₂ f)

/-- Helper: freeMorProj₂ on id case. -/
@[simp]
theorem freeMorProj₂_id (a : (prodQuotData F₁ F₂).quiver.Obj) :
    freeMorProj₂ F₁ F₂ (FreeMor.id a) = FreeMor.id (Q := (quotData₂ F₂).quiver) a.2 :=
  rfl

/-- Since prodQuiver_src_snd and prodQuiver_tgt_snd are rfl, freeMorProj₂ on var simplifies. -/
@[simp]
theorem freeMorProj₂_var_simple (f₁ : F₁.morC) (f₂ : F₂.morC) :
    freeMorProj₂ F₁ F₂ (FreeMor.var (f₁, f₂)) =
    FreeMor.var (Q := (quotData₂ F₂).quiver) f₂ := rfl

/-- HEq congruence for freeMorProj₂: projecting HEq-related morphisms gives HEq results. -/
theorem freeMorProj₂_heq {a₁ b₁ a₂ b₂ : (prodQuotData F₁ F₂).quiver.Obj}
    {m₁ : FreeMor (prodQuotData F₁ F₂).quiver a₁ b₁}
    {m₂ : FreeMor (prodQuotData F₁ F₂).quiver a₂ b₂}
    (ha : a₁ = a₂) (hb : b₁ = b₂) (hm : HEq m₁ m₂) :
    HEq (freeMorProj₂ F₁ F₂ m₁) (freeMorProj₂ F₁ F₂ m₂) := by
  cases ha
  cases hb
  cases eq_of_heq hm
  rfl

/-- Helper: freeMorProj₂ applied to cast of var equals cast of var projection.
    This shows that projection commutes with cast for var terms in the id_witness case. -/
theorem freeMorProj₂_cast_id_var (i₁ : F₁.idC) (i₂ : F₂.idC) :
    HEq
      (freeMorProj₂ F₁ F₂
        (cast (by rw [(prodQuotData F₁ F₂).id_src (i₁, i₂),
                      (prodQuotData F₁ F₂).id_tgt (i₁, i₂)])
          (FreeMor.var ((prodQuotData F₁ F₂).idMor (i₁, i₂)))))
      (cast (by rw [(quotData₂ F₂).id_src i₂, (quotData₂ F₂).id_tgt i₂])
        (FreeMor.var ((quotData₂ F₂).idMor i₂))) := by
  have h_lhs_cast : HEq
      (cast (by rw [(prodQuotData F₁ F₂).id_src (i₁, i₂),
                    (prodQuotData F₁ F₂).id_tgt (i₁, i₂)])
        (FreeMor.var ((prodQuotData F₁ F₂).idMor (i₁, i₂))))
      (FreeMor.var ((prodQuotData F₁ F₂).idMor (i₁, i₂))) := cast_heq _ _
  have h_proj_heq : HEq
      (freeMorProj₂ F₁ F₂
        (cast (by rw [(prodQuotData F₁ F₂).id_src (i₁, i₂),
                      (prodQuotData F₁ F₂).id_tgt (i₁, i₂)])
          (FreeMor.var ((prodQuotData F₁ F₂).idMor (i₁, i₂)))))
      (freeMorProj₂ F₁ F₂ (FreeMor.var ((prodQuotData F₁ F₂).idMor (i₁, i₂)))) :=
    freeMorProj₂_heq F₁ F₂
      ((prodQuotData F₁ F₂).id_src (i₁, i₂)).symm
      ((prodQuotData F₁ F₂).id_tgt (i₁, i₂)).symm
      h_lhs_cast
  have h_rhs_cast : HEq
      (cast (by rw [(quotData₂ F₂).id_src i₂, (quotData₂ F₂).id_tgt i₂])
        (FreeMor.var ((quotData₂ F₂).idMor i₂)))
      (FreeMor.var (Q := (quotData₂ F₂).quiver) ((quotData₂ F₂).idMor i₂)) :=
    cast_heq _ _
  exact h_proj_heq.trans h_rhs_cast.symm

/-- Step A for id_witness on proj₂: The LHS (cast var) projects to something equiv to id. -/
theorem freeMorProj₂_id_witness_stepA (i : (prodQuotData F₁ F₂).IdWitness) :
    CategoryQuotientData.FreeMorEquiv (quotData₂ F₂)
      (freeMorProj₂ F₁ F₂
        (cast (by rw [(prodQuotData F₁ F₂).id_src i, (prodQuotData F₁ F₂).id_tgt i])
          (FreeMor.var ((prodQuotData F₁ F₂).idMor i))))
      (FreeMor.id (Q := (quotData₂ F₂).quiver) (((prodQuotData F₁ F₂).idObj i).2)) := by
  rcases i with ⟨i₁, i₂⟩
  convert CategoryQuotientData.FreeMorEquiv.rel
    (@CategoryQuotientData.FreeMorEquivGen.id_witness (quotData₂ F₂) i₂) using 2
  exact eq_of_heq (freeMorProj₂_cast_id_var F₁ F₂ i₁ i₂)

/-- Step B for id_witness on proj₂: FreeMor.id projects to itself. -/
theorem freeMorProj₂_id_witness_stepB (i : (prodQuotData F₁ F₂).IdWitness) :
    CategoryQuotientData.FreeMorEquiv (quotData₂ F₂)
      (FreeMor.id (Q := (quotData₂ F₂).quiver) (((prodQuotData F₁ F₂).idObj i).2))
      (freeMorProj₂ F₁ F₂ (FreeMor.id ((prodQuotData F₁ F₂).idObj i))) := by
  simp only [freeMorProj₂_id]
  exact CategoryQuotientData.FreeMorEquiv.refl _

/-- Full proof for id_witness case on proj₂. -/
theorem freeMorProj₂_respects_id_witness (i : (prodQuotData F₁ F₂).IdWitness) :
    CategoryQuotientData.FreeMorEquiv (quotData₂ F₂)
      (freeMorProj₂ F₁ F₂
        (cast (by rw [(prodQuotData F₁ F₂).id_src i, (prodQuotData F₁ F₂).id_tgt i])
          (FreeMor.var ((prodQuotData F₁ F₂).idMor i))))
      (freeMorProj₂ F₁ F₂ (FreeMor.id ((prodQuotData F₁ F₂).idObj i))) :=
  CategoryQuotientData.FreeMorEquiv.trans
    (freeMorProj₂_id_witness_stepA F₁ F₂ i)
    (freeMorProj₂_id_witness_stepB F₁ F₂ i)

/-- Helper: freeMorProj₁ on id case. -/
@[simp]
theorem freeMorProj₁_id (a : (prodQuotData F₁ F₂).quiver.Obj) :
    freeMorProj₁ F₁ F₂ (FreeMor.id a) = FreeMor.id (Q := (quotData₁ F₁).quiver) a.1 :=
  rfl

/-- Helper: freeMorProj₁ on var case. -/
theorem freeMorProj₁_var (f₁ : F₁.morC) (f₂ : F₂.morC) :
    freeMorProj₁ F₁ F₂ (FreeMor.var (f₁, f₂)) =
    (prodQuiver_src_fst F₁ F₂ f₁ f₂) ▸ (prodQuiver_tgt_fst F₁ F₂ f₁ f₂) ▸
      FreeMor.var (Q := (quotData₁ F₁).quiver) f₁ := rfl

/-- Since prodQuiver_src_fst and prodQuiver_tgt_fst are rfl, freeMorProj₁ on var simplifies. -/
@[simp]
theorem freeMorProj₁_var_simple (f₁ : F₁.morC) (f₂ : F₂.morC) :
    freeMorProj₁ F₁ F₂ (FreeMor.var (f₁, f₂)) =
    FreeMor.var (Q := (quotData₁ F₁).quiver) f₁ := rfl

/-- freeMorProj₁ commutes with transport operations on var terms. -/
theorem freeMorProj₁_cast_var
    {a b : (prodQuotData F₁ F₂).quiver.Obj}
    (f₁ : F₁.morC) (f₂ : F₂.morC)
    (hsrc : (prodQuotData F₁ F₂).quiver.src (f₁, f₂) = a)
    (htgt : (prodQuotData F₁ F₂).quiver.tgt (f₁, f₂) = b) :
    freeMorProj₁ F₁ F₂
      (hsrc ▸ htgt ▸ FreeMor.var (Q := (prodQuotData F₁ F₂).quiver) (f₁, f₂)) =
    (congrArg Prod.fst hsrc) ▸ (congrArg Prod.fst htgt) ▸
      FreeMor.var (Q := (quotData₁ F₁).quiver) f₁ := by
  cases hsrc
  cases htgt
  rfl

-- Factored lemmas for id_witness and comp_witness cases.
-- Following the factoring-into-lemmas technique: define lemmas with underscores,
-- use them in the main proof to verify they fit, then fill in proofs.
-- The lemma types are crafted to match the exact goal types from the main proof.

/-- The product's idObj first component equals the component's idObj.
    This is definitionally equal but we state it explicitly for clarity. -/
theorem prodQuotData_idObj_fst_eq (i : (prodQuotData F₁ F₂).IdWitness) :
    ((prodQuotData F₁ F₂).idObj i).1 = (quotData₁ F₁).idObj i.1 := rfl

/-- HEq congruence for freeMorProj₁: projecting HEq-related morphisms gives HEq results. -/
theorem freeMorProj₁_heq {a₁ b₁ a₂ b₂ : (prodQuotData F₁ F₂).quiver.Obj}
    {m₁ : FreeMor (prodQuotData F₁ F₂).quiver a₁ b₁}
    {m₂ : FreeMor (prodQuotData F₁ F₂).quiver a₂ b₂}
    (ha : a₁ = a₂) (hb : b₁ = b₂) (hm : HEq m₁ m₂) :
    HEq (freeMorProj₁ F₁ F₂ m₁) (freeMorProj₁ F₁ F₂ m₂) := by
  cases ha
  cases hb
  cases eq_of_heq hm
  rfl

/-- Helper: freeMorProj₁ applied to cast of var equals cast of var projection.
    This shows that projection commutes with cast for var terms in the id_witness case. -/
theorem freeMorProj₁_cast_id_var (i₁ : F₁.idC) (i₂ : F₂.idC) :
    HEq
      (freeMorProj₁ F₁ F₂
        (cast (by rw [(prodQuotData F₁ F₂).id_src (i₁, i₂),
                      (prodQuotData F₁ F₂).id_tgt (i₁, i₂)])
          (FreeMor.var ((prodQuotData F₁ F₂).idMor (i₁, i₂)))))
      (cast (by rw [(quotData₁ F₁).id_src i₁, (quotData₁ F₁).id_tgt i₁])
        (FreeMor.var ((quotData₁ F₁).idMor i₁))) := by
  -- Strategy: Both sides are HEq to FreeMor.var ((quotData₁ F₁).idMor i₁).
  -- Use cast_heq to relate cast terms to their uncast forms, then show the
  -- uncast forms are equal (freeMorProj₁ (var (m₁,m₂)) = var m₁).

  -- Step 1: LHS cast is HEq to its uncast form
  have h_lhs_cast : HEq
      (cast (by rw [(prodQuotData F₁ F₂).id_src (i₁, i₂),
                    (prodQuotData F₁ F₂).id_tgt (i₁, i₂)])
        (FreeMor.var ((prodQuotData F₁ F₂).idMor (i₁, i₂))))
      (FreeMor.var ((prodQuotData F₁ F₂).idMor (i₁, i₂))) := cast_heq _ _
  -- Step 2: Apply freeMorProj₁_heq to get HEq between freeMorProj₁ applications
  -- Note: need .symm since id_src says src = idObj, but we need idObj = src
  have h_proj_heq : HEq
      (freeMorProj₁ F₁ F₂
        (cast (by rw [(prodQuotData F₁ F₂).id_src (i₁, i₂),
                      (prodQuotData F₁ F₂).id_tgt (i₁, i₂)])
          (FreeMor.var ((prodQuotData F₁ F₂).idMor (i₁, i₂)))))
      (freeMorProj₁ F₁ F₂ (FreeMor.var ((prodQuotData F₁ F₂).idMor (i₁, i₂)))) :=
    freeMorProj₁_heq F₁ F₂
      ((prodQuotData F₁ F₂).id_src (i₁, i₂)).symm
      ((prodQuotData F₁ F₂).id_tgt (i₁, i₂)).symm
      h_lhs_cast
  -- Step 3: freeMorProj₁ (var (m₁, m₂)) = var m₁ by freeMorProj₁_var_simple
  -- So h_proj_heq gives: LHS HEq var (idMor i₁)

  -- Step 4: RHS cast is HEq to var (idMor i₁)
  have h_rhs_cast : HEq
      (cast (by rw [(quotData₁ F₁).id_src i₁, (quotData₁ F₁).id_tgt i₁])
        (FreeMor.var ((quotData₁ F₁).idMor i₁)))
      (FreeMor.var (Q := (quotData₁ F₁).quiver) ((quotData₁ F₁).idMor i₁)) :=
    cast_heq _ _
  -- Step 5: Combine: LHS HEq var m₁ HEq RHS
  exact h_proj_heq.trans h_rhs_cast.symm

/-- Step A for id_witness: The LHS (cast var) projects to something equiv to id.
    The proof works by showing both sides are FreeMorEquiv to the uncast var form. -/
theorem freeMorProj₁_id_witness_stepA (i : (prodQuotData F₁ F₂).IdWitness) :
    CategoryQuotientData.FreeMorEquiv (quotData₁ F₁)
      (freeMorProj₁ F₁ F₂
        (cast (by rw [(prodQuotData F₁ F₂).id_src i, (prodQuotData F₁ F₂).id_tgt i])
          (FreeMor.var ((prodQuotData F₁ F₂).idMor i))))
      (FreeMor.id (Q := (quotData₁ F₁).quiver) (((prodQuotData F₁ F₂).idObj i).1)) := by
  rcases i with ⟨i₁, i₂⟩
  -- Use convert to match against the component's id_witness generator.
  convert CategoryQuotientData.FreeMorEquiv.rel
    (@CategoryQuotientData.FreeMorEquivGen.id_witness (quotData₁ F₁) i₁) using 2
  -- Use the helper lemma with eq_of_heq since the types are equal
  exact eq_of_heq (freeMorProj₁_cast_id_var F₁ F₂ i₁ i₂)

/-- Step B for id_witness: FreeMor.id projects to itself via id_witness symmetry.
    Since stepA shows LHS ~ FreeMor.id and RHS = FreeMor.id, we use refl. -/
theorem freeMorProj₁_id_witness_stepB (i : (prodQuotData F₁ F₂).IdWitness) :
    CategoryQuotientData.FreeMorEquiv (quotData₁ F₁)
      (FreeMor.id (Q := (quotData₁ F₁).quiver) (((prodQuotData F₁ F₂).idObj i).1))
      (freeMorProj₁ F₁ F₂ (FreeMor.id ((prodQuotData F₁ F₂).idObj i))) := by
  -- RHS = FreeMor.id ((prodQuotData F₁ F₂).idObj i).1 by definition of freeMorProj₁
  simp only [freeMorProj₁_id]
  -- Now both sides are FreeMor.id at the same index, so use refl.
  exact CategoryQuotientData.FreeMorEquiv.refl _

/-- Full proof for id_witness case via transitivity of stepA and stepB. -/
theorem freeMorProj₁_respects_id_witness (i : (prodQuotData F₁ F₂).IdWitness) :
    CategoryQuotientData.FreeMorEquiv (quotData₁ F₁)
      (freeMorProj₁ F₁ F₂
        (cast (by rw [(prodQuotData F₁ F₂).id_src i, (prodQuotData F₁ F₂).id_tgt i])
          (FreeMor.var ((prodQuotData F₁ F₂).idMor i))))
      (freeMorProj₁ F₁ F₂ (FreeMor.id ((prodQuotData F₁ F₂).idObj i))) :=
  CategoryQuotientData.FreeMorEquiv.trans
    (freeMorProj₁_id_witness_stepA F₁ F₂ i)
    (freeMorProj₁_id_witness_stepB F₁ F₂ i)

/-- freeMorProj₁ of a cast-comp term reduces to a comp of projections.
    Both projections are FreeMorEquiv to the component's comp_witness form.
    Strategy: use freeMorProj₁_heq with cast_heq to relate through the uncast forms. -/
theorem freeMorProj₁_comp_left_heq (c₁ : F₁.compC) (c₂ : F₂.compC) :
    HEq
      (freeMorProj₁ F₁ F₂ (FreeMor.var ((prodQuotData F₁ F₂).compLeft (c₁, c₂))))
      (FreeMor.var (Q := (quotData₁ F₁).quiver) ((quotData₁ F₁).compLeft c₁)) :=
  HEq.refl _

/-- freeMorProj₁ of compRight var is HEq to the component's compRight var. -/
theorem freeMorProj₁_comp_right_heq (c₁ : F₁.compC) (c₂ : F₂.compC) :
    HEq
      (freeMorProj₁ F₁ F₂ (FreeMor.var ((prodQuotData F₁ F₂).compRight (c₁, c₂))))
      (FreeMor.var (Q := (quotData₁ F₁).quiver) ((quotData₁ F₁).compRight c₁)) :=
  HEq.refl _

/-- freeMorProj₁ of compComposite var is HEq to the component's compComposite var. -/
theorem freeMorProj₁_comp_composite_heq (c₁ : F₁.compC) (c₂ : F₂.compC) :
    HEq
      (freeMorProj₁ F₁ F₂ (FreeMor.var ((prodQuotData F₁ F₂).compComposite (c₁, c₂))))
      (FreeMor.var (Q := (quotData₁ F₁).quiver) ((quotData₁ F₁).compComposite c₁)) :=
  HEq.refl _

/-- The cast proof for comp_match on the product.
    comp_match c : tgt compRight = src compLeft.
    We need to cast var compLeft from source at (src compLeft) to source at (tgt compRight)
    so it can compose with var compRight (which has target at tgt compRight). -/
def prodCompMatchCast (c₁ : F₁.compC) (c₂ : F₂.compC) :
    FreeMor (prodQuotData F₁ F₂).quiver
      ((prodQuotData F₁ F₂).quiver.src ((prodQuotData F₁ F₂).compLeft (c₁, c₂)))
      ((prodQuotData F₁ F₂).quiver.tgt ((prodQuotData F₁ F₂).compLeft (c₁, c₂))) =
    FreeMor (prodQuotData F₁ F₂).quiver
      ((prodQuotData F₁ F₂).quiver.tgt ((prodQuotData F₁ F₂).compRight (c₁, c₂)))
      ((prodQuotData F₁ F₂).quiver.tgt ((prodQuotData F₁ F₂).compLeft (c₁, c₂))) :=
  congrArg
    (fun x => FreeMor (prodQuotData F₁ F₂).quiver x
      ((prodQuotData F₁ F₂).quiver.tgt ((prodQuotData F₁ F₂).compLeft (c₁, c₂))))
    ((prodQuotData F₁ F₂).comp_match (c₁, c₂)).symm

/-- The cast proof for comp_dom/comp_cod on the product.
    comp_dom c : src compComposite = src compRight.
    comp_cod c : tgt compComposite = tgt compLeft. -/
def prodCompDomCodCast (c₁ : F₁.compC) (c₂ : F₂.compC) :
    FreeMor (prodQuotData F₁ F₂).quiver
      ((prodQuotData F₁ F₂).quiver.src ((prodQuotData F₁ F₂).compComposite (c₁, c₂)))
      ((prodQuotData F₁ F₂).quiver.tgt ((prodQuotData F₁ F₂).compComposite (c₁, c₂))) =
    FreeMor (prodQuotData F₁ F₂).quiver
      ((prodQuotData F₁ F₂).quiver.src ((prodQuotData F₁ F₂).compRight (c₁, c₂)))
      ((prodQuotData F₁ F₂).quiver.tgt ((prodQuotData F₁ F₂).compLeft (c₁, c₂))) :=
  congrArg₂
    (FreeMor (prodQuotData F₁ F₂).quiver)
    ((prodQuotData F₁ F₂).comp_dom (c₁, c₂))
    ((prodQuotData F₁ F₂).comp_cod (c₁, c₂))

/-- Helper: freeMorProj₁ applied to cast of compLeft var equals cast of compLeft projection.
    This shows projection commutes with cast for compLeft in comp_witness case. -/
theorem freeMorProj₁_cast_compLeft_var (c₁ : F₁.compC) (c₂ : F₂.compC) :
    HEq
      (freeMorProj₁ F₁ F₂
        (cast (prodCompMatchCast F₁ F₂ c₁ c₂)
          (FreeMor.var ((prodQuotData F₁ F₂).compLeft (c₁, c₂)))))
      (cast (by rw [← (quotData₁ F₁).comp_match c₁])
        (FreeMor.var ((quotData₁ F₁).compLeft c₁))) := by
  -- Strategy: Both sides are HEq to FreeMor.var ((quotData₁ F₁).compLeft c₁).
  -- Use cast_heq to relate cast terms to their uncast forms.
  have h_lhs_cast : HEq
      (cast (prodCompMatchCast F₁ F₂ c₁ c₂)
        (FreeMor.var ((prodQuotData F₁ F₂).compLeft (c₁, c₂))))
      (FreeMor.var ((prodQuotData F₁ F₂).compLeft (c₁, c₂))) := cast_heq _ _
  have h_proj_heq : HEq
      (freeMorProj₁ F₁ F₂
        (cast (prodCompMatchCast F₁ F₂ c₁ c₂)
          (FreeMor.var ((prodQuotData F₁ F₂).compLeft (c₁, c₂)))))
      (freeMorProj₁ F₁ F₂ (FreeMor.var ((prodQuotData F₁ F₂).compLeft (c₁, c₂)))) :=
    freeMorProj₁_heq F₁ F₂
      ((prodQuotData F₁ F₂).comp_match (c₁, c₂))
      rfl
      h_lhs_cast
  have h_rhs_cast : HEq
      (cast (by rw [← (quotData₁ F₁).comp_match c₁])
        (FreeMor.var ((quotData₁ F₁).compLeft c₁)))
      (FreeMor.var (Q := (quotData₁ F₁).quiver) ((quotData₁ F₁).compLeft c₁)) :=
    cast_heq _ _
  exact h_proj_heq.trans h_rhs_cast.symm

/-- Helper: freeMorProj₁ applied to cast of compComposite var equals cast projection. -/
theorem freeMorProj₁_cast_compComposite_var (c₁ : F₁.compC) (c₂ : F₂.compC) :
    HEq
      (freeMorProj₁ F₁ F₂
        (cast (prodCompDomCodCast F₁ F₂ c₁ c₂)
          (FreeMor.var ((prodQuotData F₁ F₂).compComposite (c₁, c₂)))))
      (cast (by rw [(quotData₁ F₁).comp_dom c₁, (quotData₁ F₁).comp_cod c₁])
        (FreeMor.var ((quotData₁ F₁).compComposite c₁))) := by
  have h_lhs_cast : HEq
      (cast (prodCompDomCodCast F₁ F₂ c₁ c₂)
        (FreeMor.var ((prodQuotData F₁ F₂).compComposite (c₁, c₂))))
      (FreeMor.var ((prodQuotData F₁ F₂).compComposite (c₁, c₂))) := cast_heq _ _
  have h_proj_heq : HEq
      (freeMorProj₁ F₁ F₂
        (cast (prodCompDomCodCast F₁ F₂ c₁ c₂)
          (FreeMor.var ((prodQuotData F₁ F₂).compComposite (c₁, c₂)))))
      (freeMorProj₁ F₁ F₂ (FreeMor.var ((prodQuotData F₁ F₂).compComposite (c₁, c₂)))) :=
    freeMorProj₁_heq F₁ F₂
      ((prodQuotData F₁ F₂).comp_dom (c₁, c₂)).symm
      ((prodQuotData F₁ F₂).comp_cod (c₁, c₂)).symm
      h_lhs_cast
  have h_rhs_cast : HEq
      (cast (by rw [(quotData₁ F₁).comp_dom c₁, (quotData₁ F₁).comp_cod c₁])
        (FreeMor.var ((quotData₁ F₁).compComposite c₁)))
      (FreeMor.var (Q := (quotData₁ F₁).quiver) ((quotData₁ F₁).compComposite c₁)) :=
    cast_heq _ _
  exact h_proj_heq.trans h_rhs_cast.symm

/-- The first projection respects comp_witness: projects product comp_witness to
    component comp_witness. Uses HEq reasoning through casts similar to id_witness. -/
theorem freeMorProj₁_respects_comp_witness (c₁ : F₁.compC) (c₂ : F₂.compC) :
    CategoryQuotientData.FreeMorEquiv (quotData₁ F₁)
      (freeMorProj₁ F₁ F₂
        (FreeMor.comp
          (cast (prodCompMatchCast F₁ F₂ c₁ c₂)
            (FreeMor.var ((prodQuotData F₁ F₂).compLeft (c₁, c₂))))
          (FreeMor.var ((prodQuotData F₁ F₂).compRight (c₁, c₂)))))
      (freeMorProj₁ F₁ F₂
        (cast (prodCompDomCodCast F₁ F₂ c₁ c₂)
          (FreeMor.var ((prodQuotData F₁ F₂).compComposite (c₁, c₂))))) := by
  -- freeMorProj₁ distributes over comp
  simp only [freeMorProj₁]
  -- Use convert to match the component's comp_witness generator
  convert CategoryQuotientData.FreeMorEquiv.rel
    (@CategoryQuotientData.FreeMorEquivGen.comp_witness (quotData₁ F₁) c₁) using 2
  · -- LHS: show projected composition matches comp_witness LHS
    -- freeMorProj₁ (cast ... (var compLeft)) HEq cast ... (var compLeft_c₁)
    -- freeMorProj₁ (var compRight) = var compRight_c₁ definitionally
    exact eq_of_heq (freeMorProj₁_cast_compLeft_var F₁ F₂ c₁ c₂)
  · -- RHS: show projected composite matches comp_witness RHS
    exact eq_of_heq (freeMorProj₁_cast_compComposite_var F₁ F₂ c₁ c₂)

/-- Helper: freeMorProj₂ applied to cast of compLeft var equals cast of projection. -/
theorem freeMorProj₂_cast_compLeft_var (c₁ : F₁.compC) (c₂ : F₂.compC) :
    HEq
      (freeMorProj₂ F₁ F₂
        (cast (prodCompMatchCast F₁ F₂ c₁ c₂)
          (FreeMor.var ((prodQuotData F₁ F₂).compLeft (c₁, c₂)))))
      (cast (by rw [← (quotData₂ F₂).comp_match c₂])
        (FreeMor.var ((quotData₂ F₂).compLeft c₂))) := by
  have h_lhs_cast : HEq
      (cast (prodCompMatchCast F₁ F₂ c₁ c₂)
        (FreeMor.var ((prodQuotData F₁ F₂).compLeft (c₁, c₂))))
      (FreeMor.var ((prodQuotData F₁ F₂).compLeft (c₁, c₂))) := cast_heq _ _
  have h_proj_heq : HEq
      (freeMorProj₂ F₁ F₂
        (cast (prodCompMatchCast F₁ F₂ c₁ c₂)
          (FreeMor.var ((prodQuotData F₁ F₂).compLeft (c₁, c₂)))))
      (freeMorProj₂ F₁ F₂ (FreeMor.var ((prodQuotData F₁ F₂).compLeft (c₁, c₂)))) :=
    freeMorProj₂_heq F₁ F₂
      ((prodQuotData F₁ F₂).comp_match (c₁, c₂))
      rfl
      h_lhs_cast
  have h_rhs_cast : HEq
      (cast (by rw [← (quotData₂ F₂).comp_match c₂])
        (FreeMor.var ((quotData₂ F₂).compLeft c₂)))
      (FreeMor.var (Q := (quotData₂ F₂).quiver) ((quotData₂ F₂).compLeft c₂)) :=
    cast_heq _ _
  exact h_proj_heq.trans h_rhs_cast.symm

/-- Helper: freeMorProj₂ applied to cast of compComposite var equals cast projection. -/
theorem freeMorProj₂_cast_compComposite_var (c₁ : F₁.compC) (c₂ : F₂.compC) :
    HEq
      (freeMorProj₂ F₁ F₂
        (cast (prodCompDomCodCast F₁ F₂ c₁ c₂)
          (FreeMor.var ((prodQuotData F₁ F₂).compComposite (c₁, c₂)))))
      (cast (by rw [(quotData₂ F₂).comp_dom c₂, (quotData₂ F₂).comp_cod c₂])
        (FreeMor.var ((quotData₂ F₂).compComposite c₂))) := by
  have h_lhs_cast : HEq
      (cast (prodCompDomCodCast F₁ F₂ c₁ c₂)
        (FreeMor.var ((prodQuotData F₁ F₂).compComposite (c₁, c₂))))
      (FreeMor.var ((prodQuotData F₁ F₂).compComposite (c₁, c₂))) := cast_heq _ _
  have h_proj_heq : HEq
      (freeMorProj₂ F₁ F₂
        (cast (prodCompDomCodCast F₁ F₂ c₁ c₂)
          (FreeMor.var ((prodQuotData F₁ F₂).compComposite (c₁, c₂)))))
      (freeMorProj₂ F₁ F₂ (FreeMor.var ((prodQuotData F₁ F₂).compComposite (c₁, c₂)))) :=
    freeMorProj₂_heq F₁ F₂
      ((prodQuotData F₁ F₂).comp_dom (c₁, c₂)).symm
      ((prodQuotData F₁ F₂).comp_cod (c₁, c₂)).symm
      h_lhs_cast
  have h_rhs_cast : HEq
      (cast (by rw [(quotData₂ F₂).comp_dom c₂, (quotData₂ F₂).comp_cod c₂])
        (FreeMor.var ((quotData₂ F₂).compComposite c₂)))
      (FreeMor.var (Q := (quotData₂ F₂).quiver) ((quotData₂ F₂).compComposite c₂)) :=
    cast_heq _ _
  exact h_proj_heq.trans h_rhs_cast.symm

/-- The second projection respects comp_witness: projects product comp_witness to
    component comp_witness. -/
theorem freeMorProj₂_respects_comp_witness (c₁ : F₁.compC) (c₂ : F₂.compC) :
    CategoryQuotientData.FreeMorEquiv (quotData₂ F₂)
      (freeMorProj₂ F₁ F₂
        (FreeMor.comp
          (cast (prodCompMatchCast F₁ F₂ c₁ c₂)
            (FreeMor.var ((prodQuotData F₁ F₂).compLeft (c₁, c₂))))
          (FreeMor.var ((prodQuotData F₁ F₂).compRight (c₁, c₂)))))
      (freeMorProj₂ F₁ F₂
        (cast (prodCompDomCodCast F₁ F₂ c₁ c₂)
          (FreeMor.var ((prodQuotData F₁ F₂).compComposite (c₁, c₂))))) := by
  simp only [freeMorProj₂]
  convert CategoryQuotientData.FreeMorEquiv.rel
    (@CategoryQuotientData.FreeMorEquivGen.comp_witness (quotData₂ F₂) c₂) using 2
  · exact eq_of_heq (freeMorProj₂_cast_compLeft_var F₁ F₂ c₁ c₂)
  · exact eq_of_heq (freeMorProj₂_cast_compComposite_var F₁ F₂ c₁ c₂)

/-- The first projection respects the equivalence relation generators. -/
theorem freeMorProj₁_respects_gen {a b : (prodQuotData F₁ F₂).quiver.Obj}
    {m₁ m₂ : FreeMor (prodQuotData F₁ F₂).quiver a b}
    (h : CategoryQuotientData.FreeMorEquivGen (prodQuotData F₁ F₂) m₁ m₂) :
    CategoryQuotientData.FreeMorEquiv (quotData₁ F₁)
      (freeMorProj₁ F₁ F₂ m₁) (freeMorProj₁ F₁ F₂ m₂) := by
  induction h with
  | id_left f =>
    exact CategoryQuotientData.FreeMorEquiv.rel
      (CategoryQuotientData.FreeMorEquivGen.id_left _)
  | id_right f =>
    exact CategoryQuotientData.FreeMorEquiv.rel
      (CategoryQuotientData.FreeMorEquivGen.id_right _)
  | assoc h g f =>
    exact CategoryQuotientData.FreeMorEquiv.rel
      (CategoryQuotientData.FreeMorEquivGen.assoc _ _ _)
  | id_witness i =>
    exact freeMorProj₁_respects_id_witness F₁ F₂ i
  | comp_witness c =>
    exact freeMorProj₁_respects_comp_witness F₁ F₂ c.1 c.2
  | cong_left h hfg ih =>
    exact CategoryQuotientData.FreeMorEquiv.cong_left
      (D := quotData₁ F₁) (freeMorProj₁ F₁ F₂ h) ih
  | cong_right k hfg ih =>
    exact CategoryQuotientData.FreeMorEquiv.cong_right
      (D := quotData₁ F₁) (freeMorProj₁ F₁ F₂ k) ih

/-- The first projection respects the full equivalence relation. -/
theorem freeMorProj₁_respects_equiv {a b : (prodQuotData F₁ F₂).quiver.Obj}
    {m₁ m₂ : FreeMor (prodQuotData F₁ F₂).quiver a b}
    (h : CategoryQuotientData.FreeMorEquiv (prodQuotData F₁ F₂) m₁ m₂) :
    CategoryQuotientData.FreeMorEquiv (quotData₁ F₁)
      (freeMorProj₁ F₁ F₂ m₁) (freeMorProj₁ F₁ F₂ m₂) := by
  induction h with
  | rel hgen => exact freeMorProj₁_respects_gen F₁ F₂ hgen
  | refl m => exact CategoryQuotientData.FreeMorEquiv.refl _
  | symm _ ih => exact CategoryQuotientData.FreeMorEquiv.symm ih
  | trans _ _ ih1 ih2 => exact CategoryQuotientData.FreeMorEquiv.trans ih1 ih2

/-- freeMorProj₂ respects generators (symmetric to freeMorProj₁).
    Note: Returns FreeMorEquiv since the witness cases need additional work. -/
theorem freeMorProj₂_respects_gen {a b : (prodQuotData F₁ F₂).quiver.Obj}
    {m₁ m₂ : FreeMor (prodQuotData F₁ F₂).quiver a b}
    (h : (prodQuotData F₁ F₂).FreeMorEquivGen m₁ m₂) :
    CategoryQuotientData.FreeMorEquiv (quotData₂ F₂)
      (freeMorProj₂ F₁ F₂ m₁) (freeMorProj₂ F₁ F₂ m₂) := by
  induction h with
  | id_left f =>
    exact CategoryQuotientData.FreeMorEquiv.rel
      (CategoryQuotientData.FreeMorEquivGen.id_left _)
  | id_right f =>
    exact CategoryQuotientData.FreeMorEquiv.rel
      (CategoryQuotientData.FreeMorEquivGen.id_right _)
  | assoc h g f =>
    exact CategoryQuotientData.FreeMorEquiv.rel
      (CategoryQuotientData.FreeMorEquivGen.assoc _ _ _)
  | id_witness i =>
    exact freeMorProj₂_respects_id_witness F₁ F₂ i
  | comp_witness c =>
    exact freeMorProj₂_respects_comp_witness F₁ F₂ c.1 c.2
  | cong_left h _ ih =>
    exact CategoryQuotientData.FreeMorEquiv.cong_left
      (D := quotData₂ F₂) (freeMorProj₂ F₁ F₂ h) ih
  | cong_right k _ ih =>
    exact CategoryQuotientData.FreeMorEquiv.cong_right
      (D := quotData₂ F₂) (freeMorProj₂ F₁ F₂ k) ih

/-- freeMorProj₂ respects equivalence (symmetric to freeMorProj₁). -/
theorem freeMorProj₂_respects_equiv {a b : (prodQuotData F₁ F₂).quiver.Obj}
    {m₁ m₂ : FreeMor (prodQuotData F₁ F₂).quiver a b}
    (h : CategoryQuotientData.FreeMorEquiv (prodQuotData F₁ F₂) m₁ m₂) :
    CategoryQuotientData.FreeMorEquiv (quotData₂ F₂)
      (freeMorProj₂ F₁ F₂ m₁) (freeMorProj₂ F₁ F₂ m₂) := by
  induction h with
  | rel hgen => exact freeMorProj₂_respects_gen F₁ F₂ hgen
  | refl m => exact CategoryQuotientData.FreeMorEquiv.refl _
  | symm _ ih => exact CategoryQuotientData.FreeMorEquiv.symm ih
  | trans _ _ ih1 ih2 => exact CategoryQuotientData.FreeMorEquiv.trans ih1 ih2

/-- Quotient-level projection to first component. -/
def quotMorProj₁ {a b : (prodQuotData F₁ F₂).quiver.Obj}
    (q : (prodQuotData F₁ F₂).QuotMor a b) :
    (quotData₁ F₁).QuotMor a.1 b.1 :=
  Quotient.lift
    (fun m => (quotData₁ F₁).quotMor (freeMorProj₁ F₁ F₂ m))
    (fun _ _ h => Quotient.sound (freeMorProj₁_respects_equiv F₁ F₂ h))
    q

/-- Quotient-level projection to second component. -/
def quotMorProj₂ {a b : (prodQuotData F₁ F₂).quiver.Obj}
    (q : (prodQuotData F₁ F₂).QuotMor a b) :
    (quotData₂ F₂).QuotMor a.2 b.2 :=
  Quotient.lift
    (fun m => (quotData₂ F₂).quotMor (freeMorProj₂ F₁ F₂ m))
    (fun _ _ h => Quotient.sound (freeMorProj₂_respects_equiv F₁ F₂ h))
    q

/-!
### Backward Pairing Map: L(F₁) × L(F₂) → L(F₁ × F₂)

We now define the inverse direction: given morphisms in `L(F₁)` and `L(F₂)`,
we construct a morphism in `L(F₁ × F₂)` by pairing free morphisms.
-/

/-- For well-formed FunctorData (coming from categories), every object has an
    identity morphism. This type captures that property, providing a way to
    find identity witnesses for arbitrary objects. -/
structure HasAllIdentities (D : CategoryQuotientData.{v, u}) where
  findIdWitness : D.quiver.Obj → D.IdWitness
  findIdWitness_spec : ∀ a, D.idObj (findIdWitness a) = a

/-- If both components have all identities, so does the product. -/
def prodHasAllIdentities
    (hid₁ : HasAllIdentities (quotData₁ F₁))
    (hid₂ : HasAllIdentities (quotData₂ F₂)) :
    HasAllIdentities (prodQuotData F₁ F₂) where
  findIdWitness := fun (a₁, a₂) => (hid₁.findIdWitness a₁, hid₂.findIdWitness a₂)
  findIdWitness_spec := fun (a₁, a₂) =>
    Prod.ext (hid₁.findIdWitness_spec a₁) (hid₂.findIdWitness_spec a₂)

/-- Embed a FreeMor from component 1 into the product, with identity in
    component 2. For a morphism m₁ : a₁ → b₁ and fixed a₂, produces a
    morphism (a₁, a₂) → (b₁, a₂) in the product. -/
def freeMorLeftEmbed
    (hid₂ : HasAllIdentities (quotData₂ F₂))
    {a₁ b₁ : (quotData₁ F₁).quiver.Obj}
    (m₁ : FreeMor (quotData₁ F₁).quiver a₁ b₁)
    (a₂ : (quotData₂ F₂).quiver.Obj) :
    FreeMor (prodQuotData F₁ F₂).quiver (a₁, a₂) (b₁, a₂) :=
  match m₁ with
  | .var f₁ =>
    let i₂ := hid₂.findIdWitness a₂
    let idMor₂ := (quotData₂ F₂).idMor i₂
    let h_src := ((quotData₂ F₂).id_src i₂).trans (hid₂.findIdWitness_spec a₂)
    let h_tgt := ((quotData₂ F₂).id_tgt i₂).trans (hid₂.findIdWitness_spec a₂)
    have h_type : FreeMor (prodQuotData F₁ F₂).quiver
        ((quotData₁ F₁).quiver.src f₁, (quotData₂ F₂).quiver.src idMor₂)
        ((quotData₁ F₁).quiver.tgt f₁, (quotData₂ F₂).quiver.tgt idMor₂) =
      FreeMor (prodQuotData F₁ F₂).quiver
        ((quotData₁ F₁).quiver.src f₁, a₂)
        ((quotData₁ F₁).quiver.tgt f₁, a₂) := by rw [h_src, h_tgt]
    cast h_type (FreeMor.var (Q := (prodQuotData F₁ F₂).quiver) (f₁, idMor₂))
  | .id a => FreeMor.id (Q := (prodQuotData F₁ F₂).quiver) (a, a₂)
  | .comp g₁ f₁ =>
    .comp (freeMorLeftEmbed hid₂ g₁ a₂) (freeMorLeftEmbed hid₂ f₁ a₂)

/-- Embed a FreeMor from component 2 into the product, with identity in
    component 1. For a morphism m₂ : a₂ → b₂ and fixed b₁, produces a
    morphism (b₁, a₂) → (b₁, b₂) in the product. -/
def freeMorRightEmbed
    (hid₁ : HasAllIdentities (quotData₁ F₁))
    (b₁ : (quotData₁ F₁).quiver.Obj)
    {a₂ b₂ : (quotData₂ F₂).quiver.Obj}
    (m₂ : FreeMor (quotData₂ F₂).quiver a₂ b₂) :
    FreeMor (prodQuotData F₁ F₂).quiver (b₁, a₂) (b₁, b₂) :=
  match m₂ with
  | .var f₂ =>
    let i₁ := hid₁.findIdWitness b₁
    let idMor₁ := (quotData₁ F₁).idMor i₁
    let h_src := ((quotData₁ F₁).id_src i₁).trans (hid₁.findIdWitness_spec b₁)
    let h_tgt := ((quotData₁ F₁).id_tgt i₁).trans (hid₁.findIdWitness_spec b₁)
    have h_type : FreeMor (prodQuotData F₁ F₂).quiver
        ((quotData₁ F₁).quiver.src idMor₁, (quotData₂ F₂).quiver.src f₂)
        ((quotData₁ F₁).quiver.tgt idMor₁, (quotData₂ F₂).quiver.tgt f₂) =
      FreeMor (prodQuotData F₁ F₂).quiver
        (b₁, (quotData₂ F₂).quiver.src f₂)
        (b₁, (quotData₂ F₂).quiver.tgt f₂) := by rw [h_src, h_tgt]
    cast h_type (FreeMor.var (Q := (prodQuotData F₁ F₂).quiver) (idMor₁, f₂))
  | .id a => FreeMor.id (Q := (prodQuotData F₁ F₂).quiver) (b₁, a)
  | .comp g₂ f₂ =>
    .comp (freeMorRightEmbed hid₁ b₁ g₂) (freeMorRightEmbed hid₁ b₁ f₂)

/-- Pair two free morphisms into a free morphism in the product quiver.
    Defined compositionally as: first embed m₁ with identity in component 2,
    then compose with m₂ embedded with identity in component 1. -/
def freeMorPairComp
    (hid₁ : HasAllIdentities (quotData₁ F₁))
    (hid₂ : HasAllIdentities (quotData₂ F₂))
    {a₁ b₁ : (quotData₁ F₁).quiver.Obj}
    {a₂ b₂ : (quotData₂ F₂).quiver.Obj}
    (m₁ : FreeMor (quotData₁ F₁).quiver a₁ b₁)
    (m₂ : FreeMor (quotData₂ F₂).quiver a₂ b₂) :
    FreeMor (prodQuotData F₁ F₂).quiver (a₁, a₂) (b₁, b₂) :=
  .comp (freeMorRightEmbed (F₁ := F₁) (F₂ := F₂) hid₁ b₁ m₂)
        (freeMorLeftEmbed (F₁ := F₁) (F₂ := F₂) hid₂ m₁ a₂)

end BinaryProduct

/-!
## Terminal and Initial Objects

Terminal object for categories (one object, only identity morphism) and
initial object for categories (empty category). We prove that L preserves
terminal objects and Φ preserves initial objects.
-/

section TerminalAndInitial

universe uTerm

/-- The terminal quiver has one object and one morphism (the identity). -/
def OverQuiver.terminal : OverQuiver.{uTerm, uTerm} where
  Obj := PUnit.{uTerm + 1}
  MorType := PUnit.{uTerm + 1}
  src := fun _ => PUnit.unit
  tgt := fun _ => PUnit.unit

/-- The terminal category has one object and only the identity morphism. -/
def OverCategoryData.terminal : OverCategoryData OverQuiver.terminal where
  idFn := fun _ => PUnit.unit
  compFn := fun _ => PUnit.unit
  id_src := fun _ => rfl
  id_tgt := fun _ => rfl
  comp_src := fun _ => rfl
  comp_tgt := fun _ => rfl
  id_comp := fun _ => rfl
  comp_id := fun _ => rfl
  assoc := fun _ => rfl

/-- The initial quiver has no objects and no morphisms. -/
def OverQuiver.initial : OverQuiver.{uTerm, uTerm} where
  Obj := PEmpty.{uTerm + 1}
  MorType := PEmpty.{uTerm + 1}
  src := PEmpty.elim
  tgt := PEmpty.elim

/-- The initial category is the empty category. -/
def OverCategoryData.initial : OverCategoryData OverQuiver.initial where
  idFn := PEmpty.elim
  compFn := fun ⟨p, _⟩ => p.1.elim
  id_src := fun a => a.elim
  id_tgt := fun a => a.elim
  comp_src := fun ⟨p, _⟩ => p.1.elim
  comp_tgt := fun ⟨p, _⟩ => p.1.elim
  id_comp := fun a => a.elim
  comp_id := fun a => a.elim
  assoc := fun ⟨⟨f, _, _⟩, _, _⟩ => f.elim

/-- The terminal copresheaf maps everything to PUnit. -/
def FunctorData.terminal : CategoryJudgments.FunctorData (Type uTerm) where
  objC := PUnit.{uTerm + 1}
  morC := PUnit.{uTerm + 1}
  idC := PUnit.{uTerm + 1}
  compC := PUnit.{uTerm + 1}
  dom := fun _ => PUnit.unit
  cod := fun _ => PUnit.unit
  idMor := fun _ => PUnit.unit
  left := fun _ => PUnit.unit
  right := fun _ => PUnit.unit
  composite := fun _ => PUnit.unit
  h_id_endo := rfl
  h_comp_match := rfl
  h_comp_dom := rfl
  h_comp_cod := rfl

/-- The initial copresheaf maps everything to PEmpty. -/
def FunctorData.initial : CategoryJudgments.FunctorData (Type uTerm) where
  objC := PEmpty.{uTerm + 1}
  morC := PEmpty.{uTerm + 1}
  idC := PEmpty.{uTerm + 1}
  compC := PEmpty.{uTerm + 1}
  dom := PEmpty.elim
  cod := PEmpty.elim
  idMor := PEmpty.elim
  left := PEmpty.elim
  right := PEmpty.elim
  composite := PEmpty.elim
  h_id_endo := funext (fun x => x.elim)
  h_comp_match := funext (fun x => x.elim)
  h_comp_dom := funext (fun x => x.elim)
  h_comp_cod := funext (fun x => x.elim)

/-- Φ applied to the initial category. -/
def phiOfInitial : CategoryJudgments.FunctorData (Type uTerm) :=
  OverCategoryData.initial.toJudgmentFunctorData

/-- Map from initial composable pairs to PEmpty. -/
def initialCompCMap : OverQuiver.initial.ComposablePairsType → PEmpty.{uTerm + 1} :=
  fun ⟨p, _⟩ => p.1.elim

/-- Inverse map from PEmpty to initial composable pairs. -/
def initialCompCMapInv : PEmpty.{uTerm + 1} → OverQuiver.initial.ComposablePairsType :=
  PEmpty.elim

/-- Φ(initial category) ≅ initial copresheaf. This shows Φ preserves the
    initial object. -/
def phiFunctorPreservesInitial :
    CategoryJudgments.NatTransData phiOfInitial FunctorData.initial where
  appObj := id
  appMor := id
  appId := id
  appComp := initialCompCMap
  naturality_dom := funext (fun x => x.elim)
  naturality_cod := funext (fun x => x.elim)
  naturality_idMor := funext (fun x => x.elim)
  naturality_left := funext (fun ⟨p, _⟩ => p.1.elim)
  naturality_right := funext (fun ⟨p, _⟩ => p.1.elim)
  naturality_composite := funext (fun ⟨p, _⟩ => p.1.elim)

/-- The inverse natural transformation for Φ preserves initial. -/
def phiFunctorPreservesInitialInv :
    CategoryJudgments.NatTransData FunctorData.initial phiOfInitial where
  appObj := id
  appMor := id
  appId := id
  appComp := initialCompCMapInv
  naturality_dom := funext (fun x => x.elim)
  naturality_cod := funext (fun x => x.elim)
  naturality_idMor := funext (fun x => x.elim)
  naturality_left := funext (fun x => x.elim)
  naturality_right := funext (fun x => x.elim)
  naturality_composite := funext (fun x => x.elim)

/-- Round-trip identity: forward then backward is identity. -/
theorem phiFunctorPreservesInitial_comp_inv :
    phiFunctorPreservesInitial.comp phiFunctorPreservesInitialInv =
    CategoryJudgments.NatTransData.id phiOfInitial := by
  ext
  · rfl
  · rfl
  · rfl
  · rename_i a
    exact a.1.1.elim

/-- Round-trip identity: backward then forward is identity. -/
theorem phiFunctorPreservesInitial_inv_comp :
    phiFunctorPreservesInitialInv.comp phiFunctorPreservesInitial =
    CategoryJudgments.NatTransData.id FunctorData.initial := by
  ext
  · rfl
  · rfl
  · rfl
  · rename_i x
    exact x.elim

/-- L applied to the terminal copresheaf. -/
def lOfTerminal : BundledOverCategoryData.{uTerm, uTerm} :=
  LFunctorObj FunctorData.terminal

/-- The bundled terminal category. -/
def bundledTerminal : BundledOverCategoryData.{uTerm, uTerm} :=
  bundleOverCategory OverCategoryData.terminal

/-- The quiver of L(terminal). -/
def lOfTerminalQuiver : OverQuiver.{uTerm, uTerm} :=
  lOfTerminal.quiver

/-- The morphism map for the functor from L(terminal) to terminal. -/
def lToTerminalMorFn : lOfTerminalQuiver.MorType → OverQuiver.terminal.MorType :=
  fun _ => PUnit.unit

/-- The functor from L(terminal) to the terminal category (quiver level). -/
def lToTerminalQuiver : OverQuiverMorphism lOfTerminalQuiver OverQuiver.terminal where
  objFn := fun _ => PUnit.unit
  morFn := lToTerminalMorFn
  src_comm := fun _ => rfl
  tgt_comm := fun _ => rfl

/-- The functor from L(terminal) to terminal preserves identity. -/
theorem lToTerminal_map_id (a : lOfTerminalQuiver.Obj) :
    lToTerminalQuiver.morFn (lOfTerminal.data.idFn a) =
    OverCategoryData.terminal.idFn (lToTerminalQuiver.objFn a) := rfl

/-- Composability is trivial in the terminal quiver. -/
theorem terminal_composable (f g : OverQuiver.terminal.MorType) :
    OverQuiver.terminal.Composable f g := rfl

/-- The functor from L(terminal) to terminal preserves composition. -/
theorem lToTerminal_map_comp (p : lOfTerminalQuiver.ComposablePairsType) :
    lToTerminalQuiver.morFn (lOfTerminal.data.compFn p) =
    OverCategoryData.terminal.compFn
      ⟨(lToTerminalQuiver.morFn p.val.1, lToTerminalQuiver.morFn p.val.2),
        terminal_composable _ _⟩ := rfl

/-- The functor from L(terminal) to the terminal category.
    This is one half of the isomorphism L(terminal) ≅ terminal. -/
def lToTerminalFunctor : OverFunctorData lOfTerminal.data OverCategoryData.terminal where
  toOverQuiverMorphism := lToTerminalQuiver
  map_id := lToTerminal_map_id
  map_comp := lToTerminal_map_comp

/-- The CategoryQuotientData for the terminal copresheaf. -/
def terminalQuotData : CategoryQuotientData.{uTerm, uTerm} :=
  FunctorData.terminal.toCategoryQuotientData

/-- The quiver for the terminal copresheaf (abbreviation for clarity). -/
abbrev terminalQuiver : OverQuiver.{uTerm, uTerm} := terminalQuotData.quiver

/-- In the terminal copresheaf, var(idMor i) is equivalent to id(idObj i).
    The id_witness rule directly gives us this equivalence. -/
theorem terminal_var_equiv_id_at_idObj (i : terminalQuotData.IdWitness) :
    CategoryQuotientData.FreeMorEquiv terminalQuotData
      (cast (congrArg₂ (FreeMor terminalQuiver)
        (terminalQuotData.id_src i) (terminalQuotData.id_tgt i))
        (FreeMor.var (terminalQuotData.idMor i)))
      (FreeMor.id (terminalQuotData.idObj i)) :=
  CategoryQuotientData.FreeMorEquiv.rel
    (CategoryQuotientData.FreeMorEquivGen.id_witness i)

set_option backward.isDefEq.respectTransparency false in
/-- In the terminal copresheaf, FreeMor.var PUnit.unit is equivalent to
    FreeMor.id PUnit.unit. Since id_src = id_tgt = rfl for terminal,
    the cast is trivial. -/
theorem terminal_var_equiv_id :
    let Q := terminalQuiver
    CategoryQuotientData.FreeMorEquiv terminalQuotData
      (FreeMor.var (Q := Q) PUnit.unit) (FreeMor.id (Q := Q) PUnit.unit) := by
  have h := terminal_var_equiv_id_at_idObj PUnit.unit
  simp only [terminalQuotData, CategoryJudgments.FunctorData.toCategoryQuotientData,
    FunctorData.terminal, cast_eq] at h
  exact h

/-- Helper: all free morphisms in the terminal quiver are equivalent to identity,
    with generalized source and target (which must be PUnit.unit). -/
theorem terminal_freemor_equiv_id_aux
    {a b : terminalQuiver.Obj}
    (m : FreeMor terminalQuiver a b) :
    CategoryQuotientData.FreeMorEquiv terminalQuotData
      m (FreeMor.id (Q := terminalQuiver) a) := by
  induction m with
  | var f =>
    match f with
    | .unit =>
      have h := terminal_var_equiv_id
      simp only [terminalQuiver, terminalQuotData,
        CategoryJudgments.FunctorData.toCategoryQuotientData,
        CategoryJudgments.FunctorData.toQuiver, FunctorData.terminal] at h ⊢
      exact h
  | id a =>
    exact CategoryQuotientData.FreeMorEquiv.refl _
  | comp g f ih_g ih_f =>
    -- comp g f ~ comp (id _) f by right congruence with ih_g
    have step1 := CategoryQuotientData.FreeMorEquiv.cong_right terminalQuotData f ih_g
    -- comp (id _) f ~ f by id_left
    have step2 := CategoryQuotientData.FreeMorEquiv.rel
      (CategoryQuotientData.FreeMorEquivGen.id_left (D := terminalQuotData) f)
    -- Combine: comp g f ~ comp (id _) f ~ f ~ id _
    exact CategoryQuotientData.FreeMorEquiv.trans step1
      (CategoryQuotientData.FreeMorEquiv.trans step2 ih_f)

/-- All free morphisms in the terminal quiver (from PUnit.unit to PUnit.unit)
    are equivalent to the identity morphism FreeMor.id PUnit.unit. -/
theorem terminal_freemor_equiv_id
    (m : FreeMor terminalQuiver PUnit.unit PUnit.unit) :
    CategoryQuotientData.FreeMorEquiv terminalQuotData
      m (FreeMor.id (Q := terminalQuiver) PUnit.unit) :=
  terminal_freemor_equiv_id_aux m

/-- All quotient morphisms in L(terminal) from PUnit.unit to PUnit.unit are equal
    to the quotient identity. -/
theorem terminal_quotmor_eq_id
    (qm : terminalQuotData.QuotMor PUnit.unit PUnit.unit) :
    qm = terminalQuotData.quotId PUnit.unit := by
  induction qm using Quotient.ind with
  | _ m =>
    apply Quotient.sound
    exact terminal_freemor_equiv_id m

/-- The quotient morphism type in L(terminal) is a subsingleton. -/
instance terminalQuotMorSubsingleton :
    Subsingleton (terminalQuotData.QuotMor PUnit.unit PUnit.unit) where
  allEq := fun q1 q2 => by
    rw [terminal_quotmor_eq_id q1, terminal_quotmor_eq_id q2]

/-- The object function for the functor from terminal to L(terminal). -/
def terminalToL_objFn : OverQuiver.terminal.Obj → lOfTerminalQuiver.Obj :=
  fun _ => PUnit.unit

/-- The morphism function for the functor from terminal to L(terminal).
    Since L(terminal) has only one morphism (up to equality), we map to the
    identity. -/
def terminalToL_morFn : OverQuiver.terminal.MorType → lOfTerminalQuiver.MorType :=
  fun _ => ⟨PUnit.unit, PUnit.unit, terminalQuotData.quotId PUnit.unit⟩

/-- The quiver morphism from terminal to L(terminal). -/
def terminalToLQuiver : OverQuiverMorphism OverQuiver.terminal lOfTerminalQuiver where
  objFn := terminalToL_objFn
  morFn := terminalToL_morFn
  src_comm := fun _ => rfl
  tgt_comm := fun _ => rfl

/-- The functor from terminal to L(terminal) preserves identity. -/
theorem terminalToL_map_id (a : OverQuiver.terminal.Obj) :
    terminalToLQuiver.morFn (OverCategoryData.terminal.idFn a) =
    lOfTerminal.data.idFn (terminalToLQuiver.objFn a) := by
  cases a
  simp only [terminalToLQuiver, terminalToL_morFn, terminalToL_objFn,
    OverCategoryData.terminal, lOfTerminal, LFunctorObj, bundleOverCategory,
    CategoryJudgments.FunctorData.toOverCategoryData,
    CategoryQuotientData.toOverCategoryData,
    CategoryJudgments.FunctorData.toCategoryQuotientData]
  rfl

/-- Composability proof for the terminal-to-L morphism mapping. -/
theorem terminalToL_composable (p : OverQuiver.terminal.ComposablePairsType) :
    lOfTerminalQuiver.Composable
      (terminalToLQuiver.morFn p.val.1)
      (terminalToLQuiver.morFn p.val.2) := rfl

/-- Composition of quotient identities is identity. -/
theorem terminal_quotComp_id_id :
    terminalQuotData.quotComp
      (terminalQuotData.quotId PUnit.unit)
      (terminalQuotData.quotId PUnit.unit) =
    terminalQuotData.quotId PUnit.unit := by
  rw [CategoryQuotientData.quotComp_id_left]

/-- The functor from terminal to L(terminal) preserves composition. -/
theorem terminalToL_map_comp (p : OverQuiver.terminal.ComposablePairsType) :
    terminalToLQuiver.morFn (OverCategoryData.terminal.compFn p) =
    lOfTerminal.data.compFn
      ⟨(terminalToLQuiver.morFn p.val.1, terminalToLQuiver.morFn p.val.2),
        terminalToL_composable p⟩ := by
  simp only [terminalToLQuiver, terminalToL_morFn, OverCategoryData.terminal,
    lOfTerminal, LFunctorObj, bundleOverCategory,
    CategoryJudgments.FunctorData.toOverCategoryData,
    CategoryQuotientData.toOverCategoryData,
    CategoryJudgments.FunctorData.toCategoryQuotientData]
  -- Goal is now equality of bundled sigma types
  refine Sigma.ext rfl ?_
  refine heq_of_eq ?_
  refine Sigma.ext rfl ?_
  refine heq_of_eq ?_
  exact terminal_quotComp_id_id.symm

/-- The functor from terminal to L(terminal).
    This is the other half of the isomorphism L(terminal) ≅ terminal. -/
def terminalToLFunctor : OverFunctorData OverCategoryData.terminal lOfTerminal.data where
  toOverQuiverMorphism := terminalToLQuiver
  map_id := terminalToL_map_id
  map_comp := terminalToL_map_comp

/-- Round-trip: L(terminal) → terminal → L(terminal) is identity. -/
theorem lTerminal_roundtrip_LtoL :
    OverFunctorData.comp lToTerminalFunctor terminalToLFunctor =
    OverFunctorData.id lOfTerminal.data := by
  ext
  case objFn.h a =>
    match a with
    | .unit => rfl
  case morFn.h m =>
    simp only [OverFunctorData.comp, OverQuiverMorphism.comp, OverFunctorData.id,
      OverQuiverMorphism.id, lToTerminalFunctor, lToTerminalQuiver,
      terminalToLFunctor, terminalToLQuiver]
    -- Goal: ⟨PUnit.unit, PUnit.unit, quotId PUnit.unit⟩ = m
    rcases m with ⟨a, b, qm⟩
    match a, b with
    | .unit, .unit =>
      -- Goal: ⟨PUnit.unit, PUnit.unit, quotId PUnit.unit⟩ = ⟨PUnit.unit, PUnit.unit, qm⟩
      refine Sigma.ext rfl ?_
      refine heq_of_eq ?_
      refine Sigma.ext rfl ?_
      refine heq_of_eq ?_
      exact (terminal_quotmor_eq_id qm).symm

/-- Round-trip: terminal → L(terminal) → terminal is identity. -/
theorem lTerminal_roundtrip_termTerm :
    OverFunctorData.comp terminalToLFunctor lToTerminalFunctor =
    OverFunctorData.id OverCategoryData.terminal := by
  ext
  case objFn.h a =>
    match a with
    | .unit => rfl
  case morFn.h m =>
    match m with
    | .unit => rfl

end TerminalAndInitial

end GebLean
