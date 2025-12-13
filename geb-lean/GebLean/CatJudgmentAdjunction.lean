import GebLean.CategoryJudgments
import GebLean.Utilities.Category
import GebLean.Utilities.OverCategoryEquiv

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

end GebLean
