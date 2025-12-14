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
      -- Try congrArg₂ with FreeMor.comp directly
      -- Goal: (cast _ (var g₁)).comp (cast _ (var f₁)) = cast _ ((cast _ (var g₂)).comp (var f₂))
      -- where g₁ = g₂ (by h) and f₁ = f₂ (by h')
      -- Use Eq.rec to transport var through the equality
      have var_eq_L : FreeMor.var (F.quiverMor.morFn (D₁.compLeft c)) =
          h ▸ FreeMor.var (D₂.compLeft (F.compWitMap c)) :=
        h.symm.rec rfl
      have var_eq_R : FreeMor.var (F.quiverMor.morFn (D₁.compRight c)) =
          h' ▸ FreeMor.var (D₂.compRight (F.compWitMap c)) :=
        h'.symm.rec rfl
      simp only [var_eq_L, var_eq_R]
      -- Now both sides have the same vars; the casts use proof irrelevance
      -- Use cast_subst_var to get the vars into the same form
      rw [cast_subst_var h _ _ _ _, cast_subst_var h' _ _ _ _]
      -- 8 proof obligations for the cast_subst_var arguments, plus main composition goal
      -- Main goal: (cast _ g).comp (cast _ f) = cast _ ((cast _ g).comp f)
      on_goal 1 => grind
      all_goals first
          | exact F.quiverMor.src_comm _
          | exact F.quiverMor.tgt_comm _
          | exact ha
          | exact hb
          | exact (D₂.comp_match _).symm
          | exact (D₂.comp_match _).trans
              ((congrArg D₂.quiver.tgt (F.compRight_comm c).symm).trans
                (F.quiverMor.tgt_comm _))
          | exact ((congrArg D₂.quiver.src (F.compLeft_comm c).symm).trans
                (F.quiverMor.src_comm _)).trans (congrArg _ (D₁.comp_match c).symm)
          | exact (congrArg D₂.quiver.tgt (F.compRight_comm c).symm).trans
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
    -- Use Quotient.recOnSubsingleton to relate the quotients
    -- Actually, let's use a simpler approach with HEq transitivity
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

/-- Helper: counitEvalQuot on quotId gives idFn. -/
theorem counitEvalQuot_quotId (a : Q.Obj) :
    counitEvalQuot C ((derivedQuotientData C).quotId a) =
    ⟨C.idFn a, C.id_src a, C.id_tgt a⟩ := by
  simp only [counitEvalQuot, CategoryQuotientData.quotId, CategoryQuotientData.quotMor,
    Quotient.lift_mk, counitEval_id]

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

end GebLean
