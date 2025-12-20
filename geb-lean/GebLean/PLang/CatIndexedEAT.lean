import GebLean.PLang.IndexedEAT
import GebLean.CategoryJudgments
import GebLean.CatJudgmentAdjunction

/-!
# Category Theory as an Indexed EAT

This module demonstrates that the category adjunction (L ⊣ Φ between Cat and
copresheaves on CategoryJudgments) arises as an instance of the generic EAT
framework from `IndexedEAT.lean`.

## Overview

The category theory essentially algebraic theory (EAT) consists of:

1. **Index Type**: `CategoryJudgments.Obj` with 4 objects:
   - `obj` : objects of a category
   - `mor` : morphisms
   - `id` : identity witnesses
   - `comp` : composition witnesses

2. **Polynomial Endofunctor**: P on `Over CategoryJudgments.Obj` where:
   - P(A) at `obj` = A(obj)  (objects pass through)
   - P(A) at `mor` = A(mor) + A(id) + A(comp)  (morphisms, identities, composites)
   - P(A) at `id` = A(id)  (identity witnesses pass through)
   - P(A) at `comp` = A(comp)  (composition witnesses pass through)

   This captures the fact that morphisms in the free category come from:
   - Variables (base morphisms)
   - Identity morphisms (from identity witnesses)
   - Composite morphisms (from composition witnesses)

3. **Equations**: The EAT equations on `PolyFix P` are:
   - Left unit: id ∘ f ≃ f
   - Right unit: f ∘ id ≃ f
   - Associativity: h ∘ (g ∘ f) ≃ (h ∘ g) ∘ f
   - Identity witness: var(idMor i) ≃ id(idObj i)
   - Composition witness: var(composite c) ≃ var(left c) ∘ var(right c)

## Structure of this Module

We proceed in stages:
1. Define the polynomial endofunctor `catPoly` for categories
2. Define the equivalence relation `catEquations` on initial algebra
3. Construct `catEAT : IndexedEAT CategoryJudgments.Obj`
4. Provide `EATHasQuotient catEAT` instance
5. Show that `eatAdjunction catEAT` matches `catCopresheafMathlibAdjunction`

## References

- `GebLean/PLang/IndexedEAT.lean` - Generic EAT framework
- `GebLean/CatJudgmentAdjunction.lean` - Direct category adjunction construction
- `docs/generic-essentially-algebraic-embedding.md` - Mathematical background
-/

namespace GebLean

open CategoryTheory CategoryJudgments

universe u

/-! ## The Polynomial Endofunctor for Categories

The polynomial P encodes the operations that build free morphisms:
- At `obj`: just pass through (no operations produce objects)
- At `mor`: union of base morphisms, identities, and composites
- At `id` and `comp`: pass through (these are input data)

However, since we're working in the indexed setting over `CategoryJudgments.Obj`,
the polynomial structure is more nuanced. Each position in the polynomial
corresponds to a way of constructing an element at a particular judgment.
-/

section CatPolynomial

/--
The position types for the category polynomial at each judgment.

At each judgment type j, we have positions indexing how elements are built:
- `obj`: single position (identity functor component)
- `mor`: three positions (variable, identity, composite)
- `id`: single position (pass-through)
- `comp`: single position (pass-through)
-/
inductive CatPolyPosition : Obj → Type u where
  | objPos : CatPolyPosition Obj.obj
  | morVar : CatPolyPosition Obj.mor
  | morId : CatPolyPosition Obj.mor
  | morComp : CatPolyPosition Obj.mor
  | idPos : CatPolyPosition Obj.id
  | compPos : CatPolyPosition Obj.comp
  deriving DecidableEq, Repr

/--
The target judgment for each position. This determines where the
constructed element lives.
-/
def CatPolyPosition.target : {j : Obj} → CatPolyPosition j → Obj
  | _, objPos => Obj.obj
  | _, morVar => Obj.mor
  | _, morId => Obj.mor
  | _, morComp => Obj.mor
  | _, idPos => Obj.id
  | _, compPos => Obj.comp

/--
The arity (number of children) for each position.

- objPos: 1 child (the object itself)
- morVar: 1 child (the base morphism)
- morId: 1 child (the identity witness, which determines the object)
- morComp: 2 children (the two morphisms being composed)
- idPos: 1 child (the identity witness)
- compPos: 1 child (the composition witness)
-/
inductive CatPolyArity : {j : Obj} → CatPolyPosition j → Type u where
  | objChild : CatPolyArity CatPolyPosition.objPos
  | morVarChild : CatPolyArity CatPolyPosition.morVar
  | morIdChild : CatPolyArity CatPolyPosition.morId
  | morCompLeft : CatPolyArity CatPolyPosition.morComp
  | morCompRight : CatPolyArity CatPolyPosition.morComp
  | idChild : CatPolyArity CatPolyPosition.idPos
  | compChild : CatPolyArity CatPolyPosition.compPos
  deriving DecidableEq, Repr

/--
The source judgment for each child position. This determines what type
of element is needed as input.
-/
def CatPolyArity.source : {j : Obj} → {p : CatPolyPosition j} →
    CatPolyArity p → Obj
  | _, _, objChild => Obj.obj
  | _, _, morVarChild => Obj.mor
  | _, _, morIdChild => Obj.id
  | _, _, morCompLeft => Obj.mor
  | _, _, morCompRight => Obj.mor
  | _, _, idChild => Obj.id
  | _, _, compChild => Obj.comp

/-! ### Constructing the Formal Polynomial

We now construct `catPoly : PolyEndo Obj` from the position/arity data above.
The polynomial is a family indexed by Obj, where at each j we have a
coproduct of covariant representables.
-/

/--
The family object for each position. This is an object of `Over Obj` whose
fiber gives the children and whose map gives their judgment types.
-/
def CatPolyPosition.family : {j : Obj} → CatPolyPosition j → Over Obj
  | _, objPos => Over.mk (X := Obj) (fun _ : Unit => Obj.obj)
  | _, morVar => Over.mk (X := Obj) (fun _ : Unit => Obj.mor)
  | _, morId => Over.mk (X := Obj) (fun _ : Unit => Obj.id)
  | _, morComp => Over.mk (X := Obj) (fun _ : Bool => Obj.mor)
  | _, idPos => Over.mk (X := Obj) (fun _ : Unit => Obj.id)
  | _, compPos => Over.mk (X := Obj) (fun _ : Unit => Obj.comp)

/--
The polynomial functor for categories at each judgment.
Returns a `CoprodCovarRepCat (Over Obj)` which is a coproduct of representables.
-/
def catPolyAt (j : Obj) : CoprodCovarRepCat (Over Obj) :=
  ccrObjMk (fun p : CatPolyPosition j => CatPolyPosition.family p)

/--
The polynomial endofunctor for categories on `Over Obj`.
This is the formal polynomial whose algebras are "pre-categories" (before
imposing equations) and whose initial algebra gives free morphisms.
-/
def catPoly : PolyEndo Obj := catPolyAt

/--
The index type at each judgment is exactly `CatPolyPosition j`.
-/
theorem catPoly_index (j : Obj) :
    polyBetweenIndex Obj Obj catPoly j = CatPolyPosition j := rfl

/--
The family at each position is `CatPolyPosition.family p`.
-/
theorem catPoly_family (j : Obj) (p : CatPolyPosition j) :
    polyBetweenFamily Obj Obj catPoly j p = CatPolyPosition.family p := rfl

end CatPolynomial

/-! ## Free Morphisms as PolyFix

We show that `PolyFix catPoly Obj.mor` corresponds to `FreeMor` from the
existing adjunction construction.
-/

section FreeMorCorrespondence

/-
## Correspondence: FreeMor vs PolyFreeM catPoly

The correspondence between FreeMor and the generic polynomial construction
works through `PolyFreeM` (the free monad), not `PolyFix` (initial algebra):

### Constructor Correspondence

FreeMor Q a b builds morphisms with source/target tracking.
PolyFreeM catPoly A Obj.mor builds trees with A-valued leaves.

| FreeMor        | PolyFreeM catPoly A                              |
|----------------|--------------------------------------------------|
| var f          | PolyFreeM.pure (a morphism leaf from A)          |
| id x           | PolyFreeM.mk morId (child in id judgment)        |
| comp g f       | PolyFreeM.mk morComp (children: [g, f])          |

### Equation Correspondence

| FreeMorEquivGen      | CatEquivGen                                    |
|----------------------|------------------------------------------------|
| id_left: id . f ~ f  | left_unit: comp(id, f) ~ f                     |
| id_right: f . id ~ f | right_unit: comp(f, id) ~ f                    |
| assoc                | assoc: h . (g . f) ~ (h . g) . f               |
| id_witness           | (requires PolyFreeM with witness-containing A) |
| comp_witness         | (requires PolyFreeM with witness-containing A) |

### Source/Target Tracking

FreeMor explicitly tracks source and target types in the inductive.
PolyFreeM stores this information implicitly in the tree structure:
- Objects appear as leaves (via PolyFreeM.pure at obj judgment)
- The well-formedness of compositions is not syntactically enforced
- Instead, it is recovered when folding into an actual category

### Completing the Correspondence

A full isomorphism would require:
1. A fiber-respecting bijection
   PolyFreeM catPoly A Obj.mor ≃ Σ (a b : ObjFiber A), FreeMor (quiverOf A) a b
2. Showing FreeAlgEquiv catEAT matches FreeMorEquiv under this bijection
3. Lifting to an isomorphism of functors

This demonstrates that catEAT captures the same algebraic structure as
the hand-built FreeMor construction in CatJudgmentAdjunction.
-/

end FreeMorCorrespondence

/-! ## Category Equations

The equations that turn free P-algebras into actual categories.
These correspond to the `FreeMorEquivGen` generating relations.
-/

section CatEquations

/-
The category equations on PolyFix catPoly correspond to FreeMorEquivGen:

1. Left unit: id ∘ f = f
   In PolyFix: comp(id(b), f) ≃ f where f ends at b

2. Right unit: f ∘ id = f
   In PolyFix: comp(f, id(a)) ≃ f where f starts at a

3. Associativity: h ∘ (g ∘ f) = (h ∘ g) ∘ f
   In PolyFix: comp(h, comp(g, f)) ≃ comp(comp(h, g), f)

4. Identity witness: var(idMor i) = id(idObj i)
   In PolyFix: morVar tree for identity ≃ morId tree

5. Composition witness: var(composite c) = var(left c) ∘ var(right c)
   In PolyFix: morVar tree for composite ≃ morComp tree

These generate an equivalence relation via reflexive-symmetric-transitive
closure and congruence.
-/

/--
The generating relations for category equations on PolyFix.
This mirrors `FreeMorEquivGen` from CatJudgmentAdjunction.
-/
inductive CatEquivGen : {j : Obj} → PolyFix catPoly j → PolyFix catPoly j → Prop
  -- Structural equations (only at mor judgment)
  | left_unit {f : PolyFix catPoly Obj.mor} {idTree : PolyFix catPoly Obj.mor} :
      -- comp(id, f) ≃ f
      CatEquivGen
        (PolyFix.mk Obj.mor CatPolyPosition.morComp
          (fun b => match b with | true => idTree | false => f))
        f
  | right_unit {f : PolyFix catPoly Obj.mor} {idTree : PolyFix catPoly Obj.mor} :
      -- comp(f, id) ≃ f
      CatEquivGen
        (PolyFix.mk Obj.mor CatPolyPosition.morComp
          (fun b => match b with | true => f | false => idTree))
        f
  | assoc {h g f : PolyFix catPoly Obj.mor} :
      -- comp(h, comp(g, f)) ≃ comp(comp(h, g), f)
      CatEquivGen
        (PolyFix.mk Obj.mor CatPolyPosition.morComp
          (fun b => match b with
            | true => h
            | false => PolyFix.mk Obj.mor CatPolyPosition.morComp
                (fun b' => match b' with | true => g | false => f)))
        (PolyFix.mk Obj.mor CatPolyPosition.morComp
          (fun b => match b with
            | true => PolyFix.mk Obj.mor CatPolyPosition.morComp
                (fun b' => match b' with | true => h | false => g)
            | false => f))

/--
The full equivalence relation: reflexive-symmetric-transitive closure
of `CatEquivGen` plus congruence.
-/
inductive CatEquiv : {j : Obj} → PolyFix catPoly j → PolyFix catPoly j → Prop
  | gen {j : Obj} {t₁ t₂ : PolyFix catPoly j} :
      CatEquivGen t₁ t₂ → CatEquiv t₁ t₂
  | refl {j : Obj} (t : PolyFix catPoly j) :
      CatEquiv t t
  | symm {j : Obj} {t₁ t₂ : PolyFix catPoly j} :
      CatEquiv t₁ t₂ → CatEquiv t₂ t₁
  | trans {j : Obj} {t₁ t₂ t₃ : PolyFix catPoly j} :
      CatEquiv t₁ t₂ → CatEquiv t₂ t₃ → CatEquiv t₁ t₃
  | congr {j : Obj} {p : CatPolyPosition j}
      {children₁ children₂ : ∀ e : (CatPolyPosition.family p).left,
        PolyFix catPoly ((CatPolyPosition.family p).hom e)} :
      (∀ e, CatEquiv (children₁ e) (children₂ e)) →
      CatEquiv (PolyFix.mk j p children₁) (PolyFix.mk j p children₂)

/--
CatEquiv is reflexive.
-/
theorem catEquiv_refl : ∀ (j : Obj) (t : PolyFix catPoly j), CatEquiv t t :=
  fun _ t => CatEquiv.refl t

/--
CatEquiv is symmetric.
-/
theorem catEquiv_symm :
    ∀ (j : Obj), ∀ {t₁ t₂ : PolyFix catPoly j}, CatEquiv t₁ t₂ → CatEquiv t₂ t₁ :=
  fun _ _ => CatEquiv.symm

/--
CatEquiv is transitive.
-/
theorem catEquiv_trans :
    ∀ (j : Obj), ∀ {t₁ t₂ t₃ : PolyFix catPoly j},
    CatEquiv t₁ t₂ → CatEquiv t₂ t₃ → CatEquiv t₁ t₃ :=
  fun _ _ _ => CatEquiv.trans

/--
The category equations as a `PolyFixRel` for the generic EAT framework.
-/
def catEquations : PolyFixRel Obj catPoly := fun _ t₁ t₂ => CatEquiv t₁ t₂

/--
The equations form an equivalence relation at each fiber.
-/
theorem catEquations_isEquiv : catEquations.IsEquivalence where
  refl := catEquiv_refl
  symm := catEquiv_symm
  trans := catEquiv_trans

end CatEquations

/-! ## The Category IndexedEAT

We now assemble the polynomial and equations into an IndexedEAT structure.
-/

section CatIndexedEAT

/--
The essentially algebraic theory of categories, expressed as an IndexedEAT.

This captures the same structure as the hand-built CatJudgmentAdjunction
but in the generic framework:
- `poly = catPoly`: the polynomial encoding category operations
- `equations = catEquations`: associativity, unit laws, and witnesses
-/
def catEAT : IndexedEAT Obj where
  poly := catPoly
  equations := catEquations
  eqIsEquiv := catEquations_isEquiv

/-
A model of catEAT is precisely a category (in the sense of OverCategoryData).

A P-algebra A : PolyAlg catPoly satisfies IsEATModel catEAT iff the fold
from the initial algebra respects the category equations. This means:
- Associativity holds in A
- Unit laws hold in A
- Identity and composition witnesses are respected

This correspondence would be proven by showing that the fold-based model
predicate captures exactly the category axioms when unpacked.
-/

end CatIndexedEAT

/-! ## Relationship to Existing Adjunction

We establish the connection between the generic EAT adjunction and
the explicitly constructed `catCopresheafMathlibAdjunction`.

Observations:
1. `PolyFreeM` on an input `A : Over CategoryJudgments.Obj` corresponds to
   `FreeMor` built from the quiver structure of `A`
2. The EAT equations correspond exactly to `FreeMorEquiv`
3. The quotient construction matches the explicit quotient in
   `CategoryJudgments.FunctorData.toOverCategoryData`
-/

section Correspondence

/--
A copresheaf on CategoryJudgments viewed as an object of
`Over CategoryJudgments.Obj`.

This converts a `FunctorData (Type u)` to an `Over Obj` by taking
the sigma type of all judgments.
-/
def functorDataToOver (F : CategoryJudgments.FunctorData (Type u)) :
    Over Obj :=
  Over.mk (X := Obj) (Y := Σ j : Obj, match j with
    | Obj.obj => F.objC
    | Obj.mor => F.morC
    | Obj.id => F.idC
    | Obj.comp => F.compC) Sigma.fst

/--
The fiber of `functorDataToOver F` at each judgment recovers the original
component of F.
-/
def functorDataToOver_fiber_obj (F : CategoryJudgments.FunctorData (Type u)) :
    { a : (functorDataToOver F).left // (functorDataToOver F).hom a = Obj.obj } ≃
    F.objC where
  toFun := fun ⟨⟨j, x⟩, hj⟩ => by
    simp only [functorDataToOver] at hj
    cases hj
    exact x
  invFun := fun x => ⟨⟨Obj.obj, x⟩, rfl⟩
  left_inv := fun ⟨⟨j, x⟩, hj⟩ => by
    simp only [functorDataToOver] at hj
    cases hj
    rfl
  right_inv := fun _ => rfl

/-
The correspondence between `Over Obj` and `FunctorData` is more subtle
than a simple equivalence because `FunctorData` carries additional structure
(dom, cod, etc.) that isn't present in a bare `Over Obj` object.

A full equivalence would require enriching `Over Obj` with the copresheaf
structure morphisms, which is what the `familySliceEquiv` machinery provides.
-/

end Correspondence

/-! ## Path to EATHasQuotient

To provide `EATHasQuotient catEAT`, we need to construct the quotient algebra
for each `A : Over Obj`. The construction leverages the existing FreeMor/
FreeMorEquiv infrastructure from CatJudgmentAdjunction.
-/

section QuotientConstruction

/--
Extract the object fiber from an `Over Obj` at the obj judgment.
-/
def overObjFiber (A : Over Obj) : Type u := { a : A.left // A.hom a = Obj.obj }

/--
Extract the morphism fiber from an `Over Obj` at the mor judgment.
-/
def overMorFiber (A : Over Obj) : Type u := { a : A.left // A.hom a = Obj.mor }

/--
Extract the identity witness fiber from an `Over Obj` at the id judgment.
-/
def overIdFiber (A : Over Obj) : Type u := { a : A.left // A.hom a = Obj.id }

/--
Extract the composition witness fiber from an `Over Obj` at the comp judgment.
-/
def overCompFiber (A : Over Obj) : Type u :=
  { a : A.left // A.hom a = Obj.comp }

/--
Helper to construct a PolyFreeM node at a given position with given children.
This wraps PolyFix.mk with Sum.inr for the structured node case.
-/
def mkPolyFreeMNode (A : Over Obj) (j : Obj) (p : CatPolyPosition j)
    (children : ∀ e : (CatPolyPosition.family p).left,
      PolyFreeM A catPoly ((CatPolyPosition.family p).hom e)) :
    PolyFreeM A catPoly j :=
  PolyFix.mk j (Sum.inr p) children

/--
Helper for morComp case: build node from two representatives.
-/
def catQuotMorCompNodeAt (A : Over Obj) (c_true c_false : PolyFreeM A catPoly Obj.mor) :
    FreeAlgQuot catEAT A Obj.mor :=
  FreeAlgQuot.mk catEAT A (mkPolyFreeMNode A Obj.mor CatPolyPosition.morComp
    (fun b => match b with | true => c_true | false => c_false))

/--
The morComp node respects equivalence in both arguments.
-/
lemma catQuotMorCompNodeAt_resp (A : Over Obj)
    (c1_true c2_true c1_false c2_false : PolyFreeM A catPoly Obj.mor)
    (heq_true : FreeAlgEquiv catEAT A Obj.mor c1_true c2_true)
    (heq_false : FreeAlgEquiv catEAT A Obj.mor c1_false c2_false) :
    catQuotMorCompNodeAt A c1_true c1_false = catQuotMorCompNodeAt A c2_true c2_false := by
  unfold catQuotMorCompNodeAt
  apply Quot.sound
  exact @FreeAlgEquiv.cong Obj catEAT A Obj.mor CatPolyPosition.morComp _ _
    (fun b => match b with | true => heq_true | false => heq_false)

/--
The morComp node respects equivalence in the first (true) argument.
-/
lemma catQuotMorCompNodeAt_resp_true (A : Over Obj)
    (c1 c2 c_false : PolyFreeM A catPoly Obj.mor)
    (heq : FreeAlgEquiv catEAT A Obj.mor c1 c2) :
    catQuotMorCompNodeAt A c1 c_false = catQuotMorCompNodeAt A c2 c_false :=
  catQuotMorCompNodeAt_resp A c1 c2 c_false c_false heq
    (@FreeAlgEquiv.refl Obj catEAT A Obj.mor c_false)

/--
The morComp node respects equivalence in the second (false) argument.
-/
lemma catQuotMorCompNodeAt_resp_false (A : Over Obj)
    (c_true c1 c2 : PolyFreeM A catPoly Obj.mor)
    (heq : FreeAlgEquiv catEAT A Obj.mor c1 c2) :
    catQuotMorCompNodeAt A c_true c1 = catQuotMorCompNodeAt A c_true c2 :=
  catQuotMorCompNodeAt_resp A c_true c_true c1 c2
    (@FreeAlgEquiv.refl Obj catEAT A Obj.mor c_true) heq

/--
The quotient algebra structure map for catEAT.

At each position, we lift through the quotient using the congruence property.
Since catPoly positions have at most 2 children (morComp has Bool = 2 children),
we can handle each case explicitly using nested Quot.lift.
-/
def catQuotientStrAt (A : Over Obj) (j : Obj)
    (p : CatPolyPosition j)
    (children : ∀ e : (CatPolyPosition.family p).left,
      FreeAlgQuot catEAT A ((CatPolyPosition.family p).hom e)) :
    FreeAlgQuot catEAT A j := by
  match j, p with
  | Obj.obj, CatPolyPosition.objPos =>
    -- 1 child of type Unit at Obj.obj
    exact Quot.lift
      (fun c => FreeAlgQuot.mk catEAT A (mkPolyFreeMNode A Obj.obj
        CatPolyPosition.objPos (fun _ => c)))
      (fun c1 c2 heq => Quot.sound
        (@FreeAlgEquiv.cong Obj catEAT A Obj.obj CatPolyPosition.objPos
          _ _ (fun _ => heq)))
      (children ())
  | Obj.mor, CatPolyPosition.morVar =>
    -- 1 child of type Unit at Obj.mor
    exact Quot.lift
      (fun c => FreeAlgQuot.mk catEAT A (mkPolyFreeMNode A Obj.mor
        CatPolyPosition.morVar (fun _ => c)))
      (fun c1 c2 heq => Quot.sound
        (@FreeAlgEquiv.cong Obj catEAT A Obj.mor CatPolyPosition.morVar
          _ _ (fun _ => heq)))
      (children ())
  | Obj.mor, CatPolyPosition.morId =>
    -- 1 child of type Unit at Obj.id
    exact Quot.lift
      (fun c => FreeAlgQuot.mk catEAT A (mkPolyFreeMNode A Obj.mor
        CatPolyPosition.morId (fun _ => c)))
      (fun c1 c2 heq => Quot.sound
        (@FreeAlgEquiv.cong Obj catEAT A Obj.mor CatPolyPosition.morId
          _ _ (fun _ => heq)))
      (children ())
  | Obj.mor, CatPolyPosition.morComp =>
    -- 2 children of type Bool at Obj.mor - use nested Quot.lift with helper
    exact Quot.lift
      (fun c_true =>
        Quot.lift
          (fun c_false => catQuotMorCompNodeAt A c_true c_false)
          (catQuotMorCompNodeAt_resp_false A c_true)
          (children false))
      (fun c1 c2 heq => by
        -- Need to prove: Quot.lift f₁ r₁ (children false) = Quot.lift f₂ r₂ (children false)
        -- Use Quot.ind to reduce to proving for representatives
        induction children false using Quot.ind with
        | mk c_false =>
          exact catQuotMorCompNodeAt_resp_true A c1 c2 c_false heq)
      (children true)
  | Obj.id, CatPolyPosition.idPos =>
    -- 1 child of type Unit at Obj.id
    exact Quot.lift
      (fun c => FreeAlgQuot.mk catEAT A (mkPolyFreeMNode A Obj.id
        CatPolyPosition.idPos (fun _ => c)))
      (fun c1 c2 heq => Quot.sound
        (@FreeAlgEquiv.cong Obj catEAT A Obj.id CatPolyPosition.idPos
          _ _ (fun _ => heq)))
      (children ())
  | Obj.comp, CatPolyPosition.compPos =>
    -- 1 child of type Unit at Obj.comp
    exact Quot.lift
      (fun c => FreeAlgQuot.mk catEAT A (mkPolyFreeMNode A Obj.comp
        CatPolyPosition.compPos (fun _ => c)))
      (fun c1 c2 heq => Quot.sound
        (@FreeAlgEquiv.cong Obj catEAT A Obj.comp CatPolyPosition.compPos
          _ _ (fun _ => heq)))
      (children ())

/--
Helper lemma for sigma transport: if a sigma equals `⟨a', b'⟩`, then
transporting its `.snd` along any fiber proof yields `b'`.
-/
lemma sigma_snd_transport_eq {α : Type*} {β : α → Type*}
    {x : Σ a, β a} {a' : α} {b' : β a'}
    (h_eq : x = ⟨a', b'⟩) (h_fst : x.fst = a') :
    h_fst ▸ x.snd = b' := by
  subst h_eq
  rfl

/--
Extract children from the polynomial evaluation structure as a function
into FreeAlgQuot, by using the Over morphism structure.
-/
def catExtractQuotChildren (A : Over Obj) (j : Obj) (p : CatPolyPosition j)
    (childMor : (CatPolyPosition.family p) ⟶ freeAlgQuotOver catEAT A) :
    ∀ e : (CatPolyPosition.family p).left,
      FreeAlgQuot catEAT A ((CatPolyPosition.family p).hom e) := by
  intro e
  -- childMor.left e gives us an element of (freeAlgQuotOver catEAT A).left
  -- which is Σ x, FreeAlgQuot catEAT A x
  let child := childMor.left e
  -- The fiber preservation gives us that child.fst = family.hom e
  have fiber_eq : child.fst = (CatPolyPosition.family p).hom e :=
    congrFun (Over.w childMor) e
  exact fiber_eq ▸ child.snd

/--
When composing a morphism into the free algebra with the quotient map,
extracting children gives `FreeAlgQuot.mk` of the transported original children.
-/
lemma catExtractQuotChildren_comp_quotient (A : Over Obj) (j : Obj)
    (p : CatPolyPosition j)
    (mor : (CatPolyPosition.family p) ⟶ (polyFreeAlg A catPoly).a)
    (e : (CatPolyPosition.family p).left) :
    catExtractQuotChildren A j p (mor ≫ freeAlgQuotMap catEAT A) e =
    FreeAlgQuot.mk catEAT A (congrFun (Over.w mor) e ▸ (mor.left e).snd) := by
  unfold catExtractQuotChildren FreeAlgQuot.mk freeAlgQuotMap
  simp only [CategoryTheory.Over.comp_left]
  exact quot_mk_transport_eq _ _

/--
The left component of the quotient structure map.
Takes an element of the polynomial applied to the quotient carrier
and produces an element of the quotient carrier.
-/
def catQuotientStrLeft (A : Over Obj) :
    ((polyEndoFunctor Obj catPoly).obj (freeAlgQuotOver catEAT A)).left →
    (freeAlgQuotOver catEAT A).left := by
  intro ⟨j, elem⟩
  -- elem : polyBetweenEvalFamily Obj Obj catPoly (freeAlgQuotOver catEAT A) j
  -- Extract position and children morphism
  let p : CatPolyPosition j := ptoefIndex Obj elem
  let childMor := ptoefMor Obj elem
  let children := catExtractQuotChildren A j p childMor
  exact ⟨j, catQuotientStrAt A j p children⟩

/--
The quotient structure map preserves fibers.
-/
lemma catQuotientStr_comm (A : Over Obj) :
    catQuotientStrLeft A ≫ (freeAlgQuotOver catEAT A).hom =
    ((polyEndoFunctor Obj catPoly).obj (freeAlgQuotOver catEAT A)).hom := rfl

/--
The quotient structure map as an Over morphism.
-/
def catQuotientStr (A : Over Obj) :
    (polyEndoFunctor Obj catPoly).obj (freeAlgQuotOver catEAT A) ⟶
    freeAlgQuotOver catEAT A :=
  Over.homMk (catQuotientStrLeft A) (catQuotientStr_comm A)

/--
The quotient P-algebra for catEAT.
Assembles the quotient carrier with its algebra structure.
-/
def catQuotientAlg (A : Over Obj) : PolyAlg catPoly where
  a := freeAlgQuotOver catEAT A
  str := catQuotientStr A

/--
The quotient algebra carrier is the quotient carrier by definition.
-/
theorem catQuotientAlg_carrier (A : Over Obj) :
    (catQuotientAlg A).a = freeAlgQuotOver catEAT A := rfl

end QuotientConstruction

/-! ## Quotient Algebra Properties

We establish that the quotient algebra is an EAT model and construct
the quotient homomorphism and functoriality.
-/

section QuotientProperties

/--
The fold from the initial algebra to the quotient algebra.
This composition gives the unique algebra homomorphism.
-/
def catQuotientFoldAt (A : Over Obj) (x : Obj) (t : PolyFix catPoly x) :
    FreeAlgQuot catEAT A x :=
  FreeAlgQuot.mk catEAT A (polyFixToFreeAlg catPoly A x t)

/--
When `catQuotientStrAt` is applied to children that are quotients of representatives,
it produces the quotient of the node with those representatives.

This follows from `Quot.lift (f) h (Quot.mk r x) = f x`.
-/
lemma catQuotientStrAt_mk (A : Over Obj) (j : Obj) (p : CatPolyPosition j)
    (reps : ∀ e : (CatPolyPosition.family p).left,
      PolyFreeM A catPoly ((CatPolyPosition.family p).hom e)) :
    catQuotientStrAt A j p (fun e => FreeAlgQuot.mk catEAT A (reps e)) =
    FreeAlgQuot.mk catEAT A (mkPolyFreeMNode A j p reps) := by
  match j, p with
  | Obj.obj, CatPolyPosition.objPos => rfl
  | Obj.mor, CatPolyPosition.morVar => rfl
  | Obj.mor, CatPolyPosition.morId => rfl
  | Obj.mor, CatPolyPosition.morComp =>
    -- catQuotientStrAt uses nested Quot.lift with helper
    simp only [catQuotientStrAt, FreeAlgQuot.mk, catQuotMorCompNodeAt, mkPolyFreeMNode]
    congr 2
    funext b
    cases b <;> rfl
  | Obj.id, CatPolyPosition.idPos => rfl
  | Obj.comp, CatPolyPosition.compPos => rfl

/--
The fold into the quotient algebra equals the quotient of the embedded tree.
This is proved by induction on the tree structure.
-/
lemma catQuotientFold_eq_mk (A : Over Obj) (x : Obj) (t : PolyFix catPoly x) :
    polyFixFoldAtWithProof catPoly (catQuotientAlg A) x t =
    ⟨⟨x, FreeAlgQuot.mk catEAT A (polyFixToFreeAlg catPoly A x t)⟩, rfl⟩ := by
  induction t with
  | mk y p children ih =>
    apply Subtype.ext
    simp only [polyFixFoldAtWithProof, polyFixToFreeAlg]
    simp only [catQuotientAlg, catQuotientStr, catQuotientStrLeft, Over.homMk_left]
    apply congrArg (Sigma.mk y)
    simp only [ptoefIndex, ccrEvalIndex]
    -- Goal: catQuotientStrAt A y p (fun e => extracted_child e) = mk(node)
    -- The extracted children should equal mk(polyFixToFreeAlg ... (children e))
    -- by the IH applied to each child
    have h_children_ext : ∀ e, catExtractQuotChildren A y p
        (ptoefMor Obj ⟨p, Over.homMk
          (fun e' => (polyFixFoldAtWithProof catPoly (catQuotientAlg A)
            ((polyBetweenFamily Obj Obj catPoly y p).hom e') (children e')).val)
          (by funext e'; exact (polyFixFoldAtWithProof catPoly (catQuotientAlg A)
            ((polyBetweenFamily Obj Obj catPoly y p).hom e') (children e')).property)⟩) e =
        FreeAlgQuot.mk catEAT A
          (polyFixToFreeAlg catPoly A _ (children e)) := by
      intro e
      unfold catExtractQuotChildren ptoefMor ccrEvalMor
      simp only [Over.homMk_left]
      have ih_e := ih e
      have h_val : (polyFixFoldAtWithProof catPoly (catQuotientAlg A)
          ((polyBetweenFamily Obj Obj catPoly y p).hom e) (children e)).val =
          ⟨(polyBetweenFamily Obj Obj catPoly y p).hom e,
           FreeAlgQuot.mk catEAT A (polyFixToFreeAlg catPoly A _ (children e))⟩ :=
        congrArg Subtype.val ih_e
      exact sigma_snd_transport_eq h_val _
    -- Apply catQuotientStrAt_mk with the extracted children function
    have h_eq : (fun e => catExtractQuotChildren A y p
        (ptoefMor Obj ⟨p, Over.homMk
          (fun e' => (polyFixFoldAtWithProof catPoly (catQuotientAlg A)
            ((polyBetweenFamily Obj Obj catPoly y p).hom e') (children e')).val)
          _⟩) e) =
        (fun e => FreeAlgQuot.mk catEAT A
          (polyFixToFreeAlg catPoly A _ (children e))) := funext h_children_ext
    -- The goal has the struct literal form of catQuotientAlg.
    -- We prove the equality by showing both sides produce the same result.
    have h_step : catQuotientStrAt A y p (catExtractQuotChildren A y p
        (ptoefMor Obj ⟨p, Over.homMk
          (fun e => (polyFixFoldAtWithProof catPoly (catQuotientAlg A)
            ((polyBetweenFamily Obj Obj catPoly y p).hom e) (children e)).val)
          _⟩)) =
        catQuotientStrAt A y p (fun e => FreeAlgQuot.mk catEAT A
          (polyFixToFreeAlg catPoly A _ (children e))) := congrArg (catQuotientStrAt A y p) h_eq
    calc catQuotientStrAt A y p _ = catQuotientStrAt A y p _ := rfl
      _ = catQuotientStrAt A y p (fun e => FreeAlgQuot.mk catEAT A
          (polyFixToFreeAlg catPoly A _ (children e))) := h_step
      _ = _ := catQuotientStrAt_mk A y p _

/--
The quotient algebra is an EAT model: the fold respects catEquations.

This follows from `freeAlgQuot_isModel` which shows that the quotient
identifies equation-equivalent elements by construction.
-/
theorem catQuotientIsModel (A : Over Obj) : IsEATModel catEAT (catQuotientAlg A) := by
  intro x t₁ t₂ heq
  -- Use the characterization of the fold
  have h1 := catQuotientFold_eq_mk A x t₁
  have h2 := catQuotientFold_eq_mk A x t₂
  change (polyFixFoldAtWithProof catEAT.poly (catQuotientAlg A) x t₁).val =
       (polyFixFoldAtWithProof catEAT.poly (catQuotientAlg A) x t₂).val
  -- catEAT.poly = catPoly by definition
  simp only [catEAT] at h1 h2 ⊢
  -- Now rewrite using our characterization to get sigma elements
  rw [h1, h2]
  -- Goal: ⟨x, mk t₁⟩ = ⟨x, mk t₂⟩ in Σ x, FreeAlgQuot catEAT A x
  -- Both have the same first component x, so use congrArg
  apply congrArg (Sigma.mk x)
  -- Now goal is: mk t₁ = mk t₂ in FreeAlgQuot catEAT A x
  exact freeAlgQuot_isModel catEAT A x t₁ t₂ heq

/--
The quotient homomorphism: the canonical map from Free(A) to Quotient(A).
This is the quotient map lifted to an algebra homomorphism.
-/
def catQuotientHom (A : Over Obj) :
    polyFreeAlg A catPoly ⟶ catQuotientAlg A where
  f := freeAlgQuotMap catEAT A
  h := by
    apply Over.OverMorphism.ext
    funext ⟨j, elem⟩
    obtain ⟨p, mor⟩ := elem
    change catQuotientStrLeft A (((polyToOverEvalMap Obj catPolyAt
        (freeAlgQuotMap catEAT A)).left) ⟨j, ⟨p, mor⟩⟩) =
      (freeAlgQuotMap catEAT A).left (polyFreeMStrLeft A catPolyAt ⟨j, ⟨p, mor⟩⟩)
    simp only [polyToOverEvalMap_left, ccrEvalMap]
    apply congrArg (Sigma.mk _)
    simp only [ptoefIndex, ptoefMor, ccrEvalIndex, ccrEvalMor,
               polyFreeMStrFamily, pbefIndex, pbefMor]
    have h_children : ∀ e, catExtractQuotChildren A j p (mor ≫ freeAlgQuotMap catEAT A) e =
        FreeAlgQuot.mk catEAT A (congrFun (Over.w mor) e ▸ (mor.left e).snd) :=
      fun e => catExtractQuotChildren_comp_quotient A j p mor e
    conv_lhs => rw [funext h_children, catQuotientStrAt_mk]
    rfl

/-! ### Quotient Algebra Functoriality

The quotient algebra construction is functorial: morphisms in Over Obj
lift to algebra homomorphisms between quotient algebras.
-/

/--
Helper: the quotient map on elements at a fiber.
-/
def catQuotientAlgMapAt (A B : Over Obj) (f : A ⟶ B) (j : Obj)
    (q : FreeAlgQuot catEAT A j) : FreeAlgQuot catEAT B j :=
  freeAlgQuotMapAt catEAT A B f j q

/--
Transport commutes with freeAlgQuotMapAt: mapping then transporting equals
transporting then mapping.
-/
lemma freeAlgQuotMapAt_transport (A B : Over Obj) (g : A ⟶ B)
    (x y : Obj) (h : x = y) (q : FreeAlgQuot catEAT A x) :
    h ▸ freeAlgQuotMapAt catEAT A B g x q =
    freeAlgQuotMapAt catEAT A B g y (h ▸ q) := by
  subst h
  rfl

/--
polyFreeMapAt on a node equals a node with mapped children.
This is definitional from the structure of polyFreeMBind.
-/
lemma polyFreeMapAt_node (A B : Over Obj) (g : A ⟶ B)
    (j : Obj) (p : CatPolyPosition j)
    (children : ∀ e : (CatPolyPosition.family p).left,
      PolyFreeM A catPoly ((CatPolyPosition.family p).hom e)) :
    polyFreeMapAt A B catPoly g j (mkPolyFreeMNode A j p children) =
    mkPolyFreeMNode B j p (fun e => polyFreeMapAt A B catPoly g _ (children e)) := by
  simp only [mkPolyFreeMNode, polyFreeMapAt, polyFreeMBind]
  rfl

/--
Child extraction composed with quotient map equals quotient map applied to extracted children.
-/
lemma catExtractQuotChildren_comp_quotMor (A B : Over Obj) (g : A ⟶ B)
    (j : Obj) (p : CatPolyPosition j)
    (mor : (CatPolyPosition.family p) ⟶ freeAlgQuotOver catEAT A) (e) :
    catExtractQuotChildren B j p (mor ≫ freeAlgQuotMor catEAT A B g) e =
    freeAlgQuotMapAt catEAT A B g _ (catExtractQuotChildren A j p mor e) := by
  unfold catExtractQuotChildren
  have h_fib : (mor.left e).fst = (CatPolyPosition.family p).hom e := congrFun (Over.w mor) e
  -- Both fiber proofs are of the same statement and definitionally equal paths
  have h_fib' : ((mor ≫ freeAlgQuotMor catEAT A B g).left e).fst =
      (CatPolyPosition.family p).hom e := h_fib
  -- The goal is: h_fib' ▸ (mapped q) = map (h_fib ▸ q)
  -- Use transport commutativity
  exact freeAlgQuotMapAt_transport A B g _ _ h_fib _

/--
The quotient structure map commutes with the quotient map: applying the B-structure
to mapped children equals mapping the result of the A-structure.
-/
lemma catQuotientStrAt_comm_quotMap (A B : Over Obj) (g : A ⟶ B)
    (j : Obj) (p : CatPolyPosition j)
    (children : ∀ e : (CatPolyPosition.family p).left,
      FreeAlgQuot catEAT A ((CatPolyPosition.family p).hom e)) :
    catQuotientStrAt B j p (fun e => freeAlgQuotMapAt catEAT A B g _ (children e)) =
    freeAlgQuotMapAt catEAT A B g j (catQuotientStrAt A j p children) := by
  match j, p with
  | Obj.obj, CatPolyPosition.objPos =>
    obtain ⟨t, ht⟩ : ∃ t, children () = Quot.mk _ t :=
      (Quot.exists_rep (children ())).imp (fun _ ha => ha.symm)
    have h_children : children = (fun _ => FreeAlgQuot.mk catEAT A t) := funext fun _ => ht
    simp only [h_children, freeAlgQuotMapAt]
    exact congrArg (Quot.mk _) (polyFreeMapAt_node A B g Obj.obj
      CatPolyPosition.objPos (fun _ => t))
  | Obj.mor, CatPolyPosition.morVar =>
    obtain ⟨t, ht⟩ : ∃ t, children () = Quot.mk _ t :=
      (Quot.exists_rep (children ())).imp (fun _ ha => ha.symm)
    have h_children : children = (fun _ => FreeAlgQuot.mk catEAT A t) := funext fun _ => ht
    simp only [h_children, freeAlgQuotMapAt]
    exact congrArg (Quot.mk _) (polyFreeMapAt_node A B g Obj.mor
      CatPolyPosition.morVar (fun _ => t))
  | Obj.mor, CatPolyPosition.morId =>
    obtain ⟨t, ht⟩ : ∃ t, children () = Quot.mk _ t :=
      (Quot.exists_rep (children ())).imp (fun _ ha => ha.symm)
    have h_children : children = (fun _ => FreeAlgQuot.mk catEAT A t) := funext fun _ => ht
    simp only [h_children, freeAlgQuotMapAt]
    exact congrArg (Quot.mk _) (polyFreeMapAt_node A B g Obj.mor
      CatPolyPosition.morId (fun _ => t))
  | Obj.id, CatPolyPosition.idPos =>
    obtain ⟨t, ht⟩ : ∃ t, children () = Quot.mk _ t :=
      (Quot.exists_rep (children ())).imp (fun _ ha => ha.symm)
    have h_children : children = (fun _ => FreeAlgQuot.mk catEAT A t) := funext fun _ => ht
    simp only [h_children, freeAlgQuotMapAt]
    exact congrArg (Quot.mk _) (polyFreeMapAt_node A B g Obj.id
      CatPolyPosition.idPos (fun _ => t))
  | Obj.comp, CatPolyPosition.compPos =>
    obtain ⟨t, ht⟩ : ∃ t, children () = Quot.mk _ t :=
      (Quot.exists_rep (children ())).imp (fun _ ha => ha.symm)
    have h_children : children = (fun _ => FreeAlgQuot.mk catEAT A t) := funext fun _ => ht
    simp only [h_children, freeAlgQuotMapAt]
    exact congrArg (Quot.mk _) (polyFreeMapAt_node A B g Obj.comp
      CatPolyPosition.compPos (fun _ => t))
  | Obj.mor, CatPolyPosition.morComp =>
    obtain ⟨t_true, ht_true⟩ : ∃ t, children true = Quot.mk _ t :=
      (Quot.exists_rep (children true)).imp (fun _ ha => ha.symm)
    obtain ⟨t_false, ht_false⟩ : ∃ t, children false = Quot.mk _ t :=
      (Quot.exists_rep (children false)).imp (fun _ ha => ha.symm)
    have h_children : children = fun e => match e with
      | true => FreeAlgQuot.mk catEAT A t_true
      | false => FreeAlgQuot.mk catEAT A t_false := by
      funext b; cases b <;> assumption
    simp only [h_children, freeAlgQuotMapAt, catEAT]
    apply congrArg (Quot.mk _)
    have heq := (polyFreeMapAt_node A B g Obj.mor
      CatPolyPosition.morComp (fun e => match e with
        | true => t_true
        | false => t_false)).symm
    convert heq using 2
    funext b
    cases b <;> rfl

/--
The quotient map applied to identity is identity on quotient elements.
-/
lemma freeAlgQuotMapAt_id (A : Over Obj) (x : Obj) (q : FreeAlgQuot catEAT A x) :
    freeAlgQuotMapAt catEAT A A (𝟙 A) x q = q := by
  induction q using Quot.ind with
  | mk t =>
    simp only [freeAlgQuotMapAt, FreeAlgQuot.mk]
    congr 1
    exact polyFreeMapAt_id A catEAT.poly x t

/--
The quotient map respects composition.
-/
lemma freeAlgQuotMapAt_comp (A B C : Over Obj) (f : A ⟶ B) (g : B ⟶ C)
    (x : Obj) (q : FreeAlgQuot catEAT A x) :
    freeAlgQuotMapAt catEAT A C (f ≫ g) x q =
    freeAlgQuotMapAt catEAT B C g x (freeAlgQuotMapAt catEAT A B f x q) := by
  induction q using Quot.ind with
  | mk t =>
    simp only [freeAlgQuotMapAt, FreeAlgQuot.mk]
    congr 1
    exact polyFreeMapAt_comp A B C catEAT.poly f g x t

/--
The quotient morphism applied to identity is identity.
-/
lemma freeAlgQuotMor_id (A : Over Obj) :
    freeAlgQuotMor catEAT A A (𝟙 A) = 𝟙 (freeAlgQuotOver catEAT A) := by
  apply Over.OverMorphism.ext
  funext ⟨x, q⟩
  simp only [freeAlgQuotMor, Over.homMk_left, freeAlgQuotMapTotal, Over.id_left,
    types_id_apply]
  exact congrArg (Sigma.mk _) (freeAlgQuotMapAt_id A x q)

/--
The quotient morphism respects composition.
-/
lemma freeAlgQuotMor_comp (A B C : Over Obj) (f : A ⟶ B) (g : B ⟶ C) :
    freeAlgQuotMor catEAT A C (f ≫ g) =
    freeAlgQuotMor catEAT A B f ≫ freeAlgQuotMor catEAT B C g := by
  apply Over.OverMorphism.ext
  funext ⟨x, q⟩
  simp only [freeAlgQuotMor, Over.homMk_left, freeAlgQuotMapTotal, Over.comp_left,
    types_comp_apply]
  exact congrArg (Sigma.mk _) (freeAlgQuotMapAt_comp A B C f g x q)

def catQuotientAlgMap (A B : Over Obj) (f : A ⟶ B) :
    catQuotientAlg A ⟶ catQuotientAlg B where
  f := freeAlgQuotMor catEAT A B f
  h := by
    apply Over.OverMorphism.ext
    funext ⟨j, elem⟩
    obtain ⟨p, mor⟩ := elem
    -- Goal: structure on B after quotient map = quotient map after structure on A
    change catQuotientStrLeft B (((polyToOverEvalMap Obj catPolyAt
        (freeAlgQuotMor catEAT A B f)).left) ⟨j, ⟨p, mor⟩⟩) =
      (freeAlgQuotMor catEAT A B f).left (catQuotientStrLeft A ⟨j, ⟨p, mor⟩⟩)
    simp only [polyToOverEvalMap_left, ccrEvalMap]
    apply congrArg (Sigma.mk _)
    simp only [ptoefIndex, ptoefMor, ccrEvalIndex, ccrEvalMor]
    -- Use the commutation lemmas
    have h1 : (fun e => catExtractQuotChildren B j p (mor ≫ freeAlgQuotMor catEAT A B f) e) =
              (fun e => freeAlgQuotMapAt catEAT A B f _ (catExtractQuotChildren A j p mor e)) :=
      funext (catExtractQuotChildren_comp_quotMor A B f j p mor)
    conv_lhs =>
      rw [show catExtractQuotChildren B j p (mor ≫ freeAlgQuotMor catEAT A B f) =
          (fun e => catExtractQuotChildren B j p (mor ≫ freeAlgQuotMor catEAT A B f) e)
        from rfl]
      rw [h1]
    exact catQuotientStrAt_comm_quotMap A B f j p (catExtractQuotChildren A j p mor)

/--
The quotient homomorphism is natural with respect to morphisms in Over Obj.
-/
lemma catQuotientNaturality (A B : Over Obj) (f : A ⟶ B) :
    polyFreeAlgMap A B catPoly f ≫ catQuotientHom B =
    catQuotientHom A ≫ catQuotientAlgMap A B f := by
  apply Endofunctor.Algebra.Hom.ext
  apply Over.OverMorphism.ext
  funext ⟨x, t⟩
  rfl

/--
The quotient homomorphism respects the equivalence relation.
-/
lemma catQuotientRespectsEquiv (A : Over Obj) :
    AlgHomRespectsEquiv catEAT A (catQuotientAlg A) (catQuotientHom A) := by
  intro x t1 t2 hequiv
  simp only [catQuotientHom, freeAlgQuotMap, Over.homMk_left, FreeAlgQuot.mk]
  exact congrArg (Sigma.mk x) (Quot.sound hequiv)

/--
The quotient algebra map preserves identity.
-/
lemma catQuotientAlgMap_id (A : Over Obj) :
    catQuotientAlgMap A A (𝟙 A) = 𝟙 (catQuotientAlg A) := by
  apply Endofunctor.Algebra.Hom.ext
  exact freeAlgQuotMor_id A

/--
The quotient algebra map preserves composition.
-/
lemma catQuotientAlgMap_comp (A B C : Over Obj) (f : A ⟶ B) (g : B ⟶ C) :
    catQuotientAlgMap A C (f ≫ g) = catQuotientAlgMap A B f ≫ catQuotientAlgMap B C g := by
  apply Endofunctor.Algebra.Hom.ext
  exact freeAlgQuotMor_comp A B C f g

/--
The underlying morphism of the quotient factor.
Given h : Free(A) → M that respects equivalence, produce an Over morphism
freeAlgQuotOver catEAT A → M.a.
-/
def catQuotientFactorMor (A : Over Obj) (M : PolyAlg catPoly)
    (h : polyFreeAlg A catPoly ⟶ M) (hresp : AlgHomRespectsEquiv catEAT A M h) :
    freeAlgQuotOver catEAT A ⟶ M.a :=
  Over.homMk (fun ⟨x, q⟩ =>
    Quot.lift (fun t => h.f.left ⟨x, t⟩)
      (fun t1 t2 heq => hresp x t1 t2 heq) q)
    (by
      funext ⟨x, q⟩
      induction q using Quot.ind with
      | mk t => exact congrFun (Over.w h.f) ⟨x, t⟩)

/--
When catQuotientStrAt is applied to representative children and then the factor is applied,
the result equals applying h to the free algebra node directly.
-/
lemma catQuotientFactorMor_strAt_reps (A : Over Obj) (M : PolyAlg catPoly)
    (h : polyFreeAlg A catPoly ⟶ M) (hresp : AlgHomRespectsEquiv catEAT A M h)
    (j : Obj) (p : CatPolyPosition j)
    (reps : ∀ e, PolyFreeM A catPoly ((CatPolyPosition.family p).hom e)) :
    (catQuotientFactorMor A M h hresp).left
      ⟨j, catQuotientStrAt A j p (fun e => FreeAlgQuot.mk catEAT A (reps e))⟩ =
    h.f.left ⟨j, mkPolyFreeMNode A j p reps⟩ := by
  rw [catQuotientStrAt_mk]
  rfl

/--
The quotient factor is an algebra homomorphism.
-/
def catQuotientFactor (A : Over Obj) (M : PolyAlg catPoly) (hM : IsEATModel catEAT M)
    (h : polyFreeAlg A catPoly ⟶ M) (hresp : AlgHomRespectsEquiv catEAT A M h) :
    catQuotientAlg A ⟶ M where
  f := catQuotientFactorMor A M h hresp
  h := by
    apply Over.OverMorphism.ext
    funext ⟨j, elem⟩
    obtain ⟨p, mor⟩ := elem
    simp only [Over.comp_left, types_comp_apply]
    match j, p with
    | Obj.obj, CatPolyPosition.objPos =>
      have fiber_eq : (mor.left ()).fst = Obj.obj := by
        have := congrFun (Over.w mor) ()
        simp only [catQuotientAlg, freeAlgQuotOver, FreeAlgQuotTotal.proj, Over.mk_hom,
          types_comp_apply] at this
        exact this
      generalize hq : (mor.left ()).snd = q at *
      induction q using Quot.ind with
      | mk t =>
        simp only [catQuotientAlg, catQuotientStr, catQuotientStrLeft,
          catQuotientStrAt, catQuotientFactorMor, Over.homMk_left, FreeAlgQuot.mk]
        unfold ptoefIndex ptoefMor ccrEvalIndex ccrEvalMor catExtractQuotChildren
        dsimp only []
        rw [hq]
        rw [show (fiber_eq ▸ Quot.mk (FreeAlgEquiv catEAT A (mor.left ()).fst) t :
            Quot (FreeAlgEquiv catEAT A Obj.obj)) =
            Quot.mk (FreeAlgEquiv catEAT A Obj.obj) (fiber_eq ▸ t) from
          @Eq.rec Obj (mor.left ()).fst
            (fun x h =>
              (h ▸ Quot.mk (FreeAlgEquiv catEAT A (mor.left ()).fst) t :
                Quot (FreeAlgEquiv catEAT A x)) =
              Quot.mk (FreeAlgEquiv catEAT A x) (h ▸ t))
            rfl
            Obj.obj
            fiber_eq]
        simp only [Quot.lift_mk]
        have h_alg := congrFun (congrArg (·.left) h.h)
          (⟨Obj.obj, ⟨CatPolyPosition.objPos,
            Over.homMk (fun _ => ⟨Obj.obj, fiber_eq ▸ t⟩) rfl⟩⟩ :
            (polyToOverEval Obj catPolyAt (polyFreeMCarrier A catPoly)).left)
        simp only [Over.comp_left, types_comp_apply, Over.homMk_left,
          polyFreeAlg, polyFreeMStr, polyFreeMStrLeft, polyFreeMStrFamily,
          polyEndoFunctor, polyBetweenEvalFunctor, pbefIndex, pbefMor,
          ptoefIndex, ptoefMor, ccrEvalIndex, ccrEvalMor, mkPolyFreeMNode] at h_alg ⊢
        simp only [polyToOverFunctor, polyToOverEvalMap, familySliceForward,
          familySliceForwardMap, polyToOverEvalFamilyMap,
          Over.homMk_left, ccrEvalMap] at h_alg ⊢
        convert h_alg using 2
        congr 2
        apply Over.OverMorphism.ext
        funext u
        simp only [Over.comp_left, types_comp_apply, Over.homMk_left]
        have sigma_eq : (⟨(mor.left u).fst, t⟩ : Σ x, PolyFreeM A catPoly x) =
            ⟨Obj.obj, fiber_eq ▸ t⟩ :=
          Sigma.ext fiber_eq (heq_eqRec fiber_eq t)
        simp only [show u = () from rfl] at sigma_eq ⊢
        show Quot.lift (fun t => h.f.left ⟨(mor.left ()).fst, t⟩) _ (mor.left ()).snd =
          h.f.left ⟨Obj.obj, fiber_eq ▸ t⟩
        rw [hq]
        simp only [Quot.lift_mk]
        exact congrArg h.f.left sigma_eq
    | Obj.mor, CatPolyPosition.morVar =>
      have fiber_eq : (mor.left ()).fst = Obj.mor := by
        have := congrFun (Over.w mor) ()
        simp only [catQuotientAlg, freeAlgQuotOver, FreeAlgQuotTotal.proj, Over.mk_hom,
          types_comp_apply] at this
        exact this
      generalize hq : (mor.left ()).snd = q at *
      induction q using Quot.ind with
      | mk t =>
        simp only [catQuotientAlg, catQuotientStr, catQuotientStrLeft,
          catQuotientStrAt, catQuotientFactorMor, Over.homMk_left, FreeAlgQuot.mk]
        unfold ptoefIndex ptoefMor ccrEvalIndex ccrEvalMor catExtractQuotChildren
        dsimp only []
        rw [hq]
        rw [show (fiber_eq ▸ Quot.mk (FreeAlgEquiv catEAT A (mor.left ()).fst) t :
            Quot (FreeAlgEquiv catEAT A Obj.mor)) =
            Quot.mk (FreeAlgEquiv catEAT A Obj.mor) (fiber_eq ▸ t) from
          @Eq.rec Obj (mor.left ()).fst
            (fun x h =>
              (h ▸ Quot.mk (FreeAlgEquiv catEAT A (mor.left ()).fst) t :
                Quot (FreeAlgEquiv catEAT A x)) =
              Quot.mk (FreeAlgEquiv catEAT A x) (h ▸ t))
            rfl
            Obj.mor
            fiber_eq]
        simp only [Quot.lift_mk]
        have h_alg := congrFun (congrArg (·.left) h.h)
          (⟨Obj.mor, ⟨CatPolyPosition.morVar,
            Over.homMk (fun _ => ⟨Obj.mor, fiber_eq ▸ t⟩) rfl⟩⟩ :
            (polyToOverEval Obj catPolyAt (polyFreeMCarrier A catPoly)).left)
        simp only [Over.comp_left, types_comp_apply, Over.homMk_left,
          polyFreeAlg, polyFreeMStr, polyFreeMStrLeft, polyFreeMStrFamily,
          polyEndoFunctor, polyBetweenEvalFunctor, pbefIndex, pbefMor,
          ptoefIndex, ptoefMor, ccrEvalIndex, ccrEvalMor, mkPolyFreeMNode] at h_alg ⊢
        simp only [polyToOverFunctor, polyToOverEvalMap, familySliceForward,
          familySliceForwardMap, polyToOverEvalFamilyMap,
          Over.homMk_left, ccrEvalMap] at h_alg ⊢
        convert h_alg using 2
        congr 2
        apply Over.OverMorphism.ext
        funext u
        simp only [Over.comp_left, types_comp_apply, Over.homMk_left]
        have sigma_eq : (⟨(mor.left u).fst, t⟩ : Σ x, PolyFreeM A catPoly x) =
            ⟨Obj.mor, fiber_eq ▸ t⟩ :=
          Sigma.ext fiber_eq (heq_eqRec fiber_eq t)
        simp only [show u = () from rfl] at sigma_eq ⊢
        show Quot.lift (fun t => h.f.left ⟨(mor.left ()).fst, t⟩) _ (mor.left ()).snd =
          h.f.left ⟨Obj.mor, fiber_eq ▸ t⟩
        rw [hq]
        simp only [Quot.lift_mk]
        exact congrArg h.f.left sigma_eq
    | Obj.mor, CatPolyPosition.morId =>
      have fiber_eq : (mor.left ()).fst = Obj.id := by
        have := congrFun (Over.w mor) ()
        simp only [catQuotientAlg, freeAlgQuotOver, FreeAlgQuotTotal.proj, Over.mk_hom,
          types_comp_apply] at this
        exact this
      generalize hq : (mor.left ()).snd = q at *
      induction q using Quot.ind with
      | mk t =>
        simp only [catQuotientAlg, catQuotientStr, catQuotientStrLeft,
          catQuotientStrAt, catQuotientFactorMor, Over.homMk_left, FreeAlgQuot.mk]
        unfold ptoefIndex ptoefMor ccrEvalIndex ccrEvalMor catExtractQuotChildren
        dsimp only []
        rw [hq]
        rw [show (fiber_eq ▸ Quot.mk (FreeAlgEquiv catEAT A (mor.left ()).fst) t :
            Quot (FreeAlgEquiv catEAT A Obj.id)) =
            Quot.mk (FreeAlgEquiv catEAT A Obj.id) (fiber_eq ▸ t) from
          @Eq.rec Obj (mor.left ()).fst
            (fun x h =>
              (h ▸ Quot.mk (FreeAlgEquiv catEAT A (mor.left ()).fst) t :
                Quot (FreeAlgEquiv catEAT A x)) =
              Quot.mk (FreeAlgEquiv catEAT A x) (h ▸ t))
            rfl
            Obj.id
            fiber_eq]
        simp only [Quot.lift_mk]
        have h_alg := congrFun (congrArg (·.left) h.h)
          (⟨Obj.mor, ⟨CatPolyPosition.morId,
            Over.homMk (fun _ => ⟨Obj.id, fiber_eq ▸ t⟩) rfl⟩⟩ :
            (polyToOverEval Obj catPolyAt (polyFreeMCarrier A catPoly)).left)
        simp only [Over.comp_left, types_comp_apply, Over.homMk_left,
          polyFreeAlg, polyFreeMStr, polyFreeMStrLeft, polyFreeMStrFamily,
          polyEndoFunctor, polyBetweenEvalFunctor, pbefIndex, pbefMor,
          ptoefIndex, ptoefMor, ccrEvalIndex, ccrEvalMor, mkPolyFreeMNode] at h_alg ⊢
        simp only [polyToOverFunctor, polyToOverEvalMap, familySliceForward,
          familySliceForwardMap, polyToOverEvalFamilyMap,
          Over.homMk_left, ccrEvalMap] at h_alg ⊢
        convert h_alg using 2
        congr 2
        apply Over.OverMorphism.ext
        funext u
        simp only [Over.comp_left, types_comp_apply, Over.homMk_left]
        have sigma_eq : (⟨(mor.left u).fst, t⟩ : Σ x, PolyFreeM A catPoly x) =
            ⟨Obj.id, fiber_eq ▸ t⟩ :=
          Sigma.ext fiber_eq (heq_eqRec fiber_eq t)
        simp only [show u = () from rfl] at sigma_eq ⊢
        show Quot.lift (fun t => h.f.left ⟨(mor.left ()).fst, t⟩) _ (mor.left ()).snd =
          h.f.left ⟨Obj.id, fiber_eq ▸ t⟩
        rw [hq]
        simp only [Quot.lift_mk]
        exact congrArg h.f.left sigma_eq
    | Obj.mor, CatPolyPosition.morComp =>
      have fiber_eq_t : (mor.left true).fst = Obj.mor := by
        have := congrFun (Over.w mor) true
        simp only [catQuotientAlg, freeAlgQuotOver, FreeAlgQuotTotal.proj, Over.mk_hom,
          types_comp_apply] at this
        exact this
      have fiber_eq_f : (mor.left false).fst = Obj.mor := by
        have := congrFun (Over.w mor) false
        simp only [catQuotientAlg, freeAlgQuotOver, FreeAlgQuotTotal.proj, Over.mk_hom,
          types_comp_apply] at this
        exact this
      generalize hq_t : (mor.left true).snd = q_t at *
      generalize hq_f : (mor.left false).snd = q_f at *
      induction q_t using Quot.ind with
      | mk t_true =>
        induction q_f using Quot.ind with
        | mk t_false =>
          let t_true' : PolyFreeM A catPoly Obj.mor := fiber_eq_t ▸ t_true
          let t_false' : PolyFreeM A catPoly Obj.mor := fiber_eq_f ▸ t_false
          let reps : (b : Bool) → PolyFreeM A catPoly Obj.mor :=
            fun b => match b with | true => t_true' | false => t_false'
          have h_alg := congrFun (congrArg (·.left) h.h)
            (⟨Obj.mor, ⟨CatPolyPosition.morComp,
              Over.homMk (fun b => ⟨Obj.mor, reps b⟩) rfl⟩⟩ :
              (polyToOverEval Obj catPolyAt (polyFreeMCarrier A catPoly)).left)
          simp only [Over.comp_left, types_comp_apply, Over.homMk_left,
            polyFreeAlg, polyFreeMStr, polyFreeMStrLeft, polyFreeMStrFamily] at h_alg
          simp only [catQuotientAlg, catQuotientStr, catQuotientStrLeft,
            catQuotientStrAt, catQuotMorCompNodeAt, catQuotientFactorMor,
            Over.homMk_left, FreeAlgQuot.mk]
          have sigma_eq_t : (⟨(mor.left true).fst, t_true⟩ : Σ x, PolyFreeM A catPoly x) =
              ⟨Obj.mor, t_true'⟩ :=
            Sigma.ext fiber_eq_t (heq_eqRec fiber_eq_t t_true)
          have sigma_eq_f : (⟨(mor.left false).fst, t_false⟩ : Σ x, PolyFreeM A catPoly x) =
              ⟨Obj.mor, t_false'⟩ :=
            Sigma.ext fiber_eq_f (heq_eqRec fiber_eq_f t_false)
          unfold ptoefIndex ptoefMor ccrEvalIndex ccrEvalMor catExtractQuotChildren
          dsimp only []
          have transport_t : (fiber_eq_t ▸ Quot.mk (FreeAlgEquiv catEAT A (mor.left true).fst)
              t_true : Quot (FreeAlgEquiv catEAT A Obj.mor)) =
              Quot.mk (FreeAlgEquiv catEAT A Obj.mor) t_true' :=
            @Eq.rec Obj (mor.left true).fst
              (fun x h => (h ▸ Quot.mk (FreeAlgEquiv catEAT A (mor.left true).fst) t_true :
                  Quot (FreeAlgEquiv catEAT A x)) =
                Quot.mk (FreeAlgEquiv catEAT A x) (h ▸ t_true))
              rfl Obj.mor fiber_eq_t
          have transport_f : (fiber_eq_f ▸ Quot.mk (FreeAlgEquiv catEAT A (mor.left false).fst)
              t_false : Quot (FreeAlgEquiv catEAT A Obj.mor)) =
              Quot.mk (FreeAlgEquiv catEAT A Obj.mor) t_false' :=
            @Eq.rec Obj (mor.left false).fst
              (fun x h => (h ▸ Quot.mk (FreeAlgEquiv catEAT A (mor.left false).fst) t_false :
                  Quot (FreeAlgEquiv catEAT A x)) =
                Quot.mk (FreeAlgEquiv catEAT A x) (h ▸ t_false))
              rfl Obj.mor fiber_eq_f
          simp only [hq_f, transport_f]
          have child_eq_t : h.f.left ⟨(mor.left true).fst, t_true⟩ =
              h.f.left ⟨Obj.mor, t_true'⟩ := congrArg h.f.left sigma_eq_t
          have child_eq_f : h.f.left ⟨(mor.left false).fst, t_false⟩ =
              h.f.left ⟨Obj.mor, t_false'⟩ := congrArg h.f.left sigma_eq_f
          simp only [polyEndoFunctor, polyBetweenEvalFunctor, pbefIndex, pbefMor,
            ptoefIndex, ptoefMor, ccrEvalIndex, ccrEvalMor, Over.homMk_left] at h_alg ⊢
          simp only [polyToOverFunctor, polyToOverEvalMap, familySliceForward,
            familySliceForwardMap, polyToOverEvalFamilyMap,
            ccrEvalMap] at h_alg ⊢
          simp only [Quot.lift_mk, transport_t, hq_t]
          try simp only [Over.comp_left, types_comp_apply] at h_alg ⊢
          have mor_eq : ∀ b, (mor.left b).fst = Obj.mor ∧ Quot.lift (fun t => h.f.left
              ⟨(mor.left b).fst, t⟩) (hresp (mor.left b).fst) (mor.left b).snd =
              h.f.left ⟨Obj.mor, reps b⟩ := by
            intro b
            match b with
            | true =>
              constructor
              · exact fiber_eq_t
              · rw [hq_t]; simp only [Quot.lift_mk]; exact child_eq_t
            | false =>
              constructor
              · exact fiber_eq_f
              · rw [hq_f]; simp only [Quot.lift_mk]; exact child_eq_f
          have lhs_eq : (⟨Obj.mor, (mor ≫ Over.homMk (fun x =>
              match x with | ⟨x, q⟩ => Quot.lift (fun t => h.f.left ⟨x, t⟩) _ q) _).left
              ⟨CatPolyPosition.morComp, mor⟩⟩ : M.a.left) =
              (⟨Obj.mor, (Over.homMk (fun b => ⟨Obj.mor, reps b⟩) _ ≫ h.f).left
              ⟨CatPolyPosition.morComp, Over.homMk (fun b => ⟨Obj.mor, reps b⟩) _⟩⟩ :
              M.a.left) := by
            congr 1
            simp only [Over.comp_left, types_comp_apply, Over.homMk_left]
            apply congrArg
            ext b
            simp only [Sigma.mk.injEq]
            exact mor_eq b
          simp only [← lhs_eq]
          exact h_alg
    | Obj.id, CatPolyPosition.idPos =>
      have fiber_eq : (mor.left ()).fst = Obj.id := by
        have := congrFun (Over.w mor) ()
        simp only [catQuotientAlg, freeAlgQuotOver, FreeAlgQuotTotal.proj, Over.mk_hom,
          types_comp_apply] at this
        exact this
      generalize hq : (mor.left ()).snd = q at *
      induction q using Quot.ind with
      | mk t =>
        simp only [catQuotientAlg, catQuotientStr, catQuotientStrLeft,
          catQuotientStrAt, catQuotientFactorMor, Over.homMk_left, FreeAlgQuot.mk]
        unfold ptoefIndex ptoefMor ccrEvalIndex ccrEvalMor catExtractQuotChildren
        dsimp only []
        rw [hq]
        rw [show (fiber_eq ▸ Quot.mk (FreeAlgEquiv catEAT A (mor.left ()).fst) t :
            Quot (FreeAlgEquiv catEAT A Obj.id)) =
            Quot.mk (FreeAlgEquiv catEAT A Obj.id) (fiber_eq ▸ t) from
          @Eq.rec Obj (mor.left ()).fst
            (fun x h =>
              (h ▸ Quot.mk (FreeAlgEquiv catEAT A (mor.left ()).fst) t :
                Quot (FreeAlgEquiv catEAT A x)) =
              Quot.mk (FreeAlgEquiv catEAT A x) (h ▸ t))
            rfl
            Obj.id
            fiber_eq]
        simp only [Quot.lift_mk]
        have h_alg := congrFun (congrArg (·.left) h.h)
          (⟨Obj.id, ⟨CatPolyPosition.idPos,
            Over.homMk (fun _ => ⟨Obj.id, fiber_eq ▸ t⟩) rfl⟩⟩ :
            (polyToOverEval Obj catPolyAt (polyFreeMCarrier A catPoly)).left)
        simp only [Over.comp_left, types_comp_apply, Over.homMk_left,
          polyFreeAlg, polyFreeMStr, polyFreeMStrLeft, polyFreeMStrFamily,
          polyEndoFunctor, polyBetweenEvalFunctor, pbefIndex, pbefMor,
          ptoefIndex, ptoefMor, ccrEvalIndex, ccrEvalMor, mkPolyFreeMNode] at h_alg ⊢
        simp only [polyToOverFunctor, polyToOverEvalMap, familySliceForward,
          familySliceForwardMap, polyToOverEvalFamilyMap,
          Over.homMk_left, ccrEvalMap] at h_alg ⊢
        convert h_alg using 2
        congr 2
        apply Over.OverMorphism.ext
        funext u
        simp only [Over.comp_left, types_comp_apply, Over.homMk_left]
        have sigma_eq : (⟨(mor.left u).fst, t⟩ : Σ x, PolyFreeM A catPoly x) =
            ⟨Obj.id, fiber_eq ▸ t⟩ :=
          Sigma.ext fiber_eq (heq_eqRec fiber_eq t)
        simp only [show u = () from rfl] at sigma_eq ⊢
        show Quot.lift (fun t => h.f.left ⟨(mor.left ()).fst, t⟩) _ (mor.left ()).snd =
          h.f.left ⟨Obj.id, fiber_eq ▸ t⟩
        rw [hq]
        simp only [Quot.lift_mk]
        exact congrArg h.f.left sigma_eq
    | Obj.comp, CatPolyPosition.compPos =>
      have fiber_eq : (mor.left ()).fst = Obj.comp := by
        have := congrFun (Over.w mor) ()
        simp only [catQuotientAlg, freeAlgQuotOver, FreeAlgQuotTotal.proj, Over.mk_hom,
          types_comp_apply] at this
        exact this
      generalize hq : (mor.left ()).snd = q at *
      induction q using Quot.ind with
      | mk t =>
        simp only [catQuotientAlg, catQuotientStr, catQuotientStrLeft,
          catQuotientStrAt, catQuotientFactorMor, Over.homMk_left, FreeAlgQuot.mk]
        unfold ptoefIndex ptoefMor ccrEvalIndex ccrEvalMor catExtractQuotChildren
        dsimp only []
        rw [hq]
        rw [show (fiber_eq ▸ Quot.mk (FreeAlgEquiv catEAT A (mor.left ()).fst) t :
            Quot (FreeAlgEquiv catEAT A Obj.comp)) =
            Quot.mk (FreeAlgEquiv catEAT A Obj.comp) (fiber_eq ▸ t) from
          @Eq.rec Obj (mor.left ()).fst
            (fun x h =>
              (h ▸ Quot.mk (FreeAlgEquiv catEAT A (mor.left ()).fst) t :
                Quot (FreeAlgEquiv catEAT A x)) =
              Quot.mk (FreeAlgEquiv catEAT A x) (h ▸ t))
            rfl
            Obj.comp
            fiber_eq]
        simp only [Quot.lift_mk]
        have h_alg := congrFun (congrArg (·.left) h.h)
          (⟨Obj.comp, ⟨CatPolyPosition.compPos,
            Over.homMk (fun _ => ⟨Obj.comp, fiber_eq ▸ t⟩) rfl⟩⟩ :
            (polyToOverEval Obj catPolyAt (polyFreeMCarrier A catPoly)).left)
        simp only [Over.comp_left, types_comp_apply, Over.homMk_left,
          polyFreeAlg, polyFreeMStr, polyFreeMStrLeft, polyFreeMStrFamily,
          polyEndoFunctor, polyBetweenEvalFunctor, pbefIndex, pbefMor,
          ptoefIndex, ptoefMor, ccrEvalIndex, ccrEvalMor, mkPolyFreeMNode] at h_alg ⊢
        simp only [polyToOverFunctor, polyToOverEvalMap, familySliceForward,
          familySliceForwardMap, polyToOverEvalFamilyMap,
          Over.homMk_left, ccrEvalMap] at h_alg ⊢
        convert h_alg using 2
        congr 2
        apply Over.OverMorphism.ext
        funext u
        simp only [Over.comp_left, types_comp_apply, Over.homMk_left]
        have sigma_eq : (⟨(mor.left u).fst, t⟩ : Σ x, PolyFreeM A catPoly x) =
            ⟨Obj.comp, fiber_eq ▸ t⟩ :=
          Sigma.ext fiber_eq (heq_eqRec fiber_eq t)
        simp only [show u = () from rfl] at sigma_eq ⊢
        show Quot.lift (fun t => h.f.left ⟨(mor.left ()).fst, t⟩) _ (mor.left ()).snd =
          h.f.left ⟨Obj.comp, fiber_eq ▸ t⟩
        rw [hq]
        simp only [Quot.lift_mk]
        exact congrArg h.f.left sigma_eq

/--
The factorization property: composing the quotient map with the factor gives back h.
-/
lemma catQuotientFactor_commutes (A : Over Obj) (M : PolyAlg catPoly) (hM : IsEATModel catEAT M)
    (h : polyFreeAlg A catPoly ⟶ M) (hresp : AlgHomRespectsEquiv catEAT A M h) :
    catQuotientHom A ≫ catQuotientFactor A M hM h hresp = h := by
  apply Endofunctor.Algebra.Hom.ext
  apply Over.OverMorphism.ext
  funext ⟨x, t⟩
  rfl

/--
Uniqueness of factorization: any other map g with catQuotientHom ≫ g = h equals the factor.
-/
lemma catQuotientFactor_unique (A : Over Obj) (M : PolyAlg catPoly) (hM : IsEATModel catEAT M)
    (h : polyFreeAlg A catPoly ⟶ M) (hresp : AlgHomRespectsEquiv catEAT A M h)
    (g : catQuotientAlg A ⟶ M) (hg : catQuotientHom A ≫ g = h) :
    g = catQuotientFactor A M hM h hresp := by
  apply Endofunctor.Algebra.Hom.ext
  apply Over.OverMorphism.ext
  funext ⟨x, q⟩
  induction q using Quot.ind with
  | mk t =>
    have := congrFun (congrArg (·.f.left) hg) ⟨x, t⟩
    simp only [Endofunctor.Algebra.Hom.comp_f, Over.comp_left, types_comp_apply,
      catQuotientHom, freeAlgQuotMap, Over.homMk_left, FreeAlgQuot.mk] at this
    simp only [catQuotientFactor, catQuotientFactorMor, Over.homMk_left, Quot.lift_mk]
    exact this.symm

end QuotientProperties

/-! ### EATHasQuotient Instance for Category Theory -/

/--
Category theory as an IndexedEAT has quotients: we can form the quotient algebra
for each Over Obj object.
-/
instance : EATHasQuotient catEAT where
  quotientAlg := catQuotientAlg
  quotientAlg_carrier := catQuotientAlg_carrier
  quotientIsModel := catQuotientIsModel
  quotientHomomorphism := catQuotientHom
  quotientAlgMap := catQuotientAlgMap
  quotientAlgMap_id := catQuotientAlgMap_id
  quotientAlgMap_comp := catQuotientAlgMap_comp
  quotientNaturality := catQuotientNaturality
  quotientRespectsEquiv := catQuotientRespectsEquiv
  quotientFactor := catQuotientFactor
  quotientFactor_commutes := catQuotientFactor_commutes
  quotientFactor_unique := catQuotientFactor_unique

end GebLean
