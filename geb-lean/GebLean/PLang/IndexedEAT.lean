import GebLean.PolyAlg

/-!
# Indexed Essentially Algebraic Theories

This module defines essentially algebraic theories (EATs) indexed by a type X,
and provides the framework for embedding models into copresheaf categories.

An indexed EAT over X consists of:
- A polynomial endofunctor P on Over X (encoding operations)
- An equivalence relation on PolyFix P (encoding equations)

The construction uses setoid-enriched algebras.  A model is a P-algebra
equipped with a map from the initial algebra that respects the EAT equations.

## Main definitions

- `IndexedEAT X` : An essentially algebraic theory indexed by X
- `EATCongruence` : Congruence condition ensuring quotients are algebras
- `SetoidOverX` : Setoid-valued families over X
- `PolySetoidAlg` : P-algebras with setoid structure

## References

See `docs/generic-essentially-algebraic-embedding.md` for mathematical background.
-/

namespace GebLean

open CategoryTheory

universe u

/-! ## Core Definitions -/

section IndexedEAT

variable (X : Type u)

/--
An equivalence relation on the initial algebra carrier PolyFix P,
indexed by fiber.
-/
def PolyFixRel (P : PolyEndo X) : Type u :=
  ∀ x, PolyFix P x → PolyFix P x → Prop

/--
A PolyFixRel is reflexive at all fibers.
-/
def PolyFixRel.Reflexive {P : PolyEndo X} (R : PolyFixRel X P) : Prop :=
  ∀ x t, R x t t

/--
A PolyFixRel is symmetric at all fibers.
-/
def PolyFixRel.Symmetric {P : PolyEndo X} (R : PolyFixRel X P) : Prop :=
  ∀ x, ∀ {t₁ t₂}, R x t₁ t₂ → R x t₂ t₁

/--
A PolyFixRel is transitive at all fibers.
-/
def PolyFixRel.Transitive {P : PolyEndo X} (R : PolyFixRel X P) : Prop :=
  ∀ x, ∀ {t₁ t₂ t₃}, R x t₁ t₂ → R x t₂ t₃ → R x t₁ t₃

/--
A PolyFixRel is an equivalence relation at all fibers.
-/
structure PolyFixRel.IsEquivalence {P : PolyEndo X} (R : PolyFixRel X P) : Prop
    where
  refl : R.Reflexive
  symm : R.Symmetric
  trans : R.Transitive

/--
An indexed essentially algebraic theory over X consists of:
- A polynomial endofunctor P on Over X
- An equivalence relation on PolyFix P (the equations)
-/
structure IndexedEAT where
  /-- The polynomial endofunctor encoding operations. -/
  poly : PolyEndo X
  /-- The relation on initial algebra elements (equations). -/
  equations : PolyFixRel X poly
  /-- The relation is an equivalence. -/
  eqIsEquiv : equations.IsEquivalence

end IndexedEAT

/-! ## Congruence Condition

For the quotient of an algebra by equations to remain an algebra,
the equations must form a congruence - they must be respected by the
algebra structure map.
-/

section Congruence

variable {X : Type u}

/--
The congruence condition for equations on a polynomial endofunctor.

For an algebra A with structure map str : P(A) → A, the equations R form
a congruence if:
- When we have nodes with the same P-index and R-related children,
  their images under str are R-related.

This ensures the quotient of A by R inherits the algebra structure.
-/
structure EATCongruence (T : IndexedEAT X) : Prop where
  /-- Equations respect the algebra structure. -/
  cong : ∀ (x : X) (p : polyBetweenIndex X X T.poly x)
         (children₁ children₂ : ∀ e : (polyBetweenFamily X X T.poly x p).left,
           PolyFix T.poly ((polyBetweenFamily X X T.poly x p).hom e)),
         (∀ e, T.equations _ (children₁ e) (children₂ e)) →
         T.equations x (PolyFix.mk x p children₁) (PolyFix.mk x p children₂)

end Congruence

/-! ## Setoid-Enriched Structures
-/

section SetoidOver

variable (X : Type u)

/--
A setoid-enriched object over X: a type family with fiberwise equivalence.
-/
structure SetoidOverX where
  /-- The carrier type at each fiber. -/
  carrier : X → Type u
  /-- The equivalence relation at each fiber. -/
  rel : ∀ x, carrier x → carrier x → Prop
  /-- The relation is an equivalence at each fiber. -/
  isEquiv : ∀ x, Equivalence (rel x)

/--
The setoid at a specific fiber.
-/
def SetoidOverX.setoidAt (S : SetoidOverX X) (x : X) : Setoid (S.carrier x) where
  r := S.rel x
  iseqv := S.isEquiv x

/--
The total space of a setoid over X.
-/
def SetoidOverX.total (S : SetoidOverX X) : Type u :=
  Σ x, S.carrier x

/--
The projection from total space to X.
-/
def SetoidOverX.proj (S : SetoidOverX X) : S.total → X :=
  Sigma.fst

/--
The underlying Over X object (forgetting the setoid structure).
-/
def SetoidOverX.toOver (S : SetoidOverX X) : Over X :=
  Over.mk S.proj

end SetoidOver

/-! ## The Initial Algebra as a Setoid Over X

Given an IndexedEAT, the initial algebra PolyFix forms a SetoidOverX
with the EAT equations as the equivalence relation.
-/

section InitialSetoid

variable {X : Type u}

/--
The initial P-algebra as a setoid over X, with EAT equations.
-/
def IndexedEAT.initialSetoid (T : IndexedEAT X) : SetoidOverX X where
  carrier := PolyFix T.poly
  rel := T.equations
  isEquiv := fun x => {
    refl := T.eqIsEquiv.refl x
    symm := T.eqIsEquiv.symm x
    trans := T.eqIsEquiv.trans x
  }

/--
The underlying Over X object of the initial setoid is the initial algebra
carrier.
-/
lemma IndexedEAT.initialSetoid_toOver (T : IndexedEAT X) :
    T.initialSetoid.toOver = polyFixCarrier T.poly := by
  rfl

end InitialSetoid

/-! ## Setoid-Respecting Morphisms

A morphism between setoid-over-X objects is a fiberwise function that
respects the equivalence relations.
-/

section SetoidMorphism

variable {X : Type u}

/--
A setoid-respecting morphism between SetoidOverX objects.
-/
structure SetoidOverMor (S₁ S₂ : SetoidOverX X) where
  /-- The underlying function at each fiber. -/
  fn : ∀ x, S₁.carrier x → S₂.carrier x
  /-- The function respects equivalence. -/
  respectsRel : ∀ x a₁ a₂, S₁.rel x a₁ a₂ → S₂.rel x (fn x a₁) (fn x a₂)

/--
The identity setoid morphism.
-/
def SetoidOverMor.id (S : SetoidOverX X) : SetoidOverMor S S where
  fn := fun _ a => a
  respectsRel := fun _ _ _ h => h

/--
Composition of setoid morphisms.
-/
def SetoidOverMor.comp {S₁ S₂ S₃ : SetoidOverX X}
    (g : SetoidOverMor S₂ S₃) (f : SetoidOverMor S₁ S₂) : SetoidOverMor S₁ S₃ where
  fn := fun x => g.fn x ∘ f.fn x
  respectsRel := fun x a₁ a₂ h => g.respectsRel x _ _ (f.respectsRel x a₁ a₂ h)

end SetoidMorphism

/-! ## Model Predicate

A P-algebra A is a model of EAT T if the canonical fold from the initial
algebra respects the EAT equations. The fold always exists (by initiality);
being a model means the fold collapses equation-equivalent elements.
-/

section ModelPredicate

variable {X : Type u}

/--
A P-algebra is a model of EAT T if the fold morphism respects the equations.

The fold `polyFixFold T.poly A : polyFixAlg T.poly ⟶ A` is the unique
algebra homomorphism from the initial algebra. Being a model means this
fold maps equivalent PolyFix elements to equal elements in A.
-/
def IsEATModel (T : IndexedEAT X) (A : PolyAlg T.poly) : Prop :=
  ∀ x (t₁ t₂ : PolyFix T.poly x),
    T.equations x t₁ t₂ →
    polyFixFoldLeft T.poly A ⟨x, t₁⟩ = polyFixFoldLeft T.poly A ⟨x, t₂⟩

/--
The fold morphism for a model.
-/
def modelFold (T : IndexedEAT X) (A : PolyAlg T.poly) :
    polyFixAlg T.poly ⟶ A :=
  polyFixFoldHom T.poly A

/--
Alternative characterization: A is a model iff the fold's left component
sends equation-equivalent elements to equal elements.
-/
lemma isEATModel_iff_fold (T : IndexedEAT X) (A : PolyAlg T.poly) :
    IsEATModel T A ↔
    ∀ x (t₁ t₂ : PolyFix T.poly x),
      T.equations x t₁ t₂ →
      (modelFold T A).f.left ⟨x, t₁⟩ = (modelFold T A).f.left ⟨x, t₂⟩ :=
  Iff.rfl

end ModelPredicate

/-! ## The Free Algebra Functor

The free P-algebra on an object A : Over X is given by PolyFreeM A P.
This has already been constructed in PolyAlg.lean as polyFreeFunctor.
-/

section FreeAlgebra

variable {X : Type u}

/--
The free algebra functor for an EAT is the polynomial free algebra functor.
-/
abbrev IndexedEAT.freeFunctor (T : IndexedEAT X) : Over X ⥤ PolyAlg T.poly :=
  polyFreeFunctor T.poly

/--
The forgetful functor for an EAT is the polynomial forgetful functor.
-/
abbrev IndexedEAT.forgetFunctor (T : IndexedEAT X) : PolyAlg T.poly ⥤ Over X :=
  polyForgetFunctor T.poly

/--
The unit of the Free ⊣ Forget adjunction.
-/
abbrev IndexedEAT.freeUnit (T : IndexedEAT X) :
    𝟭 (Over X) ⟶ T.freeFunctor ⋙ T.forgetFunctor :=
  polyFreeUnitNat T.poly

end FreeAlgebra

/-! ## The Model Category

Models form a full subcategory of PolyAlg. A model is a P-algebra A such that
the canonical fold from the initial algebra respects the EAT equations.
-/

section ModelCategory

variable {X : Type u}

/--
A bundled EAT model: a P-algebra together with proof it's a model.
-/
structure EATModel (T : IndexedEAT X) where
  /-- The underlying P-algebra. -/
  alg : PolyAlg T.poly
  /-- Proof that the algebra is a model. -/
  isModel : IsEATModel T alg

/--
The forgetful functor from models to P-algebras (just forgets the proof).
-/
def EATModel.toAlg (T : IndexedEAT X) (M : EATModel T) : PolyAlg T.poly :=
  M.alg

/--
Morphisms between models are just algebra homomorphisms between underlying
algebras. This gives a full subcategory structure.
-/
def EATModelHom (T : IndexedEAT X) (M₁ M₂ : EATModel T) : Type u :=
  M₁.alg ⟶ M₂.alg

instance (T : IndexedEAT X) : Category (EATModel T) where
  Hom := EATModelHom T
  id := fun M => 𝟙 M.alg
  comp := fun f g => f ≫ g
  id_comp := fun f => Category.id_comp f
  comp_id := fun f => Category.comp_id f
  assoc := fun f g h => Category.assoc f g h

/--
The inclusion functor from models to P-algebras.
-/
def EATModel.inclusionFunctor (T : IndexedEAT X) : EATModel T ⥤ PolyAlg T.poly where
  obj := fun M => M.alg
  map := fun f => f
  map_id := fun _ => rfl
  map_comp := fun _ _ => rfl

/--
The inclusion is fully faithful.
-/
def EATModel.inclusionFullyFaithful (T : IndexedEAT X) :
    (EATModel.inclusionFunctor T).FullyFaithful where
  preimage := fun f => f
  map_preimage := fun _ => rfl
  preimage_map := fun _ => rfl

end ModelCategory

/-! ## The Embedding Functor

The embedding Φ : EATModel → Over X is the composition:
  EATModel → PolyAlg T.poly → Over X

This forgets both the model property and the algebra structure.
-/

section Embedding

variable {X : Type u}

/--
The embedding functor from models to Over X.
This composes the inclusion with the forgetful functor.
-/
def EATModel.embeddingFunctor (T : IndexedEAT X) : EATModel T ⥤ Over X :=
  EATModel.inclusionFunctor T ⋙ T.forgetFunctor

end Embedding

/-! ## Trivial EAT (Identity Relation)

When the equations are trivial (everything related only to itself),
the initial algebra is already a model.
-/

section TrivialEAT

variable {X : Type u}

/--
The trivial equivalence relation where each element is only related to itself.
-/
def trivialPolyFixRel (P : PolyEndo X) : PolyFixRel X P :=
  fun _ t₁ t₂ => t₁ = t₂

/--
The trivial relation is an equivalence.
-/
def trivialPolyFixRel_isEquiv (P : PolyEndo X) :
    (trivialPolyFixRel P).IsEquivalence where
  refl := fun x t => @rfl (PolyFix P x) t
  symm := fun _ {t₁ t₂} (h : t₁ = t₂) => h.symm
  trans := fun _ {t₁ t₂ t₃} (h₁ : t₁ = t₂) (h₂ : t₂ = t₃) => h₁.trans h₂

/--
The trivial EAT on a polynomial P has no nontrivial equations.
-/
def trivialEAT (P : PolyEndo X) : IndexedEAT X where
  poly := P
  equations := trivialPolyFixRel P
  eqIsEquiv := trivialPolyFixRel_isEquiv P

/--
Every P-algebra is a model of the trivial EAT.
-/
lemma trivialEAT_allModels (P : PolyEndo X) (A : PolyAlg P) :
    IsEATModel (trivialEAT P) A := by
  intro x t₁ t₂ h
  simp only [trivialEAT, trivialPolyFixRel] at h
  rw [h]

end TrivialEAT

/-! ## Reflector for Trivial EAT

For the trivial EAT, every algebra is a model, so the reflector is essentially
the identity: it wraps each algebra with the proof that it's a model.
-/

section TrivialReflector

variable {X : Type u}

/--
The reflector for trivial EAT: wraps any algebra as a model.
-/
def trivialEAT.reflector (P : PolyEndo X) (A : PolyAlg P) : EATModel (trivialEAT P) where
  alg := A
  isModel := trivialEAT_allModels P A

/--
The reflector functor for trivial EAT: PolyAlg P → EATModel (trivialEAT P).
-/
def trivialEAT.reflectorFunctor (P : PolyEndo X) :
    PolyAlg P ⥤ EATModel (trivialEAT P) where
  obj := trivialEAT.reflector P
  map := fun f => f
  map_id := fun _ => rfl
  map_comp := fun _ _ => rfl

/--
The unit of the reflector adjunction for trivial EAT is the identity.
-/
def trivialEAT.reflectorUnit (P : PolyEndo X) :
    𝟭 (PolyAlg P) ⟶ trivialEAT.reflectorFunctor P ⋙ EATModel.inclusionFunctor _ where
  app := fun A => 𝟙 A
  naturality := fun _ _ f => by
    simp only [Functor.id_obj, Functor.comp_obj, Functor.id_map,
      Functor.comp_map, EATModel.inclusionFunctor, trivialEAT.reflectorFunctor]
    rfl

/--
The counit of the reflector adjunction for trivial EAT is the identity.
-/
def trivialEAT.reflectorCounit (P : PolyEndo X) :
    EATModel.inclusionFunctor (trivialEAT P) ⋙ trivialEAT.reflectorFunctor P ⟶
    𝟭 (EATModel (trivialEAT P)) where
  app := fun M => 𝟙 M
  naturality := fun _ _ f => by
    simp only [Functor.comp_obj, Functor.id_obj, Functor.comp_map,
      Functor.id_map, EATModel.inclusionFunctor, trivialEAT.reflectorFunctor]
    exact (Category.comp_id f).trans (Category.id_comp f).symm

/--
The adjunction Reflector ⊣ Inclusion for trivial EAT.
-/
def trivialEAT.reflectorAdjunction (P : PolyEndo X) :
    trivialEAT.reflectorFunctor P ⊣ EATModel.inclusionFunctor (trivialEAT P) :=
  Adjunction.mkOfUnitCounit {
    unit := trivialEAT.reflectorUnit P
    counit := trivialEAT.reflectorCounit P
    left_triangle := by
      ext A
      simp only [NatTrans.comp_app, Functor.comp_obj, Functor.id_obj,
        trivialEAT.reflectorUnit, trivialEAT.reflectorCounit,
        EATModel.inclusionFunctor, trivialEAT.reflectorFunctor]
      rfl
    right_triangle := by
      ext M
      simp only [NatTrans.comp_app, Functor.id_obj, Functor.comp_obj,
        trivialEAT.reflectorUnit, trivialEAT.reflectorCounit,
        EATModel.inclusionFunctor, trivialEAT.reflectorFunctor]
      rfl
  }

end TrivialReflector

/-! ## Composed Adjunction for Trivial EAT

For the trivial EAT, the composed adjunction L ⊣ Φ where:
- L = ReflectorFunctor ∘ FreeFunctor : Over X → EATModel (trivialEAT P)
- Φ = EmbeddingFunctor : EATModel (trivialEAT P) → Over X

This gives the full embedding of all P-algebras (as models) into Over X.
-/

section TrivialComposedAdjunction

variable {X : Type u}

/--
The left adjoint L for trivial EAT: composes Free with the trivial reflector.
-/
def trivialEAT.leftAdjoint (P : PolyEndo X) : Over X ⥤ EATModel (trivialEAT P) :=
  polyFreeFunctor P ⋙ trivialEAT.reflectorFunctor P

/--
The right adjoint Φ for trivial EAT: the embedding functor.
-/
abbrev trivialEAT.rightAdjoint (P : PolyEndo X) : EATModel (trivialEAT P) ⥤ Over X :=
  EATModel.embeddingFunctor (trivialEAT P)

end TrivialComposedAdjunction

/-! ## Generic Quotient Construction

The quotient of a free algebra by EAT equations is constructed generically.
Given any IndexedEAT T with a congruence condition, the quotient of Free(A)
by the EAT equations produces a model.

The construction uses:
1. The equivalence relation on PolyFreeM induced by EAT equations
2. The congruence condition to lift the algebra structure to the quotient
3. Quot types to form the actual quotient
-/

section GenericQuotient

variable {X : Type u}

/--
Embed a PolyFix element into PolyFreeM A P as a "closed" tree.
This is the image of the fold from the initial algebra to the free algebra.
Closed trees use only Sum.inr indices (P-operations), never Sum.inl (A-leaves).
-/
def polyFixToFreeAlg (P : PolyEndo X) (A : Over X) (x : X) :
    PolyFix P x → PolyFreeM A P x
  | PolyFix.mk _ p children =>
    PolyFix.mk x (Sum.inr p) (fun e => polyFixToFreeAlg P A _ (children e))

/--
The equivalence relation on free algebra elements induced by EAT equations.

Two elements of PolyFreeM A P are equivalent if:
- They are reflexively equal, or
- One can be obtained from the other by symmetry or transitivity, or
- They arise from equation-equivalent PolyFix elements, or
- They are P-nodes with the same index and equivalent children

The EAT equations apply to "closed" subtrees (those embedded from PolyFix).
-/
inductive FreeAlgEquiv (T : IndexedEAT X) (A : Over X) :
    (x : X) → PolyFreeM A T.poly x → PolyFreeM A T.poly x → Prop where
  /-- Reflexivity. -/
  | refl : ∀ x t, FreeAlgEquiv T A x t t
  /-- Symmetry. -/
  | symm : ∀ x t₁ t₂, FreeAlgEquiv T A x t₁ t₂ → FreeAlgEquiv T A x t₂ t₁
  /-- Transitivity. -/
  | trans : ∀ x t₁ t₂ t₃,
      FreeAlgEquiv T A x t₁ t₂ → FreeAlgEquiv T A x t₂ t₃ →
      FreeAlgEquiv T A x t₁ t₃
  /-- EAT equations: equation-equivalent PolyFix elements embed to equivalent. -/
  | fromEq : ∀ x (t₁ t₂ : PolyFix T.poly x),
      T.equations x t₁ t₂ →
      FreeAlgEquiv T A x
        (polyFixToFreeAlg T.poly A x t₁)
        (polyFixToFreeAlg T.poly A x t₂)
  /-- Congruence: equivalent children give equivalent P-nodes. -/
  | cong : ∀ x (p : polyBetweenIndex X X T.poly x)
      (children₁ children₂ : ∀ e : (polyBetweenFamily X X T.poly x p).left,
        PolyFreeM A T.poly ((polyBetweenFamily X X T.poly x p).hom e)),
      (∀ e, FreeAlgEquiv T A _ (children₁ e) (children₂ e)) →
      FreeAlgEquiv T A x
        (PolyFix.mk x (Sum.inr p) children₁)
        (PolyFix.mk x (Sum.inr p) children₂)

/--
The equivalence relation is indeed an equivalence.
-/
def FreeAlgEquiv.isEquivalence (T : IndexedEAT X) (A : Over X) (x : X) :
    Equivalence (FreeAlgEquiv T A x) where
  refl := FreeAlgEquiv.refl x
  symm := FreeAlgEquiv.symm x _ _
  trans := FreeAlgEquiv.trans x _ _ _

/--
The setoid on free algebra elements at fiber x.
-/
def freeAlgSetoid (T : IndexedEAT X) (A : Over X) (x : X) :
    Setoid (PolyFreeM A T.poly x) where
  r := FreeAlgEquiv T A x
  iseqv := FreeAlgEquiv.isEquivalence T A x

/--
The quotient type for free algebra elements at fiber x.
-/
def FreeAlgQuot (T : IndexedEAT X) (A : Over X) (x : X) : Type u :=
  Quot (FreeAlgEquiv T A x)

/--
The quotient map from free algebra to quotient.
-/
def FreeAlgQuot.mk (T : IndexedEAT X) (A : Over X) {x : X}
    (t : PolyFreeM A T.poly x) : FreeAlgQuot T A x :=
  Quot.mk _ t

/--
The total space of the quotient.
-/
def FreeAlgQuotTotal (T : IndexedEAT X) (A : Over X) : Type u :=
  Σ x, FreeAlgQuot T A x

/--
The projection from quotient total space to X.
-/
def FreeAlgQuotTotal.proj (T : IndexedEAT X) (A : Over X) :
    FreeAlgQuotTotal T A → X :=
  Sigma.fst

/--
The quotient as an object of Over X.
-/
def freeAlgQuotOver (T : IndexedEAT X) (A : Over X) : Over X :=
  Over.mk (FreeAlgQuotTotal.proj T A)

/--
The quotient map from free algebra to quotient, as an Over X morphism.
-/
def freeAlgQuotMap (T : IndexedEAT X) (A : Over X) :
    polyFreeMCarrier A T.poly ⟶ freeAlgQuotOver T A :=
  Over.homMk (fun ⟨x, t⟩ => ⟨x, FreeAlgQuot.mk T A t⟩) rfl

/--
Lift a function on PolyFreeM to the quotient, given proof it respects equivalence.
-/
def FreeAlgQuot.lift {T : IndexedEAT X} {A : Over X} {x : X} {β : Type u}
    (f : PolyFreeM A T.poly x → β)
    (h : ∀ t₁ t₂, FreeAlgEquiv T A x t₁ t₂ → f t₁ = f t₂) :
    FreeAlgQuot T A x → β :=
  Quot.lift f h

/--
The fold from the quotient collapses equation-equivalent elements by construction.
-/
lemma freeAlgQuot_isModel (T : IndexedEAT X) (A : Over X) :
    ∀ x (t₁ t₂ : PolyFix T.poly x),
      T.equations x t₁ t₂ →
      FreeAlgQuot.mk T A (polyFixToFreeAlg T.poly A x t₁) =
      FreeAlgQuot.mk T A (polyFixToFreeAlg T.poly A x t₂) := by
  intro x t₁ t₂ heq
  apply Quot.sound
  exact FreeAlgEquiv.fromEq x t₁ t₂ heq

/-! ### Structure Map on Representatives

The structure map on the quotient is defined by lifting through the quotients.
Given children as representatives, the structure map forms a P-node and quotients.
-/

/--
The structure map on representatives: given an index and children as PolyFreeM
elements, form the P-node and quotient it.
-/
def freeAlgQuotStrRepr (T : IndexedEAT X) (A : Over X) (x : X)
    (p : polyBetweenIndex X X T.poly x)
    (children : ∀ e : (polyBetweenFamily X X T.poly x p).left,
      PolyFreeM A T.poly ((polyBetweenFamily X X T.poly x p).hom e)) :
    FreeAlgQuot T A x :=
  FreeAlgQuot.mk T A (PolyFix.mk x (Sum.inr p) children)

/--
The structure map on representatives respects pointwise equivalence.
This is the congruence property that allows lifting through quotients.
-/
lemma freeAlgQuotStrRepr_resp (T : IndexedEAT X) (A : Over X) (x : X)
    (p : polyBetweenIndex X X T.poly x)
    (c1 c2 : ∀ e : (polyBetweenFamily X X T.poly x p).left,
      PolyFreeM A T.poly ((polyBetweenFamily X X T.poly x p).hom e))
    (h : ∀ e, FreeAlgEquiv T A _ (c1 e) (c2 e)) :
    freeAlgQuotStrRepr T A x p c1 = freeAlgQuotStrRepr T A x p c2 := by
  apply Quot.sound
  exact FreeAlgEquiv.cong x p c1 c2 h

/--
The quotient map from PolyFreeM to FreeAlgQuot.
This is the coercion from representatives to quotient elements.
-/
def polyFreeMToQuot (T : IndexedEAT X) (A : Over X) {x : X} :
    PolyFreeM A T.poly x → FreeAlgQuot T A x :=
  FreeAlgQuot.mk T A

/--
The quotient map respects equivalence (by definition of Quot).
-/
lemma polyFreeMToQuot_resp (T : IndexedEAT X) (A : Over X) {x : X}
    (t₁ t₂ : PolyFreeM A T.poly x) (h : FreeAlgEquiv T A x t₁ t₂) :
    polyFreeMToQuot T A t₁ = polyFreeMToQuot T A t₂ :=
  Quot.sound h

end GenericQuotient

/-! ## Setoid-Based Quotient Algebra

To avoid the difficulty of lifting through products of quotients, we work with
a setoid-enriched view. A P-setoid-algebra has a setoid at each fiber, with
the algebra structure respecting the equivalence relation.

The free algebra with FreeAlgEquiv forms such a setoid-algebra, and any
setoid-respecting homomorphism to a model factors uniquely through the quotient.
-/

section SetoidQuotient

variable {X : Type u}

/--
A setoid-enriched P-algebra: the carrier with an equivalence relation, and
the algebra structure respects this relation.

The relation is on elements of the fiber at each x, i.e., on elements
`{ t : alg.a.left // alg.a.hom t = x }`.
-/
structure PolySetoidAlg (P : PolyEndo X) where
  /-- The underlying P-algebra. -/
  alg : PolyAlg P
  /-- The equivalence relation on the carrier at each fiber. -/
  rel : ∀ x, { t : alg.a.left // alg.a.hom t = x } →
            { t : alg.a.left // alg.a.hom t = x } → Prop
  /-- The relation is an equivalence at each fiber. -/
  isEquiv : ∀ x, Equivalence (rel x)

/--
For the free algebra, the carrier at fiber x is `{ t : Σ y, PolyFreeM A P y // y = x }`.
This helper extracts the underlying PolyFreeM at x by transport.
-/
def freeAlgFiberElem (T : IndexedEAT X) (A : Over X) (x : X)
    (t : { t : (polyFreeAlg A T.poly).a.left //
           (polyFreeAlg A T.poly).a.hom t = x }) :
    PolyFreeM A T.poly x :=
  t.property ▸ t.val.2

/--
The free algebra with FreeAlgEquiv forms a setoid-enriched algebra.
-/
def freeAlgSetoidAlg (T : IndexedEAT X) (A : Over X) : PolySetoidAlg T.poly where
  alg := polyFreeAlg A T.poly
  rel := fun x t₁ t₂ =>
    FreeAlgEquiv T A x
      (freeAlgFiberElem T A x t₁)
      (freeAlgFiberElem T A x t₂)
  isEquiv := fun x => {
    refl := fun t => FreeAlgEquiv.refl x (freeAlgFiberElem T A x t)
    symm := fun h => FreeAlgEquiv.symm x _ _ h
    trans := fun h1 h2 => FreeAlgEquiv.trans x _ _ _ h1 h2
  }

/--
An algebra homomorphism from the free algebra respects FreeAlgEquiv if it
maps equivalent elements to equal elements.
-/
def AlgHomRespectsEquiv (T : IndexedEAT X) (A : Over X) (M : PolyAlg T.poly)
    (h : polyFreeAlg A T.poly ⟶ M) : Prop :=
  ∀ x (t₁ t₂ : PolyFreeM A T.poly x),
    FreeAlgEquiv T A x t₁ t₂ →
    h.f.left ⟨x, t₁⟩ = h.f.left ⟨x, t₂⟩

/--
If M is a model, then the counit (fold from Free(carrier) to M) respects
the EAT equations, and hence respects FreeAlgEquiv.
-/
lemma modelCounitRespectsEq (T : IndexedEAT X) (M : EATModel T) :
    ∀ x (t₁ t₂ : PolyFix T.poly x),
      T.equations x t₁ t₂ →
      polyFixFoldLeft T.poly M.alg ⟨x, t₁⟩ =
      polyFixFoldLeft T.poly M.alg ⟨x, t₂⟩ :=
  M.isModel

/--
The fold from PolyFreeM to an algebra, when restricted to "closed" trees
(those embedded from PolyFix via polyFixToFreeAlg), equals the fold from
the initial algebra.

This is proved by induction on the PolyFix structure.
-/
lemma polyFreeCounitFoldAt_closed (T : IndexedEAT X) (α : PolyAlg T.poly)
    (x : X) (t : PolyFix T.poly x) :
    (polyFreeCounitFoldAt T.poly α x (polyFixToFreeAlg T.poly α.a x t)).val =
    (polyFixFoldAtWithProof T.poly α x t).val := by
  induction t with
  | mk y p children ih =>
    simp only [polyFixToFreeAlg, polyFreeCounitFoldAt, polyFixFoldAtWithProof]
    apply congrArg
    congr 1
    apply Sigma.ext
    · rfl
    · simp only [heq_eq_eq]
      apply Over.OverMorphism.ext
      funext e
      simp only [Over.homMk_left]
      exact ih e

/--
The fold from the free algebra on M's carrier to M respects EAT equations
on the embedded initial algebra elements.
-/
lemma freeAlgFoldRespectsFromEq (T : IndexedEAT X) (M : EATModel T)
    (x : X) (t₁ t₂ : PolyFix T.poly x)
    (heq : T.equations x t₁ t₂) :
    (polyFreeCounitFold T.poly M.alg).left
      ⟨x, polyFixToFreeAlg T.poly M.alg.a x t₁⟩ =
    (polyFreeCounitFold T.poly M.alg).left
      ⟨x, polyFixToFreeAlg T.poly M.alg.a x t₂⟩ := by
  simp only [polyFreeCounitFold, Over.homMk_left, polyFreeCounitFoldLeft]
  have h1 := polyFreeCounitFoldAt_closed T M.alg x t₁
  have h2 := polyFreeCounitFoldAt_closed T M.alg x t₂
  simp only [h1, h2]
  have heq' : polyFixFoldLeft T.poly M.alg ⟨x, t₁⟩ =
              polyFixFoldLeft T.poly M.alg ⟨x, t₂⟩ := M.isModel x t₁ t₂ heq
  simp only [polyFixFoldLeft] at heq'
  exact heq'

/--
The counit homomorphism from Free(Φ(M)) to M respects FreeAlgEquiv.

This follows from:
1. FreeAlgEquiv.fromEq: equations on PolyFix induce equivalence
2. FreeAlgEquiv.cong: the relation is a congruence
3. The model property: fold respects equations
-/
lemma freeAlgCounitRespectsEquiv (T : IndexedEAT X) (M : EATModel T) :
    AlgHomRespectsEquiv T M.alg.a M.alg (polyFreeCounitHom T.poly M.alg) := by
  intro x t₁ t₂ hequiv
  induction hequiv with
  | refl => rfl
  | @symm x t₁ t₂ _ ih => exact ih.symm
  | @trans x t₁ t₂ t₃ _ _ ih1 ih2 => exact ih1.trans ih2
  | fromEq x t₁ t₂ heq => exact freeAlgFoldRespectsFromEq T M x t₁ t₂ heq
  | cong x p children₁ children₂ _ ih =>
    simp only [polyFreeCounitHom, polyFreeCounitFold, Over.homMk_left,
      polyFreeCounitFoldLeft]
    have ih' : ∀ e, (polyFreeCounitFoldAt T.poly M.alg _ (children₁ e)).val =
                   (polyFreeCounitFoldAt T.poly M.alg _ (children₂ e)).val := ih
    simp only [polyFreeCounitFoldAt]
    apply congrArg
    congr 1
    apply Sigma.ext
    · rfl
    · simp only [heq_eq_eq]
      apply Over.OverMorphism.ext
      funext e
      exact ih' e

/--
A homomorphism that respects equivalence factors through the quotient.
This gives the induced map on quotient elements.
-/
def quotientLift (T : IndexedEAT X) (A : Over X) (M : PolyAlg T.poly)
    (h : polyFreeAlg A T.poly ⟶ M)
    (hresp : AlgHomRespectsEquiv T A M h)
    (x : X) : FreeAlgQuot T A x → { t : M.a.left // M.a.hom t = x } :=
  Quot.lift
    (fun t => ⟨h.f.left ⟨x, t⟩, congrFun (Over.w h.f) ⟨x, t⟩⟩)
    (fun t₁ t₂ hequiv => Subtype.ext (hresp x t₁ t₂ hequiv))

end SetoidQuotient

/-! ## Quotient Algebra via Induced Structure

For the quotient of a free algebra to inherit an algebra structure, we use
the universal property of quotients: the quotient map from FreeAlg to FreeAlgQuot
should be an algebra homomorphism. This means the algebra structure on the
quotient is uniquely determined by requiring the quotient map to be a morphism.

Rather than defining the structure map on the quotient directly (which would
require lifting through products of quotients), we characterize the quotient
algebra by its universal property:

1. The quotient map π : FreeAlg → Q is an algebra homomorphism
2. Any equivalence-respecting homomorphism h : FreeAlg → M factors through Q
3. The factorization is unique

For models specifically, we've shown (freeAlgCounitRespectsEquiv) that the
counit FreeAlg(Φ(M)) → M respects equivalence, so it factors through the
quotient. This gives the adjunction counit Q(Φ(M)) → M.
-/

section QuotientAlgebra

variable {X : Type u}

/--
The quotient of a free algebra by FreeAlgEquiv, viewed as a model.

The model structure comes from the quotient map being an algebra homomorphism:
the fold from PolyFix factors through the quotient, and by construction the
quotient collapses equation-equivalent elements.
-/
structure FreeAlgQuotModel (T : IndexedEAT X) (A : Over X) where
  /-- The quotient carrier as an Over X object. -/
  carrier : Over X := freeAlgQuotOver T A
  /-- The quotient map collapses equation-equivalent initial algebra elements. -/
  quotientRespectsEq : ∀ x (t₁ t₂ : PolyFix T.poly x),
      T.equations x t₁ t₂ →
      FreeAlgQuot.mk T A (polyFixToFreeAlg T.poly A x t₁) =
      FreeAlgQuot.mk T A (polyFixToFreeAlg T.poly A x t₂) :=
    freeAlgQuot_isModel T A

/--
Given a morphism from A to the carrier of a model M, we get an algebra
homomorphism from Free(A) to M by the adjunction.

This is the adjunction transpose: compose the free algebra map induced by f
with the counit fold.
-/
def freeToModelHom (T : IndexedEAT X) (A : Over X) (M : EATModel T)
    (f : A ⟶ M.alg.a) : polyFreeAlg A T.poly ⟶ M.alg :=
  polyFreeAlgMap A M.alg.a T.poly f ≫ polyFreeCounitHom T.poly M.alg

/--
Bind on a closed tree (one embedded from PolyFix) just transforms
the tree without accessing any leaves.
-/
lemma polyFreeMBind_closed (P : PolyEndo X) (A B : Over X)
    (g : ∀ y, { a : A.left // A.hom a = y } → PolyFreeM B P y)
    (x : X) (t : PolyFix P x) :
    polyFreeMBind A B P (polyFixToFreeAlg P A x t) g =
    polyFixToFreeAlg P B x t := by
  induction t with
  | mk y p children ih =>
    simp only [polyFixToFreeAlg, polyFreeMBind]
    congr 1
    funext e
    exact ih e

/--
The free algebra map preserves the embedding of PolyFix into PolyFreeM.

Given f : A ⟶ B, the induced map on free algebras sends embedded PolyFix
elements to embedded PolyFix elements (since they don't use A at all).
-/
lemma polyFreeAlgMap_preserves_closed (P : PolyEndo X) (A B : Over X) (f : A ⟶ B)
    (x : X) (t : PolyFix P x) :
    (polyFreeAlgMap A B P f).f.left ⟨x, polyFixToFreeAlg P A x t⟩ =
    ⟨x, polyFixToFreeAlg P B x t⟩ := by
  simp only [polyFreeAlgMap, polyFreeMap]
  simp only [Over.homMk_left, polyFreeMapLeft]
  simp only [polyFreeMapAt]
  simp only [polyFreeMBind_closed]

/--
The homomorphism from Free(A) to M respects FreeAlgEquiv.

This requires that M is a model (fold respects EAT equations) and uses
the fact that the extension factors through the counit.
-/
lemma freeToModelHom_respectsEquiv (T : IndexedEAT X) (A : Over X) (M : EATModel T)
    (f : A ⟶ M.alg.a) :
    AlgHomRespectsEquiv T A M.alg (freeToModelHom T A M f) := by
  intro x t₁ t₂ hequiv
  induction hequiv with
  | refl => rfl
  | @symm x s₁ s₂ _ ih => exact ih.symm
  | @trans x s₁ s₂ s₃ _ _ ih1 ih2 => exact ih1.trans ih2
  | fromEq x s₁ s₂ heq =>
    simp only [freeToModelHom]
    have hcomp : (polyFreeAlgMap A M.alg.a T.poly f ≫
        polyFreeCounitHom T.poly M.alg).f.left =
        (polyFreeAlgMap A M.alg.a T.poly f).f.left ≫
        (polyFreeCounitHom T.poly M.alg).f.left := rfl
    simp only [hcomp, types_comp_apply]
    rw [polyFreeAlgMap_preserves_closed T.poly A M.alg.a f x s₁]
    rw [polyFreeAlgMap_preserves_closed T.poly A M.alg.a f x s₂]
    simp only [polyFreeCounitHom, polyFreeCounitFold, Over.homMk_left,
      polyFreeCounitFoldLeft]
    have h1 := polyFreeCounitFoldAt_closed T M.alg x s₁
    have h2 := polyFreeCounitFoldAt_closed T M.alg x s₂
    simp only [h1, h2]
    have heq' : polyFixFoldLeft T.poly M.alg ⟨x, s₁⟩ =
                polyFixFoldLeft T.poly M.alg ⟨x, s₂⟩ := M.isModel x s₁ s₂ heq
    simp only [polyFixFoldLeft] at heq'
    exact heq'
  | cong x p children₁ children₂ _ ih =>
    simp only [freeToModelHom]
    have hcomp : (polyFreeAlgMap A M.alg.a T.poly f ≫
        polyFreeCounitHom T.poly M.alg).f.left =
        (polyFreeAlgMap A M.alg.a T.poly f).f.left ≫
        (polyFreeCounitHom T.poly M.alg).f.left := rfl
    simp only [hcomp, types_comp_apply]
    simp only [polyFreeAlgMap, polyFreeMap, Over.homMk_left, polyFreeMapLeft,
      polyFreeMapAt]
    simp only [polyFreeCounitHom, polyFreeCounitFold, Over.homMk_left,
      polyFreeCounitFoldLeft]
    simp only [polyFreeMBind]
    simp only [polyFreeCounitFoldAt]
    apply congrArg
    congr 1
    apply Sigma.ext
    · rfl
    · simp only [heq_eq_eq]
      apply Over.OverMorphism.ext
      funext e
      specialize ih e
      simp only [freeToModelHom, polyFreeAlgMap, polyFreeMap,
        polyFreeCounitHom, polyFreeCounitFold] at ih
      exact ih

/--
The quotient total map: given a morphism f : A → Φ(M), we get a map from
the quotient to M by factoring the algebra homomorphism through the quotient.
-/
def freeAlgQuotUniv (T : IndexedEAT X) (A : Over X) (M : EATModel T)
    (f : A ⟶ M.alg.a) :
    FreeAlgQuotTotal T A → M.alg.a.left :=
  fun ⟨x, q⟩ => (quotientLift T A M.alg (freeToModelHom T A M f)
    (freeToModelHom_respectsEquiv T A M f) x q).val

/--
The quotient universal map is fiber-preserving.
-/
lemma freeAlgQuotUniv_fiberPreserving (T : IndexedEAT X) (A : Over X)
    (M : EATModel T) (f : A ⟶ M.alg.a) (xtq : FreeAlgQuotTotal T A) :
    M.alg.a.hom (freeAlgQuotUniv T A M f xtq) = xtq.1 := by
  obtain ⟨x, q⟩ := xtq
  simp only [freeAlgQuotUniv]
  exact (quotientLift T A M.alg (freeToModelHom T A M f)
    (freeToModelHom_respectsEquiv T A M f) x q).property

/--
The quotient universal map as an Over X morphism.
-/
def freeAlgQuotUnivMor (T : IndexedEAT X) (A : Over X) (M : EATModel T)
    (f : A ⟶ M.alg.a) : freeAlgQuotOver T A ⟶ M.alg.a :=
  Over.homMk (freeAlgQuotUniv T A M f)
    (funext (freeAlgQuotUniv_fiberPreserving T A M f))

/--
The free algebra map preserves FreeAlgEquiv: equivalent elements in Free(A)
map to equivalent elements in Free(B).
-/
lemma polyFreeMapAt_preservesEquiv (T : IndexedEAT X) (A B : Over X) (g : A ⟶ B)
    (x : X) (t₁ t₂ : PolyFreeM A T.poly x)
    (hequiv : FreeAlgEquiv T A x t₁ t₂) :
    FreeAlgEquiv T B x (polyFreeMapAt A B T.poly g x t₁)
      (polyFreeMapAt A B T.poly g x t₂) := by
  induction hequiv with
  | refl y s => exact FreeAlgEquiv.refl y _
  | @symm y s₁ s₂ _ ih => exact FreeAlgEquiv.symm y _ _ ih
  | @trans y s₁ s₂ s₃ _ _ ih1 ih2 => exact FreeAlgEquiv.trans y _ _ _ ih1 ih2
  | fromEq y s₁ s₂ heq =>
    simp only [polyFreeMapAt]
    rw [polyFreeMBind_closed, polyFreeMBind_closed]
    exact FreeAlgEquiv.fromEq y s₁ s₂ heq
  | cong y p children₁ children₂ _ ih =>
    simp only [polyFreeMapAt, polyFreeMBind]
    exact FreeAlgEquiv.cong y p _ _ ih

def freeAlgQuotMapAt (T : IndexedEAT X) (A B : Over X) (g : A ⟶ B) (x : X)
    (q : FreeAlgQuot T A x) : FreeAlgQuot T B x :=
  Quot.lift
    (fun t => FreeAlgQuot.mk T B (polyFreeMapAt A B T.poly g x t))
    (fun t₁ t₂ hequiv => Quot.sound (polyFreeMapAt_preservesEquiv T A B g x t₁ t₂ hequiv))
    q

/--
The quotient map from Free(A) to Quot(A) as a carrier morphism.
-/
def freeAlgQuotMapTotal (T : IndexedEAT X) (A B : Over X) (g : A ⟶ B) :
    FreeAlgQuotTotal T A → FreeAlgQuotTotal T B :=
  fun ⟨x, q⟩ => ⟨x, freeAlgQuotMapAt T A B g x q⟩

/--
The quotient map is fiber-preserving.
-/
lemma freeAlgQuotMapTotal_fiberPreserving (T : IndexedEAT X) (A B : Over X)
    (g : A ⟶ B) (xtq : FreeAlgQuotTotal T A) :
    (freeAlgQuotOver T B).hom (freeAlgQuotMapTotal T A B g xtq) =
    (freeAlgQuotOver T A).hom xtq := rfl

/--
The quotient map as an Over X morphism.
-/
def freeAlgQuotMor (T : IndexedEAT X) (A B : Over X) (g : A ⟶ B) :
    freeAlgQuotOver T A ⟶ freeAlgQuotOver T B :=
  Over.homMk (freeAlgQuotMapTotal T A B g)
    (funext (freeAlgQuotMapTotal_fiberPreserving T A B g))

end QuotientAlgebra

/-! ## EAT Quotient Structure

For an EAT to have quotient algebras, we need to be able to define
an algebra structure on the quotient carrier. This requires lifting
the structure map through products of quotients.

We define a typeclass `EATHasQuotient` that captures when this is possible.
The trivial EAT always has quotients (the quotient is the free algebra).
-/

section EATQuotientStructure

variable {X : Type u}

/--
An EAT has quotient structure if we can define the quotient algebra.
This requires:
1. An algebra structure on the quotient carrier
2. The algebra structure making it a model
3. The quotient map being an algebra homomorphism
-/
class EATHasQuotient (T : IndexedEAT X) where
  /-- The quotient algebra for each Over X object. -/
  quotientAlg : (A : Over X) → PolyAlg T.poly
  /-- The quotient algebra carrier is the quotient carrier. -/
  quotientAlg_carrier : ∀ A, (quotientAlg A).a = freeAlgQuotOver T A
  /-- The quotient algebra is a model. -/
  quotientIsModel : ∀ A, IsEATModel T (quotientAlg A)
  /-- The quotient map is an algebra homomorphism. -/
  quotientHomomorphism : ∀ A,
    polyFreeAlg A T.poly ⟶ quotientAlg A
  /-- The quotient algebra is functorial in A. -/
  quotientAlgMap : ∀ (A B : Over X), (A ⟶ B) → (quotientAlg A ⟶ quotientAlg B)
  /-- Functoriality preserves identity. -/
  quotientAlgMap_id : ∀ A, quotientAlgMap A A (𝟙 A) = 𝟙 (quotientAlg A)
  /-- Functoriality preserves composition. -/
  quotientAlgMap_comp : ∀ (A B C : Over X) (f : A ⟶ B) (g : B ⟶ C),
    quotientAlgMap A C (f ≫ g) = quotientAlgMap A B f ≫ quotientAlgMap B C g
  /-- The quotient map is natural. -/
  quotientNaturality : ∀ (A B : Over X) (f : A ⟶ B),
    polyFreeAlgMap A B T.poly f ≫ quotientHomomorphism B =
    quotientHomomorphism A ≫ quotientAlgMap A B f
  /-- The quotient map identifies equivalent elements. -/
  quotientRespectsEquiv : ∀ A,
    AlgHomRespectsEquiv T A (quotientAlg A) (quotientHomomorphism A)
  /-- Universal property: equivalence-respecting homs factor through quotient. -/
  quotientFactor : (A : Over X) → (M : PolyAlg T.poly) →
    (hM : IsEATModel T M) →
    (h : polyFreeAlg A T.poly ⟶ M) →
    (hresp : AlgHomRespectsEquiv T A M h) →
    (quotientAlg A ⟶ M)
  /-- The factorization commutes with the quotient map. -/
  quotientFactor_commutes : ∀ (A : Over X) (M : PolyAlg T.poly)
    (hM : IsEATModel T M)
    (h : polyFreeAlg A T.poly ⟶ M)
    (hresp : AlgHomRespectsEquiv T A M h),
    quotientHomomorphism A ≫ quotientFactor A M hM h hresp = h
  /-- Uniqueness: any homomorphism from quotient with the same composite is equal. -/
  quotientFactor_unique : ∀ (A : Over X) (M : PolyAlg T.poly)
    (hM : IsEATModel T M)
    (h : polyFreeAlg A T.poly ⟶ M)
    (hresp : AlgHomRespectsEquiv T A M h)
    (g : quotientAlg A ⟶ M),
    quotientHomomorphism A ≫ g = h →
    g = quotientFactor A M hM h hresp

/--
Bundle the quotient algebra as an EATModel.
-/
def quotientModel (T : IndexedEAT X) [EATHasQuotient T] (A : Over X) :
    EATModel T where
  alg := EATHasQuotient.quotientAlg A
  isModel := EATHasQuotient.quotientIsModel A

/--
Morphism between quotient models induced by a morphism of the underlying
Over X objects.
-/
def quotientModelHom (T : IndexedEAT X) [EATHasQuotient T] (A B : Over X)
    (f : A ⟶ B) : quotientModel T A ⟶ quotientModel T B :=
  EATHasQuotient.quotientAlgMap A B f

/--
The quotient functor from Over X to EATModel, constructed from EATHasQuotient.
-/
def EATHasQuotient.toFunctor (T : IndexedEAT X) [EATHasQuotient T] :
    Over X ⥤ EATModel T where
  obj := quotientModel T
  map := quotientModelHom T _ _
  map_id := fun A => EATHasQuotient.quotientAlgMap_id A
  map_comp := fun f g => EATHasQuotient.quotientAlgMap_comp _ _ _ f g

/--
The quotient map from the free algebra to the quotient model.
-/
def quotientHom (T : IndexedEAT X) [EATHasQuotient T] (A : Over X) :
    polyFreeAlg A T.poly ⟶ (quotientModel T A).alg :=
  EATHasQuotient.quotientHomomorphism A

/--
The quotient map as a natural transformation from the free functor to
quotient ⋙ inclusion.
-/
def EATHasQuotient.toNatTrans (T : IndexedEAT X) [EATHasQuotient T] :
    polyFreeFunctor T.poly ⟶
    EATHasQuotient.toFunctor T ⋙ EATModel.inclusionFunctor T where
  app := fun A => quotientHom T A
  naturality := fun A B f => EATHasQuotient.quotientNaturality A B f

end EATQuotientStructure

/-! ## Quotient Model Interface

For an EAT to produce models via quotienting, it needs to provide:
1. A quotient functor Q : Over X → EATModel T
2. A quotient map from Free to Q (natural transformation)

The trivial EAT provides this trivially (the quotient is the free algebra itself).
General EATs must provide their own quotient construction, typically using
the FreeAlgEquiv relation defined above.
-/

section QuotientInterface

variable {X : Type u}

/--
The data needed to quotient free algebras into models.
-/
structure EATQuotientData (T : IndexedEAT X) where
  /-- The quotient functor from Over X to EATModel. -/
  quotientFunctor : Over X ⥤ EATModel T
  /-- The quotient map from Free to Quotient (as a natural transformation). -/
  quotientNat : polyFreeFunctor T.poly ⟶
    quotientFunctor ⋙ EATModel.inclusionFunctor T

/--
The left adjoint L for an EAT with quotient data.
-/
def EATQuotientData.leftAdjoint {T : IndexedEAT X} (Q : EATQuotientData T) :
    Over X ⥤ EATModel T :=
  Q.quotientFunctor

/--
The right adjoint Φ is always the embedding functor.
-/
def eatRightAdjoint (T : IndexedEAT X) : EATModel T ⥤ Over X :=
  EATModel.embeddingFunctor T

/--
Construct EATQuotientData from EATHasQuotient.
-/
def EATQuotientData.fromHasQuotient (T : IndexedEAT X) [EATHasQuotient T] :
    EATQuotientData T where
  quotientFunctor := EATHasQuotient.toFunctor T
  quotientNat := EATHasQuotient.toNatTrans T

/--
Quotient data for the trivial EAT: the quotient is just the free algebra.
-/
def trivialEAT.quotientData (P : PolyEndo X) : EATQuotientData (trivialEAT P) where
  quotientFunctor := polyFreeFunctor P ⋙ trivialEAT.reflectorFunctor P
  quotientNat := {
    app := fun A => 𝟙 (polyFreeAlg A P)
    naturality := fun A B f => by
      simp only [Functor.comp_obj, Functor.comp_map,
        EATModel.inclusionFunctor, trivialEAT.reflectorFunctor,
        trivialEAT]
      exact (Category.comp_id _).trans (Category.id_comp _).symm
  }

end QuotientInterface

/-! ## The L ⊣ Φ Adjunction

For an EAT with quotient structure, we construct the adjunction:
- L : Over X ⥤ EATModel T (the quotient functor)
- Φ : EATModel T ⥤ Over X (the embedding functor)

The unit is the composition of the free algebra unit with the quotient map.
The counit uses the universal property of quotients.
-/

section EATAdjunction

variable {X : Type u}

/--
The unit of the L ⊣ Φ adjunction at A : Over X.
Maps A into the carrier of the quotient model L(A).
-/
def eatAdjunctionUnitAt (T : IndexedEAT X) [EATHasQuotient T] (A : Over X) :
    A ⟶ (EATHasQuotient.toFunctor T ⋙ EATModel.embeddingFunctor T).obj A :=
  polyFreeUnit A T.poly ≫ (EATHasQuotient.quotientHomomorphism A).f

/--
The unit of the L ⊣ Φ adjunction as a natural transformation.
-/
def eatAdjunctionUnit (T : IndexedEAT X) [EATHasQuotient T] :
    𝟭 (Over X) ⟶
    EATHasQuotient.toFunctor T ⋙ EATModel.embeddingFunctor T where
  app := eatAdjunctionUnitAt T
  naturality := fun A B f => by
    simp only [Functor.id_obj, Functor.comp_obj, Functor.id_map,
      Functor.comp_map, eatAdjunctionUnitAt]
    simp only [EATModel.embeddingFunctor, EATHasQuotient.toFunctor,
      quotientModelHom, quotientModel, Functor.comp_map]
    simp only [polyForgetFunctor, EATModel.inclusionFunctor,
      CategoryTheory.Endofunctor.Algebra.forget_map]
    have hQuotNat := EATHasQuotient.quotientNaturality (T := T) A B f
    have hUnitNat := polyFreeUnit_naturality A B T.poly f
    calc f ≫ polyFreeUnit B T.poly ≫ (EATHasQuotient.quotientHomomorphism B).f
        = (f ≫ polyFreeUnit B T.poly) ≫
            (EATHasQuotient.quotientHomomorphism B).f
            := (Category.assoc _ _ _).symm
      _ = (polyFreeUnit A T.poly ≫ (polyFreeAlgMap A B T.poly f).f) ≫
            (EATHasQuotient.quotientHomomorphism B).f
            := by rw [hUnitNat]; rfl
      _ = polyFreeUnit A T.poly ≫ (polyFreeAlgMap A B T.poly f).f ≫
            (EATHasQuotient.quotientHomomorphism B).f
            := Category.assoc _ _ _
      _ = polyFreeUnit A T.poly ≫
            (polyFreeAlgMap A B T.poly f ≫
             EATHasQuotient.quotientHomomorphism B).f
            := rfl
      _ = polyFreeUnit A T.poly ≫
            (EATHasQuotient.quotientHomomorphism A ≫
             EATHasQuotient.quotientAlgMap A B f).f
            := by rw [hQuotNat]
      _ = polyFreeUnit A T.poly ≫ (EATHasQuotient.quotientHomomorphism A).f ≫
            (EATHasQuotient.quotientAlgMap A B f).f
            := rfl

/--
The fold from Free(M.alg.a) to M.alg respects FreeAlgEquiv because M is a model.
-/
lemma freeCounitRespectsEquivOnModel (T : IndexedEAT X) (M : EATModel T) :
    AlgHomRespectsEquiv T M.alg.a M.alg
      (polyFreeCounitHom T.poly M.alg) :=
  freeAlgCounitRespectsEquiv T M

/--
The counit of the L ⊣ Φ adjunction at M : EATModel T.
Maps L(Φ(M)) = quotientModel T M.alg.a to M.
Uses the universal property of the quotient.
-/
def eatAdjunctionCounitAt (T : IndexedEAT X) [EATHasQuotient T]
    (M : EATModel T) :
    (EATModel.embeddingFunctor T ⋙ EATHasQuotient.toFunctor T).obj M ⟶ M :=
  EATHasQuotient.quotientFactor M.alg.a M.alg M.isModel
    (polyFreeCounitHom T.poly M.alg)
    (freeCounitRespectsEquivOnModel T M)

/--
The counit of the L ⊣ Φ adjunction as a natural transformation.
-/
def eatAdjunctionCounit (T : IndexedEAT X) [EATHasQuotient T] :
    EATModel.embeddingFunctor T ⋙ EATHasQuotient.toFunctor T ⟶
    𝟭 (EATModel T) where
  app := eatAdjunctionCounitAt T
  naturality := fun M N f => by
    simp only [Functor.comp_obj, Functor.id_obj, Functor.comp_map,
      Functor.id_map, eatAdjunctionCounitAt]
    simp only [EATModel.embeddingFunctor, EATHasQuotient.toFunctor,
      quotientModelHom, quotientModel, EATModel.inclusionFunctor,
      IndexedEAT.forgetFunctor]
    have hResp : AlgHomRespectsEquiv T M.alg.a N.alg (polyFreeCounitHom T.poly M.alg ≫ f) := by
      intro x t1 t2 heq
      have h1 := freeCounitRespectsEquivOnModel T M x t1 t2 heq
      simp only [Endofunctor.Algebra.comp_f, polyFreeCounitHom, polyFreeCounitFold] at h1 ⊢
      simp only [types_comp_apply, Over.comp_left]
      exact congrArg (f.f.left ·) h1
    have hLHS : EATHasQuotient.quotientHomomorphism M.alg.a ≫
        (EATHasQuotient.quotientAlgMap M.alg.a N.alg.a f.f ≫
         EATHasQuotient.quotientFactor N.alg.a N.alg N.isModel
           (polyFreeCounitHom T.poly N.alg) (freeCounitRespectsEquivOnModel T N)) =
        polyFreeCounitHom T.poly M.alg ≫ f := by
      rw [← Category.assoc, ← EATHasQuotient.quotientNaturality, Category.assoc,
          EATHasQuotient.quotientFactor_commutes,
          polyFreeCounitHom_natural T.poly M.alg N.alg f]
    have hRHS : EATHasQuotient.quotientHomomorphism M.alg.a ≫
        (EATHasQuotient.quotientFactor M.alg.a M.alg M.isModel
           (polyFreeCounitHom T.poly M.alg) (freeCounitRespectsEquivOnModel T M) ≫ f) =
        polyFreeCounitHom T.poly M.alg ≫ f := by
      rw [← Category.assoc, EATHasQuotient.quotientFactor_commutes]
    have hEqLHS := EATHasQuotient.quotientFactor_unique M.alg.a N.alg N.isModel
        (polyFreeCounitHom T.poly M.alg ≫ f) hResp
        (EATHasQuotient.quotientAlgMap M.alg.a N.alg.a f.f ≫
         EATHasQuotient.quotientFactor N.alg.a N.alg N.isModel
           (polyFreeCounitHom T.poly N.alg) (freeCounitRespectsEquivOnModel T N)) hLHS
    have hEqRHS := EATHasQuotient.quotientFactor_unique M.alg.a N.alg N.isModel
        (polyFreeCounitHom T.poly M.alg ≫ f) hResp
        (EATHasQuotient.quotientFactor M.alg.a M.alg M.isModel
           (polyFreeCounitHom T.poly M.alg) (freeCounitRespectsEquivOnModel T M) ≫ f) hRHS
    simp only [Functor.comp_obj, Functor.comp_map, Endofunctor.Algebra.forget]
    exact hEqLHS.trans hEqRHS.symm

/--
The L ⊣ Φ adjunction for EATs with quotient structure.
L : Over X → EATModel T (the quotient functor)
Φ : EATModel T → Over X (the embedding functor)
-/
def eatAdjunction (T : IndexedEAT X) [EATHasQuotient T] :
    EATHasQuotient.toFunctor T ⊣ EATModel.embeddingFunctor T :=
  Adjunction.mkOfUnitCounit {
    unit := eatAdjunctionUnit T
    counit := eatAdjunctionCounit T
    left_triangle := by
      ext A
      simp only [NatTrans.comp_app, Functor.comp_obj, Functor.id_obj,
        NatTrans.id_app']
      simp only [eatAdjunctionUnit, eatAdjunctionCounit]
      simp only [EATModel.embeddingFunctor, EATHasQuotient.toFunctor,
        quotientModel]
      simp only [Functor.whiskerRight_app, Functor.associator_hom_app,
        Functor.whiskerLeft_app, Functor.comp_obj,
        Functor.id_obj]
      simp only [eatAdjunctionCounitAt, eatAdjunctionUnitAt]
      simp only [EATModel.inclusionFunctor, Endofunctor.Algebra.forget]
      simp only [quotientModel, quotientModelHom]
      rw [Category.id_comp]
      have hLHS : EATHasQuotient.quotientHomomorphism A ≫
          (EATHasQuotient.quotientAlgMap A (EATHasQuotient.quotientAlg A).a
            (polyFreeUnit A T.poly ≫ (EATHasQuotient.quotientHomomorphism A).f) ≫
           EATHasQuotient.quotientFactor (EATHasQuotient.quotientAlg A).a
             (EATHasQuotient.quotientAlg A)
             (EATHasQuotient.quotientIsModel A)
             (polyFreeCounitHom T.poly (EATHasQuotient.quotientAlg A))
             (freeCounitRespectsEquivOnModel T (quotientModel T A))) =
          EATHasQuotient.quotientHomomorphism A := by
        rw [← Category.assoc]
        rw [← EATHasQuotient.quotientNaturality]
        rw [Category.assoc]
        rw [EATHasQuotient.quotientFactor_commutes]
        apply Endofunctor.Algebra.Hom.ext
        apply Over.OverMorphism.ext
        funext ⟨x, t⟩
        simp only [Endofunctor.Algebra.comp_f, polyFreeCounitHom,
          polyFreeCounitFold, polyFreeAlgMap, polyFreeMap, Over.comp_left,
          Over.homMk_left, types_comp_apply, polyFreeMapLeft,
          polyFreeCounitFoldLeft]
        induction t with
        | mk y data children ih =>
          cases data with
          | inl a =>
            simp only [polyFreeMapAt, polyFreeMBind, polyFreeCounitFoldAt,
              polyFreeMPure, Over.comp_left, types_comp_apply,
              polyFreeUnit, polyFreeUnitLeft, Over.homMk_left]
            have hfib : A.hom a.val = y := a.property
            have hEq : (⟨A.hom a.val, PolyFix.mk (A.hom a.val) (Sum.inl ⟨a.val, rfl⟩)
                (fun e => PEmpty.elim e)⟩ : (polyFreeMCarrier A T.poly).left) =
                ⟨y, PolyFix.mk y (Sum.inl a) children⟩ := by
              cases a with | mk aval aprop =>
              simp only at hfib ⊢
              cases hfib
              congr 1
              congr 1
              funext e
              exact PEmpty.elim e
            exact congrArg (EATHasQuotient.quotientHomomorphism A).f.left hEq
          | inr p =>
            simp only [polyFreeMapAt, polyFreeMBind, polyFreeCounitFoldAt]
            have hAlgHomProp := (EATHasQuotient.quotientHomomorphism (T := T) A).h
            let originalNode : ((polyBetweenEvalFunctor X X T.poly).obj
                (polyFreeMCarrier A T.poly)).left :=
              ⟨y, ⟨p, Over.homMk (fun e => ⟨(polyBetweenFamily X X T.poly y p).hom e,
                children e⟩) (by funext e; rfl)⟩⟩
            have hNodeEval : (EATHasQuotient.quotientHomomorphism A).f.left
                ⟨y, PolyFix.mk y (Sum.inr p) children⟩ =
                (EATHasQuotient.quotientHomomorphism A).f.left
                (polyFreeMStrLeft A T.poly originalNode) := rfl
            rw [hNodeEval]
            have hAlgAtNode : (EATHasQuotient.quotientAlg A).str.left
                (((polyEndoFunctor X T.poly).map
                  (EATHasQuotient.quotientHomomorphism (T := T) A).f).left originalNode) =
                (EATHasQuotient.quotientHomomorphism (T := T) A).f.left
                  (polyFreeMStrLeft A T.poly originalNode) := by
              have hLeft := congrArg (·.left) hAlgHomProp
              simp only [Over.comp_left] at hLeft
              exact congrFun hLeft originalNode
            rw [← hAlgAtNode]
            apply congrArg (EATHasQuotient.quotientAlg A).str.left
            have hMapDef : ((polyEndoFunctor X T.poly).map
                (EATHasQuotient.quotientHomomorphism (T := T) A).f).left originalNode =
                (Sigma.mk y (Sigma.mk p (Over.homMk
                  (fun e => (EATHasQuotient.quotientHomomorphism (T := T) A).f.left
                    ⟨(polyBetweenFamily X X T.poly y p).hom e, children e⟩)
                  (by funext e
                      exact congrFun
                        (Over.w (EATHasQuotient.quotientHomomorphism (T := T) A).f) _)))) := rfl
            rw [hMapDef]
            congr 1
            congr 1
            apply Over.OverMorphism.ext
            funext e
            exact ih e
      have hRHS : EATHasQuotient.quotientHomomorphism (T := T) A ≫ 𝟙 _ =
          EATHasQuotient.quotientHomomorphism (T := T) A := Category.comp_id _
      have hEqLHS := EATHasQuotient.quotientFactor_unique A
        (EATHasQuotient.quotientAlg A)
        (EATHasQuotient.quotientIsModel A)
        (EATHasQuotient.quotientHomomorphism A)
        (EATHasQuotient.quotientRespectsEquiv A)
        (EATHasQuotient.quotientAlgMap A (EATHasQuotient.quotientAlg A).a
          (polyFreeUnit A T.poly ≫ (EATHasQuotient.quotientHomomorphism A).f) ≫
         EATHasQuotient.quotientFactor (EATHasQuotient.quotientAlg A).a
           (EATHasQuotient.quotientAlg A)
           (EATHasQuotient.quotientIsModel A)
           (polyFreeCounitHom T.poly (EATHasQuotient.quotientAlg A))
           (freeCounitRespectsEquivOnModel T (quotientModel T A)))
        hLHS
      have hEqRHS := EATHasQuotient.quotientFactor_unique A
        (EATHasQuotient.quotientAlg A)
        (EATHasQuotient.quotientIsModel A)
        (EATHasQuotient.quotientHomomorphism A)
        (EATHasQuotient.quotientRespectsEquiv A)
        (𝟙 _)
        hRHS
      exact hEqLHS.trans hEqRHS.symm
    right_triangle := by
      ext M
      simp only [NatTrans.comp_app, Functor.id_obj, Functor.comp_obj,
        NatTrans.id_app']
      simp only [eatAdjunctionUnit, eatAdjunctionCounit]
      simp only [EATModel.embeddingFunctor, EATHasQuotient.toFunctor,
        quotientModel]
      simp only [Functor.whiskerRight_app, Functor.associator_inv_app,
        Functor.whiskerLeft_app]
      simp only [eatAdjunctionCounitAt, eatAdjunctionUnitAt]
      simp only [EATModel.inclusionFunctor, Endofunctor.Algebra.forget]
      have hFactor : EATHasQuotient.quotientHomomorphism M.alg.a ≫
          EATHasQuotient.quotientFactor M.alg.a M.alg M.isModel
            (polyFreeCounitHom T.poly M.alg) (freeCounitRespectsEquivOnModel T M) =
          polyFreeCounitHom T.poly M.alg :=
        EATHasQuotient.quotientFactor_commutes M.alg.a M.alg M.isModel
          (polyFreeCounitHom T.poly M.alg) (freeCounitRespectsEquivOnModel T M)
      have hTriangle : polyFreeUnit M.alg.a T.poly ≫
          (polyFreeCounitHom T.poly M.alg).f = 𝟙 M.alg.a := by
        apply Over.OverMorphism.ext
        funext a
        simp only [Over.comp_left, types_comp_apply]
        simp only [polyFreeUnit, Over.homMk_left, polyFreeUnitLeft]
        simp only [polyFreeCounitHom, polyFreeCounitFold, Over.homMk_left,
          polyFreeCounitFoldLeft]
        have hPure := polyFreeCounitFoldAt_pure T.poly M.alg (M.alg.a.hom a) ⟨a, rfl⟩
        exact congrArg Subtype.val hPure
      have hComp : polyFreeUnit M.alg.a T.poly ≫
          (EATHasQuotient.quotientHomomorphism M.alg.a).f ≫
          (EATHasQuotient.quotientFactor M.alg.a M.alg M.isModel
            (polyFreeCounitHom T.poly M.alg) (freeCounitRespectsEquivOnModel T M)).f =
          𝟙 M.alg.a := by
        calc polyFreeUnit M.alg.a T.poly ≫
             (EATHasQuotient.quotientHomomorphism M.alg.a).f ≫
             (EATHasQuotient.quotientFactor M.alg.a M.alg M.isModel
               (polyFreeCounitHom T.poly M.alg) (freeCounitRespectsEquivOnModel T M)).f
           = polyFreeUnit M.alg.a T.poly ≫
             ((EATHasQuotient.quotientHomomorphism M.alg.a) ≫
              EATHasQuotient.quotientFactor M.alg.a M.alg M.isModel
                (polyFreeCounitHom T.poly M.alg) (freeCounitRespectsEquivOnModel T M)).f := by
               simp only [Endofunctor.Algebra.comp_f]
           _ = polyFreeUnit M.alg.a T.poly ≫
             (polyFreeCounitHom T.poly M.alg).f := by
               rw [hFactor]
           _ = 𝟙 M.alg.a := hTriangle
      have hLeftComp := congrArg CommaMorphism.left hComp
      simp only [Over.comp_left, Over.id_left] at hLeftComp
      exact congrFun hLeftComp _
  }

end EATAdjunction

end GebLean
