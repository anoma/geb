import GebLean.Polynomial
import GebLean.Utilities.Category

/-!
# Adjunctions Involving Polynomial Functors

This module defines adjunctions between categories of polynomial functors
and related categories (such as `Type` and slice categories).

## Adjunctions

The following adjunctions are implemented:

* Free/forgetful adjunction between polynomial functors and `Type`
* Cofree/forgetful adjunction (dual construction)
* Slice-based adjunctions relating `PolyFunctorBetweenCat X Y` to slices

These adjunctions capture the sense in which polynomial functors arise as
free constructions and have forgetful functors with both left and right
adjoints.

## References

* https://ncatlab.org/nlab/show/polynomial+functor
-/

namespace GebLean

open CategoryTheory

universe u v w

/-! ## Position Functor

The position functor extracts the "position" (index type) from a polynomial
functor. For a polynomial `P = (I, F)` where `I : Type` and `F : I → C`,
the position is `I`.

This is the forgetful functor from `CoprodCovarRepCat C` to `Type`, which
arises from the Grothendieck construction structure.
-/

section PositionFunctor

variable (C : Type u) [Category.{v} C]

/--
The position functor from `CoprodCovarRepCat C` to `Type`.

For a polynomial `P = (I, F)` where `I : Type` and `F : I → C`, this functor
returns `I`. For a morphism, it returns the reindexing function.

This is an alias for `GrothendieckContra'.forget` specialized to
`familyFunctor C ⋙ Cat.opFunctor'`.
-/
def ccrPosFunctor : CoprodCovarRepCat.{u, v, w} C ⥤ Type w :=
  GrothendieckContra'.forget (familyFunctor.{u, v, w} C ⋙ Cat.opFunctor')

@[simp]
lemma ccrPosFunctor_obj (P : CoprodCovarRepCat.{u, v, w} C) :
    (ccrPosFunctor C).obj P = ccrIndex P :=
  rfl

@[simp]
lemma ccrPosFunctor_map {P Q : CoprodCovarRepCat.{u, v, w} C} (f : P ⟶ Q) :
    (ccrPosFunctor C).map f = ccrReindex f :=
  rfl

end PositionFunctor

/-! ## Monomial Functor

For a fixed object `c : C`, the monomial functor sends a type `A` to the
polynomial functor with positions `A` and constant fiber `c` at every position.
This represents the polynomial `A · y^c` in the notation of polynomial functors.
-/

section MonomialFunctor

variable {C : Type u} [Category.{v} C]

/--
The object map of the monomial functor: sends `A : Type` to the polynomial
`(A, fun _ => c)`.
-/
def ccrMonomialObj (c : C) (A : Type w) : CoprodCovarRepCat.{u, v, w} C :=
  ccrObjMk (fun _ : A => c)

/--
The morphism map of the monomial functor: for `f : A → B`, constructs a
morphism from `(A, const c)` to `(B, const c)` using `f` as the reindexing
and identity morphisms on the fibers.
-/
def ccrMonomialMap (c : C) {A B : Type w} (f : A → B) :
    ccrMonomialObj c A ⟶ ccrMonomialObj c B :=
  ccrHomMk f (fun _ => 𝟙 c)

@[simp]
lemma ccrMonomialMap_reindex (c : C) {A B : Type w} (f : A → B) :
    ccrReindex (ccrMonomialMap c f) = f :=
  rfl

@[simp]
lemma ccrMonomialMap_fiberMor (c : C) {A B : Type w} (f : A → B) (i : A) :
    ccrFiberMor (ccrMonomialMap c f) i = 𝟙 c :=
  rfl

lemma ccrMonomialMap_id (c : C) (A : Type w) :
    ccrMonomialMap c (id : A → A) = 𝟙 (ccrMonomialObj c A) := by
  unfold ccrMonomialMap ccrMonomialObj ccrHomMk ccrObjMk
  congr 1

lemma ccrMonomialMap_comp (c : C) {A B D : Type w} (f : A → B) (g : B → D) :
    ccrMonomialMap c (g ∘ f) = ccrMonomialMap c f ≫ ccrMonomialMap c g := by
  simp only [ccrMonomialMap, ccrComp_mk]
  congr 1
  funext _
  exact (Category.id_comp (𝟙 c)).symm

/--
The monomial functor from `Type` to `CoprodCovarRepCat C` at a fixed object
`c : C`. Sends `A` to the polynomial `(A, fun _ => c)` representing `A · y^c`.
-/
def ccrMonomialFunctor (c : C) : Type w ⥤ CoprodCovarRepCat.{u, v, w} C where
  obj := ccrMonomialObj c
  map := ccrMonomialMap c
  map_id A := ccrMonomialMap_id c A
  map_comp f g := ccrMonomialMap_comp c f g

@[simp]
lemma ccrMonomialFunctor_obj (c : C) (A : Type w) :
    (ccrMonomialFunctor c).obj A = ccrMonomialObj c A :=
  rfl

@[simp]
lemma ccrMonomialFunctor_map (c : C) {A B : Type w} (f : A → B) :
    (ccrMonomialFunctor c).map f = ccrMonomialMap c f :=
  rfl

end MonomialFunctor

/-! ## Evaluation Functor

The evaluation functor sends a polynomial `P : CoprodCovarRepCat D` to its
evaluation functor `ccrToFunctor P : D ⥤ Type`. This exhibits `ccrToFunctor`
as itself being functorial in `P`.

For a morphism `f : P ⟶ Q`, the induced natural transformation maps
`⟨i, h⟩ : ccrEval P A` to `⟨ccrReindex f i, ccrFiberMor f i ≫ h⟩ : ccrEval Q A`.
-/

section EvaluationFunctor

variable {D : Type u} [Category.{v} D]

/--
The component of the natural transformation induced by `f : P ⟶ Q` at object
`A : D`. Maps `⟨i, h⟩ : ccrEval P A` to `⟨ccrReindex f i, ccrFiberMor f i ≫ h⟩`.
-/
def ccrToFunctorMapApp {P Q : CoprodCovarRepCat.{u, v, w} D} (f : P ⟶ Q)
    (A : D) : ccrEval P A → ccrEval Q A :=
  fun x => ccrEvalMk (ccrReindex f (ccrEvalIndex x))
    (ccrFiberMor f (ccrEvalIndex x) ≫ ccrEvalMor x)

@[simp]
lemma ccrToFunctorMapApp_index {P Q : CoprodCovarRepCat.{u, v, w} D}
    (f : P ⟶ Q) (A : D) (x : ccrEval P A) :
    ccrEvalIndex (ccrToFunctorMapApp f A x) = ccrReindex f (ccrEvalIndex x) :=
  rfl

@[simp]
lemma ccrToFunctorMapApp_mor {P Q : CoprodCovarRepCat.{u, v, w} D}
    (f : P ⟶ Q) (A : D) (x : ccrEval P A) :
    ccrEvalMor (ccrToFunctorMapApp f A x) =
      ccrFiberMor f (ccrEvalIndex x) ≫ ccrEvalMor x :=
  rfl

/--
Naturality of `ccrToFunctorMapApp` in `A`: for morphisms `g : A ⟶ B` in `D`,
the square commutes.
-/
lemma ccrToFunctorMapApp_natural {P Q : CoprodCovarRepCat.{u, v, w} D}
    (f : P ⟶ Q) {A B : D} (g : A ⟶ B) :
    (ccrToFunctor P).map g ≫ ccrToFunctorMapApp f B =
      ccrToFunctorMapApp f A ≫ (ccrToFunctor Q).map g := by
  funext ⟨i, h⟩
  simp only [types_comp_apply, ccrToFunctor, ccrToFunctorMapApp, ccrEvalMap,
    ccrEvalIndex, ccrEvalMor, ccrEvalMk, Category.assoc]

/--
The natural transformation from `ccrToFunctor P` to `ccrToFunctor Q` induced
by a morphism `f : P ⟶ Q`.
-/
def ccrToFunctorMap {P Q : CoprodCovarRepCat.{u, v, w} D} (f : P ⟶ Q) :
    ccrToFunctor P ⟶ ccrToFunctor Q where
  app := ccrToFunctorMapApp f
  naturality := fun _ _ g => ccrToFunctorMapApp_natural f g

@[simp]
lemma ccrToFunctorMap_app {P Q : CoprodCovarRepCat.{u, v, w} D}
    (f : P ⟶ Q) (A : D) :
    (ccrToFunctorMap f).app A = ccrToFunctorMapApp f A :=
  rfl

/--
The identity morphism on `P` induces the identity natural transformation
on `ccrToFunctor P`.
-/
lemma ccrToFunctorMap_id (P : CoprodCovarRepCat.{u, v, w} D) :
    ccrToFunctorMap (𝟙 P) = 𝟙 (ccrToFunctor P) := by
  ext A ⟨i, h⟩
  simp only [ccrToFunctorMap_app, ccrToFunctorMapApp, NatTrans.id_app,
    ccrEvalIndex, ccrEvalMor, ccrEvalMk, types_id_apply,
    ccrId_reindex, ccrId_fiberMor, Category.id_comp]

/--
Composition of morphisms induces composition of natural transformations.
-/
lemma ccrToFunctorMap_comp {P Q R : CoprodCovarRepCat.{u, v, w} D}
    (f : P ⟶ Q) (g : Q ⟶ R) :
    ccrToFunctorMap (f ≫ g) = ccrToFunctorMap f ≫ ccrToFunctorMap g := by
  ext A ⟨i, h⟩
  simp only [ccrToFunctorMap_app, ccrToFunctorMapApp, NatTrans.comp_app,
    ccrEvalIndex, ccrEvalMor, ccrEvalMk, types_comp_apply,
    ccrComp_reindex, ccrComp_fiberMor, Category.assoc]

/--
The evaluation functor from `CoprodCovarRepCat D` to the functor category
`D ⥤ Type`.

This functor sends a polynomial `P` to its evaluation functor `ccrToFunctor P`,
and a morphism `f : P ⟶ Q` to the natural transformation `ccrToFunctorMap f`.
-/
def ccrEvalFunctor : CoprodCovarRepCat.{u, v, w} D ⥤ (D ⥤ Type (max w v)) where
  obj := ccrToFunctor
  map := ccrToFunctorMap
  map_id := ccrToFunctorMap_id
  map_comp := fun f g => ccrToFunctorMap_comp f g

lemma ccrEvalFunctor_obj (P : CoprodCovarRepCat.{u, v, w} D) :
    ccrEvalFunctor.obj P = ccrToFunctor P :=
  rfl

lemma ccrEvalFunctor_map {P Q : CoprodCovarRepCat.{u, v, w} D} (f : P ⟶ Q) :
    ccrEvalFunctor.map f = ccrToFunctorMap f :=
  rfl

/-! ### Faithfulness

The evaluation functor is faithful: distinct morphisms in `CoprodCovarRepCat D`
induce distinct natural transformations.
-/

/--
If two morphisms `f g : P ⟶ Q` in `CoprodCovarRepCat` induce the same natural
transformation, then they have equal base components.
-/
lemma ccrToFunctorMap_injective_base {P Q : CoprodCovarRepCat.{u, v, w} D}
    {f g : P ⟶ Q} (h : ccrToFunctorMap f = ccrToFunctorMap g) : f.base = g.base := by
  funext i
  have h_at : ccrToFunctorMapApp f (ccrFamily P i) (ccrEvalMk i (𝟙 _)) =
      ccrToFunctorMapApp g (ccrFamily P i) (ccrEvalMk i (𝟙 _)) :=
    congr_fun (congr_fun (congr_arg NatTrans.app h) (ccrFamily P i))
      (ccrEvalMk i (𝟙 (ccrFamily P i)))
  exact congrArg Sigma.fst h_at

/--
If two morphisms `f g : P ⟶ Q` in `CoprodCovarRepCat` induce the same natural
transformation and have equal base components, then their fiber components
are equal after composing with `eqToHom`.
-/
lemma ccrToFunctorMap_injective_fiber {P Q : CoprodCovarRepCat.{u, v, w} D}
    {f g : P ⟶ Q} (h : ccrToFunctorMap f = ccrToFunctorMap g)
    (hbase : f.base = g.base) :
    f.fiber ≫ eqToHom (by rw [hbase]) = g.fiber := by
  funext k
  have h_at : ccrToFunctorMapApp f (ccrFamily P k) (ccrEvalMk k (𝟙 _)) =
      ccrToFunctorMapApp g (ccrFamily P k) (ccrEvalMk k (𝟙 _)) :=
    congr_fun (congr_fun (congr_arg NatTrans.app h) (ccrFamily P k))
      (ccrEvalMk k (𝟙 (ccrFamily P k)))
  simp only [ccrToFunctorMapApp, ccrEvalMk, ccrEvalIndex, ccrEvalMor,
    Category.comp_id] at h_at
  have h_snd := (Sigma.mk.inj h_at).2
  simp only [ccrFiberMor] at h_snd
  rw [piOp'_fiber_comp_eqToHom_at_idx]
  exact (heq_iff_eqToHom_comp (f.fiber k) (g.fiber k) _).mp h_snd

/--
A morphism `f : P ⟶ Q` can be recovered from the natural transformation
`ccrToFunctorMap f` by evaluating at the "universal elements" `⟨i, 𝟙⟩`.
-/
lemma ccrToFunctorMap_injective {P Q : CoprodCovarRepCat.{u, v, w} D}
    {f g : P ⟶ Q} (h : ccrToFunctorMap f = ccrToFunctorMap g) : f = g :=
  GrothendieckContra'.ext _ _ (ccrToFunctorMap_injective_base h)
    (ccrToFunctorMap_injective_fiber h (ccrToFunctorMap_injective_base h))

instance : Functor.Faithful (ccrEvalFunctor (D := D)) where
  map_injective := ccrToFunctorMap_injective

end EvaluationFunctor

end GebLean
