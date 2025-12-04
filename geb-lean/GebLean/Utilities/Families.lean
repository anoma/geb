import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Pi.Basic
import Mathlib.CategoryTheory.Grothendieck
import Mathlib.CategoryTheory.Whiskering
import Mathlib.CategoryTheory.Limits.Shapes.Products
import GebLean.Utilities.Opposites
import GebLean.Utilities.Grothendieck

/-!
# The family functor and completions

Given a category `C`, the family functor `familyFunctor C : Typeᵒᵖ' ⥤ Cat` sends
a type `X` to the product category `∀ x : X, C`, which is the category of
`X`-indexed families of objects from `C`.

By applying the Grothendieck construction (covariant or contravariant) to
`familyFunctor` or `familyFunctor ⋙ opFunctor'` (which post-composes with
oppositization), we obtain four different completions of a category:

1. **Free coproduct completion** (`FreeCoprodCompletionCat`): The contravariant
   Grothendieck construction on `familyFunctor`. Objects are pairs `(X, F)`
   where `X` is a type and `F : X → C`. Morphisms `(X, F) → (Y, G)` consist of
   `f : X → Y` and `F(x) → G(f(x))`. This freely adjoins coproducts to `C`.
   This category may also be viewed as the category of coproducts of
   contravariant representables (sometimes called "Dirichlet functors").

2. **Free product completion** (`FreeProdCompletionCat`): The covariant
   Grothendieck construction on `familyFunctor`. Morphisms go in the opposite
   direction for the fiber component. This freely adjoins products to `C`.

3. **Coproducts of covariant representables** (`CoprodCovarRepCat`): The
   contravariant Grothendieck construction on `familyFunctor ⋙ opFunctor'`.
   Objects are `X`-indexed families of objects from `Cᵒᵖ'`. This produces
   the category coproducts of covariant representables, which are a form
   of polynomial functors (for some categories, including `Type`, these
   comprise _all_ polynomial functors).

4. **Products of contravariant representables** (`ProdContravarRepCat`): The
   covariant Grothendieck construction on `familyFunctor ⋙ opFunctor'`.

## References

* https://ncatlab.org/nlab/show/free+coproduct+completion#AsAGrothendieckConstruction
* https://ncatlab.org/nlab/show/family

-/

namespace GebLean

open CategoryTheory

/-! ## The family category -/

section FamilyCat

/--
For an index type `X`, the product category of `C` indexed by `X`. Objects are
functions `X → C`, and morphisms are families of morphisms indexed by `X`.
-/
@[simp]
def FamilyCat.{u, v, w} (C : Type u) [CInst : Category.{v, u} C] (X : Type w) :
  Cat.{max v w, max u w} :=
    Cat.of.{max w v, max u w} (∀ _ : X, C)

end FamilyCat

universe u v v₂

/-! ## Functoriality in the indexing type -/

section FunctorialityInIndex

variable (C : Type u) [Category.{v} C]

/--
For a function `f : X → Y`, the induced functor between family categories
sends a `Y`-indexed family to an `X`-indexed family by precomposition.
-/
@[simp]
def familyMap.{u', v', w'} {C' : Type u'} [Category.{v'} C'] {X Y : Type w'}
    (f : X ⟶ Y) : FamilyCat C' Y ⥤ FamilyCat C' X where
  obj F x := F (f x)
  map φ x := φ (f x)

@[simp]
theorem familyMap_id.{u', v', w'} {C' : Type u'} [Category.{v'} C'] (X : Type w') :
    familyMap (C' := C') (𝟙 X) = 𝟙 (FamilyCat C' X) := rfl

@[simp]
theorem familyMap_comp.{u', v', w'} {C' : Type u'} [Category.{v'} C']
    {X Y Z : Type w'} (f : X ⟶ Y) (g : Y ⟶ Z) :
    familyMap (C' := C') (f ≫ g) = familyMap (C' := C') g ⋙ familyMap (C' := C') f :=
  rfl

/--
The family functor `familyFunctor C : Typeᵒᵖ' ⥤ Cat` sends a type `X` to the
product category of `C` indexed by `X`. This is the functor whose Grothendieck
construction yields the free coproduct completion of `C`.

For a function `f : X → Y` (viewed as a morphism `X → Y` in `Typeᵒᵖ'`), the
induced functor is given by precomposition: a `Y`-indexed family is sent to
an `X`-indexed family by `(G : Y → C) ↦ (G ∘ f : X → C)`.
-/
@[simp]
def familyFunctor.{u', v', w'} (C' : Type u') [Category.{v'} C'] :
    Type w'ᵒᵖ' ⥤ Cat.{max w' v', max u' w'} where
  obj X := FamilyCat C' X
  map f := familyMap (C' := C') f
  map_id X := familyMap_id X
  map_comp _ _ := rfl

end FunctorialityInIndex

/-! ## Functoriality in the category -/

section FunctorialityInCategory

variable {C : Type u} [Category.{v} C]
variable {D : Type u} [Category.{v₂} D]

/--
A functor `F : C ⥤ D` induces a functor `FamilyCat C X ⥤ FamilyCat D X` by
postcomposition: an `X`-indexed family of objects in `C` is sent to an
`X`-indexed family of objects in `D`.
-/
@[simp]
def familyPostcomp (F : C ⥤ D) (X : Type u) : (∀ _ : X, C) ⥤ (∀ _ : X, D) where
  obj G x := F.obj (G x)
  map φ x := F.map (φ x)
  map_id G := by funext x; simp
  map_comp φ ψ := by funext x; simp

/--
`familyPostcomp` respects the identity functor.
-/
@[simp]
theorem familyPostcomp_id (X : Type u) :
    familyPostcomp (𝟭 C) X = 𝟭 (∀ _ : X, C) := rfl

/--
`familyPostcomp` respects functor composition.
-/
@[simp]
theorem familyPostcomp_comp {E : Type u} [Category E] (F : C ⥤ D) (G : D ⥤ E)
    (X : Type u) : familyPostcomp (F ⋙ G) X = familyPostcomp F X ⋙ familyPostcomp G X := rfl

/--
`familyPostcomp` is natural in the indexing type: for any function `f : X → Y`,
the following square commutes:
```
  FamilyCat C Y --familyPostcomp F Y--> FamilyCat D Y
       |                                     |
  familyMap f                           familyMap f
       |                                     |
       v                                     v
  FamilyCat C X --familyPostcomp F X--> FamilyCat D X
```
-/
@[simp]
theorem familyPostcomp_natural (F : C ⥤ D) {X Y : Type u} (f : X ⟶ Y) :
    familyMap (C' := C) f ⋙ familyPostcomp F X =
    familyPostcomp F Y ⋙ familyMap (C' := D) f := rfl

end FunctorialityInCategory

/-! ## The family bifunctor -/

section FamilyBifunctor

/--
A functor `F : C ⥤ D` induces a natural transformation from `familyFunctor C`
to `familyFunctor D`, with components given by `familyPostcomp F X`.
-/
@[simp]
def familyNatTrans {C D : Type u} [Category.{v} C] [Category.{v} D] (F : C ⥤ D) :
    familyFunctor C ⟶ familyFunctor D where
  app X := familyPostcomp F X
  naturality _ _ f := (familyPostcomp_natural F f).symm

@[simp]
theorem familyNatTrans_id (C : Type u) [Category.{v} C] :
    familyNatTrans (𝟭 C) = 𝟙 (familyFunctor C) := rfl

@[simp]
theorem familyNatTrans_comp {C D E : Type u} [Category.{v} C] [Category.{v} D]
    [Category.{v} E] (F : C ⥤ D) (G : D ⥤ E) :
    familyNatTrans (F ⋙ G) = familyNatTrans F ≫ familyNatTrans G := rfl

/--
The family bifunctor `familyBifunctor : Cat ⥤ (Type uᵒᵖ' ⥤ Cat)` sends a
category `C` to the family functor `familyFunctor C`, and a functor `F : C ⥤ D`
to the natural transformation `familyNatTrans F`.
-/
@[simp]
def familyBifunctor : Cat.{v, u} ⥤ (Type uᵒᵖ' ⥤ Cat.{max u v, u}) where
  obj C := familyFunctor C
  map F := familyNatTrans F
  map_id C := familyNatTrans_id C
  map_comp F G := familyNatTrans_comp F G

end FamilyBifunctor

/-! ## The opposite family bifunctor -/

section FamilyBifunctorOp

/--
The opposite family bifunctor `familyBifunctorOp : Cat ⥤ (Type uᵒᵖ' ⥤ Cat)` is
`familyBifunctor` post-composed with the oppositization functor `opFunctor'`.
It sends a category `C` to the functor that maps a type `X` to the opposite
of the family category `(∀ _ : X, C)ᵒᵖ'`.
-/
@[simp]
def familyBifunctorOp : Cat.{v, u} ⥤ (Type uᵒᵖ' ⥤ Cat.{max u v, u}) :=
  familyBifunctor ⋙ (Functor.whiskeringRight _ _ _).obj Cat.opFunctor'

end FamilyBifunctorOp

/-! ## Grothendieck completions -/

section GrothendieckCompletions

universe w

variable (C : Type u) [Category.{v} C]

/--
The free coproduct completion of a category `C` with index types in universe
`w`. Objects are pairs `(X, F)` where `X : Type w` and `F : X → C` is an
`X`-indexed family of objects from `C`. Morphisms `(X, F) → (Y, G)` consist of
a function `f : X → Y` and a family of morphisms `F(x) → G(f(x))`.

This is the contravariant Grothendieck construction applied to `familyFunctor`.
-/
@[simp]
def FreeCoprodCompletionCat.{u', v', w'} (C' : Type u') [Category.{v'} C'] :
    Cat.{max w' v', max (w' + 1) u' w'} :=
  Cat.of (GrothendieckContra'.{w' + 1, w', max u' w', max w' v'}
    (familyFunctor.{u', v', w'} C'))

/--
The free product completion of a category `C`. Objects are pairs `(X, F)`
where `X : Type (u+1)` and `F : X → C`. Morphisms `(X, F) → (Y, G)` consist
of a function `f : X → Y` and a family of morphisms `G(f(x)) → F(x)`.

This is the covariant Grothendieck construction applied to `familyFunctor`.
-/
@[simp]
def FreeProdCompletionCat.{u', v', w'} (C' : Type u') [Category.{v'} C'] :
    Cat.{max w' v', max (w' + 1) u' w'} :=
  Cat.of (Grothendieck.{w' + 1, w', max u' w', max w' v'}
    (familyFunctor.{u', v', w'} C'))

/--
The category of coproducts of covariant representables for `C`. Objects are
pairs `(X, F)` where `X : Type (u+1)` and `F : X → Cᵒᵖ'` is an `X`-indexed
family of objects from the opposite category.

This is the contravariant Grothendieck construction applied to `familyFunctor`
post-composed with oppositization.
-/
@[simp]
def CoprodCovarRepCat.{u', v', w'} (C' : Type u') [Category.{v'} C'] :
    Cat.{max w' v', max (w' + 1) u' w'} :=
  Cat.of (GrothendieckContra'.{w' + 1, w', max u' w', max w' v'}
    (familyFunctor.{u', v', w'} C' ⋙ Cat.opFunctor'))

/--
The category of products of contravariant representables for `C`. This is the
covariant Grothendieck construction applied to `familyFunctor` post-composed
with oppositization.
-/
@[simp]
def ProdContravarRepCat.{u', v', w'} (C' : Type u') [Category.{v'} C'] :
    Cat.{max w' v', max (w' + 1) u' w'} :=
  Cat.of (Grothendieck.{w' + 1, w', max u' w', max w' v'}
    (familyFunctor.{u', v', w'} C' ⋙ Cat.opFunctor'))

end GrothendieckCompletions

/-! ## Free coproduct completion helpers -/

section FreeCoprodCompletionHelpers

universe w

variable {C : Type u} [Category.{v} C]

/--
Construct an object of `FreeCoprodCompletionCat C` from an index type and
a family of objects.
-/
def fcObjMk {X : Type w} (F : X → C) : FreeCoprodCompletionCat.{u, v, w} C :=
  ⟨X, F⟩

/--
Extract the index type from an object of `FreeCoprodCompletionCat C`.
-/
def fcIndex (x : FreeCoprodCompletionCat.{u, v, w} C) : Type w := x.base

/--
Extract the family of objects from an object of `FreeCoprodCompletionCat C`.
-/
def fcFamily (x : FreeCoprodCompletionCat.{u, v, w} C) : fcIndex x → C := x.fiber

@[simp]
lemma fcObjMk_index {X : Type w} (F : X → C) :
    fcIndex (fcObjMk F) = X := rfl

@[simp]
lemma fcObjMk_family {X : Type w} (F : X → C) :
    fcFamily (fcObjMk F) = F := rfl

/--
Construct a morphism in `FreeCoprodCompletionCat C` from a reindexing function
and a family of fiber morphisms.

A morphism `(X, F) → (Y, G)` consists of:
- `reindex : X ⟶ Y` (morphism in `Type`, i.e., a function)
- `fiberMor : ∀ x, F(x) ⟶ G(reindex(x))` (family of morphisms in `C`)
-/
def fcHomMk {x y : FreeCoprodCompletionCat.{u, v, w} C}
    (reindex : fcIndex x ⟶ fcIndex y)
    (fiberMor : ∀ i : fcIndex x, fcFamily x i ⟶ fcFamily y (reindex i)) :
    x ⟶ y :=
  ⟨reindex, fiberMor⟩

/--
Extract the reindexing function from a morphism in `FreeCoprodCompletionCat C`.
-/
def fcReindex {x y : FreeCoprodCompletionCat.{u, v, w} C} (f : x ⟶ y) :
    fcIndex x ⟶ fcIndex y :=
  f.base

/--
Extract the fiber morphism at index `i` from a morphism in
`FreeCoprodCompletionCat C`.
-/
def fcFiberMor {x y : FreeCoprodCompletionCat.{u, v, w} C} (f : x ⟶ y)
    (i : fcIndex x) : fcFamily x i ⟶ fcFamily y (fcReindex f i) :=
  f.fiber i

@[simp]
lemma fcHomMk_reindex {x y : FreeCoprodCompletionCat.{u, v, w} C}
    (reindex : fcIndex x ⟶ fcIndex y)
    (fiberMor : ∀ i : fcIndex x, fcFamily x i ⟶ fcFamily y (reindex i)) :
    fcReindex (fcHomMk reindex fiberMor) = reindex := rfl

@[simp]
lemma fcHomMk_fiberMor {x y : FreeCoprodCompletionCat.{u, v, w} C}
    (reindex : fcIndex x ⟶ fcIndex y)
    (fiberMor : ∀ i : fcIndex x, fcFamily x i ⟶ fcFamily y (reindex i))
    (i : fcIndex x) :
    fcFiberMor (fcHomMk reindex fiberMor) i = fiberMor i := rfl

@[ext (iff := false)]
lemma fcHom_ext {x y : FreeCoprodCompletionCat.{u, v, w} C} (f g : x ⟶ y)
    (hbase : f.base = g.base)
    (hfiber : f.fiber ≫ eqToHom (by rw [hbase]) = g.fiber) : f = g :=
  GrothendieckContra'.ext f g hbase hfiber

/--
The identity morphism in `FreeCoprodCompletionCat C` has identity reindexing.
-/
@[simp]
lemma fcId_reindex (x : FreeCoprodCompletionCat.{u, v, w} C) :
    fcReindex (𝟙 x) = 𝟙 (fcIndex x) := rfl

/--
The identity morphism in `FreeCoprodCompletionCat C` has identity fiber morphisms.
-/
@[simp]
lemma fcId_fiberMor (x : FreeCoprodCompletionCat.{u, v, w} C) (i : fcIndex x) :
    fcFiberMor (𝟙 x) i = 𝟙 (fcFamily x i) := rfl

/--
Composition in `FreeCoprodCompletionCat C`: the reindexing composes covariantly.
-/
@[simp]
lemma fcComp_reindex {x y z : FreeCoprodCompletionCat.{u, v, w} C}
    (f : x ⟶ y) (g : y ⟶ z) :
    fcReindex (f ≫ g) = fcReindex f ≫ fcReindex g := rfl

/--
Composition in `FreeCoprodCompletionCat C`: the fiber morphisms compose covariantly.
For `f : x ⟶ y` and `g : y ⟶ z`, the fiber morphism at index `i` is
`f.fiberMor i ≫ g.fiberMor (f.reindex i)`.
-/
@[simp]
lemma fcComp_fiberMor {x y z : FreeCoprodCompletionCat.{u, v, w} C}
    (f : x ⟶ y) (g : y ⟶ z) (i : fcIndex x) :
    fcFiberMor (f ≫ g) i = fcFiberMor f i ≫ fcFiberMor g (fcReindex f i) := by
  unfold fcFiberMor fcReindex
  change (GrothendieckContra'.comp f g).fiber i = f.fiber i ≫ g.fiber (f.base i)
  unfold GrothendieckContra'.comp
  simp only [eqToHom_refl, Category.comp_id]
  rfl

end FreeCoprodCompletionHelpers

/-! ## Coproducts in FreeCoprodCompletionCat

The free coproduct completion has all small coproducts. Given a family
`F : I → FreeCoprodCompletionCat C`, the coproduct is:
- Index type: `Σ i, fcIndex (F i)`
- Family: `fun ⟨i, x⟩ => fcFamily (F i) x`
-/

section FreeCoprodCompletionCoproducts

open Limits

universe w

variable {C : Type u} [Category.{v} C]

/--
The coproduct object in `FreeCoprodCompletionCat C` for a family indexed by `I`.
Both `I` and the index types of the family elements must be at universe `w`.
-/
def fcCoprodObj {I : Type w} (F : I → FreeCoprodCompletionCat.{u, v, w} C) :
    FreeCoprodCompletionCat.{u, v, w} C :=
  fcObjMk (fun (p : Σ i, fcIndex (F i)) => fcFamily (F p.1) p.2)

/--
The injection morphism into the coproduct from component `i`.
-/
def fcCoprodι {I : Type w} (F : I → FreeCoprodCompletionCat.{u, v, w} C) (i : I) :
    F i ⟶ fcCoprodObj F :=
  fcHomMk (fun x => ⟨i, x⟩) (fun _ => 𝟙 _)

/--
The universal morphism from the coproduct given morphisms from each component.
-/
def fcCoprodDesc {I : Type w} {F : I → FreeCoprodCompletionCat.{u, v, w} C}
    {P : FreeCoprodCompletionCat.{u, v, w} C}
    (f : ∀ i, F i ⟶ P) : fcCoprodObj F ⟶ P :=
  fcHomMk
    (fun ⟨i, x⟩ => fcReindex (f i) x)
    (fun ⟨i, x⟩ => fcFiberMor (f i) x)

@[simp]
lemma fcCoprodι_desc {I : Type w} {F : I → FreeCoprodCompletionCat.{u, v, w} C}
    {P : FreeCoprodCompletionCat.{u, v, w} C}
    (f : ∀ i, F i ⟶ P) (i : I) :
    fcCoprodι F i ≫ fcCoprodDesc f = f i := by
  refine GrothendieckContra'.ext _ _ ?_ ?_
  · -- w_base: show base components are equal
    rfl
  · -- w_fiber: show fiber components equal with eqToHom
    simp only [eqToHom_refl, Category.comp_id]
    funext x
    change (GrothendieckContra'.comp (fcCoprodι F i) (fcCoprodDesc f)).fiber x = (f i).fiber x
    unfold GrothendieckContra'.comp
    simp only [fcCoprodι, fcCoprodDesc, fcHomMk, eqToHom_refl, Category.comp_id]
    dsimp only [familyFunctor, familyMap, fcFiberMor]
    change (𝟙 (fcFamily (F i) x) ≫ (f i).fiber x) = (f i).fiber x
    simp only [Category.id_comp]

/-- From composition fcCoprodι F i ≫ g, the fiber at x simplifies to g.fiber ⟨i, x⟩. -/
private lemma fcCoprodι_comp_fiber_eq {I : Type w}
    {F : I → FreeCoprodCompletionCat.{u, v, w} C}
    {P : FreeCoprodCompletionCat.{u, v, w} C}
    (g : fcCoprodObj F ⟶ P) (i : I) (x : fcIndex (F i)) :
    (fcCoprodι F i ≫ g).fiber x = g.fiber ⟨i, x⟩ := by
  -- Expand composition fiber definition
  change (GrothendieckContra'.comp (fcCoprodι F i) g).fiber x = _
  unfold GrothendieckContra'.comp
  simp only [fcCoprodι, fcHomMk, eqToHom_refl, Category.comp_id]
  dsimp only [familyFunctor, familyMap]
  -- The goal should now be: 𝟙 _ ≫ g.fiber ⟨i, x⟩ = g.fiber ⟨i, x⟩
  change (𝟙 (fcFamily (F i) x) ≫ g.fiber ⟨i, x⟩) = g.fiber ⟨i, x⟩
  simp only [Category.id_comp]

lemma fcCoprodDesc_unique {I : Type w} {F : I → FreeCoprodCompletionCat.{u, v, w} C}
    {P : FreeCoprodCompletionCat.{u, v, w} C}
    (f : ∀ i, F i ⟶ P) (g : fcCoprodObj F ⟶ P)
    (hg : ∀ i, fcCoprodι F i ≫ g = f i) : g = fcCoprodDesc f := by
  -- First establish base equality: g.base = (fcCoprodDesc f).base
  have hbase : g.base = (fcCoprodDesc f).base := by
    funext ⟨i, x⟩
    -- From hg i: fcCoprodι F i ≫ g = f i, extract base equality at x
    have hi := congrArg GrothendieckContra'.Hom.base (hg i)
    -- hi: (fcCoprodι F i ≫ g).base = (f i).base
    unfold GrothendieckContra'.comp at hi
    simp only [fcCoprodι, fcHomMk, fcCoprodDesc, fcReindex] at hi ⊢
    -- hi: (fun x => ⟨i, x⟩) ≫ g.base = (f i).base
    -- Goal: g.base ⟨i, x⟩ = (f i).base x
    have hix := congrFun hi x
    -- hix: ((fun x => ⟨i, x⟩) ≫ g.base) x = (f i).base x
    -- i.e., g.base ⟨i, x⟩ = (f i).base x
    exact hix
  refine GrothendieckContra'.ext _ _ hbase ?_
  funext ⟨i, x⟩
  have hfibx := congrFun (GrothendieckContra'.congr (hg i)) x
  rw [fcCoprodι_comp_fiber_eq g i x] at hfibx
  change g.fiber ⟨i, x⟩ ≫ _ = _
  rw [hfibx]
  change ((f i).fiber x ≫ _) ≫ _ = (f i).fiber x
  simp only [Category.assoc]
  simp_all

open CategoryTheory.Limits in
/-- The cofan for coproducts in the free coproduct completion. -/
def fcCofan {I : Type w} (F : I → FreeCoprodCompletionCat.{u, v, w} C) :
    Cofan F :=
  Cofan.mk (fcCoprodObj F) (fcCoprodι F)

open CategoryTheory.Limits in
/-- The coproduct cofan is a colimit in the free coproduct completion. -/
def fcIsColimitCofan {I : Type w} (F : I → FreeCoprodCompletionCat.{u, v, w} C) :
    IsColimit (fcCofan F) :=
  mkCofanColimit (fcCofan F)
    (fun t => fcCoprodDesc t.inj)
    (fun t i => fcCoprodι_desc t.inj i)
    (fun t m hm => fcCoprodDesc_unique t.inj m hm)

open CategoryTheory.Limits in
instance : HasCoproducts.{w} (FreeCoprodCompletionCat.{u, v, w} C) :=
  hasCoproducts_of_colimit_cofans fcCofan fcIsColimitCofan

end FreeCoprodCompletionCoproducts

/-! ## Free product completion helpers -/

section FreeProdCompletionHelpers

universe w

variable {C : Type u} [Category.{v} C]

/--
Construct an object of `FreeProdCompletionCat C` from an index type and
a family of objects.
-/
def fpObjMk {X : Type w} (F : X → C) : FreeProdCompletionCat.{u, v, w} C :=
  ⟨X, F⟩

/--
Extract the index type from an object of `FreeProdCompletionCat C`.
-/
def fpIndex (x : FreeProdCompletionCat.{u, v, w} C) : Type w := x.base

/--
Extract the family of objects from an object of `FreeProdCompletionCat C`.
-/
def fpFamily (x : FreeProdCompletionCat.{u, v, w} C) : fpIndex x → C := x.fiber

@[simp]
lemma fpObjMk_index {X : Type w} (F : X → C) :
    fpIndex (fpObjMk F) = X := rfl

@[simp]
lemma fpObjMk_family {X : Type w} (F : X → C) :
    fpFamily (fpObjMk F) = F := rfl

/--
Construct a morphism in `FreeProdCompletionCat C` from a reindexing function
and a family of fiber morphisms.

A morphism `(X, F) → (Y, G)` consists of:
- `reindex : Y ⟶ X` (morphism in `Type`, note: opposite direction)
- `fiberMor : ∀ j, F(reindex(j)) ⟶ G(j)` (family of morphisms in `C`)
-/
def fpHomMk {x y : FreeProdCompletionCat.{u, v, w} C}
    (reindex : fpIndex y ⟶ fpIndex x)
    (fiberMor : ∀ j : fpIndex y, fpFamily x (reindex j) ⟶ fpFamily y j) :
    x ⟶ y :=
  ⟨reindex, fiberMor⟩

/--
Extract the reindexing function from a morphism in `FreeProdCompletionCat C`.
Note: For a morphism `(X, F) → (Y, G)`, this is a morphism `Y ⟶ X` in `Type`.
-/
def fpReindex {x y : FreeProdCompletionCat.{u, v, w} C} (f : x ⟶ y) :
    fpIndex y ⟶ fpIndex x :=
  f.base

/--
Extract the fiber morphism at index `j` from a morphism in
`FreeProdCompletionCat C`. For a morphism `f : (X, F) → (Y, G)`, this is
`F(reindex j) ⟶ G(j)`.
-/
def fpFiberMor {x y : FreeProdCompletionCat.{u, v, w} C} (f : x ⟶ y)
    (j : fpIndex y) : fpFamily x (fpReindex f j) ⟶ fpFamily y j :=
  f.fiber j

@[simp]
lemma fpHomMk_reindex {x y : FreeProdCompletionCat.{u, v, w} C}
    (reindex : fpIndex y ⟶ fpIndex x)
    (fiberMor : ∀ j : fpIndex y, fpFamily x (reindex j) ⟶ fpFamily y j) :
    fpReindex (fpHomMk reindex fiberMor) = reindex := rfl

@[simp]
lemma fpHomMk_fiberMor {x y : FreeProdCompletionCat.{u, v, w} C}
    (reindex : fpIndex y ⟶ fpIndex x)
    (fiberMor : ∀ j : fpIndex y, fpFamily x (reindex j) ⟶ fpFamily y j)
    (j : fpIndex y) :
    fpFiberMor (fpHomMk reindex fiberMor) j = fiberMor j := rfl

@[ext (iff := false)]
lemma fpHom_ext {x y : FreeProdCompletionCat.{u, v, w} C} (f g : x ⟶ y)
    (hbase : f.base = g.base)
    (hfiber : eqToHom (by rw [hbase]) ≫ f.fiber = g.fiber) : f = g :=
  Grothendieck.ext f g hbase hfiber

/--
The identity morphism in `FreeProdCompletionCat C` has identity reindexing.
-/
@[simp]
lemma fpId_reindex (x : FreeProdCompletionCat.{u, v, w} C) :
    fpReindex (𝟙 x) = 𝟙 (fpIndex x) := rfl

/--
The identity morphism in `FreeProdCompletionCat C` has identity fiber morphisms.
-/
@[simp]
lemma fpId_fiberMor (x : FreeProdCompletionCat.{u, v, w} C) (j : fpIndex x) :
    fpFiberMor (𝟙 x) j = 𝟙 (fpFamily x j) := rfl

/--
Composition in `FreeProdCompletionCat C`: the reindexing composes
contravariantly (in the opposite order from the morphisms).
-/
@[simp]
lemma fpComp_reindex {x y z : FreeProdCompletionCat.{u, v, w} C}
    (f : x ⟶ y) (g : y ⟶ z) :
    fpReindex (f ≫ g) = fpReindex g ≫ fpReindex f := rfl

/--
Composition in `FreeProdCompletionCat C`: the fiber morphisms compose
covariantly. For `f : x ⟶ y` and `g : y ⟶ z`, the fiber morphism at index
`k : fpIndex z` is `fpFiberMor f (fpReindex g k) ≫ fpFiberMor g k`.
-/
@[simp]
lemma fpComp_fiberMor {x y z : FreeProdCompletionCat.{u, v, w} C}
    (f : x ⟶ y) (g : y ⟶ z) (k : fpIndex z) :
    fpFiberMor (f ≫ g) k = fpFiberMor f (fpReindex g k) ≫ fpFiberMor g k := by
  unfold fpFiberMor fpReindex
  change (Grothendieck.comp f g).fiber k = f.fiber (g.base k) ≫ g.fiber k
  unfold Grothendieck.comp
  simp only [eqToHom_refl, Category.id_comp]
  rfl

end FreeProdCompletionHelpers

/-! ## Coproduct of covariant representables helpers -/

section CoprodCovarRepHelpers

universe w

variable {C : Type u} [Category.{v} C]

/--
Construct an object of `CoprodCovarRepCat C` from an index type and
a family of objects from `C`. Internally, objects are stored as families
in `Cᵒᵖ'`, but this helper hides that detail.
-/
def ccrObjMk {X : Type w} (F : X → C) : CoprodCovarRepCat.{u, v, w} C :=
  ⟨X, F⟩

/--
Extract the index type from an object of `CoprodCovarRepCat C`.
-/
def ccrIndex (x : CoprodCovarRepCat.{u, v, w} C) : Type w := x.base

/--
Extract the family of objects from an object of `CoprodCovarRepCat C`.
Returns objects in `C` (not `Cᵒᵖ'`).
-/
def ccrFamily (x : CoprodCovarRepCat.{u, v, w} C) : ccrIndex x → C := x.fiber

@[simp]
lemma ccrObjMk_index {X : Type w} (F : X → C) :
    ccrIndex (ccrObjMk F) = X := rfl

@[simp]
lemma ccrObjMk_family {X : Type w} (F : X → C) :
    ccrFamily (ccrObjMk F) = F := rfl

/--
Construct a morphism in `CoprodCovarRepCat C` from a reindexing function
and a family of fiber morphisms.

A morphism `(X, F) → (Y, G)` consists of:
- `reindex : X ⟶ Y` (morphism in `Type`)
- `fiberMor : ∀ i, G(reindex(i)) ⟶ F(i)` (family of morphisms in `C`)

Note: The fiber morphisms go from target to source, which is opposite to
`FreeCoprodCompletionCat`.
-/
def ccrHomMk {x y : CoprodCovarRepCat.{u, v, w} C}
    (reindex : ccrIndex x ⟶ ccrIndex y)
    (fiberMor : ∀ i : ccrIndex x, ccrFamily y (reindex i) ⟶ ccrFamily x i) :
    x ⟶ y :=
  ⟨reindex, fiberMor⟩

/--
Extract the reindexing function from a morphism in `CoprodCovarRepCat C`.
-/
def ccrReindex {x y : CoprodCovarRepCat.{u, v, w} C} (f : x ⟶ y) :
    ccrIndex x ⟶ ccrIndex y :=
  f.base

/--
Extract the fiber morphism at index `i` from a morphism in
`CoprodCovarRepCat C`. For a morphism `f : (X, F) → (Y, G)`, this returns
`G(reindex i) ⟶ F(i)` in `C`.
-/
def ccrFiberMor {x y : CoprodCovarRepCat.{u, v, w} C} (f : x ⟶ y)
    (i : ccrIndex x) : ccrFamily y (ccrReindex f i) ⟶ ccrFamily x i :=
  f.fiber i

@[simp]
lemma ccrHomMk_reindex {x y : CoprodCovarRepCat.{u, v, w} C}
    (reindex : ccrIndex x ⟶ ccrIndex y)
    (fiberMor : ∀ i : ccrIndex x, ccrFamily y (reindex i) ⟶ ccrFamily x i) :
    ccrReindex (ccrHomMk reindex fiberMor) = reindex := rfl

@[simp]
lemma ccrHomMk_fiberMor {x y : CoprodCovarRepCat.{u, v, w} C}
    (reindex : ccrIndex x ⟶ ccrIndex y)
    (fiberMor : ∀ i : ccrIndex x, ccrFamily y (reindex i) ⟶ ccrFamily x i)
    (i : ccrIndex x) :
    ccrFiberMor (ccrHomMk reindex fiberMor) i = fiberMor i := rfl

@[ext (iff := false)]
lemma ccrHom_ext {x y : CoprodCovarRepCat.{u, v, w} C} (f g : x ⟶ y)
    (hbase : f.base = g.base)
    (hfiber : f.fiber ≫ eqToHom (by rw [hbase]) = g.fiber) : f = g :=
  GrothendieckContra'.ext f g hbase hfiber

/--
The identity morphism in `CoprodCovarRepCat C` has identity reindexing.
-/
@[simp]
lemma ccrId_reindex (x : CoprodCovarRepCat.{u, v, w} C) :
    ccrReindex (𝟙 x) = 𝟙 (ccrIndex x) := rfl

/--
The identity morphism in `CoprodCovarRepCat C` has identity fiber morphisms.
-/
@[simp]
lemma ccrId_fiberMor (x : CoprodCovarRepCat.{u, v, w} C) (i : ccrIndex x) :
    ccrFiberMor (𝟙 x) i = 𝟙 (ccrFamily x i) := rfl

/--
Composition in `CoprodCovarRepCat C`: the reindexing composes covariantly.
-/
@[simp]
lemma ccrComp_reindex {x y z : CoprodCovarRepCat.{u, v, w} C}
    (f : x ⟶ y) (g : y ⟶ z) :
    ccrReindex (f ≫ g) = ccrReindex f ≫ ccrReindex g := rfl

/--
Composition in `CoprodCovarRepCat C`: the fiber morphisms compose
contravariantly. For `f : x ⟶ y` and `g : y ⟶ z`, the fiber morphism at
index `i` is `ccrFiberMor g (ccrReindex f i) ≫ ccrFiberMor f i`.
-/
@[simp]
lemma ccrComp_fiberMor {x y z : CoprodCovarRepCat.{u, v, w} C}
    (f : x ⟶ y) (g : y ⟶ z) (i : ccrIndex x) :
    ccrFiberMor (f ≫ g) i = ccrFiberMor g (ccrReindex f i) ≫ ccrFiberMor f i := by
  unfold ccrFiberMor ccrReindex
  change (GrothendieckContra'.comp f g).fiber i = g.fiber (f.base i) ≫ f.fiber i
  unfold GrothendieckContra'.comp
  simp only [eqToHom_refl, Category.comp_id]
  rfl

end CoprodCovarRepHelpers

/-! ## Equivalence between CoprodCovarRepCat and FreeCoprodCompletionCat

`CoprodCovarRepCat C` is equivalent to `FreeCoprodCompletionCat (C^op')`.
This follows from the isomorphism `FamilyCat (C^op') X ≅ (FamilyCat C X)^op'`.
-/

section CoprodCovarRepEquiv

universe w

variable {C : Type u} [Category.{v} C]

def ccrFcOpEq :
  CoprodCovarRepCat.{u, v, w} C = FreeCoprodCompletionCat.{u, v, w} Cᵒᵖ' :=
    rfl

open CategoryTheory.Limits CategoryTheory.Adjunction in
instance hasCoproducts_CoprodCovarRepCat :
  HasCoproducts.{w} (CoprodCovarRepCat.{u, v, w} C) :=
    hasCoproducts_of_colimit_cofans
      (fcCofan (C := Cᵒᵖ'))
      (fcIsColimitCofan (C := Cᵒᵖ'))

end CoprodCovarRepEquiv

/-! ## Product of contravariant representables helpers -/

section ProdContravarRepHelpers

universe w

variable {C : Type u} [Category.{v} C]

/--
Construct an object of `ProdContravarRepCat C` from an index type and
a family of objects from `C`. Internally, objects are stored as families
in `Cᵒᵖ'`, but this helper hides that detail.
-/
def pcrObjMk {X : Type w} (F : X → C) : ProdContravarRepCat.{u, v, w} C :=
  ⟨X, F⟩

/--
Extract the index type from an object of `ProdContravarRepCat C`.
-/
def pcrIndex (x : ProdContravarRepCat.{u, v, w} C) : Type w := x.base

/--
Extract the family of objects from an object of `ProdContravarRepCat C`.
Returns objects in `C` (not `Cᵒᵖ'`).
-/
def pcrFamily (x : ProdContravarRepCat.{u, v, w} C) : pcrIndex x → C := x.fiber

@[simp]
lemma pcrObjMk_index {X : Type w} (F : X → C) :
    pcrIndex (pcrObjMk F) = X := rfl

@[simp]
lemma pcrObjMk_family {X : Type w} (F : X → C) :
    pcrFamily (pcrObjMk F) = F := rfl

/--
Construct a morphism in `ProdContravarRepCat C` from a reindexing function
and a family of fiber morphisms.

A morphism `(X, F) → (Y, G)` consists of:
- `reindex : Y ⟶ X` (morphism in `Type`, note: opposite direction)
- `fiberMor : ∀ j, G(j) ⟶ F(reindex(j))` (family of morphisms in `C`)

Note: The reindexing goes from target to source index, and the fiber morphisms
go from target family to source family.
-/
def pcrHomMk {x y : ProdContravarRepCat.{u, v, w} C}
    (reindex : pcrIndex y ⟶ pcrIndex x)
    (fiberMor : ∀ j : pcrIndex y, pcrFamily y j ⟶ pcrFamily x (reindex j)) :
    x ⟶ y :=
  ⟨reindex, fiberMor⟩

/--
Extract the reindexing function from a morphism in `ProdContravarRepCat C`.
Note: For a morphism `(X, F) → (Y, G)`, this is a morphism `Y ⟶ X` in `Type`.
-/
def pcrReindex {x y : ProdContravarRepCat.{u, v, w} C} (f : x ⟶ y) :
    pcrIndex y ⟶ pcrIndex x :=
  f.base

/--
Extract the fiber morphism at index `j` from a morphism in
`ProdContravarRepCat C`. For a morphism `f : (X, F) → (Y, G)`, this returns
`G(j) ⟶ F(reindex j)` in `C`.
-/
def pcrFiberMor {x y : ProdContravarRepCat.{u, v, w} C} (f : x ⟶ y)
    (j : pcrIndex y) : pcrFamily y j ⟶ pcrFamily x (pcrReindex f j) :=
  f.fiber j

@[simp]
lemma pcrHomMk_reindex {x y : ProdContravarRepCat.{u, v, w} C}
    (reindex : pcrIndex y ⟶ pcrIndex x)
    (fiberMor : ∀ j : pcrIndex y, pcrFamily y j ⟶ pcrFamily x (reindex j)) :
    pcrReindex (pcrHomMk reindex fiberMor) = reindex := rfl

@[simp]
lemma pcrHomMk_fiberMor {x y : ProdContravarRepCat.{u, v, w} C}
    (reindex : pcrIndex y ⟶ pcrIndex x)
    (fiberMor : ∀ j : pcrIndex y, pcrFamily y j ⟶ pcrFamily x (reindex j))
    (j : pcrIndex y) :
    pcrFiberMor (pcrHomMk reindex fiberMor) j = fiberMor j := rfl

@[ext (iff := false)]
lemma pcrHom_ext {x y : ProdContravarRepCat.{u, v, w} C} (f g : x ⟶ y)
    (hbase : f.base = g.base)
    (hfiber : eqToHom (by rw [hbase]) ≫ f.fiber = g.fiber) : f = g :=
  Grothendieck.ext f g hbase hfiber

/--
The identity morphism in `ProdContravarRepCat C` has identity reindexing.
-/
@[simp]
lemma pcrId_reindex (x : ProdContravarRepCat.{u, v, w} C) :
    pcrReindex (𝟙 x) = 𝟙 (pcrIndex x) := rfl

/--
The identity morphism in `ProdContravarRepCat C` has identity fiber morphisms.
-/
@[simp]
lemma pcrId_fiberMor (x : ProdContravarRepCat.{u, v, w} C) (j : pcrIndex x) :
    pcrFiberMor (𝟙 x) j = 𝟙 (pcrFamily x j) := rfl

/--
Composition in `ProdContravarRepCat C`: the reindexing composes
contravariantly (in the opposite order from the morphisms).
-/
@[simp]
lemma pcrComp_reindex {x y z : ProdContravarRepCat.{u, v, w} C}
    (f : x ⟶ y) (g : y ⟶ z) :
    pcrReindex (f ≫ g) = pcrReindex g ≫ pcrReindex f := rfl

/--
Composition in `ProdContravarRepCat C`: the fiber morphisms compose
contravariantly. For `f : x ⟶ y` and `g : y ⟶ z`, the fiber morphism at
index `k : pcrIndex z` is `pcrFiberMor g k ≫ pcrFiberMor f (pcrReindex g k)`.
-/
@[simp]
lemma pcrComp_fiberMor {x y z : ProdContravarRepCat.{u, v, w} C}
    (f : x ⟶ y) (g : y ⟶ z) (k : pcrIndex z) :
    pcrFiberMor (f ≫ g) k = pcrFiberMor g k ≫ pcrFiberMor f (pcrReindex g k) := by
  unfold pcrFiberMor pcrReindex
  change (Grothendieck.comp f g).fiber k = g.fiber k ≫ f.fiber (g.base k)
  unfold Grothendieck.comp
  simp only [eqToHom_refl, Category.id_comp]
  rfl

end ProdContravarRepHelpers

/-! ## Layered Grothendieck constructions -/

section LayeredConstructions

universe w₁ w₂

variable (C : Type u) [Category.{v} C]

/--
The free coproduct completion of the free product completion of `C`, with
flexible universe levels for the outer index types (`w₁`) and inner index
types (`w₂`).

Objects are `(I, (X_i, F_i)_{i ∈ I})` where `I : Type w₁` and for each
`i ∈ I`, `X_i : Type w₂` and `F_i : X_i → C` is a family.

Morphisms `(I, (X_i, F_i)) → (J, (Y_j, G_j))` consist of:
- `reindexOuter : I → J`
- For each `i ∈ I`, `reindexInner_i : Y_{reindexOuter(i)} → X_i`
- For each `i ∈ I` and `k ∈ Y_{reindexOuter(i)}`,
  `fiberMor_{i,k} : F_i(reindexInner_i(k)) → G_{reindexOuter(i)}(k)`
-/
@[simp]
def FreeCoprodProdCat.{u', v', w₁', w₂'} (C' : Type u') [Category.{v'} C'] : Cat :=
  FreeCoprodCompletionCat.{max (w₂' + 1) u' w₂', max w₂' v', w₁'}
    (FreeProdCompletionCat.{u', v', w₂'} C')

/--
The coproduct of covariant representables construction applied twice, with
flexible universe levels for the outer index types (`w₁`) and inner index
types (`w₂`).

Objects are `(I, (X_i, F_i)_{i ∈ I})` where `I : Type w₁` and for each
`i ∈ I`, `X_i : Type w₂` and `F_i : X_i → C` is a family.

Morphisms `(I, (X_i, F_i)) → (J, (Y_j, G_j))` consist of:
- `reindexOuter : I → J`
- For each `i ∈ I`, `reindexInner_i : Y_{reindexOuter(i)} → X_i`
- For each `i ∈ I` and `k ∈ Y_{reindexOuter(i)}`,
  `fiberMor_{i,k} : F_i(reindexInner_i(k)) → G_{reindexOuter(i)}(k)`

This has the same morphism structure as `FreeCoprodProdCat`.
-/
@[simp]
def CoprodCovarRepSquaredCat.{u', v', w₁', w₂'} (C' : Type u') [Category.{v'} C'] : Cat :=
  CoprodCovarRepCat.{max (w₂' + 1) u' w₂', max w₂' v', w₁'}
    (CoprodCovarRepCat.{u', v', w₂'} C')

end LayeredConstructions

/-! ## Free coproduct-product completion helpers -/

section FreeCoprodProdHelpers

universe w₁ w₂

variable {C : Type u} [Category.{v} C]

/--
Construct an object of `FreeCoprodProdCat C` from an outer index type,
an inner index type family, and a family of families of objects.
-/
def fcpObjMk {I : Type w₁} {X : I → Type w₂} (F : ∀ i, X i → C) :
    FreeCoprodProdCat.{u, v, w₁, w₂} C :=
  ⟨I, fun i => ⟨X i, F i⟩⟩

/--
Extract the outer index type from an object of `FreeCoprodProdCat C`.
-/
def fcpOuterIndex (x : FreeCoprodProdCat.{u, v, w₁, w₂} C) : Type w₁ :=
  x.base

/--
Extract the inner index type at outer index `i` from an object of
`FreeCoprodProdCat C`.
-/
def fcpInnerIndex (x : FreeCoprodProdCat.{u, v, w₁, w₂} C) (i : fcpOuterIndex x) :
    Type w₂ :=
  (x.fiber i).base

/--
Extract the family of objects at outer index `i` and inner index `k` from
an object of `FreeCoprodProdCat C`.
-/
def fcpFamily (x : FreeCoprodProdCat.{u, v, w₁, w₂} C) (i : fcpOuterIndex x)
    (k : fcpInnerIndex x i) : C :=
  (x.fiber i).fiber k

@[simp]
lemma fcpObjMk_outerIndex {I : Type w₁} {X : I → Type w₂}
    (F : ∀ i, X i → C) : fcpOuterIndex (fcpObjMk F) = I := rfl

@[simp]
lemma fcpObjMk_innerIndex {I : Type w₁} {X : I → Type w₂}
    (F : ∀ i, X i → C) (i : I) : fcpInnerIndex (fcpObjMk F) i = X i := rfl

@[simp]
lemma fcpObjMk_family {I : Type w₁} {X : I → Type w₂}
    (F : ∀ i, X i → C) (i : I) (k : X i) : fcpFamily (fcpObjMk F) i k = F i k :=
  rfl

/--
Construct a morphism in `FreeCoprodProdCat C`.

A morphism `(I, (X_i, F_i)) → (J, (Y_j, G_j))` consists of:
- `reindexOuter : I ⟶ J` (morphism in `Type`)
- `reindexInner : ∀ i, Y_{reindexOuter(i)} ⟶ X_i` (contravariant in `Type`)
- `fiberMor : ∀ i k, F_i(reindexInner_i(k)) ⟶ G_{reindexOuter(i)}(k)` (in `C`)
-/
def fcpHomMk {x y : FreeCoprodProdCat.{u, v, w₁, w₂} C}
    (reindexOuter : fcpOuterIndex x ⟶ fcpOuterIndex y)
    (reindexInner : ∀ i, fcpInnerIndex y (reindexOuter i) ⟶ fcpInnerIndex x i)
    (fiberMor : ∀ i k, fcpFamily x i (reindexInner i k) ⟶
      fcpFamily y (reindexOuter i) k) : x ⟶ y :=
  ⟨reindexOuter, fun i => ⟨reindexInner i, fiberMor i⟩⟩

/--
Extract the outer reindexing function from a morphism in `FreeCoprodProdCat C`.
-/
def fcpReindexOuter {x y : FreeCoprodProdCat.{u, v, w₁, w₂} C} (f : x ⟶ y) :
    fcpOuterIndex x ⟶ fcpOuterIndex y :=
  f.base

/--
Extract the inner reindexing function at outer index `i` from a morphism in
`FreeCoprodProdCat C`.
-/
def fcpReindexInner {x y : FreeCoprodProdCat.{u, v, w₁, w₂} C} (f : x ⟶ y)
    (i : fcpOuterIndex x) :
    fcpInnerIndex y (fcpReindexOuter f i) ⟶ fcpInnerIndex x i :=
  (f.fiber i).base

/--
Extract the fiber morphism at outer index `i` and inner index `k` from a
morphism in `FreeCoprodProdCat C`.
-/
def fcpFiberMor {x y : FreeCoprodProdCat.{u, v, w₁, w₂} C} (f : x ⟶ y)
    (i : fcpOuterIndex x) (k : fcpInnerIndex y (fcpReindexOuter f i)) :
    fcpFamily x i (fcpReindexInner f i k) ⟶
    fcpFamily y (fcpReindexOuter f i) k :=
  (f.fiber i).fiber k

@[simp]
lemma fcpHomMk_reindexOuter {x y : FreeCoprodProdCat.{u, v, w₁, w₂} C}
    (reindexOuter : fcpOuterIndex x ⟶ fcpOuterIndex y)
    (reindexInner : ∀ i, fcpInnerIndex y (reindexOuter i) ⟶ fcpInnerIndex x i)
    (fiberMor : ∀ i k, fcpFamily x i (reindexInner i k) ⟶
      fcpFamily y (reindexOuter i) k) :
    fcpReindexOuter (fcpHomMk reindexOuter reindexInner fiberMor) =
      reindexOuter := rfl

@[simp]
lemma fcpHomMk_reindexInner {x y : FreeCoprodProdCat.{u, v, w₁, w₂} C}
    (reindexOuter : fcpOuterIndex x ⟶ fcpOuterIndex y)
    (reindexInner : ∀ i, fcpInnerIndex y (reindexOuter i) ⟶ fcpInnerIndex x i)
    (fiberMor : ∀ i k, fcpFamily x i (reindexInner i k) ⟶
      fcpFamily y (reindexOuter i) k) (i : fcpOuterIndex x) :
    fcpReindexInner (fcpHomMk reindexOuter reindexInner fiberMor) i =
      reindexInner i := rfl

@[simp]
lemma fcpHomMk_fiberMor {x y : FreeCoprodProdCat.{u, v, w₁, w₂} C}
    (reindexOuter : fcpOuterIndex x ⟶ fcpOuterIndex y)
    (reindexInner : ∀ i, fcpInnerIndex y (reindexOuter i) ⟶ fcpInnerIndex x i)
    (fiberMor : ∀ i k, fcpFamily x i (reindexInner i k) ⟶
      fcpFamily y (reindexOuter i) k) (i : fcpOuterIndex x)
    (k : fcpInnerIndex y (reindexOuter i)) :
    fcpFiberMor (fcpHomMk reindexOuter reindexInner fiberMor) i k =
      fiberMor i k := rfl

/--
The identity morphism in `FreeCoprodProdCat C` has identity outer reindexing.
-/
@[simp]
lemma fcpId_reindexOuter (x : FreeCoprodProdCat.{u, v, w₁, w₂} C) :
    fcpReindexOuter (𝟙 x) = 𝟙 (fcpOuterIndex x) := rfl

/--
The identity morphism in `FreeCoprodProdCat C` has identity inner reindexing.
-/
@[simp]
lemma fcpId_reindexInner (x : FreeCoprodProdCat.{u, v, w₁, w₂} C)
    (i : fcpOuterIndex x) :
    fcpReindexInner (𝟙 x) i = 𝟙 (fcpInnerIndex x i) := rfl

/--
The identity morphism in `FreeCoprodProdCat C` has identity fiber morphisms.
-/
@[simp]
lemma fcpId_fiberMor (x : FreeCoprodProdCat.{u, v, w₁, w₂} C) (i : fcpOuterIndex x)
    (k : fcpInnerIndex x i) :
    fcpFiberMor (𝟙 x) i k = 𝟙 (fcpFamily x i k) := rfl

/--
Composition in `FreeCoprodProdCat C`: the outer reindexing composes
covariantly.
-/
@[simp]
lemma fcpComp_reindexOuter {x y z : FreeCoprodProdCat.{u, v, w₁, w₂} C}
    (f : x ⟶ y) (g : y ⟶ z) :
    fcpReindexOuter (f ≫ g) = fcpReindexOuter f ≫ fcpReindexOuter g := rfl

/--
Composition in `FreeCoprodProdCat C`: the inner reindexing composes
contravariantly.
-/
@[simp]
lemma fcpComp_reindexInner {x y z : FreeCoprodProdCat.{u, v, w₁, w₂} C}
    (f : x ⟶ y) (g : y ⟶ z) (i : fcpOuterIndex x) :
    fcpReindexInner (f ≫ g) i =
      fcpReindexInner g (fcpReindexOuter f i) ≫ fcpReindexInner f i := rfl

/--
Composition in `FreeCoprodProdCat C`: fiber morphisms compose covariantly
after applying the appropriate reindexing.

For `f : x ⟶ y` and `g : y ⟶ z`, the fiber morphism at outer index `i` and
inner index `k` is:
`f.fiberMor i (g.innerReindex k) ≫ g.fiberMor (f.outerReindex i) k`.

This uses `GrothendieckContra'.comp_fiber` for the outer layer and
`Grothendieck.comp_fiber` for the inner layer.
-/
@[simp]
lemma fcpComp_fiberMor {x y z : FreeCoprodProdCat.{u, v, w₁, w₂} C}
    (f : x ⟶ y) (g : y ⟶ z) (i : fcpOuterIndex x)
    (k : fcpInnerIndex z (fcpReindexOuter g (fcpReindexOuter f i))) :
    fcpFiberMor (f ≫ g) i k =
      fcpFiberMor f i (fcpReindexInner g (fcpReindexOuter f i) k) ≫
      fcpFiberMor g (fcpReindexOuter f i) k := by
  simp only [fcpFiberMor, fcpReindexOuter, fcpReindexInner]
  have h_fc := fcComp_fiberMor f g i
  have h_fp := fpComp_fiberMor (fcFiberMor f i) (fcFiberMor g (fcReindex f i)) k
  simp only [fcFiberMor, fcReindex, fpFiberMor, fpReindex] at h_fc h_fp
  intermediate_eq (f.fiber i ≫ g.fiber (f.base i)).fiber k
  · grind
  · exact h_fp

end FreeCoprodProdHelpers

/-! ## Coproduct of covariant representables squared helpers -/

section CoprodCovarRepSquaredHelpers

universe w₁ w₂

variable {C : Type u} [Category.{v} C]

/--
Construct an object of `CoprodCovarRepSquaredCat C` from an outer index type,
an inner index type family, and a family of families of objects.
-/
def ccrsObjMk {I : Type w₁} {X : I → Type w₂} (F : ∀ i, X i → C) :
    CoprodCovarRepSquaredCat.{u, v, w₁, w₂} C :=
  ⟨I, fun i => ⟨X i, F i⟩⟩

/--
Extract the outer index type from an object of `CoprodCovarRepSquaredCat C`.
-/
def ccrsOuterIndex (x : CoprodCovarRepSquaredCat.{u, v, w₁, w₂} C) : Type w₁ :=
  x.base

/--
Extract the inner index type at outer index `i` from an object of
`CoprodCovarRepSquaredCat C`.
-/
def ccrsInnerIndex (x : CoprodCovarRepSquaredCat.{u, v, w₁, w₂} C)
    (i : ccrsOuterIndex x) : Type w₂ :=
  (x.fiber i).base

/--
Extract the family of objects at outer index `i` and inner index `k` from
an object of `CoprodCovarRepSquaredCat C`.
-/
def ccrsFamily (x : CoprodCovarRepSquaredCat.{u, v, w₁, w₂} C)
    (i : ccrsOuterIndex x) (k : ccrsInnerIndex x i) : C :=
  (x.fiber i).fiber k

@[simp]
lemma ccrsObjMk_outerIndex {I : Type w₁} {X : I → Type w₂}
    (F : ∀ i, X i → C) : ccrsOuterIndex (ccrsObjMk F) = I := rfl

@[simp]
lemma ccrsObjMk_innerIndex {I : Type w₁} {X : I → Type w₂}
    (F : ∀ i, X i → C) (i : I) : ccrsInnerIndex (ccrsObjMk F) i = X i := rfl

@[simp]
lemma ccrsObjMk_family {I : Type w₁} {X : I → Type w₂}
    (F : ∀ i, X i → C) (i : I) (k : X i) : ccrsFamily (ccrsObjMk F) i k = F i k :=
  rfl

/--
Construct a morphism in `CoprodCovarRepSquaredCat C`.

A morphism `(I, (X_i, F_i)) → (J, (Y_j, G_j))` consists of:
- `reindexOuter : I ⟶ J` (morphism in `Type`, covariant)
- `reindexInner : ∀ i, Y_{reindexOuter(i)} ⟶ X_i` (contravariant in `Type`)
- `fiberMor : ∀ i k, F_i(reindexInner_i(k)) ⟶ G_{reindexOuter(i)}(k)` (in `C`)

Note: Outer reindexing is covariant, inner reindexing is contravariant,
but fiber morphisms are covariant (source to target).
-/
def ccrsHomMk {x y : CoprodCovarRepSquaredCat.{u, v, w₁, w₂} C}
    (reindexOuter : ccrsOuterIndex x ⟶ ccrsOuterIndex y)
    (reindexInner : ∀ i, ccrsInnerIndex y (reindexOuter i) ⟶ ccrsInnerIndex x i)
    (fiberMor : ∀ i k, ccrsFamily x i (reindexInner i k) ⟶
      ccrsFamily y (reindexOuter i) k) : x ⟶ y :=
  ⟨reindexOuter, fun i => ⟨reindexInner i, fiberMor i⟩⟩

/--
Extract the outer reindexing function from a morphism in
`CoprodCovarRepSquaredCat C`.
-/
def ccrsReindexOuter {x y : CoprodCovarRepSquaredCat.{u, v, w₁, w₂} C}
    (f : x ⟶ y) : ccrsOuterIndex x ⟶ ccrsOuterIndex y :=
  f.base

/--
Extract the inner reindexing function at outer index `i` from a morphism in
`CoprodCovarRepSquaredCat C`. Note: inner reindexing is contravariant.
-/
def ccrsReindexInner {x y : CoprodCovarRepSquaredCat.{u, v, w₁, w₂} C}
    (f : x ⟶ y) (i : ccrsOuterIndex x) :
    ccrsInnerIndex y (ccrsReindexOuter f i) ⟶ ccrsInnerIndex x i :=
  (f.fiber i).base

/--
Extract the fiber morphism at outer index `i` and inner index `k` from a
morphism in `CoprodCovarRepSquaredCat C`. Fiber morphisms are covariant
(source to target).
-/
def ccrsFiberMor {x y : CoprodCovarRepSquaredCat.{u, v, w₁, w₂} C}
    (f : x ⟶ y) (i : ccrsOuterIndex x)
    (k : ccrsInnerIndex y (ccrsReindexOuter f i)) :
    ccrsFamily x i (ccrsReindexInner f i k) ⟶
    ccrsFamily y (ccrsReindexOuter f i) k :=
  (f.fiber i).fiber k

@[simp]
lemma ccrsHomMk_reindexOuter {x y : CoprodCovarRepSquaredCat.{u, v, w₁, w₂} C}
    (reindexOuter : ccrsOuterIndex x ⟶ ccrsOuterIndex y)
    (reindexInner : ∀ i, ccrsInnerIndex y (reindexOuter i) ⟶ ccrsInnerIndex x i)
    (fiberMor : ∀ i k, ccrsFamily x i (reindexInner i k) ⟶
      ccrsFamily y (reindexOuter i) k) :
    ccrsReindexOuter (ccrsHomMk reindexOuter reindexInner fiberMor) =
      reindexOuter := rfl

@[simp]
lemma ccrsHomMk_reindexInner {x y : CoprodCovarRepSquaredCat.{u, v, w₁, w₂} C}
    (reindexOuter : ccrsOuterIndex x ⟶ ccrsOuterIndex y)
    (reindexInner : ∀ i, ccrsInnerIndex y (reindexOuter i) ⟶ ccrsInnerIndex x i)
    (fiberMor : ∀ i k, ccrsFamily x i (reindexInner i k) ⟶
      ccrsFamily y (reindexOuter i) k) (i : ccrsOuterIndex x) :
    ccrsReindexInner (ccrsHomMk reindexOuter reindexInner fiberMor) i =
      reindexInner i := rfl

@[simp]
lemma ccrsHomMk_fiberMor {x y : CoprodCovarRepSquaredCat.{u, v, w₁, w₂} C}
    (reindexOuter : ccrsOuterIndex x ⟶ ccrsOuterIndex y)
    (reindexInner : ∀ i, ccrsInnerIndex y (reindexOuter i) ⟶ ccrsInnerIndex x i)
    (fiberMor : ∀ i k, ccrsFamily x i (reindexInner i k) ⟶
      ccrsFamily y (reindexOuter i) k) (i : ccrsOuterIndex x)
    (k : ccrsInnerIndex y (reindexOuter i)) :
    ccrsFiberMor (ccrsHomMk reindexOuter reindexInner fiberMor) i k =
      fiberMor i k := rfl

/--
The identity morphism in `CoprodCovarRepSquaredCat C` has identity outer
reindexing.
-/
@[simp]
lemma ccrsId_reindexOuter (x : CoprodCovarRepSquaredCat.{u, v, w₁, w₂} C) :
    ccrsReindexOuter (𝟙 x) = 𝟙 (ccrsOuterIndex x) := rfl

/--
The identity morphism in `CoprodCovarRepSquaredCat C` has identity inner
reindexing.
-/
@[simp]
lemma ccrsId_reindexInner (x : CoprodCovarRepSquaredCat.{u, v, w₁, w₂} C)
    (i : ccrsOuterIndex x) :
    ccrsReindexInner (𝟙 x) i = 𝟙 (ccrsInnerIndex x i) := rfl

/--
The identity morphism in `CoprodCovarRepSquaredCat C` has identity fiber
morphisms.
-/
@[simp]
lemma ccrsId_fiberMor (x : CoprodCovarRepSquaredCat.{u, v, w₁, w₂} C)
    (i : ccrsOuterIndex x) (k : ccrsInnerIndex x i) :
    ccrsFiberMor (𝟙 x) i k = 𝟙 (ccrsFamily x i k) := rfl

/--
Composition in `CoprodCovarRepSquaredCat C`: the outer reindexing composes
covariantly.
-/
@[simp]
lemma ccrsComp_reindexOuter {x y z : CoprodCovarRepSquaredCat.{u, v, w₁, w₂} C}
    (f : x ⟶ y) (g : y ⟶ z) :
    ccrsReindexOuter (f ≫ g) = ccrsReindexOuter f ≫ ccrsReindexOuter g := rfl

/--
Composition in `CoprodCovarRepSquaredCat C`: the inner reindexing composes
contravariantly.
-/
@[simp]
lemma ccrsComp_reindexInner {x y z : CoprodCovarRepSquaredCat.{u, v, w₁, w₂} C}
    (f : x ⟶ y) (g : y ⟶ z) (i : ccrsOuterIndex x) :
    ccrsReindexInner (f ≫ g) i =
      ccrsReindexInner g (ccrsReindexOuter f i) ≫ ccrsReindexInner f i := rfl

/--
Composition in `CoprodCovarRepSquaredCat C`: the fiber morphism at outer index
`i` and inner index `k` is:
`f.fiberMor i (g.innerReindex (f.outerReindex i) k) ≫ g.fiberMor (f.outerReindex i) k`.

This uses `ccrComp_fiberMor` for both the outer and inner layers.
-/
@[simp]
lemma ccrsComp_fiberMor {x y z : CoprodCovarRepSquaredCat.{u, v, w₁, w₂} C}
    (f : x ⟶ y) (g : y ⟶ z) (i : ccrsOuterIndex x)
    (k : ccrsInnerIndex z (ccrsReindexOuter g (ccrsReindexOuter f i))) :
    ccrsFiberMor (f ≫ g) i k =
      ccrsFiberMor f i (ccrsReindexInner g (ccrsReindexOuter f i) k) ≫
      ccrsFiberMor g (ccrsReindexOuter f i) k := by
  simp only [ccrsFiberMor, ccrsReindexOuter, ccrsReindexInner]
  have h_outer := ccrComp_fiberMor f g i
  have h_inner := ccrComp_fiberMor (g.fiber (f.base i)) (f.fiber i) k
  simp only [ccrFiberMor, ccrReindex] at h_outer h_inner
  intermediate_eq (g.fiber (f.base i) ≫ f.fiber i).fiber k
  · grind
  · exact h_inner

end CoprodCovarRepSquaredHelpers

/-! ## Isomorphism between layered constructions -/

section LayeredIsomorphism

universe w₁ w₂

variable {C : Type u} [Category.{v} C]

/--
Convert an object of `FreeCoprodProdCat C` to an object of
`CoprodCovarRepSquaredCat C`.
-/
def fcpToCcrsObj (x : FreeCoprodProdCat.{u, v, w₁, w₂} C) :
    CoprodCovarRepSquaredCat.{u, v, w₁, w₂} C :=
  ⟨fcpOuterIndex x, fun i => ⟨fcpInnerIndex x i, fcpFamily x i⟩⟩

/--
Convert a morphism in `FreeCoprodProdCat C` to a morphism in
`CoprodCovarRepSquaredCat C`.
-/
def fcpToCcrsMor {x y : FreeCoprodProdCat.{u, v, w₁, w₂} C} (f : x ⟶ y) :
    fcpToCcrsObj x ⟶ fcpToCcrsObj y :=
  ⟨fcpReindexOuter f, fun i => ⟨fcpReindexInner f i, fcpFiberMor f i⟩⟩

/--
Convert an object of `CoprodCovarRepSquaredCat C` to an object of
`FreeCoprodProdCat C`.
-/
def ccrsToFcpObj (x : CoprodCovarRepSquaredCat.{u, v, w₁, w₂} C) :
    FreeCoprodProdCat.{u, v, w₁, w₂} C :=
  ⟨ccrsOuterIndex x, fun i => ⟨ccrsInnerIndex x i, ccrsFamily x i⟩⟩

/--
Convert a morphism in `CoprodCovarRepSquaredCat C` to a morphism in
`FreeCoprodProdCat C`.
-/
def ccrsToFcpMor {x y : CoprodCovarRepSquaredCat.{u, v, w₁, w₂} C} (f : x ⟶ y) :
    ccrsToFcpObj x ⟶ ccrsToFcpObj y :=
  ⟨ccrsReindexOuter f, fun i => ⟨ccrsReindexInner f i, ccrsFiberMor f i⟩⟩

@[simp]
lemma fcpToCcrsObj_ccrsToFcpObj
    (x : CoprodCovarRepSquaredCat.{u, v, w₁, w₂} C) :
    fcpToCcrsObj (ccrsToFcpObj x) = x := rfl

@[simp]
lemma ccrsToFcpObj_fcpToCcrsObj (x : FreeCoprodProdCat.{u, v, w₁, w₂} C) :
    ccrsToFcpObj (fcpToCcrsObj x) = x := rfl

@[simp]
lemma fcpToCcrsMor_ccrsToFcpMor
    {x y : CoprodCovarRepSquaredCat.{u, v, w₁, w₂} C} (f : x ⟶ y) :
    fcpToCcrsMor (ccrsToFcpMor f) = f := rfl

@[simp]
lemma ccrsToFcpMor_fcpToCcrsMor
    {x y : FreeCoprodProdCat.{u, v, w₁, w₂} C} (f : x ⟶ y) :
    ccrsToFcpMor (fcpToCcrsMor f) = f := rfl

@[simp]
lemma ccrsToFcpMor_comp {x y z : CoprodCovarRepSquaredCat.{u, v, w₁, w₂} C}
    (f : x ⟶ y) (g : y ⟶ z) :
    ccrsToFcpMor (f ≫ g) = ccrsToFcpMor f ≫ ccrsToFcpMor g := by
  simp only [ccrsToFcpMor, ccrsReindexOuter, ccrsReindexInner]
  fapply GrothendieckContra'.ext
  · rfl
  · simp only [eqToHom_refl, Category.comp_id]
    funext i
    fapply Grothendieck.ext
    · rfl
    · simp only [eqToHom_refl, Category.id_comp]
      funext k
      have h_ccrs := ccrsComp_fiberMor f g i k
      have h_fcp := fcpComp_fiberMor (ccrsToFcpMor f) (ccrsToFcpMor g) i k
      simp only [ccrsToFcpMor, ccrsReindexOuter, ccrsReindexInner, ccrsFiberMor,
                 fcpReindexOuter, fcpReindexInner, fcpFiberMor] at *
      rw [h_ccrs, h_fcp]

@[simp]
lemma fcpToCcrsMor_comp {x y z : FreeCoprodProdCat.{u, v, w₁, w₂} C}
    (f : x ⟶ y) (g : y ⟶ z) :
    fcpToCcrsMor (f ≫ g) = fcpToCcrsMor f ≫ fcpToCcrsMor g := by
  have h : f ≫ g = ccrsToFcpMor (fcpToCcrsMor f ≫ fcpToCcrsMor g) := by
    simp only [ccrsToFcpMor_comp, ccrsToFcpMor_fcpToCcrsMor]
  rw [h, fcpToCcrsMor_ccrsToFcpMor]

variable (C)

/--
The forward functor from `FreeCoprodProdCat C` to `CoprodCovarRepSquaredCat C`.
-/
@[simp]
def fcpToCcrs :
    FreeCoprodProdCat.{u, v, w₁, w₂} C ⥤ CoprodCovarRepSquaredCat.{u, v, w₁, w₂} C where
  obj := fcpToCcrsObj
  map := fcpToCcrsMor
  map_comp := fcpToCcrsMor_comp

/--
The backward functor from `CoprodCovarRepSquaredCat C` to `FreeCoprodProdCat C`.
-/
@[simp]
def ccrsToFcp :
    CoprodCovarRepSquaredCat.{u, v, w₁, w₂} C ⥤ FreeCoprodProdCat.{u, v, w₁, w₂} C where
  obj := ccrsToFcpObj
  map := ccrsToFcpMor
  map_comp := ccrsToFcpMor_comp

/--
`FreeCoprodProdCat C` and `CoprodCovarRepSquaredCat C` are isomorphic categories.
-/
def fcpCcrsIso :
    FreeCoprodProdCat.{u, v, w₁, w₂} C ≅Cat CoprodCovarRepSquaredCat.{u, v, w₁, w₂} C where
  hom := fcpToCcrs C
  inv := ccrsToFcp C

/--
`FreeCoprodProdCat C` and `CoprodCovarRepSquaredCat C` are equivalent categories.
-/
def fcpCcrsEquiv :
    FreeCoprodProdCat.{u, v, w₁, w₂} C ≌ CoprodCovarRepSquaredCat.{u, v, w₁, w₂} C :=
  Cat.equivOfIso (fcpCcrsIso C)

end LayeredIsomorphism

end GebLean
