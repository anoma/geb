import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Pi.Basic
import Mathlib.CategoryTheory.Grothendieck
import Mathlib.CategoryTheory.Whiskering
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
    (f : X → Y) : FamilyCat C' Y ⥤ FamilyCat C' X where
  obj F x := F (f x)
  map φ x := φ (f x)

@[simp]
theorem familyMap_id.{u', v', w'} {C' : Type u'} [Category.{v'} C'] (X : Type w') :
    familyMap (C' := C') (𝟙 X) = 𝟙 (FamilyCat C' X) := rfl

@[simp]
theorem familyMap_comp.{u', v', w'} {C' : Type u'} [Category.{v'} C']
    {X Y Z : Type w'} (f : X → Y) (g : Y → Z) :
    familyMap (C' := C') (g ∘ f) = familyMap (C' := C') g ⋙ familyMap (C' := C') f :=
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
theorem familyPostcomp_natural (F : C ⥤ D) {X Y : Type u} (f : X → Y) :
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

variable (C : Type u) [Category.{v} C]

/--
The free coproduct completion of a category `C`. Objects are pairs `(X, F)`
where `X : Type (u+1)` and `F : X → C` is an `X`-indexed family of objects
from `C`. Morphisms `(X, F) → (Y, G)` consist of a function `f : X → Y` and a
family of morphisms `F(x) → G(f(x))`.

This is the contravariant Grothendieck construction applied to `familyFunctor`.
-/
@[simp]
def FreeCoprodCompletionCat : Cat.{max (u + 1) v, u + 2} :=
  Cat.of (GrothendieckContra' (familyFunctor.{u, v, u + 1} C))

/--
The free product completion of a category `C`. Objects are pairs `(X, F)`
where `X : Type (u+1)` and `F : X → C`. Morphisms `(X, F) → (Y, G)` consist
of a function `f : X → Y` and a family of morphisms `G(f(x)) → F(x)`.

This is the covariant Grothendieck construction applied to `familyFunctor`.
-/
@[simp]
def FreeProdCompletionCat : Cat.{max (u + 1) v, u + 2} :=
  Cat.of (Grothendieck (familyFunctor.{u, v, u + 1} C))

/--
The category of coproducts of covariant representables for `C`. Objects are
pairs `(X, F)` where `X : Type (u+1)` and `F : X → Cᵒᵖ'` is an `X`-indexed
family of objects from the opposite category.

This is the contravariant Grothendieck construction applied to `familyFunctor`
post-composed with oppositization.
-/
@[simp]
def CoprodCovarRepCat : Cat.{max (u + 1) v, u + 2} :=
  Cat.of (GrothendieckContra' (familyFunctor.{u, v, u + 1} C ⋙ Cat.opFunctor'))

/--
The category of products of contravariant representables for `C`. This is the
covariant Grothendieck construction applied to `familyFunctor` post-composed
with oppositization.
-/
@[simp]
def ProdContravarRepCat : Cat.{max (u + 1) v, u + 2} :=
  Cat.of (Grothendieck (familyFunctor.{u, v, u + 1} C ⋙ Cat.opFunctor'))

end GrothendieckCompletions

/-! ## Free coproduct completion helpers -/

section FreeCoprodCompletionHelpers

variable {C : Type u} [Category.{v} C]

/--
Construct an object of `FreeCoprodCompletionCat C` from an index type and
a family of objects.
-/
def fcObjMk {X : Type (u + 1)} (F : X → C) : FreeCoprodCompletionCat C :=
  ⟨X, F⟩

/--
Extract the index type from an object of `FreeCoprodCompletionCat C`.
-/
def fcIndex (x : FreeCoprodCompletionCat C) : Type (u + 1) := x.base

/--
Extract the family of objects from an object of `FreeCoprodCompletionCat C`.
-/
def fcFamily (x : FreeCoprodCompletionCat C) : fcIndex x → C := x.fiber

@[simp]
lemma fcObjMk_index {X : Type (u + 1)} (F : X → C) :
    fcIndex (fcObjMk F) = X := rfl

@[simp]
lemma fcObjMk_family {X : Type (u + 1)} (F : X → C) :
    fcFamily (fcObjMk F) = F := rfl

/--
Construct a morphism in `FreeCoprodCompletionCat C` from a reindexing function
and a family of fiber morphisms.

A morphism `(X, F) → (Y, G)` consists of:
- `reindex : X → Y` (function between index types)
- `fiberMor : ∀ x, F(x) → G(reindex(x))` (family of morphisms in `C`)
-/
def fcHomMk {x y : FreeCoprodCompletionCat C}
    (reindex : fcIndex x → fcIndex y)
    (fiberMor : ∀ i : fcIndex x, fcFamily x i ⟶ fcFamily y (reindex i)) :
    x ⟶ y :=
  ⟨reindex, fiberMor⟩

/--
Extract the reindexing function from a morphism in `FreeCoprodCompletionCat C`.
-/
def fcReindex {x y : FreeCoprodCompletionCat C} (f : x ⟶ y) :
    fcIndex x → fcIndex y :=
  f.base

/--
Extract the fiber morphism at index `i` from a morphism in
`FreeCoprodCompletionCat C`.
-/
def fcFiberMor {x y : FreeCoprodCompletionCat C} (f : x ⟶ y)
    (i : fcIndex x) : fcFamily x i ⟶ fcFamily y (fcReindex f i) :=
  f.fiber i

@[simp]
lemma fcHomMk_reindex {x y : FreeCoprodCompletionCat C}
    (reindex : fcIndex x → fcIndex y)
    (fiberMor : ∀ i : fcIndex x, fcFamily x i ⟶ fcFamily y (reindex i)) :
    fcReindex (fcHomMk reindex fiberMor) = reindex := rfl

@[simp]
lemma fcHomMk_fiberMor {x y : FreeCoprodCompletionCat C}
    (reindex : fcIndex x → fcIndex y)
    (fiberMor : ∀ i : fcIndex x, fcFamily x i ⟶ fcFamily y (reindex i))
    (i : fcIndex x) :
    fcFiberMor (fcHomMk reindex fiberMor) i = fiberMor i := rfl

@[ext (iff := false)]
lemma fcHom_ext {x y : FreeCoprodCompletionCat C} (f g : x ⟶ y)
    (hbase : f.base = g.base)
    (hfiber : f.fiber ≫ eqToHom (by rw [hbase]) = g.fiber) : f = g :=
  GrothendieckContra'.ext f g hbase hfiber

end FreeCoprodCompletionHelpers

/-! ## Free product completion helpers -/

section FreeProdCompletionHelpers

variable {C : Type u} [Category.{v} C]

/--
Construct an object of `FreeProdCompletionCat C` from an index type and
a family of objects.
-/
def fpObjMk {X : Type (u + 1)} (F : X → C) : FreeProdCompletionCat C :=
  ⟨X, F⟩

/--
Extract the index type from an object of `FreeProdCompletionCat C`.
-/
def fpIndex (x : FreeProdCompletionCat C) : Type (u + 1) := x.base

/--
Extract the family of objects from an object of `FreeProdCompletionCat C`.
-/
def fpFamily (x : FreeProdCompletionCat C) : fpIndex x → C := x.fiber

@[simp]
lemma fpObjMk_index {X : Type (u + 1)} (F : X → C) :
    fpIndex (fpObjMk F) = X := rfl

@[simp]
lemma fpObjMk_family {X : Type (u + 1)} (F : X → C) :
    fpFamily (fpObjMk F) = F := rfl

/--
Construct a morphism in `FreeProdCompletionCat C` from a reindexing function
and a family of fiber morphisms.

A morphism `(X, F) → (Y, G)` consists of:
- `reindex : Y → X` (function between index types, note: opposite direction)
- `fiberMor : ∀ j, G(reindex(j)) → F(j)` (family of morphisms in `C`,
  going from target family to source family)
-/
def fpHomMk {x y : FreeProdCompletionCat C}
    (reindex : fpIndex y → fpIndex x)
    (fiberMor : ∀ j : fpIndex y, fpFamily x (reindex j) ⟶ fpFamily y j) :
    x ⟶ y :=
  ⟨reindex, fiberMor⟩

/--
Extract the reindexing function from a morphism in `FreeProdCompletionCat C`.
Note: For a morphism `(X, F) → (Y, G)`, this is a function `Y → X`.
-/
def fpReindex {x y : FreeProdCompletionCat C} (f : x ⟶ y) :
    fpIndex y → fpIndex x :=
  f.base

/--
Extract the fiber morphism at index `j` from a morphism in
`FreeProdCompletionCat C`. For a morphism `f : (X, F) → (Y, G)`, this is
`F(reindex j) → G(j)`.
-/
def fpFiberMor {x y : FreeProdCompletionCat C} (f : x ⟶ y)
    (j : fpIndex y) : fpFamily x (fpReindex f j) ⟶ fpFamily y j :=
  f.fiber j

@[simp]
lemma fpHomMk_reindex {x y : FreeProdCompletionCat C}
    (reindex : fpIndex y → fpIndex x)
    (fiberMor : ∀ j : fpIndex y, fpFamily x (reindex j) ⟶ fpFamily y j) :
    fpReindex (fpHomMk reindex fiberMor) = reindex := rfl

@[simp]
lemma fpHomMk_fiberMor {x y : FreeProdCompletionCat C}
    (reindex : fpIndex y → fpIndex x)
    (fiberMor : ∀ j : fpIndex y, fpFamily x (reindex j) ⟶ fpFamily y j)
    (j : fpIndex y) :
    fpFiberMor (fpHomMk reindex fiberMor) j = fiberMor j := rfl

@[ext (iff := false)]
lemma fpHom_ext {x y : FreeProdCompletionCat C} (f g : x ⟶ y)
    (hbase : f.base = g.base)
    (hfiber : eqToHom (by rw [hbase]) ≫ f.fiber = g.fiber) : f = g :=
  Grothendieck.ext f g hbase hfiber

end FreeProdCompletionHelpers

/-! ## Coproduct of covariant representables helpers -/

section CoprodCovarRepHelpers

variable {C : Type u} [Category.{v} C]

/--
Construct an object of `CoprodCovarRepCat C` from an index type and
a family of objects from `C`. Internally, objects are stored as families
in `Cᵒᵖ'`, but this helper hides that detail.
-/
def ccrObjMk {X : Type (u + 1)} (F : X → C) : CoprodCovarRepCat C :=
  ⟨X, F⟩

/--
Extract the index type from an object of `CoprodCovarRepCat C`.
-/
def ccrIndex (x : CoprodCovarRepCat C) : Type (u + 1) := x.base

/--
Extract the family of objects from an object of `CoprodCovarRepCat C`.
Returns objects in `C` (not `Cᵒᵖ'`).
-/
def ccrFamily (x : CoprodCovarRepCat C) : ccrIndex x → C := x.fiber

@[simp]
lemma ccrObjMk_index {X : Type (u + 1)} (F : X → C) :
    ccrIndex (ccrObjMk F) = X := rfl

@[simp]
lemma ccrObjMk_family {X : Type (u + 1)} (F : X → C) :
    ccrFamily (ccrObjMk F) = F := rfl

/--
Construct a morphism in `CoprodCovarRepCat C` from a reindexing function
and a family of fiber morphisms.

A morphism `(X, F) → (Y, G)` consists of:
- `reindex : X → Y` (function between index types)
- `fiberMor : ∀ i, G(reindex(i)) → F(i)` (family of morphisms in `C`)

Note: The fiber morphisms go from target to source, which is opposite to
`FreeCoprodCompletionCat`.
-/
def ccrHomMk {x y : CoprodCovarRepCat C}
    (reindex : ccrIndex x → ccrIndex y)
    (fiberMor : ∀ i : ccrIndex x, ccrFamily y (reindex i) ⟶ ccrFamily x i) :
    x ⟶ y :=
  ⟨reindex, fiberMor⟩

/--
Extract the reindexing function from a morphism in `CoprodCovarRepCat C`.
-/
def ccrReindex {x y : CoprodCovarRepCat C} (f : x ⟶ y) :
    ccrIndex x → ccrIndex y :=
  f.base

/--
Extract the fiber morphism at index `i` from a morphism in
`CoprodCovarRepCat C`. For a morphism `f : (X, F) → (Y, G)`, this returns
`G(reindex i) → F(i)` in `C`.
-/
def ccrFiberMor {x y : CoprodCovarRepCat C} (f : x ⟶ y)
    (i : ccrIndex x) : ccrFamily y (ccrReindex f i) ⟶ ccrFamily x i :=
  f.fiber i

@[simp]
lemma ccrHomMk_reindex {x y : CoprodCovarRepCat C}
    (reindex : ccrIndex x → ccrIndex y)
    (fiberMor : ∀ i : ccrIndex x, ccrFamily y (reindex i) ⟶ ccrFamily x i) :
    ccrReindex (ccrHomMk reindex fiberMor) = reindex := rfl

@[simp]
lemma ccrHomMk_fiberMor {x y : CoprodCovarRepCat C}
    (reindex : ccrIndex x → ccrIndex y)
    (fiberMor : ∀ i : ccrIndex x, ccrFamily y (reindex i) ⟶ ccrFamily x i)
    (i : ccrIndex x) :
    ccrFiberMor (ccrHomMk reindex fiberMor) i = fiberMor i := rfl

@[ext (iff := false)]
lemma ccrHom_ext {x y : CoprodCovarRepCat C} (f g : x ⟶ y)
    (hbase : f.base = g.base)
    (hfiber : f.fiber ≫ eqToHom (by rw [hbase]) = g.fiber) : f = g :=
  GrothendieckContra'.ext f g hbase hfiber

end CoprodCovarRepHelpers

/-! ## Product of contravariant representables helpers -/

section ProdContravarRepHelpers

variable {C : Type u} [Category.{v} C]

/--
Construct an object of `ProdContravarRepCat C` from an index type and
a family of objects from `C`. Internally, objects are stored as families
in `Cᵒᵖ'`, but this helper hides that detail.
-/
def pcrObjMk {X : Type (u + 1)} (F : X → C) : ProdContravarRepCat C :=
  ⟨X, F⟩

/--
Extract the index type from an object of `ProdContravarRepCat C`.
-/
def pcrIndex (x : ProdContravarRepCat C) : Type (u + 1) := x.base

/--
Extract the family of objects from an object of `ProdContravarRepCat C`.
Returns objects in `C` (not `Cᵒᵖ'`).
-/
def pcrFamily (x : ProdContravarRepCat C) : pcrIndex x → C := x.fiber

@[simp]
lemma pcrObjMk_index {X : Type (u + 1)} (F : X → C) :
    pcrIndex (pcrObjMk F) = X := rfl

@[simp]
lemma pcrObjMk_family {X : Type (u + 1)} (F : X → C) :
    pcrFamily (pcrObjMk F) = F := rfl

/--
Construct a morphism in `ProdContravarRepCat C` from a reindexing function
and a family of fiber morphisms.

A morphism `(X, F) → (Y, G)` consists of:
- `reindex : Y → X` (function between index types, note: opposite direction)
- `fiberMor : ∀ j, G(j) → F(reindex(j))` (family of morphisms in `C`)

Note: The reindexing goes from target to source index, and the fiber morphisms
go from target family to source family.
-/
def pcrHomMk {x y : ProdContravarRepCat C}
    (reindex : pcrIndex y → pcrIndex x)
    (fiberMor : ∀ j : pcrIndex y, pcrFamily y j ⟶ pcrFamily x (reindex j)) :
    x ⟶ y :=
  ⟨reindex, fiberMor⟩

/--
Extract the reindexing function from a morphism in `ProdContravarRepCat C`.
Note: For a morphism `(X, F) → (Y, G)`, this is a function `Y → X`.
-/
def pcrReindex {x y : ProdContravarRepCat C} (f : x ⟶ y) :
    pcrIndex y → pcrIndex x :=
  f.base

/--
Extract the fiber morphism at index `j` from a morphism in
`ProdContravarRepCat C`. For a morphism `f : (X, F) → (Y, G)`, this returns
`G(j) → F(reindex j)` in `C`.
-/
def pcrFiberMor {x y : ProdContravarRepCat C} (f : x ⟶ y)
    (j : pcrIndex y) : pcrFamily y j ⟶ pcrFamily x (pcrReindex f j) :=
  f.fiber j

@[simp]
lemma pcrHomMk_reindex {x y : ProdContravarRepCat C}
    (reindex : pcrIndex y → pcrIndex x)
    (fiberMor : ∀ j : pcrIndex y, pcrFamily y j ⟶ pcrFamily x (reindex j)) :
    pcrReindex (pcrHomMk reindex fiberMor) = reindex := rfl

@[simp]
lemma pcrHomMk_fiberMor {x y : ProdContravarRepCat C}
    (reindex : pcrIndex y → pcrIndex x)
    (fiberMor : ∀ j : pcrIndex y, pcrFamily y j ⟶ pcrFamily x (reindex j))
    (j : pcrIndex y) :
    pcrFiberMor (pcrHomMk reindex fiberMor) j = fiberMor j := rfl

@[ext (iff := false)]
lemma pcrHom_ext {x y : ProdContravarRepCat C} (f g : x ⟶ y)
    (hbase : f.base = g.base)
    (hfiber : eqToHom (by rw [hbase]) ≫ f.fiber = g.fiber) : f = g :=
  Grothendieck.ext f g hbase hfiber

end ProdContravarRepHelpers

end GebLean
