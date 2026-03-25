import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Pi.Basic
import Mathlib.CategoryTheory.Grothendieck
import Mathlib.CategoryTheory.Whiskering
import Mathlib.CategoryTheory.Limits.Shapes.Products
import GebLean.Utilities.Category
import GebLean.Utilities.Opposites
import GebLean.Utilities.Grothendieck

/-!
# The family functor and completions

Given a category `C`, the family functor `familyFunctor' C : Typeᵒᵖ' ⥤ Cat` sends
a type `X` to the product category `∀ x : X, C`, which is the category of
`X`-indexed families of objects from `C`.

By applying the Grothendieck construction (covariant or contravariant) to
`familyFunctor'` or `familyFunctor' ⋙ opFunctor'` (which post-composes with
oppositization), we obtain four different completions of a category:

1. **Free coproduct completion** (`FreeCoprodCompletionCat`): The contravariant
   Grothendieck construction on `familyFunctor'`. Objects are pairs `(X, F)`
   where `X` is a type and `F : X → C`. Morphisms `(X, F) → (Y, G)` consist of
   `f : X → Y` and `F(x) → G(f(x))`. This freely adjoins coproducts to `C`.
   This category may also be viewed as the category of coproducts of
   contravariant representables (sometimes called "Dirichlet functors").

2. **Free product completion** (`FreeProdCompletionCat`): The covariant
   Grothendieck construction on `familyFunctor'`. Morphisms go in the opposite
   direction for the fiber component. This freely adjoins products to `C`.

3. **Coproducts of covariant representables** (`CoprodCovarRepCat'`): The
   contravariant Grothendieck construction on `familyFunctor' ⋙ opFunctor'`.
   Objects are `X`-indexed families of objects from `Cᵒᵖ'`. This produces
   the category coproducts of covariant representables, which are a form
   of polynomial functors (for some categories, including `Type`, these
   comprise _all_ polynomial functors).

4. **Products of contravariant representables** (`ProdContravarRepCat`): The
   covariant Grothendieck construction on `familyFunctor' ⋙ opFunctor'`.

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
def familyMap'.{u', v', w'} {C' : Type u'} [Category.{v'} C'] {X Y : Type w'}
    (f : X ⟶ Y) : FamilyCat C' Y ⥤ FamilyCat C' X where
  obj F x := F (f x)
  map φ x := φ (f x)

theorem familyMap_id'.{u', v', w'} {C' : Type u'} [Category.{v'} C'] (X : Type w') :
    familyMap' (C' := C') (𝟙 X) = 𝟭 (X → C') := rfl

@[simp]
theorem familyMap_comp'.{u', v', w'} {C' : Type u'} [Category.{v'} C']
    {X Y Z : Type w'} (f : X ⟶ Y) (g : Y ⟶ Z) :
    familyMap' (C' := C') (f ≫ g) = familyMap' (C' := C') g ⋙ familyMap' (C' := C') f :=
  rfl

/--
The family functor `familyFunctor' C : Typeᵒᵖ' ⥤ Cat` sends a type `X` to the
product category of `C` indexed by `X`. This is the functor whose Grothendieck
construction yields the free coproduct completion of `C`.

For a function `f : X → Y` (viewed as a morphism `X → Y` in `Typeᵒᵖ'`), the
induced functor is given by precomposition: a `Y`-indexed family is sent to
an `X`-indexed family by `(G : Y → C) ↦ (G ∘ f : X → C)`.
-/
@[simp]
def familyFunctor'.{u', v', w'} (C' : Type u') [Category.{v'} C'] :
    Type w'ᵒᵖ' ⥤ Cat.{max w' v', max u' w'} where
  obj X := FamilyCat C' X
  map f := (familyMap' (C' := C') f).toCatHom
  map_id X := Cat.Hom.ext (familyMap_id' X)
  map_comp _ _ := Cat.Hom.ext rfl

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
def familyPostcomp' (F : C ⥤ D) (X : Type u) : (∀ _ : X, C) ⥤ (∀ _ : X, D) where
  obj G x := F.obj (G x)
  map φ x := F.map (φ x)
  map_id G := by funext x; simp
  map_comp φ ψ := by funext x; simp

/--
`familyPostcomp'` respects the identity functor.
-/
@[simp]
theorem familyPostcomp_id' (X : Type u) :
    familyPostcomp' (𝟭 C) X = 𝟭 (∀ _ : X, C) := rfl

/--
`familyPostcomp'` respects functor composition.
-/
@[simp]
theorem familyPostcomp_comp' {E : Type u} [Category E] (F : C ⥤ D) (G : D ⥤ E)
    (X : Type u) : familyPostcomp' (F ⋙ G) X = familyPostcomp' F X ⋙ familyPostcomp' G X := rfl

/--
`familyPostcomp'` is natural in the indexing type: for any function `f : X → Y`,
the following square commutes:
```
  FamilyCat C Y --familyPostcomp' F Y--> FamilyCat D Y
       |                                     |
  familyMap' f                           familyMap' f
       |                                     |
       v                                     v
  FamilyCat C X --familyPostcomp' F X--> FamilyCat D X
```
-/
@[simp]
theorem familyPostcomp_natural' (F : C ⥤ D) {X Y : Type u} (f : X ⟶ Y) :
    familyMap' (C' := C) f ⋙ familyPostcomp' F X =
    familyPostcomp' F Y ⋙ familyMap' (C' := D) f := rfl

end FunctorialityInCategory

/-! ## The family bifunctor -/

section FamilyBifunctor

/--
A functor `F : C ⥤ D` induces a natural transformation from `familyFunctor' C`
to `familyFunctor' D`, with components given by `familyPostcomp' F X`.
-/
@[simp]
def familyNatTrans' {C D : Type u} [Category.{v} C] [Category.{v} D] (F : C ⥤ D) :
    familyFunctor' C ⟶ familyFunctor' D where
  app X := (familyPostcomp' F X).toCatHom
  naturality _ _ f := Cat.Hom.ext (familyPostcomp_natural' F f).symm

theorem familyNatTrans_id' (C : Type u) [Category.{v} C] :
    familyNatTrans' (𝟭 C) = 𝟙 (familyFunctor' C) := by
  ext X : 2
  exact Cat.Hom.ext rfl

theorem familyNatTrans_comp' {C D E : Type u} [Category.{v} C] [Category.{v} D]
    [Category.{v} E] (F : C ⥤ D) (G : D ⥤ E) :
    familyNatTrans' (F ⋙ G) = familyNatTrans' F ≫ familyNatTrans' G := by
  ext X : 2
  exact Cat.Hom.ext rfl

/--
The family bifunctor `familyBifunctor' : Cat ⥤ (Type uᵒᵖ' ⥤ Cat)` sends a
category `C` to the family functor `familyFunctor' C`, and a functor `F : C ⥤ D`
to the natural transformation `familyNatTrans' F`.
-/
@[simp]
def familyBifunctor' : Cat.{v, u} ⥤ (Type uᵒᵖ' ⥤ Cat.{max u v, u}) where
  obj C := familyFunctor' C
  map F := familyNatTrans' F.toFunctor
  map_id C := familyNatTrans_id' C
  map_comp F G := familyNatTrans_comp' F.toFunctor G.toFunctor

end FamilyBifunctor

/-! ## The opposite family bifunctor -/

section FamilyBifunctorOp

/--
The opposite family bifunctor `familyBifunctorOp' : Cat ⥤ (Type uᵒᵖ' ⥤ Cat)` is
`familyBifunctor'` post-composed with the oppositization functor `opFunctor'`.
It sends a category `C` to the functor that maps a type `X` to the opposite
of the family category `(∀ _ : X, C)ᵒᵖ'`.
-/
@[simp]
def familyBifunctorOp' : Cat.{v, u} ⥤ (Type uᵒᵖ' ⥤ Cat.{max u v, u}) :=
  familyBifunctor' ⋙ (Functor.whiskeringRight _ _ _).obj Cat.opFunctor'

end FamilyBifunctorOp

/-! ## Family functor and bifunctor (using mathlib `op`)

The following definitions parallel the primed (`'`) versions
above but use mathlib's `Opposite` (`ᵒᵖ`) instead of
`CategoryOp'` (`ᵒᵖ'`).  The index type universe `w` is
independent of the category universe `u`, generalizing
`familyBifunctor'` which forces `w = u`.
-/

section FamilyOp

universe w

/--
For a morphism `f : X ⟶ Y` in `(Type w)ᵒᵖ` (wrapping a
function `Y.unop → X.unop`), the induced functor
precomposes an `X.unop`-indexed family with `f.unop`.
-/
@[simp]
def familyMap {C : Type u} [Category.{v} C]
    {X Y : (Type w)ᵒᵖ}
    (f : X ⟶ Y) :
    FamilyCat C X.unop ⥤ FamilyCat C Y.unop where
  obj F y := F (f.unop y)
  map φ y := φ (f.unop y)

theorem familyMap_id {C : Type u} [Category.{v} C]
    (X : (Type w)ᵒᵖ) :
    familyMap (C := C) (𝟙 X) =
      𝟭 (X.unop → C) := rfl

@[simp]
theorem familyMap_comp {C : Type u} [Category.{v} C]
    {X Y Z : (Type w)ᵒᵖ}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    familyMap (C := C) (f ≫ g) =
      familyMap f ⋙ familyMap g := rfl

/--
The family functor `familyFunctor C : (Type w)ᵒᵖ ⥤ Cat`
sends a type `X` to the product category `X → C`.  Uses
mathlib's `ᵒᵖ`; the index type universe `w` is
independent of the category universe `u`.
-/
@[simp]
def familyFunctor (C : Type u) [Category.{v} C] :
    (Type w)ᵒᵖ ⥤ Cat.{max w v, max u w} where
  obj X := FamilyCat C X.unop
  map f := (familyMap (C := C) f).toCatHom
  map_id X := Cat.Hom.ext (familyMap_id X)
  map_comp _ _ := Cat.Hom.ext rfl

/--
Postcomposition of families with a functor `F : C ⥤ D`.
The index type `X` can live in any universe `w`,
independent of the category universes.
-/
@[simp]
def familyPostcomp {C : Type u} [Category.{v} C]
    {D : Type u} [Category.{v} D]
    (F : C ⥤ D) (X : Type w) :
    (X → C) ⥤ (X → D) where
  obj G x := F.obj (G x)
  map φ x := F.map (φ x)
  map_id G := by ext x; exact F.map_id (G x)
  map_comp φ ψ := by ext x; exact F.map_comp _ _

lemma familyPostcomp_natural
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {X Y : (Type w)ᵒᵖ} (f : X ⟶ Y) :
    familyMap f ⋙ familyPostcomp F Y.unop =
      familyPostcomp F X.unop ⋙ familyMap f := rfl

/--
A functor `F : C ⥤ D` induces a natural transformation
`familyFunctor C ⟶ familyFunctor D` via postcomposition.
-/
@[simp]
def familyNatTrans
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) :
    familyFunctor.{u, v, w} C ⟶
      familyFunctor.{u, v, w} D where
  app X := (familyPostcomp F X.unop).toCatHom
  naturality _ _ f := Cat.Hom.ext
    (familyPostcomp_natural F f).symm

theorem familyNatTrans_id
    (C : Type u) [Category.{v} C] :
    familyNatTrans.{u, v, w} (𝟭 C) =
      𝟙 (familyFunctor C) := by
  ext X : 2
  exact Cat.Hom.ext rfl

theorem familyNatTrans_comp
    {C D E : Type u} [Category.{v} C]
    [Category.{v} D] [Category.{v} E]
    (F : C ⥤ D) (G : D ⥤ E) :
    familyNatTrans.{u, v, w} (F ⋙ G) =
      familyNatTrans F ≫ familyNatTrans G := by
  ext X : 2
  exact Cat.Hom.ext rfl

/--
The family bifunctor `familyBifunctor : Cat ⥤ ((Type w)ᵒᵖ ⥤ Cat)`.
Sends a category `C` to `familyFunctor C` and a functor
`F` to `familyNatTrans F`.  Uses mathlib's `ᵒᵖ`; the
index type universe `w` is independent of the category
universe.
-/
@[simp]
def familyBifunctor :
    Cat.{v, u} ⥤
      ((Type w)ᵒᵖ ⥤ Cat.{max w v, max u w}) where
  obj C := familyFunctor C
  map F := familyNatTrans F.toFunctor
  map_id C := familyNatTrans_id C
  map_comp F G :=
    familyNatTrans_comp F.toFunctor G.toFunctor

/--
The free product completion as a functor `Cat ⥤ Cat`.
Sends a category `C` to `Grothendieck (familyFunctor C)`.
Defined as `familyBifunctor ⋙ grothendieckFunctor`.
-/
def freeProdCompletionFunctor :
    Cat.{v, u} ⥤ Cat.{max w v, max (w + 1) u} :=
  let G : ((Type w)ᵒᵖ ⥤ Cat.{max w v, max u w}) ⥤
      Cat.{max w v, max (w + 1) u} :=
    grothendieckFunctor ((Type w)ᵒᵖ)
  familyBifunctor ⋙ G

/--
The free product completion of `C` with index types in
universe `w`.  Objects are pairs `(op X, F)` where
`X : Type w` and `F : X → C`.  Morphisms go forward on
both positions and directions.
-/
def FreeProdCompletion (C : Type u) [Category.{v} C] :
    Cat.{max w v, max (w + 1) u} :=
  freeProdCompletionFunctor.{u, v, w}.obj (Cat.of C)

/--
The coproduct-of-covariant-representables functor
`Cat ⥤ Cat`.  Defined as `freeProdCompletionFunctor`
post-composed with `Cat.opFunctor`.
-/
def coprodCovarRepFunctor :
    Cat.{v, u} ⥤ Cat.{max w v, max (w + 1) u} :=
  freeProdCompletionFunctor.{u, v, w} ⋙
    Cat.opFunctor

/--
The category of coproducts of covariant representables
for `C`.

A morphism from `(X₁, F₁)` to `(X₂, F₂)` consists of
a reindexing `r : X₁ → X₂` (forward on positions) and
fiber morphisms `∀ x₁, F₂(r(x₁)) ⟶ F₁(x₁)` (backward
on directions).

Defined as `coprodCovarRepFunctor` applied to `C`.
-/
def CoprodCovarRepCat
    (C : Type u) [Category.{v} C] :
    Cat.{max w v, max (w + 1) u} :=
  coprodCovarRepFunctor.{u, v, w}.obj (Cat.of C)

/-! ### Accessors for CoprodCovarRepCat -/

variable {C : Type u} [Category.{v} C]

/--
The index type (positions) of an object of
`CoprodCovarRepCat C`.
-/
def ccrNewIndex
    (P : CoprodCovarRepCat.{u, v, w} C) :
    Type w :=
  P.unop.base.unop

/--
The family (directions) of an object of
`CoprodCovarRepCat C`.
-/
def ccrNewFamily
    (P : CoprodCovarRepCat.{u, v, w} C) :
    ccrNewIndex P → C :=
  P.unop.fiber

/--
Evaluation of a polynomial at an object `A`.
-/
def ccrNewEval
    (P : CoprodCovarRepCat.{u, v, w} C)
    (A : C) :=
  Σ i : ccrNewIndex P, (ccrNewFamily P i ⟶ A)

/--
Functorial action of evaluation on morphisms
(postcomposition).
-/
def ccrNewEvalMap
    {P : CoprodCovarRepCat.{u, v, w} C}
    {A B : C} (f : A ⟶ B) :
    ccrNewEval P A → ccrNewEval P B :=
  fun ⟨i, h⟩ => ⟨i, h ≫ f⟩

@[simp]
lemma ccrNewEvalMap_id
    {P : CoprodCovarRepCat.{u, v, w} C}
    {A : C} :
    ccrNewEvalMap (𝟙 A) =
      (id : ccrNewEval P A → ccrNewEval P A) := by
  funext ⟨i, h⟩; simp [ccrNewEvalMap]

@[simp]
lemma ccrNewEvalMap_comp
    {P : CoprodCovarRepCat.{u, v, w} C}
    {A B D : C} (f : A ⟶ B) (g : B ⟶ D) :
    ccrNewEvalMap (f ≫ g) =
      ccrNewEvalMap g ∘
        ccrNewEvalMap (P := P) f := by
  funext ⟨i, h⟩; simp [ccrNewEvalMap, Category.assoc]

/--
The reindexing function from a morphism in
`CoprodCovarRepCat C`.
-/
def ccrNewReindex
    {P Q : CoprodCovarRepCat.{u, v, w} C}
    (f : P ⟶ Q) :
    ccrNewIndex P → ccrNewIndex Q :=
  f.unop.base.unop

/--
The index projection as a functor from
`CoprodCovarRepCat C` to `Type w`.  Sends an object
to its index type and a morphism to its reindexing
function.  Both functor laws hold definitionally.
-/
def ccrNewIndexFunctor
    (C : Type u) [Category.{v} C] :
    CoprodCovarRepCat.{u, v, w} C ⥤ Type w where
  obj P := ccrNewIndex P
  map f := ccrNewReindex f

/--
The fiber morphism from a morphism in
`CoprodCovarRepCat C`.
-/
def ccrNewFiberMor
    {P Q : CoprodCovarRepCat.{u, v, w} C}
    (f : P ⟶ Q) (i : ccrNewIndex P) :
    ccrNewFamily Q (ccrNewReindex f i) ⟶
      ccrNewFamily P i :=
  f.unop.fiber i

@[simp]
lemma ccrNewFiberMor_comp
    {P Q R : CoprodCovarRepCat.{u, v, w} C}
    (f : P ⟶ Q) (g : Q ⟶ R)
    (i : ccrNewIndex P) :
    ccrNewFiberMor (f ≫ g) i =
      ccrNewFiberMor g (ccrNewReindex f i) ≫
        ccrNewFiberMor f i := by
  simp only [ccrNewFiberMor, ccrNewReindex]
  change (g.unop ≫ f.unop).fiber i = _
  rw [Grothendieck.comp_fiber]
  simp [familyFunctor, familyMap]

private lemma ccrNewFiberMor_eqToHom_comp
    {Q R : CoprodCovarRepCat.{u, v, w} C}
    (g : Q ⟶ R) {i j : ccrNewIndex Q}
    (h : i = j)
    {k : ccrNewIndex R}
    (hk1 : ccrNewReindex g i = k)
    (hk2 : ccrNewReindex g j = k) :
    eqToHom (congrArg (ccrNewFamily R)
        hk1.symm) ≫
      ccrNewFiberMor g i =
    eqToHom (congrArg (ccrNewFamily R)
        hk2.symm) ≫
      ccrNewFiberMor g j ≫
      eqToHom (congrArg (ccrNewFamily Q)
        h.symm) := by
  subst h
  simp

/--
The family (directions) extraction as a functor from
the category of elements of `ccrNewIndexFunctor C` to
`Cᵒᵖ`.  Sends `(P, i)` to `Opposite.op (ccrNewFamily P i)`
and a morphism `(f, proof)` to the opposite of the
fiber morphism `ccrNewFiberMor f i`.
-/
def ccrNewFamilyFunctor
    (C : Type u) [Category.{v} C] :
    (ccrNewIndexFunctor.{u, v, w} C).Elements ⥤
      Cᵒᵖ where
  obj e := Opposite.op (ccrNewFamily e.fst e.snd)
  map {e₁ e₂} f :=
    (eqToHom (congrArg (ccrNewFamily e₂.fst)
        f.property.symm) ≫
      ccrNewFiberMor f.val e₁.snd).op
  map_id e := by
    apply Quiver.Hom.unop_inj
    simp [ccrNewFiberMor]
    rfl
  map_comp {e₁ e₂ e₃} f g := by
    apply Quiver.Hom.unop_inj
    simp only [Quiver.Hom.unop_op, unop_comp]
    have hfp : ccrNewReindex f.val e₁.snd =
        e₂.snd := f.property
    have hgp : ccrNewReindex g.val e₂.snd =
        e₃.snd := g.property
    have hcomp : ccrNewReindex g.val
        (ccrNewReindex f.val e₁.snd) =
        e₃.snd := by rw [hfp]; exact hgp
    simp only [CategoryOfElements.comp_val]
    rw [ccrNewFiberMor_comp]
    simp only [Category.assoc]
    have comm := ccrNewFiberMor_eqToHom_comp g.val
      hfp hcomp hgp
    rw [show (f ≫ g).property = hcomp from
      rfl, show g.property = hgp from rfl,
      show f.property = hfp from rfl]
    conv_lhs =>
      rw [← Category.assoc (eqToHom _)
        (ccrNewFiberMor g.val _)
        (ccrNewFiberMor f.val _)]
      rw [comm]
    simp only [Category.assoc]

/--
Evaluate a morphism in `CoprodCovarRepCat C` on an
evaluation element.
-/
def ccrNewMorphEval
    {P Q : CoprodCovarRepCat.{u, v, w} C}
    (f : P ⟶ Q) (A : C) :
    ccrNewEval P A → ccrNewEval Q A :=
  fun ⟨i, η⟩ =>
    ⟨ccrNewReindex f i, ccrNewFiberMor f i ≫ η⟩

@[simp]
lemma ccrNewMorphEval_id
    (P : CoprodCovarRepCat.{u, v, w} C) (A : C) :
    ccrNewMorphEval (𝟙 P) A = id := by
  funext ⟨i, η⟩
  exact Sigma.ext rfl
    (heq_of_eq (Category.id_comp η))

@[simp]
lemma ccrNewMorphEval_comp
    {P Q R : CoprodCovarRepCat.{u, v, w} C}
    (f : P ⟶ Q) (g : Q ⟶ R) (A : C) :
    ccrNewMorphEval (f ≫ g) A =
      ccrNewMorphEval g A ∘
        ccrNewMorphEval f A := by
  funext ⟨i, η⟩
  exact Sigma.ext rfl
    (heq_of_eq (by
      simp [ccrNewMorphEval, ccrNewFiberMor_comp,
        Category.assoc]))

/--
Evaluation of a fixed polynomial `P` as a functor
`C ⥤ Type _`.  Sends `A` to `ccrNewEval P A` and a
morphism `f` to `ccrNewEvalMap f`.
-/
def ccrNewEvalFunctor
    (P : CoprodCovarRepCat.{u, v, w} C) :
    C ⥤ Type (max w v) where
  obj A := ccrNewEval P A
  map f := ccrNewEvalMap f
  map_id _ := ccrNewEvalMap_id
  map_comp f g := ccrNewEvalMap_comp f g

/--
The evaluation functor varying `P`: sends a polynomial
`P : CoprodCovarRepCat C` to its evaluation functor
`ccrNewEvalFunctor P`, and a morphism `f : P ⟶ Q` to
the natural transformation induced by `ccrNewMorphEval`.
-/
def ccrNewEvalCatFunctor
    (C : Type u) [Category.{v} C] :
    CoprodCovarRepCat.{u, v, w} C ⥤
      (C ⥤ Type (max w v)) where
  obj P := ccrNewEvalFunctor P
  map f :=
    { app := fun A => ccrNewMorphEval f A
      naturality := fun A B g => by
        ext ⟨i, η⟩
        simp [ccrNewEvalFunctor, ccrNewMorphEval,
          ccrNewEvalMap, Category.assoc] }
  map_id P := by
    ext A ⟨i, η⟩
    simp [ccrNewEvalFunctor, ccrNewMorphEval_id]
  map_comp f g := by
    ext A ⟨i, η⟩
    simp [ccrNewEvalFunctor, ccrNewMorphEval_comp]

end FamilyOp

/-! ## Grothendieck completions -/

section GrothendieckCompletions

universe w

variable (C : Type u) [Category.{v} C]

/--
The free coproduct completion of a category `C` with index types in universe
`w`. Objects are pairs `(X, F)` where `X : Type w` and `F : X → C` is an
`X`-indexed family of objects from `C`. Morphisms `(X, F) → (Y, G)` consist of
a function `f : X → Y` and a family of morphisms `F(x) → G(f(x))`.

This is the contravariant Grothendieck construction applied to `familyFunctor'`.
-/
@[simp]
def FreeCoprodCompletionCat.{u', v', w'} (C' : Type u') [Category.{v'} C'] :
    Cat.{max w' v', max (w' + 1) u' w'} :=
  Cat.of (GrothendieckContra'.{w' + 1, w', max u' w', max w' v'}
    (familyFunctor'.{u', v', w'} C'))

/--
The free product completion of a category `C`. Objects are pairs `(X, F)`
where `X : Type (u+1)` and `F : X → C`. Morphisms `(X, F) → (Y, G)` consist
of a function `f : X → Y` and a family of morphisms `G(f(x)) → F(x)`.

This is the covariant Grothendieck construction applied to `familyFunctor'`.
-/
@[simp]
def FreeProdCompletionCat.{u', v', w'} (C' : Type u') [Category.{v'} C'] :
    Cat.{max w' v', max (w' + 1) u' w'} :=
  Cat.of (Grothendieck.{w' + 1, w', max u' w', max w' v'}
    (familyFunctor'.{u', v', w'} C'))

/--
The family functor post-composed with oppositization. This functor
`familyFunctorOp' C : Type^op ⥤ Cat` sends a type `X` to the opposite of
the product category `(X → C)^op`.

This is the functor whose contravariant Grothendieck construction yields
`CoprodCovarRepCat' C` and whose covariant Grothendieck construction yields
`ProdContravarRepCat C`.
-/
def familyFunctorOp'.{u', v', w'} (C' : Type u') [Category.{v'} C'] :
    Type w'ᵒᵖ' ⥤ Cat.{max w' v', max u' w'} :=
  familyFunctor'.{u', v', w'} C' ⋙ Cat.opFunctor'

@[simp]
lemma familyFunctorOp_eq.{u', v', w'} (C' : Type u') [Category.{v'} C'] :
    familyFunctorOp'.{u', v', w'} C' = familyFunctor'.{u', v', w'} C' ⋙ Cat.opFunctor' :=
  rfl

/--
The category of coproducts of covariant representables for `C`. Objects are
pairs `(X, F)` where `X : Type (u+1)` and `F : X → Cᵒᵖ'` is an `X`-indexed
family of objects from the opposite category.

This is the contravariant Grothendieck construction applied to `familyFunctor'`
post-composed with oppositization (i.e., `familyFunctorOp'`).
-/
@[simp]
def CoprodCovarRepCat'.{u', v', w'} (C' : Type u') [Category.{v'} C'] :
    Cat.{max w' v', max (w' + 1) u' w'} :=
  Cat.of (GrothendieckContra'.{w' + 1, w', max u' w', max w' v'}
    (familyFunctor'.{u', v', w'} C' ⋙ Cat.opFunctor'))

/--
The category of products of contravariant representables for `C`. This is the
covariant Grothendieck construction applied to `familyFunctor'` post-composed
with oppositization (i.e., `familyFunctorOp'`).
-/
@[simp]
def ProdContravarRepCat.{u', v', w'} (C' : Type u') [Category.{v'} C'] :
    Cat.{max w' v', max (w' + 1) u' w'} :=
  Cat.of (Grothendieck.{w' + 1, w', max u' w', max w' v'}
    (familyFunctor'.{u', v', w'} C' ⋙ Cat.opFunctor'))

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

/--
The identity morphism in `FreeCoprodCompletionCat C` expressed purely in terms
of the underlying category. The reindexing is `id` and each fiber morphism is `𝟙`.
-/
@[simp]
lemma fcId_mk (x : FreeCoprodCompletionCat.{u, v, w} C) :
    𝟙 x = fcHomMk id (fun i => 𝟙 (fcFamily x i)) := rfl

/--
Composition in `FreeCoprodCompletionCat C` expressed purely in terms of the
underlying category. The reindexing is function composition `g ∘ f`, and
the fiber morphism at index `i` is `f.fiber i ≫ g.fiber (f.reindex i)`.
-/
@[simp]
lemma fcComp_mk {x y z : FreeCoprodCompletionCat.{u, v, w} C}
    (f : x ⟶ y) (g : y ⟶ z) :
    f ≫ g = fcHomMk (fcReindex g ∘ fcReindex f)
      (fun i => fcFiberMor f i ≫ fcFiberMor g (fcReindex f i)) := by
  refine GrothendieckContra'.ext _ _ rfl ?_
  simp only [fcHomMk, eqToHom_refl, Category.comp_id]
  funext i
  exact fcComp_fiberMor f g i

end FreeCoprodCompletionHelpers

/-! ## Coproduct Data Typeclass

The `CoprodData` typeclass provides coproduct structure (object and injections)
without requiring the universal property. This separates computation from proof:

- **Computation**: Definitions using `CoprodData` are computable because they
  only require the coproduct object and injection morphisms as data.
- **Proof**: Proofs about coproducts can separately require `HasCoproducts` to
  access the universal property (uniqueness, factorization).

For categories like `Type` and `Over X` for `X : Type`, we provide a
computable instance using direct sigma type construction.
-/

section CoprodData

universe w

/--
Coproduct data for a category: provides the coproduct object and injection
morphisms without requiring the universal property.

This allows definitions using coproducts to be computable when a computable
instance is available (e.g., for `Over X`), while proofs can separately use
`HasCoproducts` for the universal property.
-/
class CoprodData (D : Type*) [Category D] where
  /-- The coproduct object for a family `F : I → D`. -/
  coprod : {I : Type w} → (I → D) → D
  /-- The injection morphism from `F i` into the coproduct. -/
  ι : {I : Type w} → (F : I → D) → (i : I) → F i ⟶ coprod F

variable {D : Type*} [Category D] [CoprodData.{w} D]

/-- Notation for the coproduct object from `CoprodData`. -/
notation "∐' " F:60 => CoprodData.coprod F

/-- The injection into the coproduct from component `i`. -/
abbrev CoprodData.inj {I : Type w} (F : I → D) (i : I) : F i ⟶ ∐' F :=
  CoprodData.ι F i

end CoprodData

/-! ### CoprodData instance for Over X

For `Over X`, coproducts are sigma types: the coproduct of `(A_i, h_i)` is
`(Σ i, A_i, copairing)`. This instance is computable.
-/

section CoprodDataOver

universe w

variable {X : Type w}

/--
Computable coproduct data for `Over X`. The coproduct of a family of arrows
over `X` is the sigma type of their domains with the copairing morphism.
-/
instance : CoprodData.{w} (Over X) where
  coprod F := Over.mk (fun (p : Σ i, (F i).left) => (F p.1).hom p.2)
  ι _ i := Over.homMk (fun a => ⟨i, a⟩) rfl

/--
The coproduct object in `Over X` is the sigma type of the domains.
-/
lemma coprodData_over_left {I : Type w} (F : I → Over X) :
    (∐' F).left = Σ i, (F i).left := rfl

/--
The coproduct morphism in `Over X` is the copairing of the family morphisms.
-/
lemma coprodData_over_hom {I : Type w} (F : I → Over X) (p : (∐' F).left) :
    (∐' F).hom p = (F p.1).hom p.2 := rfl

/--
The injection into the coproduct in `Over X` pairs the index with the element.
-/
lemma coprodData_over_ι_left {I : Type w} (F : I → Over X) (i : I) (a : (F i).left) :
    (CoprodData.inj F i).left a = ⟨i, a⟩ := rfl

def overCoprodMap {I : Type w} {F G : I → Over X}
    (α : ∀ i, F i ⟶ G i) :
    ∐' F ⟶ ∐' G :=
  Over.homMk
    (fun ⟨i, x⟩ => ⟨i, (α i).left x⟩)
    (by ext ⟨i, x⟩; exact congrFun (Over.w (α i)) x)

@[simp]
lemma overCoprodMap_id {I : Type w}
    (F : I → Over X) :
    overCoprodMap (fun i => 𝟙 (F i)) = 𝟙 (∐' F) :=
  rfl

@[simp]
lemma overCoprodMap_comp {I : Type w}
    {F G H : I → Over X}
    (α : ∀ i, F i ⟶ G i) (β : ∀ i, G i ⟶ H i) :
    overCoprodMap (fun i => α i ≫ β i) =
      overCoprodMap α ≫ overCoprodMap β := by
  apply Over.OverMorphism.ext
  ext ⟨i, x⟩
  rfl

end CoprodDataOver

/-! ## Product Data Typeclass

The `ProdData` typeclass provides product structure (object and projections)
without requiring the universal property. This is the dual of `CoprodData`.
-/

section ProdData

universe w

/--
Product data for a category: provides the product object and projection
morphisms without requiring the universal property.

This is the dual of `CoprodData`. It allows definitions using products to be
computable when a computable instance is available.
-/
class ProdData (D : Type*) [Category D] where
  /-- The product object for a family `F : I → D`. -/
  prod : {I : Type w} → (I → D) → D
  /-- The projection morphism from the product to `F i`. -/
  π : {I : Type w} → (F : I → D) → (i : I) → prod F ⟶ F i

variable {D : Type*} [Category D] [ProdData.{w} D]

/-- Notation for the product object from `ProdData`. -/
notation "∏' " F:60 => ProdData.prod F

/-- The projection from the product to component `i`. -/
abbrev ProdData.proj {I : Type w} (F : I → D) (i : I) : ∏' F ⟶ F i :=
  ProdData.π F i

end ProdData

/-! ### ProdData instance for Over X

For `Over X`, products are fiber products: the product of `(A_i, h_i)` is
the subtype of `∀ i, A_i` where all morphisms agree on their target in `X`.
This is the wide pullback over `X`. This instance is computable.
-/

section ProdDataOver

universe w

variable {X : Type w}

/--
The underlying type of the product in `Over X`: pairs `(x, f)` where `x : X`
and `f : ∀ i, A_i` such that all `h_i (f i) = x`.
-/
def overProdLeft {I : Type w} (F : I → Over X) : Type w :=
  { p : (Σ _ : X, ∀ i, (F i).left) // ∀ i, (F i).hom (p.2 i) = p.1 }

/--
The morphism to `X` for the product: projection to the common target.
-/
def overProdHom {I : Type w} (F : I → Over X) : overProdLeft F → X :=
  fun p => p.val.1

/--
Computable product data for `Over X`. The product of a family of arrows
over `X` is the fiber product: pairs `(x, f)` where `x : X` and `f : ∀ i, A_i`
such that all `h_i (f i) = x`.
-/
instance : ProdData.{w} (Over X) where
  prod F := Over.mk (overProdHom F)
  π _ i := Over.homMk (fun p => p.val.2 i) (funext fun p => p.property i)

/--
The product object in `Over X` is the fiber product over X.
-/
lemma prodData_over_left {I : Type w} (F : I → Over X) :
    (∏' F).left = overProdLeft F := rfl

/--
The projection from the product in `Over X` extracts the i-th component.
-/
lemma prodData_over_π_left {I : Type w} (F : I → Over X) (i : I)
    (p : (∏' F).left) : (ProdData.proj F i).left p = p.val.2 i := rfl

end ProdDataOver

/-! ### ProdData for (Over X)^op'

Products in `(Over X)ᵒᵖ'` are coproducts in `Over X`.
-/

section ProdDataOverOp

universe w

variable {X : Type w}

instance overOpProdData : ProdData.{w} ((Over X)ᵒᵖ') where
  prod F := CoprodData.coprod (D := Over X) F
  π F i := CoprodData.inj (D := Over X) F i

end ProdDataOverOp


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
    dsimp only [familyFunctor', familyMap', fcFiberMor]
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
  dsimp only [familyFunctor', familyMap']
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

/--
`CoprodData` instance for `FreeCoprodCompletionCat C` using the coproduct
construction.
-/
instance fcCoprodData : CoprodData.{w} (FreeCoprodCompletionCat.{u, v, w} C) where
  coprod := fcCoprodObj
  ι := fcCoprodι

end FreeCoprodCompletionCoproducts

/-! ## Products in FreeCoprodCompletionCat (distributed over coproducts)

When the underlying category `C` has `ProdData`, the free coproduct completion
also has products, with products distributing over coproducts.

Given a family `F : I → FreeCoprodCompletionCat C` where each `F i = (X_i, G_i)`:
- The product has index type `∀ i, X_i` (choosing an index from each component)
- For each `p : ∀ i, X_i`, the object is `∏' (fun i => G_i (p i))` in `C`

The projection `π_j : prod F ⟶ F j` has:
- Base: `p ↦ p j` (extract the j-th component)
- Fiber at `p`: `∏' (fun i => G_i (p i)) ⟶ G_j (p j)` via `ProdData.proj`
-/

section FreeCoprodCompletionProducts

universe w

variable {C : Type u} [Category.{v} C] [ProdData.{w} C]

/--
The product object in `FreeCoprodCompletionCat C` for a family indexed by `I`,
when `C` has `ProdData`. Products distribute over coproducts.
-/
def fcProdObj {I : Type w} (F : I → FreeCoprodCompletionCat.{u, v, w} C) :
    FreeCoprodCompletionCat.{u, v, w} C :=
  fcObjMk (fun (p : ∀ i, fcIndex (F i)) => ∏' (fun i => fcFamily (F i) (p i)))

/--
The projection morphism from the product to component `j` in
`FreeCoprodCompletionCat C`. The base extracts the j-th index, and the fiber
uses the product projection in `C`.
-/
def fcProdπ {I : Type w} (F : I → FreeCoprodCompletionCat.{u, v, w} C) (j : I) :
    fcProdObj F ⟶ F j :=
  fcHomMk (fun p => p j) (fun p => ProdData.proj (fun i => fcFamily (F i) (p i)) j)

/--
`ProdData` instance for `FreeCoprodCompletionCat C` when `C` has `ProdData`.
Products distribute over coproducts.
-/
instance fcProdData : ProdData.{w} (FreeCoprodCompletionCat.{u, v, w} C) where
  prod := fcProdObj
  π := fcProdπ

end FreeCoprodCompletionProducts

/-! ## Distributivity: Products distribute over coproducts

In `FreeCoprodCompletionCat C`, products distribute over coproducts. Given:
- `A : FreeCoprodCompletionCat C` (a single object)
- `F : I → FreeCoprodCompletionCat C` (a family of objects)

The distributivity isomorphism is:
  `A × (∐ᵢ Fᵢ) ≅ ∐ᵢ (A × Fᵢ)`

Concretely:
- LHS index: `fcIndex A × (Σ i, fcIndex (F i))` ≅ `Σ (a, i, x) : ...`
- RHS index: `Σ i, fcIndex A × fcIndex (F i)` ≅ `Σ (i, a, x) : ...`

The isomorphism swaps the order of `a` and `i`.
-/

section DistributivityIndex

universe w

variable {C : Type u} [Category.{v} C]

/--
The index type for `A × (∐ᵢ Fᵢ)` in `FreeCoprodCompletionCat C`.
This is `fcIndex A × (Σ i, fcIndex (F i))`.
-/
def distLhsIndex (A : FreeCoprodCompletionCat.{u, v, w} C)
    {I : Type w} (F : I → FreeCoprodCompletionCat.{u, v, w} C) : Type w :=
  fcIndex A × (Σ i, fcIndex (F i))

/--
The index type for `∐ᵢ (A × Fᵢ)` in `FreeCoprodCompletionCat C`.
This is `Σ i, fcIndex A × fcIndex (F i)`.
-/
def distRhsIndex (A : FreeCoprodCompletionCat.{u, v, w} C)
    {I : Type w} (F : I → FreeCoprodCompletionCat.{u, v, w} C) : Type w :=
  Σ i, fcIndex A × fcIndex (F i)

/--
Convert from LHS index to RHS index: `(a, ⟨i, x⟩) ↦ ⟨i, (a, x)⟩`.
-/
def distIndexToRhs {A : FreeCoprodCompletionCat.{u, v, w} C}
    {I : Type w} {F : I → FreeCoprodCompletionCat.{u, v, w} C}
    (p : distLhsIndex A F) : distRhsIndex A F :=
  ⟨p.2.1, (p.1, p.2.2)⟩

/--
Convert from RHS index to LHS index: `⟨i, (a, x)⟩ ↦ (a, ⟨i, x⟩)`.
-/
def distIndexToLhs {A : FreeCoprodCompletionCat.{u, v, w} C}
    {I : Type w} {F : I → FreeCoprodCompletionCat.{u, v, w} C}
    (p : distRhsIndex A F) : distLhsIndex A F :=
  (p.2.1, ⟨p.1, p.2.2⟩)

@[simp]
lemma distIndexToRhs_toLhs {A : FreeCoprodCompletionCat.{u, v, w} C}
    {I : Type w} {F : I → FreeCoprodCompletionCat.{u, v, w} C}
    (p : distRhsIndex A F) : distIndexToRhs (distIndexToLhs p) = p := rfl

@[simp]
lemma distIndexToLhs_toRhs {A : FreeCoprodCompletionCat.{u, v, w} C}
    {I : Type w} {F : I → FreeCoprodCompletionCat.{u, v, w} C}
    (p : distLhsIndex A F) : distIndexToLhs (distIndexToRhs p) = p := rfl

end DistributivityIndex

/-! ## Distributivity: Products distribute over coproducts

In `FreeCoprodCompletionCat C`, products distribute over coproducts. Given:
- `A : FreeCoprodCompletionCat C` (a single object)
- `F : I → FreeCoprodCompletionCat C` (a family of objects)

The distributivity isomorphism is:
  `A × (∐ᵢ Fᵢ) ≅ ∐ᵢ (A × Fᵢ)`

The isomorphism swaps the order of indices: `(a, ⟨i, x⟩) ↔ ⟨i, (a, x)⟩`.
-/

section Distributivity

universe w

variable {C : Type u} [Category.{v} C] [ProdData.{w} C]

/--
The family value at an LHS index.
At `(a, ⟨i, x⟩)`, this is `∏' [fcFamily A a, fcFamily (F i) x]` in `C`.
Uses `ULift.{w} Bool` to lift the index to universe `w`.
-/
def distLhsFamily (A : FreeCoprodCompletionCat.{u, v, w} C)
    {I : Type w} (F : I → FreeCoprodCompletionCat.{u, v, w} C)
    (p : distLhsIndex A F) : C :=
  ∏' (fun b : ULift.{w} Bool =>
    if b.down then fcFamily A p.1 else fcFamily (F p.2.1) p.2.2)

/--
The family value at an RHS index.
At `⟨i, (a, x)⟩`, this is `∏' [fcFamily A a, fcFamily (F i) x]` in `C`.
Uses `ULift.{w} Bool` to lift the index to universe `w`.
-/
def distRhsFamily (A : FreeCoprodCompletionCat.{u, v, w} C)
    {I : Type w} (F : I → FreeCoprodCompletionCat.{u, v, w} C)
    (p : distRhsIndex A F) : C :=
  ∏' (fun b : ULift.{w} Bool =>
    if b.down then fcFamily A p.2.1 else fcFamily (F p.1) p.2.2)

/--
The LHS and RHS families agree at corresponding indices.
-/
lemma distFamily_eq (A : FreeCoprodCompletionCat.{u, v, w} C)
    {I : Type w} (F : I → FreeCoprodCompletionCat.{u, v, w} C)
    (p : distLhsIndex A F) :
    distLhsFamily A F p = distRhsFamily A F (distIndexToRhs p) := rfl

/--
The LHS object: `A × (∐ᵢ Fᵢ)` as a binary product.
-/
def distLhsObj (A : FreeCoprodCompletionCat.{u, v, w} C)
    {I : Type w} (F : I → FreeCoprodCompletionCat.{u, v, w} C) :
    FreeCoprodCompletionCat.{u, v, w} C :=
  fcObjMk (distLhsFamily A F)

/--
The RHS object: `∐ᵢ (A × Fᵢ)`.
-/
def distRhsObj (A : FreeCoprodCompletionCat.{u, v, w} C)
    {I : Type w} (F : I → FreeCoprodCompletionCat.{u, v, w} C) :
    FreeCoprodCompletionCat.{u, v, w} C :=
  fcObjMk (distRhsFamily A F)

/--
The forward direction of distributivity: `A × (∐ᵢ Fᵢ) → ∐ᵢ (A × Fᵢ)`.
Reindexes from `(a, ⟨i, x⟩)` to `⟨i, (a, x)⟩` with identity fiber morphisms.
-/
def distToRhs (A : FreeCoprodCompletionCat.{u, v, w} C)
    {I : Type w} (F : I → FreeCoprodCompletionCat.{u, v, w} C) :
    distLhsObj A F ⟶ distRhsObj A F :=
  fcHomMk distIndexToRhs (fun _ => 𝟙 _)

/--
The backward direction of distributivity: `∐ᵢ (A × Fᵢ) → A × (∐ᵢ Fᵢ)`.
Reindexes from `⟨i, (a, x)⟩` to `(a, ⟨i, x⟩)` with identity fiber morphisms.
-/
def distToLhs (A : FreeCoprodCompletionCat.{u, v, w} C)
    {I : Type w} (F : I → FreeCoprodCompletionCat.{u, v, w} C) :
    distRhsObj A F ⟶ distLhsObj A F :=
  fcHomMk distIndexToLhs (fun _ => 𝟙 _)

/--
The distributivity morphisms compose to the identity (forward then back).
-/
@[simp]
lemma distToRhs_toRhs (A : FreeCoprodCompletionCat.{u, v, w} C)
    {I : Type w} (F : I → FreeCoprodCompletionCat.{u, v, w} C) :
    distToRhs A F ≫ distToLhs A F = 𝟙 (distLhsObj A F) := by
  refine GrothendieckContra'.ext _ _ ?_ ?_
  · rfl
  · simp only [eqToHom_refl, Category.comp_id]
    funext p
    change (GrothendieckContra'.comp (distToRhs A F) (distToLhs A F)).fiber p =
      (GrothendieckContra'.id (distLhsObj A F)).fiber p
    unfold GrothendieckContra'.comp GrothendieckContra'.id
    simp only [distToRhs, distToLhs, fcHomMk, eqToHom_refl, Category.comp_id]
    dsimp only [familyFunctor', familyMap']
    change (𝟙 (fcFamily (distLhsObj A F) p) ≫
      𝟙 (fcFamily (distRhsObj A F) (distIndexToRhs p))) = _
    simp only [Category.id_comp]
    rfl

/--
The distributivity morphisms compose to the identity (back then forward).
-/
@[simp]
lemma distToLhs_toLhs (A : FreeCoprodCompletionCat.{u, v, w} C)
    {I : Type w} (F : I → FreeCoprodCompletionCat.{u, v, w} C) :
    distToLhs A F ≫ distToRhs A F = 𝟙 (distRhsObj A F) := by
  refine GrothendieckContra'.ext _ _ ?_ ?_
  · rfl
  · simp only [eqToHom_refl, Category.comp_id]
    funext p
    change (GrothendieckContra'.comp (distToLhs A F) (distToRhs A F)).fiber p =
      (GrothendieckContra'.id (distRhsObj A F)).fiber p
    unfold GrothendieckContra'.comp GrothendieckContra'.id
    simp only [distToRhs, distToLhs, fcHomMk, eqToHom_refl, Category.comp_id]
    dsimp only [familyFunctor', familyMap']
    change (𝟙 (fcFamily (distRhsObj A F) p) ≫
      𝟙 (fcFamily (distLhsObj A F) (distIndexToLhs p))) = _
    simp only [Category.id_comp]
    rfl

/--
The distributivity isomorphism: `A × (∐ᵢ Fᵢ) ≅ ∐ᵢ (A × Fᵢ)`.
-/
def distIso (A : FreeCoprodCompletionCat.{u, v, w} C)
    {I : Type w} (F : I → FreeCoprodCompletionCat.{u, v, w} C) :
    distLhsObj A F ≅ distRhsObj A F where
  hom := distToRhs A F
  inv := distToLhs A F
  hom_inv_id := distToRhs_toRhs A F
  inv_hom_id := distToLhs_toLhs A F

end Distributivity

/-! ## Products in CoprodCovarRepCat' (distributed over coproducts)

Since `CoprodCovarRepCat' C = FreeCoprodCompletionCat (C^op')`, products in
`CoprodCovarRepCat'` follow when `C^op'` has `ProdData`.
-/

section CoprodCovarRepProducts

universe w

variable {C : Type u} [Category.{v} C] [ProdData.{w} Cᵒᵖ']

/--
`ProdData` instance for `CoprodCovarRepCat' C` when `C^op'` has `ProdData`.
-/
instance ccrProdData : ProdData.{w} (CoprodCovarRepCat'.{u, v, w} C) where
  prod F := fcProdObj (C := Cᵒᵖ') F
  π F j := fcProdπ (C := Cᵒᵖ') F j

end CoprodCovarRepProducts

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
Construct an object of `CoprodCovarRepCat' C` from an index type and
a family of objects from `C`. Internally, objects are stored as families
in `Cᵒᵖ'`, but this helper hides that detail.
-/
def ccrObjMk {X : Type w} (F : X → C) : CoprodCovarRepCat'.{u, v, w} C :=
  ⟨X, F⟩

/--
Extract the index type from an object of `CoprodCovarRepCat' C`.
-/
def ccrIndex (x : CoprodCovarRepCat'.{u, v, w} C) : Type w := x.base

/--
Extract the family of objects from an object of `CoprodCovarRepCat' C`.
Returns objects in `C` (not `Cᵒᵖ'`).
-/
def ccrFamily (x : CoprodCovarRepCat'.{u, v, w} C) : ccrIndex x → C := x.fiber

@[simp]
lemma ccrObjMk_index {X : Type w} (F : X → C) :
    ccrIndex (ccrObjMk F) = X := rfl

@[simp]
lemma ccrObjMk_family {X : Type w} (F : X → C) :
    ccrFamily (ccrObjMk F) = F := rfl

/--
Construct a morphism in `CoprodCovarRepCat' C` from a reindexing function
and a family of fiber morphisms.

A morphism `(X, F) → (Y, G)` consists of:
- `reindex : X ⟶ Y` (morphism in `Type`)
- `fiberMor : ∀ i, G(reindex(i)) ⟶ F(i)` (family of morphisms in `C`)

Note: The fiber morphisms go from target to source, which is opposite to
`FreeCoprodCompletionCat`.
-/
@[reducible] def ccrHomMk
    {x y : CoprodCovarRepCat'.{u, v, w} C}
    (reindex : ccrIndex x ⟶ ccrIndex y)
    (fiberMor : ∀ i : ccrIndex x,
      ccrFamily y (reindex i) ⟶
        ccrFamily x i) :
    x ⟶ y :=
  ⟨reindex, fiberMor⟩

/--
Extract the reindexing function from a morphism in `CoprodCovarRepCat' C`.
-/
def ccrReindex {x y : CoprodCovarRepCat'.{u, v, w} C} (f : x ⟶ y) :
    ccrIndex x ⟶ ccrIndex y :=
  f.base

/--
Extract the fiber morphism at index `i` from a morphism in
`CoprodCovarRepCat' C`. For a morphism `f : (X, F) → (Y, G)`, this returns
`G(reindex i) ⟶ F(i)` in `C`.
-/
def ccrFiberMor {x y : CoprodCovarRepCat'.{u, v, w} C} (f : x ⟶ y)
    (i : ccrIndex x) : ccrFamily y (ccrReindex f i) ⟶ ccrFamily x i :=
  f.fiber i

@[simp]
lemma ccrHomMk_reindex {x y : CoprodCovarRepCat'.{u, v, w} C}
    (reindex : ccrIndex x ⟶ ccrIndex y)
    (fiberMor : ∀ i : ccrIndex x, ccrFamily y (reindex i) ⟶ ccrFamily x i) :
    ccrReindex (ccrHomMk reindex fiberMor) = reindex := rfl

@[simp]
lemma ccrHomMk_fiberMor {x y : CoprodCovarRepCat'.{u, v, w} C}
    (reindex : ccrIndex x ⟶ ccrIndex y)
    (fiberMor : ∀ i : ccrIndex x, ccrFamily y (reindex i) ⟶ ccrFamily x i)
    (i : ccrIndex x) :
    ccrFiberMor (ccrHomMk reindex fiberMor) i = fiberMor i := rfl

@[ext (iff := false)]
lemma ccrHom_ext {x y : CoprodCovarRepCat'.{u, v, w} C} (f g : x ⟶ y)
    (hbase : f.base = g.base)
    (hfiber : f.fiber ≫ eqToHom (by rw [hbase]) = g.fiber) : f = g :=
  GrothendieckContra'.ext f g hbase hfiber

/--
The identity morphism in `CoprodCovarRepCat' C` has identity reindexing.
-/
@[simp]
lemma ccrId_reindex (x : CoprodCovarRepCat'.{u, v, w} C) :
    ccrReindex (𝟙 x) = 𝟙 (ccrIndex x) := rfl

/--
The identity morphism in `CoprodCovarRepCat' C` has identity fiber morphisms.
-/
@[simp]
lemma ccrId_fiberMor (x : CoprodCovarRepCat'.{u, v, w} C) (i : ccrIndex x) :
    ccrFiberMor (𝟙 x) i = 𝟙 (ccrFamily x i) := rfl

/--
Composition in `CoprodCovarRepCat' C`: the reindexing composes covariantly.
-/
@[simp]
lemma ccrComp_reindex {x y z : CoprodCovarRepCat'.{u, v, w} C}
    (f : x ⟶ y) (g : y ⟶ z) :
    ccrReindex (f ≫ g) = ccrReindex f ≫ ccrReindex g := rfl

/--
Composition in `CoprodCovarRepCat' C`: the fiber morphisms compose
contravariantly. For `f : x ⟶ y` and `g : y ⟶ z`, the fiber morphism at
index `i` is `ccrFiberMor g (ccrReindex f i) ≫ ccrFiberMor f i`.
-/
@[simp]
lemma ccrComp_fiberMor {x y z : CoprodCovarRepCat'.{u, v, w} C}
    (f : x ⟶ y) (g : y ⟶ z) (i : ccrIndex x) :
    ccrFiberMor (f ≫ g) i = ccrFiberMor g (ccrReindex f i) ≫ ccrFiberMor f i := by
  unfold ccrFiberMor ccrReindex
  change (GrothendieckContra'.comp f g).fiber i = g.fiber (f.base i) ≫ f.fiber i
  unfold GrothendieckContra'.comp
  simp only [eqToHom_refl, Category.comp_id]
  rfl

/--
The identity morphism in `CoprodCovarRepCat' C` expressed purely in terms of
the underlying category. The reindexing is `id` and each fiber morphism is `𝟙`.
-/
@[simp]
lemma ccrId_mk (x : CoprodCovarRepCat'.{u, v, w} C) :
    𝟙 x = ccrHomMk id (fun i => 𝟙 (ccrFamily x i)) := rfl

/--
Composition in `CoprodCovarRepCat' C` expressed purely in terms of the
underlying category. The reindexing is function composition `g ∘ f`, and
the fiber morphism at index `i` is `g.fiber (f.reindex i) ≫ f.fiber i`.
-/
@[simp]
lemma ccrComp_mk {x y z : CoprodCovarRepCat'.{u, v, w} C}
    (f : x ⟶ y) (g : y ⟶ z) :
    f ≫ g = ccrHomMk (ccrReindex g ∘ ccrReindex f)
      (fun i => ccrFiberMor g (ccrReindex f i) ≫ ccrFiberMor f i) := by
  refine GrothendieckContra'.ext _ _ rfl ?_
  simp only [ccrHomMk, eqToHom_refl, Category.comp_id]
  funext i
  exact ccrComp_fiberMor f g i

/-! ### Evaluation of Free Coproduct Completion (Presheaf)

An object of `FreeCoprodCompletionCat C` is a coproduct
of contravariant representables.  Given `P = (I, F : I → C)`
and `A : C`, the evaluation is:
  `P(A) = Σ i : I, Hom_C(A, F(i))`

This is contravariant in `A`: a morphism `f : A → B`
induces a map `P(B) → P(A)` by precomposition.
-/

def fcEval
    (P : FreeCoprodCompletionCat.{u, v, w} C)
    (A : C) : Type _ :=
  Σ i : fcIndex P, (A ⟶ fcFamily P i)

def fcEvalIndex
    {P : FreeCoprodCompletionCat.{u, v, w} C}
    {A : C} (x : fcEval P A) : fcIndex P :=
  x.1

def fcEvalMor
    {P : FreeCoprodCompletionCat.{u, v, w} C}
    {A : C}
    (x : fcEval P A) :
    A ⟶ fcFamily P (fcEvalIndex x) :=
  x.2

def fcEvalMk
    {P : FreeCoprodCompletionCat.{u, v, w} C}
    {A : C}
    (i : fcIndex P)
    (f : A ⟶ fcFamily P i) : fcEval P A :=
  ⟨i, f⟩

@[simp]
lemma fcEvalMk_index
    {P : FreeCoprodCompletionCat.{u, v, w} C}
    {A : C}
    (i : fcIndex P)
    (f : A ⟶ fcFamily P i) :
    fcEvalIndex (fcEvalMk i f) = i := rfl

@[simp]
lemma fcEvalMk_mor
    {P : FreeCoprodCompletionCat.{u, v, w} C}
    {A : C}
    (i : fcIndex P)
    (f : A ⟶ fcFamily P i) :
    fcEvalMor (fcEvalMk i f) = f := rfl

lemma fcEval_ext
    {P : FreeCoprodCompletionCat.{u, v, w} C}
    {A : C}
    (x y : fcEval P A)
    (hIdx : fcEvalIndex x = fcEvalIndex y)
    (hMor : fcEvalMor x =
      hIdx ▸ fcEvalMor y) :
    x = y := by
  obtain ⟨i, f⟩ := x
  obtain ⟨j, g⟩ := y
  simp only [fcEvalIndex, fcEvalMor]
    at hIdx hMor
  cases hIdx
  suffices hMor' : f = g by
    subst hMor'; rfl
  exact hMor

@[simp]
lemma fcEvalMk_eta
    {P : FreeCoprodCompletionCat.{u, v, w} C}
    {A : C} (x : fcEval P A) :
    fcEvalMk (fcEvalIndex x)
      (fcEvalMor x) = x :=
  rfl

def fcEvalMap
    {P : FreeCoprodCompletionCat.{u, v, w} C}
    {A B : C} (f : A ⟶ B) :
    fcEval P B → fcEval P A :=
  fun ⟨i, g⟩ => ⟨i, f ≫ g⟩

@[simp]
lemma fcEvalMap_index
    {P : FreeCoprodCompletionCat.{u, v, w} C}
    {A B : C} (f : A ⟶ B)
    (x : fcEval P B) :
    fcEvalIndex (fcEvalMap f x) =
      fcEvalIndex x :=
  rfl

@[simp]
lemma fcEvalMap_mor
    {P : FreeCoprodCompletionCat.{u, v, w} C}
    {A B : C} (f : A ⟶ B)
    (x : fcEval P B) :
    fcEvalMor (fcEvalMap f x) =
      f ≫ fcEvalMor x :=
  rfl

@[simp]
lemma fcEvalMap_id
    {P : FreeCoprodCompletionCat.{u, v, w} C}
    {A : C} :
    fcEvalMap (𝟙 A) =
      id (α := fcEval P A) := by
  funext ⟨i, f⟩
  simp only [fcEvalMap, Category.id_comp,
    id_eq]

@[simp]
lemma fcEvalMap_comp
    (P : FreeCoprodCompletionCat.{u, v, w} C)
    {A B C' : C} (f : A ⟶ B) (g : B ⟶ C') :
    fcEvalMap (P := P) f ∘
      fcEvalMap (P := P) g =
      fcEvalMap (P := P) (f ≫ g) := by
  funext ⟨i, h⟩
  simp only [Function.comp_apply,
    fcEvalMap, Category.assoc]

def fcToFunctor
    (P : FreeCoprodCompletionCat.{u, v, w} C) :
    Cᵒᵖ ⥤ Type _ where
  obj A := fcEval P A.unop
  map {_ _} f := fcEvalMap f.unop
  map_id _ := fcEvalMap_id
  map_comp {_ _ _} f g :=
    (fcEvalMap_comp P g.unop f.unop).symm

end CoprodCovarRepHelpers

/-! ## Equivalence between CoprodCovarRepCat' and FreeCoprodCompletionCat

`CoprodCovarRepCat' C` is equivalent to `FreeCoprodCompletionCat (C^op')`.
This follows from the isomorphism `FamilyCat (C^op') X ≅ (FamilyCat C X)^op'`.
-/

section CoprodCovarRepEquiv

universe w

variable {C : Type u} [Category.{v} C]

def ccrFcOpEq :
  CoprodCovarRepCat'.{u, v, w} C = FreeCoprodCompletionCat.{u, v, w} Cᵒᵖ' :=
    rfl

open CategoryTheory.Limits CategoryTheory.Adjunction in
instance hasCoproducts_CoprodCovarRepCat :
  HasCoproducts.{w} (CoprodCovarRepCat'.{u, v, w} C) :=
    hasCoproducts_of_colimit_cofans
      (fcCofan (C := Cᵒᵖ'))
      (fcIsColimitCofan (C := Cᵒᵖ'))

/--
`CoprodData` instance for `CoprodCovarRepCat' C`, inherited from
`FreeCoprodCompletionCat (C^op')`.
-/
instance ccrCoprodData : CoprodData.{w} (CoprodCovarRepCat'.{u, v, w} C) where
  coprod F := fcCoprodObj (C := Cᵒᵖ') F
  ι F i := fcCoprodι (C := Cᵒᵖ') F i

/-! ### Isomorphism between CoprodCovarRepCat' (Cᵒᵖ) and FreeCoprodCompletionCat C

We establish that `CoprodCovarRepCat' (Cᵒᵖ) ≅Cat FreeCoprodCompletionCat C`.

This allows working with polynomial functors on C by instead working with
`FreeCoprodCompletionCat Cᵒᵖ` (contravariant Grothendieck construction on
presheaves), which integrates with mathlib's presheaf machinery.
-/

/--
Functor from `CoprodCovarRepCat' (Cᵒᵖ)` to `FreeCoprodCompletionCat C`.

Objects: `(X, F : X → Cᵒᵖ)` maps to `(X, fun x => (F x).unop : X → C)`.
Morphisms: The fiber morphisms transpose via unop.
-/
def ccrOpToFc : CoprodCovarRepCat'.{u, v, w} Cᵒᵖ ⥤ FreeCoprodCompletionCat.{u, v, w} C where
  obj P := fcObjMk (fun x => (ccrFamily P x).unop)
  map {P Q} f := fcHomMk (ccrReindex f)
    (fun i => (ccrFiberMor f i).unop)
  map_id P := by
    refine fcHom_ext _ _ rfl ?_
    simp only [eqToHom_refl, Category.comp_id]
    funext i
    simp only [fcHomMk, ccrId_fiberMor]
    rfl
  map_comp {P Q R} f g := by
    simp only [fcComp_mk]
    congr 1
    funext i
    dsimp only [fcHomMk, fcFiberMor, fcReindex]
    simp only [ccrComp_fiberMor, unop_comp]

/--
Functor from `FreeCoprodCompletionCat C` to `CoprodCovarRepCat' (Cᵒᵖ)`.

Objects: `(X, G : X → C)` maps to `(X, fun x => op (G x) : X → Cᵒᵖ)`.
Morphisms: The fiber morphisms transpose via op.
-/
def fcToCcrOp : FreeCoprodCompletionCat.{u, v, w} C ⥤ CoprodCovarRepCat'.{u, v, w} Cᵒᵖ where
  obj P := ccrObjMk (fun x => Opposite.op (fcFamily P x))
  map {P Q} f := ccrHomMk (fcReindex f)
    (fun i => (fcFiberMor f i).op)
  map_id P := by
    refine ccrHom_ext _ _ rfl ?_
    simp only [eqToHom_refl, Category.comp_id]
    funext i
    simp only [fcId_fiberMor]
    rfl
  map_comp {P Q R} f g := by
    simp only [ccrComp_mk]
    congr 1
    funext i
    dsimp only [ccrHomMk, ccrFiberMor, ccrReindex]
    simp only [fcComp_fiberMor, op_comp]

@[simp]
lemma ccrOpToFc_fcToCcrOp : ccrOpToFc ⋙ fcToCcrOp = 𝟭 (CoprodCovarRepCat'.{u, v, w} Cᵒᵖ) := by
  fapply _root_.CategoryTheory.Functor.ext
  · intro P
    simp only [Functor.comp_obj, Functor.id_obj, ccrOpToFc, fcToCcrOp]
    simp only [ccrObjMk, fcObjMk, fcIndex, ccrIndex, fcFamily, ccrFamily]
    simp only [Opposite.op_unop]
    cases P
    rfl
  · intro P Q f
    cases P
    cases Q
    simp only [Functor.comp_map, Functor.id_map, ccrOpToFc, fcToCcrOp, eqToHom_refl,
      Category.id_comp, Category.comp_id]
    refine ccrHom_ext _ _ rfl ?_
    funext i
    simp only [eqToHom_refl, Category.comp_id]
    dsimp only [ccrHomMk, ccrFiberMor, ccrReindex, fcHomMk, fcFiberMor, fcReindex]
    simp only [Quiver.Hom.op_unop]

@[simp]
lemma fcToCcrOp_ccrOpToFc : fcToCcrOp ⋙ ccrOpToFc = 𝟭 (FreeCoprodCompletionCat.{u, v, w} C) := by
  fapply _root_.CategoryTheory.Functor.ext
  · intro P
    simp only [Functor.comp_obj, Functor.id_obj, fcToCcrOp, ccrOpToFc]
    simp only [fcObjMk, ccrObjMk, ccrIndex, fcIndex, ccrFamily, fcFamily]
    cases P
    rfl
  · intro P Q f
    cases P
    cases Q
    simp only [Functor.comp_map, Functor.id_map, fcToCcrOp, ccrOpToFc, eqToHom_refl,
      Category.id_comp, Category.comp_id]
    refine fcHom_ext _ _ rfl ?_
    funext i
    simp only [eqToHom_refl, Category.comp_id]
    dsimp only [fcHomMk, fcFiberMor, fcReindex, ccrHomMk, ccrFiberMor, ccrReindex]
    simp only [Quiver.Hom.unop_op]

/--
Categorical isomorphism between `CoprodCovarRepCat' (Cᵒᵖ)` and `FreeCoprodCompletionCat C`.

This isomorphism allows polynomial functor constructions on C to be transported
to/from the free coproduct completion, which has direct access to mathlib's
presheaf machinery via the contravariant Grothendieck construction.
-/
def ccrOpIsoCat : CoprodCovarRepCat'.{u, v, w} Cᵒᵖ ≅Cat FreeCoprodCompletionCat.{u, v, w} C where
  hom := ccrOpToFc.toCatHom
  inv := fcToCcrOp.toCatHom
  hom_inv_id := Cat.Hom.ext ccrOpToFc_fcToCcrOp
  inv_hom_id := Cat.Hom.ext fcToCcrOp_ccrOpToFc

/--
Categorical equivalence between `CoprodCovarRepCat' (Cᵒᵖ)` and `FreeCoprodCompletionCat C`,
derived from the categorical isomorphism.
-/
def ccrOpEquivFc : CoprodCovarRepCat'.{u, v, w} Cᵒᵖ ≌ FreeCoprodCompletionCat.{u, v, w} C :=
  Cat.equivOfIso ccrOpIsoCat

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

/--
Composition in `ProdContravarRepCat C` expressed purely in terms of the
underlying category. The reindexing is `g.reindex ≫ f.reindex` and the fiber
morphism at index `k` is `g.fiber k ≫ f.fiber (g.reindex k)`.
-/
@[simp]
lemma pcrComp_mk {x y z : ProdContravarRepCat.{u, v, w} C}
    (f : x ⟶ y) (g : y ⟶ z) :
    f ≫ g = pcrHomMk (pcrReindex g ≫ pcrReindex f)
      (fun k => pcrFiberMor g k ≫ pcrFiberMor f (pcrReindex g k)) := by
  refine Grothendieck.ext _ _ rfl ?_
  simp only [pcrHomMk, eqToHom_refl, Category.id_comp]
  funext k
  exact pcrComp_fiberMor f g k

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
  CoprodCovarRepCat'.{max (w₂' + 1) u' w₂', max w₂' v', w₁'}
    (CoprodCovarRepCat'.{u', v', w₂'} C')

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
  hom := (fcpToCcrs C).toCatHom
  inv := (ccrsToFcp C).toCatHom

/--
`FreeCoprodProdCat C` and `CoprodCovarRepSquaredCat C` are equivalent categories.
-/
def fcpCcrsEquiv :
    FreeCoprodProdCat.{u, v, w₁, w₂} C ≌ CoprodCovarRepSquaredCat.{u, v, w₁, w₂} C :=
  Cat.equivOfIso (fcpCcrsIso C)

end LayeredIsomorphism

/-! ## Products in FreeProdCompletionCat

The free product completion has all small products. Given a family
`F : I → FreeProdCompletionCat C`, the product is:
- Index type: `Σ i, fpIndex (F i)`
- Family: `fun ⟨i, x⟩ => fpFamily (F i) x`

This has the same formula as coproducts in `FreeCoprodCompletionCat C`.
-/

section FreeProdCompletionProducts

open Limits

universe w

variable {C : Type u} [Category.{v} C]

/--
The product object in `FreeProdCompletionCat C` for a family indexed by `I`.
Both `I` and the index types of the family elements must be at universe `w`.
-/
def fpProdObj {I : Type w} (F : I → FreeProdCompletionCat.{u, v, w} C) :
    FreeProdCompletionCat.{u, v, w} C :=
  fpObjMk (fun (p : Σ i, fpIndex (F i)) => fpFamily (F p.1) p.2)

/--
The projection morphism from the product to component `i`.
-/
def fpProdπ {I : Type w} (F : I → FreeProdCompletionCat.{u, v, w} C) (i : I) :
    fpProdObj F ⟶ F i :=
  fpHomMk (fun x => ⟨i, x⟩) (fun _ => 𝟙 _)

/--
The universal morphism to the product given morphisms to each component.
-/
def fpProdLift {I : Type w} {F : I → FreeProdCompletionCat.{u, v, w} C}
    {P : FreeProdCompletionCat.{u, v, w} C}
    (f : ∀ i, P ⟶ F i) : P ⟶ fpProdObj F :=
  fpHomMk
    (fun ⟨i, x⟩ => fpReindex (f i) x)
    (fun ⟨i, x⟩ => fpFiberMor (f i) x)

@[simp]
lemma fpProdLift_π {I : Type w} {F : I → FreeProdCompletionCat.{u, v, w} C}
    {P : FreeProdCompletionCat.{u, v, w} C}
    (f : ∀ i, P ⟶ F i) (i : I) :
    fpProdLift f ≫ fpProdπ F i = f i := by
  refine Grothendieck.ext _ _ ?_ ?_
  · -- w_base: show base components are equal
    rfl
  · -- w_fiber: show fiber components equal with eqToHom
    simp only [eqToHom_refl, Category.id_comp]
    funext x
    change (Grothendieck.comp (fpProdLift f) (fpProdπ F i)).fiber x = (f i).fiber x
    unfold Grothendieck.comp
    simp only [fpProdLift, fpProdπ, fpHomMk, eqToHom_refl, Category.id_comp]
    change (fpFiberMor (f i) x ≫ 𝟙 (fpFamily (F i) x)) = (f i).fiber x
    simp only [Category.comp_id]
    rfl

/-- From composition g ≫ fpProdπ F i, the fiber at x simplifies to g.fiber ⟨i, x⟩. -/
private lemma fpProdπ_comp_fiber_eq {I : Type w}
    {F : I → FreeProdCompletionCat.{u, v, w} C}
    {P : FreeProdCompletionCat.{u, v, w} C}
    (g : P ⟶ fpProdObj F) (i : I) (x : fpIndex (F i)) :
    (g ≫ fpProdπ F i).fiber x = g.fiber ⟨i, x⟩ := by
  change (Grothendieck.comp g (fpProdπ F i)).fiber x = g.fiber ⟨i, x⟩
  unfold Grothendieck.comp
  simp only [fpProdπ, fpHomMk, eqToHom_refl, Category.id_comp]
  dsimp only [familyFunctor', familyMap']
  -- Goal: ((fun x ↦ g.fiber ⟨i, x⟩) ≫ fun x ↦ 𝟙 _) x = g.fiber ⟨i, x⟩
  -- Pi category composition: (α ≫ β) x = α x ≫ β x
  change (g.fiber ⟨i, x⟩ ≫ 𝟙 _) = g.fiber ⟨i, x⟩
  simp only [Category.comp_id]

lemma fpProdLift_unique {I : Type w} {F : I → FreeProdCompletionCat.{u, v, w} C}
    {P : FreeProdCompletionCat.{u, v, w} C}
    (f : ∀ i, P ⟶ F i) (g : P ⟶ fpProdObj F)
    (hg : ∀ i, g ≫ fpProdπ F i = f i) : g = fpProdLift f := by
  -- First establish base equality: g.base = (fpProdLift f).base
  have hbase : g.base = (fpProdLift f).base := by
    funext ⟨i, x⟩
    -- From hg i: g ≫ fpProdπ F i = f i, extract base equality at x
    have hi := congrArg Grothendieck.Hom.base (hg i)
    change (Grothendieck.comp g (fpProdπ F i)).base = (f i).base at hi
    unfold Grothendieck.comp at hi
    simp only [fpProdπ, fpHomMk, fpProdLift, fpReindex] at hi ⊢
    exact congrFun hi x
  refine Grothendieck.ext _ _ hbase ?_
  funext ⟨i, x⟩
  have hfibx := congrFun (Grothendieck.congr (hg i)) x
  rw [fpProdπ_comp_fiber_eq g i x] at hfibx
  simp only [fpProdLift, fpHomMk, fpFiberMor]
  simp_all

open CategoryTheory.Limits in
/-- The fan for products in the free product completion. -/
def fpFan {I : Type w} (F : I → FreeProdCompletionCat.{u, v, w} C) :
    Fan F :=
  Fan.mk (fpProdObj F) (fpProdπ F)

open CategoryTheory.Limits in
/-- The product fan is a limit in the free product completion. -/
def fpIsLimitFan {I : Type w} (F : I → FreeProdCompletionCat.{u, v, w} C) :
    IsLimit (fpFan F) :=
  mkFanLimit (fpFan F)
    (fun t => fpProdLift t.proj)
    (fun t i => fpProdLift_π t.proj i)
    (fun t m hm => fpProdLift_unique t.proj m hm)

open CategoryTheory.Limits in
instance : HasProducts.{w} (FreeProdCompletionCat.{u, v, w} C) :=
  hasProducts_of_limit_fans fpFan fpIsLimitFan

/--
`ProdData` instance for `FreeProdCompletionCat C` using the product construction.
-/
instance fpProdData : ProdData.{w} (FreeProdCompletionCat.{u, v, w} C) where
  prod := fpProdObj
  π := fpProdπ

end FreeProdCompletionProducts

/-! ## Products in ProdContravarRepCat

Since `ProdContravarRepCat C = FreeProdCompletionCat (C^op')` definitionally,
products in `ProdContravarRepCat` follow directly.
-/

section ProdContravarRepProducts

open Limits

universe w

variable {C : Type u} [Category.{v} C]

/--
`ProdContravarRepCat C` has all small products, inherited from
`FreeProdCompletionCat (C^op')`.
-/
instance : HasProducts.{w} (ProdContravarRepCat.{u, v, w} C) :=
  hasProducts_of_limit_fans
    (fun F => fpFan (C := Cᵒᵖ') F)
    (fun F => fpIsLimitFan (C := Cᵒᵖ') F)

/--
`ProdData` instance for `ProdContravarRepCat C`, inherited from
`FreeProdCompletionCat (C^op')`.
-/
instance pcrProdData : ProdData.{w} (ProdContravarRepCat.{u, v, w} C) where
  prod F := fpProdObj (C := Cᵒᵖ') F
  π F j := fpProdπ (C := Cᵒᵖ') F j

end ProdContravarRepProducts

/-! ## CoprodData and ProdData for FreeCoprodProdCat

`FreeCoprodProdCat C = FreeCoprodCompletionCat (FreeProdCompletionCat C)` has:
- `CoprodData` from the outer `FreeCoprodCompletionCat` (at any universe `w₁`)
- `ProdData` from products distributing over coproducts (when universes match)

The `ProdData` instance requires `w₁ = w₂` because `fcProdData` requires
`ProdData.{w}` on the underlying category at the same universe as the
coproduct index type.
-/

section FreeCoprodProdData

universe w₁ w₂

variable {C : Type u} [Category.{v} C]

/--
`CoprodData` instance for `FreeCoprodProdCat C`. The outer free coproduct
completion provides coproducts.
-/
instance fcpCoprodData : CoprodData.{w₁} (FreeCoprodProdCat.{u, v, w₁, w₂} C) :=
  fcCoprodData

end FreeCoprodProdData

/-! ## ProdData for FreeCoprodProdCat with matching universes

Products in `FreeCoprodProdCat` distribute over coproducts. The universe
constraint `w₁ = w₂` is fundamental: products indexed by `J : Type w` create
Pi types `∀ j, fcpOuterIndex (F j)` at universe `max w w₁`. For the result
to stay in the same `FreeCoprodProdCat.{u, v, w₁, w₂}`, we need `max w w₁ = w₁`,
which combined with the inner product universe constraint gives `w = w₁ = w₂`.
-/

section FreeCoprodProdDataMatching

universe w

variable {C : Type u} [Category.{v} C]

/--
`ProdData` instance for `FreeCoprodProdCat C` when both index universes are `w`.
Products from the inner free product completion distribute over the outer
coproducts. The matching universe constraint is fundamental due to how
Pi types affect universe levels.
-/
instance fcpProdDataMatching : ProdData.{w} (FreeCoprodProdCat.{u, v, w, w} C) :=
  fcProdData

end FreeCoprodProdDataMatching

/-! ## CoprodData and ProdData for CoprodCovarRepSquaredCat

`CoprodCovarRepSquaredCat C = CoprodCovarRepCat' (CoprodCovarRepCat' C)` has:
- `CoprodData` from the outer `CoprodCovarRepCat'` (at any universe `w₁`)
- `ProdData` when universes match (via the equivalence with `FreeCoprodProdCat`)
-/

section CoprodCovarRepSquaredData

universe w₁ w₂

variable {C : Type u} [Category.{v} C]

/--
`CoprodData` instance for `CoprodCovarRepSquaredCat C`. The outer free coproduct
completion provides coproducts.
-/
instance ccrsCoprodData :
    CoprodData.{w₁} (CoprodCovarRepSquaredCat.{u, v, w₁, w₂} C) :=
  ccrCoprodData

end CoprodCovarRepSquaredData

/-! ## ProdData for CoprodCovarRepSquaredCat with matching universes -/

section CoprodCovarRepSquaredDataMatching

universe w

variable {C : Type u} [Category.{v} C]

/--
`ProdData` instance for `CoprodCovarRepSquaredCat C` when both index universes
are `w`. Uses the isomorphism with `FreeCoprodProdCat C`.
-/
instance ccrsProdDataMatching :
    ProdData.{w} (CoprodCovarRepSquaredCat.{u, v, w, w} C) where
  prod F := fcpToCcrsObj (∏' (ccrsToFcpObj ∘ F))
  π F j := fcpToCcrsObj_ccrsToFcpObj (F j) ▸
    fcpToCcrsMor (ProdData.proj (ccrsToFcpObj ∘ F) j)

end CoprodCovarRepSquaredDataMatching

end GebLean
