import GebLean.Utilities.Category
import GebLean.Utilities.TwistedArrow
import GebLean.Utilities.TwArrPresheaf
import GebLean.Utilities.Grothendieck

/-!
# The connected Grothendieck construction

Given a functor `F : Tw(C) → Cat`, this module defines a category `E(F)`
equipped with a functor `E(F) → Arr(C)`. This defines a functor

```text
E : Fun(Tw(C), Cat) → Cat/Arr(C).
```

The construction generalizes the two-sided Grothendieck construction by
allowing the indexing category to depend on the arrow `f : a → b` itself,
not just on `a` and `b` separately. The morphisms carry both an arrow-category
square and a fiber morphism in the common diagonal category.

See `docs/connected-grothendieck-construction.md` for the mathematical
specification.
-/

universe v u

namespace GebLean

open CategoryTheory

variable (C : Type u) [Category.{v} C]

section ConnectedGrothendieckData

/-! ## Objects and morphisms of the connected Grothendieck construction

We define the objects and morphisms without using typeclasses, following
the pattern in `GebLean.Utilities.Category`.
-/

variable (F : TwistedArrow' C ⥤ Cat.{v, u})

/--
An object of the connected Grothendieck construction `E(F)` consists of:
- An arrow `f : a ⟶ b` in `C` (represented as an object of `TwistedArrow' C`)
- An object `fiber` in the category `F(f)`
-/
structure ConnGrothendieckObj where
  /-- The underlying arrow in `C`, as a twisted arrow object -/
  arrow : TwistedArrow' C
  /-- An object in the fiber category over this arrow -/
  fiber : F.obj arrow

/--
The common diagonal arrow `w = f ≫ codArr = domArr ≫ f'` in the arrow square.
Given twisted arrows `tw` and `tw'` with a commuting square
`twArr' tw ≫ codArr = domArr ≫ twArr' tw'`, this is the diagonal.
-/
def connGrothendieckDiag (tw : TwistedArrow' C)
    {b' : C} (codArr : twCod' tw ⟶ b') :
    TwistedArrow' C :=
  twObjMk' (twArr' tw ≫ codArr)

/--
The twisted arrow morphism `(id, codArr) : tw → w` where `w = twArr' tw ≫ codArr`.
This transports along the codomain direction.
-/
def connGrothendieckTwMorphCod (tw : TwistedArrow' C)
    {b' : C} (codArr : twCod' tw ⟶ b') :
    tw ⟶ connGrothendieckDiag C tw codArr :=
  twHomMk' (𝟙 _) codArr (by simp only [connGrothendieckDiag, twObjMk'_arr,
    Category.id_comp])

/--
The twisted arrow morphism `(domArr, id) : tw' → w` where `w = domArr ≫ twArr' tw'`.
This transports along the domain direction.
-/
def connGrothendieckTwMorphDom (tw' : TwistedArrow' C)
    {a : C} (domArr : a ⟶ twDom' tw') :
    tw' ⟶ twObjMk' (domArr ≫ twArr' tw') :=
  twHomMk' domArr (𝟙 _) (by simp only [twObjMk'_arr, Category.comp_id])

/--
The fiber category over the diagonal of a commuting square.
Given `square_comm : twArr' x.arrow ≫ codArr = domArr ≫ twArr' y.arrow`,
this is `F(twObjMk' (twArr' x.arrow ≫ codArr))`.
-/
abbrev connGrothendieckFiberCat (x : ConnGrothendieckObj C F)
    {b' : C} (codArr : twCod' x.arrow ⟶ b') : Cat.{v, u} :=
  F.obj (connGrothendieckDiag C x.arrow codArr)

/--
A morphism in the connected Grothendieck construction from `(f, e)` to `(f', e')`
consists of:
- A morphism `(g, h)` in `Arr(C)` from `f` to `f'`, i.e., a commuting square
  where `g : a ⟶ a'` and `h : b ⟶ b'` satisfy `f ≫ h = g ≫ f'`
- A fiber morphism `φ` in `F(w)` where `w = f ≫ h = g ≫ f'` is the common
  diagonal

The fiber morphism goes from `F(id_a, h)(e)` to `F(g, id_{b'})(e')`, where:
- `(id_a, h) : f → w` is a twisted arrow morphism
- `(g, id_{b'}) : f' → w` is a twisted arrow morphism
-/
structure ConnGrothendieckHom (x y : ConnGrothendieckObj C F) where
  /-- The domain component of the arrow square: `domArr : a ⟶ a'` -/
  domArr : twDom' x.arrow ⟶ twDom' y.arrow
  /-- The codomain component of the arrow square: `codArr : b ⟶ b'` -/
  codArr : twCod' x.arrow ⟶ twCod' y.arrow
  /-- The arrow square commutes: `f ≫ codArr = domArr ≫ f'` -/
  square_comm : twArr' x.arrow ≫ codArr = domArr ≫ twArr' y.arrow
  /-- The fiber morphism in `F(w)` where `w` is the common diagonal.

  The source is the image of `x.fiber` under `F(id, codArr)`.
  The target is the image of `y.fiber` under `F(domArr, id)`, cast to the
  same fiber category using `square_comm`. -/
  fiberMorph :
    @Quiver.Hom (connGrothendieckFiberCat C F x codArr)
      (connGrothendieckFiberCat C F x codArr).str.toQuiver
      ((F.map (connGrothendieckTwMorphCod C x.arrow codArr)).obj x.fiber)
      (cast (by
        simp only [connGrothendieckFiberCat, connGrothendieckDiag, square_comm])
        ((F.map (connGrothendieckTwMorphDom C y.arrow domArr)).obj y.fiber))

/--
The hom-set for the connected Grothendieck construction.
-/
def connGrothendieckHomSet : HomSet (ConnGrothendieckObj C F) :=
  ConnGrothendieckHom C F

end ConnectedGrothendieckData

end GebLean
