import GebLean.Utilities.Category
import GebLean.Utilities.TwistedArrow
import GebLean.Utilities.TwArrPresheaf
import GebLean.Utilities.Grothendieck
import GebLean.Utilities.Opposites

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

universe v u w₁ w₂

namespace GebLean

open CategoryTheory

variable (C : Type u) [Category.{v} C]

section ConnectedGrothendieckData

/-! ## Objects and morphisms of the connected Grothendieck construction

We define the objects and morphisms without using typeclasses, following
the pattern in `GebLean.Utilities.Category`.
-/

variable (F : TwistedArrow' C ⥤ Cat.{w₁, w₂})

/--
An object of the connected Grothendieck construction `E(F)` consists of:
- An arrow `f : a ⟶ b` in `C` (represented as an object of `TwistedArrow' C`)
- An object `fiber` in the category `F(f)`
-/
@[ext]
structure ConnGrothendieckObj where
  /-- The underlying arrow in `C`, as a twisted arrow object -/
  arrow : TwistedArrow' C
  /-- An object in the fiber category over this arrow -/
  fiber : F.obj arrow

/--
The diagonal arrow `w = f ≫ codArr` in the arrow square, constructed from the
source arrow and the codomain morphism.
-/
def connGrothendieckDiagCod (tw : TwistedArrow' C)
    {b' : C} (codArr : twCod' tw ⟶ b') :
    TwistedArrow' C :=
  twObjMk' (twArr' tw ≫ codArr)

/--
The diagonal arrow `w = domArr ≫ f'` in the arrow square, constructed from the
domain morphism and the target arrow.
-/
def connGrothendieckDiagDom (tw' : TwistedArrow' C)
    {a : C} (domArr : a ⟶ twDom' tw') :
    TwistedArrow' C :=
  twObjMk' (domArr ≫ twArr' tw')

/--
Alias for `connGrothendieckDiagCod`, the standard choice for the diagonal.
-/
abbrev connGrothendieckDiag (tw : TwistedArrow' C)
    {b' : C} (codArr : twCod' tw ⟶ b') :
    TwistedArrow' C :=
  connGrothendieckDiagCod C tw codArr

set_option backward.isDefEq.respectTransparency false in
/--
The twisted arrow morphism `(id, codArr) : tw → w` where `w = twArr' tw ≫ codArr`.
This transports along the codomain direction.
-/
def connGrothendieckTwMorphCod (tw : TwistedArrow' C)
    {b' : C} (codArr : twCod' tw ⟶ b') :
    tw ⟶ connGrothendieckDiagCod C tw codArr :=
  twHomMk' (𝟙 _) codArr (by simp only [connGrothendieckDiagCod, twObjMk'_arr,
    Category.id_comp])

set_option backward.isDefEq.respectTransparency false in
/--
The twisted arrow morphism `(domArr, id) : tw' → w` where `w = domArr ≫ twArr' tw'`.
This transports along the domain direction.
-/
def connGrothendieckTwMorphDom (tw' : TwistedArrow' C)
    {a : C} (domArr : a ⟶ twDom' tw') :
    tw' ⟶ connGrothendieckDiagDom C tw' domArr :=
  twHomMk' domArr (𝟙 _) (by simp only [connGrothendieckDiagDom, twObjMk'_arr,
    Category.comp_id])

/--
The fiber category over the diagonal of a commuting square.
Given `square_comm : twArr' x.arrow ≫ codArr = domArr ≫ twArr' y.arrow`,
this is `F(twObjMk' (twArr' x.arrow ≫ codArr))`.
-/
abbrev connGrothendieckFiberCat (x : ConnGrothendieckObj C F)
    {b' : C} (codArr : twCod' x.arrow ⟶ b') : Cat.{w₁, w₂} :=
  F.obj (connGrothendieckDiag C x.arrow codArr)

/--
The equality between the two representations of the diagonal arrow.
-/
def connGrothendieckDiagEq (x y : ConnGrothendieckObj C F)
    (domArr : twDom' x.arrow ⟶ twDom' y.arrow)
    (codArr : twCod' x.arrow ⟶ twCod' y.arrow)
    (square_comm : twArr' x.arrow ≫ codArr = domArr ≫ twArr' y.arrow) :
    connGrothendieckDiagDom C y.arrow domArr =
    connGrothendieckDiagCod C x.arrow codArr := by
  simp only [connGrothendieckDiagCod, connGrothendieckDiagDom, square_comm]

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
  The target is the image of `y.fiber` under `F(domArr, id)`, transported via
  `eqToHom` using `square_comm`. -/
  fiberMorph :
    (F.map (connGrothendieckTwMorphCod C x.arrow codArr)).toFunctor.obj x.fiber ⟶
    (F.map (connGrothendieckTwMorphDom C y.arrow domArr ≫
      eqToHom (connGrothendieckDiagEq C F x y domArr codArr square_comm))).toFunctor.obj
      y.fiber

/--
The hom-set for the connected Grothendieck construction.
-/
def connGrothendieckHomSet : HomSet (ConnGrothendieckObj C F) :=
  ConnGrothendieckHom C F

end ConnectedGrothendieckData

section ConnectedGrothendieckCategory

/-! ## Category structure on the connected Grothendieck construction -/

variable (F : TwistedArrow' C ⥤ Cat.{w₁, w₂})

/--
When `codArr = 𝟙`, the diagonal equals the original arrow.
-/
lemma connGrothendieckDiagCod_id (tw : TwistedArrow' C) :
    connGrothendieckDiagCod C tw (𝟙 (twCod' tw)) = tw := by
  simp only [connGrothendieckDiagCod, Category.comp_id]
  rfl

/--
When `domArr = 𝟙`, the diagonal equals the original arrow.
-/
lemma connGrothendieckDiagDom_id (tw : TwistedArrow' C) :
    connGrothendieckDiagDom C tw (𝟙 (twDom' tw)) = tw := by
  simp only [connGrothendieckDiagDom, Category.id_comp]
  rfl

/--
A `twHomMk'` with both components being identities is the identity morphism.
This version takes an arbitrary proof of the commutativity condition.
-/
lemma twHomMk'_id_id' (tw : TwistedArrow' C)
    (h : 𝟙 (twDom' tw) ≫ twArr' tw ≫ 𝟙 (twCod' tw) = twArr' tw) :
    twHomMk' (𝟙 (twDom' tw)) (𝟙 (twCod' tw)) h = 𝟙 tw := by
  apply twHom'_ext
  · simp only [twHomMk'_domArr]; exact (twDomArr'_id tw).symm
  · simp only [twHomMk'_codArr]; exact (twCodArr'_id tw).symm

/--
A `twHomMk'` with both components being identities is the identity morphism.
-/
lemma twHomMk'_id_id (tw : TwistedArrow' C) :
    twHomMk' (𝟙 (twDom' tw)) (𝟙 (twCod' tw))
      (by simp only [Category.id_comp, Category.comp_id]) = 𝟙 tw :=
  twHomMk'_id_id' C tw _

/--
A `twHomMk'` with identity components composed with `eqToHom` simplifies to `eqToHom`.
-/
@[simp]
lemma twHomMk'_id_id_comp_eqToHom (tw tw' : TwistedArrow' C)
    (h : 𝟙 (twDom' tw) ≫ twArr' tw ≫ 𝟙 (twCod' tw) = twArr' tw)
    (heq : tw = tw') :
    twHomMk' (𝟙 (twDom' tw)) (𝟙 (twCod' tw)) h ≫ eqToHom heq = eqToHom heq := by
  simp only [twHomMk'_id_id', Category.id_comp]

/--
The diagonal equality for identity morphisms.
-/
lemma connGrothendieckDiagEq_id (x : ConnGrothendieckObj C F) :
    connGrothendieckDiagEq C F x x (𝟙 _) (𝟙 _) (by simp) =
    (connGrothendieckDiagDom_id C x.arrow).trans (connGrothendieckDiagCod_id C x.arrow).symm := by
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
The identity morphism in the connected Grothendieck construction.
-/
def connGrothendieckId (x : ConnGrothendieckObj C F) :
    ConnGrothendieckHom C F x x where
  domArr := 𝟙 _
  codArr := 𝟙 _
  square_comm := by simp
  fiberMorph := eqToHom (by
    have hCod : connGrothendieckDiagCod C x.arrow (𝟙 _) = x.arrow :=
      connGrothendieckDiagCod_id C x.arrow
    have hDom : connGrothendieckDiagDom C x.arrow (𝟙 _) = x.arrow :=
      connGrothendieckDiagDom_id C x.arrow
    have hMorphCod : connGrothendieckTwMorphCod C x.arrow (𝟙 _) =
        eqToHom hCod.symm := by
      apply twHom'_ext
      · simp only [connGrothendieckTwMorphCod, twHomMk'_domArr]
        rw [twDomArr'_eqToHom]
        simp only [eqToHom_refl]
      · simp only [connGrothendieckTwMorphCod, twHomMk'_codArr]
        rw [twCodArr'_eqToHom]
        simp only [eqToHom_refl]
    have hMorphDom : connGrothendieckTwMorphDom C x.arrow (𝟙 _) =
        eqToHom hDom.symm := by
      apply twHom'_ext
      · simp only [connGrothendieckTwMorphDom, twHomMk'_domArr]
        rw [twDomArr'_eqToHom]
        simp only [eqToHom_refl]; rfl
      · simp only [connGrothendieckTwMorphDom, twHomMk'_codArr]
        rw [twCodArr'_eqToHom]
        simp only [eqToHom_refl]
    simp only [hMorphCod, hMorphDom, eqToHom_trans])

/--
The composite diagonal for composition of morphisms.
Given `m : x → y` with codomain arrow `h` and `n : y → z` with codomain arrow `h'`,
the composite diagonal is `w₃ = f ≫ h ≫ h' = g ≫ g' ≫ f''`.
-/
def connGrothendieckDiagComp (tw : TwistedArrow' C)
    {b' b'' : C} (codArr : twCod' tw ⟶ b') (codArr' : b' ⟶ b'') :
    TwistedArrow' C :=
  connGrothendieckDiagCod C tw (codArr ≫ codArr')

set_option backward.isDefEq.respectTransparency false in
/--
The twisted arrow morphism from `w₁` to `w₃`.
`w₁ = f ≫ h` and `w₃ = f ≫ h ≫ h'`, so the morphism is `(id_a, h')`.
-/
def connGrothendieckTwMorphW1ToW3 (tw : TwistedArrow' C)
    {b' b'' : C} (codArr : twCod' tw ⟶ b') (codArr' : b' ⟶ b'') :
    connGrothendieckDiagCod C tw codArr ⟶ connGrothendieckDiagComp C tw codArr codArr' :=
  twHomMk' (𝟙 _) codArr' (by
    simp only [connGrothendieckDiagCod, connGrothendieckDiagComp, twObjMk'_arr,
      Category.id_comp, Category.assoc])

/--
The square commutativity for composed morphisms.
-/
lemma connGrothendieckCompSquareComm {x y z : ConnGrothendieckObj C F}
    (m : ConnGrothendieckHom C F x y) (n : ConnGrothendieckHom C F y z) :
    twArr' x.arrow ≫ m.codArr ≫ n.codArr = (m.domArr ≫ n.domArr) ≫ twArr' z.arrow := by
  calc twArr' x.arrow ≫ m.codArr ≫ n.codArr
      = (twArr' x.arrow ≫ m.codArr) ≫ n.codArr := by rw [Category.assoc]
    _ = (m.domArr ≫ twArr' y.arrow) ≫ n.codArr := by rw [m.square_comm]
    _ = m.domArr ≫ twArr' y.arrow ≫ n.codArr := by rw [Category.assoc]
    _ = m.domArr ≫ n.domArr ≫ twArr' z.arrow := by rw [n.square_comm]
    _ = (m.domArr ≫ n.domArr) ≫ twArr' z.arrow := by rw [Category.assoc]

/--
The diagonal `w₁ = f ≫ h` from the first morphism.
-/
abbrev connGrothendieckW1 {x y : ConnGrothendieckObj C F}
    (m : ConnGrothendieckHom C F x y) : TwistedArrow' C :=
  connGrothendieckDiagCod C x.arrow m.codArr

/--
The diagonal `w₂ = f' ≫ h'` from the second morphism.
-/
abbrev connGrothendieckW2 {y z : ConnGrothendieckObj C F}
    (n : ConnGrothendieckHom C F y z) : TwistedArrow' C :=
  connGrothendieckDiagCod C y.arrow n.codArr

/--
The composite diagonal `w₃ = f ≫ h ≫ h'`.
-/
abbrev connGrothendieckW3 {x y z : ConnGrothendieckObj C F}
    (m : ConnGrothendieckHom C F x y) (n : ConnGrothendieckHom C F y z) :
    TwistedArrow' C :=
  connGrothendieckDiagCod C x.arrow (m.codArr ≫ n.codArr)

set_option backward.isDefEq.respectTransparency false in
/--
The twisted arrow morphism `w₁ → w₃` given by `(id_a, h')`.
This is used to transport `m.fiberMorph` from `F(w₁)` to `F(w₃)`.
-/
def connGrothendieckMorphW1W3 {x y z : ConnGrothendieckObj C F}
    (m : ConnGrothendieckHom C F x y) (n : ConnGrothendieckHom C F y z) :
    connGrothendieckW1 C F m ⟶ connGrothendieckW3 C F m n :=
  twHomMk' (𝟙 _) n.codArr (by
    simp only [connGrothendieckDiagCod, twObjMk'_arr, Category.id_comp, Category.assoc])

/--
The equality between `w₂` from the domain perspective and `w₃` from the codomain perspective.
Uses the square commutativity of `m`.
-/
lemma connGrothendieckW2EqW3 {x y z : ConnGrothendieckObj C F}
    (m : ConnGrothendieckHom C F x y) (n : ConnGrothendieckHom C F y z) :
    connGrothendieckDiagDom C (connGrothendieckW2 C F n) m.domArr =
    connGrothendieckW3 C F m n := by
  simp only [connGrothendieckDiagCod, connGrothendieckDiagDom, twObjMk'_arr]
  congr 1
  calc m.domArr ≫ twArr' y.arrow ≫ n.codArr
      = (m.domArr ≫ twArr' y.arrow) ≫ n.codArr := by rw [Category.assoc]
    _ = (twArr' x.arrow ≫ m.codArr) ≫ n.codArr := by rw [← m.square_comm]
    _ = twArr' x.arrow ≫ m.codArr ≫ n.codArr := by rw [Category.assoc]

/--
The twisted arrow morphism `w₂ → w₃` given by `(g, id_{b''})`.
This is used to transport `n.fiberMorph` from `F(w₂)` to `F(w₃)`.
-/
def connGrothendieckMorphW2W3 {x y z : ConnGrothendieckObj C F}
    (m : ConnGrothendieckHom C F x y) (n : ConnGrothendieckHom C F y z) :
    connGrothendieckW2 C F n ⟶ connGrothendieckW3 C F m n :=
  connGrothendieckTwMorphDom C (connGrothendieckW2 C F n) m.domArr ≫
    eqToHom (connGrothendieckW2EqW3 C F m n)

set_option backward.isDefEq.respectTransparency false in
/--
The source of `connGrothendieckTwMorphCod` composed with `connGrothendieckMorphW1W3`
equals `connGrothendieckTwMorphCod` for the composed codomain arrows.
-/
lemma connGrothendieckTwMorphCodComp {x y z : ConnGrothendieckObj C F}
    (m : ConnGrothendieckHom C F x y) (n : ConnGrothendieckHom C F y z) :
    connGrothendieckTwMorphCod C x.arrow m.codArr ≫ connGrothendieckMorphW1W3 C F m n =
    connGrothendieckTwMorphCod C x.arrow (m.codArr ≫ n.codArr) := by
  apply twHom'_ext
  · simp only [connGrothendieckTwMorphCod, connGrothendieckMorphW1W3,
      twDomArr'_comp, twHomMk'_domArr, Category.comp_id]
  · simp only [connGrothendieckTwMorphCod, connGrothendieckMorphW1W3,
      twCodArr'_comp, twHomMk'_codArr]

/--
The equality showing that the source transport for composition factors through `w₁`.
-/
lemma connGrothendieckCompSrcEq {x y z : ConnGrothendieckObj C F}
    (m : ConnGrothendieckHom C F x y) (n : ConnGrothendieckHom C F y z) :
    (F.map (connGrothendieckTwMorphCod C x.arrow (m.codArr ≫ n.codArr))).toFunctor.obj
      x.fiber =
    (F.map (connGrothendieckMorphW1W3 C F m n)).toFunctor.obj
      ((F.map (connGrothendieckTwMorphCod C x.arrow m.codArr)).toFunctor.obj x.fiber) := by
  rw [← connGrothendieckTwMorphCodComp C F m n, Functor.map_comp,
    Cat.Hom.comp_toFunctor, Functor.comp_obj]

/--
The twisted arrow morphism from `y.arrow` to `w₃` via the path
`(m.domArr, id) ≫ eqToHom ≫ (id, n.codArr)`.
-/
def connGrothendieckTwMorphYW3_left {x y z : ConnGrothendieckObj C F}
    (m : ConnGrothendieckHom C F x y) (n : ConnGrothendieckHom C F y z) :
    y.arrow ⟶ connGrothendieckW3 C F m n :=
  connGrothendieckTwMorphDom C y.arrow m.domArr ≫
    eqToHom (connGrothendieckDiagEq C F x y m.domArr m.codArr m.square_comm) ≫
    connGrothendieckMorphW1W3 C F m n

/--
The twisted arrow morphism from `y.arrow` to `w₃` via the path
`(id, n.codArr) ≫ (m.domArr, id) ≫ eqToHom`.
-/
def connGrothendieckTwMorphYW3_right {x y z : ConnGrothendieckObj C F}
    (m : ConnGrothendieckHom C F x y) (n : ConnGrothendieckHom C F y z) :
    y.arrow ⟶ connGrothendieckW3 C F m n :=
  connGrothendieckTwMorphCod C y.arrow n.codArr ≫
    connGrothendieckMorphW2W3 C F m n

set_option backward.isDefEq.respectTransparency false in
/--
Both paths from `y.arrow` to `w₃` give the same twisted arrow morphism.
-/
lemma connGrothendieckTwMorphYW3_eq {x y z : ConnGrothendieckObj C F}
    (m : ConnGrothendieckHom C F x y) (n : ConnGrothendieckHom C F y z) :
    connGrothendieckTwMorphYW3_left C F m n =
    connGrothendieckTwMorphYW3_right C F m n := by
  apply twHom'_ext
  · simp only [connGrothendieckTwMorphYW3_left, connGrothendieckTwMorphYW3_right,
      connGrothendieckMorphW1W3, connGrothendieckMorphW2W3,
      connGrothendieckTwMorphDom, connGrothendieckTwMorphCod,
      twDomArr'_comp, twHomMk'_domArr, twDomArr'_eqToHom]
    simp only [Category.id_comp, Category.comp_id]
  · simp only [connGrothendieckTwMorphYW3_left, connGrothendieckTwMorphYW3_right,
      connGrothendieckMorphW1W3, connGrothendieckMorphW2W3,
      connGrothendieckTwMorphDom, connGrothendieckTwMorphCod,
      twCodArr'_comp, twHomMk'_codArr, twCodArr'_eqToHom]
    simp only [Category.id_comp, Category.comp_id, eqToHom_refl]

/--
The middle equality: the target of transported `m.fiberMorph` equals
the source of transported `n.fiberMorph` after appropriate eqToHom adjustments.
-/
lemma connGrothendieckCompMiddleEq {x y z : ConnGrothendieckObj C F}
    (m : ConnGrothendieckHom C F x y) (n : ConnGrothendieckHom C F y z) :
    (F.map (connGrothendieckMorphW1W3 C F m n)).toFunctor.obj
      ((F.map (connGrothendieckTwMorphDom C y.arrow m.domArr ≫
        eqToHom (connGrothendieckDiagEq C F x y m.domArr m.codArr
          m.square_comm))).toFunctor.obj y.fiber) =
    (F.map (connGrothendieckMorphW2W3 C F m n)).toFunctor.obj
      ((F.map (connGrothendieckTwMorphCod C y.arrow n.codArr)).toFunctor.obj y.fiber) := by
  have hLeft : (F.map (connGrothendieckMorphW1W3 C F m n)).toFunctor.obj
      ((F.map (connGrothendieckTwMorphDom C y.arrow m.domArr ≫
        eqToHom (connGrothendieckDiagEq C F x y m.domArr m.codArr
          m.square_comm))).toFunctor.obj y.fiber) =
      (F.map (connGrothendieckTwMorphYW3_left C F m n)).toFunctor.obj y.fiber := by
    simp only [connGrothendieckTwMorphYW3_left, Functor.map_comp,
      Cat.Hom.comp_toFunctor, Functor.comp_obj]
  have hRight : (F.map (connGrothendieckMorphW2W3 C F m n)).toFunctor.obj
      ((F.map (connGrothendieckTwMorphCod C y.arrow n.codArr)).toFunctor.obj y.fiber) =
      (F.map (connGrothendieckTwMorphYW3_right C F m n)).toFunctor.obj y.fiber := by
    simp only [connGrothendieckTwMorphYW3_right, Functor.map_comp,
      Cat.Hom.comp_toFunctor, Functor.comp_obj]
  rw [hLeft, connGrothendieckTwMorphYW3_eq, hRight]

/--
The twisted arrow morphism from `z.arrow` to `w₃` via the direct path
`(m.domArr ≫ n.domArr, id) ≫ eqToHom`.
-/
def connGrothendieckTwMorphZW3_left {x y z : ConnGrothendieckObj C F}
    (m : ConnGrothendieckHom C F x y) (n : ConnGrothendieckHom C F y z) :
    z.arrow ⟶ connGrothendieckW3 C F m n :=
  connGrothendieckTwMorphDom C z.arrow (m.domArr ≫ n.domArr) ≫
    eqToHom (connGrothendieckDiagEq C F x z (m.domArr ≫ n.domArr) (m.codArr ≫ n.codArr)
      (connGrothendieckCompSquareComm C F m n))

/--
The twisted arrow morphism from `z.arrow` to `w₃` via the factored path
`(n.domArr, id) ≫ eqToHom ≫ connGrothendieckMorphW2W3`.
-/
def connGrothendieckTwMorphZW3_right {x y z : ConnGrothendieckObj C F}
    (m : ConnGrothendieckHom C F x y) (n : ConnGrothendieckHom C F y z) :
    z.arrow ⟶ connGrothendieckW3 C F m n :=
  connGrothendieckTwMorphDom C z.arrow n.domArr ≫
    eqToHom (connGrothendieckDiagEq C F y z n.domArr n.codArr n.square_comm) ≫
    connGrothendieckMorphW2W3 C F m n

set_option backward.isDefEq.respectTransparency false in
/--
Both paths from `z.arrow` to `w₃` give the same twisted arrow morphism.
-/
lemma connGrothendieckTwMorphZW3_eq {x y z : ConnGrothendieckObj C F}
    (m : ConnGrothendieckHom C F x y) (n : ConnGrothendieckHom C F y z) :
    connGrothendieckTwMorphZW3_left C F m n =
    connGrothendieckTwMorphZW3_right C F m n := by
  apply twHom'_ext
  · simp only [connGrothendieckTwMorphZW3_left, connGrothendieckTwMorphZW3_right,
      connGrothendieckMorphW2W3, connGrothendieckTwMorphDom,
      twDomArr'_comp, twHomMk'_domArr, twDomArr'_eqToHom]
    simp only [Category.assoc, eqToHom_refl, Category.id_comp]
  · simp only [connGrothendieckTwMorphZW3_left, connGrothendieckTwMorphZW3_right,
      connGrothendieckMorphW2W3, connGrothendieckTwMorphDom,
      twCodArr'_comp, twHomMk'_codArr, twCodArr'_eqToHom]
    simp only [Category.comp_id, eqToHom_refl]

/--
The equality showing the target transport for composition factors correctly.
-/
lemma connGrothendieckCompTgtEq {x y z : ConnGrothendieckObj C F}
    (m : ConnGrothendieckHom C F x y) (n : ConnGrothendieckHom C F y z) :
    (F.map (connGrothendieckTwMorphDom C z.arrow (m.domArr ≫ n.domArr) ≫
      eqToHom (connGrothendieckDiagEq C F x z (m.domArr ≫ n.domArr) (m.codArr ≫ n.codArr)
        (connGrothendieckCompSquareComm C F m n)))).toFunctor.obj z.fiber =
    (F.map (connGrothendieckMorphW2W3 C F m n)).toFunctor.obj
      ((F.map (connGrothendieckTwMorphDom C z.arrow n.domArr ≫
        eqToHom (connGrothendieckDiagEq C F y z n.domArr n.codArr
          n.square_comm))).toFunctor.obj z.fiber) := by
  calc (F.map (connGrothendieckTwMorphDom C z.arrow (m.domArr ≫ n.domArr) ≫
      eqToHom (connGrothendieckDiagEq C F x z (m.domArr ≫ n.domArr) (m.codArr ≫ n.codArr)
        (connGrothendieckCompSquareComm C F m n)))).toFunctor.obj z.fiber
      = (F.map (connGrothendieckTwMorphZW3_left C F m n)).toFunctor.obj z.fiber := rfl
    _ = (F.map (connGrothendieckTwMorphZW3_right C F m n)).toFunctor.obj z.fiber := by
          rw [connGrothendieckTwMorphZW3_eq]
    _ = (F.map (connGrothendieckMorphW2W3 C F m n)).toFunctor.obj
        ((F.map (connGrothendieckTwMorphDom C z.arrow n.domArr ≫
          eqToHom (connGrothendieckDiagEq C F y z n.domArr n.codArr
            n.square_comm))).toFunctor.obj z.fiber) := by
            simp only [connGrothendieckTwMorphZW3_right, Functor.map_comp,
              Cat.Hom.comp_toFunctor, Functor.comp_obj]

/--
Composition of morphisms in the connected Grothendieck construction.

The fiber morphism is constructed by:
1. Transporting `m.fiberMorph` along `F(id_a, h')` to get a morphism in `F(w₃)`
2. Transporting `n.fiberMorph` along `F(g, id_{b''})` to get a morphism in `F(w₃)`
3. Composing: `F(g, id_{b''})(ψ) ∘ F(id_a, h')(φ)`
-/
def connGrothendieckComp {x y z : ConnGrothendieckObj C F}
    (m : ConnGrothendieckHom C F x y) (n : ConnGrothendieckHom C F y z) :
    ConnGrothendieckHom C F x z where
  domArr := m.domArr ≫ n.domArr
  codArr := m.codArr ≫ n.codArr
  square_comm := connGrothendieckCompSquareComm C F m n
  fiberMorph :=
    -- srcEq ≫ F(w₁→w₃)(φ) ≫ middleEq ≫ F(w₂→w₃)(ψ) ≫ tgtEq⁻¹
    eqToHom (connGrothendieckCompSrcEq C F m n) ≫
    (F.map (connGrothendieckMorphW1W3 C F m n)).toFunctor.map m.fiberMorph ≫
    eqToHom (connGrothendieckCompMiddleEq C F m n) ≫
    (F.map (connGrothendieckMorphW2W3 C F m n)).toFunctor.map n.fiberMorph ≫
    eqToHom (connGrothendieckCompTgtEq C F m n).symm

/--
Extensionality for `ConnGrothendieckHom`: two morphisms are equal if their
domain arrows, codomain arrows, and fiber morphisms (under HEq) are equal.
-/
theorem connGrothendieckHom_ext {x y : ConnGrothendieckObj C F}
    {m n : ConnGrothendieckHom C F x y}
    (hDom : m.domArr = n.domArr) (hCod : m.codArr = n.codArr)
    (hFiber : HEq m.fiberMorph n.fiberMorph) :
    m = n := by
  cases m; cases n
  simp only at hDom hCod
  subst hDom hCod
  congr 1
  exact eq_of_heq hFiber

/-- Heterogeneous extensionality for `ConnGrothendieckHom`:
if the source and target objects are equal and the domain arrows,
codomain arrows, and fiber morphisms are HEq, then the
morphisms are HEq. -/
theorem connGrothendieckHom_heq
    {x₁ x₂ y₁ y₂ : ConnGrothendieckObj C F}
    (hx : x₁ = x₂) (hy : y₁ = y₂)
    {m : ConnGrothendieckHom C F x₁ y₁}
    {n : ConnGrothendieckHom C F x₂ y₂}
    (hDom : HEq m.domArr n.domArr)
    (hCod : HEq m.codArr n.codArr)
    (hFiber : HEq m.fiberMorph n.fiberMorph) :
    HEq m n := by
  subst hx; subst hy
  cases m; cases n
  simp only [] at hDom hCod
  subst hDom; subst hCod
  congr 1
  exact eq_of_heq hFiber

/--
Category operations for the connected Grothendieck construction.
-/
def connGrothendieckCategoryOps :
    CategoryOps (connGrothendieckHomSet C F) where
  id := connGrothendieckId C F
  comp := connGrothendieckComp C F

/--
When the first morphism is identity, `connGrothendieckW1` equals `x.arrow`.
-/
lemma connGrothendieckW1_id (x : ConnGrothendieckObj C F) :
    connGrothendieckW1 C F (connGrothendieckId C F x) = x.arrow := by
  simp only [connGrothendieckW1, connGrothendieckId, connGrothendieckDiagCod_id]

/--
When the first morphism is identity, `connGrothendieckW3` equals `connGrothendieckW1` of
the second morphism.
-/
lemma connGrothendieckW3_id_left {x y : ConnGrothendieckObj C F}
    (m : ConnGrothendieckHom C F x y) :
    connGrothendieckW3 C F (connGrothendieckId C F x) m =
    connGrothendieckW1 C F m := by
  simp only [connGrothendieckW3, connGrothendieckW1, connGrothendieckId,
    connGrothendieckDiagCod, Category.id_comp]

/--
When the first morphism is identity, `connGrothendieckW1` equals `x.arrow`.
This is a variant that unfolds the abbreviation definition.
-/
lemma connGrothendieckW1_id' (x : ConnGrothendieckObj C F) :
    connGrothendieckDiagCod C x.arrow (𝟙 (twCod' x.arrow)) = x.arrow := by
  simp only [connGrothendieckDiagCod, Category.comp_id]
  rfl

/--
When the first morphism is identity, W3 equals the W1 of the second morphism.
This is a variant with explicit unfolding.
-/
lemma connGrothendieckW3_id_left' {x y : ConnGrothendieckObj C F}
    (m : ConnGrothendieckHom C F x y) :
    connGrothendieckDiagCod C x.arrow (𝟙 (twCod' x.arrow) ≫ m.codArr) =
    connGrothendieckDiagCod C x.arrow m.codArr := by
  simp only [Category.id_comp]

/-! ### Breaking down the id_comp fiber morphism proof

The goal is to prove that when composing identity on the left, the fiber morphism
chain simplifies to the original fiber morphism. We break this into steps:

1. Show that `connGrothendieckMorphW1W3` for (id, m) equals `eqToHom` composed with
   `connGrothendieckTwMorphCod`
2. Show that `connGrothendieckMorphW2W3` for (id, m) simplifies appropriately
3. Show that `F.map(eqToHom).map(eqToHom)` is `eqToHom`
4. Chain these together to get the final HEq
-/

/--
When the first morphism is identity, W1 = x.arrow.
-/
lemma connGrothendieckW1_id_comp_eq {x : ConnGrothendieckObj C F} :
    connGrothendieckW1 C F (connGrothendieckId C F x) = x.arrow :=
  connGrothendieckW1_id C F x

/--
When the first morphism is identity, W3 = connGrothendieckW1 m.
-/
lemma connGrothendieckW3_id_comp_eq {x y : ConnGrothendieckObj C F}
    (m : ConnGrothendieckHom C F x y) :
    connGrothendieckW3 C F (connGrothendieckId C F x) m = connGrothendieckW1 C F m := by
  simp only [connGrothendieckW3, connGrothendieckW1, connGrothendieckId,
    connGrothendieckDiagCod, Category.id_comp]

/--
When first morphism is identity, W2(m) = W1(m) = W3(id, m).
-/
lemma connGrothendieckW2_eq_W3_id_comp {x y : ConnGrothendieckObj C F}
    (m : ConnGrothendieckHom C F x y) :
    connGrothendieckW2 C F m = connGrothendieckW3 C F (connGrothendieckId C F x) m := by
  simp only [connGrothendieckW2, connGrothendieckW3, connGrothendieckId,
    connGrothendieckDiagCod, Category.id_comp]

/--
When first morphism is identity, W3's domain is x.arrow's domain.
-/
lemma connGrothendieckW3_id_comp_dom {x y : ConnGrothendieckObj C F}
    (m : ConnGrothendieckHom C F x y) :
    twDom' (connGrothendieckW3 C F (connGrothendieckId C F x) m) =
    twDom' x.arrow := by
  simp only [connGrothendieckW3, connGrothendieckId, connGrothendieckDiagCod,
    twObjMk'_dom, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
/--
When first morphism is identity, morphW2W3 is eqToHom.
-/
lemma connGrothendieckMorphW2W3_id_left {x y : ConnGrothendieckObj C F}
    (m : ConnGrothendieckHom C F x y) :
    connGrothendieckMorphW2W3 C F (connGrothendieckId C F x) m =
    eqToHom (connGrothendieckW2_eq_W3_id_comp C F m) := by
  apply twHom'_ext
  · simp only [connGrothendieckMorphW2W3, connGrothendieckTwMorphDom,
      connGrothendieckId, twDomArr'_comp, twHomMk'_domArr, twDomArr'_eqToHom]
    simp only [Category.id_comp, eqToHom_refl]
    simp only [connGrothendieckDiagCod, twObjMk'_dom]
  · simp only [connGrothendieckMorphW2W3, connGrothendieckTwMorphDom,
      connGrothendieckId, twCodArr'_comp, twHomMk'_codArr, twCodArr'_eqToHom]
    simp only [Category.comp_id, eqToHom_refl]

/--
morphW1W3(id, m) has codArr = m.codArr.
-/
lemma connGrothendieckMorphW1W3_id_left_codArr {x y : ConnGrothendieckObj C F}
    (m : ConnGrothendieckHom C F x y) :
    twCodArr' (connGrothendieckMorphW1W3 C F (connGrothendieckId C F x) m) =
    m.codArr := by
  simp only [connGrothendieckMorphW1W3, connGrothendieckId, twHomMk'_codArr]

/--
When second morphism is identity, W3 = W1.
-/
lemma connGrothendieckW3_id_right {x y : ConnGrothendieckObj C F}
    (m : ConnGrothendieckHom C F x y) :
    connGrothendieckW3 C F m (connGrothendieckId C F y) =
    connGrothendieckW1 C F m := by
  simp only [connGrothendieckW3, connGrothendieckW1, connGrothendieckId,
    connGrothendieckDiagCod, Category.comp_id]

/--
When second morphism is identity, morphW1W3 is eqToHom.
-/
lemma connGrothendieckMorphW1W3_id_right {x y : ConnGrothendieckObj C F}
    (m : ConnGrothendieckHom C F x y) :
    connGrothendieckMorphW1W3 C F m (connGrothendieckId C F y) =
    eqToHom (connGrothendieckW3_id_right C F m).symm := by
  apply twHom'_ext
  · simp only [connGrothendieckMorphW1W3, connGrothendieckId, twHomMk'_domArr,
      twDomArr'_eqToHom, eqToHom_refl, connGrothendieckDiagCod, twObjMk'_dom]
  · simp only [connGrothendieckMorphW1W3, connGrothendieckId, twHomMk'_codArr,
      twCodArr'_eqToHom, eqToHom_refl, connGrothendieckDiagCod, twObjMk'_cod]

/--
When second morphism is identity, W2(id) = y.arrow.
-/
lemma connGrothendieckW2_id_right (y : ConnGrothendieckObj C F) :
    connGrothendieckW2 C F (connGrothendieckId C F y) = y.arrow := by
  simp only [connGrothendieckW2, connGrothendieckId, connGrothendieckDiagCod_id]

/--
W1(id) is `connGrothendieckDiagCod x.arrow (𝟙 _)` which equals `x.arrow`.
This is the definitional form.
-/
lemma connGrothendieckW1_id_def {x : ConnGrothendieckObj C F} :
    connGrothendieckW1 C F (connGrothendieckId C F x) =
    connGrothendieckDiagCod C x.arrow (𝟙 (twCod' x.arrow)) := rfl

/--
The codArr of identity is `𝟙`.
-/
@[simp]
lemma connGrothendieckId_codArr (x : ConnGrothendieckObj C F) :
    (connGrothendieckId C F x).codArr = 𝟙 (twCod' x.arrow) := rfl

/--
The domArr of identity is `𝟙`.
-/
@[simp]
lemma connGrothendieckId_domArr (x : ConnGrothendieckObj C F) :
    (connGrothendieckId C F x).domArr = 𝟙 (twDom' x.arrow) := rfl

/--
For a functor `eqToHom h : C ⟶ D` in `Cat` where `h : C = D`,
applying it to a morphism gives something HEq to the original morphism.
-/
lemma Cat.eqToHom_map_heq {C D : Cat} (h : C = D) {x y : C} (f : x ⟶ y) :
    (eqToHom h).toFunctor.map f ≍ f := by
  subst h
  rfl

/--
Version of `Cat.eqToHom_map_heq` where the functor is only propositionally
equal to `(eqToHom h).toFunctor`.
-/
lemma Cat.functor_map_heq_of_eq_eqToHom {C D : Cat} (h : C = D)
    (G : C ⥤ D) (hG : G = (eqToHom h).toFunctor) {x y : C} (f : x ⟶ y) :
    G.map f ≍ f := by
  subst hG
  exact Cat.eqToHom_map_heq h f

/--
When functor `G` equals `G₁ ⋙ G₂ ⋙ (eqToHom h).toFunctor`, mapping by G gives
something HEq to `G₂.map (G₁.map f)`.
-/
lemma Cat.functor_map_heq_of_eq_comp_comp_eqToHom {C D E F' : Cat}
    (G : C ⥤ F') (G₁ : C ⥤ D) (G₂ : D ⥤ E)
    (h : E = F') (hG : G = G₁ ⋙ G₂ ⋙ (eqToHom h).toFunctor)
    {x y : C} (f : x ⟶ y) :
    G.map f ≍ G₂.map (G₁.map f) := by
  subst hG
  simp only [Functor.comp_map]
  exact Cat.eqToHom_map_heq h (G₂.map (G₁.map f))

/--
When the source objects are propositionally equal, `G.map (eqToHom h ≫ f)` is
HEq to `G.map f`.
-/
lemma Functor.map_eqToHom_comp_heq {C D : Type*} [Category C] [Category D]
    (G : C ⥤ D) {x x' y : C} (h : x' = x) (f : x ⟶ y) :
    G.map (eqToHom h ≫ f) ≍ G.map f := by
  cases h
  simp only [eqToHom_refl, Category.id_comp]
  exact HEq.rfl

/--
When the target objects are propositionally equal, `G.map (f ≫ eqToHom h)` is
HEq to `G.map f`.
-/
lemma Functor.map_comp_eqToHom_heq {C D : Type*} [Category C] [Category D]
    (G : C ⥤ D) {x y y' : C} (f : x ⟶ y) (h : y = y') :
    G.map (f ≫ eqToHom h) ≍ G.map f := by
  cases h
  simp only [eqToHom_refl, Category.comp_id]
  exact HEq.rfl

/--
Two morphisms in propositionally equal fiber categories are HEq iff they are
equal after transport via eqToHom functors. This is used when the categories
are `F.obj tw₁` and `F.obj tw₂` where `tw₁ = tw₂`.
-/
lemma Cat.heq_of_eqToHom_map_eq {C D : Cat} (h : C = D)
    {x₁ y₁ : C} (f₁ : x₁ ⟶ y₁)
    {x₂ y₂ : D} (f₂ : x₂ ⟶ y₂)
    (hx : (eqToHom h).toFunctor.obj x₁ = x₂)
    (hy : (eqToHom h).toFunctor.obj y₁ = y₂)
    (hf : (eqToHom h).toFunctor.map f₁ = eqToHom hx ≫ f₂ ≫ eqToHom hy.symm) :
    f₁ ≍ f₂ := by
  subst h
  simp only [eqToHom_refl, Cat.Hom.id_toFunctor, Functor.id_obj] at hx hy hf
  subst hx hy
  simp only [Functor.id_map, eqToHom_refl, Category.id_comp, Category.comp_id]
    at hf
  exact heq_of_eq hf

set_option backward.isDefEq.respectTransparency false in
/--
The left identity law: composing the identity on the left yields the original
morphism.
-/
theorem connGrothendieckId_comp {x y : ConnGrothendieckObj C F}
    (m : ConnGrothendieckHom C F x y) :
    connGrothendieckComp C F (connGrothendieckId C F x) m = m := by
  apply connGrothendieckHom_ext
  · simp only [connGrothendieckComp, connGrothendieckId, Category.id_comp]
  · simp only [connGrothendieckComp, connGrothendieckId, Category.id_comp]
  · simp only [connGrothendieckComp]
    conv_lhs => rw [← Category.assoc, ← Category.assoc, ← Category.assoc]
    apply HEq.trans (comp_eqToHom_heq _ _)
    simp only [connGrothendieckId, eqToHom_map, eqToHom_trans]
    apply HEq.trans
    · apply eqToHom_comp_heq
    change (F.map (connGrothendieckMorphW2W3 C F (connGrothendieckId C F x)
      m)).toFunctor.map m.fiberMorph ≍ m.fiberMorph
    rw [connGrothendieckMorphW2W3_id_left]
    rw [eqToHom_map]
    exact Cat.eqToHom_map_heq _ _

/--
The right identity law: composing the identity on the right yields the original
morphism.
-/
theorem connGrothendieckComp_id {x y : ConnGrothendieckObj C F}
    (m : ConnGrothendieckHom C F x y) :
    connGrothendieckComp C F m (connGrothendieckId C F y) = m := by
  apply connGrothendieckHom_ext
  · simp only [connGrothendieckComp, connGrothendieckId, Category.comp_id]
  · simp only [connGrothendieckComp, connGrothendieckId, Category.comp_id]
  · simp only [connGrothendieckComp]
    conv_lhs => rw [← Category.assoc, ← Category.assoc, ← Category.assoc]
    apply HEq.trans (comp_eqToHom_heq _ _)
    simp only [connGrothendieckId, eqToHom_map]
    change ((eqToHom _ ≫
            (F.map (connGrothendieckMorphW1W3 C F m
              (connGrothendieckId C F y))).toFunctor.map m.fiberMorph) ≫
              eqToHom _) ≫ eqToHom _ ≍ m.fiberMorph
    apply HEq.trans (comp_eqToHom_heq _ _)
    apply HEq.trans (comp_eqToHom_heq _ _)
    apply HEq.trans
    · apply eqToHom_comp_heq
    rw [connGrothendieckMorphW1W3_id_right, eqToHom_map]
    exact Cat.eqToHom_map_heq _ _

/--
The codomain arrow expressions `(a ≫ b) ≫ c` and `a ≫ b ≫ c` give the same diagonal.
-/
lemma connGrothendieckDiagCod_assoc (tw : TwistedArrow' C)
    {b' b'' b''' : C} (a : twCod' tw ⟶ b') (b : b' ⟶ b'') (c : b'' ⟶ b''') :
    connGrothendieckDiagCod C tw ((a ≫ b) ≫ c) = connGrothendieckDiagCod C tw (a ≫ b ≫ c) := by
  simp only [connGrothendieckDiagCod, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
/--
The twisted arrow morphism `TwMorphCod` for `(a ≫ b) ≫ c` equals the one for `a ≫ b ≫ c`
composed with eqToHom.
-/
lemma connGrothendieckTwMorphCod_assoc (tw : TwistedArrow' C)
    {b' b'' b''' : C} (a : twCod' tw ⟶ b') (b : b' ⟶ b'') (c : b'' ⟶ b''') :
    connGrothendieckTwMorphCod C tw ((a ≫ b) ≫ c) =
    connGrothendieckTwMorphCod C tw (a ≫ b ≫ c) ≫
    eqToHom (connGrothendieckDiagCod_assoc C tw a b c).symm := by
  apply twHom'_ext
  · simp only [connGrothendieckTwMorphCod, twDomArr'_comp, twHomMk'_domArr, twDomArr'_eqToHom]
    simp only [connGrothendieckDiagCod, twObjMk'_dom, eqToHom_refl, Category.comp_id]
  · simp only [connGrothendieckTwMorphCod, twCodArr'_comp, twHomMk'_codArr,
      twCodArr'_eqToHom, Category.comp_id, Category.assoc, eqToHom_refl]

/--
The `W3` for `(f ≫ g) ≫ h` is the same as `W3` for `f ≫ (g ≫ h)`.
Both equal `connGrothendieckDiagCod w.arrow (f.codArr ≫ g.codArr ≫ h.codArr)`.
-/
lemma connGrothendieckW3_assoc {w x y z : ConnGrothendieckObj C F}
    (f : ConnGrothendieckHom C F w x) (g : ConnGrothendieckHom C F x y)
    (h : ConnGrothendieckHom C F y z) :
    connGrothendieckW3 C F (connGrothendieckComp C F f g) h =
    connGrothendieckW3 C F f (connGrothendieckComp C F g h) := by
  simp only [connGrothendieckW3, connGrothendieckComp, connGrothendieckDiagCod, Category.assoc]

/--
W1 of the composition (f≫g) equals W3(f,g).
-/
lemma connGrothendieckW1_comp {w x y : ConnGrothendieckObj C F}
    (f : ConnGrothendieckHom C F w x) (g : ConnGrothendieckHom C F x y) :
    connGrothendieckW1 C F (connGrothendieckComp C F f g) = connGrothendieckW3 C F f g := by
  simp only [connGrothendieckW1, connGrothendieckW3, connGrothendieckComp, connGrothendieckDiagCod]

/--
morphW1W3 for (f≫g) composed with h simply extends by h.codArr.
The source is W1(f≫g) = W3(f,g), target is W3((f≫g),h).
-/
lemma connGrothendieckMorphW1W3_comp_codArr {w x y z : ConnGrothendieckObj C F}
    (f : ConnGrothendieckHom C F w x) (g : ConnGrothendieckHom C F x y)
    (h : ConnGrothendieckHom C F y z) :
    twCodArr' (connGrothendieckMorphW1W3 C F (connGrothendieckComp C F f g) h) = h.codArr := by
  simp only [connGrothendieckMorphW1W3, connGrothendieckComp, twHomMk'_codArr]

/--
morphW1W3 for (f≫g) composed with h has identity on domain.
-/
lemma connGrothendieckMorphW1W3_comp_domArr {w x y z : ConnGrothendieckObj C F}
    (f : ConnGrothendieckHom C F w x) (g : ConnGrothendieckHom C F x y)
    (h : ConnGrothendieckHom C F y z) :
    twDomArr' (connGrothendieckMorphW1W3 C F (connGrothendieckComp C F f g) h) = 𝟙 _ := by
  simp only [connGrothendieckMorphW1W3, connGrothendieckComp, twHomMk'_domArr]

/--
The "big diagonal" W4 for three composable morphisms.
This is the common target of all transports in the associativity proof.
-/
abbrev connGrothendieckW4 {w x y z : ConnGrothendieckObj C F}
    (f : ConnGrothendieckHom C F w x) (g : ConnGrothendieckHom C F x y)
    (h : ConnGrothendieckHom C F y z) : TwistedArrow' C :=
  connGrothendieckDiagCod C w.arrow (f.codArr ≫ g.codArr ≫ h.codArr)

/--
W3((f≫g), h) equals W4.
-/
lemma connGrothendieckW3_comp_left_eq_W4 {w x y z : ConnGrothendieckObj C F}
    (f : ConnGrothendieckHom C F w x) (g : ConnGrothendieckHom C F x y)
    (h : ConnGrothendieckHom C F y z) :
    connGrothendieckW3 C F (connGrothendieckComp C F f g) h = connGrothendieckW4 C F f g h := by
  simp only [connGrothendieckW3, connGrothendieckW4, connGrothendieckComp,
    connGrothendieckDiagCod, Category.assoc]

/--
W3(f, (g≫h)) equals W4.
-/
lemma connGrothendieckW3_comp_right_eq_W4 {w x y z : ConnGrothendieckObj C F}
    (f : ConnGrothendieckHom C F w x) (g : ConnGrothendieckHom C F x y)
    (h : ConnGrothendieckHom C F y z) :
    connGrothendieckW3 C F f (connGrothendieckComp C F g h) = connGrothendieckW4 C F f g h := by
  simp only [connGrothendieckW3, connGrothendieckW4, connGrothendieckComp,
    connGrothendieckDiagCod]

set_option backward.isDefEq.respectTransparency false in
/--
The transport from W1(f) to W4 can be factored as morphW1W3(f,g) followed by
the extension to W4. This is the path used in both LHS and RHS for f.fiberMorph.
-/
def connGrothendieckMorphW1W4 {w x y z : ConnGrothendieckObj C F}
    (f : ConnGrothendieckHom C F w x) (g : ConnGrothendieckHom C F x y)
    (h : ConnGrothendieckHom C F y z) :
    connGrothendieckW1 C F f ⟶ connGrothendieckW4 C F f g h :=
  twHomMk' (𝟙 _) (g.codArr ≫ h.codArr) (by
    simp only [connGrothendieckDiagCod, twObjMk'_arr, Category.id_comp, Category.assoc])

set_option backward.isDefEq.respectTransparency false in
/--
morphW1W3(f,g) followed by extension to W4 equals morphW1W4.
-/
lemma connGrothendieckMorphW1W3_extend_W4 {w x y z : ConnGrothendieckObj C F}
    (f : ConnGrothendieckHom C F w x) (g : ConnGrothendieckHom C F x y)
    (h : ConnGrothendieckHom C F y z) :
    connGrothendieckMorphW1W3 C F f g ≫
    (twHomMk' (𝟙 _) h.codArr (by
      simp only [connGrothendieckDiagCod, twObjMk'_arr, Category.id_comp, Category.assoc]) :
      connGrothendieckW3 C F f g ⟶ connGrothendieckW4 C F f g h) =
    connGrothendieckMorphW1W4 C F f g h := by
  apply twHom'_ext
  · simp only [connGrothendieckMorphW1W3, connGrothendieckMorphW1W4, twDomArr'_comp,
      twHomMk'_domArr, Category.comp_id]
  · simp only [connGrothendieckMorphW1W3, connGrothendieckMorphW1W4, twCodArr'_comp,
      twHomMk'_codArr]

/--
The transport from W2(h) to W4 factors through W3(g,h).
This is used for h.fiberMorph in both compositions.
-/
def connGrothendieckMorphW2W4 {w x y z : ConnGrothendieckObj C F}
    (f : ConnGrothendieckHom C F w x) (g : ConnGrothendieckHom C F x y)
    (h : ConnGrothendieckHom C F y z) :
    connGrothendieckW2 C F h ⟶ connGrothendieckW4 C F f g h :=
  connGrothendieckTwMorphDom C (connGrothendieckW2 C F h) (f.domArr ≫ g.domArr) ≫
    eqToHom (by
      simp only [connGrothendieckDiagDom, connGrothendieckDiagCod, twObjMk'_arr]
      congr 1
      calc (f.domArr ≫ g.domArr) ≫ twArr' y.arrow ≫ h.codArr
          = f.domArr ≫ g.domArr ≫ twArr' y.arrow ≫ h.codArr := by rw [Category.assoc]
        _ = f.domArr ≫ (g.domArr ≫ twArr' y.arrow) ≫ h.codArr := by rw [Category.assoc]
        _ = f.domArr ≫ (twArr' x.arrow ≫ g.codArr) ≫ h.codArr := by rw [← g.square_comm]
        _ = f.domArr ≫ twArr' x.arrow ≫ g.codArr ≫ h.codArr := by rw [Category.assoc]
        _ = (f.domArr ≫ twArr' x.arrow) ≫ g.codArr ≫ h.codArr := by rw [Category.assoc]
        _ = (twArr' w.arrow ≫ f.codArr) ≫ g.codArr ≫ h.codArr := by rw [← f.square_comm]
        _ = twArr' w.arrow ≫ f.codArr ≫ g.codArr ≫ h.codArr := by rw [Category.assoc])

set_option backward.isDefEq.respectTransparency false in
/--
morphW1W3(f,g) ≫ morphW1W3((f≫g),h) = morphW1W4(f,g,h).
This is the coherence for transporting f.fiberMorph in the LHS associativity path.
-/
lemma connGrothendieckMorphW1W3_comp_left {w x y z : ConnGrothendieckObj C F}
    (f : ConnGrothendieckHom C F w x) (g : ConnGrothendieckHom C F x y)
    (h : ConnGrothendieckHom C F y z) :
    connGrothendieckMorphW1W3 C F f g ≫
    eqToHom (connGrothendieckW1_comp C F f g).symm ≫
    connGrothendieckMorphW1W3 C F (connGrothendieckComp C F f g) h ≫
    eqToHom (connGrothendieckW3_comp_left_eq_W4 C F f g h) =
    connGrothendieckMorphW1W4 C F f g h := by
  apply twHom'_ext
  · simp only [connGrothendieckMorphW1W3, connGrothendieckMorphW1W4, connGrothendieckComp,
      twDomArr'_comp, twHomMk'_domArr, twDomArr'_eqToHom, Category.comp_id]
    rw [eqToHom_trans, eqToHom_refl]
  · simp only [connGrothendieckMorphW1W3, connGrothendieckMorphW1W4, connGrothendieckComp,
      twCodArr'_comp, twHomMk'_codArr, twCodArr'_eqToHom]
    simp only [Category.comp_id, eqToHom_refl, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
/--
morphW1W3(f,(g≫h)) ≫ eqToHom = morphW1W4(f,g,h).
This is the coherence for transporting f.fiberMorph in the RHS associativity path.
-/
lemma connGrothendieckMorphW1W3_comp_right {w x y z : ConnGrothendieckObj C F}
    (f : ConnGrothendieckHom C F w x) (g : ConnGrothendieckHom C F x y)
    (h : ConnGrothendieckHom C F y z) :
    connGrothendieckMorphW1W3 C F f (connGrothendieckComp C F g h) ≫
    eqToHom (connGrothendieckW3_comp_right_eq_W4 C F f g h) =
    connGrothendieckMorphW1W4 C F f g h := by
  apply twHom'_ext
  · simp only [connGrothendieckMorphW1W3, connGrothendieckMorphW1W4, connGrothendieckComp,
      twHomMk'_domArr, Category.comp_id, eqToHom_refl]
  · simp only [connGrothendieckMorphW1W3, connGrothendieckMorphW1W4, connGrothendieckComp,
      twCodArr'_comp, twHomMk'_codArr, twCodArr'_eqToHom]
    simp only [Category.comp_id, eqToHom_refl]

set_option backward.isDefEq.respectTransparency false in
/--
morphW2W3((f≫g),h) ≫ eqToHom = morphW2W4(f,g,h).
This is the coherence for transporting h.fiberMorph in the LHS associativity path.
-/
lemma connGrothendieckMorphW2W3_comp_left {w x y z : ConnGrothendieckObj C F}
    (f : ConnGrothendieckHom C F w x) (g : ConnGrothendieckHom C F x y)
    (h : ConnGrothendieckHom C F y z) :
    connGrothendieckMorphW2W3 C F (connGrothendieckComp C F f g) h ≫
    eqToHom (connGrothendieckW3_comp_left_eq_W4 C F f g h) =
    connGrothendieckMorphW2W4 C F f g h := by
  apply twHom'_ext
  · simp only [connGrothendieckMorphW2W3, connGrothendieckMorphW2W4, connGrothendieckComp,
      twDomArr'_comp, twDomArr'_eqToHom, connGrothendieckTwMorphDom, twHomMk'_domArr,
      eqToHom_refl, Category.id_comp]
  · simp only [connGrothendieckMorphW2W3, connGrothendieckMorphW2W4, connGrothendieckComp,
      twCodArr'_comp, twCodArr'_eqToHom, connGrothendieckTwMorphDom,
      Category.comp_id, eqToHom_refl, twHomMk'_codArr]

set_option backward.isDefEq.respectTransparency false in
/--
morphW2W3(g,h) ≫ morphW2W3(f,(g≫h)) ≫ eqToHom = morphW2W4(f,g,h).
This is the coherence for transporting h.fiberMorph in the RHS associativity path.
-/
lemma connGrothendieckMorphW2W3_comp_right {w x y z : ConnGrothendieckObj C F}
    (f : ConnGrothendieckHom C F w x) (g : ConnGrothendieckHom C F x y)
    (h : ConnGrothendieckHom C F y z) :
    connGrothendieckMorphW2W3 C F g h ≫
    eqToHom (connGrothendieckW1_comp C F g h).symm ≫
    connGrothendieckMorphW2W3 C F f (connGrothendieckComp C F g h) ≫
    eqToHom (connGrothendieckW3_comp_right_eq_W4 C F f g h) =
    connGrothendieckMorphW2W4 C F f g h := by
  apply twHom'_ext
  · simp only [connGrothendieckMorphW2W3, connGrothendieckMorphW2W4, connGrothendieckComp,
      twDomArr'_comp, twDomArr'_eqToHom, connGrothendieckTwMorphDom, twHomMk'_domArr,
      eqToHom_refl, Category.id_comp, Category.comp_id, Category.assoc]
  · simp only [connGrothendieckMorphW2W3, connGrothendieckMorphW2W4, connGrothendieckComp,
      twCodArr'_comp, twCodArr'_eqToHom, connGrothendieckTwMorphDom,
      Category.comp_id, eqToHom_refl, twHomMk'_codArr, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
/--
The middle coherence: morphW2W3(f,g) ≫ morphW1W3((f≫g),h) = morphW1W3(g,h) ≫ morphW2W3(f,(g≫h)).
Both paths take W1(g) to W4. This is used for g.fiberMorph.
-/
lemma connGrothendieckMorphMiddle_coherence {w x y z : ConnGrothendieckObj C F}
    (f : ConnGrothendieckHom C F w x) (g : ConnGrothendieckHom C F x y)
    (h : ConnGrothendieckHom C F y z) :
    connGrothendieckMorphW2W3 C F f g ≫
    eqToHom (connGrothendieckW1_comp C F f g).symm ≫
    connGrothendieckMorphW1W3 C F (connGrothendieckComp C F f g) h ≫
    eqToHom (connGrothendieckW3_comp_left_eq_W4 C F f g h) =
    connGrothendieckMorphW1W3 C F g h ≫
    eqToHom (connGrothendieckW1_comp C F g h).symm ≫
    connGrothendieckMorphW2W3 C F f (connGrothendieckComp C F g h) ≫
    eqToHom (connGrothendieckW3_comp_right_eq_W4 C F f g h) := by
  apply twHom'_ext
  · simp only [connGrothendieckMorphW2W3, connGrothendieckMorphW1W3, connGrothendieckComp,
      twDomArr'_comp, twDomArr'_eqToHom, connGrothendieckTwMorphDom, twHomMk'_domArr,
      eqToHom_refl, Category.id_comp, Category.comp_id]
  · simp only [connGrothendieckMorphW2W3, connGrothendieckMorphW1W3, connGrothendieckComp,
      twCodArr'_comp, twCodArr'_eqToHom, connGrothendieckTwMorphDom, twHomMk'_codArr,
      Category.comp_id, eqToHom_refl, Category.id_comp]

/--
The composed morphism has the same domArr as the composition of domArrs.
-/
@[simp]
lemma connGrothendieckComp_domArr {x y z : ConnGrothendieckObj C F}
    (m : ConnGrothendieckHom C F x y) (n : ConnGrothendieckHom C F y z) :
    (connGrothendieckComp C F m n).domArr = m.domArr ≫ n.domArr := rfl

/--
The composed morphism has the same codArr as the composition of codArrs.
-/
@[simp]
lemma connGrothendieckComp_codArr {x y z : ConnGrothendieckObj C F}
    (m : ConnGrothendieckHom C F x y) (n : ConnGrothendieckHom C F y z) :
    (connGrothendieckComp C F m n).codArr = m.codArr ≫ n.codArr := rfl

set_option backward.isDefEq.respectTransparency false in
/--
When two morphisms have the same domArr and codArr, their morphW1W3 morphisms
to any common third morphism are equal.
-/
lemma connGrothendieckMorphW1W3_irrel_fiberMorph {x y z : ConnGrothendieckObj C F}
    (m m' : ConnGrothendieckHom C F x y) (n : ConnGrothendieckHom C F y z)
    (_hDom : m.domArr = m'.domArr) (hCod : m.codArr = m'.codArr) :
    connGrothendieckMorphW1W3 C F m n =
    eqToHom (by simp only [connGrothendieckW1, connGrothendieckDiagCod]; rw [hCod]) ≫
    connGrothendieckMorphW1W3 C F m' n ≫
    eqToHom (by simp only [connGrothendieckW3, connGrothendieckDiagCod]; rw [hCod]) := by
  apply twHom'_ext
  · simp only [connGrothendieckMorphW1W3, twDomArr'_comp, twHomMk'_domArr,
      twDomArr'_eqToHom, eqToHom_refl, Category.comp_id]
  · simp only [connGrothendieckMorphW1W3, twCodArr'_comp, twHomMk'_codArr,
      twCodArr'_eqToHom, Category.comp_id, eqToHom_refl, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
/--
When two morphisms have the same domArr and codArr, their morphW2W3 morphisms
from any common first morphism are equal.
-/
lemma connGrothendieckMorphW2W3_irrel_fiberMorph {x y z : ConnGrothendieckObj C F}
    (m : ConnGrothendieckHom C F x y) (n n' : ConnGrothendieckHom C F y z)
    (_hDom : n.domArr = n'.domArr) (hCod : n.codArr = n'.codArr) :
    connGrothendieckMorphW2W3 C F m n =
    eqToHom (by simp only [connGrothendieckW2, connGrothendieckDiagCod]; rw [hCod]) ≫
    connGrothendieckMorphW2W3 C F m n' ≫
    eqToHom (by simp only [connGrothendieckW3, connGrothendieckDiagCod]; rw [hCod]) := by
  apply twHom'_ext
  · simp only [connGrothendieckMorphW2W3, twDomArr'_comp, twDomArr'_eqToHom,
      connGrothendieckTwMorphDom, twHomMk'_domArr, Category.id_comp, eqToHom_refl,
      Category.comp_id]
  · simp only [connGrothendieckMorphW2W3, twCodArr'_comp, twCodArr'_eqToHom,
      connGrothendieckTwMorphDom, twHomMk'_codArr, Category.comp_id, eqToHom_refl]

set_option backward.isDefEq.respectTransparency false in
/--
DiagCod composed with itself equals DiagCod with composed arrows.
-/
@[simp]
lemma connGrothendieckDiagCod_comp (tw : TwistedArrow' C)
    {b' b'' : C} (a : twCod' tw ⟶ b') (b : b' ⟶ b'') :
    connGrothendieckDiagCod C (connGrothendieckDiagCod C tw a) b =
    connGrothendieckDiagCod C tw (a ≫ b) := by
  simp only [connGrothendieckDiagCod, twObjMk'_arr, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
/--
The composition of two TwMorphCod morphisms equals a single TwMorphCod with composed arrows.
-/
lemma connGrothendieckTwMorphCod_comp (tw : TwistedArrow' C)
    {b' b'' : C} (a : twCod' tw ⟶ b') (b : b' ⟶ b'') :
    connGrothendieckTwMorphCod C tw a ≫
    connGrothendieckTwMorphCod C (connGrothendieckDiagCod C tw a) b =
    connGrothendieckTwMorphCod C tw (a ≫ b) ≫
    eqToHom (connGrothendieckDiagCod_comp C tw a b).symm := by
  apply twHom'_ext
  · simp only [connGrothendieckTwMorphCod, connGrothendieckDiagCod, twDomArr'_comp,
      twHomMk'_domArr, twDomArr'_eqToHom, eqToHom_refl, Category.comp_id]
  · simp only [connGrothendieckTwMorphCod, connGrothendieckDiagCod, twCodArr'_comp,
      twHomMk'_codArr, twCodArr'_eqToHom, eqToHom_refl, Category.comp_id]

/--
The fiber category for the composed diagonal equals the fiber category for the
nested diagonal application.
-/
lemma connGrothendieckFiberCat_comp (tw : TwistedArrow' C)
    {b' b'' : C} (a : twCod' tw ⟶ b') (b : b' ⟶ b'') :
    F.obj (connGrothendieckDiagCod C (connGrothendieckDiagCod C tw a) b) =
    F.obj (connGrothendieckDiagCod C tw (a ≫ b)) :=
  congrArg F.obj (connGrothendieckDiagCod_comp C tw a b)

/--
Applying F.map to the composition of TwMorphCod morphisms gives a functor
that equals F.map of the single TwMorphCod composed with eqToHom.
-/
lemma connGrothendieckFmap_TwMorphCod_comp (tw : TwistedArrow' C)
    {b' b'' : C} (a : twCod' tw ⟶ b') (b : b' ⟶ b'') :
    F.map (connGrothendieckTwMorphCod C tw a ≫
           connGrothendieckTwMorphCod C (connGrothendieckDiagCod C tw a) b) =
    F.map (connGrothendieckTwMorphCod C tw (a ≫ b)) ≫
    eqToHom (connGrothendieckFiberCat_comp C F tw a b).symm := by
  rw [connGrothendieckTwMorphCod_comp, Functor.map_comp, eqToHom_map]

/--
The source of a fiber morphism transported via nested TwMorphCod maps equals
the source transported via the single composed TwMorphCod (after eqToHom).
-/
lemma connGrothendieckTwMorphCod_map_comp_src (tw : TwistedArrow' C)
    {b' b'' : C} (a : twCod' tw ⟶ b') (b : b' ⟶ b'') (src : F.obj tw) :
    (eqToHom (connGrothendieckFiberCat_comp C F tw a b)).toFunctor.obj
      ((F.map (connGrothendieckTwMorphCod C
        (connGrothendieckDiagCod C tw a) b)).toFunctor.obj
        ((F.map (connGrothendieckTwMorphCod C tw a)).toFunctor.obj src)) =
    (F.map (connGrothendieckTwMorphCod C tw (a ≫ b))).toFunctor.obj src := by
  have hFmapComp : F.map (connGrothendieckTwMorphCod C tw a) ≫
      F.map (connGrothendieckTwMorphCod C (connGrothendieckDiagCod C tw a) b) =
      F.map (connGrothendieckTwMorphCod C tw (a ≫ b)) ≫
      eqToHom (connGrothendieckFiberCat_comp C F tw a b).symm := by
    rw [← Functor.map_comp, connGrothendieckTwMorphCod_comp, Functor.map_comp, eqToHom_map]
  calc (eqToHom (connGrothendieckFiberCat_comp C F tw a b)).toFunctor.obj
        ((F.map (connGrothendieckTwMorphCod C
          (connGrothendieckDiagCod C tw a) b)).toFunctor.obj
          ((F.map (connGrothendieckTwMorphCod C tw a)).toFunctor.obj src))
      = ((F.map (connGrothendieckTwMorphCod C tw a) ≫
          F.map (connGrothendieckTwMorphCod C (connGrothendieckDiagCod C tw a) b) ≫
          eqToHom (connGrothendieckFiberCat_comp C F tw a b))).toFunctor.obj src := by
          simp only [Cat.Hom.comp_toFunctor, Functor.comp_obj]
    _ = (((F.map (connGrothendieckTwMorphCod C tw a) ≫
          F.map (connGrothendieckTwMorphCod C (connGrothendieckDiagCod C tw a) b)) ≫
          eqToHom (connGrothendieckFiberCat_comp C F tw a b))).toFunctor.obj src := by
        simp only [Category.assoc]
    _ = (((F.map (connGrothendieckTwMorphCod C tw (a ≫ b)) ≫
          eqToHom (connGrothendieckFiberCat_comp C F tw a b).symm) ≫
          eqToHom (connGrothendieckFiberCat_comp C F tw a b))).toFunctor.obj src := by
        rw [hFmapComp]
    _ = ((F.map (connGrothendieckTwMorphCod C tw (a ≫ b)) ≫
          eqToHom (connGrothendieckFiberCat_comp C F tw a b).symm ≫
          eqToHom (connGrothendieckFiberCat_comp C F tw a b))).toFunctor.obj src := by
        simp only [Category.assoc]
    _ = ((F.map (connGrothendieckTwMorphCod C tw (a ≫ b)) ≫ 𝟙 _)).toFunctor.obj src := by
        simp only [eqToHom_trans, eqToHom_refl]
    _ = (F.map (connGrothendieckTwMorphCod C tw (a ≫ b))).toFunctor.obj src := by
        simp only [Category.comp_id]

/--
The target of a fiber morphism transported via nested TwMorphCod maps equals
the target transported via the single composed TwMorphCod (after eqToHom).
-/
lemma connGrothendieckTwMorphCod_map_comp_tgt (tw : TwistedArrow' C)
    {b' b'' : C} (a : twCod' tw ⟶ b') (b : b' ⟶ b'') (tgt : F.obj tw) :
    (eqToHom (connGrothendieckFiberCat_comp C F tw a b)).toFunctor.obj
      ((F.map (connGrothendieckTwMorphCod C (connGrothendieckDiagCod C tw a) b)).toFunctor.obj
        ((F.map (connGrothendieckTwMorphCod C tw a)).toFunctor.obj tgt)) =
    (F.map (connGrothendieckTwMorphCod C tw (a ≫ b))).toFunctor.obj tgt :=
  connGrothendieckTwMorphCod_map_comp_src C F tw a b tgt

/--
Given equal Cat morphisms, their toFunctor.map results
are HEq.
-/
private lemma connGrothendieck_Cat_hom_map_heq
    {X Y : Cat.{w₁, w₂}} {G H : X ⟶ Y}
    (h : G = H) {A B : X} (f : A ⟶ B) :
    G.toFunctor.map f ≍ H.toFunctor.map f := by
  subst h
  rfl

/--
Given category equality and piecewise morphism/object HEqs,
derives the full 6-composition HEq. Used to assemble the
three piecewise HEq proofs.
-/
private lemma connGrothendieck_assoc_core
    {D E : Cat.{w₁, w₂}}
    (hCatEq : D = E)
    {A1 A2 A3 A4 A5 A6 A7 : ↥D}
    {B1 B2 B3 B4 B5 B6 B7 : ↥E}
    (f1 : A1 ⟶ A2) (f2 : A3 ⟶ A4) (f3 : A5 ⟶ A6)
    (g1 : B1 ⟶ B2) (g2 : B3 ⟶ B4) (g3 : B5 ⟶ B6)
    (e1 : A2 = A3) (e2 : A4 = A5) (e3 : A6 = A7)
    (e1' : B2 = B3) (e2' : B4 = B5)
    (e3' : B6 = B7)
    (hf1 : f1 ≍ g1) (hf2 : f2 ≍ g2)
    (hf3 : f3 ≍ g3)
    (hA1B1 : A1 ≍ B1) (hA2B2 : A2 ≍ B2)
    (hA4B4 : A4 ≍ B4) (hA6B6 : A6 ≍ B6) :
    f1 ≫ eqToHom e1 ≫ f2 ≫ eqToHom e2 ≫
      f3 ≫ eqToHom e3 ≍
    g1 ≫ eqToHom e1' ≫ g2 ≫ eqToHom e2' ≫
      g3 ≫ eqToHom e3' := by
  subst hCatEq
  cases e1; cases e2; cases e3
  cases e1'; cases e2'; cases e3'
  simp only [eqToHom_refl, Category.id_comp,
    Category.comp_id]
  have eq1 : A1 = B1 := eq_of_heq hA1B1
  have eq2 : A2 = B2 := eq_of_heq hA2B2
  have eq4 : A4 = B4 := eq_of_heq hA4B4
  have eq6 : A6 = B6 := eq_of_heq hA6B6
  exact heq_comp eq1 eq2 eq6 hf1
    (heq_comp eq2 eq4 eq6 hf2 hf3)

/--
W1W3 composition at the TwistedArrow' level:
composing the W1W3 extension for (f,g) with W1W3 for
(fg,h) equals W1W3 for (f,gh) up to eqToHom.
-/
private lemma connGrothendieckMorphW1W3_comp_tw
    {w x y z : ConnGrothendieckObj C F}
    (f : ConnGrothendieckHom C F w x)
    (g : ConnGrothendieckHom C F x y)
    (h : ConnGrothendieckHom C F y z) :
    connGrothendieckMorphW1W3 C F f g ≫
    connGrothendieckMorphW1W3 C F
      (connGrothendieckComp C F f g) h =
    connGrothendieckMorphW1W3 C F f
      (connGrothendieckComp C F g h) ≫
    eqToHom (connGrothendieckW3_assoc C F f g h
      ).symm := by
  apply twHom'_ext
  · simp only [connGrothendieckMorphW1W3,
      connGrothendieckComp, twDomArr'_comp,
      twHomMk'_domArr, twDomArr'_eqToHom,
      Category.comp_id,
      connGrothendieckDiagCod, twObjMk'_dom,
      eqToHom_refl]
  · simp only [connGrothendieckMorphW1W3,
      connGrothendieckComp, twCodArr'_comp,
      twHomMk'_codArr, twCodArr'_eqToHom,
      connGrothendieckDiagCod,
      twObjMk'_cod, Category.comp_id, eqToHom_refl]

set_option backward.isDefEq.respectTransparency false in
/--
W2W3 composition at the TwistedArrow' level:
W2W3(fg,h) equals W2W3(g,h) composed with W2W3(f,gh)
up to eqToHom.
-/
private lemma connGrothendieckMorphW2W3_comp_tw
    {w x y z : ConnGrothendieckObj C F}
    (f : ConnGrothendieckHom C F w x)
    (g : ConnGrothendieckHom C F x y)
    (h : ConnGrothendieckHom C F y z) :
    connGrothendieckMorphW2W3 C F
      (connGrothendieckComp C F f g) h =
    connGrothendieckMorphW2W3 C F g h ≫
    connGrothendieckMorphW2W3 C F f
      (connGrothendieckComp C F g h) ≫
    eqToHom (connGrothendieckW3_assoc C F f g h
      ).symm := by
  apply twHom'_ext
  · simp only [connGrothendieckMorphW2W3,
      connGrothendieckComp, twDomArr'_comp,
      twDomArr'_eqToHom, connGrothendieckTwMorphDom,
      twHomMk'_domArr, connGrothendieckDiagCod,
      twObjMk'_dom, eqToHom_refl, Category.comp_id,
      Category.id_comp, Category.assoc]
  · simp only [connGrothendieckMorphW2W3,
      connGrothendieckComp, twCodArr'_comp,
      twCodArr'_eqToHom, connGrothendieckTwMorphDom,
      twHomMk'_codArr, connGrothendieckDiagCod,
      twObjMk'_cod, eqToHom_refl,
      Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
/--
Middle coherence at the TwistedArrow' level:
W2W3(f,g) composed with W1W3(fg,h) equals W1W3(g,h)
composed with W2W3(f,gh), up to eqToHom.
-/
private lemma connGrothendieckMorphMiddle_comp_tw
    {w x y z : ConnGrothendieckObj C F}
    (f : ConnGrothendieckHom C F w x)
    (g : ConnGrothendieckHom C F x y)
    (h : ConnGrothendieckHom C F y z) :
    connGrothendieckMorphW2W3 C F f g ≫
    connGrothendieckMorphW1W3 C F
      (connGrothendieckComp C F f g) h =
    connGrothendieckMorphW1W3 C F g h ≫
    connGrothendieckMorphW2W3 C F f
      (connGrothendieckComp C F g h) ≫
    eqToHom (connGrothendieckW3_assoc C F f g h
      ).symm := by
  apply twHom'_ext
  · simp only [connGrothendieckMorphW2W3,
      connGrothendieckMorphW1W3,
      connGrothendieckComp, twDomArr'_comp,
      twDomArr'_eqToHom, connGrothendieckTwMorphDom,
      twHomMk'_domArr, connGrothendieckDiagCod,
      twObjMk'_dom, eqToHom_refl, Category.comp_id,
      Category.id_comp]
  · simp only [connGrothendieckMorphW2W3,
      connGrothendieckMorphW1W3,
      connGrothendieckComp, twCodArr'_comp,
      twCodArr'_eqToHom, connGrothendieckTwMorphDom,
      twHomMk'_codArr, connGrothendieckDiagCod,
      twObjMk'_cod, eqToHom_refl, Category.comp_id,
      Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
/--
The fM piecewise HEq for associativity:
`F.map(W1W3(fg,h)).map(F.map(W1W3(f,g)).map(fM))`
is HEq to `F.map(W1W3(f,gh)).map(fM)`.
-/
private lemma connGrothendieckAssoc_fM_heq
    {w x y z : ConnGrothendieckObj C F}
    (f : ConnGrothendieckHom C F w x)
    (g : ConnGrothendieckHom C F x y)
    (h : ConnGrothendieckHom C F y z) :
    (F.map (connGrothendieckMorphW1W3 C F
        (connGrothendieckComp C F f g) h)
      ).toFunctor.map
      ((F.map (connGrothendieckMorphW1W3 C F f g)
        ).toFunctor.map f.fiberMorph) ≍
    (F.map (connGrothendieckMorphW1W3 C F f
        (connGrothendieckComp C F g h))
      ).toFunctor.map f.fiberMorph := by
  have h' :
      F.map (connGrothendieckMorphW1W3 C F f g) ≫
      F.map (connGrothendieckMorphW1W3 C F
        (connGrothendieckComp C F f g) h) =
      F.map (connGrothendieckMorphW1W3 C F f
        (connGrothendieckComp C F g h)) ≫
      eqToHom (congrArg F.obj
        (connGrothendieckW3_assoc C F f g h
          ).symm) := by
    rw [← F.map_comp,
      connGrothendieckMorphW1W3_comp_tw,
      F.map_comp, eqToHom_map]
  have step1 :
      (F.map (connGrothendieckMorphW1W3 C F
          (connGrothendieckComp C F f g) h)
        ).toFunctor.map
        ((F.map (connGrothendieckMorphW1W3 C F f g)
          ).toFunctor.map f.fiberMorph) =
      (F.map (connGrothendieckMorphW1W3 C F f g) ≫
        F.map (connGrothendieckMorphW1W3 C F
          (connGrothendieckComp C F f g) h)
        ).toFunctor.map f.fiberMorph := by
    simp only [Cat.Hom.comp_toFunctor,
      Functor.comp_map]
  rw [step1]
  exact HEq.trans
    (connGrothendieck_Cat_hom_map_heq h' _)
    (by simp only [Cat.Hom.comp_toFunctor,
          Functor.comp_map]
        exact Cat.eqToHom_map_heq _ _)

set_option backward.isDefEq.respectTransparency false in
/--
The gM piecewise HEq for associativity:
`F.map(W1W3(fg,h)).map(F.map(W2W3(f,g)).map(gM))`
is HEq to
`F.map(W2W3(f,gh)).map(F.map(W1W3(g,h)).map(gM))`.
-/
private lemma connGrothendieckAssoc_gM_heq
    {w x y z : ConnGrothendieckObj C F}
    (f : ConnGrothendieckHom C F w x)
    (g : ConnGrothendieckHom C F x y)
    (h : ConnGrothendieckHom C F y z) :
    (F.map (connGrothendieckMorphW1W3 C F
        (connGrothendieckComp C F f g) h)
      ).toFunctor.map
      ((F.map (connGrothendieckMorphW2W3 C F f g)
        ).toFunctor.map g.fiberMorph) ≍
    (F.map (connGrothendieckMorphW2W3 C F f
        (connGrothendieckComp C F g h))
      ).toFunctor.map
      ((F.map (connGrothendieckMorphW1W3 C F g h)
        ).toFunctor.map g.fiberMorph) := by
  have h' :
      F.map (connGrothendieckMorphW2W3 C F f g) ≫
      F.map (connGrothendieckMorphW1W3 C F
        (connGrothendieckComp C F f g) h) =
      F.map (connGrothendieckMorphW1W3 C F g h) ≫
      F.map (connGrothendieckMorphW2W3 C F f
        (connGrothendieckComp C F g h)) ≫
      eqToHom (congrArg F.obj
        (connGrothendieckW3_assoc C F f g h
          ).symm) := by
    rw [← F.map_comp,
      connGrothendieckMorphMiddle_comp_tw,
      F.map_comp, F.map_comp, eqToHom_map]
  have step1 :
      (F.map (connGrothendieckMorphW1W3 C F
          (connGrothendieckComp C F f g) h)
        ).toFunctor.map
        ((F.map (connGrothendieckMorphW2W3 C F f g)
          ).toFunctor.map g.fiberMorph) =
      (F.map (connGrothendieckMorphW2W3 C F f g) ≫
        F.map (connGrothendieckMorphW1W3 C F
          (connGrothendieckComp C F f g) h)
        ).toFunctor.map g.fiberMorph := by
    simp only [Cat.Hom.comp_toFunctor,
      Functor.comp_map]
  have step2 :
      (F.map (connGrothendieckMorphW2W3 C F f
          (connGrothendieckComp C F g h))
        ).toFunctor.map
        ((F.map (connGrothendieckMorphW1W3 C F g h)
          ).toFunctor.map g.fiberMorph) =
      (F.map (connGrothendieckMorphW1W3 C F g h) ≫
        F.map (connGrothendieckMorphW2W3 C F f
          (connGrothendieckComp C F g h))
        ).toFunctor.map g.fiberMorph := by
    simp only [Cat.Hom.comp_toFunctor,
      Functor.comp_map]
  rw [step1, step2]
  exact HEq.trans
    (connGrothendieck_Cat_hom_map_heq h' _)
    (by simp only [Cat.Hom.comp_toFunctor,
          Functor.comp_map]
        exact Cat.eqToHom_map_heq _ _)

/--
The hM piecewise HEq for associativity:
`F.map(W2W3(fg,h)).map(hM)` is HEq to
`F.map(W2W3(f,gh)).map(F.map(W2W3(g,h)).map(hM))`.
-/
private lemma connGrothendieckAssoc_hM_heq
    {w x y z : ConnGrothendieckObj C F}
    (f : ConnGrothendieckHom C F w x)
    (g : ConnGrothendieckHom C F x y)
    (h : ConnGrothendieckHom C F y z) :
    (F.map (connGrothendieckMorphW2W3 C F
        (connGrothendieckComp C F f g) h)
      ).toFunctor.map h.fiberMorph ≍
    (F.map (connGrothendieckMorphW2W3 C F f
        (connGrothendieckComp C F g h))
      ).toFunctor.map
      ((F.map (connGrothendieckMorphW2W3 C F g h)
        ).toFunctor.map h.fiberMorph) := by
  have h' :
      F.map (connGrothendieckMorphW2W3 C F
        (connGrothendieckComp C F f g) h) =
      F.map (connGrothendieckMorphW2W3 C F g h) ≫
      F.map (connGrothendieckMorphW2W3 C F f
        (connGrothendieckComp C F g h)) ≫
      eqToHom (congrArg F.obj
        (connGrothendieckW3_assoc C F f g h
          ).symm) := by
    rw [connGrothendieckMorphW2W3_comp_tw,
      F.map_comp, F.map_comp, eqToHom_map]
  exact HEq.trans
    (connGrothendieck_Cat_hom_map_heq h' _)
    (by simp only [Cat.Hom.comp_toFunctor,
          Functor.comp_map]
        exact Cat.eqToHom_map_heq _ _)

/--
Given Cat morphisms `L = R ≫ eqToHom η`, applying
`.toFunctor.obj` to both sides gives HEq of the
resulting objects (across the category equality η).
-/
private lemma connGrothendieck_obj_heq_via_eqToHom
    {A B D : Cat.{w₁, w₂}}
    {L : A ⟶ D} {R : A ⟶ B}
    {η : B = D}
    (hEq : L = R ≫ eqToHom η)
    (X : ↥A) :
    L.toFunctor.obj X ≍
    R.toFunctor.obj X := by
  have step : L.toFunctor.obj X =
      (eqToHom η).toFunctor.obj
        (R.toFunctor.obj X) := by
    rw [hEq]; rfl
  exact HEq.trans (heq_of_eq step)
    (eqToHom_obj_heq _ _ η _)

/--
The fiber component of associativity: the fiber morphisms
are HEq under the two different associations.
-/
private lemma connGrothendieckComp_assoc_fiber
    {w x y z : ConnGrothendieckObj C F}
    (f : ConnGrothendieckHom C F w x)
    (g : ConnGrothendieckHom C F x y)
    (h : ConnGrothendieckHom C F y z) :
    (connGrothendieckComp C F
      (connGrothendieckComp C F f g) h).fiberMorph ≍
    (connGrothendieckComp C F f
      (connGrothendieckComp C F g h)).fiberMorph := by
  simp only [connGrothendieckComp, Functor.map_comp,
    Category.assoc, eqToHom_trans, eqToHom_trans_assoc,
    eqToHom_map]
  apply HEq.trans (eqToHom_comp_heq _ _)
  apply HEq.trans _ (HEq.symm (eqToHom_comp_heq _ _))
  have hW1W3 :
      F.map (connGrothendieckMorphW1W3 C F f g) ≫
      F.map (connGrothendieckMorphW1W3 C F
        (connGrothendieckComp C F f g) h) =
      F.map (connGrothendieckMorphW1W3 C F f
        (connGrothendieckComp C F g h)) ≫
      eqToHom (congrArg F.obj
        (connGrothendieckW3_assoc C F f g h
          ).symm) := by
    rw [← F.map_comp,
      connGrothendieckMorphW1W3_comp_tw,
      F.map_comp, eqToHom_map]
  have hMiddle :
      F.map (connGrothendieckMorphW2W3 C F f g) ≫
      F.map (connGrothendieckMorphW1W3 C F
        (connGrothendieckComp C F f g) h) =
      (F.map (connGrothendieckMorphW1W3 C F g h) ≫
      F.map (connGrothendieckMorphW2W3 C F f
        (connGrothendieckComp C F g h))) ≫
      eqToHom (congrArg F.obj
        (connGrothendieckW3_assoc C F f g h
          ).symm) := by
    rw [← F.map_comp,
      connGrothendieckMorphMiddle_comp_tw,
      F.map_comp, F.map_comp, eqToHom_map,
      Category.assoc]
  have hW2W3 :
      F.map (connGrothendieckMorphW2W3 C F
        (connGrothendieckComp C F f g) h) =
      (F.map (connGrothendieckMorphW2W3 C F g h) ≫
      F.map (connGrothendieckMorphW2W3 C F f
        (connGrothendieckComp C F g h))) ≫
      eqToHom (congrArg F.obj
        (connGrothendieckW3_assoc C F f g h
          ).symm) := by
    rw [connGrothendieckMorphW2W3_comp_tw,
      F.map_comp, F.map_comp, eqToHom_map,
      Category.assoc]
  exact connGrothendieck_assoc_core
    (congrArg F.obj
      (connGrothendieckW3_assoc C F f g h))
    _ _ _ _ _ _ _ _ _ _ _ _
    (connGrothendieckAssoc_fM_heq C F f g h)
    (connGrothendieckAssoc_gM_heq C F f g h)
    (connGrothendieckAssoc_hM_heq C F f g h)
    (connGrothendieck_obj_heq_via_eqToHom
      hW1W3 _)
    (connGrothendieck_obj_heq_via_eqToHom
      hW1W3 _)
    (connGrothendieck_obj_heq_via_eqToHom
      hMiddle _)
    (connGrothendieck_obj_heq_via_eqToHom
      hW2W3 _)

/--
Associativity of composition in the connected Grothendieck
construction.
-/
theorem connGrothendieckComp_assoc
    {w x y z : ConnGrothendieckObj C F}
    (f : ConnGrothendieckHom C F w x)
    (g : ConnGrothendieckHom C F x y)
    (h : ConnGrothendieckHom C F y z) :
    connGrothendieckComp C F
      (connGrothendieckComp C F f g) h =
    connGrothendieckComp C F f
      (connGrothendieckComp C F g h) := by
  apply connGrothendieckHom_ext
  · exact Category.assoc _ _ _
  · exact Category.assoc _ _ _
  · exact connGrothendieckComp_assoc_fiber C F f g h

/--
Category data for the connected Grothendieck construction,
packaging the operations and laws.
-/
def connGrothendieckCategoryData :
    CategoryData (ConnGrothendieckObj C F)
      (connGrothendieckHomSet C F) where
  toCategoryOps := connGrothendieckCategoryOps C F
  laws := {
    assoc := connGrothendieckComp_assoc C F
    id_laws := {
      id_comp := connGrothendieckId_comp C F
      comp_id := connGrothendieckComp_id C F
    }
  }

/--
Category instance for the connected Grothendieck
construction `E(F)` over `Arr(C)`.
-/
instance connGrothendieckCategory :
    Category (ConnGrothendieckObj C F) :=
  CategoryOfData (connGrothendieckCategoryData C F)

end ConnectedGrothendieckCategory

section ConnectedGrothendieckProjection

/-! ## The projection functor to the arrow category -/

variable (F : TwistedArrow' C ⥤ Cat.{w₁, w₂})

/--
Convert a twisted arrow object to an Arrow object.
-/
def connGrothendieckObjToArrow (x : ConnGrothendieckObj C F) : Arrow C :=
  Arrow.mk (twArr' x.arrow)

/--
Convert a connected Grothendieck morphism to an Arrow morphism.
-/
def connGrothendieckHomToArrow {x y : ConnGrothendieckObj C F}
    (f : ConnGrothendieckHom C F x y) :
    connGrothendieckObjToArrow C F x ⟶ connGrothendieckObjToArrow C F y :=
  Arrow.homMk f.domArr f.codArr f.square_comm.symm

/--
The projection preserves identity morphisms.
-/
theorem connGrothendieckHomToArrow_id (x : ConnGrothendieckObj C F) :
    connGrothendieckHomToArrow C F (connGrothendieckId C F x) =
    𝟙 (connGrothendieckObjToArrow C F x) := by
  simp only [connGrothendieckHomToArrow, connGrothendieckId, connGrothendieckObjToArrow]
  apply Arrow.hom_ext <;> rfl

/--
The projection preserves composition.
-/
theorem connGrothendieckHomToArrow_comp {x y z : ConnGrothendieckObj C F}
    (f : ConnGrothendieckHom C F x y) (g : ConnGrothendieckHom C F y z) :
    connGrothendieckHomToArrow C F (connGrothendieckComp C F f g) =
    connGrothendieckHomToArrow C F f ≫ connGrothendieckHomToArrow C F g := by
  simp only [connGrothendieckHomToArrow, connGrothendieckComp, connGrothendieckObjToArrow]
  apply Arrow.hom_ext <;> rfl

end ConnectedGrothendieckProjection

section NestedGrothendieckApproach

/-!
## Nested Grothendieck Construction Approach

The connected Grothendieck construction can be expressed as a composition of
two standard Grothendieck constructions:

```text
E(F) = ∫_C H
```

where `H : C → Cat` is defined by `H(b) = ∫_{(Over b)^op} (ι_b ⋙ F)` and
`ι_b : (Over b)^op → Tw(C)` is the fiber inclusion functor.

This decomposition follows from the fact that `Tw(C)` is a Grothendieck
opfibration over `C` via the codomain functor, with fiber `(Over b)^op`.
-/

variable (F : TwistedArrow' C ⥤ Cat.{v, u})

/--
The restriction of `F : Tw(C) → Cat` to the fiber over `b`.
-/
def restrictToFiber (b : C) : (Over b)ᵒᵖ' ⥤ Cat.{v, u} :=
  overOpToTwistedArrow C b ⋙ F

/--
The restriction of `F : Tw(C) → Cat` to the fiber over `b`, with oppositized
fiber categories. This ensures that morphisms in `Grothendieck (restrictToFiberOp b)`
have the correct covariant direction for the connected Grothendieck construction.
-/
def restrictToFiberOp (b : C) : (Over b)ᵒᵖ' ⥤ Cat.{v, u} :=
  restrictToFiber C F b ⋙ Cat.opFunctor'

/--
The inner fiber category using `GrothendieckContra'`.

This uses the contravariant Grothendieck construction over `(Over b)ᵒᵖ'`, which
produces morphisms where:
- `f.base : x.base ⟶ y.base` in `Over b` (covariant)
- `f.base.left : x.base.left ⟶ y.base.left` (covariant - this is domArr!)
- `f.fiber : x.fiber ⟶ transported(y.fiber)` (covariant - this is fiberMorph!)

The connected Grothendieck construction uses one contravariant and
one covariant construction.
-/
def innerFiberContra (b : C) : Type _ :=
  GrothendieckContra' (restrictToFiber C F b)

instance innerFiberContraCategory (b : C) : Category (innerFiberContra C F b) :=
  GrothendieckContra'.GrothendieckContraInst'

/--
The functor that transports fiber elements along a base morphism `β : b ⟶ d`.
For `ov : Over b` and `x : F.obj (twObjMk' ov.hom)`, this produces an element
of `F.obj (twObjMk' (ov.hom ≫ β))`.
-/
def fiberTransport {b d : C} (β : b ⟶ d) (ov : Over b) :
    (restrictToFiber C F b).obj ov ⥤ (restrictToFiber C F d).obj ((Over.map β).obj ov) :=
  (F.map (fiberTransportTwMorph C β ov)).toFunctor

/--
The functor that transports fiber elements along a base morphism `β : b ⟶ d`,
for the oppositized fiber categories. This is the result of applying
`Cat.opFunctor'.map` to `fiberTransport`.
-/
def fiberTransportOp {b d : C} (β : b ⟶ d) (ov : Over b) :
    (restrictToFiberOp C F b).obj ov ⥤ (restrictToFiberOp C F d).obj ((Over.map β).obj ov) :=
  (Cat.opFunctor'.map (fiberTransport C F β ov).toCatHom).toFunctor

/--
The object mapping for the transition functor between fibers.
Given `x : Grothendieck (restrictToFiber F b)`, produces an object in
`Grothendieck (restrictToFiber F d)`.
-/
def fiberFunctorTransitionObj {b d : C} (β : b ⟶ d)
    (x : Grothendieck (restrictToFiber C F b)) :
    Grothendieck (restrictToFiber C F d) :=
  ⟨(Over.map β).obj x.base, (fiberTransport C F β x.base).obj x.fiber⟩

set_option backward.isDefEq.respectTransparency false in
/--
Functor-level naturality: fiber transport composed with restriction mapping
equals restriction mapping followed by fiber transport.
-/
theorem fiberTransport_functor_naturality {b d : C} (β : b ⟶ d)
    {ov ov' : (Over b)ᵒᵖ'} (α : ov ⟶ ov') :
    ((restrictToFiber C F b).map α).toFunctor ⋙ fiberTransport C F β ov' =
    fiberTransport C F β ov ⋙ ((restrictToFiber C F d).map ((Over.map β).map α)).toFunctor := by
  simp only [restrictToFiber, fiberTransport, Functor.comp_map]
  have h := fiberTransport_naturality C β α
  have step : (F.map ((overOpToTwistedArrow C b).map α) ≫
          F.map (fiberTransportTwMorph C β ov')).toFunctor =
      (F.map (fiberTransportTwMorph C β ov) ≫
          F.map ((overOpToTwistedArrow C d).map ((Over.map β).map α))).toFunctor := by
    calc (F.map ((overOpToTwistedArrow C b).map α) ≫
            F.map (fiberTransportTwMorph C β ov')).toFunctor
        = (F.map ((overOpToTwistedArrow C b).map α ≫ fiberTransportTwMorph C β ov')).toFunctor := by
            simp only [Functor.map_comp]
      _ = (F.map (fiberTransportTwMorph C β ov ≫
            (overOpToTwistedArrow C d).map ((Over.map β).map α))).toFunctor := by
            simp only [h]
      _ = (F.map (fiberTransportTwMorph C β ov) ≫
            F.map ((overOpToTwistedArrow C d).map ((Over.map β).map α))).toFunctor := by
            simp only [Functor.map_comp]
  simp only [Cat.Hom.comp_toFunctor] at step ⊢
  exact step

/--
Functor-level naturality for oppositized fiber transport.
-/
theorem fiberTransportOp_functor_naturality {b d : C} (β : b ⟶ d)
    {ov ov' : (Over b)ᵒᵖ'} (α : ov ⟶ ov') :
    ((restrictToFiberOp C F b).map α).toFunctor ⋙ fiberTransportOp C F β ov' =
    fiberTransportOp C F β ov ⋙ ((restrictToFiberOp C F d).map ((Over.map β).map α)).toFunctor := by
  have h := fiberTransport_functor_naturality C F β α
  simp only [restrictToFiberOp, fiberTransportOp, Functor.comp_map, Cat.opFunctor']
  exact congrArg (fun G => (Functor.op' G.toCatHom.toFunctor).toCatHom.toFunctor) h

/--
The object mapping for the transition functor between oppositized fibers.
Given `x : Grothendieck (restrictToFiberOp F b)`, produces an object in
`Grothendieck (restrictToFiberOp F d)`.
-/
def fiberFunctorTransitionObjOp {b d : C} (β : b ⟶ d)
    (x : Grothendieck (restrictToFiberOp C F b)) :
    Grothendieck (restrictToFiberOp C F d) :=
  ⟨(Over.map β).obj x.base, (fiberTransportOp C F β x.base).obj x.fiber⟩

/--
The morphism mapping for the transition functor between oppositized fiber
Grothendieck constructions.
-/
def fiberFunctorTransitionHomOp {b d : C} (β : b ⟶ d)
    {x y : Grothendieck (restrictToFiberOp C F b)} (f : x ⟶ y) :
    fiberFunctorTransitionObjOp C F β x ⟶ fiberFunctorTransitionObjOp C F β y := by
  refine ⟨(Over.map β).map f.base, ?_⟩
  have nat_eq := fiberTransportOp_functor_naturality C F β f.base
  have fiber_eq : ((restrictToFiberOp C F d).map ((Over.map β).map f.base)).toFunctor.obj
        ((fiberTransportOp C F β x.base).obj x.fiber) =
      (fiberTransportOp C F β y.base).obj
        (((restrictToFiberOp C F b).map f.base).toFunctor.obj x.fiber) :=
    congrArg (fun G => G.obj x.fiber) nat_eq.symm
  exact eqToHom fiber_eq ≫
        (fiberTransportOp C F β y.base).map f.fiber

set_option backward.isDefEq.respectTransparency false in
/--
The oppositized transition functor preserves identity morphisms.
-/
theorem fiberFunctorTransitionHomOp_id {b d : C} (β : b ⟶ d)
    (x : Grothendieck (restrictToFiberOp C F b)) :
    fiberFunctorTransitionHomOp C F β (𝟙 x) =
    𝟙 (fiberFunctorTransitionObjOp C F β x) := by
  apply Grothendieck.ext
  case w_fiber =>
    simp only [fiberFunctorTransitionHomOp, fiberFunctorTransitionObjOp,
               Grothendieck.id_fiber, Grothendieck.id_base]
    simp only [fiberTransportOp, eqToHom_map, eqToHom_trans]
  case w_base =>
    simp only [fiberFunctorTransitionHomOp, fiberFunctorTransitionObjOp,
               Grothendieck.id_base]
    exact (Over.map β).map_id x.base

set_option backward.isDefEq.respectTransparency false in
/--
The oppositized transition functor preserves composition.
-/
theorem fiberFunctorTransitionHomOp_comp {b d : C} (β : b ⟶ d)
    {x y z : Grothendieck (restrictToFiberOp C F b)}
    (f : x ⟶ y) (g : y ⟶ z) :
    fiberFunctorTransitionHomOp C F β (f ≫ g) =
    fiberFunctorTransitionHomOp C F β f ≫ fiberFunctorTransitionHomOp C F β g := by
  apply Grothendieck.ext
  case w_fiber =>
    simp only [fiberFunctorTransitionHomOp, fiberFunctorTransitionObjOp,
               Grothendieck.comp_fiber, Grothendieck.comp_base, fiberTransportOp]
    simp only [Functor.map_comp, eqToHom_map]
    simp only [Category.assoc, eqToHom_trans_assoc]
    have nat_eq := fiberTransportOp_functor_naturality C F β g.base
    simp only [restrictToFiberOp, Functor.comp_map, fiberTransportOp] at nat_eq ⊢
    have mor_eq := Functor.congr_hom nat_eq f.fiber
    simp only [Functor.comp_map] at mor_eq
    rw [mor_eq]
    simp only [Category.assoc, eqToHom_trans_assoc]
  case w_base =>
    simp only [fiberFunctorTransitionHomOp, Grothendieck.comp_base]
    rfl

/--
The transition functor from `Grothendieck (restrictToFiberOp F b)` to
`Grothendieck (restrictToFiberOp F d)` induced by `β : b ⟶ d`.
-/
def fiberFunctorTransitionOp {b d : C} (β : b ⟶ d) :
    Grothendieck (restrictToFiberOp C F b) ⥤ Grothendieck (restrictToFiberOp C F d) where
  obj := fiberFunctorTransitionObjOp C F β
  map := fiberFunctorTransitionHomOp C F β
  map_id := fiberFunctorTransitionHomOp_id C F β
  map_comp := fiberFunctorTransitionHomOp_comp C F β

/--
The morphism mapping for the transition functor between fiber Grothendieck
constructions.
-/
def fiberFunctorTransitionHom {b d : C} (β : b ⟶ d)
    {x y : Grothendieck (restrictToFiber C F b)} (f : x ⟶ y) :
    fiberFunctorTransitionObj C F β x ⟶ fiberFunctorTransitionObj C F β y := by
  refine ⟨(Over.map β).map f.base, ?_⟩
  have nat_eq := fiberTransport_functor_naturality C F β f.base
  have fiber_eq : ((restrictToFiber C F d).map ((Over.map β).map f.base)).toFunctor.obj
        ((fiberTransport C F β x.base).obj x.fiber) =
      ((fiberTransport C F β y.base).obj
        (((restrictToFiber C F b).map f.base).toFunctor.obj x.fiber)) :=
    congrArg (fun G => G.obj x.fiber) nat_eq.symm
  exact eqToHom fiber_eq ≫
        (fiberTransport C F β y.base).map f.fiber

set_option backward.isDefEq.respectTransparency false in
/--
The transition functor between fiber Grothendieck constructions preserves
identity morphisms.
-/
theorem fiberFunctorTransitionHom_id {b d : C} (β : b ⟶ d)
    (x : Grothendieck (restrictToFiber C F b)) :
    fiberFunctorTransitionHom C F β (𝟙 x) =
    𝟙 (fiberFunctorTransitionObj C F β x) := by
  apply Grothendieck.ext
  case w_fiber =>
    simp only [fiberFunctorTransitionHom, fiberFunctorTransitionObj,
               Grothendieck.id_fiber, Grothendieck.id_base, fiberTransport]
    simp only [eqToHom_trans, eqToHom_map]
  case w_base =>
    simp only [fiberFunctorTransitionHom, fiberFunctorTransitionObj,
               Grothendieck.id_base]
    exact (Over.map β).map_id x.base

set_option backward.isDefEq.respectTransparency false in
/--
The transition functor between fiber Grothendieck constructions preserves
composition.
-/
theorem fiberFunctorTransitionHom_comp {b d : C} (β : b ⟶ d)
    {x y z : Grothendieck (restrictToFiber C F b)}
    (f : x ⟶ y) (g : y ⟶ z) :
    fiberFunctorTransitionHom C F β (f ≫ g) =
    fiberFunctorTransitionHom C F β f ≫ fiberFunctorTransitionHom C F β g := by
  apply Grothendieck.ext
  case w_fiber =>
    simp only [fiberFunctorTransitionHom, fiberFunctorTransitionObj,
               Grothendieck.comp_fiber, Grothendieck.comp_base, fiberTransport]
    simp only [Functor.map_comp, eqToHom_map]
    simp only [Category.assoc, eqToHom_trans_assoc]
    have nat_eq := fiberTransport_functor_naturality C F β g.base
    simp only [restrictToFiber, Functor.comp_map, fiberTransport] at nat_eq ⊢
    have mor_eq := Functor.congr_hom nat_eq f.fiber
    simp only [Functor.comp_map] at mor_eq
    rw [mor_eq]
    simp only [Category.assoc, eqToHom_trans_assoc]
  case w_base =>
    simp only [fiberFunctorTransitionHom, Grothendieck.comp_base]
    rfl

/--
The transition functor from `Grothendieck (restrictToFiber F b)` to
`Grothendieck (restrictToFiber F d)` induced by `β : b ⟶ d`.
-/
def fiberFunctorTransition {b d : C} (β : b ⟶ d) :
    Grothendieck (restrictToFiber C F b) ⥤ Grothendieck (restrictToFiber C F d) where
  obj := fiberFunctorTransitionObj C F β
  map := fiberFunctorTransitionHom C F β
  map_id := fiberFunctorTransitionHom_id C F β
  map_comp := fiberFunctorTransitionHom_comp C F β

/-!
### Fiber Functor Identity and Composition Laws

To define `fiberFunctor : C ⥤ Cat`, we need to prove that `fiberFunctorTransition`
preserves identity and composition at the functor level.
-/

/--
The twisted arrow `twObjMk' (ov.hom ≫ 𝟙 b)` equals `twObjMk' ov.hom`.
-/
lemma twObjMk'_comp_id {b : C} (ov : Over b) :
    twObjMk' (ov.hom ≫ 𝟙 b) = twObjMk' ov.hom := by
  congr 1
  exact Category.comp_id ov.hom

/--
The fiber category equality for the identity transport.
The codomain of `fiberTransport C F (𝟙 b) ov` equals the domain.
-/
lemma fiberTransport_id_cat_eq {b : C} (ov : Over b) :
    (restrictToFiber C F b).obj ((Over.map (𝟙 b)).obj ov) =
    (restrictToFiber C F b).obj ov := by
  simp only [restrictToFiber, Functor.comp_obj, overOpToTwistedArrow,
             Over.map_obj_left, Over.map_obj_hom]
  congr 1
  exact twObjMk'_comp_id C ov

set_option backward.isDefEq.respectTransparency false in
/--
When `β = 𝟙 b`, the fiber transport functor is `eqToHom` in Cat.
-/
lemma fiberTransport_id {b : C} (ov : Over b) :
    fiberTransport C F (𝟙 b) ov =
    Cat.Hom.toFunctor (eqToHom (fiberTransport_id_cat_eq C F ov).symm) := by
  unfold Cat.Hom.toFunctor
  simp only [fiberTransport, fiberTransportTwMorph_id, eqToHom_map]

/--
The object equality for `fiberFunctorTransitionObj` with identity.
-/
lemma fiberFunctorTransitionObj_id_base {b : C}
    (x : Grothendieck (restrictToFiber C F b)) :
    ((Over.map (𝟙 b)).obj x.base) = x.base := by
  have h := Over.mapId_eq b
  exact congrFun (congrArg Functor.obj h) x.base

/--
When `β = 𝟙 b`, `fiberFunctorTransitionObj` returns an object equal to its input.
-/
lemma fiberFunctorTransitionObj_id {b : C}
    (x : Grothendieck (restrictToFiber C F b)) :
    fiberFunctorTransitionObj C F (𝟙 b) x = x := by
  rw [Grothendieck.mk.injEq]
  constructor
  · exact fiberFunctorTransitionObj_id_base C F x
  · simp only [fiberFunctorTransitionObj]
    rw [fiberTransport_id]
    exact eqToHom_obj_heq _ _ _ x.fiber

/--
Helper: The base of `eqToHom` in Grothendieck is `eqToHom` of the base equality.
-/
lemma Grothendieck.eqToHom_base' {G : C ⥤ Cat}
    {X Y : Grothendieck G} (h : X = Y) :
    (eqToHom h).base = eqToHom (congrArg Grothendieck.base h) := by
  cases h
  rfl

/--
The base component of `fiberFunctorTransitionObj_id` equals `fiberFunctorTransitionObj_id_base`.
-/
lemma fiberFunctorTransitionObj_id_base_eq {b : C}
    (x : Grothendieck (restrictToFiber C F b)) :
    congrArg Grothendieck.base (fiberFunctorTransitionObj_id C F x) =
    fiberFunctorTransitionObj_id_base C F x := by
  rfl

/--
Two `eqToHom` terms with the same source and target are equal (proof irrelevance).
-/
lemma eqToHom_proof_irrel {D : Type*} [Category D] {a b : D}
    (h₁ h₂ : a = b) : eqToHom h₁ = eqToHom h₂ := by
  cases h₁
  rfl

/--
Two `eqToHom` conjugations with the same source, middle, and target are equal.
-/
lemma eqToHom_conj_eq {D : Type*} [Category D] {a a' b b' : D}
    (ha : a = a') (ha' : a = a') (hb : b = b') (hb' : b = b')
    (f : a' ⟶ b) :
    eqToHom ha ≫ f ≫ eqToHom hb = eqToHom ha' ≫ f ≫ eqToHom hb' := by
  rw [eqToHom_proof_irrel ha ha', eqToHom_proof_irrel hb hb']

/--
Two `eqToHom` conjugations are equal when the endpoints and middle match.
More general version where the middle morphism's type is stated explicitly.
-/
lemma eqToHom_conj_eq' {D : Type*} [Category D] {a₁ a₂ b₁ b₂ : D}
    (ha₁ : a₁ = a₂) (ha₂ : a₁ = a₂) (hb₁ : b₁ = b₂) (hb₂ : b₁ = b₂)
    (f : a₂ ⟶ b₁) :
    eqToHom ha₁ ≫ f ≫ eqToHom hb₁ = eqToHom ha₂ ≫ f ≫ eqToHom hb₂ := by
  rw [eqToHom_proof_irrel ha₁ ha₂, eqToHom_proof_irrel hb₁ hb₂]

set_option backward.isDefEq.respectTransparency false in
/--
When `β = 𝟙 b`, `fiberFunctorTransition C F (𝟙 b)` equals the identity functor.
-/
theorem fiberFunctorTransition_id {b : C} :
    fiberFunctorTransition C F (𝟙 b) = 𝟭 (Grothendieck (restrictToFiber C F b)) := by
  apply _root_.CategoryTheory.Functor.ext
  case h_obj => exact fiberFunctorTransitionObj_id C F
  case h_map =>
    intro x y f
    simp only [Functor.id_map]
    apply Grothendieck.ext
    case w_base =>
      simp only [fiberFunctorTransition, fiberFunctorTransitionHom,
                 Grothendieck.comp_base, Grothendieck.eqToHom_base']
      rw [Functor.congr_hom (Over.mapId_eq b) f.base, Functor.id_map]
      apply eq_of_heq
      apply HEq.trans (eqToHom_comp_heq _ _)
      apply HEq.trans (comp_eqToHom_heq _ _)
      apply HEq.trans (comp_eqToHom_heq _ _).symm
      exact (eqToHom_comp_heq _ _).symm
    case w_fiber =>
      apply eq_of_heq
      simp only [fiberFunctorTransition, fiberFunctorTransitionHom,
                 Grothendieck.comp_fiber, Grothendieck.fiber_eqToHom,
                 eqToHom_trans_assoc, eqToHom_comp_heq_iff, heq_eqToHom_comp_iff]
      apply HEq.trans
      · exact Cat.functor_map_heq_of_eq_eqToHom _ _ (fiberTransport_id C F y.base) f.fiber
      apply HEq.symm
      simp only [Grothendieck.comp_base, eqToHom_map, eqToHom_trans_assoc]
      apply HEq.trans (eqToHom_comp_heq _ _)
      apply HEq.trans (comp_eqToHom_heq _ _)
      rw [Grothendieck.eqToHom_base', eqToHom_map]
      exact Cat.eqToHom_map_heq _ _

/--
The fiber category equality for the oppositized identity transport.
-/
lemma fiberTransportOp_id_cat_eq {b : C} (ov : Over b) :
    (restrictToFiberOp C F b).obj ((Over.map (𝟙 b)).obj ov) =
    (restrictToFiberOp C F b).obj ov := by
  simp only [restrictToFiberOp, Functor.comp_obj, Cat.opFunctor']
  congr 1
  exact fiberTransport_id_cat_eq C F ov

set_option backward.isDefEq.respectTransparency false in
/--
When `β = 𝟙 b`, the oppositized fiber transport functor is `eqToHom` in Cat.
-/
lemma fiberTransportOp_id {b : C} (ov : Over b) :
    fiberTransportOp C F (𝟙 b) ov =
    Cat.Hom.toFunctor (eqToHom (fiberTransportOp_id_cat_eq C F ov).symm) := by
  unfold Cat.Hom.toFunctor
  simp only [fiberTransportOp, fiberTransport_id, Cat.opFunctor',
    Functor.toCatHom_toFunctor, Cat.Functor.op'_eqToHom]

/--
The object equality for oppositized `fiberFunctorTransitionObjOp` with identity.
-/
lemma fiberFunctorTransitionObjOp_id_base {b : C}
    (x : Grothendieck (restrictToFiberOp C F b)) :
    ((Over.map (𝟙 b)).obj x.base) = x.base := by
  have h := Over.mapId_eq b
  exact congrFun (congrArg Functor.obj h) x.base

/--
When `β = 𝟙 b`, `fiberFunctorTransitionObjOp` returns an object equal to input.
-/
lemma fiberFunctorTransitionObjOp_id {b : C}
    (x : Grothendieck (restrictToFiberOp C F b)) :
    fiberFunctorTransitionObjOp C F (𝟙 b) x = x := by
  rw [Grothendieck.mk.injEq]
  constructor
  · exact fiberFunctorTransitionObjOp_id_base C F x
  · simp only [fiberFunctorTransitionObjOp]
    rw [fiberTransportOp_id]
    exact eqToHom_obj_heq _ _ _ _

set_option backward.isDefEq.respectTransparency false in
/--
When `β = 𝟙 b`, `fiberFunctorTransitionOp C F (𝟙 b)` equals the identity functor.
-/
theorem fiberFunctorTransitionOp_id {b : C} :
    fiberFunctorTransitionOp C F (𝟙 b) =
    𝟭 (Grothendieck (restrictToFiberOp C F b)) := by
  apply _root_.CategoryTheory.Functor.ext
  case h_obj => exact fiberFunctorTransitionObjOp_id C F
  case h_map =>
    intro x y f
    simp only [Functor.id_map]
    apply Grothendieck.ext
    case w_base =>
      simp only [fiberFunctorTransitionOp, fiberFunctorTransitionHomOp,
                 Grothendieck.comp_base, Grothendieck.eqToHom_base']
      rw [Functor.congr_hom (Over.mapId_eq b) f.base, Functor.id_map]
      apply eq_of_heq
      apply HEq.trans (eqToHom_comp_heq _ _)
      apply HEq.trans (comp_eqToHom_heq _ _)
      apply HEq.trans (comp_eqToHom_heq _ _).symm
      exact (eqToHom_comp_heq _ _).symm
    case w_fiber =>
      apply eq_of_heq
      simp only [fiberFunctorTransitionOp, fiberFunctorTransitionHomOp,
                 Grothendieck.comp_fiber, Grothendieck.fiber_eqToHom,
                 eqToHom_trans_assoc, eqToHom_comp_heq_iff, heq_eqToHom_comp_iff]
      apply HEq.trans
      · exact Cat.functor_map_heq_of_eq_eqToHom _ _
              (fiberTransportOp_id C F y.base) f.fiber
      apply HEq.symm
      simp only [Grothendieck.comp_base, eqToHom_map, eqToHom_trans_assoc]
      apply HEq.trans (eqToHom_comp_heq _ _)
      apply HEq.trans (comp_eqToHom_heq _ _)
      rw [Grothendieck.eqToHom_base', eqToHom_map]
      exact Cat.eqToHom_map_heq _ _

set_option backward.isDefEq.respectTransparency false in
/--
The fiber transport for `β ≫ γ` equals the composition of fiber transports, up to eqToHom.
-/
theorem fiberTransport_comp {b d e : C} (β : b ⟶ d) (γ : d ⟶ e) (ov : Over b) :
    fiberTransport C F (β ≫ γ) ov =
    fiberTransport C F β ov ⋙
      fiberTransport C F γ ((Over.map β).obj ov) ⋙
      (eqToHom (congrArg F.obj
        (congrArg (twObjMk' ·) (Category.assoc ov.hom β γ)))).toFunctor := by
  simp only [fiberTransport, fiberTransportTwMorph_comp, F.map_comp, eqToHom_map]
  rfl

/--
The object mapping for `fiberFunctorTransition (β ≫ γ)` equals the composition
of object mappings for `β` and `γ`.
-/
lemma fiberFunctorTransitionObj_comp {b d e : C} (β : b ⟶ d) (γ : d ⟶ e)
    (x : Grothendieck (restrictToFiber C F b)) :
    fiberFunctorTransitionObj C F (β ≫ γ) x =
    fiberFunctorTransitionObj C F γ (fiberFunctorTransitionObj C F β x) := by
  simp only [fiberFunctorTransitionObj]
  congr 1
  · exact congrArg (·.obj x.base) (Over.mapComp_eq β γ)
  · simp only [fiberTransport_comp, Functor.comp_obj]
    exact eqToHom_obj_heq _ _ _ _

set_option backward.isDefEq.respectTransparency false in
/--
The transition functor respects composition: transitioning by `β ≫ γ` equals
composing the transitions by `β` and `γ`.
-/
theorem fiberFunctorTransition_comp {b d e : C} (β : b ⟶ d) (γ : d ⟶ e) :
    fiberFunctorTransition C F (β ≫ γ) =
    fiberFunctorTransition C F β ⋙ fiberFunctorTransition C F γ := by
  apply _root_.CategoryTheory.Functor.ext
  case h_obj => exact fiberFunctorTransitionObj_comp C F β γ
  case h_map =>
    intro x y f
    apply Grothendieck.ext
    case w_base =>
      simp only [fiberFunctorTransition, Functor.comp_map, fiberFunctorTransitionHom,
                 Grothendieck.comp_base, Grothendieck.eqToHom_base']
      rw [Functor.congr_hom (Over.mapComp_eq β γ) f.base]
      simp only [Functor.comp_map]
      apply eq_of_heq
      apply HEq.trans (eqToHom_comp_heq _ _)
      apply HEq.trans (comp_eqToHom_heq _ _)
      apply HEq.symm
      apply HEq.trans (eqToHom_comp_heq _ _)
      exact comp_eqToHom_heq _ _
    case w_fiber =>
      apply eq_of_heq
      simp only [fiberFunctorTransition, Functor.comp_map, fiberFunctorTransitionHom,
                 Grothendieck.comp_fiber, Grothendieck.fiber_eqToHom,
                 eqToHom_trans_assoc, eqToHom_comp_heq_iff, heq_eqToHom_comp_iff]
      simp only [Grothendieck.comp_base, eqToHom_map]
      simp only [fiberFunctorTransitionObj]
      apply HEq.trans
      · exact Cat.functor_map_heq_of_eq_comp_comp_eqToHom
          (fiberTransport C F (β ≫ γ) y.base)
          (fiberTransport C F β y.base)
          (fiberTransport C F γ ((Over.map β).obj y.base))
          _ (fiberTransport_comp C F β γ y.base) f.fiber
      apply HEq.symm
      apply HEq.trans (eqToHom_comp_heq _ _)
      apply HEq.trans (eqToHom_comp_heq _ _)
      apply HEq.trans (comp_eqToHom_heq _ _)
      rw [Grothendieck.eqToHom_base', eqToHom_map]
      apply HEq.trans (Cat.eqToHom_map_heq _ _)
      apply HEq.trans (eqToHom_comp_heq _ _)
      exact Functor.map_eqToHom_comp_heq _ _ _

/--
The object mapping for oppositized `fiberFunctorTransitionOp (β ≫ γ)` equals
the composition of object mappings.
-/
lemma fiberFunctorTransitionObjOp_comp {b d e : C} (β : b ⟶ d) (γ : d ⟶ e)
    (x : Grothendieck (restrictToFiberOp C F b)) :
    fiberFunctorTransitionObjOp C F (β ≫ γ) x =
    fiberFunctorTransitionObjOp C F γ (fiberFunctorTransitionObjOp C F β x) := by
  simp only [fiberFunctorTransitionObjOp, fiberTransportOp]
  congr 1
  · exact congrArg (·.obj x.base) (Over.mapComp_eq β γ)
  · simp only [fiberTransport_comp, Cat.opFunctor']
    exact eqToHom_obj_heq _ _ _ _

set_option backward.isDefEq.respectTransparency false in
/--
The oppositized transition functor respects composition.
-/
theorem fiberFunctorTransitionOp_comp {b d e : C} (β : b ⟶ d) (γ : d ⟶ e) :
    fiberFunctorTransitionOp C F (β ≫ γ) =
    fiberFunctorTransitionOp C F β ⋙ fiberFunctorTransitionOp C F γ := by
  apply _root_.CategoryTheory.Functor.ext
  case h_obj => exact fiberFunctorTransitionObjOp_comp C F β γ
  case h_map =>
    intro x y f
    apply Grothendieck.ext
    case w_base =>
      simp only [fiberFunctorTransitionOp, fiberFunctorTransitionHomOp,
                 Functor.comp_map, Grothendieck.comp_base, Grothendieck.eqToHom_base']
      rw [Functor.congr_hom (Over.mapComp_eq β γ) f.base, Functor.comp_map]
      apply eq_of_heq
      apply HEq.trans (eqToHom_comp_heq _ _)
      apply HEq.trans (comp_eqToHom_heq _ _)
      apply HEq.symm
      apply HEq.trans (eqToHom_comp_heq _ _)
      exact comp_eqToHom_heq _ _
    case w_fiber =>
      apply eq_of_heq
      simp only [fiberFunctorTransitionOp, Functor.comp_map, fiberFunctorTransitionHomOp,
                 Grothendieck.comp_fiber, Grothendieck.fiber_eqToHom,
                 eqToHom_trans_assoc, eqToHom_comp_heq_iff, heq_eqToHom_comp_iff]
      simp only [Grothendieck.comp_base, eqToHom_map]
      simp only [fiberFunctorTransitionObjOp, fiberTransportOp]
      have h := fiberTransport_comp C F β γ y.base
      have hOp : Cat.opFunctor'.map (fiberTransport C F (β ≫ γ) y.base).toCatHom =
          Cat.opFunctor'.map (fiberTransport C F β y.base).toCatHom ≫
          Cat.opFunctor'.map (fiberTransport C F γ ((Over.map β).obj y.base)).toCatHom ≫
          eqToHom (congrArg Cat.opFunctor'.obj (congrArg F.obj
            (congrArg (twObjMk' ·) (Category.assoc y.base.hom β γ)))) := by
        apply Cat.Hom.ext
        simp only [Cat.Hom.comp_toFunctor, Functor.toCatHom_toFunctor, Cat.opFunctor']
        rw [h]
        simp only [Functor.op'_comp, Cat.Functor.op'_eqToHom]
      have hOpFunctor := congrArg Cat.Hom.toFunctor hOp
      simp only [Cat.Hom.comp_toFunctor] at hOpFunctor
      apply HEq.trans
      · exact Cat.functor_map_heq_of_eq_comp_comp_eqToHom
          (Cat.opFunctor'.map (fiberTransport C F (β ≫ γ) y.base).toCatHom).toFunctor
          (Cat.opFunctor'.map (fiberTransport C F β y.base).toCatHom).toFunctor
          (Cat.opFunctor'.map (fiberTransport C F γ ((Over.map β).obj y.base)).toCatHom).toFunctor
          _ hOpFunctor f.fiber
      apply HEq.symm
      apply HEq.trans (eqToHom_comp_heq _ _)
      apply HEq.trans (eqToHom_comp_heq _ _)
      apply HEq.trans (comp_eqToHom_heq _ _)
      rw [Grothendieck.eqToHom_base', eqToHom_map]
      apply HEq.trans (Cat.eqToHom_map_heq _ _)
      apply HEq.trans (eqToHom_comp_heq _ _)
      exact Functor.map_eqToHom_comp_heq _ _ _

/--
The oppositized fiber functor `fiberFunctorOp F : C ⥤ Cat` assigns to each
object `b : C` the Grothendieck construction of `restrictToFiberOp` over `b`.
-/
def fiberFunctorOp : C ⥤ Cat where
  obj b := Cat.of (Grothendieck (restrictToFiberOp C F b))
  map β := (fiberFunctorTransitionOp C F β).toCatHom
  map_id _ := Cat.Hom.ext (fiberFunctorTransitionOp_id C F)
  map_comp β γ := Cat.Hom.ext (fiberFunctorTransitionOp_comp C F β γ)

/--
The fiber functor `fiberFunctor F : C ⥤ Cat` assigns to each object `b : C`
the Grothendieck construction of `F` restricted to the fiber over `b`.
Morphisms `β : b ⟶ d` are sent to the transition functors.
-/
def fiberFunctor : C ⥤ Cat where
  obj b := Cat.of (Grothendieck (restrictToFiber C F b))
  map β := (fiberFunctorTransition C F β).toCatHom
  map_id _ := Cat.Hom.ext (fiberFunctorTransition_id C F)
  map_comp β γ := Cat.Hom.ext (fiberFunctorTransition_comp C F β γ)

/--
The object mapping for the transition functor for `innerFiberContra`.
Given `x : innerFiberContra F b`, produces an object in `innerFiberContra F d`.
-/
def innerFiberContraTransitionObj {b d : C} (β : b ⟶ d)
    (x : innerFiberContra C F b) : innerFiberContra C F d :=
  ⟨(Over.map β).obj x.base, (fiberTransport C F β x.base).obj x.fiber⟩

/--
The fiber coherence equation for `innerFiberContraTransitionHom`.
-/
theorem innerFiberContraTransition_fiber_eq {b d : C} (β : b ⟶ d)
    {x y : innerFiberContra C F b} (f : x ⟶ y) :
    (fiberTransport C F β x.base).obj
      ((restrictToFiber C F b).map f.base |>.toFunctor.obj y.fiber) =
    ((restrictToFiber C F d).map ((Over.map β).map f.base)).toFunctor.obj
      ((fiberTransport C F β y.base).obj y.fiber) :=
  congrFun (congrArg Functor.obj
    (fiberTransport_functor_naturality C F β (ov := y.base) (ov' := x.base) f.base)) y.fiber

/--
The morphism mapping for the transition functor for `innerFiberContra`.
-/
def innerFiberContraTransitionHom {b d : C} (β : b ⟶ d)
    {x y : innerFiberContra C F b} (f : x ⟶ y) :
    innerFiberContraTransitionObj C F β x ⟶ innerFiberContraTransitionObj C F β y :=
  ⟨(Over.map β).map f.base,
   (fiberTransport C F β x.base).map f.fiber ≫
     eqToHom (innerFiberContraTransition_fiber_eq C F β f)⟩

@[simp]
theorem innerFiberContraTransitionHom_base {b d : C} (β : b ⟶ d)
    {x y : innerFiberContra C F b} (f : x ⟶ y) :
    (innerFiberContraTransitionHom C F β f).base = (Over.map β).map f.base := rfl

@[simp]
theorem innerFiberContraTransitionHom_fiber {b d : C} (β : b ⟶ d)
    {x y : innerFiberContra C F b} (f : x ⟶ y) :
    (innerFiberContraTransitionHom C F β f).fiber =
    (fiberTransport C F β x.base).map f.fiber ≫
      eqToHom (innerFiberContraTransition_fiber_eq C F β f) := rfl

set_option backward.isDefEq.respectTransparency false in
/--
The transition functor for `innerFiberContra` along a base morphism `β : b ⟶ d`.
-/
def innerFiberContraTransition {b d : C} (β : b ⟶ d) :
    innerFiberContra C F b ⥤ innerFiberContra C F d where
  obj := innerFiberContraTransitionObj C F β
  map := innerFiberContraTransitionHom C F β
  map_id x := by
    refine GrothendieckContra'.ext _ _ ?_ ?_
    · simp only [innerFiberContraTransitionHom]
      exact (Over.map β).map_id x.base
    · change ((fiberTransport C F β x.base).map
               (GrothendieckContra'.id x).fiber ≫ _) ≫ eqToHom _ =
             (GrothendieckContra'.id (innerFiberContraTransitionObj C F β x)).fiber
      simp only [GrothendieckContra'.id]
      simp only [eqToHom_map, eqToHom_trans]
  map_comp {x y z} f g := by
    refine GrothendieckContra'.ext _ _ ?_ ?_
    · simp only [innerFiberContraTransitionHom_base]
      exact (Over.map β).map_comp f.base g.base
    · change ((fiberTransport C F β x.base).map (GrothendieckContra'.comp f g).fiber ≫ _) ≫
             eqToHom _ =
           (GrothendieckContra'.comp
             (innerFiberContraTransitionHom C F β f)
             (innerFiberContraTransitionHom C F β g)).fiber
      rw [GrothendieckContra'.comp_fiber, GrothendieckContra'.comp_fiber]
      simp only [innerFiberContraTransitionHom_fiber, innerFiberContraTransitionHom_base,
                 innerFiberContraTransitionObj, Functor.map_comp, Category.assoc,
                 eqToHom_map, eqToHom_trans_assoc]
      have nat_eq := fiberTransport_functor_naturality C F β
        (ov := y.base) (ov' := x.base) f.base
      have mor_eq := Functor.congr_hom nat_eq g.fiber
      simp only [Functor.comp_map] at mor_eq
      rw [mor_eq]
      simp only [Category.assoc, eqToHom_trans]

/--
Functoriality of `innerFiberContraTransition` with respect to identity morphisms.
-/
theorem innerFiberContraTransitionObj_id_base {b : C} (x : innerFiberContra C F b) :
    (innerFiberContraTransitionObj C F (𝟙 b) x).base = x.base :=
  congrFun (congrArg Functor.obj (Over.mapId_eq b)) x.base

theorem innerFiberContraTransitionObj_id_fiber {b : C} (x : innerFiberContra C F b) :
    (innerFiberContraTransitionObj C F (𝟙 b) x).fiber ≍ x.fiber := by
  unfold innerFiberContraTransitionObj
  simp only
  rw [fiberTransport_id]
  exact eqToHom_obj_heq _ _ (fiberTransport_id_cat_eq C F x.base).symm x.fiber

theorem innerFiberContraTransitionObj_id {b : C} (x : innerFiberContra C F b) :
    innerFiberContraTransitionObj C F (𝟙 b) x = x := by
  have h_base := innerFiberContraTransitionObj_id_base C F x
  have h_fiber := innerFiberContraTransitionObj_id_fiber C F x
  exact GrothendieckContra'.obj_ext _ _ h_base h_fiber

set_option backward.isDefEq.respectTransparency false in
theorem innerFiberContraTransition_id (b : C) :
    innerFiberContraTransition C F (𝟙 b) = 𝟭 (innerFiberContra C F b) := by
  fapply _root_.CategoryTheory.Functor.ext
  · exact innerFiberContraTransitionObj_id C F
  · intro x y f
    refine GrothendieckContra'.ext _ _ ?w_base ?w_fiber
    case w_base =>
      simp only [innerFiberContraTransition, innerFiberContraTransitionHom, Functor.id_map]
      rw [Functor.congr_hom (Over.mapId_eq b) f.base, Functor.id_map]
      simp +instances only [
        innerFiberContraCategory,
        GrothendieckContra'.GrothendieckContraInst',
        GrothendieckContra'.comp_base]
      conv_rhs => rw [GrothendieckContra'.base_eqToHom, GrothendieckContra'.base_eqToHom]
    case w_fiber =>
      simp only [innerFiberContraTransition, innerFiberContraTransitionHom, Functor.id_map]
      apply eq_of_heq
      apply HEq.trans (comp_eqToHom_heq _ _)
      apply HEq.trans (comp_eqToHom_heq _ _)
      have hMap := Cat.functor_map_heq_of_eq_eqToHom
        (fiberTransport_id_cat_eq C F x.base).symm
        (fiberTransport C F (𝟙 b) x.base)
        (fiberTransport_id C F x.base)
        f.fiber
      apply HEq.trans hMap
      apply HEq.symm
      exact GrothendieckContra'.conj_eqToHom_fiber_heq _ f _

/--
Functoriality of `innerFiberContraTransition` with respect to composition.
-/
theorem innerFiberContraTransitionObj_comp {b d e : C} (β : b ⟶ d) (γ : d ⟶ e)
    (x : innerFiberContra C F b) :
    innerFiberContraTransitionObj C F (β ≫ γ) x =
    innerFiberContraTransitionObj C F γ (innerFiberContraTransitionObj C F β x) := by
  apply GrothendieckContra'.obj_ext
  · -- base field: (Over.map (β ≫ γ)).obj = (Over.map γ).obj ∘ (Over.map β).obj
    exact congrArg (·.obj x.base) (Over.mapComp_eq β γ)
  · -- fiber field: uses fiberTransport_comp
    simp only [innerFiberContraTransitionObj, fiberTransport_comp, Functor.comp_obj]
    exact eqToHom_obj_heq _ _ _ _

set_option backward.isDefEq.respectTransparency false in
theorem innerFiberContraTransition_comp {b d e : C} (β : b ⟶ d) (γ : d ⟶ e) :
    innerFiberContraTransition C F (β ≫ γ) =
    innerFiberContraTransition C F β ⋙ innerFiberContraTransition C F γ := by
  fapply _root_.CategoryTheory.Functor.ext
  · exact innerFiberContraTransitionObj_comp C F β γ
  · intro x y f
    refine GrothendieckContra'.ext _ _ ?w_base ?w_fiber
    case w_base =>
      unfold innerFiberContraTransition innerFiberContraTransitionHom
      simp only [Functor.comp_map]
      rw [Functor.congr_hom (Over.mapComp_eq β γ) f.base, Functor.comp_map]
      simp +instances only [
        innerFiberContraCategory,
        GrothendieckContra'.GrothendieckContraInst',
        GrothendieckContra'.comp_base]
      conv_rhs => rw [GrothendieckContra'.base_eqToHom, GrothendieckContra'.base_eqToHom]
    case w_fiber =>
      unfold innerFiberContraTransition innerFiberContraTransitionHom
      simp only [Functor.comp_map]
      apply eq_of_heq
      apply HEq.trans (comp_eqToHom_heq _ _)
      apply HEq.trans (comp_eqToHom_heq _ _)
      apply HEq.trans
      · exact Cat.functor_map_heq_of_eq_comp_comp_eqToHom
          (fiberTransport C F (β ≫ γ) x.base)
          (fiberTransport C F β x.base)
          (fiberTransport C F γ ((Over.map β).obj x.base))
          _ (fiberTransport_comp C F β γ x.base) f.fiber
      apply HEq.symm
      apply HEq.trans (GrothendieckContra'.conj_eqToHom_fiber_heq _ _ _)
      simp only [innerFiberContraTransitionObj]
      apply HEq.trans (comp_eqToHom_heq _ _)
      exact Functor.map_comp_eqToHom_heq _ _ _

/--
The contravariant fiber functor using `GrothendieckContra'` for the inner layer.
For each `b : C`, this assigns the category `innerFiberContra C F b`.
-/
def fiberFunctorContra : C ⥤ Cat where
  obj b := Cat.of (innerFiberContra C F b)
  map β := (innerFiberContraTransition C F β).toCatHom
  map_id b := Cat.Hom.ext (innerFiberContraTransition_id C F b)
  map_comp β γ := Cat.Hom.ext (innerFiberContraTransition_comp C F β γ)

/--
The connected Grothendieck construction using `GrothendieckContra'` for the inner layer.

This construction produces morphisms with:
- domArr: covariant (x → y)
- codArr: covariant (x.base → y.base)
- fiberMorph: covariant (x.fiber → transported(y.fiber))

All three directions match the target `ConnGrothendieckHom` structure.
-/
def ConnectedGrothendieckContra : Type _ := Grothendieck (fiberFunctorContra C F)

instance : Category (ConnectedGrothendieckContra C F) :=
  inferInstanceAs (Category (Grothendieck (fiberFunctorContra C F)))

section ConnectedGrothendieckContraMorphisms

/-!
## Morphism Components for `ConnectedGrothendieckContra`

This section verifies that all three morphism directions are correct:
- domArr: covariant (x → y)
- codArr: covariant (x → y)
- fiberMorph: covariant (x-related → y-related)
-/

/--
Extract the codomain arrow from a morphism in `ConnectedGrothendieckContra`.

For `f : x ⟶ y`, this is `f.base : x.base ⟶ y.base` in `C`.
-/
def connGrothendieckContraHomCodArr {x y : ConnectedGrothendieckContra C F}
    (f : x ⟶ y) : x.base ⟶ y.base :=
  f.base

/--
Extract the domain arrow from a morphism in `ConnectedGrothendieckContra`.

For `f : x ⟶ y`:
- `f.fiber` is a morphism in `innerFiberContra C F y.base`
- `f.fiber.base` is a morphism in `Over y.base`
- `f.fiber.base.left` is a morphism `x.fiber.base.left ⟶ y.fiber.base.left` in `C`
-/
def connGrothendieckContraHomDomArr {x y : ConnectedGrothendieckContra C F}
    (f : x ⟶ y) : x.fiber.base.left ⟶ y.fiber.base.left :=
  f.fiber.base.left

/--
The commuting square condition for morphisms in `ConnectedGrothendieckContra`.

For `f : x ⟶ y`, we have:
  `x.fiber.base.hom ≫ codArr = domArr ≫ y.fiber.base.hom`
-/
theorem connGrothendieckContraMorphSquareComm {x y : ConnectedGrothendieckContra C F}
    (f : x ⟶ y) :
    x.fiber.base.hom ≫ connGrothendieckContraHomCodArr C F f =
      connGrothendieckContraHomDomArr C F f ≫ y.fiber.base.hom := by
  simp only [connGrothendieckContraHomDomArr, connGrothendieckContraHomCodArr]
  exact (Over.w f.fiber.base).symm

/--
Convert an object of `ConnectedGrothendieckContra` to `ConnGrothendieckObj`.
-/
def connGrothendieckContraObjToObj (x : ConnectedGrothendieckContra C F) :
    ConnGrothendieckObj C F where
  arrow := twObjMk' x.fiber.base.hom
  fiber := x.fiber.fiber

/--
Convert a `ConnGrothendieckObj` to an object of `ConnectedGrothendieckContra`.
-/
def connGrothendieckObjToContraObj (x : ConnGrothendieckObj C F) :
    ConnectedGrothendieckContra C F :=
  ⟨twCod' x.arrow,
   ⟨Over.mk (twArr' x.arrow), x.fiber⟩⟩

/--
The round-trip from `ConnectedGrothendieckContra` to `ConnGrothendieckObj` and back.
-/
theorem connGrothendieckContraObj_roundtrip (x : ConnectedGrothendieckContra C F) :
    connGrothendieckObjToContraObj C F (connGrothendieckContraObjToObj C F x) = x := by
  simp only [connGrothendieckContraObjToObj, connGrothendieckObjToContraObj]
  rfl

/--
The round-trip from `ConnGrothendieckObj` to `ConnectedGrothendieckContra` and back.
-/
theorem connGrothendieckObj_contraRoundtrip (x : ConnGrothendieckObj C F) :
    connGrothendieckContraObjToObj C F (connGrothendieckObjToContraObj C F x) = x := by
  simp only [connGrothendieckObjToContraObj, connGrothendieckContraObjToObj]
  ext
  · simp only [Over.mk_hom]
    exact twObjMk'_twArr' x.arrow
  · simp only [Over.mk_hom]
    rfl

/--
The type of objects in `ConnectedGrothendieckContra` is equivalent to `ConnGrothendieckObj`.
-/
def connGrothendieckContraObjEquiv :
    ConnectedGrothendieckContra C F ≃ ConnGrothendieckObj C F where
  toFun := connGrothendieckContraObjToObj C F
  invFun := connGrothendieckObjToContraObj C F
  left_inv := connGrothendieckContraObj_roundtrip C F
  right_inv := connGrothendieckObj_contraRoundtrip C F

section MorphismEquivalence

/-!
### Morphism Equivalence

We establish that morphisms in `ConnectedGrothendieckContra` correspond to
`ConnGrothendieckHom`.

For `f : x ⟶ y` in `ConnectedGrothendieckContra`:
- `f.base : x.base ⟶ y.base` (codArr in C)
- `f.fiber : (innerFiberContraTransition f.base).obj x.fiber ⟶ y.fiber`
  - This is a `GrothendieckContra'.Hom` with:
    - `.base : (innerFiberContraTransitionObj f.base x.fiber).base ⟶ y.fiber.base`
      which is a morphism in `Over y.base`
    - `.fiber : (innerFiberContraTransitionObj ...).fiber ⟶
                (restrictToFiber.map f.fiber.base).obj y.fiber.fiber`
-/

/--
Extract the fiber morphism from a morphism in `ConnectedGrothendieckContra`.

This extracts `f.fiber.fiber` which is a morphism in the functor category `F(...)`.
-/
def connGrothendieckContraHomFiberMorph {x y : ConnectedGrothendieckContra C F}
    (f : x ⟶ y) :
    (innerFiberContraTransitionObj C F f.base x.fiber).fiber ⟶
    ((restrictToFiber C F y.base).map f.fiber.base).toFunctor.obj y.fiber.fiber :=
  f.fiber.fiber

/--
The type of the fiber morphism extracted from `ConnectedGrothendieckContra`.
-/
def connGrothendieckContraFiberMorphType {x y : ConnectedGrothendieckContra C F}
    (f : x ⟶ y) : Type _ :=
  (innerFiberContraTransitionObj C F f.base x.fiber).fiber ⟶
    ((restrictToFiber C F y.base).map f.fiber.base).toFunctor.obj y.fiber.fiber

/--
Simplify the source of the fiber morphism type.

The source is `(innerFiberContraTransitionObj C F f.base x.fiber).fiber`.
By definition of `innerFiberContraTransitionObj`, this equals
`(fiberTransport C F f.base x.fiber.base).obj x.fiber.fiber`.
-/
theorem connGrothendieckContraFiberMorphSource {x y : ConnectedGrothendieckContra C F}
    (f : x ⟶ y) :
    (innerFiberContraTransitionObj C F f.base x.fiber).fiber =
    (fiberTransport C F f.base x.fiber.base).obj x.fiber.fiber := rfl

/--
Simplify the target of the fiber morphism type.

The target is `((restrictToFiber C F y.base).map f.fiber.base).obj y.fiber.fiber`.
By definition of `restrictToFiber`, this equals
`(F.map (overOpToTwistedArrow y.base).map f.fiber.base).obj y.fiber.fiber`.
-/
theorem connGrothendieckContraFiberMorphTarget {x y : ConnectedGrothendieckContra C F}
    (f : x ⟶ y) :
    ((restrictToFiber C F y.base).map f.fiber.base).toFunctor.obj y.fiber.fiber =
    (F.map ((overOpToTwistedArrow C y.base).map f.fiber.base)).toFunctor.obj
      y.fiber.fiber := rfl

/--
The twisted arrow morphism corresponding to `f.fiber.base`.

Since `f.fiber.base` is a morphism in `Over y.base`, the functor
`overOpToTwistedArrow y.base` maps it to a twisted arrow morphism.

The type shows:
- Source: `(overOpToTwistedArrow y.base).obj y.fiber.base` = `twObjMk' y.fiber.base.hom`
- Target: `(overOpToTwistedArrow y.base).obj (transported x.fiber).base`
        = `twObjMk' (transported x.fiber).base.hom`
-/
def connGrothendieckContraFiberBaseTwMorph {x y : ConnectedGrothendieckContra C F}
    (f : x ⟶ y) :
    (overOpToTwistedArrow C y.base).obj y.fiber.base ⟶
    (overOpToTwistedArrow C y.base).obj
      (((fiberFunctorContra C F).map f.base).toFunctor.obj x.fiber).base :=
  (overOpToTwistedArrow C y.base).map f.fiber.base

/--
Examine the source of the fiber morphism in terms of twisted arrows.

The fiber morphism source is in `F.obj (twObjMk' (transported x.fiber).base.hom)`.
-/
theorem connGrothendieckContraFiberSourceTw {x y : ConnectedGrothendieckContra C F}
    (f : x ⟶ y) :
    (innerFiberContraTransitionObj C F f.base x.fiber).fiber =
    (fiberTransport C F f.base x.fiber.base).obj x.fiber.fiber := rfl

/--
Examine what object in `F` the fiber morphism source lives in.
-/
def connGrothendieckContraFiberSourceCat {x y : ConnectedGrothendieckContra C F}
    (f : x ⟶ y) : Cat :=
  F.obj (twObjMk' (innerFiberContraTransitionObj C F f.base x.fiber).base.hom)

/--
Examine what object in `F` the fiber morphism target lives in.
-/
def connGrothendieckContraFiberTargetCat {x y : ConnectedGrothendieckContra C F}
    (f : x ⟶ y) : Cat :=
  F.obj ((overOpToTwistedArrow C y.base).obj
    (innerFiberContraTransitionObj C F f.base x.fiber).base)

/--
The square condition for morphisms in `ConnectedGrothendieckContra` expressed in
terms of `ConnGrothendieckObj` arrows.

For `f : x ⟶ y`, the square `x.fiber.base.hom ≫ f.base = f.fiber.base.left ≫
y.fiber.base.hom` must commute.
-/
theorem connGrothendieckContraSquare {x y : ConnectedGrothendieckContra C F}
    (f : x ⟶ y) :
    x.fiber.base.hom ≫ f.base = f.fiber.base.left ≫ y.fiber.base.hom :=
  (Over.w f.fiber.base).symm

/--
The fiberTransportTwMorph equals connGrothendieckTwMorphCod when applied appropriately.
-/
theorem fiberTransportTwMorph_eq_connGrothendieckTwMorphCod
    {x : ConnectedGrothendieckContra C F} {b : C} (β : x.base ⟶ b) :
    fiberTransportTwMorph C β x.fiber.base =
    connGrothendieckTwMorphCod C (twObjMk' x.fiber.base.hom) β := by
  simp only [fiberTransportTwMorph, connGrothendieckTwMorphCod, connGrothendieckDiagCod]
  rfl

theorem fiberTransportTwMorph_eq_connGrothendieckTwMorphCod'
    {b b' : C} (ov : Over b) (β : b ⟶ b') :
    fiberTransportTwMorph C β ov =
    connGrothendieckTwMorphCod C (twObjMk' ov.hom) β := by
  simp only [fiberTransportTwMorph, connGrothendieckTwMorphCod, connGrothendieckDiagCod]
  rfl

/--
The source object in TwistedArrow for the target of `f.fiber.fiber`.
-/
theorem overOpToTwistedArrow_map_source {x y : ConnectedGrothendieckContra C F}
    (_f : x ⟶ y) :
    (overOpToTwistedArrow C y.base).obj y.fiber.base = twObjMk' y.fiber.base.hom :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
The target object in TwistedArrow for the target of `f.fiber.fiber`.
-/
theorem overOpToTwistedArrow_map_target {x y : ConnectedGrothendieckContra C F}
    (f : x ⟶ y) :
    (overOpToTwistedArrow C y.base).obj
      (innerFiberContraTransitionObj C F f.base x.fiber).base =
    twObjMk' (x.fiber.base.hom ≫ f.base) := by
  simp only [innerFiberContraTransitionObj, Over.map_obj_hom, overOpToTwistedArrow]

set_option backward.isDefEq.respectTransparency false in
/--
The fiberMorph source category.
-/
theorem connGrothendieckContra_fiberMorph_source_cat {x y : ConnectedGrothendieckContra C F}
    (f : x ⟶ y) :
    connGrothendieckDiagCod C (twObjMk' x.fiber.base.hom) f.base =
    twObjMk' (x.fiber.base.hom ≫ f.base) := by
  simp only [connGrothendieckDiagCod, twObjMk'_arr]

set_option backward.isDefEq.respectTransparency false in
/--
The fiberMorph target category before eqToHom transport.
-/
theorem connGrothendieckContra_fiberMorph_target_cat {x y : ConnectedGrothendieckContra C F}
    (f : x ⟶ y) :
    connGrothendieckDiagDom C (twObjMk' y.fiber.base.hom) f.fiber.base.left =
    twObjMk' (f.fiber.base.left ≫ y.fiber.base.hom) := by
  simp only [connGrothendieckDiagDom, twObjMk'_arr]

set_option backward.isDefEq.respectTransparency false in
/--
The source category of `f.fiber.fiber` equals the diagonal category.

The source is `F.obj (twObjMk' (x.fiber.base.hom ≫ f.base))` which equals
`F.obj (connGrothendieckDiagCod (twObjMk' x.fiber.base.hom) f.base)`.
-/
theorem connGrothendieckContraFiberMorph_source_cat_eq
    {x y : ConnectedGrothendieckContra C F} (f : x ⟶ y) :
    F.obj (twObjMk' (x.fiber.base.hom ≫ f.base)) =
    F.obj (connGrothendieckDiagCod C (twObjMk' x.fiber.base.hom) f.base) := by
  simp only [connGrothendieckDiagCod, twObjMk'_arr]

set_option backward.isDefEq.respectTransparency false in
/--
The target category of `f.fiber.fiber` equals the diagonal category.

The target is `F.obj (twObjMk' (x.fiber.base.hom ≫ f.base))` (same as source due to
how overOpToTwistedArrow maps f.fiber.base to the same twisted arrow target).
-/
theorem connGrothendieckContraFiberMorph_target_cat_eq
    {x y : ConnectedGrothendieckContra C F} (f : x ⟶ y) :
    F.obj ((overOpToTwistedArrow C y.base).obj
      (innerFiberContraTransitionObj C F f.base x.fiber).base) =
    F.obj (twObjMk' (x.fiber.base.hom ≫ f.base)) := by
  simp only [innerFiberContraTransitionObj, overOpToTwistedArrow, Over.map_obj_hom]

/--
The target category matches the diagonal via square_comm.
-/
theorem connGrothendieckContraFiberMorph_diag_eq
    {x y : ConnectedGrothendieckContra C F} (f : x ⟶ y) :
    F.obj (twObjMk' (x.fiber.base.hom ≫ f.base)) =
    F.obj (connGrothendieckDiagDom C (twObjMk' y.fiber.base.hom) f.fiber.base.left) := by
  simp only [connGrothendieckDiagDom, twObjMk'_arr]
  exact congrArg (F.obj ∘ twObjMk') (connGrothendieckContraSquare C F f)

/--
The diagonal equality for the fiberMorph construction (in the direction needed by
connGrothendieckDiagEq: DiagCod = DiagDom).
-/
theorem fiberMorph_diag_tw_eq {x y : ConnectedGrothendieckContra C F} (f : x ⟶ y) :
    connGrothendieckDiagCod C (twObjMk' x.fiber.base.hom) f.base =
    connGrothendieckDiagDom C (twObjMk' y.fiber.base.hom) f.fiber.base.left := by
  simp only [connGrothendieckDiagDom, connGrothendieckDiagCod, twObjMk'_arr]
  exact congrArg twObjMk' (connGrothendieckContraSquare C F f)

set_option backward.isDefEq.respectTransparency false in
/--
The target of `overOpToTwistedArrow.map f.fiber.base` equals DiagCod.
-/
theorem overOpToTwistedArrow_map_target_eq_diagCod
    {x y : ConnectedGrothendieckContra C F} (f : x ⟶ y) :
    (overOpToTwistedArrow C y.base).obj
      (innerFiberContraTransitionObj C F f.base x.fiber).base =
    connGrothendieckDiagCod C (twObjMk' x.fiber.base.hom) f.base := by
  simp only [innerFiberContraTransitionObj, overOpToTwistedArrow, Over.map_obj_hom,
    connGrothendieckDiagCod, twObjMk'_arr]

/--
`Over.map` preserves the `left` component of an Over object.
-/
@[simp]
theorem Over.map_obj_left {a b : C} (f : a ⟶ b) (x : Over a) :
    ((Over.map f).obj x).left = x.left := rfl

/--
The domain of DiagDom equals the domain of DiagCod (both are `x.fiber.base.left`).
-/
theorem twDom'_diagDom_eq_diagCod {x y : ConnectedGrothendieckContra C F} (f : x ⟶ y) :
    twDom' (connGrothendieckDiagDom C (twObjMk' y.fiber.base.hom) f.fiber.base.left) =
    twDom' (connGrothendieckDiagCod C (twObjMk' x.fiber.base.hom) f.base) := by
  simp only [connGrothendieckDiagDom, connGrothendieckDiagCod, twObjMk'_arr, twObjMk'_dom,
    fiberFunctorContra, Functor.id_obj, innerFiberContraTransition]
  rfl

/--
The codomain of DiagDom equals the codomain of DiagCod (both are `y.base`).
-/
theorem twCod'_diagDom_eq_diagCod {x y : ConnectedGrothendieckContra C F} (f : x ⟶ y) :
    twCod' (connGrothendieckDiagDom C (twObjMk' y.fiber.base.hom) f.fiber.base.left) =
    twCod' (connGrothendieckDiagCod C (twObjMk' x.fiber.base.hom) f.base) := by
  simp only [connGrothendieckDiagDom, connGrothendieckDiagCod, twObjMk'_arr, twObjMk'_cod]
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
The twisted arrow morphism `overOpToTwistedArrow.map f.fiber.base` equals
`connGrothendieckTwMorphDom ≫ eqToHom`.

Both have the same domain arrow (`f.fiber.base.left`) and codomain arrow (`𝟙 y.base`).
-/
theorem overOpToTwistedArrow_map_eq_twMorphDom_comp_eqToHom
    {x y : ConnectedGrothendieckContra C F} (f : x ⟶ y) :
    (overOpToTwistedArrow C y.base).map f.fiber.base =
    connGrothendieckTwMorphDom C (twObjMk' y.fiber.base.hom) f.fiber.base.left ≫
    eqToHom (fiberMorph_diag_tw_eq C F f).symm := by
  apply twHom'_ext
  · simp only [twDomArr'_comp, twDomArr'_eqToHom, connGrothendieckTwMorphDom,
      overOpToTwistedArrow, twHomMk'_domArr, twObjMk'_dom]
    simp only [connGrothendieckDiagDom, twObjMk'_dom, twObjMk'_arr, fiberFunctorContra,
      Functor.id_obj, eqToHom_refl, Category.id_comp]
    rfl
  · simp only [twCodArr'_comp, twCodArr'_eqToHom, connGrothendieckTwMorphDom,
      overOpToTwistedArrow, twHomMk'_codArr, twObjMk'_cod]
    simp only [connGrothendieckDiagDom, twObjMk'_cod, twObjMk'_arr, Functor.fromPUnit,
      eqToHom_refl, Category.comp_id]
    rfl

set_option backward.isDefEq.respectTransparency false in
/--
Convert a morphism in `ConnectedGrothendieckContra` to a `ConnGrothendieckHom`.
-/
def connGrothendieckContraHomToHom {x y : ConnectedGrothendieckContra C F}
    (f : x ⟶ y) :
    ConnGrothendieckHom C F
      (connGrothendieckContraObjToObj C F x)
      (connGrothendieckContraObjToObj C F y) where
  domArr := f.fiber.base.left
  codArr := f.base
  square_comm := by
    simp only [connGrothendieckContraObjToObj, twObjMk'_arr]
    exact connGrothendieckContraSquare C F f
  fiberMorph := by
    simp only [connGrothendieckContraObjToObj]
    rw [← fiberTransportTwMorph_eq_connGrothendieckTwMorphCod (β := f.base)]
    rw [← overOpToTwistedArrow_map_eq_twMorphDom_comp_eqToHom]
    exact f.fiber.fiber

/--
The inner base morphism for converting `ConnGrothendieckHom` to
`ConnectedGrothendieckContra` morphism.

Given `domArr : twDom' x.arrow ⟶ twDom' y.arrow` satisfying the square
condition, we construct an `Over.OverMorphism` from
`Over.mk (twArr' x.arrow ≫ codArr)` to `Over.mk (twArr' y.arrow)` in `Over b'`
where `b' = twCod' y.arrow`.
-/
def connGrothendieckHomToContraInnerBase {x y : ConnGrothendieckObj C F}
    (f : ConnGrothendieckHom C F x y) :
    Over.mk (twArr' x.arrow ≫ f.codArr) ⟶ Over.mk (twArr' y.arrow) :=
  Over.homMk f.domArr (by simp only [Over.mk_hom]; exact f.square_comm.symm)

/--
The transported source object in the inner fiber for the reverse conversion.
-/
def connGrothendieckHomToContraTransportedSource {x y : ConnGrothendieckObj C F}
    (f : ConnGrothendieckHom C F x y) :
    innerFiberContra C F (twCod' y.arrow) :=
  (innerFiberContraTransition C F f.codArr).obj
    ⟨Over.mk (twArr' x.arrow),
     (eqToHom (congrArg F.obj (twObjMk'_twArr' x.arrow).symm)).toFunctor.obj x.fiber⟩

/--
The base of the transported source equals `Over.mk (twArr' x.arrow ≫ f.codArr)`.
-/
theorem connGrothendieckHomToContraTransportedSource_base {x y : ConnGrothendieckObj C F}
    (f : ConnGrothendieckHom C F x y) :
    (connGrothendieckHomToContraTransportedSource C F f).base =
    Over.mk (twArr' x.arrow ≫ f.codArr) := by
  simp only [connGrothendieckHomToContraTransportedSource, innerFiberContraTransition,
    innerFiberContraTransitionObj]
  rfl

/--
The source fiber of the reverse conversion equals the fiberMorph source (up to eqToHom).

The source is `(fiberTransport f.codArr ...).obj ((eqToHom ...).obj x.fiber)`,
which equals `(F.map (connGrothendieckTwMorphCod ...)).obj x.fiber` up to eqToHom.
-/
theorem connGrothendieckHomToContra_source_eq {x y : ConnGrothendieckObj C F}
    (f : ConnGrothendieckHom C F x y) :
    (((fiberFunctorContra C F).map f.codArr).toFunctor.obj
      (connGrothendieckObjToContraObj C F x).fiber).fiber =
    (F.map (connGrothendieckTwMorphCod C x.arrow f.codArr)).toFunctor.obj x.fiber := by
  simp only [fiberFunctorContra, connGrothendieckObjToContraObj,
    innerFiberContraTransition]
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
The target twisted arrow morphism for the reverse conversion.

`overOpToTwistedArrow.map innerBase` goes from `y.arrow` to `DiagCod x.arrow f.codArr`,
while `connGrothendieckTwMorphDom` goes from `y.arrow` to `DiagDom y.arrow f.domArr`.
By the diagonal equality, these targets are equal.
-/
theorem overOpToTwArr_map_innerBase_eq {x y : ConnGrothendieckObj C F}
    (f : ConnGrothendieckHom C F x y) :
    (overOpToTwistedArrow C (twCod' y.arrow)).map (connGrothendieckHomToContraInnerBase C F f) =
    connGrothendieckTwMorphDom C y.arrow f.domArr ≫
    eqToHom (connGrothendieckDiagEq C F x y f.domArr f.codArr f.square_comm) := by
  apply twHom'_ext
  · simp only [twDomArr'_comp, twDomArr'_eqToHom, connGrothendieckTwMorphDom, twHomMk'_domArr,
      overOpToTwistedArrow, connGrothendieckHomToContraInnerBase, Over.homMk_left, id]
    simp only [connGrothendieckDiagDom, twObjMk'_dom, eqToHom_refl, Category.id_comp]
  · simp only [twCodArr'_comp, twCodArr'_eqToHom, connGrothendieckTwMorphDom, twHomMk'_codArr,
      overOpToTwistedArrow, connGrothendieckHomToContraInnerBase, id]
    simp only [connGrothendieckDiagDom, twObjMk'_cod, eqToHom_refl, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
/--
Convert a `ConnGrothendieckHom` to a morphism in `ConnectedGrothendieckContra`.
-/
def connGrothendieckHomToContraHom {x y : ConnGrothendieckObj C F}
    (f : ConnGrothendieckHom C F x y) :
    connGrothendieckObjToContraObj C F x ⟶ connGrothendieckObjToContraObj C F y := by
  refine ⟨f.codArr, ?_⟩
  refine ⟨?innerBase, ?innerFiber⟩
  case innerBase =>
    exact connGrothendieckHomToContraInnerBase C F f
  case innerFiber =>
    simp only [fiberFunctorContra, connGrothendieckObjToContraObj,
      innerFiberContraTransition]
    unfold Cat.Hom.toFunctor Functor.toCatHom
    simp only [innerFiberContraTransitionObj, fiberTransport,
      restrictToFiber, Functor.comp_obj, Functor.comp_map]
    rw [fiberTransportTwMorph_eq_connGrothendieckTwMorphCod']
    rw [overOpToTwArr_map_innerBase_eq]
    simp only [Over.mk_hom, twObjMk'_twArr']
    exact f.fiberMorph

set_option backward.isDefEq.respectTransparency false in
/--
Round-trip: converting a `ConnGrothendieckHom` to `ConnectedGrothendieckContra` morphism
and back gives the original morphism (up to the object round-trip equality).
-/
theorem connGrothendieckHom_roundtrip {x y : ConnGrothendieckObj C F}
    (f : ConnGrothendieckHom C F x y) :
    HEq (connGrothendieckContraHomToHom C F (connGrothendieckHomToContraHom C F f)) f := by
  have hx : connGrothendieckContraObjToObj C F (connGrothendieckObjToContraObj C F x) = x :=
    connGrothendieckObj_contraRoundtrip C F x
  have hy : connGrothendieckContraObjToObj C F (connGrothendieckObjToContraObj C F y) = y :=
    connGrothendieckObj_contraRoundtrip C F y
  cases hx
  cases hy
  apply heq_of_eq
  simp only [connGrothendieckContraHomToHom, connGrothendieckHomToContraHom,
    connGrothendieckHomToContraInnerBase, Over.homMk_left]
  obtain ⟨domArr, codArr, square_comm, fiberMorph⟩ := f
  congr 1
  simp only [id_eq]
  apply eq_of_heq
  refine HEq.trans (cast_heq _ _) ?_
  exact cast_heq _ _

set_option backward.isDefEq.respectTransparency false in
/--
Round-trip: converting a `ConnectedGrothendieckContra` morphism to `ConnGrothendieckHom`
and back gives the original morphism (up to the object round-trip equality).
-/
theorem connGrothendieckContraHom_roundtrip {x y : ConnectedGrothendieckContra C F}
    (f : x ⟶ y) :
    HEq (connGrothendieckHomToContraHom C F (connGrothendieckContraHomToHom C F f)) f := by
  have hx : connGrothendieckObjToContraObj C F (connGrothendieckContraObjToObj C F x) = x :=
    connGrothendieckContraObj_roundtrip C F x
  have hy : connGrothendieckObjToContraObj C F (connGrothendieckContraObjToObj C F y) = y :=
    connGrothendieckContraObj_roundtrip C F y
  cases hx
  cases hy
  apply heq_of_eq
  simp only [connGrothendieckHomToContraHom, connGrothendieckContraHomToHom,
    connGrothendieckHomToContraInnerBase]
  refine Grothendieck.ext _ _ ?_ ?_
  · rfl
  · simp only [eqToHom_refl, Category.id_comp]
    refine GrothendieckContra'.ext _ _ ?_ ?_
    · ext
      rfl
    · simp only [eqToHom_refl, Category.comp_id]
      simp only [id_eq]
      have mpr_heq : ∀ {α β : Sort _} (h : α = β) (b : β), h.mpr b ≍ b := by
        intros α β h b
        subst h
        rfl
      apply eq_of_heq
      refine HEq.trans (mpr_heq _ _) ?_
      refine HEq.trans (mpr_heq _ _) ?_
      refine HEq.trans (mpr_heq _ _) ?_
      exact mpr_heq _ _

end MorphismEquivalence

end ConnectedGrothendieckContraMorphisms

end NestedGrothendieckApproach

section ProjectionFunctor

/-!
## Projection Functor to Arrow Category

The connected Grothendieck construction comes equipped with a projection functor
`π_F : E(F) → Arr(C)` that forgets the fiber data.

On objects: `(f : a → b, e)` maps to `f` viewed as an arrow.
On morphisms: `(domArr, codArr, φ)` maps to `(domArr, codArr)`.
-/

variable (C : Type u) [Category.{v} C]
variable (F : TwistedArrow' C ⥤ Cat.{v, u})

/--
Convert a `ConnectedGrothendieckContra` object to an `Arrow` object.

An object of `ConnectedGrothendieckContra` has:
- `x.base : C` (the codomain of the underlying arrow)
- `x.fiber.base : (Over x.base)ᵒᵖ'` (whose `.hom` is the arrow itself)

The underlying arrow is `x.fiber.base.hom : x.fiber.base.left ⟶ x.base`.
-/
def connGrothendieckContraObjToArrow (x : ConnectedGrothendieckContra C F) :
    Arrow C :=
  Arrow.mk x.fiber.base.hom

set_option backward.isDefEq.respectTransparency false in
/--
For identity morphisms, the domain arrow component is identity.
-/
theorem connGrothendieckContraHomDomArr_id (x : ConnectedGrothendieckContra C F) :
    connGrothendieckContraHomDomArr C F (𝟙 x) = 𝟙 x.fiber.base.left := by
  unfold connGrothendieckContraHomDomArr
  rw [Grothendieck.id_fiber]
  rw [GrothendieckContra'.base_eqToHom]
  rw [Over.eqToHom_left]
  rfl

/--
For identity morphisms, the codomain arrow component is identity.
-/
theorem connGrothendieckContraHomCodArr_id (x : ConnectedGrothendieckContra C F) :
    connGrothendieckContraHomCodArr C F (𝟙 x) = 𝟙 x.base :=
  rfl

/--
For morphisms in `GrothendieckContra'`, composition of `.base.left` equals
`.left` of `.base` composition.
-/
lemma grothendieckContra'_comp_base_left {b : C}
    {x y z : GrothendieckContra' (restrictToFiber C F b)}
    (f : x ⟶ y) (g : y ⟶ z) :
    (f ≫ g).base.left = f.base.left ≫ g.base.left :=
  rfl

/--
The transition functor preserves `.base.left`: applying `(fiberFunctorContra C F).map β`
to a morphism `f` gives a morphism whose `.base.left` equals `f.base.left`.
-/
lemma fiberFunctorContra_map_base_left {b d : C} (β : b ⟶ d)
    {x y : innerFiberContra C F b} (f : x ⟶ y) :
    (((fiberFunctorContra C F).map β).toFunctor.map f).base.left = f.base.left := by
  unfold Cat.Hom.toFunctor
  simp only [fiberFunctorContra, innerFiberContraTransition]
  rfl

/--
For `eqToHom` in `GrothendieckContra'`, the `.base.left` is `eqToHom` in `C`.
-/
lemma grothendieckContra'_eqToHom_base_left {b : C}
    {x y : GrothendieckContra' (restrictToFiber C F b)} (h : x = y) :
    (eqToHom h).base.left = eqToHom (by subst h; rfl) := by
  subst h
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
The domain arrow composition: `(f ≫ g).domArr = f.domArr ≫ g.domArr`.
-/
theorem connGrothendieckContraHomDomArr_comp
    {x y z : ConnectedGrothendieckContra C F}
    (f : x ⟶ y) (g : y ⟶ z) :
    connGrothendieckContraHomDomArr C F (f ≫ g) =
      connGrothendieckContraHomDomArr C F f ≫
        connGrothendieckContraHomDomArr C F g := by
  simp only [connGrothendieckContraHomDomArr]
  change (f ≫ g).fiber.base.left = f.fiber.base.left ≫ g.fiber.base.left
  rw [Grothendieck.comp_fiber]
  rw [grothendieckContra'_comp_base_left, grothendieckContra'_comp_base_left]
  rw [grothendieckContra'_eqToHom_base_left, eqToHom_refl, Category.id_comp]
  rw [fiberFunctorContra_map_base_left]

/--
The codomain arrow composition: `(f ≫ g).codArr = f.codArr ≫ g.codArr`.
-/
theorem connGrothendieckContraHomCodArr_comp
    {x y z : ConnectedGrothendieckContra C F}
    (f : x ⟶ y) (g : y ⟶ z) :
    connGrothendieckContraHomCodArr C F (f ≫ g) =
      connGrothendieckContraHomCodArr C F f ≫
        connGrothendieckContraHomCodArr C F g :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
The projection functor from `ConnectedGrothendieckContra` to the arrow category.

This functor forgets the fiber data:
- On objects: extracts the underlying arrow from the nested Grothendieck structure
- On morphisms: extracts `(domArr, codArr)` forming a commutative square
-/
def connGrothendieckContraProjection :
    ConnectedGrothendieckContra C F ⥤ Arrow C where
  obj x := connGrothendieckContraObjToArrow C F x
  map {x y} f := Arrow.homMk
    (connGrothendieckContraHomDomArr C F f)
    (connGrothendieckContraHomCodArr C F f)
    (connGrothendieckContraMorphSquareComm C F f).symm
  map_id x := by
    apply Arrow.hom_ext
    · simp only [Arrow.homMk_left, Arrow.id_left, connGrothendieckContraHomDomArr_id,
        connGrothendieckContraObjToArrow, Arrow.mk_left]
      rfl
    · simp only [Arrow.homMk_right, Arrow.id_right, connGrothendieckContraHomCodArr_id,
        connGrothendieckContraObjToArrow, Arrow.mk_right]
      rfl
  map_comp {x y z} f g := by
    apply Arrow.hom_ext
    · simp only [Arrow.comp_left, Arrow.homMk_left, connGrothendieckContraHomDomArr_comp]
    · simp only [Arrow.comp_right, Arrow.homMk_right, connGrothendieckContraHomCodArr_comp]

/--
The projection preserves domain extraction.
-/
@[simp]
lemma connGrothendieckContraProjection_obj_left
    (x : ConnectedGrothendieckContra C F) :
    ((connGrothendieckContraProjection C F).obj x).left = x.fiber.base.left :=
  rfl

/--
The projection preserves codomain extraction.
-/
@[simp]
lemma connGrothendieckContraProjection_obj_right
    (x : ConnectedGrothendieckContra C F) :
    ((connGrothendieckContraProjection C F).obj x).right = x.base :=
  rfl

/--
The projection preserves the underlying arrow.
-/
@[simp]
lemma connGrothendieckContraProjection_obj_hom
    (x : ConnectedGrothendieckContra C F) :
    ((connGrothendieckContraProjection C F).obj x).hom = x.fiber.base.hom :=
  rfl

/--
The projection preserves the left morphism component (domain arrow).
-/
@[simp]
lemma connGrothendieckContraProjection_map_left
    {x y : ConnectedGrothendieckContra C F} (f : x ⟶ y) :
    ((connGrothendieckContraProjection C F).map f).left =
      connGrothendieckContraHomDomArr C F f :=
  rfl

/--
The projection preserves the right morphism component (codomain arrow).
-/
@[simp]
lemma connGrothendieckContraProjection_map_right
    {x y : ConnectedGrothendieckContra C F} (f : x ⟶ y) :
    ((connGrothendieckContraProjection C F).map f).right =
      connGrothendieckContraHomCodArr C F f :=
  rfl

end ProjectionFunctor

section Functoriality

/-!
## Functoriality of Connected Grothendieck Construction

A natural transformation `α : F ⟶ G` between functors `F G : Tw(C) ⥤ Cat`
induces a functor between the corresponding connected Grothendieck categories.
This makes the connected Grothendieck construction into a functor

```
(TwistedArrow' C ⥤ Cat) ⥤ Over (Cat.of (Arrow C))
```
-/

variable {F G H : TwistedArrow' C ⥤ Cat.{v, u}}

/--
A natural transformation `α : F ⟶ G` induces a natural transformation between
the restricted fiber functors.
-/
def restrictToFiberNatTrans (α : F ⟶ G) (b : C) :
    restrictToFiber C F b ⟶ restrictToFiber C G b :=
  Functor.whiskerLeft (overOpToTwistedArrow C b) α

@[simp]
theorem restrictToFiberNatTrans_id (b : C) :
    restrictToFiberNatTrans C (𝟙 F) b = 𝟙 (restrictToFiber C F b) := by
  simp only [restrictToFiberNatTrans, Functor.whiskerLeft_id', restrictToFiber]

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem restrictToFiberNatTrans_comp (α : F ⟶ G) (β : G ⟶ H) (b : C) :
    restrictToFiberNatTrans C (α ≫ β) b =
      restrictToFiberNatTrans C α b ≫ restrictToFiberNatTrans C β b := by
  simp only [restrictToFiberNatTrans, Functor.whiskerLeft_comp]

/--
A natural transformation `α : F ⟶ G` induces a functor between the inner
fiber categories for each `b : C`.
-/
def innerFiberContraMap (α : F ⟶ G) (b : C) :
    innerFiberContra C F b ⥤ innerFiberContra C G b :=
  GrothendieckContra'.map (restrictToFiberNatTrans C α b)

@[simp]
theorem innerFiberContraMap_id (b : C) :
    innerFiberContraMap C (𝟙 F) b =
      Cat.Hom.toFunctor (𝟙 (Cat.of (innerFiberContra C F b))) := by
  simp only [innerFiberContraMap, restrictToFiberNatTrans_id,
    GrothendieckContra'.map_id_eq, innerFiberContra, Cat.Hom.id_toFunctor]
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem innerFiberContraMap_comp (α : F ⟶ G) (β : G ⟶ H) (b : C) :
    innerFiberContraMap C (α ≫ β) b =
      innerFiberContraMap C α b ⋙ innerFiberContraMap C β b := by
  simp only [innerFiberContraMap, restrictToFiberNatTrans_comp,
    GrothendieckContra'.map_comp_eq]

@[simp]
theorem innerFiberContraMap_obj (α : F ⟶ G) (b : C)
    (x : innerFiberContra C F b) :
    (innerFiberContraMap C α b).obj x =
      ⟨x.base, (α.app ((overOpToTwistedArrow C b).obj x.base)).toFunctor.obj x.fiber⟩ := by
  simp only [innerFiberContraMap, restrictToFiberNatTrans]
  rfl

/--
The inner fiber map preserves the base component of objects.
-/
@[simp]
theorem innerFiberContraMap_obj_base (α : F ⟶ G) (b : C)
    (x : innerFiberContra C F b) :
    ((innerFiberContraMap C α b).obj x).base = x.base :=
  rfl

/--
The inner fiber map preserves base morphisms.
-/
theorem innerFiberContraMap_map_base (α : F ⟶ G) (b : C)
    {x y : innerFiberContra C F b} (f : x ⟶ y) :
    ((innerFiberContraMap C α b).map f).base = f.base :=
  rfl

/--
Naturality of `innerFiberContraMap` with respect to base morphisms `β : b ⟶ d`.
This shows that the square commutes on objects.
-/
theorem innerFiberContraMap_natural_obj (α : F ⟶ G) {b d : C} (β : b ⟶ d)
    (x : innerFiberContra C F b) :
    (innerFiberContraMap C α d).obj ((innerFiberContraTransition C F β).obj x) =
    (innerFiberContraTransition C G β).obj ((innerFiberContraMap C α b).obj x) := by
  have nat_eq := α.naturality (fiberTransportTwMorph C β x.base)
  have functor_eq := congrArg Cat.Hom.toFunctor nat_eq
  rw [Cat.Hom.comp_toFunctor, Cat.Hom.comp_toFunctor] at functor_eq
  have h := Functor.congr_obj functor_eq x.fiber
  simp only [Functor.comp_obj] at h
  apply GrothendieckContra'.obj_ext
  · rfl
  · simp only [innerFiberContraMap, innerFiberContraTransition,
      innerFiberContraTransitionObj, GrothendieckContra'.map_obj, restrictToFiberNatTrans,
      Functor.whiskerLeft_app, fiberTransport, overOpToTwistedArrow, Over.map_obj_hom]
    exact heq_of_eq h

/--
The natural transformation between fiber functors induced by `α : F ⟶ G`.
-/
@[simp]
theorem innerFiberContraTransition_map_base {b d : C} (β : b ⟶ d)
    {x y : innerFiberContra C F b} (f : x ⟶ y) :
    ((innerFiberContraTransition C F β).map f).base = (Over.map β).map f.base :=
  rfl

-- Helper lemma for LHS of fiberFunctorContraNatTrans naturality
theorem fiberFunctorContra_map_map_base {b d : C} (β : b ⟶ d)
    {x y : innerFiberContra C F b} (f : x ⟶ y) :
    (((fiberFunctorContra C F).map β).toFunctor.map f).base = (Over.map β).map f.base :=
  rfl

set_option backward.isDefEq.respectTransparency false in
-- Helper lemma for RHS of fiberFunctorContraNatTrans naturality
-- Shows that eqToHom compositions don't change the base result
theorem fiberFunctorContraNatTrans_rhs_base_eq (α : F ⟶ G) {b d : C} (β : b ⟶ d)
    {X Y : innerFiberContra C F b} (f : X ⟶ Y)
    (hX : (innerFiberContraMap C α d).obj
      ((innerFiberContraTransition C F β).obj X) =
      (innerFiberContraTransition C G β).obj
      ((innerFiberContraMap C α b).obj X))
    (hY : (innerFiberContraMap C α d).obj
      ((innerFiberContraTransition C F β).obj Y) =
      (innerFiberContraTransition C G β).obj
      ((innerFiberContraMap C α b).obj Y)) :
    (eqToHom hX ≫ ((fiberFunctorContra C G).map β).toFunctor.map
      ((innerFiberContraMap C α b).map f) ≫ eqToHom hY.symm).base =
    (Over.map β).map f.base := by
  -- Unfold category structure and apply comp_base
  simp +instances only [
    innerFiberContraCategory,
    GrothendieckContra'.GrothendieckContraInst',
    GrothendieckContra'.comp_base]
  -- Apply base_eqToHom to the eqToHom terms
  conv_lhs => rw [GrothendieckContra'.base_eqToHom, GrothendieckContra'.base_eqToHom]
  -- Simplify toCatHom.toFunctor back to underlying functor and apply fiberFunctorContra
  simp only [Functor.toCatHom_toFunctor, fiberFunctorContra,
             innerFiberContraTransition_map_base, innerFiberContraMap_map_base]
  -- The eqToHom terms should cancel
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

/--
Naturality of a natural transformation `α : F ⟶ G` with respect to fiber transport.
This says that `α` commutes with the fiber transport functors.
-/
theorem alpha_fiberTransport_naturality (α : F ⟶ G) {b d : C} (β : b ⟶ d)
    (ov : (Over b)ᵒᵖ') :
    (α.app ((overOpToTwistedArrow C b).obj ov)).toFunctor ⋙ fiberTransport C G β ov =
    fiberTransport C F β ov ⋙
      (α.app ((overOpToTwistedArrow C d).obj ((Over.map β).obj ov))).toFunctor := by
  simp only [fiberTransport]
  have nat := α.naturality (fiberTransportTwMorph C β ov)
  have functor_eq := congrArg Cat.Hom.toFunctor nat
  rw [Cat.Hom.comp_toFunctor, Cat.Hom.comp_toFunctor] at functor_eq
  exact functor_eq.symm

/--
For eqToHom between equal functors, the app component is eqToHom at the object
level.
-/
theorem eqToHom_functor_app' {A B : Type*} [Category A] [Category B]
    {F₁ F₂ : A ⥤ B} (h : F₁ = F₂) (x : A) :
    (eqToHom h).app x = eqToHom (congrArg (·.obj x) h) := by
  subst h
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
Core naturality of `innerFiberContraMap` with respect to transition functors
at the fiber level.
-/
theorem innerFiberContraMap_naturality_fiber (α : F ⟶ G) {b d : C} (β : b ⟶ d)
    {X Y : innerFiberContra C F b} (f : X ⟶ Y) :
    ((innerFiberContraMap C α d).map ((innerFiberContraTransition C F β).map f)).fiber ≍
    ((innerFiberContraTransition C G β).map ((innerFiberContraMap C α b).map f)).fiber := by
  -- Unfold innerFiberContraMap using GrothendieckContra'.map_map
  simp only [innerFiberContraMap]
  erw [GrothendieckContra'.map_map, GrothendieckContra'.map_map]
  -- Unfold innerFiberContraTransition using innerFiberContraTransitionHom_fiber
  simp only [innerFiberContraTransition, innerFiberContraTransitionHom_fiber]
  -- restrictToFiberNatTrans is just whiskerLeft, so app = α.app
  simp only [restrictToFiberNatTrans, Functor.whiskerLeft_app]
  -- GrothendieckContra'.map preserves the base
  simp only [GrothendieckContra'.map_obj]
  -- innerFiberContraTransitionObj.base = (Over.map β).obj X.base
  simp only [innerFiberContraTransitionObj]
  -- Both sides simplify to the same core, differing only in eqToHom transport
  simp only [Functor.map_comp, eqToHom_map, Category.assoc]
  -- Use naturality of α
  have alpha_nat := alpha_fiberTransport_naturality C α β X.base
  have alpha_nat_mor := Functor.congr_hom alpha_nat f.fiber
  simp only [Functor.comp_map] at alpha_nat_mor
  -- Rewrite RHS using alpha_nat_mor
  conv_rhs => rw [alpha_nat_mor]
  simp only [Category.assoc]
  -- Convert (eqToHom h).toNatTrans.app to eqToHom on LHS
  rw [Cat.eqToHom_app]
  -- Collapse adjacent eqToHom on LHS
  simp only [eqToHom_trans]
  -- Convert (eqToHom h).toNatTrans.app on RHS to eqToHom
  conv_rhs => rw [Cat.eqToHom_app]
  -- Convert F.map (eqToHom h) to eqToHom on RHS
  simp only [functor_map_eqToHom]
  -- Collapse adjacent eqToHom on RHS
  simp only [eqToHom_trans]
  -- Goal: core ≫ eqToHom ⋯ ≍ eqToHom ⋯ ≫ core ≫ eqToHom ⋯
  -- Strip leading eqToHom from RHS
  apply HEq.symm
  apply HEq.trans (eqToHom_comp_heq _ _)
  -- Goal: core ≫ eqToHom ⋯ ≍ core ≫ eqToHom ⋯
  apply HEq.symm
  -- Both sides have form core ≫ eqToHom _
  -- Use transitivity: core ≫ eqToHom h1 ≍ core ≍ core ≫ eqToHom h2
  apply HEq.trans (comp_eqToHom_heq _ _)
  exact (comp_eqToHom_heq _ _).symm

set_option backward.isDefEq.respectTransparency false in
def fiberFunctorContraNatTrans (α : F ⟶ G) :
    fiberFunctorContra C F ⟶ fiberFunctorContra C G where
  app b := (innerFiberContraMap C α b).toCatHom
  naturality {b d} β := by
    apply Cat.Hom.ext
    simp only [Cat.Hom.comp_toFunctor, Functor.toCatHom_toFunctor]
    fapply _root_.CategoryTheory.Functor.ext
    · intro x
      exact innerFiberContraMap_natural_obj C α β x
    · intro X Y f
      apply GrothendieckContra'.ext
      case w_base =>
        -- Decompose functor composition and simplify base map
        simp only [Functor.comp_map, innerFiberContraMap_map_base]
        -- LHS = (Over.map β).map f.base by fiberFunctorContra_map_map_base
        -- RHS = (Over.map β).map f.base by fiberFunctorContraNatTrans_rhs_base_eq
        rw [fiberFunctorContra_map_map_base]
        rw [fiberFunctorContraNatTrans_rhs_base_eq C α β f
            (innerFiberContraMap_natural_obj C α β X)
            (innerFiberContraMap_natural_obj C α β Y)]
      case w_fiber =>
        -- Use heterogeneous equality approach
        apply eq_of_heq
        apply HEq.trans (comp_eqToHom_heq _ _)
        -- Use naturality lemma
        apply HEq.trans (innerFiberContraMap_naturality_fiber C α β f)
        -- Handle the conjugation with eqToHom
        exact (GrothendieckContra'.conj_eqToHom_fiber_heq _ _ _).symm

@[simp]
theorem fiberFunctorContraNatTrans_id :
    fiberFunctorContraNatTrans C (𝟙 F) = 𝟙 (fiberFunctorContra C F) := by
  ext b
  simp only [fiberFunctorContraNatTrans, innerFiberContraMap_id, NatTrans.id_app,
    fiberFunctorContra, innerFiberContra, Functor.toCatHom_toFunctor]

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem fiberFunctorContraNatTrans_comp (α : F ⟶ G) (β : G ⟶ H) :
    fiberFunctorContraNatTrans C (α ≫ β) =
      fiberFunctorContraNatTrans C α ≫ fiberFunctorContraNatTrans C β := by
  ext b
  simp only [Functor.toCatHom_toFunctor, fiberFunctorContraNatTrans, innerFiberContraMap_comp,
    NatTrans.comp_app, Cat.comp_eq_comp]

/--
A natural transformation `α : F ⟶ G` induces a functor between the
connected Grothendieck categories.
-/
def connGrothendieckContraMap (α : F ⟶ G) :
    ConnectedGrothendieckContra C F ⥤ ConnectedGrothendieckContra C G :=
  Grothendieck.map (fiberFunctorContraNatTrans C α)

@[simp]
theorem connGrothendieckContraMap_obj (α : F ⟶ G)
    (x : ConnectedGrothendieckContra C F) :
    (connGrothendieckContraMap C α).obj x =
      ⟨x.base, (innerFiberContraMap C α x.base).obj x.fiber⟩ :=
  rfl

@[simp]
theorem connGrothendieckContraMap_map_base (α : F ⟶ G)
    {x y : ConnectedGrothendieckContra C F} (f : x ⟶ y) :
    ((connGrothendieckContraMap C α).map f).base = f.base :=
  rfl

/--
For eqToHom between equal functors, the app component is eqToHom at the object level.
-/
theorem eqToHom_functor_app {A B : Type*} [Category A] [Category B]
    {F₁ F₂ : A ⥤ B} (h : F₁ = F₂) (x : A) :
    (eqToHom h).app x = eqToHom (congrArg (·.obj x) h) := by
  subst h
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
The map functor preserves the left component of the fiber's base.
-/
@[simp]
theorem connGrothendieckContraMap_map_fiber_base_left (α : F ⟶ G)
    {X Y : ConnectedGrothendieckContra C F} (f : X ⟶ Y) :
    ((connGrothendieckContraMap C α).map f).fiber.base.left = f.fiber.base.left := by
  simp only [connGrothendieckContraMap, fiberFunctorContraNatTrans]
  -- fiber = (eqToHom nat.symm).app X.fiber ≫ (innerFiberContraMap C α Y.base).map f.fiber
  erw [GrothendieckContra'.comp_base]
  simp only [Functor.toCatHom_toFunctor, innerFiberContraMap_map_base]
  -- Goal: (((eqToHom ⋯).toNatTrans.app X.fiber).base ≫ f.fiber.base).left = f.fiber.base.left
  -- The eqToHom arises from naturality of fiberFunctorContraNatTrans
  rw [Cat.eqToHom_app]
  -- Now: ((eqToHom _).base ≫ f.fiber.base).left = f.fiber.base.left
  erw [GrothendieckContra'.base_eqToHom]
  -- Now: (eqToHom _ ≫ f.fiber.base).left = f.fiber.base.left
  simp only [eqToHom_refl, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
/--
The map functor commutes with the projection to `Arrow C`.
-/
theorem connGrothendieckContraMap_comp_projection (α : F ⟶ G) :
    connGrothendieckContraMap C α ⋙ connGrothendieckContraProjection C G =
    connGrothendieckContraProjection C F := by
  fapply _root_.CategoryTheory.Functor.ext
  · intro x
    simp only [Functor.comp_obj, connGrothendieckContraProjection,
      connGrothendieckContraMap_obj, connGrothendieckContraObjToArrow,
      innerFiberContraMap_obj_base]
  · intro X Y f
    apply Arrow.hom_ext
    · -- Left component: show fiber.base.left is preserved
      simp only [Functor.comp_map, connGrothendieckContraProjection, Arrow.homMk_left,
        connGrothendieckContraHomDomArr, eqToHom_refl, Category.id_comp, Category.comp_id,
        connGrothendieckContraMap_map_fiber_base_left]
    · simp only [Functor.comp_map, connGrothendieckContraProjection, Arrow.homMk_right,
        connGrothendieckContraHomCodArr, connGrothendieckContraMap_map_base,
        eqToHom_refl, Category.id_comp, Category.comp_id]

/--
The identity natural transformation maps to the identity functor.
-/
@[simp]
theorem connGrothendieckContraMap_id :
    connGrothendieckContraMap C (𝟙 F) =
      𝟭 (ConnectedGrothendieckContra C F) := by
  simp only [connGrothendieckContraMap, fiberFunctorContraNatTrans_id,
    Grothendieck.map_id_eq, ConnectedGrothendieckContra]

set_option backward.isDefEq.respectTransparency false in
/--
Composition of natural transformations maps to composition of functors.
-/
@[simp]
theorem connGrothendieckContraMap_comp (α : F ⟶ G) (β : G ⟶ H) :
    connGrothendieckContraMap C (α ≫ β) =
      connGrothendieckContraMap C α ⋙ connGrothendieckContraMap C β := by
  simp only [connGrothendieckContraMap, fiberFunctorContraNatTrans_comp,
    Grothendieck.map_comp_eq]

/--
The connected Grothendieck construction as a functor to the over category
`Over (Cat.of (Arrow C))`.
-/
def connGrothendieckContraFunctor :
    (TwistedArrow' C ⥤ Cat.{v, u}) ⥤ Over (Cat.of (Arrow C)) where
  obj F' := Over.mk (Y := Cat.of (ConnectedGrothendieckContra C F'))
    (connGrothendieckContraProjection C F').toCatHom
  map {F' G'} α := Over.homMk (connGrothendieckContraMap C α).toCatHom
    (by apply Cat.Hom.ext
        simp only [Cat.Hom.comp_toFunctor, Functor.toCatHom_toFunctor]
        exact connGrothendieckContraMap_comp_projection C α)
  map_id F' := by
    apply Over.OverMorphism.ext
    simp only [Over.mk_left, Over.homMk_left]
    apply Cat.Hom.ext
    simp only [Functor.toCatHom_toFunctor]
    exact connGrothendieckContraMap_id C
  map_comp {F' G' H'} α β := by
    apply Over.OverMorphism.ext
    simp only [Over.mk_left, Over.homMk_left]
    apply Cat.Hom.ext
    simp only [Functor.toCatHom_toFunctor]
    exact connGrothendieckContraMap_comp C α β

end Functoriality

/-!
## Presheaf Connected Grothendieck Construction

This section defines the connected Grothendieck construction for presheaves
on twisted arrows: functors `G : Tw(C)^op' ⥤ Cat`.

The construction follows the same pattern as `GrothendieckContra'`:

```
GrothendieckContra' F' = (Grothendieck (Cat.postCompOpFunctor'.obj F'))^op'
```

For `G : Tw(C)^op → Cat`, we define:

```
ConnectedGrothendieckPresheaf G = (ConnectedGrothendieckContra C^op H')^op'
```

where:
1. Use `Tw(C) ≅ Tw(C^op)` to view `G` as `H : Tw(C^op)^op → Cat`
2. `H' = Cat.postCompOpFunctor'.obj H : Tw(C^op) → Cat` (covariant)
3. Apply copresheaf construction over `C^op`
4. Take `op'` of the result

This produces a category over `Arrow C` with morphisms going in the correct
direction for a presheaf construction.
-/

section PresheafConnectedGrothendieck

variable {C : Type u} [Category.{v} C]
variable (C)
variable (G : (TwistedArrow' C)ᵒᵖ' ⥤ Cat.{v, u})

/-!
### Direct Presheaf Connected Grothendieck Construction

The presheaf connected Grothendieck construction is defined directly for
`G : (TwistedArrow' C)ᵒᵖ' ⥤ Cat`, analogous to how `GrothendieckContra'` is
defined for presheaves.
-/

/--
Objects of the presheaf connected Grothendieck construction for `G : Tw(C)^op' ⥤ Cat`.
An object consists of a twisted arrow and a fiber element.
-/
structure ConnGrothendieckPresheafObj where
  /-- The underlying twisted arrow -/
  tw : TwistedArrow' C
  /-- An element in the fiber category `G.obj tw` -/
  fiber : G.obj tw

/--
Morphisms in the presheaf connected Grothendieck construction.

For `G : (TwistedArrow' C)ᵒᵖ' ⥤ Cat`, a morphism from `(tw₁, e₁)` to `(tw₂, e₂)` consists of:
- A morphism `twMorph : tw₁ ⟶ tw₂` in `TwistedArrow' C`
- A morphism `fiberMorph : e₁ ⟶ (G.map twMorph).obj e₂` in `G.obj tw₁`

The fiber morphism goes to the pullback of `e₂` along `twMorph` because `G` is
contravariant: viewing `twMorph : tw₁ ⟶ tw₂` in `TwistedArrow' C` as a morphism
`tw₂ ⟶ tw₁` in `(TwistedArrow' C)ᵒᵖ'`, we get `G.map twMorph : G.obj tw₂ ⥤ G.obj tw₁`.
-/
structure ConnGrothendieckPresheafHom (X Y : ConnGrothendieckPresheafObj C G) where
  /-- The morphism between twisted arrows -/
  twMorph : X.tw ⟶ Y.tw
  /-- The fiber morphism going to the pullback -/
  fiberMorph : X.fiber ⟶ (G.map twMorph).toFunctor.obj Y.fiber

namespace ConnGrothendieckPresheafHom

variable {C G}

/-- The fiber codomain equality for identity morphisms -/
theorem id_fiber_cod_eq (X : ConnGrothendieckPresheafObj C G) :
    (G.map (𝟙 X.tw)).toFunctor.obj X.fiber = X.fiber := by
  have h : G.map (𝟙 X.tw) = 𝟙 (G.obj X.tw) := G.map_id X.tw
  conv_lhs => rw [h]
  rw [Cat.Hom.id_toFunctor]
  rfl

/-- Identity morphism in the presheaf connected Grothendieck construction -/
def id (X : ConnGrothendieckPresheafObj C G) : ConnGrothendieckPresheafHom C G X X where
  twMorph := 𝟙 X.tw
  fiberMorph := eqToHom (id_fiber_cod_eq X).symm

/-- The fiber codomain equality for composed morphisms.
For `G : (TwistedArrow' C)ᵒᵖ' ⥤ Cat`, the composition `g.twMorph ≫ f.twMorph` in the opposite
category equals `f.twMorph ≫ g.twMorph` at the underlying level.
-/
theorem comp_fiber_cod_eq {X Y Z : ConnGrothendieckPresheafObj C G}
    (f : ConnGrothendieckPresheafHom C G X Y) (g : ConnGrothendieckPresheafHom C G Y Z) :
    (G.map f.twMorph).toFunctor.obj ((G.map g.twMorph).toFunctor.obj Z.fiber) =
    (G.map (@CategoryStruct.comp (TwistedArrow' C) _ _ _ _ f.twMorph g.twMorph)).toFunctor.obj
      Z.fiber := by
  conv_lhs => rw [← Functor.comp_obj]
  conv_lhs => rw [← Cat.Hom.comp_toFunctor]
  congr 2
  exact (G.map_comp g.twMorph f.twMorph).symm

/-- Composition of morphisms in the presheaf connected Grothendieck construction -/
def comp {X Y Z : ConnGrothendieckPresheafObj C G}
    (f : ConnGrothendieckPresheafHom C G X Y)
    (g : ConnGrothendieckPresheafHom C G Y Z) :
    ConnGrothendieckPresheafHom C G X Z where
  twMorph := @CategoryStruct.comp (TwistedArrow' C) _ _ _ _ f.twMorph g.twMorph
  fiberMorph :=
    f.fiberMorph ≫
    (G.map f.twMorph).toFunctor.map g.fiberMorph ≫
    eqToHom (comp_fiber_cod_eq f g)

/-- Extensionality for presheaf connected Grothendieck morphisms -/
@[ext (iff := false)]
theorem ext {X Y : ConnGrothendieckPresheafObj C G}
    (f g : ConnGrothendieckPresheafHom C G X Y)
    (h_tw : f.twMorph = g.twMorph)
    (h_fiber : f.fiberMorph ≫ eqToHom (by rw [h_tw]) = g.fiberMorph) :
    f = g := by
  cases f; cases g
  congr
  dsimp at h_tw
  cat_disch

end ConnGrothendieckPresheafHom

attribute [local simp] eqToHom_map CategoryTheory.Functor.map_id

set_option backward.isDefEq.respectTransparency false in
instance connGrothendieckPresheafCategory :
    Category (ConnGrothendieckPresheafObj C G) where
  Hom := ConnGrothendieckPresheafHom C G
  id := ConnGrothendieckPresheafHom.id
  comp := ConnGrothendieckPresheafHom.comp
  id_comp {X Y} f := by
    apply ConnGrothendieckPresheafHom.ext
    case h_tw =>
      simp only [ConnGrothendieckPresheafHom.comp, ConnGrothendieckPresheafHom.id]
      exact @Category.id_comp (TwistedArrow' C) _ _ _ f.twMorph
    case h_fiber =>
      simp only [ConnGrothendieckPresheafHom.comp, ConnGrothendieckPresheafHom.id]
      simp only [Category.assoc]
      have h : (G.map (𝟙 X.tw)).toFunctor = 𝟭 (G.obj X.tw) :=
        (congrArg Cat.Hom.toFunctor (G.map_id X.tw)).trans Cat.Hom.id_toFunctor
      slice_lhs 2 3 => erw [Functor.congr_hom h f.fiberMorph]
      cat_disch
  comp_id {X Y} f := by
    apply ConnGrothendieckPresheafHom.ext
    case h_tw =>
      simp only [ConnGrothendieckPresheafHom.comp, ConnGrothendieckPresheafHom.id]
      exact @Category.comp_id (TwistedArrow' C) _ _ _ f.twMorph
    case h_fiber =>
      simp only [ConnGrothendieckPresheafHom.comp, ConnGrothendieckPresheafHom.id]
      simp only [eqToHom_map, Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
  assoc f g h := by
    apply ConnGrothendieckPresheafHom.ext
    case h_tw =>
      simp only [ConnGrothendieckPresheafHom.comp]
      exact @Category.assoc (TwistedArrow' C) _ _ _ _ _ f.twMorph g.twMorph h.twMorph
    case h_fiber =>
      simp only [ConnGrothendieckPresheafHom.comp, Category.assoc]
      have hcomp : (G.map (g.twMorph ≫ f.twMorph)).toFunctor =
          (G.map g.twMorph).toFunctor ⋙ (G.map f.twMorph).toFunctor :=
        (congrArg Cat.Hom.toFunctor (G.map_comp g.twMorph f.twMorph)).trans
          (Cat.Hom.comp_toFunctor (G.map g.twMorph) (G.map f.twMorph))
      slice_lhs 3 4 =>
        erw [Functor.congr_hom hcomp h.fiberMorph]
      cat_disch

/--
The presheaf connected Grothendieck construction for `G : Tw(C)^op' ⥤ Cat`.
-/
abbrev ConnectedGrothendieckPresheaf : Type _ := ConnGrothendieckPresheafObj C G

instance : Category (ConnectedGrothendieckPresheaf C G) :=
  connGrothendieckPresheafCategory C G

end PresheafConnectedGrothendieck

/-!
## Projection Functor for Presheaf Connected Grothendieck

The presheaf connected Grothendieck construction `ConnectedGrothendieckPresheaf C G`
projects naturally to `TwistedArrow' C`, not to `Arrow C`. This is because the
morphisms use `TwistedArrow'` morphisms (with one backward, one forward component)
rather than `Arrow` morphisms (both forward).

To obtain a functor to `Arrow C`, we compose with the fact that
`TwistedArrow' C` admits a "forgetful" functor to various arrow categories.
-/

section PresheafConnectedGrothendieckProjection

variable {C : Type u} [Category.{v} C]
variable (C)
variable (G : (TwistedArrow' C)ᵒᵖ' ⥤ Cat.{v, u})

/--
Convert a presheaf Grothendieck object to its underlying twisted arrow.
-/
def connGrothendieckPresheafObjToTw
    (X : ConnGrothendieckPresheafObj C G) : TwistedArrow' C :=
  X.tw

/--
Extract the twisted arrow morphism from a presheaf Grothendieck morphism.
-/
def connGrothendieckPresheafHomToTwHom
    {X Y : ConnGrothendieckPresheafObj C G}
    (f : ConnGrothendieckPresheafHom C G X Y) : X.tw ⟶ Y.tw :=
  f.twMorph

/--
The projection functor from `ConnectedGrothendieckPresheaf C G` to `TwistedArrow' C`.
-/
def connGrothendieckPresheafProjection :
    ConnectedGrothendieckPresheaf C G ⥤ TwistedArrow' C where
  obj := connGrothendieckPresheafObjToTw C G
  map f := connGrothendieckPresheafHomToTwHom C G f
  map_id _ := rfl
  map_comp _ _ := rfl

/--
The projection preserves the underlying twisted arrow on objects.
-/
@[simp]
lemma connGrothendieckPresheafProjection_obj
    (X : ConnectedGrothendieckPresheaf C G) :
    (connGrothendieckPresheafProjection C G).obj X = X.tw :=
  rfl

/--
The projection preserves the twisted arrow morphism component.
-/
@[simp]
lemma connGrothendieckPresheafProjection_map
    {X Y : ConnectedGrothendieckPresheaf C G}
    (f : X ⟶ Y) :
    (connGrothendieckPresheafProjection C G).map f = f.twMorph :=
  rfl

end PresheafConnectedGrothendieckProjection

/-!
## Remarks on Presheaf Construction and Arrow Projection

The presheaf connected Grothendieck construction `ConnectedGrothendieckPresheaf C G`
naturally projects to `TwistedArrow' C` via `connGrothendieckPresheafProjection`.

### Why Arrow Projection Works for Copresheaves but Not Presheaves

The copresheaf construction projects to `Arrow C` using a diagonal construction:
given an Arrow morphism with components `(domArr, codArr)`, we form a diagonal
twisted arrow `w` and TwistedArrow' morphisms from both source and target arrows
to this diagonal. These morphisms go from component arrows to a composite arrow.

For **covariant** `F : TwistedArrow' C ⥤ Cat`:
- `F.map (X.tw → w) : F(X.tw) ⥤ F(w)` transports fibers INTO `F(w)`
- `F.map (Y.tw → w) : F(Y.tw) ⥤ F(w)` transports fibers INTO `F(w)`
- Both fiber elements end up in the common category `F(w)` where they can be
  compared via a fiber morphism

For **contravariant** `G : (TwistedArrow' C)ᵒᵖ' ⥤ Cat`:
- `G.map (X.tw → w) : G(w) ⥤ G(X.tw)` transports FROM `G(w)` out to `G(X.tw)`
- `G.map (Y.tw → w) : G(w) ⥤ G(Y.tw)` transports FROM `G(w)` out to `G(Y.tw)`
- We cannot use these to transport fibers INTO a common category

The asymmetry arises because TwistedArrow' morphisms naturally go from component
arrows to composite arrows (the diagonal). The covariant functor maps follow this
direction, enabling fiber comparison in the diagonal fiber. The contravariant
functor maps reverse this direction, preventing the diagonal construction from
working for fiber transport.

### Presheaf Construction Uses TwistedArrow' Morphisms Directly

The presheaf construction instead uses TwistedArrow' morphisms directly as the
base morphisms. For `twMorph : X.tw ⟶ Y.tw`:
- `G.map twMorph : G(Y.tw) ⥤ G(X.tw)` transports `Y.fiber` into `G(X.tw)`
- The fiber morphism `X.fiber ⟶ (G.map twMorph).obj Y.fiber` lives in `G(X.tw)`

This is the natural structure for presheaves on twisted arrows, and it projects
to `TwistedArrow' C` rather than `Arrow C`.
-/

/-!
## Alternative Connected Grothendieck Construction

The connected Grothendieck construction can be defined in two equivalent ways:

1. **Codomain-based (existing)**: Covariant outer Grothendieck over contravariant
   inner Grothendieck on `(Over b)^op`. This is `ConnectedGrothendieckContra`.

2. **Domain-based (alternative)**: Contravariant outer Grothendieck over covariant
   inner Grothendieck on `Under a`. This is `ConnectedGrothendieckAlt`.

Both constructions yield equivalent categories, validating the symmetry of the
connected Grothendieck construction.
-/

section AlternativeConstruction

variable (C : Type u) [Category.{v} C]
variable (F : TwistedArrow' C ⥤ Cat.{v, u})

/-!
### Fiber inclusion by domain

For each object `a : C`, we define a functor `Under a ⥤ TwistedArrow' C` that
includes arrows out of `a` as twisted arrows.
-/

/--
The functor from `Under a` to `TwistedArrow' C` that includes arrows out of `a`.

On objects: `(f : a ⟶ b)` maps to `f` viewed as a twisted arrow.
On morphisms: `α : f → g` in `Under a` (i.e., `α : b → c` with `g = f ≫ α`)
  maps to `(𝟙 a, α) : f → g` in `TwistedArrow' C`.
-/
def underToTwistedArrow (a : C) : Under a ⥤ TwistedArrow' C where
  obj un := twObjMk' un.hom
  map {un un'} α :=
    twHomMk'
      (x := twObjMk' un.hom)
      (y := twObjMk' un'.hom)
      (by simp only [twObjMk'_dom]; exact 𝟙 a)
      (by simp only [twObjMk'_cod]; exact α.right)
      (by
        simp only [twObjMk'_arr]
        change id (𝟙 a) ≫ un.hom ≫ id α.right = un'.hom
        simp only [id, Category.id_comp]
        exact Under.w α)
  map_id un := by
    apply twHom'_ext <;> rfl
  map_comp {un un' un''} α β := by
    apply twHom'_ext
    · simp only [twHomMk'_domArr, twDomArr'_comp]
      exact (Category.id_comp (𝟙 a)).symm
    · rfl

/--
The restriction of `F : TwistedArrow' C ⥤ Cat` to the fiber over domain `a`.
-/
def restrictToDomainFiber (a : C) : Under a ⥤ Cat.{v, u} :=
  underToTwistedArrow C a ⋙ F

/-!
### Domain fiber transport

For `α : c ⟶ a` in `C`, we get a functor `Under a ⥤ Under c` by precomposition.
This induces transport between the corresponding Grothendieck categories.
-/

set_option backward.isDefEq.respectTransparency false in
/--
The twisted arrow morphism for domain fiber transport.
Given `α : c ⟶ a` and `un : Under a` (an arrow `f : a ⟶ b`),
this is the morphism `f → (α ≫ f)` in `TwistedArrow' C`.

The domain arrow is `α : c ⟶ a` going from the target domain to the source domain
(backwards, as required by `twHomMk'`), and the codomain arrow is `𝟙 b`.
-/
def domainFiberTransportTwMorph {a c : C} (α : c ⟶ a) (un : Under a) :
    (underToTwistedArrow C a).obj un ⟶
    (underToTwistedArrow C c).obj ((Under.map α).obj un) :=
  twHomMk'
    (x := twObjMk' un.hom)
    (y := twObjMk' (α ≫ un.hom))
    α
    (𝟙 _)
    (by simp only [twObjMk'_arr, Category.comp_id])

/--
The transport functor for domain fibers. Given `α : c ⟶ a`, this transports
elements from the fiber over `a` to the fiber over `c`.
-/
def domainFiberTransport {a c : C} (α : c ⟶ a) (un : Under a) :
    F.obj ((underToTwistedArrow C a).obj un) ⥤
    F.obj ((underToTwistedArrow C c).obj ((Under.map α).obj un)) :=
  (F.map (domainFiberTransportTwMorph C α un)).toFunctor

set_option backward.isDefEq.respectTransparency false in
/--
Naturality of domain fiber transport at the twisted arrow level.
-/
theorem domainFiberTransport_naturality {a c : C} (α : c ⟶ a)
    {un un' : Under a} (β : un ⟶ un') :
    (underToTwistedArrow C a).map β ≫ domainFiberTransportTwMorph C α un' =
    domainFiberTransportTwMorph C α un ≫ (underToTwistedArrow C c).map ((Under.map α).map β) := by
  apply twHom'_ext
  · simp only [twDomArr'_comp, twHomMk'_domArr, underToTwistedArrow,
               domainFiberTransportTwMorph, twHomMk'_domArr, id, Under.map_map_right]
    trans α
    · exact Category.comp_id α
    · exact (Category.id_comp α).symm
  · simp only [twCodArr'_comp, twHomMk'_codArr, underToTwistedArrow,
               domainFiberTransportTwMorph, twHomMk'_codArr, id, Under.map_map_right]
    trans β.right
    · exact Category.comp_id β.right
    · exact (Category.id_comp β.right).symm

/--
Functor-level naturality: domain fiber transport composed with restriction mapping
equals restriction mapping followed by domain fiber transport.
-/
theorem domainFiberTransport_functor_naturality {a c : C} (α : c ⟶ a)
    {un un' : Under a} (β : un ⟶ un') :
    ((restrictToDomainFiber C F a).map β).toFunctor ⋙ domainFiberTransport C F α un' =
    domainFiberTransport C F α un ⋙
      ((restrictToDomainFiber C F c).map ((Under.map α).map β)).toFunctor := by
  simp only [restrictToDomainFiber, domainFiberTransport, Functor.comp_map]
  unfold Cat.Hom.toFunctor
  have h := domainFiberTransport_naturality C α β
  calc (F.map ((underToTwistedArrow C a).map β)).toFunctor ⋙
        (F.map (domainFiberTransportTwMorph C α un')).toFunctor
      = ((F.map ((underToTwistedArrow C a).map β)) ≫
          (F.map (domainFiberTransportTwMorph C α un'))).toFunctor := by
          rw [Cat.Hom.comp_toFunctor]
    _ = (F.map ((underToTwistedArrow C a).map β ≫ domainFiberTransportTwMorph C α un')).toFunctor :=
          by rw [F.map_comp]
    _ = (F.map (domainFiberTransportTwMorph C α un ≫
          (underToTwistedArrow C c).map ((Under.map α).map β))).toFunctor := by
          rw [h]
    _ = ((F.map (domainFiberTransportTwMorph C α un)) ≫
          (F.map ((underToTwistedArrow C c).map ((Under.map α).map β)))).toFunctor := by
          rw [← F.map_comp]
    _ = (F.map (domainFiberTransportTwMorph C α un)).toFunctor ⋙
          (F.map ((underToTwistedArrow C c).map ((Under.map α).map β))).toFunctor := by
          rw [Cat.Hom.comp_toFunctor]

set_option backward.isDefEq.respectTransparency false in
/--
`domainFiberTransportTwMorph C α un` equals `connGrothendieckTwMorphDom C (twObjMk' un.hom) α`.

Both morphisms have:
- Source: `twObjMk' un.hom`
- Target: `twObjMk' (α ≫ un.hom)`
- left = α, right = 𝟙
-/
theorem domainFiberTransportTwMorph_eq_connGrothendieckTwMorphDom
    {a c : C} (α : c ⟶ a) (un : Under a) :
    domainFiberTransportTwMorph C α un =
    connGrothendieckTwMorphDom C (twObjMk' un.hom) α := by
  simp only [domainFiberTransportTwMorph, connGrothendieckTwMorphDom, connGrothendieckDiagDom]

set_option backward.isDefEq.respectTransparency false in
/--
The target of `(Under.map α).obj un` as a twisted arrow.
For `α : c ⟶ a` and `un : Under a`, `(Under.map α).obj un` has hom = `α ≫ un.hom`.
-/
theorem underToTwistedArrow_map_obj_eq {a c : C} (α : c ⟶ a) (un : Under a) :
    (underToTwistedArrow C c).obj ((Under.map α).obj un) =
    twObjMk' (α ≫ un.hom) := by
  simp only [underToTwistedArrow, Under.map_obj_hom]

set_option backward.isDefEq.respectTransparency false in
/--
`underToTwistedArrow.map` relates to `connGrothendieckTwMorphCod` via the square equality.

For `β : un ⟶ (Under.map α).obj un'` in `Under a` (where `α : a ⟶ b` and `un' : Under b`),
`Under.w β` gives: `un.hom = β.right ≫ (α ≫ un'.hom)`

Both morphisms have left = 𝟙, right = β.right.
The target equality `un.hom ≫ β.right = α ≫ un'.hom` follows from Under.w and associativity.
-/
theorem underToTwistedArrow_map_eq_connGrothendieckTwMorphCod
    {a b : C} (α : a ⟶ b) {un : Under a} {un' : Under b}
    (β : un ⟶ (Under.map α).obj un') :
    (underToTwistedArrow C a).map β =
    connGrothendieckTwMorphCod C (twObjMk' un.hom) β.right ≫
      eqToHom (by
        simp only [connGrothendieckDiagCod, underToTwistedArrow, Under.map_obj_hom]
        congr 1
        have hw := Under.w β
        simp only [Under.map_obj_hom] at hw
        exact hw) := by
  apply twHom'_ext
  · simp only [underToTwistedArrow, twHomMk'_domArr, twDomArr'_comp, twDomArr'_eqToHom,
               connGrothendieckTwMorphCod, connGrothendieckDiagCod, Under.map_obj_hom,
               twObjMk'_dom, id, Category.comp_id]
    rfl
  · simp only [underToTwistedArrow, twHomMk'_codArr, twCodArr'_comp, twCodArr'_eqToHom,
               connGrothendieckTwMorphCod, connGrothendieckDiagCod, Under.map_obj_hom,
               twObjMk'_cod, id, eqToHom_refl, Category.comp_id]

/-!
### Inner fiber category (covariant Grothendieck)

The inner layer uses the standard covariant Grothendieck construction on `Under a`.
-/

/--
The inner fiber category for the alternative construction.
For each `a : C`, this is `Grothendieck (restrictToDomainFiber C F a)`.
-/
def innerFiberAlt (a : C) : Type _ := Grothendieck (restrictToDomainFiber C F a)

instance innerFiberAltCategory (a : C) : Category (innerFiberAlt C F a) :=
  inferInstanceAs (Category (Grothendieck (restrictToDomainFiber C F a)))

/--
Transport an object from `innerFiberAlt C F a` to `innerFiberAlt C F c` via `α : c ⟶ a`.
-/
def innerFiberAltTransitionObj {a c : C} (α : c ⟶ a)
    (x : innerFiberAlt C F a) : innerFiberAlt C F c :=
  ⟨(Under.map α).obj x.base,
   (domainFiberTransport C F α x.base).obj x.fiber⟩

/--
The fiber coherence equation for `innerFiberAltTransitionHom`.
-/
theorem innerFiberAltTransition_fiber_eq {a c : C} (α : c ⟶ a)
    {x y : innerFiberAlt C F a} (f : x ⟶ y) :
    ((restrictToDomainFiber C F c).map ((Under.map α).map f.base)).toFunctor.obj
      ((domainFiberTransport C F α x.base).obj x.fiber) =
    (domainFiberTransport C F α y.base).obj
      (((restrictToDomainFiber C F a).map f.base).toFunctor.obj x.fiber) :=
  congrFun (congrArg Functor.obj
    (domainFiberTransport_functor_naturality C F α
      (un := x.base) (un' := y.base) f.base).symm) x.fiber

/--
Transport a morphism from `innerFiberAlt C F a` to `innerFiberAlt C F c` via `α : c ⟶ a`.
-/
def innerFiberAltTransitionHom {a c : C} (α : c ⟶ a)
    {x y : innerFiberAlt C F a} (f : x ⟶ y) :
    innerFiberAltTransitionObj C F α x ⟶ innerFiberAltTransitionObj C F α y :=
  ⟨(Under.map α).map f.base,
   eqToHom (innerFiberAltTransition_fiber_eq C F α f) ≫
     (domainFiberTransport C F α y.base).map f.fiber⟩

@[simp]
theorem innerFiberAltTransitionHom_base {a c : C} (α : c ⟶ a)
    {x y : innerFiberAlt C F a} (f : x ⟶ y) :
    (innerFiberAltTransitionHom C F α f).base = (Under.map α).map f.base := rfl

@[simp]
theorem innerFiberAltTransitionHom_fiber {a c : C} (α : c ⟶ a)
    {x y : innerFiberAlt C F a} (f : x ⟶ y) :
    (innerFiberAltTransitionHom C F α f).fiber =
    eqToHom (innerFiberAltTransition_fiber_eq C F α f) ≫
      (domainFiberTransport C F α y.base).map f.fiber := rfl

set_option backward.isDefEq.respectTransparency false in
/--
The transition functor for inner fibers via `α : c ⟶ a`.
-/
def innerFiberAltTransition {a c : C} (α : c ⟶ a) :
    innerFiberAlt C F a ⥤ innerFiberAlt C F c where
  obj := innerFiberAltTransitionObj C F α
  map := innerFiberAltTransitionHom C F α
  map_id x := by
    refine Grothendieck.ext _ _ ?w_base ?w_fiber
    case w_base =>
      simp only [innerFiberAltTransitionHom]
      exact (Under.map α).map_id x.base
    case w_fiber =>
      rw [innerFiberAltTransitionHom_fiber, Grothendieck.id_fiber, Grothendieck.id_fiber]
      simp only [eqToHom_map, eqToHom_trans]
  map_comp {x y z} f g := by
    refine Grothendieck.ext _ _ ?w_base ?w_fiber
    case w_base =>
      simp only [innerFiberAltTransitionHom_base]
      exact (Under.map α).map_comp f.base g.base
    case w_fiber =>
      rw [innerFiberAltTransitionHom_fiber, Grothendieck.comp_fiber, Grothendieck.comp_fiber]
      simp only [innerFiberAltTransitionHom_fiber, innerFiberAltTransitionHom_base,
                 innerFiberAltTransitionObj, Functor.map_comp, eqToHom_map, eqToHom_trans_assoc,
                 Category.assoc]
      have nat_eq := domainFiberTransport_functor_naturality C F α
        (un := y.base) (un' := z.base) g.base
      have mor_eq := Functor.congr_hom nat_eq f.fiber
      simp only [Functor.comp_map] at mor_eq
      rw [mor_eq]
      simp only [Category.assoc, eqToHom_trans_assoc]

@[simp]
theorem innerFiberAltTransition_map {a c : C} (α : c ⟶ a)
    {x y : innerFiberAlt C F a} (f : x ⟶ y) :
    (innerFiberAltTransition C F α).map f = innerFiberAltTransitionHom C F α f := rfl

/-!
### Identity and Composition Laws for `innerFiberAltTransition`
-/

set_option backward.isDefEq.respectTransparency false in
/--
The twisted arrow object for `(Under.map (𝟙 a)).obj un` equals that for `un`.
-/
lemma underToTwArr_map_id_obj_eq {a : C} (un : Under a) :
    (underToTwistedArrow C a).obj ((Under.map (𝟙 a)).obj un) =
    (underToTwistedArrow C a).obj un := by
  simp only [underToTwistedArrow, Under.map_obj_right, Under.map_obj_hom, Category.id_comp]

/--
The codomain of `domainFiberTransport C F (𝟙 a) un` equals the domain.
-/
lemma domainFiberTransport_id_cat_eq {a : C} (un : Under a) :
    (restrictToDomainFiber C F a).obj ((Under.map (𝟙 a)).obj un) =
    (restrictToDomainFiber C F a).obj un := by
  simp only [restrictToDomainFiber, Functor.comp_obj]
  exact congrArg F.obj (underToTwArr_map_id_obj_eq C un)

/--
The twisted arrow morphism for domain fiber transport with identity is `eqToHom`.
-/
lemma underToTwArr_map_id_dom_eq {a : C} (un : Under a) :
    twDom' ((underToTwistedArrow C a).obj ((Under.map (𝟙 a)).obj un)) =
    twDom' ((underToTwistedArrow C a).obj un) := rfl

lemma underToTwArr_map_id_cod_eq {a : C} (un : Under a) :
    twCod' ((underToTwistedArrow C a).obj ((Under.map (𝟙 a)).obj un)) =
    twCod' ((underToTwistedArrow C a).obj un) := rfl

set_option backward.isDefEq.respectTransparency false in
lemma domainFiberTransportTwMorph_id {a : C} (un : Under a) :
    domainFiberTransportTwMorph C (𝟙 a) un =
    eqToHom (underToTwArr_map_id_obj_eq C un).symm := by
  apply twHom'_ext
  · simp only [domainFiberTransportTwMorph, twHomMk'_domArr, twDomArr'_eqToHom]
    rfl
  · simp only [domainFiberTransportTwMorph, twHomMk'_codArr, twCodArr'_eqToHom]
    rfl

set_option backward.isDefEq.respectTransparency false in
/--
When `α = 𝟙 a`, the domain fiber transport functor is `eqToHom` in Cat.
-/
lemma domainFiberTransport_id {a : C} (un : Under a) :
    domainFiberTransport C F (𝟙 a) un =
    (eqToHom (domainFiberTransport_id_cat_eq C F un).symm).toFunctor := by
  simp only [domainFiberTransport, domainFiberTransportTwMorph_id, eqToHom_map]

/--
The object equality for `innerFiberAltTransitionObj` with identity.
-/
lemma innerFiberAltTransitionObj_id_base {a : C} (x : innerFiberAlt C F a) :
    ((Under.map (𝟙 a)).obj x.base) = x.base := by
  have h := Under.mapId_eq a
  exact congrFun (congrArg Functor.obj h) x.base

/--
The fiber equality for `innerFiberAltTransitionObj` with identity.
-/
lemma innerFiberAltTransitionObj_id_fiber {a : C} (x : innerFiberAlt C F a) :
    (innerFiberAltTransitionObj C F (𝟙 a) x).fiber ≍ x.fiber := by
  simp only [innerFiberAltTransitionObj]
  rw [domainFiberTransport_id]
  exact eqToHom_obj_heq _ _ _ x.fiber

/--
The full object equality for `innerFiberAltTransitionObj` with identity.
-/
lemma innerFiberAltTransitionObj_id {a : C} (x : innerFiberAlt C F a) :
    innerFiberAltTransitionObj C F (𝟙 a) x = x := by
  have h_base := innerFiberAltTransitionObj_id_base C F x
  have h_fiber := innerFiberAltTransitionObj_id_fiber C F x
  exact Grothendieck.obj_ext _ _ _ h_base h_fiber

/--
The LHS of the fiber identity law for `innerFiberAltTransition`.
Shows that `(domainFiberTransport C F (𝟙 a) y.base).map f.fiber` is HEq to `f.fiber`.
-/
lemma innerFiberAltTransition_id_fiber_lhs {a : C}
    {x y : innerFiberAlt C F a} (f : x ⟶ y) :
    (domainFiberTransport C F (𝟙 a) y.base).map f.fiber ≍ f.fiber :=
  Cat.functor_map_heq_of_eq_eqToHom _ _ (domainFiberTransport_id C F y.base) f.fiber

set_option backward.isDefEq.respectTransparency false in
/--
Identity law for `innerFiberAltTransition`.
-/
theorem innerFiberAltTransition_id (a : C) :
    innerFiberAltTransition C F (𝟙 a) = 𝟭 (innerFiberAlt C F a) := by
  apply _root_.CategoryTheory.Functor.ext
  case h_obj => exact innerFiberAltTransitionObj_id C F
  case h_map =>
    intro x y f
    simp only [Functor.id_map]
    apply Grothendieck.ext
    case w_base =>
      dsimp only [innerFiberAltTransition]
      rw [innerFiberAltTransitionHom_base]
      rw [Grothendieck.comp_base, Grothendieck.comp_base]
      rw [Grothendieck.eqToHom_base', Grothendieck.eqToHom_base']
      rw [Functor.congr_hom (Under.mapId_eq a) f.base, Functor.id_map]
    case w_fiber =>
      apply eq_of_heq
      simp only [innerFiberAltTransition, innerFiberAltTransitionHom_fiber,
                 eqToHom_trans_assoc, eqToHom_comp_heq_iff]
      apply HEq.trans (innerFiberAltTransition_id_fiber_lhs C F f)
      apply HEq.symm
      exact Grothendieck.conj_eqToHom_fiber_heq
        (F := restrictToDomainFiber C F a) _ _ _

set_option backward.isDefEq.respectTransparency false in
/--
The twisted arrow object for composition of `Under.map`.
-/
lemma underToTwArr_mapComp_obj_eq {a c e : C} (α : c ⟶ a) (γ : e ⟶ c) (un : Under a) :
    (underToTwistedArrow C e).obj ((Under.map (γ ≫ α)).obj un) =
    (underToTwistedArrow C e).obj ((Under.map γ).obj ((Under.map α).obj un)) := by
  simp only [underToTwistedArrow, Under.map_obj_right, Under.map_obj_hom, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
/--
The twisted arrow morphism for domain fiber transport composes.
-/
lemma domainFiberTransportTwMorph_comp {a c e : C} (α : c ⟶ a) (γ : e ⟶ c) (un : Under a) :
    domainFiberTransportTwMorph C (γ ≫ α) un =
      domainFiberTransportTwMorph C α un ≫
      domainFiberTransportTwMorph C γ ((Under.map α).obj un) ≫
      eqToHom (underToTwArr_mapComp_obj_eq C α γ un).symm := by
  apply twHom'_ext
  · simp only [domainFiberTransportTwMorph, twHomMk'_domArr, twDomArr'_comp,
               twDomArr'_eqToHom, Category.assoc, eqToHom_refl]
    simp only [underToTwistedArrow, twObjMk'_dom, Under.map_obj_hom, Category.id_comp]
  · simp only [domainFiberTransportTwMorph, twHomMk'_codArr, twCodArr'_comp,
               twCodArr'_eqToHom, Under.map_obj_right, eqToHom_refl,
               underToTwistedArrow, twObjMk'_cod, Category.id_comp]

/--
The category equality for composing domain fiber transports.
-/
lemma domainFiberTransport_comp_cat_eq {a c e : C} (α : c ⟶ a) (γ : e ⟶ c) (un : Under a) :
    (restrictToDomainFiber C F e).obj ((Under.map (γ ≫ α)).obj un) =
    (restrictToDomainFiber C F e).obj ((Under.map γ).obj ((Under.map α).obj un)) := by
  simp only [restrictToDomainFiber, Functor.comp_obj]
  exact congrArg F.obj (underToTwArr_mapComp_obj_eq C α γ un)

/--
The domain fiber transport for a composition decomposes.
-/
lemma domainFiberTransport_comp {a c e : C} (α : c ⟶ a) (γ : e ⟶ c) (un : Under a) :
    domainFiberTransport C F (γ ≫ α) un =
      domainFiberTransport C F α un ⋙
      domainFiberTransport C F γ ((Under.map α).obj un) ⋙
      (eqToHom (domainFiberTransport_comp_cat_eq C F α γ un).symm).toFunctor := by
  simp only [domainFiberTransport, domainFiberTransportTwMorph_comp, F.map_comp, eqToHom_map]
  rfl

/--
The base equality for `innerFiberAltTransitionObj` with composition.
-/
lemma innerFiberAltTransitionObj_comp_base {a c e : C} (α : c ⟶ a) (γ : e ⟶ c)
    (x : innerFiberAlt C F a) :
    (innerFiberAltTransitionObj C F (γ ≫ α) x).base =
    ((Under.map γ).obj ((Under.map α).obj x.base)) := by
  simp only [innerFiberAltTransitionObj]
  have h := Under.mapComp_eq γ α
  exact congrFun (congrArg Functor.obj h) x.base

/--
The fiber equality for `innerFiberAltTransitionObj` with composition.
-/
lemma innerFiberAltTransitionObj_comp_fiber {a c e : C} (α : c ⟶ a) (γ : e ⟶ c)
    (x : innerFiberAlt C F a) :
    (innerFiberAltTransitionObj C F (γ ≫ α) x).fiber ≍
    (innerFiberAltTransitionObj C F γ (innerFiberAltTransitionObj C F α x)).fiber := by
  simp only [innerFiberAltTransitionObj]
  rw [domainFiberTransport_comp]
  exact eqToHom_obj_heq _ _ _ _

/--
The full object equality for `innerFiberAltTransitionObj` with composition.
-/
lemma innerFiberAltTransitionObj_comp {a c e : C} (α : c ⟶ a) (γ : e ⟶ c)
    (x : innerFiberAlt C F a) :
    innerFiberAltTransitionObj C F (γ ≫ α) x =
    innerFiberAltTransitionObj C F γ (innerFiberAltTransitionObj C F α x) := by
  simp only [innerFiberAltTransitionObj]
  congr 1
  · exact congrArg (·.obj x.base) (Under.mapComp_eq γ α)
  · simp only [domainFiberTransport_comp]
    exact eqToHom_obj_heq _ _ _ _

set_option backward.isDefEq.respectTransparency false in
/--
The RHS base component in the composition law.
-/
lemma innerFiberAltTransition_comp_base_rhs_base {a c e : C} (α : c ⟶ a) (γ : e ⟶ c)
    {x y : innerFiberAlt C F a} (f : x ⟶ y) :
    (innerFiberAltTransitionHom C F γ (innerFiberAltTransitionHom C F α f)).base =
    (Under.map γ).map ((Under.map α).map f.base) := by
  simp only [innerFiberAltTransitionHom_base]

set_option backward.isDefEq.respectTransparency false in
/--
The RHS of the base composition law.
Shows that the RHS is HEq to `(Under.map γ).map ((Under.map α).map f.base)`.
-/
lemma innerFiberAltTransition_comp_base_rhs {a c e : C} (α : c ⟶ a) (γ : e ⟶ c)
    {x y : innerFiberAlt C F a} (f : x ⟶ y)
    (h : (innerFiberAltTransitionObj C F (γ ≫ α) x) =
         (innerFiberAltTransitionObj C F γ (innerFiberAltTransitionObj C F α x)))
    (h' : (innerFiberAltTransitionObj C F (γ ≫ α) y) =
          (innerFiberAltTransitionObj C F γ (innerFiberAltTransitionObj C F α y))) :
    (eqToHom h ≫
      innerFiberAltTransitionHom C F γ (innerFiberAltTransitionHom C F α f) ≫
      eqToHom h'.symm).base ≍
    (Under.map γ).map ((Under.map α).map f.base) := by
  rw [Grothendieck.comp_base, Grothendieck.comp_base]
  rw [Grothendieck.eqToHom_base', Grothendieck.eqToHom_base']
  rw [innerFiberAltTransition_comp_base_rhs_base]
  apply HEq.trans (eqToHom_comp_heq _ _)
  exact comp_eqToHom_heq _ _

/--
The LHS of the fiber composition law.
Using `domainFiberTransport_comp`, the LHS simplifies to a composition of transports.
-/
lemma innerFiberAltTransition_comp_fiber_lhs {a c e : C} (α : c ⟶ a) (γ : e ⟶ c)
    {x y : innerFiberAlt C F a} (f : x ⟶ y) :
    (domainFiberTransport C F (γ ≫ α) y.base).map f.fiber ≍
    (domainFiberTransport C F γ ((Under.map α).obj y.base)).map
      ((domainFiberTransport C F α y.base).map f.fiber) := by
  exact Cat.functor_map_heq_of_eq_comp_comp_eqToHom
    (domainFiberTransport C F (γ ≫ α) y.base)
    (domainFiberTransport C F α y.base)
    (domainFiberTransport C F γ ((Under.map α).obj y.base))
    _ (domainFiberTransport_comp C F α γ y.base) f.fiber

/--
The RHS of the fiber composition law.
Shows the RHS is HEq to the composition of transports.
-/
lemma innerFiberAltTransition_comp_fiber_rhs {a c e : C} (α : c ⟶ a) (γ : e ⟶ c)
    {x y : innerFiberAlt C F a} (f : x ⟶ y)
    (h : (innerFiberAltTransitionObj C F (γ ≫ α) x) =
         (innerFiberAltTransitionObj C F γ (innerFiberAltTransitionObj C F α x)))
    (h' : (innerFiberAltTransitionObj C F (γ ≫ α) y) =
          (innerFiberAltTransitionObj C F γ (innerFiberAltTransitionObj C F α y))) :
    (eqToHom h ≫
      innerFiberAltTransitionHom C F γ (innerFiberAltTransitionHom C F α f) ≫
      eqToHom h'.symm).fiber ≍
    (domainFiberTransport C F γ ((Under.map α).obj y.base)).map
      ((domainFiberTransport C F α y.base).map f.fiber) := by
  apply HEq.trans (Grothendieck.conj_eqToHom_fiber_heq
    (F := restrictToDomainFiber C F e) h _ h'.symm)
  simp only [innerFiberAltTransitionHom_fiber]
  apply HEq.trans (eqToHom_comp_heq _ _)
  apply HEq.trans (Functor.map_eqToHom_comp_heq _ _ _)
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
Composition law for `innerFiberAltTransition`.
-/
theorem innerFiberAltTransition_comp {a c e : C} (α : c ⟶ a) (γ : e ⟶ c) :
    innerFiberAltTransition C F (γ ≫ α) =
    innerFiberAltTransition C F α ⋙ innerFiberAltTransition C F γ := by
  apply _root_.CategoryTheory.Functor.ext
  case h_obj => exact innerFiberAltTransitionObj_comp C F α γ
  case h_map =>
    intro x y f
    apply Grothendieck.ext
    case w_base =>
      dsimp only [innerFiberAltTransition, Functor.comp_map]
      simp only [innerFiberAltTransitionHom_base]
      rw [Functor.congr_hom (Under.mapComp_eq γ α) f.base]
      simp only [Functor.comp_map]
      apply eq_of_heq
      apply HEq.trans (eqToHom_comp_heq _ _)
      apply HEq.trans (comp_eqToHom_heq _ _)
      exact (innerFiberAltTransition_comp_base_rhs C F α γ f
        (innerFiberAltTransitionObj_comp C F α γ x)
        (innerFiberAltTransitionObj_comp C F α γ y)).symm
    case w_fiber =>
      dsimp only [innerFiberAltTransition, Functor.comp_map]
      apply eq_of_heq
      simp only [innerFiberAltTransitionHom_fiber,
                 eqToHom_trans_assoc, eqToHom_comp_heq_iff]
      apply HEq.trans (innerFiberAltTransition_comp_fiber_lhs C F α γ f)
      exact (innerFiberAltTransition_comp_fiber_rhs C F α γ f
        (innerFiberAltTransitionObj_comp C F α γ x)
        (innerFiberAltTransitionObj_comp C F α γ y)).symm

/-!
### The Domain Fiber Functor

The domain fiber functor `domainFiberFunctor : Cᵒᵖ' ⥤ Cat` assigns to each object
`a : Cᵒᵖ'` (equivalently `a : C`) the category `innerFiberAlt C F a`, and to each
morphism `α : a ⟶ b` in `Cᵒᵖ'` (which is `α : b ⟶ a` in `C`) the transition functor
`innerFiberAltTransition C F α`.
-/

/--
The domain fiber functor from `Cᵒᵖ'` to `Cat`.

For an object `a : Cᵒᵖ'`, this assigns `innerFiberAlt C F a`.
For a morphism `α : a ⟶ b` in `Cᵒᵖ'` (which is `α : b ⟶ a` in `C`),
this assigns `innerFiberAltTransition C F α`.
-/
def domainFiberFunctor : Cᵒᵖ' ⥤ Cat where
  obj a := Cat.of (innerFiberAlt C F a)
  map α := (innerFiberAltTransition C F α).toCatHom
  map_id a := by
    apply Cat.Hom.ext
    exact innerFiberAltTransition_id C F a
  map_comp α β := by
    apply Cat.Hom.ext
    exact innerFiberAltTransition_comp C F α β

@[simp]
theorem domainFiberFunctor_map {a c : Cᵒᵖ'} (α : a ⟶ c) :
    (domainFiberFunctor C F).map α = (innerFiberAltTransition C F α).toCatHom := rfl

section AltFunctoriality

/-!
### Functoriality of the Alternative Construction

Natural transformations `α : F ⟶ G` induce functors between the alternative
connected Grothendieck categories.
-/

variable {F} {G H : TwistedArrow' C ⥤ Cat.{v, u}}

def restrictToDomainFiberNatTrans (α : F ⟶ G) (a : C) :
    restrictToDomainFiber C F a ⟶ restrictToDomainFiber C G a :=
  Functor.whiskerLeft (underToTwistedArrow C a) α

@[simp]
theorem restrictToDomainFiberNatTrans_id (a : C) :
    restrictToDomainFiberNatTrans C (𝟙 F) a = 𝟙 (restrictToDomainFiber C F a) := by
  simp only [restrictToDomainFiberNatTrans, Functor.whiskerLeft_id', restrictToDomainFiber]

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem restrictToDomainFiberNatTrans_comp (α : F ⟶ G) (β : G ⟶ H) (a : C) :
    restrictToDomainFiberNatTrans C (α ≫ β) a =
      restrictToDomainFiberNatTrans C α a ≫ restrictToDomainFiberNatTrans C β a := by
  simp only [restrictToDomainFiberNatTrans, Functor.whiskerLeft_comp]

def innerFiberAltMap (α : F ⟶ G) (a : C) :
    innerFiberAlt C F a ⥤ innerFiberAlt C G a :=
  Grothendieck.map (restrictToDomainFiberNatTrans C α a)

@[simp]
theorem innerFiberAltMap_id (a : C) :
    innerFiberAltMap C (𝟙 F) a = 𝟭 (innerFiberAlt C F a) := by
  simp only [innerFiberAltMap, restrictToDomainFiberNatTrans_id,
    Grothendieck.map_id_eq, innerFiberAlt]

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem innerFiberAltMap_comp (α : F ⟶ G) (β : G ⟶ H) (a : C) :
    innerFiberAltMap C (α ≫ β) a = innerFiberAltMap C α a ⋙ innerFiberAltMap C β a := by
  simp only [innerFiberAltMap, restrictToDomainFiberNatTrans_comp, Grothendieck.map_comp_eq]

@[simp]
theorem innerFiberAltMap_obj_base (α : F ⟶ G) {a : C} (x : innerFiberAlt C F a) :
    ((innerFiberAltMap C α a).obj x).base = x.base := by
  simp only [innerFiberAltMap, Grothendieck.map_obj]

/--
Naturality of a natural transformation `α : F ⟶ G` with respect to domain fiber transport.
-/
theorem alpha_domainFiberTransport_naturality (α : F ⟶ G) {a c : C} (γ : c ⟶ a)
    (un : Under a) :
    (α.app ((underToTwistedArrow C a).obj un)).toFunctor ⋙ domainFiberTransport C G γ un =
    domainFiberTransport C F γ un ⋙
      (α.app ((underToTwistedArrow C c).obj ((Under.map γ).obj un))).toFunctor := by
  simp only [domainFiberTransport]
  have nat := α.naturality (domainFiberTransportTwMorph C γ un)
  have nat' := congrArg Cat.Hom.toFunctor nat.symm
  rw [Cat.Hom.comp_toFunctor, Cat.Hom.comp_toFunctor] at nat'
  exact nat'

/--
Objects are naturally equal after composing `innerFiberAltMap` and
`innerFiberAltTransition`.
-/
theorem innerFiberAltMap_natural_obj (α : F ⟶ G) {a c : C} (γ : c ⟶ a)
    (x : innerFiberAlt C F a) :
    (innerFiberAltMap C α c).obj ((innerFiberAltTransition C F γ).obj x) =
    (innerFiberAltTransition C G γ).obj ((innerFiberAltMap C α a).obj x) := by
  simp only [innerFiberAltMap, innerFiberAltTransition, innerFiberAltTransitionObj]
  simp only [Grothendieck.map_obj]
  simp only [restrictToDomainFiberNatTrans, Functor.whiskerLeft_app]
  have nat := alpha_domainFiberTransport_naturality C α γ x.base
  exact congrArg (Grothendieck.mk _) (congrFun (congrArg Functor.obj nat.symm) x.fiber)

@[simp]
theorem innerFiberAltMap_map_base (α : F ⟶ G) {a : C}
    {x y : innerFiberAlt C F a} (f : x ⟶ y) :
    ((innerFiberAltMap C α a).map f).base = f.base := by
  simp only [innerFiberAltMap, Grothendieck.map_map]

@[simp]
theorem innerFiberAltTransition_map_base {a c : C} (γ : c ⟶ a)
    {x y : innerFiberAlt C F a} (f : x ⟶ y) :
    ((innerFiberAltTransition C F γ).map f).base = (Under.map γ).map f.base :=
  rfl

theorem domainFiberFunctor_map_map_base {a c : C} (γ : c ⟶ a)
    {x y : innerFiberAlt C F a} (f : x ⟶ y) :
    (((domainFiberFunctor C F).map γ).toFunctor.map f).base = (Under.map γ).map f.base :=
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem domainFiberFunctorNatTrans_rhs_base_eq (α : F ⟶ G) {a c : C} (γ : c ⟶ a)
    {X Y : innerFiberAlt C F a} (f : X ⟶ Y)
    (hX : (innerFiberAltMap C α c).obj
      ((innerFiberAltTransition C F γ).obj X) =
      (innerFiberAltTransition C G γ).obj
      ((innerFiberAltMap C α a).obj X))
    (hY : (innerFiberAltMap C α c).obj
      ((innerFiberAltTransition C F γ).obj Y) =
      (innerFiberAltTransition C G γ).obj
      ((innerFiberAltMap C α a).obj Y)) :
    (eqToHom hX ≫ (innerFiberAltTransition C G γ).map
      ((innerFiberAltMap C α a).map f) ≫ eqToHom hY.symm).base =
    (Under.map γ).map f.base := by
  rw [Grothendieck.comp_base, Grothendieck.comp_base]
  rw [Grothendieck.base_eqToHom, Grothendieck.base_eqToHom]
  simp only [innerFiberAltTransition_map_base, innerFiberAltMap_map_base]
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
/--
Core naturality of `innerFiberAltMap` with respect to transition functors
at the fiber level.
-/
theorem innerFiberAltMap_naturality_fiber (α : F ⟶ G) {a c : C} (γ : c ⟶ a)
    {X Y : innerFiberAlt C F a} (f : X ⟶ Y) :
    ((innerFiberAltMap C α c).map ((innerFiberAltTransition C F γ).map f)).fiber ≍
    ((innerFiberAltTransition C G γ).map ((innerFiberAltMap C α a).map f)).fiber := by
  simp only [innerFiberAltMap]
  erw [Grothendieck.map_map, Grothendieck.map_map]
  simp only [innerFiberAltTransition, innerFiberAltTransitionHom_fiber]
  simp only [restrictToDomainFiberNatTrans, Functor.whiskerLeft_app]
  simp only [Grothendieck.map_obj]
  simp only [innerFiberAltTransitionObj]
  simp only [Functor.map_comp, eqToHom_map]
  have alpha_nat := alpha_domainFiberTransport_naturality C α γ Y.base
  have alpha_nat_mor := Functor.congr_hom alpha_nat f.fiber
  simp only [Functor.comp_map] at alpha_nat_mor
  conv_rhs => rw [alpha_nat_mor]
  rw [Cat.eqToHom_app]
  conv_rhs => rw [Cat.eqToHom_app]
  simp only [functor_map_eqToHom]
  cat_disch

set_option backward.isDefEq.respectTransparency false in
def domainFiberFunctorNatTrans (α : F ⟶ G) :
    domainFiberFunctor C F ⟶ domainFiberFunctor C G where
  app a := (innerFiberAltMap C α a).toCatHom
  naturality {a c} γ := by
    apply Cat.Hom.ext
    fapply _root_.CategoryTheory.Functor.ext
    · intro x
      exact innerFiberAltMap_natural_obj C α γ x
    · intro X Y f
      apply Grothendieck.ext
      case w_base =>
        simp only [Cat.Hom.comp_toFunctor, domainFiberFunctor_map,
          Functor.toCatHom_toFunctor, Functor.comp_map, innerFiberAltMap_map_base,
          innerFiberAltTransition_map_base]
        rw [← domainFiberFunctorNatTrans_rhs_base_eq C α γ f
          (innerFiberAltMap_natural_obj C α γ X)
          (innerFiberAltMap_natural_obj C α γ Y)]
      case w_fiber =>
        simp only [Cat.Hom.comp_toFunctor]
        apply eq_of_heq
        apply HEq.trans (eqToHom_comp_heq _ _)
        apply HEq.trans (innerFiberAltMap_naturality_fiber C α γ f)
        apply HEq.symm
        exact Grothendieck.conj_eqToHom_fiber_heq
          (F := restrictToDomainFiber C G c) _ _ _

@[simp]
theorem domainFiberFunctorNatTrans_app (α : F ⟶ G) (a : C) :
    (domainFiberFunctorNatTrans C α).app a = (innerFiberAltMap C α a).toCatHom := rfl

@[simp]
theorem domainFiberFunctorNatTrans_id :
    domainFiberFunctorNatTrans C (𝟙 F) = 𝟙 (domainFiberFunctor C F) := by
  ext a
  simp only [domainFiberFunctorNatTrans, innerFiberAltMap_id, NatTrans.id_app,
    domainFiberFunctor, innerFiberAlt, Functor.toCatHom_toFunctor, Cat.Hom.id_toFunctor]
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem domainFiberFunctorNatTrans_comp (α : F ⟶ G) (β : G ⟶ H) :
    domainFiberFunctorNatTrans C (α ≫ β) =
      domainFiberFunctorNatTrans C α ≫ domainFiberFunctorNatTrans C β := by
  ext a
  simp only [domainFiberFunctorNatTrans, innerFiberAltMap_comp, NatTrans.comp_app,
    Cat.comp_eq_comp, Functor.toCatHom_toFunctor]

end AltFunctoriality

/-!
### The Alternative Connected Grothendieck Construction

The alternative connected Grothendieck construction is defined as
`GrothendieckContra' (domainFiberFunctor C F)`.

This is the dual of `ConnectedGrothendieckContra`, using `Under a` (domain-indexed
fibers) instead of `(Over b)^op` (codomain-indexed fibers).
-/

/--
The alternative connected Grothendieck construction.

This is defined as `GrothendieckContra' (domainFiberFunctor C F)`, where
`domainFiberFunctor C F : Cᵒᵖ' ⥤ Cat` assigns domain-indexed fiber categories.

An object is a pair `(a, e)` where `a : C` (viewed in `Cᵒᵖ'`) and
`e : innerFiberAlt C F a = Grothendieck (restrictToDomainFiber C F a)`.

A morphism from `(a, e)` to `(a', e')` consists of:
- `base : a ⟶ a'` in `Cᵒᵖ'` (equivalently `a' ⟶ a` in `C`)
- `fiber : e ⟶ (domainFiberFunctor.map base).obj e'`
-/
def ConnectedGrothendieckAlt : Type _ :=
  GrothendieckContra' (domainFiberFunctor C F)

instance : Category (ConnectedGrothendieckAlt C F) :=
  inferInstanceAs (Category (GrothendieckContra' (domainFiberFunctor C F)))

/-!
### Object and Morphism Equivalence

We establish that `ConnectedGrothendieckAlt` has the same objects and morphisms
as `ConnGrothendieckObj` and `ConnGrothendieckHom`, following the pattern used
for `ConnectedGrothendieckContra`.
-/

section ObjectEquivalence

/--
Convert an object of `ConnectedGrothendieckAlt` to `ConnGrothendieckObj`.

An object of `ConnectedGrothendieckAlt` is `(a, e)` where:
- `a : Cᵒᵖ'` (viewed as `a : C`)
- `e : innerFiberAlt C F a = Grothendieck (restrictToDomainFiber C F a)`
  which consists of `(un : Under a, fiber : F.obj (twObjMk' un.hom))`

This maps to `ConnGrothendieckObj`:
- `arrow = twObjMk' un.hom` (the twisted arrow from `a` to `un.right`)
- `fiber = e.fiber`
-/
def connGrothendieckAltObjToObj (x : ConnectedGrothendieckAlt C F) :
    ConnGrothendieckObj C F where
  arrow := (underToTwistedArrow C x.base).obj x.fiber.base
  fiber := x.fiber.fiber

/--
The equality between `(underToTwistedArrow C (twDom' arrow)).obj (Under.mk (twArr' arrow))`
and `arrow`.
-/
lemma underToTwArr_mk_twArr_eq (arrow : TwistedArrow' C) :
    (underToTwistedArrow C (twDom' arrow)).obj (Under.mk (twArr' arrow)) = arrow := by
  simp only [underToTwistedArrow, Under.mk_hom]
  exact twObjMk'_twArr' arrow

/--
Convert a `ConnGrothendieckObj` to an object of `ConnectedGrothendieckAlt`.

Given `(arrow, fiber)` in `ConnGrothendieckObj`:
- `base = twDom' arrow` (the domain of the arrow, viewed in `Cᵒᵖ'`)
- `fiber.base = Under.mk (twArr' arrow)` (the arrow as an object of `Under (twDom' arrow)`)
- `fiber.fiber` needs to be transported via the equality
  `(underToTwistedArrow C (twDom' arrow)).obj (Under.mk (twArr' arrow)) = arrow`
-/
def connGrothendieckObjToAltObj (x : ConnGrothendieckObj C F) :
    ConnectedGrothendieckAlt C F :=
  ⟨twDom' x.arrow,
   ⟨Under.mk (twArr' x.arrow),
    (eqToHom (congrArg F.obj (underToTwArr_mk_twArr_eq C x.arrow))).toFunctor.obj x.fiber⟩⟩

set_option backward.isDefEq.respectTransparency false in
/--
The round-trip from `ConnectedGrothendieckAlt` to `ConnGrothendieckObj` and back.
-/
theorem connGrothendieckAltObj_roundtrip (x : ConnectedGrothendieckAlt C F) :
    connGrothendieckObjToAltObj C F (connGrothendieckAltObjToObj C F x) = x := by
  unfold connGrothendieckAltObjToObj connGrothendieckObjToAltObj
  apply GrothendieckContra'.obj_ext
  · -- base equality: (Functor.fromPUnit x.base).obj x.fiber.base.left = x.base
    simp only [underToTwistedArrow, twObjMk'_dom]
    rfl
  · -- fiber HEq: inner Grothendieck objects are HEq
    simp only [heq_eq_eq, underToTwistedArrow, twObjMk'_arr, twObjMk'_dom]
    -- underToTwArr_mk_twArr_eq (twObjMk' x.fiber.base.hom) is rfl after simplification
    rfl

/--
The round-trip from `ConnGrothendieckObj` to `ConnectedGrothendieckAlt` and back.
-/
theorem connGrothendieckObj_altRoundtrip (x : ConnGrothendieckObj C F) :
    connGrothendieckAltObjToObj C F (connGrothendieckObjToAltObj C F x) = x := by
  simp only [connGrothendieckObjToAltObj, connGrothendieckAltObjToObj]
  apply ConnGrothendieckObj.ext
  · simp only [underToTwistedArrow, Under.mk_hom]
    exact twObjMk'_twArr' x.arrow
  · simp only [underToTwistedArrow, Under.mk_hom]
    exact eqToHom_obj_heq (F.obj _) (F.obj x.arrow)
      (congrArg F.obj (underToTwArr_mk_twArr_eq C x.arrow)) x.fiber

/--
The type of objects in `ConnectedGrothendieckAlt` is equivalent to `ConnGrothendieckObj`.
-/
def connGrothendieckAltObjEquiv :
    ConnectedGrothendieckAlt C F ≃ ConnGrothendieckObj C F where
  toFun := connGrothendieckAltObjToObj C F
  invFun := connGrothendieckObjToAltObj C F
  left_inv := connGrothendieckAltObj_roundtrip C F
  right_inv := connGrothendieckObj_altRoundtrip C F

end ObjectEquivalence

section MorphismEquivalence

/-!
### Morphism Equivalence

We establish that morphisms in `ConnectedGrothendieckAlt` correspond to
`ConnGrothendieckHom` between the corresponding objects.

A morphism `f : x ⟶ y` in `ConnectedGrothendieckAlt` consists of:
- `f.base : x.base ⟶ y.base` in `Cᵒᵖ'` (equivalently `y.base ⟶ x.base` in C)
- `f.fiber : x.fiber ⟶ (innerFiberAltTransition f.base).obj y.fiber`

The fiber morphism `f.fiber` is a Grothendieck morphism with:
- `f.fiber.base : x.fiber.base ⟶ ((Under.map f.base).obj y.fiber.base)`
- `f.fiber.fiber` in the appropriate fiber category
-/

section ProjectionToArrow

/-!
### Projection to Arrow Category

We define a projection functor from `ConnectedGrothendieckAlt` to `Arrow C`.

For an Alt object `x`:
- `x.base : C` is the domain of the underlying arrow
- `x.fiber.base : Under x.base` with `x.fiber.base.hom : x.base → x.fiber.base.right`
- The underlying arrow is `x.fiber.base.hom`

For an Alt morphism `f : x ⟶ y`:
- `f.base : x.base ⟶ y.base` in C (domain direction, forward)
- `f.fiber.base.right : x.fiber.base.right ⟶ (transported y.fiber).base.right`
  where transported preserves `.right`, so this is `x.cod ⟶ y.cod` (forward)
-/

/--
Convert an Alt object to an Arrow object.
-/
def connGrothendieckAltObjToArrow (x : ConnectedGrothendieckAlt C F) :
    Arrow C :=
  Arrow.mk x.fiber.base.hom

/--
Extract the domain arrow from an Alt morphism.
-/
def connGrothendieckAltHomDomArr {x y : ConnectedGrothendieckAlt C F}
    (f : x ⟶ y) : x.base ⟶ y.base :=
  f.base

/--
Extract the codomain arrow from an Alt morphism.

For `f : x ⟶ y`, the fiber morphism `f.fiber` is in `innerFiberAlt C F x.base`.
Its base component is an Under morphism, and `.right` gives the codomain direction.
-/
def connGrothendieckAltHomCodArr {x y : ConnectedGrothendieckAlt C F}
    (f : x ⟶ y) : x.fiber.base.right ⟶ y.fiber.base.right :=
  f.fiber.base.right

/--
The commuting square condition for Alt morphisms.
-/
theorem connGrothendieckAltMorphSquareComm {x y : ConnectedGrothendieckAlt C F}
    (f : x ⟶ y) :
    x.fiber.base.hom ≫ connGrothendieckAltHomCodArr C F f =
      connGrothendieckAltHomDomArr C F f ≫ y.fiber.base.hom := by
  simp only [connGrothendieckAltHomDomArr, connGrothendieckAltHomCodArr]
  -- f.fiber.base is an Under x.base morphism from x.fiber.base to the transported y.fiber.base
  -- The target is ((domainFiberFunctor C F).map f.base).obj y.fiber).base
  --             = (innerFiberAltTransitionObj C F f.base y.fiber).base
  --             = (Under.map f.base).obj y.fiber.base
  -- which has .hom = f.base ≫ y.fiber.base.hom and .right = y.fiber.base.right

  -- Under.w for f.fiber.base : x.fiber.base ⟶ (Under.map f.base).obj y.fiber.base gives:
  -- x.fiber.base.hom ≫ f.fiber.base.right = ((Under.map f.base).obj y.fiber.base).hom
  --                                       = f.base ≫ y.fiber.base.hom

  -- This is exactly the Arrow square condition!
  have h_under_w := Under.w f.fiber.base
  -- h_under_w : x.fiber.base.hom ≫ f.fiber.base.right =
  --             (((domainFiberFunctor C F).map f.base).obj y.fiber).base.hom
  simp only [domainFiberFunctor, innerFiberAltTransition] at h_under_w
  exact h_under_w

/--
Identity morphisms preserve the domain arrow component.
-/
@[simp]
theorem connGrothendieckAltHomDomArr_id (x : ConnectedGrothendieckAlt C F) :
    connGrothendieckAltHomDomArr C F (𝟙 x) = 𝟙 x.base := by
  simp only [connGrothendieckAltHomDomArr]
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
Identity morphisms preserve the codomain arrow component.
-/
@[simp]
theorem connGrothendieckAltHomCodArr_id (x : ConnectedGrothendieckAlt C F) :
    connGrothendieckAltHomCodArr C F (𝟙 x) = 𝟙 x.fiber.base.right := by
  simp only [connGrothendieckAltHomCodArr]
  -- 𝟙 x is definitionally GrothendieckContra'.id x via the category instance
  change (GrothendieckContra'.id x).fiber.base.right = 𝟙 x.fiber.base.right
  rw [GrothendieckContra'.id_fiber_val, Grothendieck.base_eqToHom, Under.eqToHom_right]
  rfl

/--
Composition preserves the domain arrow component.
-/
@[simp]
theorem connGrothendieckAltHomDomArr_comp {x y z : ConnectedGrothendieckAlt C F}
    (f : x ⟶ y) (g : y ⟶ z) :
    connGrothendieckAltHomDomArr C F (f ≫ g) =
      connGrothendieckAltHomDomArr C F f ≫ connGrothendieckAltHomDomArr C F g := by
  simp only [connGrothendieckAltHomDomArr]
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
Composition preserves the codomain arrow component.
-/
@[simp]
theorem connGrothendieckAltHomCodArr_comp {x y z : ConnectedGrothendieckAlt C F}
    (f : x ⟶ y) (g : y ⟶ z) :
    connGrothendieckAltHomCodArr C F (f ≫ g) =
      connGrothendieckAltHomCodArr C F f ≫ connGrothendieckAltHomCodArr C F g := by
  simp only [connGrothendieckAltHomCodArr]
  -- f ≫ g is definitionally GrothendieckContra'.comp f g via the category instance
  change (GrothendieckContra'.comp f g).fiber.base.right =
    f.fiber.base.right ≫ g.fiber.base.right
  rw [GrothendieckContra'.comp_fiber]
  simp only [domainFiberFunctor_map, Functor.toCatHom_toFunctor, innerFiberAltTransition_map]
  rw [Grothendieck.comp_base, Grothendieck.comp_base]
  rw [Comma.comp_right, Comma.comp_right]
  rw [innerFiberAltTransitionHom_base]
  rw [Under.map_map_right]
  rw [Grothendieck.base_eqToHom, Under.eqToHom_right]
  simp only [eqToHom_refl, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
/--
The projection functor from `ConnectedGrothendieckAlt` to the arrow category.

This functor forgets the fiber data:
- On objects: extracts the underlying arrow from the Alt structure
- On morphisms: extracts `(domArr, codArr)` forming a commutative square
-/
def connGrothendieckAltProjection :
    ConnectedGrothendieckAlt C F ⥤ Arrow C where
  obj x := connGrothendieckAltObjToArrow C F x
  map {x y} f := Arrow.homMk
    (connGrothendieckAltHomDomArr C F f)
    (connGrothendieckAltHomCodArr C F f)
    (connGrothendieckAltMorphSquareComm C F f).symm
  map_id x := by
    apply Arrow.hom_ext
    · simp only [Arrow.homMk_left, Arrow.id_left, connGrothendieckAltHomDomArr_id,
        connGrothendieckAltObjToArrow, Arrow.mk_left]
      rfl
    · simp only [Arrow.homMk_right, Arrow.id_right, connGrothendieckAltHomCodArr_id,
        connGrothendieckAltObjToArrow, Arrow.mk_right]
      rfl
  map_comp {x y z} f g := by
    apply Arrow.hom_ext
    · simp only [Arrow.comp_left, Arrow.homMk_left, connGrothendieckAltHomDomArr_comp]
    · simp only [Arrow.comp_right, Arrow.homMk_right, connGrothendieckAltHomCodArr_comp]

/--
The projection preserves domain extraction.
-/
@[simp]
lemma connGrothendieckAltProjection_obj_left
    (x : ConnectedGrothendieckAlt C F) :
    ((connGrothendieckAltProjection C F).obj x).left = x.base :=
  rfl

/--
The projection preserves codomain extraction.
-/
@[simp]
lemma connGrothendieckAltProjection_obj_right
    (x : ConnectedGrothendieckAlt C F) :
    ((connGrothendieckAltProjection C F).obj x).right = x.fiber.base.right :=
  rfl

/--
The projection preserves the underlying arrow.
-/
@[simp]
lemma connGrothendieckAltProjection_obj_hom
    (x : ConnectedGrothendieckAlt C F) :
    ((connGrothendieckAltProjection C F).obj x).hom = x.fiber.base.hom :=
  rfl

end ProjectionToArrow

section MorphismConversion

/-!
### Morphism Conversion

We establish that morphisms in `ConnectedGrothendieckAlt` correspond to
`ConnGrothendieckHom` between the corresponding objects.
-/

/--
The source category for the fiber morphism in `connGrothendieckAltHomToHom`.
This is the category `F.obj (connGrothendieckDiagCod ...)`.
-/
abbrev connGrothendieckAltHomFiberSrcCat {x y : ConnectedGrothendieckAlt C F}
    (f : x ⟶ y) : Cat :=
  F.obj (connGrothendieckDiagCod C (twObjMk' x.fiber.base.hom) f.fiber.base.right)

/--
The target category for the fiber morphism in `connGrothendieckAltHomToHom`.
This is the category containing the goal target.
-/
abbrev connGrothendieckAltHomFiberTgtCat {x y : ConnectedGrothendieckAlt C F}
    (f : x ⟶ y) : Cat :=
  F.obj (connGrothendieckDiagDom C (twObjMk' y.fiber.base.hom) f.base)

/--
The source category for `f.fiber.fiber`, which differs from the goal source
category by an `eqToHom` composition.
-/
abbrev connGrothendieckAltFiberFiberSrcCat {x y : ConnectedGrothendieckAlt C F}
    (f : x ⟶ y) : Cat :=
  (restrictToDomainFiber C F x.base).obj
    (((domainFiberFunctor C F).map f.base).toFunctor.obj y.fiber).base

/--
The underlying arrow equality from `Under.w`.
-/
theorem connGrothendieckAltHomFiberArrowEq {x y : ConnectedGrothendieckAlt C F}
    (f : x ⟶ y) :
    x.fiber.base.hom ≫ f.fiber.base.right = f.base ≫ y.fiber.base.hom := by
  have hw := Under.w f.fiber.base
  exact hw

/--
The equality between the goal source category and `f.fiber.fiber` source category.
-/
theorem connGrothendieckAltHomFiberSrcCat_eq {x y : ConnectedGrothendieckAlt C F}
    (f : x ⟶ y) :
    connGrothendieckAltHomFiberSrcCat C F f =
    connGrothendieckAltFiberFiberSrcCat C F f := by
  simp only [connGrothendieckAltHomFiberSrcCat, connGrothendieckAltFiberFiberSrcCat]
  simp only [restrictToDomainFiber, Functor.comp_obj, underToTwistedArrow]
  simp only [domainFiberFunctor, innerFiberAltTransition]
  simp only [connGrothendieckDiagCod, twObjMk'_arr]
  exact congrArg F.obj (congrArg twObjMk' (connGrothendieckAltHomFiberArrowEq C F f))

/--
The target category for `f.fiber.fiber`.
This is the same as `connGrothendieckAltFiberFiberSrcCat` because both source and target
of a Grothendieck morphism live in the same category.
-/
abbrev connGrothendieckAltFiberFiberTgtCat {x y : ConnectedGrothendieckAlt C F}
    (f : x ⟶ y) : Cat :=
  connGrothendieckAltFiberFiberSrcCat C F f

/--
The source object for the fiber morphism goal lives in `connGrothendieckAltHomFiberSrcCat`.
-/
def connGrothendieckAltHomFiberSrc {x y : ConnectedGrothendieckAlt C F}
    (f : x ⟶ y) : connGrothendieckAltHomFiberSrcCat C F f :=
  (F.map (connGrothendieckTwMorphCod C (twObjMk' x.fiber.base.hom)
    f.fiber.base.right)).toFunctor.obj x.fiber.fiber

/--
The source object for `f.fiber.fiber` lives in `connGrothendieckAltFiberFiberSrcCat`.
-/
def connGrothendieckAltFiberFiberSrc {x y : ConnectedGrothendieckAlt C F}
    (f : x ⟶ y) : connGrothendieckAltFiberFiberSrcCat C F f :=
  ((restrictToDomainFiber C F x.base).map f.fiber.base).toFunctor.obj x.fiber.fiber

/--
The target object for `f.fiber.fiber` lives in `connGrothendieckAltFiberFiberTgtCat`.
-/
def connGrothendieckAltFiberFiberTgt {x y : ConnectedGrothendieckAlt C F}
    (f : x ⟶ y) : connGrothendieckAltFiberFiberTgtCat C F f :=
  (innerFiberAltTransitionObj C F f.base y.fiber).fiber

/--
The target object for the fiber morphism goal lives in `connGrothendieckAltHomFiberSrcCat`.
(After the eqToHom composition, the target is in the same category as the source.)
-/
def connGrothendieckAltHomFiberTgt {x y : ConnectedGrothendieckAlt C F}
    (f : x ⟶ y)
    (h_sq : x.fiber.base.hom ≫ f.fiber.base.right = f.base ≫ y.fiber.base.hom) :
    connGrothendieckAltHomFiberSrcCat C F f :=
  (F.map (connGrothendieckTwMorphDom C (twObjMk' y.fiber.base.hom) f.base ≫
    eqToHom (connGrothendieckDiagEq C F
      (connGrothendieckAltObjToObj C F x)
      (connGrothendieckAltObjToObj C F y)
      f.base f.fiber.base.right (by
        simp only [connGrothendieckAltObjToObj, underToTwistedArrow, twObjMk'_arr]
        exact h_sq)))).toFunctor.obj y.fiber.fiber

set_option backward.isDefEq.respectTransparency false in
/--
The source objects are equal after transport via the category equality.
-/
theorem connGrothendieckAltHomFiberSrc_eq {x y : ConnectedGrothendieckAlt C F}
    (f : x ⟶ y) :
    (eqToHom (connGrothendieckAltHomFiberSrcCat_eq C F f)).toFunctor.obj
      (connGrothendieckAltHomFiberSrc C F f) =
    connGrothendieckAltFiberFiberSrc C F f := by
  simp only [connGrothendieckAltHomFiberSrc, connGrothendieckAltFiberFiberSrc]
  simp only [restrictToDomainFiber, Functor.comp_obj, Functor.comp_map]
  rw [underToTwistedArrow_map_eq_connGrothendieckTwMorphCod C f.base f.fiber.base]
  simp only [Functor.map_comp, eqToHom_map]
  rfl

/--
In Cat, composing `eqToHom h` with `eqToHom h.symm` on objects gives identity.
-/
lemma eqToHom_comp_symm_obj (A B : Cat) (h : A = B) (x : A.α) :
    (eqToHom h.symm).toFunctor.obj ((eqToHom h).toFunctor.obj x) = x := by
  cases h
  rfl

/--
In Cat, composing `eqToHom h.symm` with `eqToHom h` on objects gives identity.
-/
lemma eqToHom_symm_comp_obj (A B : Cat) (h : A = B) (y : B.α) :
    (eqToHom h).toFunctor.obj ((eqToHom h.symm).toFunctor.obj y) = y := by
  cases h
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
The fiber morphism for `connGrothendieckAltHomToHom`.

This constructs a morphism by casting `f.fiber.fiber` using the type equalities
that follow from the commutativity square.
-/
def connGrothendieckAltHomFiberMorph {x y : ConnectedGrothendieckAlt C F}
    (f : x ⟶ y)
    (h_sq : x.fiber.base.hom ≫ f.fiber.base.right = f.base ≫ y.fiber.base.hom) :
    connGrothendieckAltHomFiberSrc C F f ⟶
    connGrothendieckAltHomFiberTgt C F f h_sq := by
  let cat_eq := connGrothendieckAltHomFiberSrcCat_eq C F f
  let transported := (eqToHom cat_eq.symm).toFunctor.map f.fiber.fiber
  have src_eq : (eqToHom cat_eq.symm).toFunctor.obj (connGrothendieckAltFiberFiberSrc C F f) =
      connGrothendieckAltHomFiberSrc C F f := by
    have h := connGrothendieckAltHomFiberSrc_eq C F f
    rw [← h]
    exact eqToHom_comp_symm_obj _ _ cat_eq _
  have tgt_eq : (eqToHom cat_eq.symm).toFunctor.obj (connGrothendieckAltFiberFiberTgt C F f) =
      connGrothendieckAltHomFiberTgt C F f h_sq := by
    simp only [connGrothendieckAltFiberFiberTgt, connGrothendieckAltHomFiberTgt]
    simp only [innerFiberAltTransitionObj, domainFiberTransport]
    rw [domainFiberTransportTwMorph_eq_connGrothendieckTwMorphDom C f.base y.fiber.base]
    simp only [Functor.map_comp, eqToHom_map, Cat.Hom.comp_toFunctor, Functor.comp_obj]
  exact eqToHom src_eq.symm ≫ transported ≫ eqToHom tgt_eq

/--
Convert a morphism in `ConnectedGrothendieckAlt` to a `ConnGrothendieckHom`.

For a morphism `f : x ⟶ y`:
- `domArr = f.base` (the base component)
- `codArr = f.fiber.base.right` (the codomain direction from the fiber)
- `square_comm` from `connGrothendieckAltMorphSquareComm`
- `fiberMorph` from `f.fiber.fiber` with appropriate transport
-/
def connGrothendieckAltHomToHom {x y : ConnectedGrothendieckAlt C F}
    (f : x ⟶ y) :
    ConnGrothendieckHom C F
      (connGrothendieckAltObjToObj C F x)
      (connGrothendieckAltObjToObj C F y) where
  domArr := connGrothendieckAltHomDomArr C F f
  codArr := connGrothendieckAltHomCodArr C F f
  square_comm := by
    simp only [connGrothendieckAltObjToObj, connGrothendieckAltHomDomArr,
      connGrothendieckAltHomCodArr]
    simp only [underToTwistedArrow, twObjMk'_arr]
    exact connGrothendieckAltMorphSquareComm C F f
  fiberMorph := connGrothendieckAltHomFiberMorph C F f
    (connGrothendieckAltMorphSquareComm C F f)

section ReverseConversion

/-!
### Reverse Morphism Conversion

We define the reverse conversion from `ConnGrothendieckHom` to Alt morphisms.
-/

/--
The base component for `connGrothendieckHomToAltHom`.
This is simply `m.domArr`.
-/
def connGrothendieckHomToAltBase {x y : ConnGrothendieckObj C F}
    (m : ConnGrothendieckHom C F x y) :
    twDom' x.arrow ⟶ twDom' y.arrow :=
  m.domArr

/--
The target Under object after transition for `connGrothendieckHomToAltHom`.
This is `(Under.map m.domArr).obj (Under.mk (twArr' y.arrow))`.
-/
abbrev connGrothendieckHomToAltFiberTargetBase {x y : ConnGrothendieckObj C F}
    (m : ConnGrothendieckHom C F x y) : Under (twDom' x.arrow) :=
  (Under.map m.domArr).obj (Under.mk (twArr' y.arrow))

/--
The Under morphism for the fiber component of `connGrothendieckHomToAltHom`.
Uses `m.codArr` with the commutativity from `m.square_comm`.
-/
def connGrothendieckHomToAltFiberBase {x y : ConnGrothendieckObj C F}
    (m : ConnGrothendieckHom C F x y) :
    Under.mk (twArr' x.arrow) ⟶ connGrothendieckHomToAltFiberTargetBase C F m :=
  Under.homMk m.codArr m.square_comm

/--
The source fiber element for `connGrothendieckHomToAltHom`.
This is the fiber of `connGrothendieckObjToAltObj C F x`.
-/
abbrev connGrothendieckHomToAltFiberSrcObj {x : ConnGrothendieckObj C F} :
    (restrictToDomainFiber C F (twDom' x.arrow)).obj (Under.mk (twArr' x.arrow)) :=
  (eqToHom (congrArg F.obj (underToTwArr_mk_twArr_eq C x.arrow))).toFunctor.obj x.fiber

/--
The target fiber element after transition for `connGrothendieckHomToAltHom`.
-/
abbrev connGrothendieckHomToAltFiberTgtObj {x y : ConnGrothendieckObj C F}
    (m : ConnGrothendieckHom C F x y) :
    (restrictToDomainFiber C F (twDom' x.arrow)).obj
      (connGrothendieckHomToAltFiberTargetBase C F m) :=
  (innerFiberAltTransitionObj C F m.domArr
    ⟨Under.mk (twArr' y.arrow), connGrothendieckHomToAltFiberSrcObj C F⟩).fiber

/--
The source category for the fiber morphism in `connGrothendieckHomToAltHom`.
-/
abbrev connGrothendieckHomToAltFiberCat {x y : ConnGrothendieckObj C F}
    (m : ConnGrothendieckHom C F x y) : Cat :=
  (restrictToDomainFiber C F (twDom' x.arrow)).obj
    (connGrothendieckHomToAltFiberTargetBase C F m)

/--
The source object of the fiber morphism (after transport via the Under morphism).
-/
abbrev connGrothendieckHomToAltFiberMorphSrc {x y : ConnGrothendieckObj C F}
    (m : ConnGrothendieckHom C F x y) :
    connGrothendieckHomToAltFiberCat C F m :=
  ((restrictToDomainFiber C F (twDom' x.arrow)).map
    (connGrothendieckHomToAltFiberBase C F m)).toFunctor.obj
    (connGrothendieckHomToAltFiberSrcObj C F)

/--
The target object of the fiber morphism.
-/
abbrev connGrothendieckHomToAltFiberMorphTgt {x y : ConnGrothendieckObj C F}
    (m : ConnGrothendieckHom C F x y) :
    connGrothendieckHomToAltFiberCat C F m :=
  connGrothendieckHomToAltFiberTgtObj C F m

/--
The category equality for the fiber morphism source.
-/
theorem connGrothendieckHomToAltFiberMorphSrc_cat_eq {x y : ConnGrothendieckObj C F}
    (m : ConnGrothendieckHom C F x y) :
    connGrothendieckHomToAltFiberCat C F m =
    F.obj (connGrothendieckDiagCod C x.arrow m.codArr) := by
  simp only [connGrothendieckHomToAltFiberCat, connGrothendieckHomToAltFiberTargetBase]
  simp only [restrictToDomainFiber, Functor.comp_obj]
  simp only [underToTwistedArrow_map_obj_eq, Under.mk_hom]
  simp only [connGrothendieckDiagCod]
  congr 1
  have hw := Under.w (connGrothendieckHomToAltFiberBase C F m)
  simp only [Under.map_obj_hom, Under.mk_hom] at hw
  exact congrArg twObjMk' hw.symm

/--
The source of `fiberMorph_transported` after transport.
-/
abbrev connGrothendieckHomToAltFiberMorphTransportedSrc {x y : ConnGrothendieckObj C F}
    (m : ConnGrothendieckHom C F x y) :
    connGrothendieckHomToAltFiberCat C F m :=
  let cat_eq := connGrothendieckHomToAltFiberMorphSrc_cat_eq C F m
  (eqToHom cat_eq.symm).toFunctor.obj
    ((F.map (connGrothendieckTwMorphCod C x.arrow m.codArr)).toFunctor.obj x.fiber)

/--
The target of `fiberMorph_transported` after transport.
-/
abbrev connGrothendieckHomToAltFiberMorphTransportedTgt {x y : ConnGrothendieckObj C F}
    (m : ConnGrothendieckHom C F x y) :
    connGrothendieckHomToAltFiberCat C F m :=
  let cat_eq := connGrothendieckHomToAltFiberMorphSrc_cat_eq C F m
  (eqToHom cat_eq.symm).toFunctor.obj
    ((F.map (connGrothendieckTwMorphDom C y.arrow m.domArr ≫
      eqToHom (connGrothendieckDiagEq C F x y m.domArr m.codArr m.square_comm))).toFunctor.obj
        y.fiber)

set_option backward.isDefEq.respectTransparency false in
/--
The underlying Under morphism map equals `connGrothendieckTwMorphCod` composed with eqToHom.
-/
theorem connGrothendieckHomToAltFiberBase_twArr_eq {x y : ConnGrothendieckObj C F}
    (m : ConnGrothendieckHom C F x y) :
    (underToTwistedArrow C (twDom' x.arrow)).map (connGrothendieckHomToAltFiberBase C F m) =
    connGrothendieckTwMorphCod C x.arrow m.codArr ≫
      eqToHom (by
        simp only [connGrothendieckDiagCod, underToTwistedArrow, Under.map_obj_hom, Under.mk_hom]
        simp only [connGrothendieckHomToAltFiberTargetBase]
        congr 1
        exact m.square_comm) := by
  apply twHom'_ext
  · simp only [underToTwistedArrow, twHomMk'_domArr, twDomArr'_comp, twDomArr'_eqToHom,
      connGrothendieckTwMorphCod, connGrothendieckDiagCod, Under.map_obj_hom,
      twObjMk'_dom, id, Category.comp_id, connGrothendieckHomToAltFiberBase,
      connGrothendieckHomToAltFiberTargetBase, Under.mk_hom, eqToHom_refl]
    rfl
  · simp only [underToTwistedArrow, twHomMk'_codArr, twCodArr'_comp, twCodArr'_eqToHom,
      connGrothendieckTwMorphCod, connGrothendieckDiagCod, Under.map_obj_hom,
      twObjMk'_cod, id, eqToHom_refl, Category.comp_id, connGrothendieckHomToAltFiberBase,
      connGrothendieckHomToAltFiberTargetBase, Under.mk_hom]
    rfl

set_option backward.isDefEq.respectTransparency false in
/--
Source equality for fiber morphism.
-/
theorem connGrothendieckHomToAltFiberMorphSrc_eq {x y : ConnGrothendieckObj C F}
    (m : ConnGrothendieckHom C F x y) :
    connGrothendieckHomToAltFiberMorphSrc C F m =
    connGrothendieckHomToAltFiberMorphTransportedSrc C F m := by
  simp only [connGrothendieckHomToAltFiberMorphSrc,
    connGrothendieckHomToAltFiberMorphTransportedSrc]
  simp only [connGrothendieckHomToAltFiberSrcObj]
  simp only [restrictToDomainFiber, Functor.comp_obj, Functor.comp_map]
  rw [connGrothendieckHomToAltFiberBase_twArr_eq]
  simp only [Functor.map_comp, eqToHom_map, Cat.Hom.comp_toFunctor, Functor.comp_obj]
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
The fiber transport commutes with functor application up to eqToHom.

This lemma handles the case where applying `eqToHom` before vs after a functor
gives equivalent results when the proof terms compose appropriately.
-/
lemma fiberMorphTgt_functor_eqToHom_comm {x y : ConnGrothendieckObj C F}
    (m : ConnGrothendieckHom C F x y) :
    (F.map (connGrothendieckTwMorphDom C y.arrow m.domArr)).toFunctor.obj
      ((eqToHom (congrArg F.obj (underToTwArr_mk_twArr_eq C y.arrow))).toFunctor.obj y.fiber) =
    (eqToHom (connGrothendieckHomToAltFiberMorphSrc_cat_eq C F m).symm).toFunctor.obj
      ((eqToHom (congrArg F.obj
        (connGrothendieckDiagEq C F x y m.domArr m.codArr m.square_comm))).toFunctor.obj
        ((F.map (connGrothendieckTwMorphDom C y.arrow m.domArr)).toFunctor.obj y.fiber)) := by
  simp only [underToTwistedArrow, Under.mk_hom,
    twObjMk'_twArr', eqToHom_refl, Cat.Hom.id_toFunctor, Functor.id_obj]
  conv_rhs =>
    rw [← Functor.comp_obj, ← Cat.Hom.comp_toFunctor]
  simp only [eqToHom_trans, eqToHom_refl, Cat.Hom.id_toFunctor, Functor.id_obj]

set_option backward.isDefEq.respectTransparency false in
/--
Target equality for fiber morphism.
-/
theorem connGrothendieckHomToAltFiberMorphTgt_eq {x y : ConnGrothendieckObj C F}
    (m : ConnGrothendieckHom C F x y) :
    connGrothendieckHomToAltFiberMorphTgt C F m =
    connGrothendieckHomToAltFiberMorphTransportedTgt C F m := by
  simp only [connGrothendieckHomToAltFiberMorphTgt,
    connGrothendieckHomToAltFiberMorphTransportedTgt]
  simp only [connGrothendieckHomToAltFiberTgtObj, connGrothendieckHomToAltFiberSrcObj]
  simp only [innerFiberAltTransitionObj, domainFiberTransport]
  simp only [domainFiberTransportTwMorph, twObjMk'_twArr', Under.mk_hom]
  have h := domainFiberTransportTwMorph_eq_connGrothendieckTwMorphDom C m.domArr
    (Under.mk (twArr' y.arrow))
  simp only [domainFiberTransportTwMorph, twObjMk'_twArr', Under.mk_hom] at h
  rw [h]
  simp only [Functor.map_comp, Cat.Hom.comp_toFunctor, Functor.comp_obj, eqToHom_map]
  exact fiberMorphTgt_functor_eqToHom_comm C F m

/--
The fiber morphism for `connGrothendieckHomToAltHom`.

This transports `m.fiberMorph` through the appropriate `eqToHom`s.
-/
def connGrothendieckHomToAltFiberMorph {x y : ConnGrothendieckObj C F}
    (m : ConnGrothendieckHom C F x y) :
    connGrothendieckHomToAltFiberMorphSrc C F m ⟶
    connGrothendieckHomToAltFiberMorphTgt C F m := by
  let cat_eq := connGrothendieckHomToAltFiberMorphSrc_cat_eq C F m
  let fiberMorph_transported := (eqToHom cat_eq.symm).toFunctor.map m.fiberMorph
  let src_eq := connGrothendieckHomToAltFiberMorphSrc_eq C F m
  let tgt_eq := connGrothendieckHomToAltFiberMorphTgt_eq C F m
  exact eqToHom src_eq ≫ fiberMorph_transported ≫ eqToHom tgt_eq.symm

/--
Convert a `ConnGrothendieckHom` to a morphism in `ConnectedGrothendieckAlt`.

For a morphism `m : x ⟶ y` in `ConnGrothendieckHom`:
- `base = m.domArr`
- `fiber.base = Under.homMk m.codArr m.square_comm`
- `fiber.fiber` from `m.fiberMorph` with appropriate transport
-/
def connGrothendieckHomToAltHom {x y : ConnGrothendieckObj C F}
    (m : ConnGrothendieckHom C F x y) :
    connGrothendieckObjToAltObj C F x ⟶ connGrothendieckObjToAltObj C F y where
  base := m.domArr
  fiber := {
    base := connGrothendieckHomToAltFiberBase C F m
    fiber := connGrothendieckHomToAltFiberMorph C F m
  }

set_option backward.isDefEq.respectTransparency false in
/--
Helper lemma for the fiber morphism roundtrip.
The composition of eqToHom transports in the roundtrip gives back the original fiber morphism.
-/
lemma connGrothendieckHom_altFiberMorphRoundtrip {x y : ConnGrothendieckObj C F}
    (f : ConnGrothendieckHom C F x y) :
    connGrothendieckAltHomFiberMorph C F (connGrothendieckHomToAltHom C F f)
      (connGrothendieckAltMorphSquareComm C F (connGrothendieckHomToAltHom C F f)) =
    f.fiberMorph := by
  simp only [connGrothendieckAltHomFiberMorph, connGrothendieckHomToAltHom,
    connGrothendieckHomToAltFiberMorph]
  apply eq_of_heq
  conv_lhs => rw [← Category.assoc]
  apply HEq.trans (comp_eqToHom_heq _ _)
  apply HEq.trans
  · apply eqToHom_comp_heq
  apply HEq.trans (Cat.eqToHom_map_heq _ _)
  conv_lhs => rw [← Category.assoc]
  apply HEq.trans (comp_eqToHom_heq _ _)
  apply HEq.trans
  · apply eqToHom_comp_heq
  exact Cat.eqToHom_map_heq _ _

/--
Round-trip: converting a `ConnGrothendieckHom` to `ConnectedGrothendieckAlt` morphism
and back gives the original morphism (up to the object round-trip equality).
-/
theorem connGrothendieckHom_altRoundtrip {x y : ConnGrothendieckObj C F}
    (f : ConnGrothendieckHom C F x y) :
    HEq (connGrothendieckAltHomToHom C F (connGrothendieckHomToAltHom C F f)) f := by
  have hx : connGrothendieckAltObjToObj C F (connGrothendieckObjToAltObj C F x) = x :=
    connGrothendieckObj_altRoundtrip C F x
  have hy : connGrothendieckAltObjToObj C F (connGrothendieckObjToAltObj C F y) = y :=
    connGrothendieckObj_altRoundtrip C F y
  cases hx
  cases hy
  apply heq_of_eq
  simp only [connGrothendieckAltHomToHom, connGrothendieckHomToAltHom]
  simp only [connGrothendieckAltHomDomArr, connGrothendieckAltHomCodArr]
  simp only [connGrothendieckHomToAltFiberBase, Under.homMk_right]
  obtain ⟨domArr, codArr, square_comm, fiberMorph⟩ := f
  congr 1
  exact connGrothendieckHom_altFiberMorphRoundtrip C F _

/--
Round-trip: converting a `ConnectedGrothendieckAlt` morphism to `ConnGrothendieckHom`
and back gives the original morphism (up to the object round-trip equality).
-/
theorem connGrothendieckAltHom_roundtrip {x y : ConnectedGrothendieckAlt C F}
    (f : x ⟶ y) :
    HEq (connGrothendieckHomToAltHom C F (connGrothendieckAltHomToHom C F f)) f := by
  have hx : connGrothendieckObjToAltObj C F (connGrothendieckAltObjToObj C F x) = x :=
    connGrothendieckAltObj_roundtrip C F x
  have hy : connGrothendieckObjToAltObj C F (connGrothendieckAltObjToObj C F y) = y :=
    connGrothendieckAltObj_roundtrip C F y
  cases hx
  cases hy
  apply heq_of_eq
  simp only [connGrothendieckHomToAltHom, connGrothendieckAltHomToHom]
  simp only [connGrothendieckAltHomDomArr, connGrothendieckAltHomCodArr]
  refine GrothendieckContra'.ext _ _ rfl ?_
  simp only [eqToHom_refl, Category.comp_id]
  apply Grothendieck.ext
  · simp only [connGrothendieckAltHomFiberMorph, connGrothendieckHomToAltFiberMorph]
    apply eq_of_heq
    apply HEq.trans
    · apply eqToHom_comp_heq
    conv_lhs => rw [← Category.assoc]
    apply HEq.trans (comp_eqToHom_heq _ _)
    apply HEq.trans
    · apply eqToHom_comp_heq
    apply HEq.trans (Cat.eqToHom_map_heq _ _)
    conv_lhs => rw [← Category.assoc]
    apply HEq.trans (comp_eqToHom_heq _ _)
    apply HEq.trans
    · apply eqToHom_comp_heq
    exact Cat.eqToHom_map_heq _ _
  · simp only [connGrothendieckHomToAltFiberBase]
    apply Under.UnderMorphism.ext
    simp only [Under.homMk_right]

end ReverseConversion

end MorphismConversion

end MorphismEquivalence

section AltFunctorMap

variable {F} {G H : TwistedArrow' C ⥤ Cat.{v, u}}

/--
A natural transformation `α : F ⟶ G` induces a functor between the corresponding
alternative connected Grothendieck constructions.

This is defined using `GrothendieckContra'.map` with `domainFiberFunctorNatTrans`.
-/
def connGrothendieckAltMap (α : F ⟶ G) :
    ConnectedGrothendieckAlt C F ⥤ ConnectedGrothendieckAlt C G :=
  GrothendieckContra'.map (domainFiberFunctorNatTrans C α)

@[simp]
theorem connGrothendieckAltMap_obj (α : F ⟶ G)
    (x : ConnectedGrothendieckAlt C F) :
    (connGrothendieckAltMap C α).obj x =
      ⟨x.base, (innerFiberAltMap C α x.base).obj x.fiber⟩ :=
  rfl

@[simp]
theorem connGrothendieckAltMap_map_base (α : F ⟶ G)
    {x y : ConnectedGrothendieckAlt C F} (f : x ⟶ y) :
    ((connGrothendieckAltMap C α).map f).base = f.base :=
  rfl

@[simp]
theorem connGrothendieckAltMap_id :
    connGrothendieckAltMap C (𝟙 F) =
      𝟭 (ConnectedGrothendieckAlt C F) := by
  simp only [connGrothendieckAltMap, domainFiberFunctorNatTrans_id,
    GrothendieckContra'.map_id_eq, ConnectedGrothendieckAlt]

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem connGrothendieckAltMap_comp (α : F ⟶ G) (β : G ⟶ H) :
    connGrothendieckAltMap C (α ≫ β) =
      connGrothendieckAltMap C α ⋙ connGrothendieckAltMap C β := by
  simp only [connGrothendieckAltMap, domainFiberFunctorNatTrans_comp,
    GrothendieckContra'.map_comp_eq]

/--
The map functor preserves the base of the fiber (the Under object).
-/
@[simp]
theorem connGrothendieckAltMap_obj_fiber_base (α : F ⟶ G)
    (x : ConnectedGrothendieckAlt C F) :
    ((connGrothendieckAltMap C α).obj x).fiber.base = x.fiber.base := by
  simp only [connGrothendieckAltMap_obj, innerFiberAltMap_obj_base]

set_option backward.isDefEq.respectTransparency false in
/--
The map preserves the right component of the fiber's base in morphisms.
-/
theorem connGrothendieckAltMap_map_fiber_base_right (α : F ⟶ G)
    {x y : ConnectedGrothendieckAlt C F} (f : x ⟶ y) :
    ((connGrothendieckAltMap C α).map f).fiber.base.right = f.fiber.base.right := by
  change ((GrothendieckContra'.map (domainFiberFunctorNatTrans C α)).map f).fiber.base.right =
    f.fiber.base.right
  erw [GrothendieckContra'.map_map]
  rw [Grothendieck.comp_base, Comma.comp_right]
  simp only [domainFiberFunctorNatTrans_app, Functor.toCatHom_toFunctor]
  rw [innerFiberAltMap_map_base]
  simp only [Cat.Hom₂.eqToHom_toNatTrans, eqToHom_app]
  rw [Grothendieck.base_eqToHom, Under.eqToHom_right, eqToHom_refl, Category.comp_id]

/--
The map functor preserves the base of the fiber in morphisms.
-/
@[simp]
theorem connGrothendieckAltMap_map_fiber_base (α : F ⟶ G)
    {x y : ConnectedGrothendieckAlt C F} (f : x ⟶ y) :
    ((connGrothendieckAltMap C α).map f).fiber.base = f.fiber.base := by
  apply Under.UnderMorphism.ext
  exact connGrothendieckAltMap_map_fiber_base_right C α f

set_option backward.isDefEq.respectTransparency false in
/--
The Alt map functor commutes with the projection to `Arrow C`.
-/
theorem connGrothendieckAltMap_comp_projection (α : F ⟶ G) :
    connGrothendieckAltMap C α ⋙ connGrothendieckAltProjection C G =
    connGrothendieckAltProjection C F := by
  fapply _root_.CategoryTheory.Functor.ext
  · intro x
    simp only [Functor.comp_obj, connGrothendieckAltProjection,
      connGrothendieckAltMap_obj, connGrothendieckAltObjToArrow]
    rw [innerFiberAltMap_obj_base]
  · intro X Y f
    apply Arrow.hom_ext
    · simp only [Functor.comp_map, connGrothendieckAltProjection, Arrow.homMk_left,
        connGrothendieckAltHomDomArr, eqToHom_refl, Category.id_comp, Category.comp_id,
        connGrothendieckAltMap_map_base]
    · simp only [Functor.comp_map, connGrothendieckAltProjection, Arrow.homMk_right,
        connGrothendieckAltHomCodArr, eqToHom_refl, Category.id_comp, Category.comp_id,
        connGrothendieckAltMap_map_base, connGrothendieckAltMap_map_fiber_base_right]

/--
The alternative connected Grothendieck construction as a functor to the over category
`Over (Cat.of (Arrow C))`.

For each `F : TwistedArrow' C ⥤ Cat`, we get `ConnectedGrothendieckAlt C F` with
a projection to `Arrow C`. Natural transformations `α : F ⟶ G` induce functors
that commute with the projections.
-/
def connGrothendieckAltFunctor :
    (TwistedArrow' C ⥤ Cat.{v, u}) ⥤ Over (Cat.of (Arrow C)) where
  obj F' := Over.mk (Y := Cat.of (ConnectedGrothendieckAlt C F'))
    (connGrothendieckAltProjection C F').toCatHom
  map {F' G'} α := Over.homMk (connGrothendieckAltMap C α).toCatHom
    (by apply Cat.Hom.ext; simp only [Cat.Hom.comp_toFunctor, Functor.toCatHom_toFunctor]
        exact connGrothendieckAltMap_comp_projection C α)
  map_id F' := by
    apply Over.OverMorphism.ext
    simp only [Over.mk_left, Over.homMk_left]
    apply Cat.Hom.ext
    simp only [Functor.toCatHom_toFunctor]
    exact connGrothendieckAltMap_id C
  map_comp {F' G' H'} α β := by
    apply Over.OverMorphism.ext
    simp only [Over.mk_left, Over.homMk_left, Over.comp_left]
    apply Cat.Hom.ext
    simp only [Cat.Hom.comp_toFunctor, Functor.toCatHom_toFunctor]
    exact connGrothendieckAltMap_comp C α β

end AltFunctorMap

end AlternativeConstruction

/-!
## Functor Characterization for Connected Grothendieck

This section provides introduction and elimination rules for functors
to, from, and between connected Grothendieck constructions, analogous to
`FunctorToData`, `FunctorFromData`, and `FunctorBetweenData` in
`Grothendieck.lean`.

The connected Grothendieck construction projects to `Arrow C`, so functors
are characterized relative to this projection via the "diagonal construction".
-/

section FunctorCharacterization

variable {C : Type u} [Category.{v} C]

/-!
### The Diagonal Construction

Given an Arrow morphism `(left, right) : arr ⟶ arr'`, the diagonal is the
arrow `arr.hom ≫ right = left ≫ arr'.hom`. There are canonical TwistedArrow
morphisms from both the source and target arrows to this diagonal.
-/

section DiagonalConstruction

variable {arr arr' : Arrow C} (arrMor : arr ⟶ arr')

/--
The diagonal arrow from an Arrow morphism.
Given `arr.hom : arr.left ⟶ arr.right` and `arr'.hom : arr'.left ⟶ arr'.right`
with `arrMor.left : arr.left ⟶ arr'.left` and
`arrMor.right : arr.right ⟶ arr'.right`,
the diagonal is `arr.hom ≫ arrMor.right : arr.left ⟶ arr'.right`.
-/
def arrowDiagonal : arr.left ⟶ arr'.right :=
  arr.hom ≫ arrMor.right

/--
The diagonal equals the other composite via the Arrow square.
-/
lemma arrowDiagonal_eq :
    arrowDiagonal arrMor = arrMor.left ≫ arr'.hom := arrMor.w.symm

/--
Convert an Arrow to its corresponding TwistedArrow.
-/
def arrowToTwisted (arr : Arrow C) : TwistedArrow' C :=
  twObjMk' arr.hom

@[simp]
lemma arrowToTwisted_dom (arr : Arrow C) :
    twDom' (arrowToTwisted arr) = arr.left := rfl

@[simp]
lemma arrowToTwisted_cod (arr : Arrow C) :
    twCod' (arrowToTwisted arr) = arr.right := rfl

@[simp]
lemma arrowToTwisted_arr (arr : Arrow C) :
    twArr' (arrowToTwisted arr) = arr.hom := rfl

/--
The diagonal as a TwistedArrow object.
-/
def arrowDiagonalTwisted : TwistedArrow' C :=
  twObjMk' (arrowDiagonal arrMor)

@[simp]
lemma arrowDiagonalTwisted_dom :
    twDom' (arrowDiagonalTwisted arrMor) = arr.left := rfl

@[simp]
lemma arrowDiagonalTwisted_cod :
    twCod' (arrowDiagonalTwisted arrMor) = arr'.right := rfl

@[simp]
lemma arrowDiagonalTwisted_arr :
    twArr' (arrowDiagonalTwisted arrMor) = arrowDiagonal arrMor := rfl

/--
Canonical TwistedArrow morphism from the source arrow to the diagonal.
Domain component is identity, codomain component is `arrMor.right`.
-/
def twMorphToDiagonalLeft :
    arrowToTwisted arr ⟶ arrowDiagonalTwisted arrMor :=
  twHomMk' (𝟙 arr.left) arrMor.right (by simp [arrowDiagonal])

/--
Canonical TwistedArrow morphism from the target arrow to the diagonal.
Domain component is `arrMor.left`, codomain component is identity.
-/
def twMorphToDiagonalRight :
    arrowToTwisted arr' ⟶ arrowDiagonalTwisted arrMor :=
  twHomMk' arrMor.left (𝟙 arr'.right) (by
    simp only [arrowToTwisted_arr, arrowDiagonalTwisted_arr, arrowDiagonal_eq]
    simp)

lemma twMorphToDiagonalLeft_domArr :
    twDomArr' (twMorphToDiagonalLeft arrMor) = 𝟙 arr.left := by
  simp only [twMorphToDiagonalLeft, twHomMk'_domArr]

lemma twMorphToDiagonalLeft_codArr :
    twCodArr' (twMorphToDiagonalLeft arrMor) = arrMor.right := by
  simp only [twMorphToDiagonalLeft, twHomMk'_codArr]

lemma twMorphToDiagonalRight_domArr :
    twDomArr' (twMorphToDiagonalRight arrMor) = arrMor.left := by
  simp only [twMorphToDiagonalRight, twHomMk'_domArr]

lemma twMorphToDiagonalRight_codArr :
    twCodArr' (twMorphToDiagonalRight arrMor) = 𝟙 arr'.right := by
  simp only [twMorphToDiagonalRight, twHomMk'_codArr]

end DiagonalConstruction

/-!
### Identity lemmas for diagonal construction

These lemmas show how the diagonal construction behaves on identity morphisms.
-/

/--
The diagonal for the identity Arrow morphism is the original arrow.
-/
lemma arrowDiagonal_id (arr : Arrow C) :
    arrowDiagonal (𝟙 arr) = arr.hom := by
  simp only [arrowDiagonal, Arrow.id_right]
  simp

set_option backward.isDefEq.respectTransparency false in
/--
The diagonal TwistedArrow for identity equals the original.
-/
lemma arrowDiagonalTwisted_id (arr : Arrow C) :
    arrowDiagonalTwisted (𝟙 arr) = arrowToTwisted arr := by
  simp only [arrowDiagonalTwisted, arrowToTwisted, arrowDiagonal_id]

/--
The twisted arrow morphism to diagonal left for identity is an identity
(cast via eqToHom).
-/
lemma twMorphToDiagonalLeft_id (arr : Arrow C) :
    twMorphToDiagonalLeft (𝟙 arr) =
    eqToHom (arrowDiagonalTwisted_id arr).symm := by
  apply twHom'_ext
  · simp only [twMorphToDiagonalLeft_domArr, twDomArr'_eqToHom,
      arrowToTwisted_dom, arrowDiagonalTwisted_dom, eqToHom_refl]
  · simp only [twMorphToDiagonalLeft_codArr, Arrow.id_right, twCodArr'_eqToHom,
      arrowToTwisted_cod, arrowDiagonalTwisted_cod, eqToHom_refl]

/--
The twisted arrow morphism to diagonal right for identity is an identity
(cast via eqToHom).
-/
lemma twMorphToDiagonalRight_id (arr : Arrow C) :
    twMorphToDiagonalRight (𝟙 arr) =
    eqToHom (arrowDiagonalTwisted_id arr).symm := by
  apply twHom'_ext
  · simp only [twMorphToDiagonalRight_domArr, Arrow.id_left, twDomArr'_eqToHom,
      arrowToTwisted_dom, arrowDiagonalTwisted_dom, eqToHom_refl]
  · simp only [twMorphToDiagonalRight_codArr, twCodArr'_eqToHom,
      arrowToTwisted_cod, arrowDiagonalTwisted_cod, eqToHom_refl]

/-!
### Composition lemmas for diagonal construction

These lemmas show how the diagonal construction behaves on composed morphisms.
-/

section DiagonalComposition

variable {arr₁ arr₂ arr₃ : Arrow C} (f : arr₁ ⟶ arr₂) (g : arr₂ ⟶ arr₃)

set_option backward.isDefEq.respectTransparency false in
/--
The diagonal of a composition decomposes via the right component.
-/
lemma arrowDiagonal_comp :
    arrowDiagonal (f ≫ g) = arrowDiagonal f ≫ g.right := by
  simp only [arrowDiagonal, Arrow.comp_right, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
/--
Alternative decomposition of diagonal composition via the left component.
-/
lemma arrowDiagonal_comp' :
    arrowDiagonal (f ≫ g) = f.left ≫ arrowDiagonal g := by
  simp only [arrowDiagonal, Arrow.comp_right]
  have h := f.w
  simp only [Functor.id_map] at h
  rw [← Category.assoc, h.symm, Category.assoc]

end DiagonalComposition

/-!
### Transport morphisms for composition

These morphisms transport from the diagonal of `g` or `h` to the diagonal of
`g ≫ h`, enabling the composition coherence condition.
-/

section DiagonalCompositionTransport

variable {arr₁ arr₂ arr₃ : Arrow C} (f : arr₁ ⟶ arr₂) (g : arr₂ ⟶ arr₃)

/--
Transport from the diagonal of `f` to the diagonal of `f ≫ g`.
Domain is identity, codomain is `g.right`.
-/
def twMorphDiagonalToComp :
    arrowDiagonalTwisted f ⟶ arrowDiagonalTwisted (f ≫ g) :=
  twHomMk' (𝟙 arr₁.left) g.right (by
    simp only [arrowDiagonalTwisted_arr, arrowDiagonal_comp]
    aesop_cat)

@[simp]
lemma twMorphDiagonalToComp_domArr :
    twDomArr' (twMorphDiagonalToComp f g) = 𝟙 arr₁.left := rfl

@[simp]
lemma twMorphDiagonalToComp_codArr :
    twCodArr' (twMorphDiagonalToComp f g) = g.right := rfl

/--
Transport from the diagonal of `g` to the diagonal of `f ≫ g`.
Domain is `f.left`, codomain is identity.
-/
def twMorphDiagonalFromComp :
    arrowDiagonalTwisted g ⟶ arrowDiagonalTwisted (f ≫ g) :=
  twHomMk' f.left (𝟙 arr₃.right) (by
    simp only [arrowDiagonalTwisted_arr, arrowDiagonal_comp']
    aesop_cat)

@[simp]
lemma twMorphDiagonalFromComp_domArr :
    twDomArr' (twMorphDiagonalFromComp f g) = f.left := rfl

@[simp]
lemma twMorphDiagonalFromComp_codArr :
    twCodArr' (twMorphDiagonalFromComp f g) = 𝟙 arr₃.right := rfl

end DiagonalCompositionTransport

/-!
### FunctorToConnGrothendieckData

Data specifying a functor `D ⥤ ConnectedGrothendieckAlt C F`. This is analogous
to `Grothendieck.FunctorToData` but uses the diagonal construction for fiber
morphisms.
-/

section FunctorToConnGrothendieck

universe u₃ v₃

variable {D : Type u₃} [Category.{v₃} D]
variable (F : TwistedArrow' C ⥤ Cat.{v, u})

/--
Fiber objects: for each `d : D`, an object in `F.obj (arrowToTwisted (arrFun.obj d))`.
-/
abbrev FunctorToConnGrothendieckFib (arrFun : D ⥤ Arrow C) :=
  (d : D) → (F.obj (arrowToTwisted (arrFun.obj d)))

variable {F}
variable {arrFun : D ⥤ Arrow C}
variable (fib : FunctorToConnGrothendieckFib F arrFun)

/--
The target TwistedArrow for a morphism in D via the diagonal construction.
-/
abbrev functorToConnGrothendieckTarget {d d' : D} (g : d ⟶ d') :
    TwistedArrow' C :=
  arrowDiagonalTwisted (arrFun.map g)

/--
Transport the source fiber element to the diagonal.
-/
abbrev functorToConnGrothendieckSrcTransport {d d' : D} (g : d ⟶ d') :
    (F.obj (arrowToTwisted (arrFun.obj d))) ⥤
    (F.obj (functorToConnGrothendieckTarget (arrFun := arrFun) g)) :=
  (F.map (twMorphToDiagonalLeft (arrFun.map g))).toFunctor

/--
Transport the target fiber element to the diagonal.
-/
abbrev functorToConnGrothendieckTgtTransport {d d' : D} (g : d ⟶ d') :
    (F.obj (arrowToTwisted (arrFun.obj d'))) ⥤
    (F.obj (functorToConnGrothendieckTarget (arrFun := arrFun) g)) :=
  (F.map (twMorphToDiagonalRight (arrFun.map g))).toFunctor

/--
Fiber morphisms via the diagonal: for each `g : d ⟶ d'`, a morphism in the
diagonal fiber from the transported source fiber to the transported target fiber.
-/
abbrev FunctorToConnGrothendieckHom :=
  {d d' : D} → (g : d ⟶ d') →
    (functorToConnGrothendieckSrcTransport (arrFun := arrFun) g).obj (fib d) ⟶
    (functorToConnGrothendieckTgtTransport (arrFun := arrFun) g).obj (fib d')

variable (hom : FunctorToConnGrothendieckHom fib)

/--
For identity morphisms, the diagonal target equals the original twisted arrow.
-/
lemma functorToConnGrothendieckTarget_id (d : D) :
    functorToConnGrothendieckTarget (arrFun := arrFun) (𝟙 d) =
    arrowToTwisted (arrFun.obj d) := by
  simp only [functorToConnGrothendieckTarget]
  simp [arrowDiagonalTwisted_id]

/--
The fiber category for the diagonal at identity.
-/
abbrev functorToConnGrothendieckDiagFib (d : D) :=
  F.obj (functorToConnGrothendieckTarget (arrFun := arrFun) (𝟙 d))

/--
The source fiber category equals the diagonal fiber category for identity.
-/
lemma functorToConnGrothendieckSrcFib_eq_diagFib (d : D) :
    F.obj (arrowToTwisted (arrFun.obj d)) =
    functorToConnGrothendieckDiagFib (F := F) (arrFun := arrFun) d := by
  simp only [functorToConnGrothendieckDiagFib, functorToConnGrothendieckTarget_id]

/--
Identity coherence: `hom (𝟙 d)` should be an identity (up to transport via eqToHom).
We state this as heterogeneous equality since the source and target live in
types that may differ syntactically but are propositionally equal.
-/
abbrev FunctorToConnGrothendieckHomId := (d : D) →
  HEq (hom (𝟙 d)) (𝟙 (fib d))

/--
The target for composition using raw Arrow composition (before applying Functor.map_comp).
-/
abbrev functorToConnGrothendieckCompTargetRaw {d d' d'' : D}
    (g : d ⟶ d') (h : d' ⟶ d'') : TwistedArrow' C :=
  arrowDiagonalTwisted (arrFun.map g ≫ arrFun.map h)

/--
The composition target equals the raw target via Functor.map_comp.
-/
lemma functorToConnGrothendieckCompTargetRaw_eq {d d' d'' : D}
    (g : d ⟶ d') (h : d' ⟶ d'') :
    functorToConnGrothendieckCompTargetRaw (arrFun := arrFun) g h =
    functorToConnGrothendieckTarget (arrFun := arrFun) (g ≫ h) := by
  simp only [functorToConnGrothendieckCompTargetRaw, functorToConnGrothendieckTarget,
    Functor.map_comp]

/--
Transport from diagonal of g to the raw composite diagonal.
-/
abbrev functorToConnGrothendieckTransportGToGHRaw {d d' d'' : D}
    (g : d ⟶ d') (h : d' ⟶ d'') :
    F.obj (functorToConnGrothendieckTarget (arrFun := arrFun) g) ⥤
    F.obj (functorToConnGrothendieckCompTargetRaw (arrFun := arrFun) g h) :=
  (F.map (twMorphDiagonalToComp (arrFun.map g) (arrFun.map h))).toFunctor

/--
Transport from diagonal of h to the raw composite diagonal.
-/
abbrev functorToConnGrothendieckTransportHToGHRaw {d d' d'' : D}
    (g : d ⟶ d') (h : d' ⟶ d'') :
    F.obj (functorToConnGrothendieckTarget (arrFun := arrFun) h) ⥤
    F.obj (functorToConnGrothendieckCompTargetRaw (arrFun := arrFun) g h) :=
  (F.map (twMorphDiagonalFromComp (arrFun.map g) (arrFun.map h))).toFunctor

/--
The two TwistedArrow morphism paths from `arrowToTwisted (arrFun.obj d')` to the
raw composite diagonal coincide.
-/
lemma functorToConnGrothendieckTwMorphCoherence {d d' d'' : D}
    (g : d ⟶ d') (h : d' ⟶ d'') :
    twMorphToDiagonalRight (arrFun.map g) ≫
      twMorphDiagonalToComp (arrFun.map g) (arrFun.map h) =
    twMorphToDiagonalLeft (arrFun.map h) ≫
      twMorphDiagonalFromComp (arrFun.map g) (arrFun.map h) := by
  apply twHom'_ext
  · simp only [twDomArr'_comp, twMorphToDiagonalRight_domArr, twMorphDiagonalToComp_domArr,
      twMorphToDiagonalLeft_domArr, twMorphDiagonalFromComp_domArr]
    simp_all
  · simp only [twCodArr'_comp, twMorphToDiagonalRight_codArr, twMorphDiagonalToComp_codArr,
      twMorphToDiagonalLeft_codArr, twMorphDiagonalFromComp_codArr]
    simp_all

/--
Coherence lemma: the two transport paths to the raw diagonal coincide at `fib d'`.
-/
lemma functorToConnGrothendieckTransportCoherence {d d' d'' : D}
    (g : d ⟶ d') (h : d' ⟶ d'') :
    (functorToConnGrothendieckTransportGToGHRaw (F := F) (arrFun := arrFun) g h).obj
      ((functorToConnGrothendieckTgtTransport (arrFun := arrFun) g).obj (fib d')) =
    (functorToConnGrothendieckTransportHToGHRaw (F := F) (arrFun := arrFun) g h).obj
      ((functorToConnGrothendieckSrcTransport (arrFun := arrFun) h).obj (fib d')) := by
  simp only [functorToConnGrothendieckTransportGToGHRaw,
    functorToConnGrothendieckTransportHToGHRaw, functorToConnGrothendieckTgtTransport,
    functorToConnGrothendieckSrcTransport]
  simp only [← Functor.comp_obj]
  have eq := functorToConnGrothendieckTwMorphCoherence (arrFun := arrFun) g h
  rw [show (F.map (twMorphToDiagonalRight (arrFun.map g))).toFunctor ⋙
        (F.map (twMorphDiagonalToComp (arrFun.map g) (arrFun.map h))).toFunctor =
      (F.map (twMorphToDiagonalRight (arrFun.map g) ≫
        twMorphDiagonalToComp (arrFun.map g) (arrFun.map h))).toFunctor by
      rw [← Cat.Hom.comp_toFunctor]; congr 1; exact (F.map_comp _ _).symm]
  rw [show (F.map (twMorphToDiagonalLeft (arrFun.map h))).toFunctor ⋙
        (F.map (twMorphDiagonalFromComp (arrFun.map g) (arrFun.map h))).toFunctor =
      (F.map (twMorphToDiagonalLeft (arrFun.map h) ≫
        twMorphDiagonalFromComp (arrFun.map g) (arrFun.map h))).toFunctor by
      rw [← Cat.Hom.comp_toFunctor]; congr 1; exact (F.map_comp _ _).symm]
  rw [eq]

/--
Data specifying a functor `D ⥤ ConnectedGrothendieckAlt C F`.

This is analogous to `Grothendieck.FunctorToData` but adapted for the connected
Grothendieck construction which uses the diagonal construction for fiber morphisms.
-/
structure FunctorToConnGrothendieckData where
  /-- The arrow functor from `D` to `Arrow C` -/
  arrFun : D ⥤ Arrow C
  /-- Fiber objects: for each `d : D`, an object in the fiber over the
      corresponding twisted arrow -/
  fib : FunctorToConnGrothendieckFib F arrFun
  /-- Fiber morphisms via the diagonal: for each `g : d ⟶ d'`, a morphism
      between transported fiber elements in the diagonal fiber -/
  hom : FunctorToConnGrothendieckHom fib
  /-- Identity coherence: `hom (𝟙 d) ≅ 𝟙 (fib d)` (heterogeneous equality) -/
  hom_id : (d : D) → HEq (hom (𝟙 d)) (𝟙 (fib d))
  /-- Composition coherence: `hom (g ≫ h)` equals transported composition -/
  hom_comp : {d d' d'' : D} → (g : d ⟶ d') → (h : d' ⟶ d'') →
    HEq (hom (g ≫ h))
      ((functorToConnGrothendieckTransportGToGHRaw (F := F) (arrFun := arrFun) g h).map
          (hom g) ≫
        eqToHom (functorToConnGrothendieckTransportCoherence fib g h) ≫
        (functorToConnGrothendieckTransportHToGHRaw (F := F) (arrFun := arrFun) g h).map
          (hom h))

/-!
### Object Construction

Given `FunctorToConnGrothendieckData`, we construct the object mapping for
the functor `D ⥤ ConnectedGrothendieckAlt C F`.
-/

/--
The Under object for a given arrow.
For `arr : Arrow C`, the Under object representing `arr.hom : arr.left ⟶ arr.right`.
-/
abbrev arrowToUnder (arr : Arrow C) : Under arr.left :=
  Under.mk arr.hom

variable (F) in
/--
Type equality: the fiber category over `arrowToUnder arr` equals the fiber category
at `arrowToTwisted arr`.
-/
lemma arrowToUnder_fiber_eq (arr : Arrow C) :
    (restrictToDomainFiber C F arr.left).obj (arrowToUnder arr) =
    F.obj (arrowToTwisted arr) := by
  simp only [arrowToUnder, restrictToDomainFiber, Functor.comp_obj,
    underToTwistedArrow, arrowToTwisted]
  rfl

variable (F) in
/--
Construct an inner fiber object from an arrow and a fiber element.
-/
def functorToConnGrothendieckInnerFiber (arr : Arrow C)
    (e : F.obj (arrowToTwisted arr)) :
    innerFiberAlt C F arr.left :=
  ⟨arrowToUnder arr,
   (eqToHom (arrowToUnder_fiber_eq F arr).symm).toFunctor.obj e⟩

variable (F) in
/--
Construct an object of `ConnectedGrothendieckAlt` from an arrow and fiber element.
-/
def functorToConnGrothendieckObj (arr : Arrow C)
    (e : F.obj (arrowToTwisted arr)) :
    ConnectedGrothendieckAlt C F :=
  ⟨arr.left, functorToConnGrothendieckInnerFiber F arr e⟩

variable (data : @FunctorToConnGrothendieckData C _ D _ F)

/--
The object mapping for `functorToConnGrothendieck`.
-/
abbrev functorToConnGrothendieckObjMap (d : D) :
    ConnectedGrothendieckAlt C F :=
  functorToConnGrothendieckObj F (data.arrFun.obj d) (data.fib d)

@[simp]
lemma functorToConnGrothendieckObjMap_base (d : D) :
    (functorToConnGrothendieckObjMap data d).base = (data.arrFun.obj d).left :=
  rfl

@[simp]
lemma functorToConnGrothendieckObjMap_fiber_base (d : D) :
    (functorToConnGrothendieckObjMap data d).fiber.base =
    arrowToUnder (data.arrFun.obj d) :=
  rfl

@[simp]
lemma functorToConnGrothendieckObjMap_fiber_fiber (d : D) :
    (functorToConnGrothendieckObjMap data d).fiber.fiber =
    (eqToHom (arrowToUnder_fiber_eq F (data.arrFun.obj d))).toFunctor.obj (data.fib d) :=
  rfl

/-!
### Morphism Construction

Given `g : d ⟶ d'` in `D`:

1. Base morphism: `(data.arrFun.map g).left` gives the domain direction
2. Fiber morphism: Uses `data.hom g` to construct the inner Grothendieck morphism

The fiber morphism construction requires transporting through several equality
steps to match the types expected by `GrothendieckContra'.Hom`.
-/

/--
Base component of the morphism for `functorToConnGrothendieck`.
-/
abbrev functorToConnGrothendieckMapBase {d d' : D} (g : d ⟶ d') :
    (data.arrFun.obj d).left ⟶ (data.arrFun.obj d').left :=
  (data.arrFun.map g).left

set_option backward.isDefEq.respectTransparency false in
/--
Helper lemma for Under object equality.
Two Under objects are equal if they have the same right and hom components.
-/
lemma Under.obj_eq' {X : C} (A B : Under X)
    (h_right : A.right = B.right)
    (h_hom : A.hom ≫ eqToHom h_right = B.hom) : A = B := by
  rcases A with ⟨⟨⟨⟩⟩, rA, homA⟩
  rcases B with ⟨⟨⟨⟩⟩, rB, homB⟩
  simp only at h_right h_hom
  subst h_right
  simp only [eqToHom_refl, Category.comp_id] at h_hom
  subst h_hom
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
Type equality for the source object's fiber base after transport.

When we transport `target.fiber` by `mapBase g`, the result's base is related to
the source by the Arrow morphism structure.
-/
lemma functorToConnGrothendieckTransportBase {d d' : D} (g : d ⟶ d') :
    (Under.map (data.arrFun.map g).left).obj (arrowToUnder (data.arrFun.obj d')) =
    Under.mk (arrowDiagonal (data.arrFun.map g)) := by
  simp only [arrowToUnder, arrowDiagonal]
  fapply Under.obj_eq'
  · rfl
  · simp only [Under.map_obj_hom, Under.mk_hom, eqToHom_refl, Category.comp_id]
    exact (data.arrFun.map g).w

/--
The inner Under morphism for the inner Grothendieck morphism.

This maps from `arrowToUnder (arrFun.obj d)` to `Under.mk (arrowDiagonal ...)`.
The `right` component is the codomain direction of the Arrow morphism.
-/
def functorToConnGrothendieckInnerUnderMorph {d d' : D} (g : d ⟶ d') :
    arrowToUnder (data.arrFun.obj d) ⟶ Under.mk (arrowDiagonal (data.arrFun.map g)) :=
  Under.homMk (data.arrFun.map g).right rfl

/--
The twisted arrow morphism corresponding to the inner Under morphism.

This maps the Under morphism to `twMorphToDiagonalLeft`, which goes from the source
arrow to the diagonal (with identity domain component and `arrMor.right` codomain component).
-/
lemma functorToConnGrothendieckInnerUnderTwMorph {d d' : D} (g : d ⟶ d') :
    (underToTwistedArrow C (data.arrFun.obj d).left).map
      (functorToConnGrothendieckInnerUnderMorph data g) =
    twMorphToDiagonalLeft (data.arrFun.map g) := by
  apply twHom'_ext
  · simp only [underToTwistedArrow, twHomMk'_domArr, twMorphToDiagonalLeft]
    rfl
  · simp only [underToTwistedArrow, twHomMk'_codArr, twMorphToDiagonalLeft,
      functorToConnGrothendieckInnerUnderMorph, Under.homMk_right]
    rfl

/--
The category equality for the diagonal fiber type.
-/
lemma functorToConnGrothendieckDiagonalFiberEq {d d' : D} (g : d ⟶ d') :
    (restrictToDomainFiber C F (data.arrFun.obj d).left).obj
      (Under.mk (arrowDiagonal (data.arrFun.map g))) =
    F.obj (arrowDiagonalTwisted (data.arrFun.map g)) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
The functor from source arrow category to diagonal category via the restrict functor.
The restrict functor map equals the source transport functor.
-/
lemma functorToConnGrothendieckMapEq {d d' : D} (g : d ⟶ d') :
    ((restrictToDomainFiber C F (data.arrFun.obj d).left).map
      (functorToConnGrothendieckInnerUnderMorph data g)).toFunctor =
    functorToConnGrothendieckSrcTransport (arrFun := data.arrFun) g := by
  unfold Cat.Hom.toFunctor
  simp only [restrictToDomainFiber, Functor.comp_map, functorToConnGrothendieckSrcTransport,
    functorToConnGrothendieckInnerUnderTwMorph]

set_option backward.isDefEq.respectTransparency false in
/--
The source object's fiber for the inner Grothendieck morphism equals the
SrcTransport applied to the original fiber (with the arrowToUnder_fiber_eq transport).
-/
lemma functorToConnGrothendieckInnerFiberSrcEq {d d' : D} (g : d ⟶ d') :
    ((restrictToDomainFiber C F (data.arrFun.obj d).left).map
      (functorToConnGrothendieckInnerUnderMorph data g)).toFunctor.obj
    ((eqToHom (arrowToUnder_fiber_eq F (data.arrFun.obj d)).symm).toFunctor.obj (data.fib d)) =
    (eqToHom (functorToConnGrothendieckDiagonalFiberEq data g).symm).toFunctor.obj
      ((functorToConnGrothendieckSrcTransport (arrFun := data.arrFun) g).obj (data.fib d)) := by
  unfold Cat.Hom.toFunctor
  simp only [functorToConnGrothendieckMapEq, functorToConnGrothendieckDiagonalFiberEq,
    eqToHom_refl, Cat.Hom.id_toFunctor, Functor.id_obj]

/--
The Under to TwistedArrow transformation on arrowToUnder gives arrowToTwisted.
This is definitional equality (both expand to `twObjMk' arr.hom`).
-/
lemma underToTwistedArrow_arrowToUnder (arr : Arrow C) :
    (underToTwistedArrow C arr.left).obj (arrowToUnder arr) = arrowToTwisted arr := rfl

/--
The twisted arrow target of domain fiber transport equals the diagonal twisted arrow.

Using `functorToConnGrothendieckTransportBase`, the Under object
`(Under.map arrMor.left).obj (arrowToUnder arr')` equals `Under.mk (arrowDiagonal arrMor)`.
Applying `underToTwistedArrow` yields the diagonal twisted arrow.
-/
lemma functorToConnGrothendieckDomainTransportTargetTw {d d' : D} (g : d ⟶ d') :
    (underToTwistedArrow C (data.arrFun.obj d).left).obj
      ((Under.map (data.arrFun.map g).left).obj (arrowToUnder (data.arrFun.obj d'))) =
    arrowDiagonalTwisted (data.arrFun.map g) := by
  simp only [underToTwistedArrow, Under.map_obj_hom, arrowToUnder, Under.mk_hom,
    arrowDiagonalTwisted, arrowDiagonal]
  congr 1
  exact (data.arrFun.map g).w

/--
For identity, the domain transport target twisted arrow equals the original.
-/
lemma functorToConnGrothendieckDomainTransportTargetTw_id (d : D) :
    (underToTwistedArrow C (data.arrFun.obj d).left).obj
      ((Under.map (data.arrFun.map (𝟙 d)).left).obj (arrowToUnder (data.arrFun.obj d))) =
    arrowToTwisted (data.arrFun.obj d) := by
  rw [functorToConnGrothendieckDomainTransportTargetTw]
  simp only [CategoryTheory.Functor.map_id, arrowDiagonalTwisted_id]

set_option backward.isDefEq.respectTransparency false in
/--
The domain fiber transport twisted arrow morphism equals `twMorphToDiagonalRight`
(after rewriting the target via the equality lemma; the source is definitionally equal).
-/
lemma functorToConnGrothendieckDomainTransportTwEq {d d' : D} (g : d ⟶ d') :
    domainFiberTransportTwMorph C (data.arrFun.map g).left
      (arrowToUnder (data.arrFun.obj d')) =
    twMorphToDiagonalRight (data.arrFun.map g) ≫
    eqToHom (functorToConnGrothendieckDomainTransportTargetTw data g).symm := by
  apply twHom'_ext
  · simp only [domainFiberTransportTwMorph, twHomMk'_domArr, twDomArr'_comp,
      twDomArr'_eqToHom, twMorphToDiagonalRight, twHomMk'_domArr]
    simp only [underToTwistedArrow, Under.map_obj_hom, arrowToUnder, Under.mk_hom,
      arrowDiagonalTwisted, arrowDiagonal, twObjMk'_dom, Functor.fromPUnit]
    convert (Category.id_comp _).symm using 2
  · simp only [domainFiberTransportTwMorph, twHomMk'_codArr, twCodArr'_comp,
      twCodArr'_eqToHom, twMorphToDiagonalRight, twHomMk'_codArr]
    simp only [underToTwistedArrow, Under.map_obj_hom, arrowToUnder, Under.mk_hom, Under.mk_right,
      arrowDiagonalTwisted, arrowDiagonal, twObjMk'_cod, Functor.id_obj]
    convert (Category.comp_id _).symm using 2

set_option backward.isDefEq.respectTransparency false in
/--
The domain fiber transport functor equals the target transport functor
(up to the appropriate eqToHom conversion from the target equality).
-/
lemma functorToConnGrothendieckDomainTransportFunctorEq {d d' : D} (g : d ⟶ d') :
    domainFiberTransport C F (data.arrFun.map g).left (arrowToUnder (data.arrFun.obj d')) =
    functorToConnGrothendieckTgtTransport (arrFun := data.arrFun) g ⋙
    (eqToHom (congrArg F.obj
      (functorToConnGrothendieckDomainTransportTargetTw data g)).symm).toFunctor := by
  simp only [domainFiberTransport, functorToConnGrothendieckTgtTransport]
  rw [functorToConnGrothendieckDomainTransportTwEq]
  simp only [Functor.map_comp, eqToHom_map]
  rfl

/-!
### Relating Transport Constructions

The transport functors `twMorphToDiagonalLeft/Right` used in `FunctorToConnGrothendieckData`
are the same as `connGrothendieckTwMorphCod/Dom` used in `ConnGrothendieckHom`, when applied
to arrows from `arrowToTwisted`.
-/

variable {arr arr' : Arrow C} (arrMor : arr ⟶ arr')

set_option backward.isDefEq.respectTransparency false in
/--
The diagonal codomain coincides with the diagonal twisted arrow.
-/
lemma connGrothendieckDiagCod_eq_arrowDiagonalTwisted :
    connGrothendieckDiagCod C (arrowToTwisted arr) arrMor.right =
    arrowDiagonalTwisted arrMor := by
  simp only [connGrothendieckDiagCod, arrowToTwisted, twObjMk'_arr, twObjMk'_cod,
    arrowDiagonalTwisted, arrowDiagonal]

/--
The diagonal domain coincides with the diagonal twisted arrow.
-/
lemma connGrothendieckDiagDom_eq_arrowDiagonalTwisted :
    connGrothendieckDiagDom C (arrowToTwisted arr') arrMor.left =
    arrowDiagonalTwisted arrMor := by
  simp only [connGrothendieckDiagDom, arrowToTwisted, twObjMk'_arr, twObjMk'_dom,
    arrowDiagonalTwisted, arrowDiagonal]
  congr 1
  exact arrMor.w

/-!
### ConnGrothendieckObj Construction

We construct `ConnGrothendieckObj` from Arrows and fibers to use the existing
morphism conversion machinery.
-/

/--
Convert an Arrow and fiber element to a `ConnGrothendieckObj`.
-/
def arrowToConnGrothendieckObj (arr : Arrow C)
    (e : F.obj (arrowToTwisted arr)) : ConnGrothendieckObj C F :=
  ⟨arrowToTwisted arr, e⟩

/--
The source `ConnGrothendieckObj` for `data.arrFun.obj d` and `data.fib d`.
-/
abbrev functorToConnGrothendieckSrcObj (d : D) : ConnGrothendieckObj C F :=
  arrowToConnGrothendieckObj (data.arrFun.obj d) (data.fib d)

/--
The target `ConnGrothendieckObj` for `data.arrFun.obj d'` and `data.fib d'`.
-/
abbrev functorToConnGrothendieckTgtObj (d' : D) : ConnGrothendieckObj C F :=
  arrowToConnGrothendieckObj (data.arrFun.obj d') (data.fib d')

/--
The `connGrothendieckObjToAltObj` applied to source equals `functorToConnGrothendieckObjMap`.
-/
lemma functorToConnGrothendieckSrcObj_toAlt (d : D) :
    connGrothendieckObjToAltObj C F (functorToConnGrothendieckSrcObj data d) =
    functorToConnGrothendieckObjMap data d := by
  simp only [arrowToConnGrothendieckObj,
    connGrothendieckObjToAltObj, functorToConnGrothendieckObjMap, functorToConnGrothendieckObj,
    functorToConnGrothendieckInnerFiber, arrowToTwisted, arrowToUnder]
  congr 1

/--
The base morphism in `C` for the `GrothendieckContra'` morphism construction.
-/
abbrev functorToConnGrothendieckAltBase {d d' : D} (g : d ⟶ d') :
    (functorToConnGrothendieckObjMap data d).base ⟶
    (functorToConnGrothendieckObjMap data d').base :=
  (data.arrFun.map g).left

/--
The target fiber transported to source domain category.
-/
abbrev functorToConnGrothendieckTransportedTgt {d d' : D} (g : d ⟶ d') :
    (domainFiberFunctor C F).obj (functorToConnGrothendieckObjMap data d).base :=
  ((domainFiberFunctor C F).map (functorToConnGrothendieckAltBase data g)).toFunctor.obj
    (functorToConnGrothendieckObjMap data d').fiber

set_option backward.isDefEq.respectTransparency false in
/--
The hom of the transported Under target equals the diagonal.
-/
lemma functorToConnGrothendieckInnerBaseTgt_hom_eq {d d' : D} (g : d ⟶ d') :
    ((Under.map (data.arrFun.map g).left).obj (arrowToUnder (data.arrFun.obj d'))).hom =
    arrowDiagonal (data.arrFun.map g) := by
  simp only [Under.map_obj_hom, arrowToUnder, Under.mk_hom, arrowDiagonal_eq]

/--
The base component of the inner Grothendieck morphism.
This is an Under morphism from `arrowToUnder (data.arrFun.obj d)` to the
transported target Under object.
-/
def functorToConnGrothendieckInnerBase {d d' : D} (g : d ⟶ d') :
    arrowToUnder (data.arrFun.obj d) ⟶
    (Under.map (data.arrFun.map g).left).obj (arrowToUnder (data.arrFun.obj d')) :=
  Under.homMk (data.arrFun.map g).right (by
    simp only [Under.map_obj_hom, arrowToUnder, Under.mk_hom]
    exact (data.arrFun.map g).w.symm)

/--
The target of innerBase composition via Under.map equals the direct target.
-/
lemma functorToConnGrothendieckInnerBase_comp_tgt_eq {d d' d'' : D}
    (g : d ⟶ d') (h : d' ⟶ d'') :
    (Under.map (data.arrFun.map g).left).obj
      ((Under.map (data.arrFun.map h).left).obj (arrowToUnder (data.arrFun.obj d''))) =
    (Under.map (data.arrFun.map (g ≫ h)).left).obj (arrowToUnder (data.arrFun.obj d'')) := by
  simp only [Functor.map_comp, Arrow.comp_left]
  exact congrArg (·.obj (arrowToUnder (data.arrFun.obj d'')))
    (Under.mapComp_eq (data.arrFun.map g).left (data.arrFun.map h).left).symm

set_option backward.isDefEq.respectTransparency false in
/--
The composition property for `functorToConnGrothendieckInnerBase`. The innerBase of a
composition equals the composition of innerBases, up to eqToHom for Under.map.
-/
lemma functorToConnGrothendieckInnerBase_comp {d d' d'' : D} (g : d ⟶ d') (h : d' ⟶ d'') :
    functorToConnGrothendieckInnerBase data (g ≫ h) =
    functorToConnGrothendieckInnerBase data g ≫
      (Under.map (data.arrFun.map g).left).map (functorToConnGrothendieckInnerBase data h) ≫
      eqToHom (functorToConnGrothendieckInnerBase_comp_tgt_eq data g h) := by
  apply Under.UnderMorphism.ext
  rw [Comma.comp_right, Comma.comp_right]
  rw [Under.eqToHom_right, Under.map_map_right]
  simp only [functorToConnGrothendieckInnerBase, Under.homMk_right, Functor.map_comp,
    Arrow.comp_right, eqToHom_refl, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
/--
The twisted arrow morphism from applying underToTwistedArrow to innerBase equals
twMorphToDiagonalLeft followed by an eqToHom for the target.
-/
lemma functorToConnGrothendieckInnerBaseTwMorph {d d' : D} (g : d ⟶ d') :
    (underToTwistedArrow C (data.arrFun.obj d).left).map (functorToConnGrothendieckInnerBase data g)
    = twMorphToDiagonalLeft (data.arrFun.map g) ≫
      eqToHom (functorToConnGrothendieckDomainTransportTargetTw data g).symm := by
  apply twHom'_ext
  · simp only [underToTwistedArrow, twHomMk'_domArr, functorToConnGrothendieckInnerBase,
      twDomArr'_comp, twDomArr'_eqToHom, twMorphToDiagonalLeft, id_eq, eqToHom_refl,
      Category.id_comp]
  · simp only [underToTwistedArrow, twHomMk'_codArr, functorToConnGrothendieckInnerBase,
      Under.homMk_right, twCodArr'_comp, twCodArr'_eqToHom, twMorphToDiagonalLeft, id_eq,
      eqToHom_refl, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
/--
The restrictToDomainFiber map of innerBase equals SrcTransport followed by eqToHom.
-/
lemma functorToConnGrothendieckInnerBaseMapEq {d d' : D} (g : d ⟶ d') :
    ((restrictToDomainFiber C F (data.arrFun.obj d).left).map
      (functorToConnGrothendieckInnerBase data g)).toFunctor =
    functorToConnGrothendieckSrcTransport (arrFun := data.arrFun) g ⋙
    (eqToHom (congrArg F.obj
      (functorToConnGrothendieckDomainTransportTargetTw data g)).symm).toFunctor := by
  unfold Cat.Hom.toFunctor
  simp only [restrictToDomainFiber, Functor.comp_map]
  rw [functorToConnGrothendieckInnerBaseTwMorph]
  simp only [Functor.map_comp, eqToHom_map, functorToConnGrothendieckSrcTransport]
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
The fiber morphism for the `GrothendieckContra'` morphism construction.
This is a morphism in the inner Grothendieck category from the source fiber to
the transported target fiber.
-/
def functorToConnGrothendieckAltFiber {d d' : D} (g : d ⟶ d') :
    (functorToConnGrothendieckObjMap data d).fiber ⟶
    functorToConnGrothendieckTransportedTgt data g := by
  simp only [functorToConnGrothendieckTransportedTgt, domainFiberFunctor_map,
    innerFiberAltTransition]
  refine ⟨functorToConnGrothendieckInnerBase data g, ?_⟩
  simp only [restrictToDomainFiber, Functor.comp_map,
    functorToConnGrothendieckObjMap_base]
  rw [functorToConnGrothendieckInnerBaseTwMorph]
  unfold Cat.Hom.toFunctor Functor.toCatHom
  simp only [Functor.map_comp, Functor.comp_obj, Cat.Hom.comp_toFunctor,
    functorToConnGrothendieckAltBase, functorToConnGrothendieckObjMap_fiber_base,
    eqToHom_map, functorToConnGrothendieckObjMap_fiber_fiber, innerFiberAltTransitionObj]
  unfold domainFiberTransport
  rw [functorToConnGrothendieckDomainTransportTwEq]
  simp only [Functor.map_comp, eqToHom_map]
  exact (eqToHom (congrArg F.obj
    (functorToConnGrothendieckDomainTransportTargetTw data g).symm)).toFunctor.map (data.hom g)

/--
The base component of `functorToConnGrothendieckAltFiber` is `functorToConnGrothendieckInnerBase`.
-/
@[simp]
lemma functorToConnGrothendieckAltFiber_base {d d' : D} (g : d ⟶ d') :
    (functorToConnGrothendieckAltFiber data g).base =
    functorToConnGrothendieckInnerBase data g := rfl

set_option backward.isDefEq.respectTransparency false in
/--
The fiber of `functorToConnGrothendieckAltFiber` is HEq to `data.hom`.
This follows because the fiber is `(eqToHom ...).map (data.hom g)`.
-/
lemma functorToConnGrothendieckAltFiber_fiber_heq {d d' : D} (g : d ⟶ d') :
    (functorToConnGrothendieckAltFiber data g).fiber ≍ data.hom g := by
  simp only [functorToConnGrothendieckAltFiber]
  apply HEq.trans (cast_heq _ _)
  apply HEq.trans (cast_heq _ _)
  apply HEq.trans (cast_heq _ _)
  apply HEq.trans (cast_heq _ _)
  exact Cat.eqToHom_map_heq _ _

/--
The morphism map for `functorToConnGrothendieck`.
-/
def functorToConnGrothendieckMapHom {d d' : D} (g : d ⟶ d') :
    functorToConnGrothendieckObjMap data d ⟶
    functorToConnGrothendieckObjMap data d' :=
  ⟨functorToConnGrothendieckAltBase data g, functorToConnGrothendieckAltFiber data g⟩

/-!
### Identity lemmas (factored step-by-step)

These lemmas establish what happens to each component when we apply the identity
morphism `𝟙 d` in `D`.
-/

/--
Step 1: The base component of the identity map is the identity.
-/
lemma functorToConnGrothendieckAltBase_id (d : D) :
    functorToConnGrothendieckAltBase data (𝟙 d) = 𝟙 (data.arrFun.obj d).left := by
  simp only [functorToConnGrothendieckAltBase, CategoryTheory.Functor.map_id, Arrow.id_left]

/--
Step 2: The transported target when g = 𝟙 d equals the source fiber.
-/
lemma functorToConnGrothendieckTransportedTgt_id (d : D) :
    functorToConnGrothendieckTransportedTgt data (𝟙 d) =
    (functorToConnGrothendieckObjMap data d).fiber := by
  simp only [functorToConnGrothendieckTransportedTgt, functorToConnGrothendieckAltBase_id,
    domainFiberFunctor_map, innerFiberAltTransition]
  exact innerFiberAltTransitionObj_id C F _

/--
Step 3: The diagonal twisted arrow for the identity Arrow morphism.
-/
lemma functorToConnGrothendieck_arrowDiagonalTwisted_id (d : D) :
    arrowDiagonalTwisted (data.arrFun.map (𝟙 d)) = arrowToTwisted (data.arrFun.obj d) := by
  simp only [CategoryTheory.Functor.map_id, arrowDiagonalTwisted_id]

/--
Step 4: The transported target Under object when g = 𝟙 d.
-/
lemma functorToConnGrothendieckInnerBase_tgt_eq_id (d : D) :
    (Under.map (data.arrFun.map (𝟙 d)).left).obj (arrowToUnder (data.arrFun.obj d)) =
    arrowToUnder (data.arrFun.obj d) := by
  simp only [CategoryTheory.Functor.map_id, Arrow.id_left]
  have h := Under.mapId_eq (data.arrFun.obj d).left
  exact congrFun (congrArg Functor.obj h) (arrowToUnder (data.arrFun.obj d))

/--
Step 5: The inner base morphism when g = 𝟙 d equals eqToHom of a refl equality.
-/
lemma functorToConnGrothendieckInnerBase_id (d : D) :
    functorToConnGrothendieckInnerBase data (𝟙 d) =
    eqToHom (functorToConnGrothendieckInnerBase_tgt_eq_id data d).symm := by
  simp only [functorToConnGrothendieckInnerBase, CategoryTheory.Functor.map_id, Arrow.id_right]
  apply Under.UnderMorphism.ext
  simp only [Under.eqToHom_right, Under.homMk_right]
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
Step 6: The base component of `functorToConnGrothendieckAltFiber data (𝟙 d)` equals
an eqToHom.
-/
lemma functorToConnGrothendieckAltFiber_id_base (d : D) :
    (functorToConnGrothendieckAltFiber data (𝟙 d)).base =
    eqToHom (functorToConnGrothendieckInnerBase_tgt_eq_id data d).symm := by
  simp only [functorToConnGrothendieckAltFiber]
  exact functorToConnGrothendieckInnerBase_id data d

/--
Step 7: The fiber component of `functorToConnGrothendieckAltFiber data (𝟙 d)` is HEq to
an identity morphism.
-/
lemma functorToConnGrothendieckAltFiber_id_fiber_heq (d : D) :
    (functorToConnGrothendieckAltFiber data (𝟙 d)).fiber ≍
    𝟙 ((functorToConnGrothendieckObjMap data d).fiber.fiber) := by
  simp only [functorToConnGrothendieckAltFiber]
  apply HEq.trans (cast_heq _ _)
  apply HEq.trans (cast_heq _ _)
  apply HEq.trans (cast_heq _ _)
  apply HEq.trans (cast_heq _ _)
  apply HEq.trans (Cat.eqToHom_map_heq _ _)
  exact data.hom_id d

/--
Step 8: The functor `(restrictToDomainFiber C F a).map (eqToHom h).base` equals
`eqToHom` of an appropriate equality.
-/
lemma restrictToDomainFiber_map_grothendieck_eqToHom_base (a : C)
    {x y : Grothendieck (restrictToDomainFiber C F a)} (h : x = y) :
    (restrictToDomainFiber C F a).map (eqToHom h).base =
    eqToHom (congrArg (restrictToDomainFiber C F a).obj (congrArg Grothendieck.base h)) := by
  rw [Grothendieck.eqToHom_base', eqToHom_map]

/--
For any proof `h : X = Y`, we have `eqToHom h ≍ 𝟙 X` as a heterogeneous equality.
-/
lemma eqToHom_heq_id {E : Type*} [Category E] {X Y : E} (h : X = Y) : eqToHom h ≍ 𝟙 X := by
  cases h
  rfl

/--
Symmetric version: for any proof `h : X = Y`, we have `eqToHom h ≍ 𝟙 Y`.
-/
lemma eqToHom_heq_id' {E : Type*} [Category E] {X Y : E} (h : X = Y) : eqToHom h ≍ 𝟙 Y := by
  cases h
  rfl

/--
For Grothendieck categories, the fiber of eqToHom is HEq to identity.
-/
lemma Grothendieck.eqToHom_fiber_heq_id {C : Type*} [Category C] {P : C ⥤ Cat}
    {X Y : Grothendieck P} (h : X = Y) :
    (eqToHom h).fiber ≍ 𝟙 X.fiber := by
  subst h
  -- After subst, goal is (eqToHom rfl).fiber ≍ 𝟙 X.fiber
  -- eqToHom rfl = 𝟙 X (definitionally)
  simp only [eqToHom_refl]
  -- Now goal is Hom.fiber (𝟙 X) ≍ 𝟙 X.fiber
  rw [CategoryTheory.Grothendieck.id_fiber]
  -- Now goal is eqToHom (...) ≍ 𝟙 X.fiber
  exact eqToHom_heq_id' (by simp)

/--
If `f ≍ 𝟙 W` for some object `W`, and the composition `f ≫ g` is well-typed, then
`f ≫ g ≍ g` (where `g` on the RHS is appropriately typed via transport).

This handles the case where `f : X ⟶ Y` with `X = W` and `Y = W` (propositionally), so
`f` is essentially an identity morphism up to transport.
-/
lemma comp_heq_of_heq_id {E : Type*} [Category E]
    {X Y Z W : E} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hXW : X = W) (hYW : Y = W) (hf : f ≍ 𝟙 W) :
    (f ≫ g) ≍ g := by
  cases hXW
  cases hYW
  have hfeq : f = 𝟙 X := eq_of_heq hf
  rw [hfeq, Category.id_comp]

/--
Variant that derives domain/codomain equalities from HEq to identity on codomain.
-/
lemma comp_heq_of_heq_id' {E : Type*} [Category E]
    {X Y Z W : E} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hXY : X = Y) (hYW : Y = W) (hf : f ≍ 𝟙 W) :
    (f ≫ g) ≍ g := by
  subst hXY hYW
  have hfeq : f = 𝟙 X := eq_of_heq hf
  rw [hfeq, Category.id_comp]

/--
The transported target for the identity equals the fiber image under identity.
-/
lemma functorToConnGrothendieck_transportedTgt_id_eq (d : D) :
    functorToConnGrothendieckTransportedTgt data (𝟙 d) =
    ((domainFiberFunctor C F).map
      (GrothendieckContra'.id (functorToConnGrothendieckObjMap data d)).base).toFunctor.obj
      (functorToConnGrothendieckObjMap data d).fiber := by
  unfold Cat.Hom.toFunctor
  simp only [functorToConnGrothendieckTransportedTgt, functorToConnGrothendieckAltBase,
    CategoryTheory.Functor.map_id, Arrow.id_left, GrothendieckContra'.id,
    functorToConnGrothendieckObjMap_base]

set_option backward.isDefEq.respectTransparency false in
/--
The transported target for composition equals the fiber image under composition.
-/
lemma functorToConnGrothendieck_transportedTgt_comp_eq {d d' d'' : D}
    (g : d ⟶ d') (h : d' ⟶ d'') :
    functorToConnGrothendieckTransportedTgt data (g ≫ h) =
    ((domainFiberFunctor C F).map
      (GrothendieckContra'.comp
        ⟨functorToConnGrothendieckAltBase data g, functorToConnGrothendieckAltFiber data g⟩
        ⟨functorToConnGrothendieckAltBase data h, functorToConnGrothendieckAltFiber data h⟩
      ).base).toFunctor.obj (functorToConnGrothendieckObjMap data d'').fiber := by
  unfold Cat.Hom.toFunctor
  simp only [functorToConnGrothendieckTransportedTgt, functorToConnGrothendieckAltBase,
    Functor.map_comp, Arrow.comp_left, GrothendieckContra'.comp_base]

set_option backward.isDefEq.respectTransparency false in
/--
The base component of the map_id fiber case: the base of the LHS equals the base of the RHS.
-/
lemma functorToConnGrothendieck_map_id_fiber_base (d : D) :
    (functorToConnGrothendieckAltFiber data (𝟙 d) ≫
      eqToHom (functorToConnGrothendieck_transportedTgt_id_eq data d)).base =
    ((GrothendieckContra'.id (functorToConnGrothendieckObjMap data d)).fiber).base := by
  rw [GrothendieckContra'.id_fiber_val]
  rw [Grothendieck.comp_base]
  rw [Grothendieck.base_eqToHom]
  rw [functorToConnGrothendieckAltFiber_id_base]
  rw [Grothendieck.base_eqToHom]
  rw [eqToHom_trans]

set_option backward.isDefEq.respectTransparency false in
/--
The fiber component of the map_id fiber case (Grothendieck.ext form).
-/
lemma functorToConnGrothendieck_map_id_fiber_fiber (d : D) :
    eqToHom (by rw [functorToConnGrothendieck_map_id_fiber_base data d]) ≫
      (functorToConnGrothendieckAltFiber data (𝟙 d) ≫
        eqToHom (functorToConnGrothendieck_transportedTgt_id_eq data d)).fiber =
    ((GrothendieckContra'.id (functorToConnGrothendieckObjMap data d)).fiber).fiber := by
  simp only [GrothendieckContra'.id_fiber_val]
  rw [Grothendieck.comp_fiber]
  simp only [eqToHom_trans_assoc]
  have hIdFiber := functorToConnGrothendieckAltFiber_id_fiber_heq data d
  apply eq_of_heq
  -- Remove the leading eqToHom
  apply HEq.trans (eqToHom_comp_heq _ _)
  -- Now goal is (F.map (eqToHom).base).map fiber ≫ (eqToHom).fiber ≍ (eqToHom).fiber
  -- Use the fact that F.map (eqToHom).base = eqToHom
  have hFunEq := restrictToDomainFiber_map_grothendieck_eqToHom_base
    (functorToConnGrothendieckObjMap data d).base
    (functorToConnGrothendieck_transportedTgt_id_eq data d)
  -- Use Cat.functor_map_heq_of_eq_eqToHom to show G.map fiber ≍ fiber
  -- Convert hFunEq to use .toFunctor on both sides
  have hFunEq' := congrArg Cat.Hom.toFunctor hFunEq
  have hMapFiber := Cat.functor_map_heq_of_eq_eqToHom _ _ hFunEq'
    (functorToConnGrothendieckAltFiber data (𝟙 d)).fiber
  -- Both G.map fiber and fiber are HEq to 𝟙
  have hGmapId : ((restrictToDomainFiber C F
      (functorToConnGrothendieckObjMap data d).base).map
      (eqToHom (functorToConnGrothendieck_transportedTgt_id_eq data d)).base).toFunctor.map
      (functorToConnGrothendieckAltFiber data (𝟙 d)).fiber ≍
      𝟙 (functorToConnGrothendieckObjMap data d).fiber.fiber := by
    exact HEq.trans hMapFiber hIdFiber
  -- Goal: G.map fiber ≫ (eqToHom h).fiber ≍ (eqToHom h).fiber
  -- The (eqToHom h).fiber is itself an eqToHom by Grothendieck.fiber_eqToHom
  -- First rewrite the fiber in the composition using that fact
  rw [Grothendieck.fiber_eqToHom]
  -- Now goal: G.map fiber ≫ eqToHom (...) ≍ (eqToHom h').fiber
  -- where h' = functorToConnGrothendieck_transportedTgt_id_eq data d
  -- LHS: by comp_eqToHom_heq, G.map fiber ≫ eqToHom h ≍ G.map fiber
  apply HEq.trans (comp_eqToHom_heq _ _)
  -- Now goal: G.map fiber ≍ (eqToHom h').fiber
  -- Use hGmapId: G.map fiber ≍ 𝟙 W
  apply HEq.trans hGmapId
  -- Now goal: 𝟙 W ≍ (eqToHom h').fiber
  -- Use the new helper: (eqToHom h).fiber ≍ 𝟙 X.fiber
  apply HEq.symm
  exact Grothendieck.eqToHom_fiber_heq_id _

/--
The fiber case of map_id: proves that the fiber component of
`functorToConnGrothendieckMapHom data (𝟙 d)` composed with the appropriate eqToHom
equals the fiber of `GrothendieckContra'.id`.
-/
lemma functorToConnGrothendieck_map_id_fiber (d : D) :
    functorToConnGrothendieckAltFiber data (𝟙 d) ≫
      eqToHom (functorToConnGrothendieck_transportedTgt_id_eq data d) =
    (GrothendieckContra'.id (functorToConnGrothendieckObjMap data d)).fiber := by
  apply Grothendieck.ext
  case w_base => exact functorToConnGrothendieck_map_id_fiber_base data d
  case w_fiber => exact functorToConnGrothendieck_map_id_fiber_fiber data d

/--
The base component of the transported target for composition equals the iterated
transition.
-/
lemma functorToConnGrothendieck_transportedTgt_comp_base_eq {d d' d'' : D}
    (g : d ⟶ d') (h : d' ⟶ d'') :
    (functorToConnGrothendieckTransportedTgt data (g ≫ h)).base =
    ((innerFiberAltTransition C F (functorToConnGrothendieckAltBase data g)).obj
        ((innerFiberAltTransition C F (functorToConnGrothendieckAltBase data h)).obj
          (functorToConnGrothendieckObjMap data d'').fiber)).base := by
  simp only [functorToConnGrothendieckTransportedTgt, domainFiberFunctor_map,
    innerFiberAltTransition, innerFiberAltTransitionObj, functorToConnGrothendieckAltBase,
    Functor.map_comp, Arrow.comp_left]
  -- Now LHS is (Under.map (f ≫ g)).obj x.base, RHS is (Under.map f).obj ((Under.map g).obj x.base)
  exact congrArg (·.obj (functorToConnGrothendieckObjMap data d'').fiber.base)
    (Under.mapComp_eq (data.arrFun.map g).left (data.arrFun.map h).left)

set_option backward.isDefEq.respectTransparency false in
/--
The base component of the map_comp fiber case.
-/
lemma functorToConnGrothendieck_map_comp_fiber_base {d d' d'' : D}
    (g : d ⟶ d') (h : d' ⟶ d'') :
    (functorToConnGrothendieckAltFiber data (g ≫ h) ≫
      eqToHom (functorToConnGrothendieck_transportedTgt_comp_eq data g h)).base =
    (GrothendieckContra'.comp
      ⟨functorToConnGrothendieckAltBase data g, functorToConnGrothendieckAltFiber data g⟩
      ⟨functorToConnGrothendieckAltBase data h,
        functorToConnGrothendieckAltFiber data h⟩).fiber.base := by
  simp only [GrothendieckContra'.comp_fiber, functorToConnGrothendieckAltFiber,
    domainFiberFunctor_map]
  apply Under.UnderMorphism.ext
  simp only [id_eq]
  rw [Grothendieck.comp_base, Comma.comp_right]
  simp only [functorToConnGrothendieckObjMap_base, functorToConnGrothendieckObjMap_fiber_base,
    Under.mk_right, Functor.id_obj, CategoryOp'.eq_1,
    Functor.toCatHom_toFunctor, TwistedArrow'.eq_1,
    Functor.comp_obj,
    functorToConnGrothendieckObjMap_fiber_fiber, eqToHom_refl, Cat.Hom.id_toFunctor,
    Cat.Hom.comp_toFunctor, eq_mpr_eq_cast, GrothendieckContra'.comp_base, Functor.map_comp,
    functor_map_eqToHom, congrArg_cast_hom_right, cast_cast, innerFiberAltTransition_map]
  rw [Grothendieck.comp_base, Comma.comp_right]
  simp only [Under.mk_right, Functor.id_obj]
  rw [Grothendieck.comp_base, Comma.comp_right]
  simp only [innerFiberAltTransitionHom_base, functorToConnGrothendieckInnerBase,
    Under.homMk_right, Under.map_map_right, Functor.map_comp, Arrow.comp_right,
    Category.assoc]
  -- The two sides differ only in the eqToHom proof terms
  -- Use Grothendieck.eqToHom_base' to simplify (eqToHom _).base to eqToHom _
  rw [Grothendieck.eqToHom_base', Grothendieck.eqToHom_base']
  -- Now use Under.eqToHom_right to simplify .right
  rw [Under.eqToHom_right, Under.eqToHom_right]

/--
The fiber component of `functorToConnGrothendieckAltFiber data (g ≫ h)` is HEq to
a transported composition via `data.hom_comp`.
-/
lemma functorToConnGrothendieckAltFiber_comp_fiber_heq {d d' d'' : D}
    (g : d ⟶ d') (h : d' ⟶ d'') :
    (functorToConnGrothendieckAltFiber data (g ≫ h)).fiber ≍
    ((functorToConnGrothendieckTransportGToGHRaw (F := F)
        (arrFun := data.arrFun) g h).map (data.hom g) ≫
      eqToHom (functorToConnGrothendieckTransportCoherence data.fib g h) ≫
      (functorToConnGrothendieckTransportHToGHRaw (F := F)
        (arrFun := data.arrFun) g h).map (data.hom h)) := by
  simp only [functorToConnGrothendieckAltFiber]
  apply HEq.trans (cast_heq _ _)
  apply HEq.trans (cast_heq _ _)
  apply HEq.trans (cast_heq _ _)
  apply HEq.trans (cast_heq _ _)
  apply HEq.trans (Cat.eqToHom_map_heq _ _)
  exact data.hom_comp g h

end FunctorToConnGrothendieck

end FunctorCharacterization

section TwGrothendieck

/-! ## TwGrothendieck: connected Grothendieck indexed by `TwistedArrow`

Given `F : TwistedArrow C ⥤ Cat`, we define `TwGrothendieckObj C F`
as `ConnGrothendieckObj C (tw'ToTw ⋙ F)`, making the components
accessible via the unprimed twisted arrow API.
-/

variable (F : TwistedArrow C ⥤ Cat.{w₁, w₂})

/-- The connected Grothendieck construction indexed by
`TwistedArrow C` rather than `TwistedArrow' C`.

Given `F : TwistedArrow C ⥤ Cat`, an object consists of:
- An arrow `f : a ⟶ b` in `C` (as a `TwistedArrow C` object)
- An object in the fiber category `F(f)` -/
abbrev TwGrothendieckObj :=
  ConnGrothendieckObj C (tw'ToTw ⋙ F)

/-- The morphisms of the connected Grothendieck construction
indexed by `TwistedArrow C`. -/
abbrev TwGrothendieckHom
    (x y : TwGrothendieckObj C F) :=
  ConnGrothendieckHom C (tw'ToTw ⋙ F) x y

end TwGrothendieck

end GebLean
