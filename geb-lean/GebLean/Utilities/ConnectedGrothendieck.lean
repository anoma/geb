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

/--
The twisted arrow morphism `(id, codArr) : tw → w` where `w = twArr' tw ≫ codArr`.
This transports along the codomain direction.
-/
def connGrothendieckTwMorphCod (tw : TwistedArrow' C)
    {b' : C} (codArr : twCod' tw ⟶ b') :
    tw ⟶ connGrothendieckDiagCod C tw codArr :=
  twHomMk' (𝟙 _) codArr (by simp only [connGrothendieckDiagCod, twObjMk'_arr,
    Category.id_comp])

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
    {b' : C} (codArr : twCod' x.arrow ⟶ b') : Cat.{v, u} :=
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
    (F.map (connGrothendieckTwMorphCod C x.arrow codArr)).obj x.fiber ⟶
    (F.map (connGrothendieckTwMorphDom C y.arrow domArr ≫
      eqToHom (connGrothendieckDiagEq C F x y domArr codArr square_comm))).obj
      y.fiber

/--
The hom-set for the connected Grothendieck construction.
-/
def connGrothendieckHomSet : HomSet (ConnGrothendieckObj C F) :=
  ConnGrothendieckHom C F

end ConnectedGrothendieckData

section ConnectedGrothendieckCategory

/-! ## Category structure on the connected Grothendieck construction -/

variable (F : TwistedArrow' C ⥤ Cat.{v, u})

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
    (F.map (connGrothendieckTwMorphCod C x.arrow (m.codArr ≫ n.codArr))).obj x.fiber =
    (F.map (connGrothendieckMorphW1W3 C F m n)).obj
      ((F.map (connGrothendieckTwMorphCod C x.arrow m.codArr)).obj x.fiber) := by
  rw [← connGrothendieckTwMorphCodComp C F m n, Functor.map_comp]
  rfl

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
    (F.map (connGrothendieckMorphW1W3 C F m n)).obj
      ((F.map (connGrothendieckTwMorphDom C y.arrow m.domArr ≫
        eqToHom (connGrothendieckDiagEq C F x y m.domArr m.codArr m.square_comm))).obj
        y.fiber) =
    (F.map (connGrothendieckMorphW2W3 C F m n)).obj
      ((F.map (connGrothendieckTwMorphCod C y.arrow n.codArr)).obj y.fiber) := by
  have hLeft : (F.map (connGrothendieckMorphW1W3 C F m n)).obj
      ((F.map (connGrothendieckTwMorphDom C y.arrow m.domArr ≫
        eqToHom (connGrothendieckDiagEq C F x y m.domArr m.codArr m.square_comm))).obj
        y.fiber) =
      (F.map (connGrothendieckTwMorphYW3_left C F m n)).obj y.fiber := by
    simp only [connGrothendieckTwMorphYW3_left, Functor.map_comp]
    rfl
  have hRight : (F.map (connGrothendieckMorphW2W3 C F m n)).obj
      ((F.map (connGrothendieckTwMorphCod C y.arrow n.codArr)).obj y.fiber) =
      (F.map (connGrothendieckTwMorphYW3_right C F m n)).obj y.fiber := by
    simp only [connGrothendieckTwMorphYW3_right, Functor.map_comp]
    rfl
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
        (connGrothendieckCompSquareComm C F m n)))).obj z.fiber =
    (F.map (connGrothendieckMorphW2W3 C F m n)).obj
      ((F.map (connGrothendieckTwMorphDom C z.arrow n.domArr ≫
        eqToHom (connGrothendieckDiagEq C F y z n.domArr n.codArr n.square_comm))).obj
        z.fiber) := by
  calc (F.map (connGrothendieckTwMorphDom C z.arrow (m.domArr ≫ n.domArr) ≫
      eqToHom (connGrothendieckDiagEq C F x z (m.domArr ≫ n.domArr) (m.codArr ≫ n.codArr)
        (connGrothendieckCompSquareComm C F m n)))).obj z.fiber
      = (F.map (connGrothendieckTwMorphZW3_left C F m n)).obj z.fiber := rfl
    _ = (F.map (connGrothendieckTwMorphZW3_right C F m n)).obj z.fiber := by
          rw [connGrothendieckTwMorphZW3_eq]
    _ = (F.map (connGrothendieckMorphW2W3 C F m n)).obj
        ((F.map (connGrothendieckTwMorphDom C z.arrow n.domArr ≫
          eqToHom (connGrothendieckDiagEq C F y z n.domArr n.codArr n.square_comm))).obj
          z.fiber) := by
            simp only [connGrothendieckTwMorphZW3_right, Functor.map_comp]; rfl

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
    (F.map (connGrothendieckMorphW1W3 C F m n)).map m.fiberMorph ≫
    eqToHom (connGrothendieckCompMiddleEq C F m n) ≫
    (F.map (connGrothendieckMorphW2W3 C F m n)).map n.fiberMorph ≫
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
    (eqToHom h).map f ≍ f := by
  subst h
  rfl

/--
Version of `Cat.eqToHom_map_heq` where the functor is only propositionally
equal to `eqToHom`.
-/
lemma Cat.functor_map_heq_of_eq_eqToHom {C D : Cat} (h : C = D)
    (G : C ⥤ D) (hG : G = eqToHom h) {x y : C} (f : x ⟶ y) :
    G.map f ≍ f := by
  subst hG
  exact Cat.eqToHom_map_heq h f

/--
When functor `G` equals `G₁ ⋙ G₂ ⋙ eqToHom h`, mapping by G gives something
HEq to `G₂.map (G₁.map f)`.
-/
lemma Cat.functor_map_heq_of_eq_comp_comp_eqToHom {C D E F' : Cat}
    (G : C ⥤ F') (G₁ : C ⥤ D) (G₂ : D ⥤ E)
    (h : E = F') (hG : G = G₁ ⋙ G₂ ⋙ eqToHom h)
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
    (hx : (eqToHom h).obj x₁ = x₂) (hy : (eqToHom h).obj y₁ = y₂)
    (hf : (eqToHom h).map f₁ = eqToHom hx ≫ f₂ ≫ eqToHom hy.symm) :
    f₁ ≍ f₂ := by
  subst h
  simp only [eqToHom_refl] at hx hy hf
  subst hx hy
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hf
  exact heq_of_eq hf

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
  · -- The LHS fiber morphism is:
    -- eqToHom(...) ≫ F.map(morphW1W3).map(id.fiberMorph) ≫ eqToHom(...) ≫
    -- F.map(morphW2W3).map(m.fiberMorph) ≫ eqToHom(...)
    --
    -- Since id.fiberMorph = eqToHom(...), and morphW2W3(id, m) = eqToHom(...),
    -- we need to show this chain of eqToHoms and functors applied to m.fiberMorph
    -- equals m.fiberMorph up to HEq.
    -- Don't unfold connGrothendieckId, to enable using connGrothendieckMorphW2W3_id_left
    simp only [connGrothendieckComp]
    -- Left-associate to get trailing eqToHom in form (... ≫ eqToHom)
    conv_lhs => rw [← Category.assoc, ← Category.assoc, ← Category.assoc]
    -- Peel off trailing eqToHom
    apply HEq.trans (comp_eqToHom_heq _ _)
    -- First simplify F.map(morphW1W3).map(id.fiberMorph) using that id.fiberMorph is eqToHom
    simp only [connGrothendieckId, eqToHom_map, eqToHom_trans]
    -- Now goal is:
    -- eqToHom ⋯ ≫ (F.map (morphW2W3 {...} m)).map m.fiberMorph ≍ m.fiberMorph
    -- Use HEq.trans to peel off leading eqToHom via eqToHom_comp_heq
    apply HEq.trans
    · apply eqToHom_comp_heq
    -- Now goal: F.map(morphW2W3 {...} m).map(m.fiberMorph) ≍ m.fiberMorph
    -- Fold the connGrothendieckId back
    change (F.map (connGrothendieckMorphW2W3 C F (connGrothendieckId C F x) m)).map m.fiberMorph ≍
         m.fiberMorph
    -- Now use connGrothendieckMorphW2W3_id_left: morphW2W3(id, m) = eqToHom(...)
    rw [connGrothendieckMorphW2W3_id_left]
    -- So F.map(eqToHom).map(m.fiberMorph) should simplify
    rw [eqToHom_map]
    -- Now (eqToHom ...).map(m.fiberMorph) from Cat
    -- Use Cat.eqToHom_map_heq to finish
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
  · -- Similar structure to id_comp but with the second morphism being identity
    -- Keep connGrothendieckId folded to enable using connGrothendieckMorphW1W3_id_right
    simp only [connGrothendieckComp]
    -- Left-associate
    conv_lhs => rw [← Category.assoc, ← Category.assoc, ← Category.assoc]
    -- Peel off trailing eqToHom
    apply HEq.trans (comp_eqToHom_heq _ _)
    -- Now: (eqToHom ≫ morphW1W3.map(m.fiberMorph) ≫ eqToHom) ≫ morphW2W3.map(id.fiberMorph) ≍ ?
    -- First simplify id.fiberMorph = eqToHom, and eqToHom_map
    simp only [connGrothendieckId, eqToHom_map]
    -- morphW2W3.map(eqToHom) simplified to eqToHom
    -- Now fold the connGrothendieckId back
    change ((eqToHom _ ≫
            (F.map (connGrothendieckMorphW1W3 C F m (connGrothendieckId C F y))).map
              m.fiberMorph) ≫ eqToHom _) ≫ eqToHom _ ≍ m.fiberMorph
    -- Peel off trailing eqToHoms by HEq.trans
    apply HEq.trans (comp_eqToHom_heq _ _)
    apply HEq.trans (comp_eqToHom_heq _ _)
    -- Now: eqToHom ≫ morphW1W3.map(m.fiberMorph) ≍ ?
    -- Peel off leading eqToHom
    apply HEq.trans
    · apply eqToHom_comp_heq
    -- Now: morphW1W3.map(m.fiberMorph) ≍ m.fiberMorph
    -- Since morphW1W3(m, id) = eqToHom, F.map(eqToHom).map(...) ≍ ...
    -- Use connGrothendieckMorphW1W3_id_right
    rw [connGrothendieckMorphW1W3_id_right, eqToHom_map]
    exact Cat.eqToHom_map_heq _ _

/--
The codomain arrow expressions `(a ≫ b) ≫ c` and `a ≫ b ≫ c` give the same diagonal.
-/
lemma connGrothendieckDiagCod_assoc (tw : TwistedArrow' C)
    {b' b'' b''' : C} (a : twCod' tw ⟶ b') (b : b' ⟶ b'') (c : b'' ⟶ b''') :
    connGrothendieckDiagCod C tw ((a ≫ b) ≫ c) = connGrothendieckDiagCod C tw (a ≫ b ≫ c) := by
  simp only [connGrothendieckDiagCod, Category.assoc]

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

/--
DiagCod composed with itself equals DiagCod with composed arrows.
-/
@[simp]
lemma connGrothendieckDiagCod_comp (tw : TwistedArrow' C)
    {b' b'' : C} (a : twCod' tw ⟶ b') (b : b' ⟶ b'') :
    connGrothendieckDiagCod C (connGrothendieckDiagCod C tw a) b =
    connGrothendieckDiagCod C tw (a ≫ b) := by
  simp only [connGrothendieckDiagCod, twObjMk'_arr, Category.assoc]

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
    (eqToHom (connGrothendieckFiberCat_comp C F tw a b)).obj
      ((F.map (connGrothendieckTwMorphCod C (connGrothendieckDiagCod C tw a) b)).obj
        ((F.map (connGrothendieckTwMorphCod C tw a)).obj src)) =
    (F.map (connGrothendieckTwMorphCod C tw (a ≫ b))).obj src := by
  have hFmapComp : F.map (connGrothendieckTwMorphCod C tw a) ≫
      F.map (connGrothendieckTwMorphCod C (connGrothendieckDiagCod C tw a) b) =
      F.map (connGrothendieckTwMorphCod C tw (a ≫ b)) ≫
      eqToHom (connGrothendieckFiberCat_comp C F tw a b).symm := by
    rw [← Functor.map_comp, connGrothendieckTwMorphCod_comp, Functor.map_comp, eqToHom_map]
  calc (eqToHom (connGrothendieckFiberCat_comp C F tw a b)).obj
        ((F.map (connGrothendieckTwMorphCod C (connGrothendieckDiagCod C tw a) b)).obj
          ((F.map (connGrothendieckTwMorphCod C tw a)).obj src))
      = ((F.map (connGrothendieckTwMorphCod C tw a) ≫
          F.map (connGrothendieckTwMorphCod C (connGrothendieckDiagCod C tw a) b) ≫
          eqToHom (connGrothendieckFiberCat_comp C F tw a b))).obj src := rfl
    _ = (((F.map (connGrothendieckTwMorphCod C tw a) ≫
          F.map (connGrothendieckTwMorphCod C (connGrothendieckDiagCod C tw a) b)) ≫
          eqToHom (connGrothendieckFiberCat_comp C F tw a b))).obj src := by
        simp only [Category.assoc]
    _ = (((F.map (connGrothendieckTwMorphCod C tw (a ≫ b)) ≫
          eqToHom (connGrothendieckFiberCat_comp C F tw a b).symm) ≫
          eqToHom (connGrothendieckFiberCat_comp C F tw a b))).obj src := by
        rw [hFmapComp]
    _ = ((F.map (connGrothendieckTwMorphCod C tw (a ≫ b)) ≫
          eqToHom (connGrothendieckFiberCat_comp C F tw a b).symm ≫
          eqToHom (connGrothendieckFiberCat_comp C F tw a b))).obj src := by
        simp only [Category.assoc]
    _ = ((F.map (connGrothendieckTwMorphCod C tw (a ≫ b)) ≫ 𝟙 _)).obj src := by
        simp only [eqToHom_trans, eqToHom_refl]
    _ = (F.map (connGrothendieckTwMorphCod C tw (a ≫ b))).obj src := by
        simp only [Category.comp_id]

/--
The target of a fiber morphism transported via nested TwMorphCod maps equals
the target transported via the single composed TwMorphCod (after eqToHom).
-/
lemma connGrothendieckTwMorphCod_map_comp_tgt (tw : TwistedArrow' C)
    {b' b'' : C} (a : twCod' tw ⟶ b') (b : b' ⟶ b'') (tgt : F.obj tw) :
    (eqToHom (connGrothendieckFiberCat_comp C F tw a b)).obj
      ((F.map (connGrothendieckTwMorphCod C (connGrothendieckDiagCod C tw a) b)).obj
        ((F.map (connGrothendieckTwMorphCod C tw a)).obj tgt)) =
    (F.map (connGrothendieckTwMorphCod C tw (a ≫ b))).obj tgt :=
  connGrothendieckTwMorphCod_map_comp_src C F tw a b tgt

end ConnectedGrothendieckCategory

section ConnectedGrothendieckProjection

/-! ## The projection functor to the arrow category -/

variable (F : TwistedArrow' C ⥤ Cat.{v, u})

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
The fiber inclusion functor from `(Over b)^op` to `TwistedArrow' C`.

On objects: `(f : a → b) ↦ f` (viewed as a twisted arrow `a → b`)
On morphisms: `α : f → g` in `(Over b)^op` (i.e., `α : c → a` with `f ∘ α = g`)
  maps to `(α, 𝟙 b) : f → g` in `Tw(C)`
-/
def overOpToTwistedArrow (b : C) : (Over b)ᵒᵖ' ⥤ TwistedArrow' C where
  obj ov := twObjMk' ov.hom
  map {ov ov'} α :=
    twHomMk'
      (x := twObjMk' ov.hom)
      (y := twObjMk' ov'.hom)
      (by simp only [twObjMk'_dom]; exact α.left)
      (by simp only [twObjMk'_cod]; exact 𝟙 b)
      (by
        simp only [twObjMk'_arr]
        change id α.left ≫ ov.hom ≫ id (𝟙 b) = ov'.hom
        simp only [id]
        have h : ov.hom ≫ 𝟙 b = ov.hom := Category.comp_id ov.hom
        rw [h]
        exact Over.w α)
  map_id ov := by
    apply twHom'_ext <;> rfl
  map_comp {ov ov' ov''} α β := by
    apply twHom'_ext
    · rfl
    · simp only [twHomMk'_codArr, twCodArr'_comp]
      exact (Category.id_comp (𝟙 b)).symm

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
The twisted arrow morphism from `twObjMk' ov.hom` to `twObjMk' (ov.hom ≫ β)`,
used to transport fiber elements along a base morphism `β : b ⟶ d`.
-/
def fiberTransportTwMorph {b d : C} (β : b ⟶ d) (ov : Over b) :
    twObjMk' ov.hom ⟶ twObjMk' (ov.hom ≫ β) :=
  twHomMk'
    (x := twObjMk' ov.hom)
    (y := twObjMk' (ov.hom ≫ β))
    (by simp only [twObjMk'_dom]; exact 𝟙 ov.left)
    (by simp only [twObjMk'_cod]; exact β)
    (by
      simp only [twObjMk'_arr]
      change id (𝟙 ov.left) ≫ ov.hom ≫ id β = ov.hom ≫ β
      simp only [id, Category.id_comp])

/--
The functor that transports fiber elements along a base morphism `β : b ⟶ d`.
For `ov : Over b` and `x : F.obj (twObjMk' ov.hom)`, this produces an element
of `F.obj (twObjMk' (ov.hom ≫ β))`.
-/
def fiberTransport {b d : C} (β : b ⟶ d) (ov : Over b) :
    (restrictToFiber C F b).obj ov ⥤ (restrictToFiber C F d).obj ((Over.map β).obj ov) :=
  F.map (fiberTransportTwMorph C β ov)

/--
The functor that transports fiber elements along a base morphism `β : b ⟶ d`,
for the oppositized fiber categories. This is the result of applying
`Cat.opFunctor'.map` to `fiberTransport`.
-/
def fiberTransportOp {b d : C} (β : b ⟶ d) (ov : Over b) :
    (restrictToFiberOp C F b).obj ov ⥤ (restrictToFiberOp C F d).obj ((Over.map β).obj ov) :=
  Cat.opFunctor'.map (fiberTransport C F β ov)

/--
The object mapping for the transition functor between fibers.
Given `x : Grothendieck (restrictToFiber F b)`, produces an object in
`Grothendieck (restrictToFiber F d)`.
-/
def fiberFunctorTransitionObj {b d : C} (β : b ⟶ d)
    (x : Grothendieck (restrictToFiber C F b)) :
    Grothendieck (restrictToFiber C F d) :=
  ⟨(Over.map β).obj x.base, (fiberTransport C F β x.base).obj x.fiber⟩

/--
Coherence lemma: the twisted arrow morphism corresponding to `fiberTransport`
composed with the image of a base morphism under `overOpToTwistedArrow d`
equals the image of the base morphism under `overOpToTwistedArrow b`
composed with `fiberTransportTwMorph`.

In the opposite category `(Over b)ᵒᵖ'`, a morphism `α : ov ⟶ ov'` corresponds
to a morphism `ov' ⟶ ov` in `Over b`, so the functors map it in reverse.
-/
theorem fiberTransport_naturality {b d : C} (β : b ⟶ d)
    {ov ov' : (Over b)ᵒᵖ'} (α : ov ⟶ ov') :
    (overOpToTwistedArrow C b).map α ≫ fiberTransportTwMorph C β ov' =
    fiberTransportTwMorph C β ov ≫ (overOpToTwistedArrow C d).map ((Over.map β).map α) := by
  apply twHom'_ext
  · simp only [twDomArr'_comp, twHomMk'_domArr, overOpToTwistedArrow,
               fiberTransportTwMorph, twHomMk'_domArr, id, Over.map_map_left]
    trans α.left
    · exact Category.id_comp α.left
    · exact (Category.comp_id α.left).symm
  · simp only [twCodArr'_comp, twHomMk'_codArr, overOpToTwistedArrow,
               fiberTransportTwMorph, twHomMk'_codArr, id]
    trans β
    · exact Category.id_comp β
    · exact (Category.comp_id β).symm

/--
Functor-level naturality: fiber transport composed with restriction mapping
equals restriction mapping followed by fiber transport.
-/
theorem fiberTransport_functor_naturality {b d : C} (β : b ⟶ d)
    {ov ov' : (Over b)ᵒᵖ'} (α : ov ⟶ ov') :
    (restrictToFiber C F b).map α ⋙ fiberTransport C F β ov' =
    fiberTransport C F β ov ⋙ (restrictToFiber C F d).map ((Over.map β).map α) := by
  simp only [restrictToFiber, fiberTransport, Functor.comp_map]
  have h := fiberTransport_naturality C β α
  calc F.map ((overOpToTwistedArrow C b).map α) ⋙ F.map (fiberTransportTwMorph C β ov')
      = F.map ((overOpToTwistedArrow C b).map α) ≫ F.map (fiberTransportTwMorph C β ov') := rfl
    _ = F.map ((overOpToTwistedArrow C b).map α ≫ fiberTransportTwMorph C β ov') := by
          rw [F.map_comp]
    _ = F.map (fiberTransportTwMorph C β ov ≫
          (overOpToTwistedArrow C d).map ((Over.map β).map α)) := by
          rw [h]
    _ = F.map (fiberTransportTwMorph C β ov) ≫
          F.map ((overOpToTwistedArrow C d).map ((Over.map β).map α)) := by
          rw [← F.map_comp]
    _ = F.map (fiberTransportTwMorph C β ov) ⋙
          F.map ((overOpToTwistedArrow C d).map ((Over.map β).map α)) := rfl

/--
Functor-level naturality for oppositized fiber transport.
-/
theorem fiberTransportOp_functor_naturality {b d : C} (β : b ⟶ d)
    {ov ov' : (Over b)ᵒᵖ'} (α : ov ⟶ ov') :
    (restrictToFiberOp C F b).map α ⋙ fiberTransportOp C F β ov' =
    fiberTransportOp C F β ov ⋙ (restrictToFiberOp C F d).map ((Over.map β).map α) := by
  have h := fiberTransport_functor_naturality C F β α
  simp only [restrictToFiberOp, fiberTransportOp, Functor.comp_map, Cat.opFunctor']
  exact congrArg Functor.op' h

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
  have fiber_eq : ((restrictToFiberOp C F d).map ((Over.map β).map f.base) |>.obj
        ((fiberTransportOp C F β x.base).obj x.fiber)) =
      ((fiberTransportOp C F β y.base).obj
        ((restrictToFiberOp C F b).map f.base |>.obj x.fiber)) :=
    congrArg (fun G => G.obj x.fiber) nat_eq.symm
  exact eqToHom fiber_eq ≫
        (fiberTransportOp C F β y.base).map f.fiber

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
  have fiber_eq : ((restrictToFiber C F d).map ((Over.map β).map f.base) |>.obj
        ((fiberTransport C F β x.base).obj x.fiber)) =
      ((fiberTransport C F β y.base).obj
        ((restrictToFiber C F b).map f.base |>.obj x.fiber)) :=
    congrArg (fun G => G.obj x.fiber) nat_eq.symm
  exact eqToHom fiber_eq ≫
        (fiberTransport C F β y.base).map f.fiber

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
               Grothendieck.id_fiber, Grothendieck.id_base]
    simp only [fiberTransport, eqToHom_map, eqToHom_trans]
  case w_base =>
    simp only [fiberFunctorTransitionHom, fiberFunctorTransitionObj,
               Grothendieck.id_base]
    exact (Over.map β).map_id x.base

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
When `β = 𝟙 b`, the fiber transport twisted arrow morphism is `eqToHom`.
-/
lemma fiberTransportTwMorph_id {b : C} (ov : Over b) :
    fiberTransportTwMorph C (𝟙 b) ov =
    eqToHom (twObjMk'_comp_id C ov).symm := by
  apply twHom'_ext
  · simp only [fiberTransportTwMorph, twHomMk'_domArr, twDomArr'_eqToHom,
               twObjMk'_dom, eqToHom_refl, id, Functor.id_obj]
  · simp only [fiberTransportTwMorph, twHomMk'_codArr, twCodArr'_eqToHom,
               twObjMk'_cod, eqToHom_refl, id]
    rfl

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

/--
When `β = 𝟙 b`, the fiber transport functor is `eqToHom` in Cat.
-/
lemma fiberTransport_id {b : C} (ov : Over b) :
    fiberTransport C F (𝟙 b) ov =
    eqToHom (fiberTransport_id_cat_eq C F ov).symm := by
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
In the category Cat, applying `eqToHom` to an object produces heterogeneous
equality with the original object. This uses `cases` to eliminate the equality.
-/
lemma eqToHom_obj_heq (A B : Cat) (h : A = B) (x : A.α) :
    HEq ((eqToHom h).obj x) x := by
  cases h
  rfl

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

/--
When `β = 𝟙 b`, `fiberFunctorTransition C F (𝟙 b)` equals the identity functor.
-/
theorem fiberFunctorTransition_id {b : C} :
    fiberFunctorTransition C F (𝟙 b) = 𝟭 (Grothendieck (restrictToFiber C F b)) := by
  apply Functor.ext
  case h_obj => exact fiberFunctorTransitionObj_id C F
  case h_map =>
    intro x y f
    -- After simplification by Functor.ext, the goal is:
    -- (fiberFunctorTransition C F (𝟙 b)).map f = eqToHom _ ≫ f ≫ eqToHom _
    simp only [Functor.id_map]
    apply Grothendieck.ext
    case w_base =>
      simp only [fiberFunctorTransition, fiberFunctorTransitionHom,
                 Grothendieck.comp_base, Grothendieck.eqToHom_base']
      -- Goal: (Over.map (𝟙 b)).map f.base = eqToHom _ ≫ f.base ≫ eqToHom _
      -- Use Functor.congr_hom (Over.mapId_eq b) to convert LHS to RHS form
      -- congr_hom says: F.map f = eqToHom _ ≫ G.map f ≫ eqToHom _
      -- Here F = Over.map (𝟙 b), G = 𝟭 (Over b), so:
      -- (Over.map (𝟙 b)).map f.base = eqToHom _ ≫ (𝟭 (Over b)).map f.base ≫ eqToHom _
      rw [Functor.congr_hom (Over.mapId_eq b) f.base, Functor.id_map]
      -- Now goal is: eqToHom _ ≫ f.base ≫ eqToHom _ = eqToHom _ ≫ f.base ≫ eqToHom _
      -- Both sides are HEq to f.base, so they're equal via transitivity
      apply eq_of_heq
      -- eqToHom_comp_heq : eqToHom h ≫ f ≍ f
      -- comp_eqToHom_heq : f ≫ eqToHom h ≍ f
      apply HEq.trans (eqToHom_comp_heq _ _)
      apply HEq.trans (comp_eqToHom_heq _ _)
      apply HEq.trans (comp_eqToHom_heq _ _).symm
      exact (eqToHom_comp_heq _ _).symm
    case w_fiber =>
      -- Goal: eqToHom ⋯ ≫ ((fiberFunctorTransition C F (𝟙 b)).map f).fiber
      --     = (eqToHom ⋯ ≫ f ≫ eqToHom ⋯).fiber
      -- Both expressions reduce to eqToHom chains around f.fiber, all HEq to f.fiber.
      apply eq_of_heq
      simp only [fiberFunctorTransition, fiberFunctorTransitionHom,
                 Grothendieck.comp_fiber, Grothendieck.fiber_eqToHom,
                 eqToHom_trans_assoc, eqToHom_comp_heq_iff, heq_eqToHom_comp_iff]
      -- Goal: (fiberTransport C F (𝟙 b) y.base).map f.fiber ≍
      --   ((restrictToFiber C F b).map (eqToHom ⋯).base).map f.fiber ≫ eqToHom _
      -- Use the lemma with fiberTransport_id
      apply HEq.trans
      · exact Cat.functor_map_heq_of_eq_eqToHom _ _ (fiberTransport_id C F y.base) f.fiber
      -- Goal: f.fiber ≍ ((restrictToFiber C F b).map (f ≫ eqToHom ⋯).base).map (eqToHom ⋯)
      --            ≫ eqToHom ⋯ ≫ ((restrictToFiber C F b).map (eqToHom ⋯).base).map f.fiber
      --            ≫ eqToHom ⋯
      apply HEq.symm
      -- Simplify (f ≫ eqToHom _).base and (eqToHom _).base
      simp only [Grothendieck.comp_base, eqToHom_map, eqToHom_trans_assoc]
      -- Goal: eqToHom ⋯ ≫ ((restrictToFiber C F b).map (eqToHom ⋯).base).map f.fiber
      --       ≫ eqToHom ⋯ ≍ f.fiber
      -- Strip leading and trailing eqToHom
      apply HEq.trans (eqToHom_comp_heq _ _)
      apply HEq.trans (comp_eqToHom_heq _ _)
      -- Goal: ((restrictToFiber C F b).map (eqToHom ⋯).base).map f.fiber ≍ f.fiber
      -- (eqToHom _).base = eqToHom _ by Grothendieck.eqToHom_base'
      -- Then restrictToFiber.map (eqToHom _) = eqToHom _ by eqToHom_map
      -- So we have (eqToHom _).map f.fiber ≍ f.fiber
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

/--
When `β = 𝟙 b`, the oppositized fiber transport functor is `eqToHom` in Cat.
-/
lemma fiberTransportOp_id {b : C} (ov : Over b) :
    fiberTransportOp C F (𝟙 b) ov =
    eqToHom (fiberTransportOp_id_cat_eq C F ov).symm := by
  simp only [fiberTransportOp, fiberTransport_id, Cat.opFunctor', eqToHom_map]

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

/--
When `β = 𝟙 b`, `fiberFunctorTransitionOp C F (𝟙 b)` equals the identity functor.
-/
theorem fiberFunctorTransitionOp_id {b : C} :
    fiberFunctorTransitionOp C F (𝟙 b) =
    𝟭 (Grothendieck (restrictToFiberOp C F b)) := by
  apply Functor.ext
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

/--
The twisted arrow morphism for `β ≫ γ` equals the composition of the twisted
arrow morphisms for `β` and `γ`, up to the path equality.
-/
lemma fiberTransportTwMorph_comp {b d e : C} (β : b ⟶ d) (γ : d ⟶ e) (ov : Over b) :
    fiberTransportTwMorph C (β ≫ γ) ov =
    fiberTransportTwMorph C β ov ≫
      fiberTransportTwMorph C γ ((Over.map β).obj ov) ≫
      eqToHom (congrArg (twObjMk' ·) (Category.assoc ov.hom β γ)) := by
  apply twHom'_ext
  · -- Domain arrow: LHS is 𝟙 ov.left
    -- RHS is 𝟙 ov.left ≫ 𝟙 (Over.map β).obj ov).left ≫ eqToHom.domArr
    simp only [fiberTransportTwMorph, twDomArr'_comp, twHomMk'_domArr,
               twDomArr'_eqToHom, id, Over.map_obj_left]
    -- Goal: 𝟙 ov.left = (eqToHom ⋯ ≫ 𝟙 ov.left) ≫ 𝟙 ov.left
    -- The eqToHom is on ov.left (not arrows), so it's the identity
    -- After rw: 𝟙 ov.left = 𝟙 ov.left ≫ 𝟙 ov.left
    rw [eqToHom_refl, Category.id_comp]
    exact (Category.id_comp (𝟙 ov.left)).symm
  · -- Codomain arrow: LHS is β ≫ γ
    -- RHS is β ≫ γ ≫ eqToHom.codArr
    simp only [fiberTransportTwMorph, twCodArr'_comp, twHomMk'_codArr,
               twCodArr'_eqToHom, id, Over.map_obj_hom]
    -- Goal: β ≫ γ = β ≫ γ ≫ eqToHom ⋯
    simp only [eqToHom_refl, Category.comp_id]

/--
The fiber transport for `β ≫ γ` equals the composition of fiber transports, up to eqToHom.
-/
theorem fiberTransport_comp {b d e : C} (β : b ⟶ d) (γ : d ⟶ e) (ov : Over b) :
    fiberTransport C F (β ≫ γ) ov =
    fiberTransport C F β ov ⋙
      fiberTransport C F γ ((Over.map β).obj ov) ⋙
      eqToHom (congrArg F.obj (congrArg (twObjMk' ·) (Category.assoc ov.hom β γ))) := by
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
  · -- Base part: (Over.map (β ≫ γ)).obj x.base = (Over.map γ).obj ((Over.map β).obj x.base)
    exact congrArg (·.obj x.base) (Over.mapComp_eq β γ)
  · -- Fiber part: uses fiberTransport_comp
    simp only [fiberTransport_comp, Functor.comp_obj]
    -- Goal: (eqToHom ...).obj (...) ≍ (...)
    -- (eqToHom h).obj x ≍ x
    exact eqToHom_obj_heq _ _ _ _

/--
The transition functor respects composition: transitioning by `β ≫ γ` equals
composing the transitions by `β` and `γ`.
-/
theorem fiberFunctorTransition_comp {b d e : C} (β : b ⟶ d) (γ : d ⟶ e) :
    fiberFunctorTransition C F (β ≫ γ) =
    fiberFunctorTransition C F β ⋙ fiberFunctorTransition C F γ := by
  apply Functor.ext
  case h_obj => exact fiberFunctorTransitionObj_comp C F β γ
  case h_map =>
    intro x y f
    -- Goal: (fiberFunctorTransition C F (β ≫ γ)).map f =
    --       eqToHom _ ≫ (fiberFunctorTransition C F β ⋙ fiberFunctorTransition C F γ).map f
    --       ≫ eqToHom _
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
      -- LHS: (fiberTransport C F (β ≫ γ) y.base).map f.fiber
      -- RHS: (eqToHoms around (fiberTransport γ).map ((fiberTransport β).map f.fiber))
      -- Apply fiberTransport_comp to convert LHS
      apply HEq.trans
      · exact Cat.functor_map_heq_of_eq_comp_comp_eqToHom
          (fiberTransport C F (β ≫ γ) y.base)
          (fiberTransport C F β y.base)
          (fiberTransport C F γ ((Over.map β).obj y.base))
          _ (fiberTransport_comp C F β γ y.base) f.fiber
      -- Goal: (fiberTransport γ).map ((fiberTransport β).map f.fiber) ≍ RHS
      -- RHS: ((restrictToFiber C F e).map (eqToHom _).base).map
      --        (eqToHom _ ≫ (fiberTransport γ).map (eqToHom _ ≫ (fiberTransport β).map f.fiber))
      -- Work on RHS by stripping eqToHom layers
      apply HEq.symm
      -- Strip leading eqToHoms
      apply HEq.trans (eqToHom_comp_heq _ _)
      apply HEq.trans (eqToHom_comp_heq _ _)
      apply HEq.trans (comp_eqToHom_heq _ _)
      -- Goal: ((restrictToFiber C F e).map (eqToHom _).base).map
      --         (eqToHom _ ≫ (fiberTransport γ).map (eqToHom _ ≫ (fiberTransport β).map f.fiber))
      --   ≍ (fiberTransport γ).map ((fiberTransport β).map f.fiber)
      -- The outer layer is (restrictToFiber C F e).map applied to (eqToHom _).base
      -- (eqToHom _).base = eqToHom _, so (restrictToFiber C F e).map (eqToHom _) = eqToHom _
      -- Thus the outer application is (eqToHom _).map (...)
      -- Goal: ((restrictToFiber C F e).map (eqToHom _).base).map
      --         (eqToHom _ ≫ (fiberTransport γ).map (eqToHom _ ≫ (fiberTransport β).map f.fiber))
      --   ≍ (fiberTransport γ).map ((fiberTransport β).map f.fiber)
      -- (eqToHom _).base in Grothendieck = eqToHom by Grothendieck.eqToHom_base'
      -- Then (restrictToFiber C F e).map (eqToHom _) = eqToHom by eqToHom_map
      -- So the outer layer is (eqToHom _).map (...)
      rw [Grothendieck.eqToHom_base', eqToHom_map]
      -- Goal: (eqToHom _).map (eqToHom _ ≫ (fiberTransport γ).map
      --       (eqToHom _ ≫ (fiberTransport β).map f.fiber))
      --   ≍ (fiberTransport γ).map ((fiberTransport β).map f.fiber)
      apply HEq.trans (Cat.eqToHom_map_heq _ _)
      apply HEq.trans (eqToHom_comp_heq _ _)
      -- Goal: (fiberTransport γ).map (eqToHom _ ≫ (fiberTransport β).map f.fiber)
      --   ≍ (fiberTransport γ).map ((fiberTransport β).map f.fiber)
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

/--
The oppositized transition functor respects composition.
-/
theorem fiberFunctorTransitionOp_comp {b d e : C} (β : b ⟶ d) (γ : d ⟶ e) :
    fiberFunctorTransitionOp C F (β ≫ γ) =
    fiberFunctorTransitionOp C F β ⋙ fiberFunctorTransitionOp C F γ := by
  apply Functor.ext
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
      have hOp : Cat.opFunctor'.map (fiberTransport C F (β ≫ γ) y.base) =
          Cat.opFunctor'.map (fiberTransport C F β y.base) ⋙
          Cat.opFunctor'.map (fiberTransport C F γ ((Over.map β).obj y.base)) ⋙
          eqToHom (congrArg Cat.opFunctor'.obj (congrArg F.obj
            (congrArg (twObjMk' ·) (Category.assoc y.base.hom β γ)))) := by
        simp only [h, Cat.opFunctor', Functor.op'_comp, Cat.Functor.op'_eqToHom]
      apply HEq.trans
      · exact Cat.functor_map_heq_of_eq_comp_comp_eqToHom
          (Cat.opFunctor'.map (fiberTransport C F (β ≫ γ) y.base))
          (Cat.opFunctor'.map (fiberTransport C F β y.base))
          (Cat.opFunctor'.map (fiberTransport C F γ ((Over.map β).obj y.base)))
          _ hOp f.fiber
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
  map β := fiberFunctorTransitionOp C F β
  map_id _ := fiberFunctorTransitionOp_id C F
  map_comp β γ := fiberFunctorTransitionOp_comp C F β γ

/--
The fiber functor `fiberFunctor F : C ⥤ Cat` assigns to each object `b : C`
the Grothendieck construction of `F` restricted to the fiber over `b`.
Morphisms `β : b ⟶ d` are sent to the transition functors.
-/
def fiberFunctor : C ⥤ Cat where
  obj b := Cat.of (Grothendieck (restrictToFiber C F b))
  map β := fiberFunctorTransition C F β
  map_id _ := fiberFunctorTransition_id C F
  map_comp β γ := fiberFunctorTransition_comp C F β γ

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
      ((restrictToFiber C F b).map f.base |>.obj y.fiber) =
    ((restrictToFiber C F d).map ((Over.map β).map f.base)).obj
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

theorem innerFiberContraTransition_id (b : C) :
    innerFiberContraTransition C F (𝟙 b) = 𝟭 (innerFiberContra C F b) := by
  fapply Functor.ext
  · exact innerFiberContraTransitionObj_id C F
  · intro x y f
    refine GrothendieckContra'.ext _ _ ?w_base ?w_fiber
    case w_base =>
      simp only [innerFiberContraTransition, innerFiberContraTransitionHom, Functor.id_map]
      rw [Functor.congr_hom (Over.mapId_eq b) f.base, Functor.id_map]
      simp only [innerFiberContraCategory, GrothendieckContra'.GrothendieckContraInst',
                 GrothendieckContra'.comp_base]
      conv_rhs => rw [GrothendieckContra'.base_eqToHom, GrothendieckContra'.base_eqToHom]
    case w_fiber =>
      -- LHS.fiber ≫ eqToHom _ = RHS.fiber (from GrothendieckContra'.ext)
      simp only [innerFiberContraTransition, innerFiberContraTransitionHom, Functor.id_map]
      -- Goal: ((fiberTransport C F (𝟙 b) x.base).map f.fiber ≫ eqToHom _) ≫ eqToHom _ =
      --   (eqToHom _ ≫ f ≫ eqToHom _).fiber
      apply eq_of_heq
      -- Strip the two trailing eqToHom from LHS
      apply HEq.trans (comp_eqToHom_heq _ _)
      apply HEq.trans (comp_eqToHom_heq _ _)
      -- Goal: (fiberTransport C F (𝟙 b) x.base).map f.fiber ≍ RHS.fiber
      have hMap := Cat.functor_map_heq_of_eq_eqToHom
        (fiberTransport_id_cat_eq C F x.base).symm
        (fiberTransport C F (𝟙 b) x.base)
        (fiberTransport_id C F x.base)
        f.fiber
      apply HEq.trans hMap
      -- Goal: f.fiber ≍ (eqToHom _ ≫ f ≫ eqToHom _).fiber
      apply HEq.symm
      -- Goal: (eqToHom _ ≫ f ≫ eqToHom _).fiber ≍ f.fiber
      -- Use the lemma that (eqToHom _ ≫ f ≫ eqToHom _).fiber ≍ f.fiber
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

theorem innerFiberContraTransition_comp {b d e : C} (β : b ⟶ d) (γ : d ⟶ e) :
    innerFiberContraTransition C F (β ≫ γ) =
    innerFiberContraTransition C F β ⋙ innerFiberContraTransition C F γ := by
  fapply Functor.ext
  · exact innerFiberContraTransitionObj_comp C F β γ
  · intro x y f
    refine GrothendieckContra'.ext _ _ ?w_base ?w_fiber
    case w_base =>
      unfold innerFiberContraTransition innerFiberContraTransitionHom
      simp only [Functor.comp_map]
      rw [Functor.congr_hom (Over.mapComp_eq β γ) f.base, Functor.comp_map]
      simp only [innerFiberContraCategory, GrothendieckContra'.GrothendieckContraInst',
                 GrothendieckContra'.comp_base]
      conv_rhs => rw [GrothendieckContra'.base_eqToHom, GrothendieckContra'.base_eqToHom]
    case w_fiber =>
      unfold innerFiberContraTransition innerFiberContraTransitionHom
      simp only [Functor.comp_map]
      apply eq_of_heq
      -- Strip trailing eqToHoms from LHS
      apply HEq.trans (comp_eqToHom_heq _ _)
      apply HEq.trans (comp_eqToHom_heq _ _)
      -- LHS: (fiberTransport C F (β ≫ γ) x.base).map f.fiber
      -- Use fiberTransport_comp to decompose this
      apply HEq.trans
      · exact Cat.functor_map_heq_of_eq_comp_comp_eqToHom
          (fiberTransport C F (β ≫ γ) x.base)
          (fiberTransport C F β x.base)
          (fiberTransport C F γ ((Over.map β).obj x.base))
          _ (fiberTransport_comp C F β γ x.base) f.fiber
      -- LHS: (fiberTransport γ).map ((fiberTransport β).map f.fiber)
      -- RHS: (eqToHom ≫ middle_morph ≫ eqToHom).fiber
      apply HEq.symm
      apply HEq.trans (GrothendieckContra'.conj_eqToHom_fiber_heq _ _ _)
      -- RHS is now middle_morph.fiber
      -- middle_morph = { base := ..., fiber := (fiberTransport γ).map (...) ≫ eqToHom }
      -- .fiber extracts this fiber field
      simp only [innerFiberContraTransitionObj]
      -- Strip trailing eqToHom from RHS fiber
      apply HEq.trans (comp_eqToHom_heq _ _)
      -- RHS: (fiberTransport γ).map ((fiberTransport β).map f.fiber ≫ eqToHom)
      -- Use Functor.map_comp_eqToHom_heq to strip the eqToHom inside
      exact Functor.map_comp_eqToHom_heq _ _ _

/--
The contravariant fiber functor using `GrothendieckContra'` for the inner layer.
For each `b : C`, this assigns the category `innerFiberContra C F b`.
-/
def fiberFunctorContra : C ⥤ Cat where
  obj b := Cat.of (innerFiberContra C F b)
  map β := innerFiberContraTransition C F β
  map_id b := innerFiberContraTransition_id C F b
  map_comp β γ := innerFiberContraTransition_comp C F β γ

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
    ((restrictToFiber C F y.base).map f.fiber.base).obj y.fiber.fiber :=
  f.fiber.fiber

/--
The type of the fiber morphism extracted from `ConnectedGrothendieckContra`.
-/
def connGrothendieckContraFiberMorphType {x y : ConnectedGrothendieckContra C F}
    (f : x ⟶ y) : Type _ :=
  (innerFiberContraTransitionObj C F f.base x.fiber).fiber ⟶
    ((restrictToFiber C F y.base).map f.fiber.base).obj y.fiber.fiber

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
    ((restrictToFiber C F y.base).map f.fiber.base).obj y.fiber.fiber =
    (F.map ((overOpToTwistedArrow C y.base).map f.fiber.base)).obj y.fiber.fiber := rfl

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
      (((fiberFunctorContra C F).map f.base).obj x.fiber).base :=
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

/--
The target object in TwistedArrow for the target of `f.fiber.fiber`.
-/
theorem overOpToTwistedArrow_map_target {x y : ConnectedGrothendieckContra C F}
    (f : x ⟶ y) :
    (overOpToTwistedArrow C y.base).obj
      (innerFiberContraTransitionObj C F f.base x.fiber).base =
    twObjMk' (x.fiber.base.hom ≫ f.base) := by
  simp only [innerFiberContraTransitionObj, Over.map_obj_hom, overOpToTwistedArrow]

/--
The fiberMorph source category.
-/
theorem connGrothendieckContra_fiberMorph_source_cat {x y : ConnectedGrothendieckContra C F}
    (f : x ⟶ y) :
    connGrothendieckDiagCod C (twObjMk' x.fiber.base.hom) f.base =
    twObjMk' (x.fiber.base.hom ≫ f.base) := by
  simp only [connGrothendieckDiagCod, twObjMk'_arr]

/--
The fiberMorph target category before eqToHom transport.
-/
theorem connGrothendieckContra_fiberMorph_target_cat {x y : ConnectedGrothendieckContra C F}
    (f : x ⟶ y) :
    connGrothendieckDiagDom C (twObjMk' y.fiber.base.hom) f.fiber.base.left =
    twObjMk' (f.fiber.base.left ≫ y.fiber.base.hom) := by
  simp only [connGrothendieckDiagDom, twObjMk'_arr]

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
    fiberFunctorContra, Functor.id_obj, innerFiberContraTransition, innerFiberContraTransitionObj,
    Over.map_obj_left]

/--
The codomain of DiagDom equals the codomain of DiagCod (both are `y.base`).
-/
theorem twCod'_diagDom_eq_diagCod {x y : ConnectedGrothendieckContra C F} (f : x ⟶ y) :
    twCod' (connGrothendieckDiagDom C (twObjMk' y.fiber.base.hom) f.fiber.base.left) =
    twCod' (connGrothendieckDiagCod C (twObjMk' x.fiber.base.hom) f.base) := by
  simp only [connGrothendieckDiagDom, connGrothendieckDiagCod, twObjMk'_arr, twObjMk'_cod]
  rfl

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
    -- Goal: id f.fiber.base.left = eqToHom _ ≫ f.fiber.base.left
    -- The eqToHom is from congrArg twDom' of fiberMorph_diag_tw_eq.symm
    -- Since twDom' DiagDom = twDom' DiagCod (both = x.fiber.base.left),
    -- the eqToHom simplifies to identity
    simp only [connGrothendieckDiagDom, twObjMk'_dom, twObjMk'_arr, fiberFunctorContra,
      Functor.id_obj, eqToHom_refl, Category.id_comp]
    rfl
  · simp only [twCodArr'_comp, twCodArr'_eqToHom, connGrothendieckTwMorphDom,
      overOpToTwistedArrow, twHomMk'_codArr, twObjMk'_cod]
    -- Goal: 𝟙 y.base = 𝟙 y.base ≫ eqToHom _
    -- Since twCod' DiagDom = twCod' DiagCod (both = y.base),
    -- the eqToHom simplifies to identity
    simp only [connGrothendieckDiagDom, twObjMk'_cod, twObjMk'_arr, Functor.fromPUnit,
      eqToHom_refl, Category.comp_id]
    rfl

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
    -- Rewrite source using fiberTransportTwMorph = TwMorphCod
    rw [← fiberTransportTwMorph_eq_connGrothendieckTwMorphCod (β := f.base)]
    -- Now source matches source of f.fiber.fiber
    -- Use the equality of twisted arrow morphisms to rewrite the target
    rw [← overOpToTwistedArrow_map_eq_twMorphDom_comp_eqToHom]
    -- Now the goal matches f.fiber.fiber exactly
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
     (eqToHom (congrArg F.obj (twObjMk'_twArr' x.arrow).symm)).obj x.fiber⟩

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
    (((fiberFunctorContra C F).map f.codArr).obj
      (connGrothendieckObjToContraObj C F x).fiber).fiber =
    (F.map (connGrothendieckTwMorphCod C x.arrow f.codArr)).obj x.fiber := by
  simp only [fiberFunctorContra, connGrothendieckObjToContraObj,
    innerFiberContraTransition, innerFiberContraTransitionObj]
  simp only [fiberTransport, fiberTransportTwMorph, connGrothendieckTwMorphCod, Over.mk_hom]
  rfl

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
    -- Unfold definitions but keep overOpToTwistedArrow and
    -- connGrothendieckHomToContraInnerBase folded for the rewrite
    simp only [fiberFunctorContra, connGrothendieckObjToContraObj,
      innerFiberContraTransition, innerFiberContraTransitionObj,
      fiberTransport, restrictToFiber, Functor.comp_obj, Functor.comp_map]
    -- Rewrite source using fiberTransportTwMorph = connGrothendieckTwMorphCod
    rw [fiberTransportTwMorph_eq_connGrothendieckTwMorphCod']
    -- Rewrite target using overOpToTwArr_map = TwMorphDom ≫ eqToHom
    rw [overOpToTwArr_map_innerBase_eq]
    -- Now simplify twObjMk'_twArr' to get x.arrow from
    -- twObjMk' (Over.mk (twArr' x.arrow)).hom
    simp only [Over.mk_hom, twObjMk'_twArr']
    exact f.fiberMorph

/--
Round-trip: converting a `ConnGrothendieckHom` to `ConnectedGrothendieckContra` morphism
and back gives the original morphism (up to the object round-trip equality).
-/
theorem connGrothendieckHom_roundtrip {x y : ConnGrothendieckObj C F}
    (f : ConnGrothendieckHom C F x y) :
    HEq (connGrothendieckContraHomToHom C F (connGrothendieckHomToContraHom C F f)) f := by
  -- The LHS is a ConnGrothendieckHom between (roundtrip x) and (roundtrip y)
  -- The RHS is a ConnGrothendieckHom between x and y
  -- These are HEq by the roundtrip equalities
  have hx : connGrothendieckContraObjToObj C F (connGrothendieckObjToContraObj C F x) = x :=
    connGrothendieckObj_contraRoundtrip C F x
  have hy : connGrothendieckContraObjToObj C F (connGrothendieckObjToContraObj C F y) = y :=
    connGrothendieckObj_contraRoundtrip C F y
  cases hx
  cases hy
  apply heq_of_eq
  -- Unfold the conversions
  simp only [connGrothendieckContraHomToHom, connGrothendieckHomToContraHom,
    connGrothendieckHomToContraInnerBase, Over.homMk_left]
  -- Decompose f and prove by structure equality
  obtain ⟨domArr, codArr, square_comm, fiberMorph⟩ := f
  -- Goal now: {domArr, codArr, ⋯, id (...)} = {domArr, codArr, square_comm, fiberMorph}
  -- domArr, codArr match; square_comm is proof irrelevant
  -- fiberMorph has a chain of Eq.mpr from the convert tactic
  congr 1
  -- Simplify the id wrappers first
  simp only [id_eq]
  -- Use eq_of_heq and cast_heq to show the mpr transports are HEq to identity
  -- Each Eq.mpr h x is equivalent to cast h.symm x which is HEq to x
  apply eq_of_heq
  refine HEq.trans (cast_heq _ _) ?_
  exact cast_heq _ _

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
  -- Unfold the conversions
  simp only [connGrothendieckHomToContraHom, connGrothendieckContraHomToHom,
    connGrothendieckHomToContraInnerBase]
  -- Use Grothendieck.ext - need to be careful about goal ordering
  refine Grothendieck.ext _ _ ?_ ?_
  · -- Base equality - trivial
    rfl
  · -- Fiber morphism equality
    -- Need to show eqToHom ≫ constructed_morphism = f.fiber
    -- The eqToHom is rfl since the base components are definitionally equal
    simp only [eqToHom_refl, Category.id_comp]
    -- Now goal is the constructed morphism = f.fiber
    refine GrothendieckContra'.ext _ _ ?_ ?_
    · -- Inner base
      ext
      rfl
    · -- Inner fiber: need to show m.fiber ≫ eqToHom _ = f.fiber.fiber
      -- Since bases match, the eqToHom should be rfl
      simp only [eqToHom_refl, Category.comp_id]
      -- Goal: id (Eq.mpr ... (Eq.mpr ... f.fiber.fiber)) = f.fiber.fiber
      -- First strip id wrappers
      simp only [id_eq]
      -- Goal is now: mpr (mpr (mpr (mpr f.fiber.fiber))) = f.fiber.fiber
      -- Local helper: Eq.mpr h b ≍ b
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
    (((fiberFunctorContra C F).map β).map f).base.left = f.base.left := by
  simp only [fiberFunctorContra, innerFiberContraTransition,
             innerFiberContraTransitionHom_base]
  rfl

/--
For `eqToHom` in `GrothendieckContra'`, the `.base.left` is `eqToHom` in `C`.
-/
lemma grothendieckContra'_eqToHom_base_left {b : C}
    {x y : GrothendieckContra' (restrictToFiber C F b)} (h : x = y) :
    (eqToHom h).base.left = eqToHom (by subst h; rfl) := by
  subst h
  rfl

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
### Contravariant Functor Transformation

We need to transform `G : (TwistedArrow' C)ᵒᵖ' ⥤ Cat` into a covariant functor
`TwistedArrowOp' C ⥤ Cat` for use with `ConnectedGrothendieckContra`.

The approach uses functor composition:
1. `Functor.op' twistedArrowOp'ToTwistedArrow : (TwistedArrowOp' C)ᵒᵖ' ⥤ (TwistedArrow' C)ᵒᵖ'`
2. Compose with `G` to get `(TwistedArrowOp' C)ᵒᵖ' ⥤ Cat`
3. Apply `Cat.postCompOpFunctor'` to flip fiber categories, keeping domain the same
4. Since `(TwistedArrowOp' C)ᵒᵖ' = TwistedArrowOp' C` at the type level, this gives
   the right functor

Note: The domain type `(TwistedArrowOp' C)ᵒᵖ'` is definitionally equal to `TwistedArrowOp' C`
as a type (since `CategoryOp' X = X`), but has reversed morphism directions. However,
`Cat.postCompOpFunctor'` preserves the domain, so we get morphisms going in the
opposite direction from what we need.

Actually, the correct approach is to recognize that:
- `TwistedArrowOp' C = TwistedArrow' (Cᵒᵖ')` definitionally (both types and categories)
- We need a functor `TwistedArrow' (Cᵒᵖ') ⥤ Cat`
- Given `G : (TwistedArrow' C)ᵒᵖ' ⥤ Cat`, we use the equivalence between
  `TwistedArrow' (Cᵒᵖ')` and `(TwistedArrow' C)ᵒᵖ'` (same twisted arrows, opposite morphisms)
-/

/-!
### Direct Presheaf Connected Grothendieck Construction

Rather than trying to transform `G : (TwistedArrow' C)ᵒᵖ' ⥤ Cat` into a covariant
functor, we define the presheaf connected Grothendieck construction directly,
analogous to how `GrothendieckContra'` is defined for presheaves.

The morphism directions in `TwistedArrowOp' C` and
`(TwistedArrow' C)ᵒᵖ'` don't align, so we make a direct definition.
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
  fiberMorph : X.fiber ⟶ (G.map twMorph).obj Y.fiber

namespace ConnGrothendieckPresheafHom

variable {C G}

/-- The fiber codomain equality for identity morphisms -/
theorem id_fiber_cod_eq (X : ConnGrothendieckPresheafObj C G) :
    (G.map (𝟙 X.tw)).obj X.fiber = X.fiber :=
  (Functor.congr_obj (G.map_id X.tw).symm X.fiber).symm

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
    (G.map f.twMorph).obj ((G.map g.twMorph).obj Z.fiber) =
    (G.map (@CategoryStruct.comp (TwistedArrow' C) _ _ _ _ f.twMorph g.twMorph)).obj Z.fiber := by
  -- In (TwistedArrow' C)ᵒᵖ', g.twMorph ≫ f.twMorph is composable (Z→Y→X in op' sense)
  -- and definitionally equals f.twMorph ≫ g.twMorph in TwistedArrow' C
  exact (Functor.congr_obj (G.map_comp g.twMorph f.twMorph) Z.fiber).symm

/-- Composition of morphisms in the presheaf connected Grothendieck construction -/
def comp {X Y Z : ConnGrothendieckPresheafObj C G}
    (f : ConnGrothendieckPresheafHom C G X Y)
    (g : ConnGrothendieckPresheafHom C G Y Z) :
    ConnGrothendieckPresheafHom C G X Z where
  twMorph := @CategoryStruct.comp (TwistedArrow' C) _ _ _ _ f.twMorph g.twMorph
  fiberMorph :=
    f.fiberMorph ≫
    (G.map f.twMorph).map g.fiberMorph ≫
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

attribute [local simp] eqToHom_map Functor.map_id

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
      -- Goal: eqToHom _ ≫ (G.map (𝟙 X.tw)).map f.fiberMorph ≫ eqToHom _ = f.fiberMorph
      -- Use G.map_id to rewrite G.map (𝟙 X.tw) to 𝟙 (G.obj X.tw)
      simp only [Category.assoc]
      slice_lhs 2 3 => erw [Functor.congr_hom (G.map_id X.tw) f.fiberMorph]
      -- Goal: eqToHom _ ≫ eqToHom _ ≫ (𝟙 (G.obj X.tw)).map f.fiberMorph = f.fiberMorph
      cat_disch
  comp_id {X Y} f := by
    apply ConnGrothendieckPresheafHom.ext
    case h_tw =>
      simp only [ConnGrothendieckPresheafHom.comp, ConnGrothendieckPresheafHom.id]
      exact @Category.comp_id (TwistedArrow' C) _ _ _ f.twMorph
    case h_fiber =>
      simp only [ConnGrothendieckPresheafHom.comp, ConnGrothendieckPresheafHom.id]
      -- Goal: f.fiberMorph ≫ (G.map f.twMorph).map (eqToHom _) ≫ eqToHom _ = f.fiberMorph
      -- Use eqToHom_map to convert the functor map of eqToHom to eqToHom
      simp only [eqToHom_map, Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
  assoc f g h := by
    apply ConnGrothendieckPresheafHom.ext
    case h_tw =>
      simp only [ConnGrothendieckPresheafHom.comp]
      exact @Category.assoc (TwistedArrow' C) _ _ _ _ _ f.twMorph g.twMorph h.twMorph
    case h_fiber =>
      simp only [ConnGrothendieckPresheafHom.comp, Category.assoc]
      -- Use G.map_comp to rewrite G.map (f ≫ g) to G.map g ⋙ G.map f
      slice_lhs 3 4 =>
        erw [Functor.congr_hom (G.map_comp g.twMorph f.twMorph) h.fiberMorph]
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

end GebLean
