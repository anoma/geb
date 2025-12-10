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

end GebLean
