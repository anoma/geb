import GebLean.Polynomial
import GebLean.Utilities.Equalities
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers

/-!
# Universal Morphisms for Polynomial Functors

This module defines universal constructions (limits and colimits) in
the vertical category `PolyFunctorBetweenCat X Y` of polynomial
functors between slice categories `Over X` and `Over Y`.

## Main definitions

* `polyBetweenProd` - Arbitrary-indexed products
* `polyBetweenCoprod` - Arbitrary-indexed coproducts

## References

* Section 5.4 of "Polynomial Functors: A Mathematical Theory of
  Interaction" (Niu & Spivak, 2024)
-/

namespace GebLean

open CategoryTheory CategoryTheory.Limits

universe u

/-! ## Products of polynomial functors

For a family `F : I → PolyFunctorBetweenCat X Y`, the product has:

- **Positions** at `y`: `∀ i, polyBetweenIndex (F i) y`
- **Family** at position tuple `p`: the coproduct over `I` of the
  families `polyBetweenFamily (F i) y (p i)`

The projection `π_j` reindexes by evaluating the tuple at `j`,
with fiber morphism given by the coproduct injection.
-/

section Products

variable {X Y : Type u}

/--
The position type of the product polynomial functor.
At each `y : Y`, a position is a tuple assigning a position
of `F i` for each index `i`.
-/
def polyBetweenProdPos (I : Type u)
    (F : I → PolyFunctorBetweenCat X Y) (y : Y) :
    Type u :=
  ∀ i, polyBetweenIndex X Y (F i) y

/--
The family (directions) of the product polynomial functor.
At position-tuple `p`, the representing object is the
coproduct `Σ i, family_i(y)(p(i))` in `Over X`.
-/
def polyBetweenProdDir (I : Type u)
    (F : I → PolyFunctorBetweenCat X Y) (y : Y)
    (p : polyBetweenProdPos I F y) : Over X :=
  ∐' (fun i => polyBetweenFamily X Y (F i) y (p i))

/--
The product polynomial functor for a family indexed by `I`.
-/
def polyBetweenProd (I : Type u)
    (F : I → PolyFunctorBetweenCat X Y) :
    PolyFunctorBetweenCat X Y :=
  fun y => ccrObjMk (polyBetweenProdDir I F y)

/--
The projection's action on positions: evaluates the
position-tuple at index `j`.
-/
def polyBetweenProjReindex (I : Type u)
    (F : I → PolyFunctorBetweenCat X Y) (j : I) (y : Y)
    (p : polyBetweenProdPos I F y) :
    polyBetweenIndex X Y (F j) y :=
  p j

/--
The projection's action on directions: the coproduct
injection at index `j`.
-/
def polyBetweenProjFiber (I : Type u)
    (F : I → PolyFunctorBetweenCat X Y) (j : I) (y : Y)
    (p : polyBetweenProdPos I F y) :
    polyBetweenFamily X Y (F j) y
      (polyBetweenProjReindex I F j y p) ⟶
    polyBetweenProdDir I F y p :=
  CoprodData.inj
    (fun i => polyBetweenFamily X Y (F i) y (p i)) j

/--
The projection morphism from the product to the `j`-th factor.
-/
def polyBetweenProj (I : Type u)
    (F : I → PolyFunctorBetweenCat X Y) (j : I) :
    polyBetweenProd I F ⟶ F j :=
  fun y => ccrHomMk
    (polyBetweenProjReindex I F j y)
    (polyBetweenProjFiber I F j y)

/--
The lift's action on positions: builds a position-tuple
by applying each `m_i`'s reindexing.
-/
def polyBetweenProdLiftReindex (I : Type u)
    (F : I → PolyFunctorBetweenCat X Y)
    (Q : PolyFunctorBetweenCat X Y)
    (m : ∀ i, Q ⟶ F i) (y : Y)
    (q : polyBetweenIndex X Y Q y) :
    polyBetweenProdPos I F y :=
  fun i => ccrReindex (m i y) q

/--
The underlying function of the lift's fiber morphism.
Dispatches each `⟨i, e⟩` from the product's coproduct
to the `i`-th component's fiber morphism.
-/
def polyBetweenProdLiftFiberLeft (I : Type u)
    (F : I → PolyFunctorBetweenCat X Y)
    (Q : PolyFunctorBetweenCat X Y)
    (m : ∀ i, Q ⟶ F i) (y : Y)
    (q : polyBetweenIndex X Y Q y)
    (ie : (polyBetweenProdDir I F y
      (polyBetweenProdLiftReindex I F Q m y q)).left) :
    (polyBetweenFamily X Y Q y q).left :=
  match ie with
  | ⟨i, e⟩ => (ccrFiberMor (m i y) q).left e

/--
The commutation proof for the lift's fiber morphism:
the dispatch function commutes with the projection to `X`.
-/
theorem polyBetweenProdLiftFiberComm (I : Type u)
    (F : I → PolyFunctorBetweenCat X Y)
    (Q : PolyFunctorBetweenCat X Y)
    (m : ∀ i, Q ⟶ F i) (y : Y)
    (q : polyBetweenIndex X Y Q y) :
    (polyBetweenFamily X Y Q y q).hom ∘
      polyBetweenProdLiftFiberLeft I F Q m y q =
    (polyBetweenProdDir I F y
      (polyBetweenProdLiftReindex I F Q m y q)).hom := by
  funext ⟨i, e⟩
  exact congrFun (Over.w (ccrFiberMor (m i y) q)) e

/--
The lift's action on directions: at position `q`, dispatches
each tagged element `⟨i, e⟩` from the product's coproduct
family to the `i`-th component's fiber morphism applied
to `e`.
-/
def polyBetweenProdLiftFiber (I : Type u)
    (F : I → PolyFunctorBetweenCat X Y)
    (Q : PolyFunctorBetweenCat X Y)
    (m : ∀ i, Q ⟶ F i) (y : Y)
    (q : polyBetweenIndex X Y Q y) :
    polyBetweenProdDir I F y
      (polyBetweenProdLiftReindex I F Q m y q) ⟶
    polyBetweenFamily X Y Q y q :=
  Over.homMk
    (polyBetweenProdLiftFiberLeft I F Q m y q)
    (polyBetweenProdLiftFiberComm I F Q m y q)

/--
The universal pairing morphism into the product.
Given morphisms `m_i : Q ⟶ F(i)` for each `i`, produce
a morphism `Q ⟶ Π_i F(i)`.
-/
def polyBetweenProdLift (I : Type u)
    (F : I → PolyFunctorBetweenCat X Y)
    (Q : PolyFunctorBetweenCat X Y)
    (m : ∀ i, Q ⟶ F i) :
    Q ⟶ polyBetweenProd I F :=
  fun y => ccrHomMk
    (polyBetweenProdLiftReindex I F Q m y)
    (polyBetweenProdLiftFiber I F Q m y)

/--
The factorization property: composing the lift with a projection
recovers the original morphism.
-/
theorem polyBetweenProdLift_proj (I : Type u)
    (F : I → PolyFunctorBetweenCat X Y)
    (Q : PolyFunctorBetweenCat X Y)
    (m : ∀ i, Q ⟶ F i) (j : I) :
    polyBetweenProdLift I F Q m ≫ polyBetweenProj I F j =
      m j := by
  funext y
  change (polyBetweenProdLift I F Q m y ≫
    polyBetweenProj I F j y) = m j y
  refine ccrHom_ext _ _ rfl ?_
  simp only [eqToHom_refl, Category.comp_id]
  funext q
  change ccrFiberMor
    (polyBetweenProdLift I F Q m y ≫
      polyBetweenProj I F j y) q =
    ccrFiberMor (m j y) q
  simp only [ccrComp_fiberMor]
  dsimp [polyBetweenProdLift, polyBetweenProj,
    polyBetweenProdLiftReindex,
    polyBetweenProdLiftFiber,
    polyBetweenProjReindex, polyBetweenProjFiber]
  ext e
  dsimp [CoprodData.inj, CoprodData.ι,
    polyBetweenProdLiftFiberLeft]

lemma ccrHom_ext_subst
    {C' : Type*} [Category C']
    {x y : CoprodCovarRepCat C'}
    (f g : x ⟶ y)
    (hbase : f.base = g.base)
    (hfiber : ∀ i,
      ccrFiberMor f i =
        eqToHom (congrArg (ccrFamily y)
          (congrFun hbase i)) ≫
        ccrFiberMor g i) : f = g := by
  cases f; cases g; dsimp at hbase
  subst hbase
  congr 1
  funext i
  simp only [eqToHom_refl, Category.id_comp] at hfiber
  exact hfiber i

lemma ccrFiberMor_congr
    {C' : Type*} [Category C']
    {x y : CoprodCovarRepCat C'}
    {f g : x ⟶ y} (h : f = g) (q : ccrIndex x) :
    ccrFiberMor f q =
      eqToHom (congrArg (ccrFamily y)
        (congrFun (congrArg ccrReindex h) q)) ≫
      ccrFiberMor g q := by
  subst h; simp

private lemma eqToHom_coprod_inj
    {I : Type u} {X : Type u}
    {f g : I → Over X}
    (heq : f = g) (j : I) :
    CoprodData.inj f j ≫
      eqToHom (congrArg (∐' ·) heq) =
    eqToHom (congrFun heq j) ≫
      CoprodData.inj g j := by
  subst heq; simp

lemma overCoprod_hom_ext
    {I : Type u} {X : Type u}
    {f : I → Over X} {T : Over X}
    (g₁ g₂ : (∐' f : Over X) ⟶ T)
    (h : ∀ j, CoprodData.inj f j ≫ g₁ =
      CoprodData.inj f j ≫ g₂) :
    g₁ = g₂ := by
  ext ⟨j, e⟩
  exact congrFun (congrArg (·.left) (h j)) e

private lemma prodFiber_inj_comp
    (I : Type u)
    (F : I → PolyFunctorBetweenCat X Y)
    (j : I)
    (Q : PolyFunctorBetweenCat X Y)
    (g : Q ⟶ polyBetweenProd I F)
    (y : Y) (q : ccrIndex (Q y)) :
    CoprodData.inj
      (fun i => polyBetweenFamily X Y (F i) y
        (ccrReindex (g y) q i)) j ≫
    ccrFiberMor (g y) q =
    ccrFiberMor
      (g y ≫ polyBetweenProj I F j y) q := by
  rw [ccrComp_fiberMor]; congr 1

private lemma polyBetweenProdLift_unique_fiber
    (I : Type u)
    (F : I → PolyFunctorBetweenCat X Y)
    (Q : PolyFunctorBetweenCat X Y)
    (m : ∀ i, Q ⟶ F i)
    (h : Q ⟶ polyBetweenProd I F)
    (hfac : ∀ j,
      h ≫ polyBetweenProj I F j = m j)
    (y : Y) (q : ccrIndex (Q y))
    (hbase : (h y).base =
      (polyBetweenProdLift I F Q m y).base) :
    ccrFiberMor (h y) q =
      eqToHom (congrArg
        (ccrFamily (polyBetweenProd I F y))
        (congrFun hbase q)) ≫
      ccrFiberMor
        (polyBetweenProdLift I F Q m y) q := by
  have family_eq :
      (fun i => polyBetweenFamily X Y (F i) y
        (ccrReindex (h y) q i)) =
      (fun i => polyBetweenFamily X Y (F i) y
        (ccrReindex
          (polyBetweenProdLift I F Q m y) q i)) :=
    funext fun i => congrArg _
      (congrFun (congrFun hbase q) i)
  conv_rhs => rw [show eqToHom _ =
    eqToHom (congrArg (∐' ·) family_eq)
    from by congr 1]
  apply overCoprod_hom_ext
  intro j
  rw [prodFiber_inj_comp I F j Q h y q]
  rw [← Category.assoc,
    eqToHom_coprod_inj family_eq j,
    Category.assoc,
    prodFiber_inj_comp I F j Q
      (polyBetweenProdLift I F Q m) y q]
  change ccrFiberMor
      ((h ≫ polyBetweenProj I F j) y) q =
    eqToHom _ ≫ ccrFiberMor
      ((polyBetweenProdLift I F Q m ≫
        polyBetweenProj I F j) y) q
  rw [ccrFiberMor_congr
    (congrFun (hfac j) y) q]
  rw [ccrFiberMor_congr
    (congrFun
      (polyBetweenProdLift_proj I F Q m j)
      y) q]
  simp only [eqToHom_trans_assoc]

/--
Uniqueness of the lift: any morphism `h : Q ⟶ Π_i F(i)`
satisfying `h ≫ π_j = m j` for all `j` equals the
canonical lift.
-/
theorem polyBetweenProdLift_unique (I : Type u)
    (F : I → PolyFunctorBetweenCat X Y)
    (Q : PolyFunctorBetweenCat X Y)
    (m : ∀ i, Q ⟶ F i)
    (h : Q ⟶ polyBetweenProd I F)
    (hfac : ∀ j,
      h ≫ polyBetweenProj I F j = m j) :
    h = polyBetweenProdLift I F Q m := by
  funext y
  change h y = polyBetweenProdLift I F Q m y
  have hbase : (h y).base =
      (polyBetweenProdLift I F Q m y).base := by
    funext q i
    exact congrFun
      (congrArg ccrReindex
        (congrFun (hfac i) y)) q
  exact ccrHom_ext_subst _ _ hbase
    (fun q => polyBetweenProdLift_unique_fiber
      I F Q m h hfac y q hbase)

/--
The product fan for a family of polynomial functors.
-/
def polyBetweenFan (I : Type u)
    (F : I → PolyFunctorBetweenCat X Y) : Fan F :=
  Fan.mk (polyBetweenProd I F) (polyBetweenProj I F)

/--
The product fan is a limit fan.
-/
def polyBetweenIsLimitFan (I : Type u)
    (F : I → PolyFunctorBetweenCat X Y) :
    IsLimit (polyBetweenFan I F) :=
  mkFanLimit (polyBetweenFan I F)
    (fun s => polyBetweenProdLift I F s.pt s.proj)
    (fun s j =>
      polyBetweenProdLift_proj I F s.pt s.proj j)
    (fun s m hm =>
      polyBetweenProdLift_unique I F s.pt s.proj
        m hm)

instance : HasProducts.{u}
    (PolyFunctorBetweenCat.{u, u} X Y) :=
  hasProducts_of_limit_fans
    (fun F => polyBetweenFan _ F)
    (fun F => polyBetweenIsLimitFan _ F)

end Products

/-! ## Coproducts of polynomial functors

For a family `F : I → PolyFunctorBetweenCat X Y`, the coproduct has:

- **Positions** at `y`: `Σ i, polyBetweenIndex (F i) y`
- **Family** at tagged position `⟨i, p⟩`:
  `polyBetweenFamily (F i) y p`

The injection `ι_j` tags positions with `j`, with the identity fiber
morphism. The universal descent dispatches by the tag.
-/

section Coproducts

variable {X Y : Type u}

/--
The position type of the coproduct polynomial functor.
At each `y : Y`, a position is a tagged position `⟨i, p⟩`
where `p` is a position of `F i` at `y`.
-/
def polyBetweenCoprodPos (I : Type u)
    (F : I → PolyFunctorBetweenCat X Y) (y : Y) :
    Type u :=
  Σ i, polyBetweenIndex X Y (F i) y

/--
The family (directions) of the coproduct polynomial functor.
At tagged position `⟨i, p⟩`, the representing object is
`polyBetweenFamily (F i) y p`.
-/
def polyBetweenCoprodDir (I : Type u)
    (F : I → PolyFunctorBetweenCat X Y) (y : Y)
    (p : polyBetweenCoprodPos I F y) : Over X :=
  polyBetweenFamily X Y (F p.1) y p.2

/--
The coproduct polynomial functor for a family indexed by `I`.
-/
def polyBetweenCoprod (I : Type u)
    (F : I → PolyFunctorBetweenCat X Y) :
    PolyFunctorBetweenCat X Y :=
  fun y => ccrObjMk (polyBetweenCoprodDir I F y)

/--
The injection's action on positions: tags a position of `F j`
with the index `j`.
-/
def polyBetweenInjReindex (I : Type u)
    (F : I → PolyFunctorBetweenCat X Y) (j : I) (y : Y)
    (p : polyBetweenIndex X Y (F j) y) :
    polyBetweenCoprodPos I F y :=
  ⟨j, p⟩

/--
The injection's action on directions: the identity morphism,
since the coproduct's family at `⟨j, p⟩` is exactly the
family of `F j` at `p`.
-/
def polyBetweenInjFiber (I : Type u)
    (F : I → PolyFunctorBetweenCat X Y) (j : I) (y : Y)
    (p : polyBetweenIndex X Y (F j) y) :
    polyBetweenCoprodDir I F y
      (polyBetweenInjReindex I F j y p) ⟶
    polyBetweenFamily X Y (F j) y p :=
  𝟙 _

/--
The injection morphism from the `j`-th factor into the coproduct.
-/
def polyBetweenInj (I : Type u)
    (F : I → PolyFunctorBetweenCat X Y) (j : I) :
    F j ⟶ polyBetweenCoprod I F :=
  fun y => ccrHomMk
    (polyBetweenInjReindex I F j y)
    (polyBetweenInjFiber I F j y)

/--
The descent's action on positions: dispatches the tagged
position `⟨i, p⟩` to the `i`-th morphism's reindexing
applied to `p`.
-/
def polyBetweenCoprodDescReindex (I : Type u)
    (F : I → PolyFunctorBetweenCat X Y)
    (Q : PolyFunctorBetweenCat X Y)
    (m : ∀ i, F i ⟶ Q) (y : Y)
    (ip : polyBetweenCoprodPos I F y) :
    polyBetweenIndex X Y Q y :=
  ccrReindex (m ip.1 y) ip.2

/--
The descent's action on directions: at tagged position
`⟨i, p⟩`, applies the `i`-th morphism's fiber morphism.
-/
def polyBetweenCoprodDescFiber (I : Type u)
    (F : I → PolyFunctorBetweenCat X Y)
    (Q : PolyFunctorBetweenCat X Y)
    (m : ∀ i, F i ⟶ Q) (y : Y)
    (ip : polyBetweenCoprodPos I F y) :
    polyBetweenFamily X Y Q y
      (polyBetweenCoprodDescReindex I F Q m y ip) ⟶
    polyBetweenCoprodDir I F y ip :=
  ccrFiberMor (m ip.1 y) ip.2

/--
The universal copairing morphism from the coproduct.
Given morphisms `m_i : F(i) ⟶ Q` for each `i`, produce
a morphism `∐_i F(i) ⟶ Q`.
-/
def polyBetweenCoprodDesc (I : Type u)
    (F : I → PolyFunctorBetweenCat X Y)
    (Q : PolyFunctorBetweenCat X Y)
    (m : ∀ i, F i ⟶ Q) :
    polyBetweenCoprod I F ⟶ Q :=
  fun y => ccrHomMk
    (polyBetweenCoprodDescReindex I F Q m y)
    (polyBetweenCoprodDescFiber I F Q m y)

/--
The factorization property: composing an injection with the
descent recovers the original morphism.
-/
theorem polyBetweenCoprodInj_desc (I : Type u)
    (F : I → PolyFunctorBetweenCat X Y)
    (Q : PolyFunctorBetweenCat X Y)
    (m : ∀ i, F i ⟶ Q) (j : I) :
    polyBetweenInj I F j ≫
      polyBetweenCoprodDesc I F Q m = m j := by
  funext y
  change (polyBetweenInj I F j y ≫
    polyBetweenCoprodDesc I F Q m y) = m j y
  refine ccrHom_ext _ _ rfl ?_
  simp only [eqToHom_refl, Category.comp_id]
  funext q
  change ccrFiberMor
    (polyBetweenInj I F j y ≫
      polyBetweenCoprodDesc I F Q m y) q =
    ccrFiberMor (m j y) q
  simp only [ccrComp_fiberMor]
  dsimp [polyBetweenInj, polyBetweenCoprodDesc,
    polyBetweenInjReindex, polyBetweenInjFiber,
    polyBetweenCoprodDescReindex,
    polyBetweenCoprodDescFiber]
  exact Category.comp_id _

/--
Uniqueness of the descent: any morphism
`h : ∐_i F(i) ⟶ Q` satisfying `ι_j ≫ h = m j` for
all `j` equals the canonical descent.
-/
theorem polyBetweenCoprodDesc_unique (I : Type u)
    (F : I → PolyFunctorBetweenCat X Y)
    (Q : PolyFunctorBetweenCat X Y)
    (m : ∀ i, F i ⟶ Q)
    (h : polyBetweenCoprod I F ⟶ Q)
    (hfac : ∀ j,
      polyBetweenInj I F j ≫ h = m j) :
    h = polyBetweenCoprodDesc I F Q m := by
  funext y
  change h y = polyBetweenCoprodDesc I F Q m y
  have hbase : (h y).base =
      (polyBetweenCoprodDesc I F Q m y).base := by
    funext ⟨j, p⟩
    exact congrFun
      (congrArg ccrReindex
        (congrFun (hfac j) y)) p
  have hfiber : ∀ (ip : polyBetweenCoprodPos I F y),
      ccrFiberMor (h y) ip =
        eqToHom (congrArg
          (ccrFamily (Q y))
          (congrFun hbase ip)) ≫
        ccrFiberMor
          (polyBetweenCoprodDesc I F Q m y) ip := by
    intro ⟨j, p⟩
    have h_comp := ccrFiberMor_congr
      (congrFun (hfac j) y) p
    change ccrFiberMor
      (polyBetweenInj I F j y ≫ h y) p =
      _ at h_comp
    rw [ccrComp_fiberMor] at h_comp
    dsimp [polyBetweenInj, polyBetweenInjReindex,
      polyBetweenInjFiber] at h_comp
    erw [Category.comp_id] at h_comp
    rw [h_comp]
    dsimp [polyBetweenCoprodDesc,
      polyBetweenCoprodDescReindex,
      polyBetweenCoprodDescFiber]
  exact ccrHom_ext_subst _ _ hbase hfiber

/--
The coproduct cofan for a family of polynomial functors.
-/
def polyBetweenCofan (I : Type u)
    (F : I → PolyFunctorBetweenCat X Y) :
    Cofan F :=
  Cofan.mk (polyBetweenCoprod I F) (polyBetweenInj I F)

/--
The coproduct cofan is a colimit cofan.
-/
def polyBetweenIsColimitCofan (I : Type u)
    (F : I → PolyFunctorBetweenCat X Y) :
    IsColimit (polyBetweenCofan I F) :=
  mkCofanColimit (polyBetweenCofan I F)
    (fun s =>
      polyBetweenCoprodDesc I F s.pt s.inj)
    (fun s j =>
      polyBetweenCoprodInj_desc I F s.pt s.inj j)
    (fun s m hm =>
      polyBetweenCoprodDesc_unique I F s.pt s.inj
        m hm)

instance : HasCoproducts.{u}
    (PolyFunctorBetweenCat.{u, u} X Y) :=
  hasCoproducts_of_colimit_cofans
    (fun F => polyBetweenCofan _ F)
    (fun F => polyBetweenIsColimitCofan _ F)

end Coproducts

/-! ## Equalizers of polynomial functors

For morphisms `f, g : P ⟶ Q` in `PolyFunctorBetweenCat X Y`, the
equalizer has:

- **Positions** at `y`: `{ i : ccrIndex (P y) | ccrReindex (f y) i =
  ccrReindex (g y) i }` (positions where `f` and `g` agree on
  reindexing)
- **Directions** at `⟨i, h⟩`: coequalizer of the two fiber
  morphisms from `ccrFamily (Q y) (ccrReindex (f y) i)` to
  `ccrFamily (P y) i`
-/

section Equalizers

variable {X Y : Type u}
variable {P Q : PolyFunctorBetweenCat.{u, u} X Y}
  (f g : P ⟶ Q)

/--
The position type of the equalizer: positions of `P` at `y`
where `f` and `g` agree on reindexing.
-/
def polyBetweenEqPos (y : Y) : Type u :=
  { i : ccrIndex (P y) //
    ccrReindex (f y) i = ccrReindex (g y) i }

/--
The first fiber morphism for the equalizer's direction
coequalizer: `ccrFiberMor (f y) i`.
-/
def polyBetweenEqFiberα (y : Y)
    (ip : polyBetweenEqPos f g y) :
    ccrFamily (Q y) (ccrReindex (f y) ip.val) ⟶
    ccrFamily (P y) ip.val :=
  ccrFiberMor (f y) ip.val

/--
The second fiber morphism for the equalizer's direction
coequalizer: `eqToHom (h) ≫ ccrFiberMor (g y) i`, where
`h` transports along the position equality.
-/
def polyBetweenEqFiberβ (y : Y)
    (ip : polyBetweenEqPos f g y) :
    ccrFamily (Q y) (ccrReindex (f y) ip.val) ⟶
    ccrFamily (P y) ip.val :=
  eqToHom (congrArg (ccrFamily (Q y)) ip.property) ≫
    ccrFiberMor (g y) ip.val

/--
The direction (family) of the equalizer at position `ip`:
the coequalizer of the two fiber morphisms in `Over X`.
-/
def polyBetweenEqDir (y : Y)
    (ip : polyBetweenEqPos f g y) : Over X :=
  overCoeqObj
    (polyBetweenEqFiberα f g y ip)
    (polyBetweenEqFiberβ f g y ip)

/--
The equalizer polynomial functor for morphisms `f g : P ⟶ Q`.
-/
def polyBetweenEq : PolyFunctorBetweenCat X Y :=
  fun y => ccrObjMk (polyBetweenEqDir f g y)

/--
The inclusion morphism's action on positions: subtype
projection.
-/
def polyBetweenEqInclReindex (y : Y)
    (ip : polyBetweenEqPos f g y) :
    ccrIndex (P y) :=
  ip.val

/--
The inclusion morphism's action on directions: the
coequalizer projection.
-/
def polyBetweenEqInclFiber (y : Y)
    (ip : polyBetweenEqPos f g y) :
    ccrFamily (P y) (polyBetweenEqInclReindex f g y ip) ⟶
    polyBetweenEqDir f g y ip :=
  overCoeqπ
    (polyBetweenEqFiberα f g y ip)
    (polyBetweenEqFiberβ f g y ip)

/--
The inclusion morphism from the equalizer into `P`.
-/
def polyBetweenEqIncl : polyBetweenEq f g ⟶ P :=
  fun y => ccrHomMk
    (polyBetweenEqInclReindex f g y)
    (polyBetweenEqInclFiber f g y)

/--
The fork condition: `polyBetweenEqIncl f g ≫ f =
polyBetweenEqIncl f g ≫ g`.
-/
theorem polyBetweenEqIncl_condition :
    polyBetweenEqIncl f g ≫ f =
      polyBetweenEqIncl f g ≫ g := by
  funext y
  change polyBetweenEqIncl f g y ≫ f y =
    polyBetweenEqIncl f g y ≫ g y
  refine ccrHom_ext_subst _ _ ?_ ?_
  · funext ip
    exact ip.property
  · intro ip
    simp only [ccrComp_fiberMor]
    dsimp [polyBetweenEqIncl,
      polyBetweenEqInclReindex,
      polyBetweenEqInclFiber]
    exact overCoeq_condition
      (polyBetweenEqFiberα f g y ip)
      (polyBetweenEqFiberβ f g y ip)

/--
The lift's action on positions: builds a position in the
equalizer from the hypothesis that `h ≫ f = h ≫ g`.
-/
def polyBetweenEqLiftReindex
    {R : PolyFunctorBetweenCat.{u, u} X Y}
    (h : R ⟶ P) (w : h ≫ f = h ≫ g)
    (y : Y) (q : ccrIndex (R y)) :
    polyBetweenEqPos f g y :=
  ⟨ccrReindex (h y) q,
    congrFun (congrArg ccrReindex
      (congrFun w y)) q⟩

/--
The fiber morphism `ccrFiberMor (h y) q` coequalizes the
two fiber morphisms of the equalizer.
-/
private theorem polyBetweenEqLiftFiber_coeq
    {R : PolyFunctorBetweenCat.{u, u} X Y}
    (h : R ⟶ P) (w : h ≫ f = h ≫ g)
    (y : Y) (q : ccrIndex (R y)) :
    polyBetweenEqFiberα f g y
      (polyBetweenEqLiftReindex f g h w y q) ≫
      ccrFiberMor (h y) q =
    polyBetweenEqFiberβ f g y
      (polyBetweenEqLiftReindex f g h w y q) ≫
      ccrFiberMor (h y) q := by
  dsimp [polyBetweenEqFiberα, polyBetweenEqFiberβ,
    polyBetweenEqLiftReindex]
  rw [Category.assoc,
    ← ccrComp_fiberMor (h y) (f y),
    ← ccrComp_fiberMor (h y) (g y)]
  exact ccrFiberMor_congr (congrFun w y) q

/--
The lift's action on directions: factors `ccrFiberMor (h y) q`
through the coequalizer.
-/
def polyBetweenEqLiftFiber
    {R : PolyFunctorBetweenCat.{u, u} X Y}
    (h : R ⟶ P) (w : h ≫ f = h ≫ g)
    (y : Y) (q : ccrIndex (R y)) :
    polyBetweenEqDir f g y
      (polyBetweenEqLiftReindex f g h w y q) ⟶
    ccrFamily (R y) q :=
  overCoeqDesc
    (polyBetweenEqFiberα f g y _)
    (polyBetweenEqFiberβ f g y _)
    (ccrFiberMor (h y) q)
    (polyBetweenEqLiftFiber_coeq f g h w y q)

/--
The universal lift into the equalizer.
-/
def polyBetweenEqLift
    {R : PolyFunctorBetweenCat.{u, u} X Y}
    (h : R ⟶ P) (w : h ≫ f = h ≫ g) :
    R ⟶ polyBetweenEq f g :=
  fun y => ccrHomMk
    (polyBetweenEqLiftReindex f g h w y)
    (polyBetweenEqLiftFiber f g h w y)

/--
Factorization: `polyBetweenEqLift h w ≫ polyBetweenEqIncl f g = h`.
-/
theorem polyBetweenEqLift_incl
    {R : PolyFunctorBetweenCat.{u, u} X Y}
    (h : R ⟶ P) (w : h ≫ f = h ≫ g) :
    polyBetweenEqLift f g h w ≫
      polyBetweenEqIncl f g = h := by
  funext y
  change polyBetweenEqLift f g h w y ≫
    polyBetweenEqIncl f g y = h y
  refine ccrHom_ext _ _ rfl ?_
  simp only [eqToHom_refl, Category.comp_id]
  funext q
  change ccrFiberMor
    (polyBetweenEqLift f g h w y ≫
      polyBetweenEqIncl f g y) q =
    ccrFiberMor (h y) q
  simp only [ccrComp_fiberMor]
  dsimp [polyBetweenEqLift, polyBetweenEqIncl,
    polyBetweenEqLiftReindex,
    polyBetweenEqLiftFiber,
    polyBetweenEqInclReindex,
    polyBetweenEqInclFiber]
  exact overCoeq_fac _ _ _ _

/--
Naturality of `overCoeqπ` with respect to `eqToHom`
transport along the equalizer position.
-/
private theorem overCoeqπ_eqToHom_transport
    {y : Y} {ip₁ ip₂ : polyBetweenEqPos f g y}
    (hip : ip₁ = ip₂) :
    overCoeqπ
        (polyBetweenEqFiberα f g y ip₁)
        (polyBetweenEqFiberβ f g y ip₁) ≫
      eqToHom (congrArg
        (polyBetweenEqDir f g y) hip) =
    eqToHom (congrArg
        (fun ip => ccrFamily (P y) ip.val)
        hip) ≫
      overCoeqπ
        (polyBetweenEqFiberα f g y ip₂)
        (polyBetweenEqFiberβ f g y ip₂) := by
  subst hip; simp

/--
Uniqueness of the lift into the equalizer.
-/
theorem polyBetweenEqLift_unique
    {R : PolyFunctorBetweenCat.{u, u} X Y}
    (h : R ⟶ P) (w : h ≫ f = h ≫ g)
    (m : R ⟶ polyBetweenEq f g)
    (hm : m ≫ polyBetweenEqIncl f g = h) :
    m = polyBetweenEqLift f g h w := by
  suffices ∀ y, m y = polyBetweenEqLift
      f g h w y by funext y; exact this y
  intro y
  have hbase : (m y).base =
      (polyBetweenEqLift f g h w y).base := by
    funext q
    exact Subtype.ext
      (congrFun (congrArg ccrReindex
        (congrFun hm y)) q)
  refine ccrHom_ext_subst _ _ hbase ?_
  intro q
  dsimp [polyBetweenEqLift,
    polyBetweenEqLiftReindex,
    polyBetweenEqLiftFiber]
  apply overCoeq_epi
    (polyBetweenEqFiberα f g y
      (ccrReindex (m y) q))
    (polyBetweenEqFiberβ f g y
      (ccrReindex (m y) q))
  have h_comp :=
    ccrFiberMor_congr (congrFun hm y) q
  change ccrFiberMor
    (m y ≫ polyBetweenEqIncl f g y) q =
    _ at h_comp
  rw [ccrComp_fiberMor] at h_comp
  dsimp [polyBetweenEqIncl,
    polyBetweenEqInclReindex,
    polyBetweenEqInclFiber] at h_comp
  rw [h_comp]
  symm
  rw [← Category.assoc]
  simp only [ccrReindex]
  rw [overCoeqπ_eqToHom_transport f g
      (congrFun hbase q)]
  dsimp only [polyBetweenEqLift, ccrHomMk,
    polyBetweenEqLiftReindex, ccrReindex]
  rw [Category.assoc, overCoeq_fac]

/--
The fork for the equalizer of `f` and `g` in
`PolyFunctorBetweenCat`.
-/
def polyBetweenFork : Fork f g :=
  Fork.ofι (polyBetweenEqIncl f g)
    (polyBetweenEqIncl_condition f g)

/--
The fork for the equalizer is a limit cone.
-/
def polyBetweenIsLimitFork :
    IsLimit (polyBetweenFork f g) :=
  Fork.IsLimit.mk (polyBetweenFork f g)
    (fun s => polyBetweenEqLift f g s.ι s.condition)
    (fun s =>
      polyBetweenEqLift_incl f g s.ι s.condition)
    (fun s m hm =>
      polyBetweenEqLift_unique f g
        s.ι s.condition m hm)

instance : HasEqualizer f g :=
  HasLimit.mk ⟨polyBetweenFork f g,
    polyBetweenIsLimitFork f g⟩

instance : HasEqualizers
    (PolyFunctorBetweenCat.{u, u} X Y) :=
  hasEqualizers_of_hasLimit_parallelPair _

end Equalizers

section Coequalizers

variable {X Y : Type u}
  {P Q : PolyFunctorBetweenCat.{u, u} X Y}
  (s t : P ⟶ Q)

/--
The edge relation on Q-positions: `j₁` and `j₂` are related
when there exists a P-position `i` with `s` mapping `i` to
`j₁` and `t` mapping `i` to `j₂`.
-/
def polyBetweenCoeqRel (y : Y) :
    ccrIndex (Q y) → ccrIndex (Q y) → Prop :=
  fun j₁ j₂ => ∃ i : ccrIndex (P y),
    ccrReindex (s y) i = j₁ ∧
    ccrReindex (t y) i = j₂

/--
Coequalizer positions: connected components of the graph
whose vertices are Q-positions and whose edges connect
`ccrReindex (s y) i` to `ccrReindex (t y) i` for each
P-position `i`.
-/
def polyBetweenCoeqPos (y : Y) : Type u :=
  Quot (polyBetweenCoeqRel s t y)

/--
Vertices of the graph in component `c`: Q-positions
mapping to `c` under the quotient.
-/
def polyBetweenCoeqVert (y : Y)
    (c : polyBetweenCoeqPos s t y) : Type u :=
  { j : ccrIndex (Q y) //
    Quot.mk (polyBetweenCoeqRel s t y) j = c }

/--
Edges of the graph in component `c`: P-positions whose
source (via `s`) maps to `c`.
-/
def polyBetweenCoeqEdge (y : Y)
    (c : polyBetweenCoeqPos s t y) : Type u :=
  { i : ccrIndex (P y) //
    Quot.mk (polyBetweenCoeqRel s t y)
      (ccrReindex (s y) i) = c }

/--
The target endpoint of an edge also maps to the same
component `c`.
-/
theorem polyBetweenCoeqEdge_target (y : Y)
    (c : polyBetweenCoeqPos s t y)
    (e : polyBetweenCoeqEdge s t y c) :
    Quot.mk (polyBetweenCoeqRel s t y)
      (ccrReindex (t y) e.val) = c :=
  (Quot.sound ⟨e.val, rfl, rfl⟩).symm.trans
    e.property

/--
The Q-family indexed by vertices in component `c`.
-/
def polyBetweenCoeqVertFamily (y : Y)
    (c : polyBetweenCoeqPos s t y) :
    polyBetweenCoeqVert s t y c → Over X :=
  fun v => ccrFamily (Q y) v.val

/--
The P-family indexed by edges in component `c`.
-/
def polyBetweenCoeqEdgeFamily (y : Y)
    (c : polyBetweenCoeqPos s t y) :
    polyBetweenCoeqEdge s t y c → Over X :=
  fun e => ccrFamily (P y) e.val

/--
Product of Q-fibers over vertices in component `c`.
-/
def polyBetweenCoeqVertProd (y : Y)
    (c : polyBetweenCoeqPos s t y) : Over X :=
  overProdObj (polyBetweenCoeqVertFamily s t y c)

/--
Product of P-fibers over edges in component `c`.
-/
def polyBetweenCoeqEdgeProd (y : Y)
    (c : polyBetweenCoeqPos s t y) : Over X :=
  overProdObj (polyBetweenCoeqEdgeFamily s t y c)

/--
The source vertex of an edge `e` in component `c`,
as an element of `polyBetweenCoeqVert`.
-/
def polyBetweenCoeqEdgeSrc (y : Y)
    (c : polyBetweenCoeqPos s t y)
    (e : polyBetweenCoeqEdge s t y c) :
    polyBetweenCoeqVert s t y c :=
  ⟨ccrReindex (s y) e.val, e.property⟩

/--
The target vertex of an edge `e` in component `c`,
as an element of `polyBetweenCoeqVert`.
-/
def polyBetweenCoeqEdgeTgt (y : Y)
    (c : polyBetweenCoeqPos s t y)
    (e : polyBetweenCoeqEdge s t y c) :
    polyBetweenCoeqVert s t y c :=
  ⟨ccrReindex (t y) e.val,
    polyBetweenCoeqEdge_target s t y c e⟩

/--
The `s`-induced map from vertex product to edge product:
projects to the source vertex, then applies `ccrFiberMor s`.
-/
def polyBetweenCoeqMapS (y : Y)
    (c : polyBetweenCoeqPos s t y) :
    polyBetweenCoeqVertProd s t y c ⟶
    polyBetweenCoeqEdgeProd s t y c :=
  overProdLift
    (polyBetweenCoeqEdgeFamily s t y c)
    (fun e =>
      overProdπ
        (polyBetweenCoeqVertFamily s t y c)
        (polyBetweenCoeqEdgeSrc s t y c e) ≫
      ccrFiberMor (s y) e.val)

/--
The `t`-induced map from vertex product to edge product:
projects to the target vertex, then applies `ccrFiberMor t`.
-/
def polyBetweenCoeqMapT (y : Y)
    (c : polyBetweenCoeqPos s t y) :
    polyBetweenCoeqVertProd s t y c ⟶
    polyBetweenCoeqEdgeProd s t y c :=
  overProdLift
    (polyBetweenCoeqEdgeFamily s t y c)
    (fun e =>
      overProdπ
        (polyBetweenCoeqVertFamily s t y c)
        (polyBetweenCoeqEdgeTgt s t y c e) ≫
      ccrFiberMor (t y) e.val)

/--
Coequalizer directions at component `c`: the equalizer
of the two maps `s*` and `t*` between the vertex and
edge products. This is an object of `Over X`.
-/
def polyBetweenCoeqDir (y : Y)
    (c : polyBetweenCoeqPos s t y) : Over X :=
  overEqObj
    (polyBetweenCoeqMapS s t y c)
    (polyBetweenCoeqMapT s t y c)

/--
The coequalizer object in `PolyFunctorBetweenCat X Y`.
-/
def polyBetweenCoeq :
    PolyFunctorBetweenCat.{u, u} X Y :=
  fun y => ccrObjMk (polyBetweenCoeqDir s t y)

/--
Reindex component of the projection `Q ⟶ polyBetweenCoeq`:
sends a Q-position to its connected component.
-/
def polyBetweenCoeqProjReindex (y : Y) :
    ccrIndex (Q y) → polyBetweenCoeqPos s t y :=
  Quot.mk (polyBetweenCoeqRel s t y)

/--
Fiber component of the projection `Q ⟶ polyBetweenCoeq`:
at Q-position `j`, the direction map goes from the
equalizer (at component of `j`) to `ccrFamily (Q y) j`.

Concretely, this composes the equalizer inclusion with
the projection to the vertex `⟨j, rfl⟩`.
-/
def polyBetweenCoeqProjFiber (y : Y)
    (j : ccrIndex (Q y)) :
    polyBetweenCoeqDir s t y
      (polyBetweenCoeqProjReindex s t y j) ⟶
    ccrFamily (Q y) j :=
  overEqι
    (polyBetweenCoeqMapS s t y _)
    (polyBetweenCoeqMapT s t y _) ≫
  overProdπ
    (polyBetweenCoeqVertFamily s t y _)
    ⟨j, rfl⟩

/--
The projection morphism `Q ⟶ polyBetweenCoeq s t`.
-/
def polyBetweenCoeqProj :
    Q ⟶ polyBetweenCoeq s t :=
  fun y => ccrHomMk
    (polyBetweenCoeqProjReindex s t y)
    (polyBetweenCoeqProjFiber s t y)

theorem polyBetweenCoeqProj_base_eq (y : Y)
    (i : ccrIndex (P y)) :
    polyBetweenCoeqProjReindex s t y
      (ccrReindex (s y) i) =
    polyBetweenCoeqProjReindex s t y
      (ccrReindex (t y) i) :=
  Quot.sound ⟨i, rfl, rfl⟩

private lemma polyBetweenCoeq_transport (y : Y)
    (j : ccrIndex (Q y))
    {c₁ c₂ : polyBetweenCoeqPos s t y}
    (hj₁ : Quot.mk
      (polyBetweenCoeqRel s t y) j = c₁)
    (hj₂ : Quot.mk
      (polyBetweenCoeqRel s t y) j = c₂)
    (hc : c₁ = c₂) :
    overEqι
      (polyBetweenCoeqMapS s t y c₁)
      (polyBetweenCoeqMapT s t y c₁) ≫
    overProdπ
      (polyBetweenCoeqVertFamily s t y c₁)
      ⟨j, hj₁⟩ =
    eqToHom
      (congrArg
        (polyBetweenCoeqDir s t y) hc) ≫
    overEqι
      (polyBetweenCoeqMapS s t y c₂)
      (polyBetweenCoeqMapT s t y c₂) ≫
    overProdπ
      (polyBetweenCoeqVertFamily s t y c₂)
      ⟨j, hj₂⟩ := by
  subst hc
  simp only [eqToHom_refl, Category.id_comp]

private lemma polyBetweenCoeq_edge_eq (y : Y)
    (c : polyBetweenCoeqPos s t y)
    (e : polyBetweenCoeqEdge s t y c) :
    overEqι
      (polyBetweenCoeqMapS s t y c)
      (polyBetweenCoeqMapT s t y c) ≫
    overProdπ
      (polyBetweenCoeqVertFamily s t y c)
      (polyBetweenCoeqEdgeSrc s t y c e) ≫
    ccrFiberMor (s y) e.val =
    overEqι
      (polyBetweenCoeqMapS s t y c)
      (polyBetweenCoeqMapT s t y c) ≫
    overProdπ
      (polyBetweenCoeqVertFamily s t y c)
      (polyBetweenCoeqEdgeTgt s t y c e) ≫
    ccrFiberMor (t y) e.val := by
  have h := overEq_condition
    (polyBetweenCoeqMapS s t y c)
    (polyBetweenCoeqMapT s t y c)
  have h' := congrArg
    (· ≫ overProdπ
      (polyBetweenCoeqEdgeFamily s t y c) e) h
  simp only [Category.assoc] at h' ⊢
  dsimp only [polyBetweenCoeqMapS,
    polyBetweenCoeqMapT] at h'
  simp only [overProd_fac] at h'
  exact h'

private lemma polyBetweenCoeqProj_fiber_eq
    (y : Y) (i : ccrIndex (P y)) :
    polyBetweenCoeqProjFiber s t y
      (ccrReindex (s y) i) ≫
    ccrFiberMor (s y) i =
    eqToHom (congrArg
      (polyBetweenCoeqDir s t y)
      (polyBetweenCoeqProj_base_eq s t y i)) ≫
    polyBetweenCoeqProjFiber s t y
      (ccrReindex (t y) i) ≫
    ccrFiberMor (t y) i := by
  dsimp only [polyBetweenCoeqProjFiber,
    polyBetweenCoeqProjReindex]
  simp only [Category.assoc]
  have h_eq :=
    polyBetweenCoeq_edge_eq s t y _ ⟨i, rfl⟩
  dsimp only [polyBetweenCoeqEdgeSrc,
    polyBetweenCoeqEdgeTgt,
    polyBetweenCoeqProjReindex] at h_eq
  rw [h_eq]
  have h_tr := polyBetweenCoeq_transport s t y
    (ccrReindex (t y) i)
    (polyBetweenCoeqProj_base_eq s t y i).symm
    rfl
    (polyBetweenCoeqProj_base_eq s t y i)
  dsimp only [polyBetweenCoeqProjReindex] at h_tr
  conv_lhs => rw [← Category.assoc]
  rw [h_tr]
  simp only [Category.assoc]

/--
The coequalizer condition:
`s ≫ polyBetweenCoeqProj = t ≫ polyBetweenCoeqProj`.
-/
theorem polyBetweenCoeqProj_condition :
    s ≫ polyBetweenCoeqProj s t =
    t ≫ polyBetweenCoeqProj s t := by
  funext y
  change s y ≫ polyBetweenCoeqProj s t y =
    t y ≫ polyBetweenCoeqProj s t y
  refine ccrHom_ext_subst _ _ ?_ ?_
  · funext i
    exact polyBetweenCoeqProj_base_eq s t y i
  · intro i
    simp only [ccrComp_fiberMor]
    exact polyBetweenCoeqProj_fiber_eq s t y i

def polyBetweenCoeqLiftReindex
    {R : PolyFunctorBetweenCat.{u, u} X Y}
    (h : Q ⟶ R) (w : s ≫ h = t ≫ h)
    (y : Y) :
    polyBetweenCoeqPos s t y →
    ccrIndex (R y) :=
  Quot.lift (ccrReindex (h y))
    (fun _ _ ⟨i, hs, ht⟩ => by
      subst hs; subst ht
      exact congrFun
        (congrArg ccrReindex (congrFun w y)) i)

private lemma polyBetweenCoeqLiftReindex_eq
    {R : PolyFunctorBetweenCat.{u, u} X Y}
    (h : Q ⟶ R) (w : s ≫ h = t ≫ h)
    (y : Y) (j : ccrIndex (Q y))
    {c : polyBetweenCoeqPos s t y}
    (hj : Quot.mk
      (polyBetweenCoeqRel s t y) j = c) :
    polyBetweenCoeqLiftReindex s t h w y c =
    ccrReindex (h y) j := by
  subst hj; rfl

def polyBetweenCoeqLiftVertex
    {R : PolyFunctorBetweenCat.{u, u} X Y}
    (h : Q ⟶ R) (w : s ≫ h = t ≫ h)
    (y : Y) (c : polyBetweenCoeqPos s t y)
    (v : polyBetweenCoeqVert s t y c) :
    ccrFamily (R y)
      (polyBetweenCoeqLiftReindex
        s t h w y c) ⟶
    ccrFamily (Q y) v.val :=
  eqToHom (congrArg (ccrFamily (R y))
    (polyBetweenCoeqLiftReindex_eq
      s t h w y v.val v.property)) ≫
  ccrFiberMor (h y) v.val

def polyBetweenCoeqLiftProd
    {R : PolyFunctorBetweenCat.{u, u} X Y}
    (h : Q ⟶ R) (w : s ≫ h = t ≫ h)
    (y : Y) (c : polyBetweenCoeqPos s t y) :
    ccrFamily (R y)
      (polyBetweenCoeqLiftReindex
        s t h w y c) ⟶
    polyBetweenCoeqVertProd s t y c :=
  overProdLift
    (polyBetweenCoeqVertFamily s t y c)
    (polyBetweenCoeqLiftVertex s t h w y c)

private lemma overProd_hom_ext
    {X' : Type u} {I' : Type u}
    (F' : I' → Over X') {S' : Over X'}
    (f' g' : S' ⟶ overProdObj F')
    (h' : ∀ i,
      f' ≫ overProdπ F' i =
      g' ≫ overProdπ F' i) :
    f' = g' :=
  (overProd_uniq F' _ f' (fun _ => rfl)).trans
    (overProd_uniq F' _ g'
      (fun i => (h' i).symm)).symm

private theorem polyBetweenCoeqLiftProd_eq
    {R : PolyFunctorBetweenCat.{u, u} X Y}
    (h : Q ⟶ R) (w : s ≫ h = t ≫ h)
    (y : Y) (c : polyBetweenCoeqPos s t y) :
    polyBetweenCoeqLiftProd s t h w y c ≫
      polyBetweenCoeqMapS s t y c =
    polyBetweenCoeqLiftProd s t h w y c ≫
      polyBetweenCoeqMapT s t y c := by
  apply overProd_hom_ext
  intro e
  simp only [Category.assoc]
  dsimp only [polyBetweenCoeqMapS,
    polyBetweenCoeqMapT]
  simp only [overProd_fac]
  simp only [← Category.assoc]
  dsimp only [polyBetweenCoeqLiftProd]
  simp only [overProd_fac]
  dsimp only [polyBetweenCoeqLiftVertex,
    polyBetweenCoeqEdgeSrc,
    polyBetweenCoeqEdgeTgt]
  simp only [Category.assoc]
  rw [← ccrComp_fiberMor (s y) (h y) e.val,
    ← ccrComp_fiberMor (t y) (h y) e.val]
  change eqToHom _ ≫ ccrFiberMor ((s ≫ h) y) e.val =
    eqToHom _ ≫ ccrFiberMor ((t ≫ h) y) e.val
  rw [ccrFiberMor_congr (congrFun w y) e.val]
  simp only [eqToHom_trans_assoc]

def polyBetweenCoeqLiftFiber
    {R : PolyFunctorBetweenCat.{u, u} X Y}
    (h : Q ⟶ R) (w : s ≫ h = t ≫ h)
    (y : Y) (c : polyBetweenCoeqPos s t y) :
    ccrFamily (R y)
      (polyBetweenCoeqLiftReindex
        s t h w y c) ⟶
    polyBetweenCoeqDir s t y c :=
  overEqLift
    (polyBetweenCoeqMapS s t y c)
    (polyBetweenCoeqMapT s t y c)
    (polyBetweenCoeqLiftProd s t h w y c)
    (polyBetweenCoeqLiftProd_eq s t h w y c)

def polyBetweenCoeqLift
    {R : PolyFunctorBetweenCat.{u, u} X Y}
    (h : Q ⟶ R) (w : s ≫ h = t ≫ h) :
    polyBetweenCoeq s t ⟶ R :=
  fun y => ccrHomMk
    (polyBetweenCoeqLiftReindex s t h w y)
    (polyBetweenCoeqLiftFiber s t h w y)

theorem polyBetweenCoeqLift_fac
    {R : PolyFunctorBetweenCat.{u, u} X Y}
    (h : Q ⟶ R) (w : s ≫ h = t ≫ h) :
    polyBetweenCoeqProj s t ≫
      polyBetweenCoeqLift s t h w = h := by
  funext y
  refine ccrHom_ext_subst _ _ rfl ?_
  intro q
  change ccrFiberMor
    (polyBetweenCoeqProj s t y ≫
      polyBetweenCoeqLift s t h w y) q =
    eqToHom _ ≫ ccrFiberMor (h y) q
  rw [ccrComp_fiberMor]
  dsimp only [polyBetweenCoeqLift,
    polyBetweenCoeqProj,
    polyBetweenCoeqProjFiber,
    polyBetweenCoeqLiftFiber]
  simp only [ccrHomMk, ccrFiberMor, ccrReindex]
  dsimp only [polyBetweenCoeqProjReindex,
    polyBetweenCoeqProjFiber,
    polyBetweenCoeqLiftFiber]
  simp only [← Category.assoc]
  rw [overEq_fac]
  dsimp only [polyBetweenCoeqLiftProd]
  rw [overProd_fac]
  dsimp only [polyBetweenCoeqLiftVertex]
  rfl

private lemma polyBetweenCoeqLift_base_unique
    {R : PolyFunctorBetweenCat.{u, u} X Y}
    (h : Q ⟶ R) (w : s ≫ h = t ≫ h)
    (m : polyBetweenCoeq s t ⟶ R)
    (hm : polyBetweenCoeqProj s t ≫ m = h)
    (y : Y) (c : polyBetweenCoeqPos s t y) :
    ccrReindex (m y) c =
    polyBetweenCoeqLiftReindex s t h w y c := by
  induction c using Quot.ind with
  | mk j =>
    exact congrFun
      (congrArg ccrReindex (congrFun hm y)) j

private lemma coeq_fiber_ι_vertex
    {R : PolyFunctorBetweenCat.{u, u} X Y}
    (h : Q ⟶ R) (w : s ≫ h = t ≫ h)
    (m : polyBetweenCoeq s t ⟶ R)
    (hm : polyBetweenCoeqProj s t ≫ m = h)
    (y : Y)
    (c : polyBetweenCoeqPos s t y)
    (j : ccrIndex (Q y))
    (hj : Quot.mk
      (polyBetweenCoeqRel s t y) j = c) :
    ccrFiberMor (m y) c ≫
      overEqι
        (polyBetweenCoeqMapS s t y c)
        (polyBetweenCoeqMapT s t y c) ≫
      overProdπ
        (polyBetweenCoeqVertFamily s t y c)
        ⟨j, hj⟩ =
    eqToHom (congrArg (ccrFamily (R y))
      (polyBetweenCoeqLift_base_unique
        s t h w m hm y c)) ≫
    polyBetweenCoeqLiftProd s t h w y c ≫
      overProdπ
        (polyBetweenCoeqVertFamily s t y c)
        ⟨j, hj⟩ := by
  subst hj
  change ccrFiberMor
    (polyBetweenCoeqProj s t y ≫ m y) j =
    eqToHom _ ≫ ccrFiberMor (h y) j
  exact ccrFiberMor_congr (congrFun hm y) j

private lemma polyBetweenCoeqLift_fiber_unique
    {R : PolyFunctorBetweenCat.{u, u} X Y}
    (h : Q ⟶ R) (w : s ≫ h = t ≫ h)
    (m : polyBetweenCoeq s t ⟶ R)
    (hm : polyBetweenCoeqProj s t ≫ m = h)
    (y : Y) (q : ccrIndex (Q y)) :
    ccrFiberMor (m y)
      (Quot.mk (polyBetweenCoeqRel s t y) q) =
    eqToHom (congrArg (ccrFamily (R y))
      (polyBetweenCoeqLift_base_unique
        s t h w m hm y
        (Quot.mk _ q))) ≫
    polyBetweenCoeqLiftFiber s t h w y
      (Quot.mk _ q) := by
  set c := Quot.mk (polyBetweenCoeqRel s t y) q
  set mapS' :=
    polyBetweenCoeqMapS s t y c
  set mapT' :=
    polyBetweenCoeqMapT s t y c
  set lp :=
    polyBetweenCoeqLiftProd s t h w y c
  set be := polyBetweenCoeqLift_base_unique
    s t h w m hm y c
  set h₀ :=
    eqToHom (congrArg (ccrFamily (R y)) be) ≫
    lp
  have w₀ : h₀ ≫ mapS' = h₀ ≫ mapT' := by
    simp only [h₀, Category.assoc]
    exact congrArg (eqToHom _ ≫ ·)
      (polyBetweenCoeqLiftProd_eq
        s t h w y c)
  have step1 : ccrFiberMor (m y) c ≫
      overEqι mapS' mapT' = h₀ := by
    apply overProd_hom_ext
    intro ⟨j, hj⟩
    simp only [Category.assoc]
    exact coeq_fiber_ι_vertex
      s t h w m hm y c j hj
  calc ccrFiberMor (m y) c
      = overEqLift mapS' mapT' h₀ w₀ := by
        exact overEq_uniq mapS' mapT'
          h₀ w₀ _ step1
    _ = eqToHom _ ≫
        polyBetweenCoeqLiftFiber s t h w y
          c := by
        symm
        exact overEq_uniq mapS' mapT'
          h₀ w₀ _
          (by have : polyBetweenCoeqLiftFiber
                s t h w y c =
                overEqLift mapS' mapT' lp
                  (polyBetweenCoeqLiftProd_eq
                    s t h w y c) := rfl
              rw [Category.assoc, this,
                overEq_fac])

theorem polyBetweenCoeqLift_unique
    {R : PolyFunctorBetweenCat.{u, u} X Y}
    (h : Q ⟶ R) (w : s ≫ h = t ≫ h)
    (m : polyBetweenCoeq s t ⟶ R)
    (hm : polyBetweenCoeqProj s t ≫ m = h) :
    m = polyBetweenCoeqLift s t h w := by
  funext y
  refine ccrHom_ext_subst _ _ ?_ ?_
  · funext c
    exact polyBetweenCoeqLift_base_unique
      s t h w m hm y c
  · intro c
    induction c using Quot.ind with
    | mk q =>
      exact polyBetweenCoeqLift_fiber_unique
        s t h w m hm y q

def polyBetweenCofork : Cofork s t :=
  Cofork.ofπ (polyBetweenCoeqProj s t)
    (polyBetweenCoeqProj_condition s t)

def polyBetweenIsColimitCofork :
    IsColimit (polyBetweenCofork s t) :=
  Cofork.IsColimit.mk (polyBetweenCofork s t)
    (fun c => polyBetweenCoeqLift s t c.π c.condition)
    (fun c =>
      polyBetweenCoeqLift_fac s t c.π c.condition)
    (fun c m hm =>
      polyBetweenCoeqLift_unique s t
        c.π c.condition m hm)

instance : HasCoequalizer s t :=
  HasColimit.mk ⟨polyBetweenCofork s t,
    polyBetweenIsColimitCofork s t⟩

instance : HasCoequalizers
    (PolyFunctorBetweenCat.{u, u} X Y) :=
  hasCoequalizers_of_hasColimit_parallelPair _

end Coequalizers

section LimitsColimits

variable {X Y : Type u}

instance : HasFiniteProducts
    (PolyFunctorBetweenCat.{u, u} X Y) :=
  hasFiniteProducts_of_hasProducts _

instance : HasFiniteCoproducts
    (PolyFunctorBetweenCat.{u, u} X Y) :=
  hasFiniteCoproducts_of_hasCoproducts _

instance : HasFiniteLimits
    (PolyFunctorBetweenCat.{u, u} X Y) :=
  hasFiniteLimits_of_hasEqualizers_and_finite_products

instance : HasLimitsOfSize.{u, u}
    (PolyFunctorBetweenCat.{u, u} X Y) :=
  has_limits_of_hasEqualizers_and_products

instance : HasFiniteColimits
    (PolyFunctorBetweenCat.{u, u} X Y) :=
  hasFiniteColimits_of_hasCoequalizers_and_finite_coproducts

instance : HasColimitsOfSize.{u, u}
    (PolyFunctorBetweenCat.{u, u} X Y) :=
  has_colimits_of_hasCoequalizers_and_coproducts

end LimitsColimits

/-! ## Left Kan Extensions

Given `q : PolyFunctorBetweenCat X Z` and
`p : PolyFunctorBetweenCat X Y`, the left Kan extension
`Lan_q(p) : PolyFunctorBetweenCat Z Y` has at each `y : Y`:
- Positions: `ccrIndex (p y)`
- Family at `ip`: `polyBetweenEval q (ccrFamily (p y) ip)`
-/

section LeftKanExtension

variable {X Y Z : Type u}
  (q : PolyFunctorBetweenCat.{u, u} X Z)

/--
The object part of the left Kan extension along `q`.
At each `y : Y`, positions are those of `p y`, and the
family at position `ip` evaluates `q` at the `ip`-fiber
of `p`.
-/
def polyBetweenLKanObj
    (p : PolyFunctorBetweenCat.{u, u} X Y) :
    PolyFunctorBetweenCat.{u, u} Z Y :=
  fun y => ccrObjMk
    (fun ip => polyBetweenEval X Z q
      (ccrFamily (p y) ip))

/--
The action on morphisms of the left Kan extension along `q`.
Given `alpha : p ⟶ p'`, the reindexing at `y` is
`ccrReindex (alpha y)`, and the fiber morphism at `ip`
applies `polyBetweenEvalMap q` to `ccrFiberMor (alpha y) ip`.
-/
def polyBetweenLKanMap
    {p p' : PolyFunctorBetweenCat.{u, u} X Y}
    (alpha : p ⟶ p') :
    polyBetweenLKanObj q p ⟶
      polyBetweenLKanObj q p' :=
  fun y => ccrHomMk
    (fun ip => ccrReindex (alpha y) ip)
    (fun ip => polyBetweenEvalMap X Z q
      (ccrFiberMor (alpha y) ip))

@[simp]
lemma polyBetweenLKanMap_id
    (p : PolyFunctorBetweenCat.{u, u} X Y) :
    polyBetweenLKanMap q (𝟙 p) =
      𝟙 (polyBetweenLKanObj q p) := by
  funext y
  simp only [polyBetweenLKanMap]
  rfl

@[simp]
lemma polyBetweenLKanMap_comp
    {p p' p'' : PolyFunctorBetweenCat.{u, u} X Y}
    (alpha : p ⟶ p') (beta : p' ⟶ p'') :
    polyBetweenLKanMap q (alpha ≫ beta) =
      polyBetweenLKanMap q alpha ≫
        polyBetweenLKanMap q beta := by
  funext y
  simp only [polyBetweenLKanMap]
  rfl

/--
The left Kan extension functor along `q`:
`PolyFunctorBetweenCat X Y ⥤ PolyFunctorBetweenCat Z Y`.
-/
def polyBetweenLKanFunctor :
    PolyFunctorBetweenCat.{u, u} X Y ⥤
      PolyFunctorBetweenCat.{u, u} Z Y where
  obj := polyBetweenLKanObj q
  map := polyBetweenLKanMap q
  map_id := polyBetweenLKanMap_id q
  map_comp := polyBetweenLKanMap_comp q

lemma cast_ccrFamily_left
    (q' : PolyFunctorBetweenCat.{u, u} X Z)
    {z z' : Z} (hz : z = z')
    {ip : ccrIndex (q' z)} :
    (ccrFamily (q' z')
      (cast (congrArg (fun z => ccrIndex (q' z)) hz)
        ip)).left =
    (ccrFamily (q' z) ip).left := by
  subst hz; rfl

lemma cast_ccrFamily_hom
    (q' : PolyFunctorBetweenCat.{u, u} X Z)
    {z z' : Z} (hz : z = z')
    {ip : ccrIndex (q' z)}
    (e : (ccrFamily (q' z')
      (cast (congrArg (fun z => ccrIndex (q' z)) hz)
        ip)).left) :
    (ccrFamily (q' z) ip).hom
      (cast (cast_ccrFamily_left q' hz) e) =
    (ccrFamily (q' z')
      (cast (congrArg (fun z => ccrIndex (q' z)) hz)
        ip)).hom e := by
  subst hz; rfl

/--
The reindexing for right whiskering: given `alpha : r ⟶ r'`
and a composed position `⟨ir, pf⟩`, produces a composed
position in `r' ∘ q` by applying `alpha`'s reindex to `ir`
and transporting `pf` through `alpha`'s fiber morphism.
-/
def polyBetweenWhiskerRightReindex
    {r r' : PolyFunctorBetweenCat.{u, u} Z Y}
    (alpha : r ⟶ r') (y : Y)
    (p : polyBetweenCompIndex r q y) :
    polyBetweenCompIndex r' q y :=
  let fib := ccrFiberMor (alpha y) p.1
  ⟨ccrReindex (alpha y) p.1,
   fun e' =>
    cast (congrArg (fun z => ccrIndex (q z))
      (congrFun (Over.w fib) e'))
    (p.2 (fib.left e'))⟩

/--
The underlying function for the fiber morphism
of right whiskering. Maps directions `⟨e', eq'⟩`
from the target composition to directions in the
source composition via `alpha`'s fiber morphism.
-/
def polyBetweenWhiskerRightFiberLeft
    {r r' : PolyFunctorBetweenCat.{u, u} Z Y}
    (alpha : r ⟶ r') (y : Y)
    (p : polyBetweenCompIndex r q y)
    (d : (polyBetweenCompFamily r' q y
      (polyBetweenWhiskerRightReindex
        q alpha y p)).left) :
    (polyBetweenCompFamily r q y p).left :=
  let fib := ccrFiberMor (alpha y) p.1
  let hz := congrFun (Over.w fib) d.1
  ⟨fib.left d.1,
   cast (cast_ccrFamily_left q hz) d.2⟩

theorem polyBetweenWhiskerRightFiberComm
    {r r' : PolyFunctorBetweenCat.{u, u} Z Y}
    (alpha : r ⟶ r') (y : Y)
    (p : polyBetweenCompIndex r q y) :
    (polyBetweenCompFamily r q y p).hom ∘
      polyBetweenWhiskerRightFiberLeft
        q alpha y p =
    (polyBetweenCompFamily r' q y
      (polyBetweenWhiskerRightReindex
        q alpha y p)).hom := by
  let fib := ccrFiberMor (alpha y) p.1
  let hz := congrFun (Over.w fib)
  funext ⟨e', eq'⟩
  change (ccrFamily (q _) (p.2 (fib.left e'))).hom
    (cast (cast_ccrFamily_left q (hz e')) eq') =
    (ccrFamily (q _)
      (cast _ (p.2 (fib.left e')))).hom eq'
  exact cast_ccrFamily_hom q (hz e') eq'

/--
The fiber morphism for right whiskering at a
composed position `p`.
-/
def polyBetweenWhiskerRightFiber
    {r r' : PolyFunctorBetweenCat.{u, u} Z Y}
    (alpha : r ⟶ r') (y : Y)
    (p : polyBetweenCompIndex r q y) :
    polyBetweenCompFamily r' q y
      (polyBetweenWhiskerRightReindex
        q alpha y p) ⟶
    polyBetweenCompFamily r q y p :=
  Over.homMk
    (polyBetweenWhiskerRightFiberLeft
      q alpha y p)
    (polyBetweenWhiskerRightFiberComm
      q alpha y p)

/--
Right whiskering: given `alpha : r ⟶ r'` in
`PolyFunctorBetweenCat Z Y`, produce
`r ∘ q ⟶ r' ∘ q` in `PolyFunctorBetweenCat X Y`.
-/
def polyBetweenWhiskerRight
    {r r' : PolyFunctorBetweenCat.{u, u} Z Y}
    (alpha : r ⟶ r') :
    polyBetweenComp r q ⟶
      polyBetweenComp r' q :=
  fun y => ccrHomMk
    (polyBetweenWhiskerRightReindex
      q alpha y)
    (polyBetweenWhiskerRightFiber
      q alpha y)

@[simp]
lemma polyBetweenWhiskerRight_id
    (r : PolyFunctorBetweenCat.{u, u} Z Y) :
    polyBetweenWhiskerRight q (𝟙 r) =
      𝟙 (polyBetweenComp r q) := by
  funext y
  change polyBetweenWhiskerRight q (𝟙 r) y =
    𝟙 (polyBetweenComp r q y)
  simp only [polyBetweenWhiskerRight, ccrId_mk]
  refine ccrHom_ext_subst _ _ ?_ ?_
  · funext ⟨ir, pf⟩
    rfl
  · intro i
    simp only [ccrHomMk_fiberMor, ccrHomMk_reindex,
      eqToHom_refl, Category.id_comp]
    ext ⟨e, d⟩
    rfl

lemma polyBetweenWhiskerRightReindex_comp
    {r r' r'' : PolyFunctorBetweenCat.{u, u} Z Y}
    (alpha : r ⟶ r') (beta : r' ⟶ r'')
    (y : Y) :
    polyBetweenWhiskerRightReindex q (alpha ≫ beta) y =
      polyBetweenWhiskerRightReindex q beta y ∘
        polyBetweenWhiskerRightReindex q alpha y := by
  funext ⟨ir, pf⟩
  dsimp [polyBetweenWhiskerRightReindex,
    ccrFiberMor, ccrReindex]
  congr 1
  funext e'
  simp only [cast_cast]
  rfl

private lemma eqToHom_compFamily_fst
    {r : PolyFunctorBetweenCat.{u, u} Z Y}
    {y : Y}
    {p₁ p₂ : ccrIndex (polyBetweenComp r q y)}
    (hp : p₁ = p₂)
    (ed : (ccrFamily
      (polyBetweenComp r q y) p₁).left) :
    ((eqToHom (congrArg
      (ccrFamily (polyBetweenComp r q y))
        hp)).left ed).fst =
    cast (congrArg (fun p =>
      (ccrFamily (r y) p.fst).left)
        hp) ed.fst := by
  subst hp; rfl

private lemma eqToHom_compFamily_snd_heq
    {r : PolyFunctorBetweenCat.{u, u} Z Y}
    {y : Y}
    {p₁ p₂ : ccrIndex (polyBetweenComp r q y)}
    (hp : p₁ = p₂)
    (ed : (ccrFamily
      (polyBetweenComp r q y) p₁).left) :
    HEq
      ((eqToHom (congrArg
        (ccrFamily (polyBetweenComp r q y))
          hp)).left ed).snd
      ed.snd := by
  subst hp; rfl

@[simp]
lemma polyBetweenWhiskerRight_comp
    {r r' r'' : PolyFunctorBetweenCat.{u, u} Z Y}
    (alpha : r ⟶ r') (beta : r' ⟶ r'') :
    polyBetweenWhiskerRight q (alpha ≫ beta) =
      polyBetweenWhiskerRight q alpha ≫
        polyBetweenWhiskerRight q beta := by
  funext y
  change polyBetweenWhiskerRight q (alpha ≫ beta) y =
    (polyBetweenWhiskerRight q alpha y ≫
      polyBetweenWhiskerRight q beta y)
  simp only [polyBetweenWhiskerRight, ccrComp_mk]
  refine ccrHom_ext_subst _ _ ?_ ?_
  · exact polyBetweenWhiskerRightReindex_comp
      q alpha beta y
  · intro i
    simp only [ccrHomMk_fiberMor, ccrHomMk_reindex,
      polyBetweenWhiskerRightFiber]
    ext ⟨e, d⟩
    simp only [Over.comp_left, types_comp_apply,
      Over.homMk_left,
      polyBetweenWhiskerRightFiberLeft,
      polyBetweenWhiskerRightReindex]
    congr 1
    · have htf := eqToHom_compFamily_fst q
        (congrFun
          (polyBetweenWhiskerRightReindex_comp
            q alpha beta y) i) ⟨e, d⟩
      rw [htf]
      simp only [FamilyCat.eq_1,
        CoprodCovarRepCat.eq_1,
        CategoryOp'.eq_1,
        familyFunctor.eq_1, Cat.of_α,
        familyMap.eq_1,
        Cat.opFunctor'.eq_1,
        Functor.op'.eq_1,
        functorOp'Obj.eq_1,
        Pi.comp_apply,
        Function.comp_apply, cast_eq]
      rw [ccrComp_fiberMor (alpha y) (beta y)
        i.fst, Over.comp_left, types_comp_apply]
    · have hts := eqToHom_compFamily_snd_heq q
        (congrFun
          (polyBetweenWhiskerRightReindex_comp
            q alpha beta y) i) ⟨e, d⟩
      simp only [FamilyCat.eq_1,
        CoprodCovarRepCat.eq_1,
        CategoryOp'.eq_1,
        familyFunctor.eq_1, Cat.of_α,
        familyMap.eq_1,
        Cat.opFunctor'.eq_1,
        Functor.op'.eq_1,
        functorOp'Obj.eq_1,
        Pi.comp_apply,
        Function.comp_apply, cast_cast,
        heq_cast_iff_heq,
        cast_heq_iff_heq]
      exact hts.symm

def polyBetweenPrecompObj
    (r : PolyFunctorBetweenCat.{u, u} Z Y) :
    PolyFunctorBetweenCat.{u, u} X Y :=
  polyBetweenComp r q

def polyBetweenPrecompFunctor :
    ↑(PolyFunctorBetweenCat.{u, u} Z Y) ⥤
      ↑(PolyFunctorBetweenCat.{u, u} X Y) where
  obj r := polyBetweenPrecompObj q r
  map alpha := polyBetweenWhiskerRight q alpha
  map_id r := polyBetweenWhiskerRight_id q r
  map_comp f g :=
    polyBetweenWhiskerRight_comp q f g

section Adjunction

variable
  {p : PolyFunctorBetweenCat.{u, u} X Y}
  {r : PolyFunctorBetweenCat.{u, u} Z Y}

private def lkanLAdjFiberW
    (alpha : polyBetweenLKanObj q p ⟶ r)
    (y : Y) (ip : ccrIndex (p y))
    (e : (ccrFamily (r y)
      (ccrReindex (alpha y) ip)).left) :
    ((ccrFiberMor (alpha y) ip).left e).fst =
      (ccrFamily (r y)
        (ccrReindex (alpha y) ip)).hom e :=
  congrFun (Over.w (ccrFiberMor (alpha y) ip)) e

private def lkanLAdjReindex
    (alpha : polyBetweenLKanObj q p ⟶ r)
    (y : Y) (ip : ccrIndex (p y)) :
    ccrIndex (polyBetweenComp r q y) :=
  ⟨ccrReindex (alpha y) ip,
   fun e => cast
     (congrArg (fun z => ccrIndex (q z))
       (lkanLAdjFiberW q alpha y ip e))
     ((ccrFiberMor (alpha y) ip).left e).2.1⟩

private def lkanLAdjFiberLeft
    (alpha : polyBetweenLKanObj q p ⟶ r)
    (y : Y) (ip : ccrIndex (p y))
    (ed : (polyBetweenCompFamily r q y
      (lkanLAdjReindex q alpha y ip)).left) :
    (ccrFamily (p y) ip).left :=
  let val := (ccrFiberMor (alpha y) ip).left ed.1
  val.snd.snd.left
    (cast (cast_ccrFamily_left q
      (lkanLAdjFiberW q alpha y ip ed.1)) ed.2)

private lemma lkanLAdjFiberComm
    (alpha : polyBetweenLKanObj q p ⟶ r)
    (y : Y) (ip : ccrIndex (p y))
    (ed : (polyBetweenCompFamily r q y
      (lkanLAdjReindex q alpha y ip)).left) :
    (ccrFamily (p y) ip).hom
      (lkanLAdjFiberLeft q alpha y ip ed) =
    (polyBetweenCompFamily r q y
      (lkanLAdjReindex q alpha y ip)).hom ed := by
  simp only [lkanLAdjFiberLeft]
  exact (congrFun (Over.w
    ((ccrFiberMor (alpha y) ip).left ed.1).snd.snd)
    _).trans
    (cast_ccrFamily_hom q
      (lkanLAdjFiberW q alpha y ip ed.1)
      ed.2)

private def lkanLAdjFiber
    (alpha : polyBetweenLKanObj q p ⟶ r)
    (y : Y) (ip : ccrIndex (p y)) :
    polyBetweenCompFamily r q y
      (lkanLAdjReindex q alpha y ip) ⟶
    ccrFamily (p y) ip :=
  Over.homMk (lkanLAdjFiberLeft q alpha y ip)
    (funext (lkanLAdjFiberComm q alpha y ip))

def polyBetweenLKanLAdj
    (alpha : polyBetweenLKanObj q p ⟶ r) :
    p ⟶ polyBetweenPrecompObj q r :=
  fun y => ccrHomMk
    (lkanLAdjReindex q alpha y)
    (lkanLAdjFiber q alpha y)

private def lkanRAdjReindex
    (beta : p ⟶ polyBetweenPrecompObj q r)
    (y : Y) (ip : ccrIndex (p y)) :
    ccrIndex (r y) :=
  (ccrReindex (beta y) ip).fst

private def lkanRAdjFiberMor
    (beta : p ⟶ polyBetweenPrecompObj q r)
    (y : Y) (ip : ccrIndex (p y))
    (e : (ccrFamily (r y)
      (lkanRAdjReindex q beta y ip)).left) :
    ccrFamily
      (q ((ccrFamily (r y)
        (lkanRAdjReindex q beta y ip)).hom e))
      ((ccrReindex (beta y) ip).snd e) ⟶
    ccrFamily (p y) ip :=
  Over.homMk
    (fun d =>
      (ccrFiberMor (beta y) ip).left ⟨e, d⟩)
    (funext fun d =>
      congrFun (Over.w (ccrFiberMor (beta y) ip))
        ⟨e, d⟩)

private def lkanRAdjFiberLeft
    (beta : p ⟶ polyBetweenPrecompObj q r)
    (y : Y) (ip : ccrIndex (p y))
    (e : (ccrFamily (r y)
      (lkanRAdjReindex q beta y ip)).left) :
    (ccrFamily
      (polyBetweenLKanObj q p y) ip).left :=
  ⟨(ccrFamily (r y)
      (lkanRAdjReindex q beta y ip)).hom e,
   (ccrReindex (beta y) ip).snd e,
   lkanRAdjFiberMor q beta y ip e⟩

private def lkanRAdjFiber
    (beta : p ⟶ polyBetweenPrecompObj q r)
    (y : Y) (ip : ccrIndex (p y)) :
    ccrFamily (r y)
      (lkanRAdjReindex q beta y ip) ⟶
    ccrFamily (polyBetweenLKanObj q p y) ip :=
  Over.homMk
    (lkanRAdjFiberLeft q beta y ip)
    rfl

def polyBetweenLKanRAdj
    (beta : p ⟶ polyBetweenPrecompObj q r) :
    polyBetweenLKanObj q p ⟶ r :=
  fun y => ccrHomMk
    (lkanRAdjReindex q beta y)
    (lkanRAdjFiber q beta y)

lemma polyBetweenLKanLAdj_RAdj
    (beta : p ⟶ polyBetweenPrecompObj q r) :
    polyBetweenLKanLAdj q
      (polyBetweenLKanRAdj q beta) = beta := by
  rfl

private lemma lkanRoundtripFiber_left_eq
    (alpha : polyBetweenLKanObj q p ⟶ r)
    (y : Y) (ip : ccrIndex (p y))
    (e : (ccrFamily (r y)
      (ccrReindex (alpha y) ip)).left) :
    (ccrFiberMor
      (polyBetweenLKanRAdj q
        (polyBetweenLKanLAdj q alpha) y) ip).left
      e =
    (ccrFiberMor (alpha y) ip).left e := by
  change lkanRAdjFiberLeft q
    (polyBetweenLKanLAdj q alpha) y ip e =
    (ccrFiberMor (alpha y) ip).left e
  simp only [lkanRAdjFiberLeft, lkanRAdjReindex,
    polyBetweenLKanLAdj, ccrHomMk_reindex,
    ccrHomMk_fiberMor, lkanLAdjReindex,
    lkanRAdjFiberMor, lkanLAdjFiber,
    Over.homMk_left, lkanLAdjFiberLeft]
  set val := (ccrFiberMor (alpha y) ip).left e
  suffices h : ∀ (z : Z) (hz : val.fst = z),
      (⟨z,
        cast (congrArg
          (fun z => ccrIndex (q z)) hz)
          val.snd.fst,
        Over.homMk
          (fun d => val.snd.snd.left
            (cast (cast_ccrFamily_left q hz) d))
          (by subst hz
              exact Over.w val.snd.snd)⟩ :
        (ccrFamily
          (polyBetweenLKanObj q p y) ip).left) =
      val from
    h _ (lkanLAdjFiberW q alpha y ip e)
  intro z hz
  subst hz
  exact Sigma.ext rfl
    (heq_of_eq (Sigma.ext rfl
      (heq_of_eq (Over.OverMorphism.ext rfl))))

lemma polyBetweenLKanRAdj_LAdj
    (alpha : polyBetweenLKanObj q p ⟶ r) :
    polyBetweenLKanRAdj q
      (polyBetweenLKanLAdj q alpha) = alpha := by
  funext y
  refine ccrHom_ext_subst _ _ rfl ?_
  intro ip
  simp only [eqToHom_refl, Category.id_comp]
  apply Over.OverMorphism.ext
  funext e
  exact lkanRoundtripFiber_left_eq q alpha y ip e

def polyBetweenLKanHomEquiv
    (p : ↑(PolyFunctorBetweenCat.{u, u} X Y))
    (r : ↑(PolyFunctorBetweenCat.{u, u} Z Y)) :
    ((polyBetweenLKanFunctor q).obj p ⟶ r) ≃
      (p ⟶ (polyBetweenPrecompFunctor q).obj r) where
  toFun := polyBetweenLKanLAdj q
  invFun := polyBetweenLKanRAdj q
  left_inv := polyBetweenLKanRAdj_LAdj q
  right_inv := polyBetweenLKanLAdj_RAdj q

private lemma eqToHom_polyBetweenComp_fst
    {r' : PolyFunctorBetweenCat.{u, u} Z Y}
    {y : Y}
    {idx₁ idx₂ :
      polyBetweenCompIndex r' q y}
    (h : idx₁ = idx₂)
    (d : (polyBetweenCompFamily r' q y
      idx₁).left) :
    ((eqToHom (congrArg
      (ccrFamily (polyBetweenComp r' q y))
        h)).left d).fst =
    cast (congrArg
      (fun idx =>
        (ccrFamily (r' y) idx.fst).left)
      h) d.fst := by
  subst h; rfl

@[simp]
private lemma eqToHom_polyBetweenComp_left_id
    {r' : PolyFunctorBetweenCat.{u, u} Z Y}
    {y : Y}
    {idx₁ idx₂ :
      polyBetweenCompIndex r' q y}
    (h : idx₁ = idx₂)
    (d : (polyBetweenCompFamily r' q y
      idx₁).left) :
    (eqToHom (congrArg
      (ccrFamily (polyBetweenComp r' q y))
        h)).left d =
    cast (congrArg
      (fun idx =>
        (polyBetweenCompFamily r' q y
          idx).left)
      h) d := by
  subst h; rfl

private lemma
    cast_polyBetweenCompFamily_sigma_fst
    {r' : PolyFunctorBetweenCat.{u, u} Z Y}
    {y : Y}
    {fst₁ : ccrIndex (r' y)}
    {snd₁ snd₂ :
      ∀ (e : (ccrFamily (r' y) fst₁).left),
        ccrIndex
          (q ((ccrFamily (r' y) fst₁).hom e))}
    (h : (⟨fst₁, snd₁⟩ :
      polyBetweenCompIndex r' q y) =
      ⟨fst₁, snd₂⟩)
    (d : (polyBetweenCompFamily r' q y
      ⟨fst₁, snd₁⟩).left) :
    (cast (congrArg
      (fun idx =>
        (polyBetweenCompFamily r' q y
          idx).left)
      h) d).fst = d.fst := by
  have hsnd : snd₁ = snd₂ :=
    eq_of_heq (Sigma.mk.inj h).2
  subst hsnd
  rfl

private lemma
    cast_polyBetweenCompFamily_sigma_snd_heq
    {r' : PolyFunctorBetweenCat.{u, u} Z Y}
    {y : Y}
    {fst₁ : ccrIndex (r' y)}
    {snd₁ snd₂ :
      ∀ (e : (ccrFamily (r' y) fst₁).left),
        ccrIndex
          (q ((ccrFamily (r' y) fst₁).hom e))}
    (h : (⟨fst₁, snd₁⟩ :
      polyBetweenCompIndex r' q y) =
      ⟨fst₁, snd₂⟩)
    (d : (polyBetweenCompFamily r' q y
      ⟨fst₁, snd₁⟩).left) :
    HEq
      (cast (congrArg
        (fun idx =>
          (polyBetweenCompFamily r' q y
            idx).left)
        h) d).snd
      d.snd := by
  have hsnd : snd₁ = snd₂ :=
    eq_of_heq (Sigma.mk.inj h).2
  subst hsnd
  exact HEq.rfl

private lemma lkanLAdj_naturality_right_base_eq
    {r' : PolyFunctorBetweenCat.{u, u} Z Y}
    (alpha : polyBetweenLKanObj q p ⟶ r)
    (beta : r ⟶ r') (y : Y)
    (ip : ccrIndex (p y)) :
    lkanLAdjReindex q (alpha ≫ beta) y ip =
    polyBetweenWhiskerRightReindex q beta y
      (lkanLAdjReindex q alpha y ip) := by
  simp only [lkanLAdjReindex,
    polyBetweenWhiskerRightReindex]
  refine Sigma.ext rfl ?_
  simp only [heq_eq_eq]
  funext e
  have hfib :=
    ccrComp_fiberMor
      (f := alpha y) (g := beta y) (i := ip)
  have hleft := congrArg
    (fun (f : ccrFamily (r' y)
      (ccrReindex (beta y)
        (ccrReindex (alpha y) ip)) ⟶
      ccrFamily
        (polyBetweenLKanObj q p y) ip) =>
      f.left e) hfib
  simp only [Over.comp_left,
    types_comp_apply] at hleft
  rw [cast_cast]
  congr 1

private lemma lkanLAdj_fiber_combined_helper
    {r' : PolyFunctorBetweenCat.{u, u} Z Y}
    (alpha : polyBetweenLKanObj q p ⟶ r)
    (beta : r ⟶ r') (y : Y)
    (ip : ccrIndex (p y))
    {m : ccrFamily (r' y)
      (ccrReindex (beta y)
        (ccrReindex (alpha y) ip)) ⟶
      ccrFamily
        (polyBetweenLKanObj q p y) ip}
    (hm : m = ccrFiberMor (beta y)
      (ccrReindex (alpha y) ip) ≫
      ccrFiberMor (alpha y) ip)
    (e : (ccrFamily (r' y)
      (ccrReindex (beta y)
        (ccrReindex (alpha y) ip))).left)
    (s_cast :
      (ccrFamily
        (q (m.left e).fst)
        (m.left e).snd.fst).left)
    {e' : (ccrFamily (r' y)
      (ccrReindex (beta y)
        (ccrReindex (alpha y) ip))).left}
    (he : e' = e)
    {s_cast' :
      (ccrFamily
        (q ((ccrFiberMor (beta y)
          (ccrReindex (alpha y) ip) ≫
          ccrFiberMor (alpha y) ip).left
            e').fst)
        ((ccrFiberMor (beta y)
          (ccrReindex (alpha y) ip) ≫
          ccrFiberMor (alpha y) ip).left
            e').snd.fst).left}
    (hs : HEq s_cast' s_cast) :
    (m.left e).snd.snd.left s_cast =
    ((ccrFiberMor (alpha y) ip).left
      ((ccrFiberMor (beta y)
        (ccrReindex (alpha y) ip)).left
          e')).snd.snd.left s_cast' := by
  subst hm
  subst he
  have hse := eq_of_heq hs
  subst hse
  rfl

private lemma
    lkanLAdj_naturality_right_fiber_elem
    {r' : PolyFunctorBetweenCat.{u, u} Z Y}
    (alpha : polyBetweenLKanObj q p ⟶ r)
    (beta : r ⟶ r') (y : Y)
    (ip : ccrIndex (p y))
    (d : (polyBetweenCompFamily r' q y
      (lkanLAdjReindex q
        (alpha ≫ beta) y ip)).left) :
    lkanLAdjFiberLeft q (alpha ≫ beta)
      y ip d =
    lkanLAdjFiberLeft q alpha y ip
      (polyBetweenWhiskerRightFiberLeft
        q beta y
        (lkanLAdjReindex q alpha y ip)
        (cast (congrArg
          (fun idx =>
            (polyBetweenCompFamily r' q y
              idx).left)
          (lkanLAdj_naturality_right_base_eq
            q alpha beta y ip)) d)) := by
  obtain ⟨e, s⟩ := d
  simp only [lkanLAdjFiberLeft,
    polyBetweenWhiskerRightFiberLeft]
  refine lkanLAdj_fiber_combined_helper
    q alpha beta y ip
    (ccrComp_fiberMor
      (f := alpha y) (g := beta y)
      (i := ip))
    e _
    (cast_polyBetweenCompFamily_sigma_fst
      q
      (lkanLAdj_naturality_right_base_eq
        q alpha beta y ip)
      ⟨e, s⟩)
    ?_
  exact (cast_heq _ _).trans
    ((cast_heq _ _).trans
      ((cast_polyBetweenCompFamily_sigma_snd_heq
        q
        (lkanLAdj_naturality_right_base_eq
          q alpha beta y ip)
        ⟨e, s⟩).trans
        (cast_heq _ s).symm))

private lemma
    polyBetweenLKanHomEquiv_naturality_right
    {r' : PolyFunctorBetweenCat.{u, u} Z Y}
    (alpha : polyBetweenLKanObj q p ⟶ r)
    (beta : r ⟶ r') (y : Y) :
    polyBetweenLKanLAdj q (alpha ≫ beta) y =
    polyBetweenLKanLAdj q alpha y ≫
      polyBetweenWhiskerRight q beta y := by
  simp only [polyBetweenLKanLAdj,
    polyBetweenWhiskerRight, ccrComp_mk,
    ccrHomMk_reindex, ccrHomMk_fiberMor]
  have hbase :
      (ccrHomMk
        (lkanLAdjReindex q (alpha ≫ beta) y)
        (lkanLAdjFiber q
          (alpha ≫ beta) y)).base =
      (ccrHomMk
        (polyBetweenWhiskerRightReindex
          q beta y ∘
          lkanLAdjReindex q alpha y)
        (fun i =>
          polyBetweenWhiskerRightFiber
            q beta y
            (lkanLAdjReindex q alpha y i) ≫
          lkanLAdjFiber q alpha y i)).base :=
    funext
      (lkanLAdj_naturality_right_base_eq
        q alpha beta y)
  refine ccrHom_ext_subst _ _ hbase ?_
  intro ip
  simp only [ccrHomMk_fiberMor]
  simp only [lkanLAdjFiber,
    polyBetweenWhiskerRightFiber]
  ext d
  simp only [Over.homMk_left, Over.comp_left,
    types_comp_apply]
  rw [eqToHom_polyBetweenComp_left_id]
  swap
  · exact congrFun hbase ip
  exact lkanLAdj_naturality_right_fiber_elem
    q alpha beta y ip d

def polyBetweenLKanCoreHomEquiv :
    Adjunction.CoreHomEquiv
      (polyBetweenLKanFunctor (Y := Y) q)
      (polyBetweenPrecompFunctor (Y := Y) q) where
  homEquiv := polyBetweenLKanHomEquiv q
  homEquiv_naturality_left_symm := by
    intro p₁ p₂ r f g
    rfl
  homEquiv_naturality_right := by
    intro p r r' alpha beta
    funext y
    exact
      polyBetweenLKanHomEquiv_naturality_right
        q alpha beta y

def polyBetweenLKanAdj :
    polyBetweenLKanFunctor (Y := Y) q ⊣
    polyBetweenPrecompFunctor (Y := Y) q :=
  Adjunction.mkOfHomEquiv
    (polyBetweenLKanCoreHomEquiv q)

end Adjunction

end LeftKanExtension

end GebLean
