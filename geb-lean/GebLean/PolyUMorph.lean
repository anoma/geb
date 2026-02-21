import GebLean.Polynomial
import GebLean.Utilities.Equalities
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts

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

private lemma ccrHom_ext_subst
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

private lemma ccrFiberMor_congr
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

private lemma overCoprod_hom_ext
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

section FiniteLimitsColimits

variable {X Y : Type u}

instance : HasFiniteProducts
    (PolyFunctorBetweenCat.{u, u} X Y) :=
  hasFiniteProducts_of_hasProducts _

instance : HasFiniteCoproducts
    (PolyFunctorBetweenCat.{u, u} X Y) :=
  hasFiniteCoproducts_of_hasCoproducts _

end FiniteLimitsColimits

end GebLean
