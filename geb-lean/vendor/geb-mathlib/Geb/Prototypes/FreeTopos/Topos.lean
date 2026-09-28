/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Prototypes.FreeTopos.Category
public import Geb.Mathlib.CategoryTheory.ElementaryTopos

set_option doc.verso true in
/-!
# A model of the theory of an elementary topos is an elementary topos

The category of a model of the partial Horn theory of an elementary topos carries the chosen
structure of {name}`CategoryTheory.ElementaryTopos`: the terminal object and binary products as
the cartesian structure, the initial object, binary coproducts, equalizers and coequalizers as
chosen limit cones and colimit cocones, exponentials as the closed structure, and the subobject
classifier; each is built from the model's operations and proved universal from the axioms.

## Main definitions

* {lit}`ToposModel.terminalCone`, {lit}`ToposModel.binaryProductCone`,
  {lit}`ToposModel.initialCocone`, {lit}`ToposModel.binaryCoproductCocone`,
  {lit}`ToposModel.equalizerCone`, {lit}`ToposModel.coequalizerCocone` — the chosen finite limits
  and colimits.
* {lit}`ToposModel.cartesianMonoidalCategory`, {lit}`ToposModel.monoidalClosed` — the cartesian
  and closed structures.
* {lit}`ToposModel.classifier` — the subobject classifier.
* {lit}`ToposModel.elementaryTopos` — the elementary topos.

## Tags

elementary topos, model, finite limits, finite colimits
-/

set_option doc.verso true

@[expose] public section

namespace Geb.FreeTopos

open CategoryTheory Limits

universe v

namespace ToposModel

variable (T : ToposModel.{v})

/-- The chosen terminal cone, whose point is the terminal object at reducible
transparency. -/
abbrev terminalCone : LimitCone (Functor.empty.{0} T.Cat) where
  cone := { pt := T.one, π := (asEmptyCone T.one).π }
  isLimit := IsTerminal.ofUniqueHom (fun a ↦ T.toOne a) (fun _ f ↦ T.toOne_uniq f)

/-- The chosen binary product cone, whose point is the product at reducible transparency, so
that the cartesian structure's tensor product is the product. -/
abbrev binaryProductCone (a b : T.Cat) : LimitCone (Limits.pair a b) where
  cone := { pt := T.prod a b, π := (BinaryFan.mk (T.prodFst a b) (T.prodSnd a b)).π }
  isLimit := BinaryFan.IsLimit.mk _ (fun f g ↦ prodLift f g) (fun f g ↦ prodLift_fst f g)
    (fun f g ↦ prodLift_snd f g)
    (fun _ _ m hf hg ↦ (prodLift_uniq m).trans (congrArg₂ prodLift hf hg))

/-- The chosen initial cocone. -/
def initialCocone : ColimitCocone (Functor.empty.{0} T.Cat) where
  cocone := asEmptyCocone T.zero
  isColimit := IsInitial.ofUniqueHom (fun a ↦ T.fromZero a) (fun _ f ↦ T.fromZero_uniq f)

/-- The chosen binary coproduct cocone. -/
def binaryCoproductCocone (a b : T.Cat) : ColimitCocone (Limits.pair a b) where
  cocone := BinaryCofan.mk (T.coprodInl a b) (T.coprodInr a b)
  isColimit := BinaryCofan.IsColimit.mk _ (fun f g ↦ coprodDesc f g)
    (fun f g ↦ coprodInl_desc f g) (fun f g ↦ coprodInr_desc f g)
    (fun _ _ m hl hr ↦ (coprodDesc_uniq m).trans (congrArg₂ coprodDesc hl hr))

/-- The chosen equalizer cone. -/
def equalizerCone {a b : T.Cat} (f g : a ⟶ b) : LimitCone (parallelPair f g) where
  cone := Fork.ofι (equalizerι f g) (equalizerι_condition f g)
  isLimit := Fork.IsLimit.mk _ (fun s ↦ equalizerLift s.ι s.condition)
    (fun s ↦ equalizerLift_ι _ _) (fun s m hm ↦ by rw [equalizerLift_uniq m]; congr)

/-- The chosen coequalizer cocone. -/
def coequalizerCocone {a b : T.Cat} (f g : a ⟶ b) : ColimitCocone (parallelPair f g) where
  cocone := Cofork.ofπ (coequalizerπ f g) (coequalizerπ_condition f g)
  isColimit := Cofork.IsColimit.mk _ (fun s ↦ coequalizerDesc s.π s.condition)
    (fun s ↦ coequalizerπ_desc _ _) (fun s m hm ↦ by rw [coequalizerDesc_uniq m]; congr)

/-- The cartesian monoidal structure, from the chosen terminal cone and binary product
cones. -/
@[instance_reducible]
def cartesianMonoidalCategory : CartesianMonoidalCategory T.Cat :=
  CartesianMonoidalCategory.ofChosenFiniteProducts T.terminalCone T.binaryProductCone

attribute [local instance] cartesianMonoidalCategory

open MonoidalCategory

/-- The cartesian structure's first projection is the model's. -/
theorem fst_eq (a c : T.Cat) : SemiCartesianMonoidalCategory.fst a c = T.prodFst a c := rfl

/-- The cartesian structure's second projection is the model's. -/
theorem snd_eq (a c : T.Cat) : SemiCartesianMonoidalCategory.snd a c = T.prodSnd a c := rfl

/-- Left whiskering by an object, after the symmetry, is the product with the identity
followed by the symmetry. -/
theorem swap_whiskerLeft (a : T.Cat) {c d : T.Cat} (f : c ⟶ d) :
    T.swap c a ≫ (a ◁ f) = prodMap f a ≫ T.swap d a := by
  refine prod_hom_ext (m := T.swap c a ≫ (a ◁ f)) ?_ ?_
  · rw [Category.assoc]
    erw [CartesianMonoidalCategory.whiskerLeft_fst]
    simp only [fst_eq, swap, prodMap, Category.assoc, prodLift_fst, prodLift_snd]
  · rw [Category.assoc]
    erw [CartesianMonoidalCategory.whiskerLeft_snd]
    simp only [snd_eq, swap, prodMap, Category.assoc, prodLift_fst, prodLift_snd,
      prodLift_snd_assoc]

/-- The exponential's equivalence of hom-sets at the product, through its symmetry. -/
def expHomEquivProd (a c b : T.Cat) : (T.prod a c ⟶ b) ≃ (c ⟶ T.exp a b) where
  toFun g := curry (T.swap c a ≫ g)
  invFun h := T.swap a c ≫ prodMap h a ≫ T.ev a b
  left_inv g := by
    simp only [prodMap_curry_ev, swap_swap_assoc]
  right_inv h := by
    simp only [swap_swap_assoc, curry_uniq]

/-- The exponential's equivalence of hom-sets, at the tensor product of the cartesian
structure. -/
def expHomEquiv (a c b : T.Cat) : ((tensorLeft a).obj c ⟶ b) ≃ (c ⟶ T.exp a b) :=
  T.expHomEquivProd a c b

/-- The exponential's equivalence is natural in its domain. -/
theorem expHomEquiv_naturality (a c' c b : T.Cat) (f : c' ⟶ c)
    (g : (tensorLeft a).obj c ⟶ b) :
    T.expHomEquiv a c' b ((tensorLeft a).map f ≫ g) = f ≫ T.expHomEquiv a c b g := by
  change curry (T.swap c' a ≫ (a ◁ f) ≫ g) = f ≫ curry (T.swap c a ≫ g)
  rw [comp_curry, ← Category.assoc, swap_whiskerLeft, Category.assoc]

/-- The closed structure: the exponential is right adjoint to the product with an object. -/
@[instance_reducible]
def monoidalClosed : MonoidalClosed T.Cat where
  closed a :=
    { rightAdj := Adjunction.rightAdjointOfEquiv (T.expHomEquiv a) (T.expHomEquiv_naturality a)
      adj := Adjunction.adjunctionOfEquivRight (T.expHomEquiv a) (T.expHomEquiv_naturality a) }

/-- A monomorphism is the pullback of truth along its characteristic map. -/
theorem isPullback_chiHom {u x : T.Cat} (m : u ⟶ x) [Mono m] :
    IsPullback m (T.toOne u) (chiHom m (isMono_of_mono m)) T.truth :=
  IsPullback.of_isLimit (PullbackCone.IsLimit.mk (chiHom_square m (isMono_of_mono m))
    (fun s ↦ chiLift m (isMono_of_mono m) s.fst (s.condition.trans (by rw [T.toOne_uniq s.snd])))
    (fun s ↦ chiLift_fac m _ _ _)
    (fun s ↦ (T.toOne_uniq _).trans (T.toOne_uniq s.snd).symm)
    (fun s n h1 _ ↦ (cancel_mono m).mp (h1.trans (chiLift_fac m _ _ _).symm)))

/-- A morphism into the classifier along which a monomorphism is a pullback of truth is its
characteristic map. -/
theorem eq_chiHom_of_isPullback {u x : T.Cat} (m : u ⟶ x) [Mono m] (φ : x ⟶ T.omega)
    (hφ : IsPullback m (T.toOne u) φ T.truth) : φ = chiHom m (isMono_of_mono m) := by
  obtain ⟨hl⟩ := hφ.isLimit'
  have hc : equalizerι φ (T.toOne x ≫ T.truth) ≫ φ =
      T.toOne (equalizer φ (T.toOne x ≫ T.truth)) ≫ T.truth := by
    rw [equalizerι_condition, ← Category.assoc, T.toOne_uniq (equalizerι _ _ ≫ T.toOne x)]
  exact chiHom_uniq m (isMono_of_mono m) φ hφ.w (hl.lift (PullbackCone.mk _ _ hc))
    (PullbackCone.IsLimit.lift_fst hl _ _ hc)

/-- The subobject classifier, with the terminal object as the domain of truth. -/
def classifier : CategoryTheory.Classifier T.Cat :=
  CategoryTheory.Classifier.mkOfTerminalΩ₀ T.one T.terminalCone.isLimit T.omega T.truth
    (fun m _ ↦ chiHom m (isMono_of_mono m)) (fun m _ ↦ T.isPullback_chiHom m)
    (fun m _ φ hφ ↦ T.eq_chiHom_of_isPullback m φ hφ)

/-- A model of the theory of an elementary topos is an elementary topos. -/
@[instance_reducible]
def elementaryTopos : ElementaryTopos T.Cat where
  cartesian := T.cartesianMonoidalCategory
  closed := T.monoidalClosed
  initialCocone := T.initialCocone
  binaryCoproductCocone := T.binaryCoproductCocone
  equalizerCone f g := T.equalizerCone f g
  coequalizerCocone f g := T.coequalizerCocone f g
  classifier := T.classifier

end ToposModel

end Geb.FreeTopos

end
