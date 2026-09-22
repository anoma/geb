/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Prototypes.Typechecker.Coequalizers
public import Geb.Prototypes.Typechecker.Classifier
public import Geb.Prototypes.Typechecker.Exponentials
public import Geb.Prototypes.Typechecker.Initial
public import Geb.Prototypes.Typechecker.SizeBounded
public import Geb.Prototypes.Typechecker.Terminal
public import Geb.Mathlib.CategoryTheory.ElementaryTopos
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Topos.Classifier

set_option doc.verso true in
/-!
# Limit and colimit structure for decision problems

The singleton-fiber construction supplies a chosen terminal cone and the
corresponding existence instance. Pair coding supplies binary product cones.
Together these feed {name}`CategoryTheory.CartesianMonoidalCategory.ofChosenFiniteProducts`,
supplying the cartesian field of {lit}`ElementaryTopos`.
The constant-false construction supplies the chosen cocone required by its
{lit}`initialCocone` field, together with initial-object existence.
Tagged-union coding supplies its {lit}`binaryCoproductCocone` field and the
corresponding binary-coproduct existence instance.
Agreement filtering supplies its {lit}`equalizerCone` field and equalizer existence.
Class normalization together with agreement filtering supplies its
{lit}`coequalizerCocone` field and coequalizer existence.
Extensional function codes supply its {lit}`closed` field over the chosen
cartesian structure. An admissible function without fixed points prevents
closure of an everywhere-accepting object.
Image checkers and admissible image inverses supply its {lit}`classifier` field.
The necessary image-test theorem also applies to classifiers with more than two truth values.

## Main definitions

* {lit}`DecisionProblem.terminalConeOfSingleton` packages an accessible singleton.
* {lit}`DecisionProblem.terminalCone` specializes to a checker accepting exactly true.
* {lit}`DecisionProblem.hasTerminal` registers terminal-object existence under
  {lit}`DecisionProblem.HasTrueSingletonChecker`.
* {lit}`DecisionProblem.initialCocone` packages the constant-false checker.
* {lit}`DecisionProblem.hasInitial` registers initial-object existence under
  {lit}`DecisionProblem.HasFalseChecker`.
* {lit}`DecisionProblem.binaryProductCone` packages the pair-coding construction.
* {lit}`DecisionProblem.hasBinaryProducts` supplies the corresponding existence instance.
* {lit}`DecisionProblem.cartesianMonoidalCategory` combines terminal and product data.
* {lit}`DecisionProblem.binaryCoproductCocone` packages the tagged-union construction.
* {lit}`DecisionProblem.hasBinaryCoproducts` supplies the corresponding existence instance.
* {lit}`DecisionProblem.equalizerCone` packages the agreement-filtering construction.
* {lit}`DecisionProblem.hasEqualizers` supplies the corresponding existence instance.
* {lit}`DecisionProblem.coequalizerCocone` packages the class-normalization construction.
* {lit}`DecisionProblem.hasCoequalizers` supplies the corresponding existence instance.
* {lit}`DecisionProblem.closedOfCoding` supplies a right adjoint to product with one object.
* {lit}`DecisionProblem.monoidalClosed` supplies the closed field from function coding.
* {lit}`DecisionProblem.ClassifierData.classifier` packages subobject classification.
* {lit}`DecisionProblem.exists_image_test_of_classifier` is the necessary image condition.
* {lit}`DecisionProblem.not_monoidalClosed_of_classifierData` proves that the two-valued
  classifier package and pair coding preclude cartesian closure.
* {lit}`DecisionProblem.elementaryTopos` assembles all the sufficient conditions.
* {lit}`DecisionProblem.not_closed` is the diagonal obstruction to an exponential
  of the everywhere-accepting object into itself.
* {lit}`DecisionProblem.not_hasBinaryProducts_of_sizeBounded` rules out binary products
  for unary size-bounded algebras with an everywhere-accepting object.
* {lit}`DecisionProblem.not_hasBinaryCoproducts_of_sizeBounded` rules out binary
  coproducts for the same algebras.

## Implementation notes

This module only packages the universal properties proved in the core modules.
Mathlib's empty-diagram cones and cocones depend on {name}`Classical.choice`, so this wrapper
is admitted to {lit}`GebMeta.classicalAllowedModules`.

## Tags

decision problem, terminal object, initial object, binary product, binary coproduct,
equalizer, coequalizer, exponential, subobject classifier, elementary topos
-/
set_option doc.verso true

@[expose] public section

universe u

namespace GebProto.EndomorphismCategory.DecisionProblem

open CategoryTheory Limits

variable {B : Type u} {S : Submonoid (Function.End B)} {t f : B}

/-- The chosen terminal cone associated with an accessible singleton checker. -/
def terminalConeOfSingleton (T : DecisionProblem S t f) (a : B)
    (hT : ∀ x : B, T.checker.val x = t ↔ x = a)
    (r : AdmissibleEndomorphism S) (hr : r.val t = a) :
    LimitCone (Functor.empty.{0} (DecisionProblem S t f)) where
  cone := asEmptyCone T
  isLimit := by
    letI := uniqueToSingleton T a hT r hr
    exact IsTerminal.ofUnique T

/-- The terminal cone supplied by an admissible checker accepting exactly true. -/
def terminalCone (T : DecisionProblem S t f)
    (hT : ∀ x : B, T.checker.val x = t ↔ x = t) :
    LimitCone (Functor.empty.{0} (DecisionProblem S t f)) :=
  terminalConeOfSingleton T t hT 1 rfl

/-- An admissible true-singleton checker supplies a terminal object. -/
instance hasTerminal [h : Fact (HasTrueSingletonChecker S t f)] :
    HasTerminal (DecisionProblem S t f) := by
  obtain ⟨T, hT⟩ := h.out
  exact IsTerminal.hasTerminal (terminalCone T hT).isLimit

/-- The chosen initial cocone supplied by the admissible constant-false checker. -/
def initialCocone (h : HasFalseChecker S t f) :
    ColimitCocone (Functor.empty.{0} (DecisionProblem S t f)) where
  cocone := asEmptyCocone (rejectAll h)
  isColimit := by
    letI := uniqueFromFalse h
    exact IsInitial.ofUnique (rejectAll h)

/-- An admissible constant-false checker supplies an initial object. -/
instance hasInitial [h : Fact (HasFalseChecker S t f)] : HasInitial (DecisionProblem S t f) :=
  IsInitial.hasInitial (initialCocone h.out).isColimit

/-- The chosen binary product cone provided by pair coding and checker conjunction. -/
def binaryProductCone (d : ProductCoding S t f) (X Y : DecisionProblem S t f) :
    LimitCone (pair X Y) where
  cone := BinaryFan.mk (d.fst X Y) (d.snd X Y)
  isLimit := BinaryFan.IsLimit.mk _ d.lift d.lift_fst d.lift_snd
    (fun r s _ hl hr ↦ d.hom_ext (hl.trans (d.lift_fst r s).symm)
      (hr.trans (d.lift_snd r s).symm))

/-- Pair coding supplies a limit for each binary product diagram. -/
instance hasLimit_pair [h : Nonempty (ProductCoding S t f)] {X Y : DecisionProblem S t f} :
    HasLimit (pair X Y) := by
  obtain ⟨d⟩ := h
  exact ⟨⟨binaryProductCone d X Y⟩⟩

/-- Pair coding supplies binary products. -/
instance hasBinaryProducts [Nonempty (ProductCoding S t f)] :
    HasBinaryProducts (DecisionProblem S t f) :=
  hasBinaryProducts_of_hasLimit_pair _

/-- The cartesian structure used by the elementary-topos interface, from the chosen singleton
checker and pair coding. It remains explicit to retain the chosen computational data. -/
@[instance_reducible]
def cartesianMonoidalCategory (T : DecisionProblem S t f)
    (hT : ∀ x : B, T.checker.val x = t ↔ x = t) (d : ProductCoding S t f) :
    CartesianMonoidalCategory (DecisionProblem S t f) :=
  .ofChosenFiniteProducts (terminalCone T hT) (binaryProductCone d)

/-- The chosen tagged-union cocone, with the type used by the elementary-topos interface. -/
def binaryCoproductCocone (d : CoproductCoding S t f) (X Y : DecisionProblem S t f) :
    ColimitCocone (pair X Y) where
  cocone := BinaryCofan.mk (d.inl X Y) (d.inr X Y)
  isColimit := BinaryCofan.IsColimit.mk _ d.desc d.inl_desc d.inr_desc
    (fun r s _ hl hr ↦ d.hom_ext (hl.trans (d.inl_desc r s).symm)
      (hr.trans (d.inr_desc r s).symm))

/-- Tagged-union coding supplies a colimit for each binary coproduct diagram. -/
instance hasColimit_pair [h : Nonempty (CoproductCoding S t f)] {X Y : DecisionProblem S t f} :
    HasColimit (pair X Y) := by
  obtain ⟨d⟩ := h
  exact ⟨⟨binaryCoproductCocone d X Y⟩⟩

/-- Tagged-union coding supplies binary coproducts. -/
instance hasBinaryCoproducts [Nonempty (CoproductCoding S t f)] :
    HasBinaryCoproducts (DecisionProblem S t f) :=
  hasBinaryCoproducts_of_hasColimit_pair _

/-- The chosen equalizer cone supplied by checkers for agreement on the source fiber. -/
def equalizerCone (d : EqualizerCheckers S t f) {X Y : DecisionProblem S t f} (r s : X ⟶ Y) :
    LimitCone (parallelPair r s) where
  cone := Fork.ofι (d.ι r s) (d.condition r s)
  isLimit := Fork.IsLimit.mk _ (fun c ↦ d.lift r s c.ι c.condition)
    (fun c ↦ d.lift_ι r s c.ι c.condition)
    (fun c _ hm ↦ d.hom_ext (hm.trans (d.lift_ι r s c.ι c.condition).symm))

/-- Agreement filtering supplies a limit for each parallel pair. -/
instance hasLimit_parallelPair [h : Nonempty (EqualizerCheckers S t f)]
    {X Y : DecisionProblem S t f} (r s : X ⟶ Y) : HasLimit (parallelPair r s) := by
  obtain ⟨d⟩ := h
  exact ⟨⟨equalizerCone d r s⟩⟩

/-- Agreement filtering supplies equalizers. -/
instance hasEqualizers [Nonempty (EqualizerCheckers S t f)] :
    HasEqualizers (DecisionProblem S t f) := hasEqualizers_of_hasLimit_parallelPair _

/-- The chosen coequalizer cocone supplied by an admissible class normalizer. -/
def coequalizerCocone (d : EqualizerCheckers S t f) {X Y : DecisionProblem S t f}
    {r s : X ⟶ Y} (n : ClassNormalizer r s) : ColimitCocone (parallelPair r s) where
  cocone := Cofork.ofπ (n.π d) (n.comp_π d)
  isColimit := Cofork.IsColimit.mk _ (fun c ↦ n.desc d c.π)
    (fun c ↦ n.π_desc d c.π c.condition)
    (fun c _ hm ↦ n.hom_ext d (hm.trans (n.π_desc d c.π c.condition).symm))

/-- Class normalization and agreement filtering supply a colimit for each parallel pair. -/
instance hasColimit_parallelPair [hd : Nonempty (EqualizerCheckers S t f)]
    [hn : Nonempty (CoequalizerNormalForms S t f)]
    {X Y : DecisionProblem S t f} (r s : X ⟶ Y) : HasColimit (parallelPair r s) := by
  obtain ⟨d⟩ := hd
  obtain ⟨n⟩ := hn
  exact ⟨⟨coequalizerCocone d (n r s)⟩⟩

/-- Class normalization and agreement filtering supply coequalizers. -/
instance hasCoequalizers [Nonempty (EqualizerCheckers S t f)]
    [Nonempty (CoequalizerNormalForms S t f)] : HasCoequalizers (DecisionProblem S t f) :=
  hasCoequalizers_of_hasColimit_parallelPair _

section Exponentials

open MonoidalCategory

variable (T : DecisionProblem S t f) (hT : ∀ x, T.checker.val x = t ↔ x = t)
  (p : ProductCoding S t f)

/-- Left whiskering in the chosen cartesian structure is substitution in the second
component of the product coding. -/
theorem whiskerLeft_eq_lift (X : DecisionProblem S t f) {Z Z' : DecisionProblem S t f}
    (g : Z' ⟶ Z) :
    letI := cartesianMonoidalCategory T hT p
    X ◁ g = p.lift (p.fst X Z') (p.snd X Z' ≫ g) := by
  let := cartesianMonoidalCategory T hT p
  apply p.hom_ext
  · exact (CartesianMonoidalCategory.whiskerLeft_fst X g).trans (p.lift_fst _ _).symm
  · exact (CartesianMonoidalCategory.whiskerLeft_snd X g).trans (p.lift_snd _ _).symm

/-- Extensional function coding supplies the right adjoint to product with a fixed object. -/
@[instance_reducible]
def closedOfCoding (X : DecisionProblem S t f) (d : ∀ Y, ExponentialCoding p X Y) :
    letI := cartesianMonoidalCategory T hT p
    Closed X := by
  letI := cartesianMonoidalCategory T hT p
  let equiv (Z Y : DecisionProblem S t f) :
      ((tensorLeft X).obj Z ⟶ Y) ≃ (Z ⟶ (d Y).codes) := (d Y).homEquiv
  have naturality : ∀ Z' Z Y (g : Z' ⟶ Z) (h : (tensorLeft X).obj Z ⟶ Y),
      equiv Z' Y ((tensorLeft X).map g ≫ h) = g ≫ equiv Z Y h := by
    intro Z' Z Y g h
    change (d Y).curry (X ◁ g ≫ h) = g ≫ (d Y).curry h
    rw [whiskerLeft_eq_lift T hT p]
    exact (d Y).curry_natural g h
  exact
    { rightAdj := Adjunction.rightAdjointOfEquiv equiv naturality
      adj := Adjunction.adjunctionOfEquivRight equiv naturality }

/-- The closed field of the elementary-topos interface, retaining the chosen coding data. -/
@[instance_reducible]
def monoidalClosed (d : ∀ X Y, ExponentialCoding p X Y) :
    letI := cartesianMonoidalCategory T hT p
    MonoidalClosed (DecisionProblem S t f) :=
  letI := cartesianMonoidalCategory T hT p
  { closed X := closedOfCoding T hT p X (d X) }

/-- A fixed-point-free admissible function prevents the everywhere-accepting object
from being closed in the chosen cartesian structure. -/
theorem not_closed (U : DecisionProblem S t f) (hU : ∀ x, U.checker.val x = t)
    (a : S) (ha : ∀ y, a.val y ≠ y) :
    letI := cartesianMonoidalCategory T hT p
    ¬Nonempty (Closed U) := by
  let := cartesianMonoidalCategory T hT p
  rintro ⟨h⟩
  let := h
  obtain ⟨y, hy⟩ := exists_fixed_point_of_exponential p U ((ihom U).obj U) hU
    ((ihom.ev U).app U) (fun k ↦ ⟨MonoidalClosed.curry k, by
      rw [← whiskerLeft_eq_lift T hT p]
      exact MonoidalClosed.uncurry_curry k⟩) a
  exact ha y hy

/-- The diagonal obstruction also rules out the closed field of the elementary-topos
interface for the chosen cartesian structure. -/
theorem not_monoidalClosed (U : DecisionProblem S t f) (hU : ∀ x, U.checker.val x = t)
    (a : S) (ha : ∀ y, a.val y ≠ y) :
    letI := cartesianMonoidalCategory T hT p
    ¬Nonempty (MonoidalClosed (DecisionProblem S t f)) := by
  let := cartesianMonoidalCategory T hT p
  rintro ⟨h⟩
  exact not_closed T hT p U hU a ha ⟨h.closed U⟩

end Exponentials

section Classifiers

variable {X Y K O : DecisionProblem S t f}

/-- With admissible constants, pulling back truth from a singleton detects the image on points. -/
theorem image_iff_of_isPullback (hS : HasConstants S) (m : X ⟶ Y) (k : X ⟶ K)
    (chi : Y ⟶ O) (truth : K ⟶ O) (hp : IsPullback m k chi truth)
    (a : Fiber K) (ha : ∀ b : Fiber K, b = a) (y : Fiber Y) :
    chi.restrict y = truth.restrict a ↔ ∃ x : Fiber X, m.restrict x = y := by
  constructor
  · intro he
    have hw : (constantRep hS K y).toHom ≫ chi =
        (constantRep hS K a).toHom ≫ truth := by
      apply Hom.ext
      funext z
      simp only [Hom.restrict_comp, Function.comp_apply]
      exact he
    obtain ⟨l, hl, _⟩ := hp.exists_lift _ _ hw
    refine ⟨l.restrict a, ?_⟩
    apply Subtype.ext
    have he := congrArg (fun r : K ⟶ Y ↦ (r.restrict a).val) hl
    simp only [Hom.restrict_comp, Function.comp_apply] at he
    exact he
  · rintro ⟨x, rfl⟩
    have he := congrArg (fun r : X ⟶ O ↦ r.restrict x) hp.w
    simpa only [Hom.restrict_comp, Function.comp_apply, ha (k.restrict x)] using he

/-- Every classifier tests mono images by equality with a fixed truth point, provided constants
are admissible and some object has an accepted point. The classifier need not be two-valued. -/
theorem image_iff_of_classifier (hS : HasConstants S)
    (c : CategoryTheory.Classifier (DecisionProblem S t f))
    {T : DecisionProblem S t f} (a : Fiber T) (m : X ⟶ Y) [Mono m] (y : Fiber Y) :
    (c.χ m).restrict y = c.truth.restrict ((c.χ₀ T).restrict a) ↔
      ∃ x : Fiber X, m.restrict x = y := by
  apply image_iff_of_isPullback hS m (c.χ₀ X) (c.χ m) c.truth (c.isPullback m)
  intro b
  have he := c.isTerminalΩ₀.hom_ext (constantRep hS T b).toHom (c.χ₀ T)
  exact congrArg (fun r : T ⟶ c.Ω₀ ↦ r.restrict a) he

/-- On accepted target inputs, every mono image is an equality fiber of an admissible
endomorphism if a classifier exists. This is a necessary condition on the function subset. -/
theorem exists_image_test_of_classifier (hS : HasConstants S)
    (c : CategoryTheory.Classifier (DecisionProblem S t f))
    {T : DecisionProblem S t f} (a : Fiber T) (m : X ⟶ Y) [Mono m] :
    ∃ r : S, ∃ v : B, ∀ y : Fiber Y,
      r.val y.val = v ↔ ∃ x : Fiber X, m.restrict x = y := by
  obtain ⟨r, hr⟩ : ∃ r : S, ∀ y : Fiber Y, r.val y.val = ((c.χ m).restrict y).val :=
    Quotient.inductionOn (c.χ m) fun k ↦ ⟨k.val, fun _ ↦ rfl⟩
  refine ⟨r, (c.truth.restrict ((c.χ₀ T).restrict a)).val, fun y ↦ ?_⟩
  rw [hr y]
  exact Subtype.ext_iff.symm.trans (image_iff_of_classifier hS c a m y)

namespace ClassifierData

variable (d : ClassifierData S t f)

/-- The image inverse supplies the universal property of the characteristic square. -/
theorem isPullback (m : X ⟶ Y) [Mono m] :
    IsPullback m (d.toTerminal X) (d.chi m) d.truth := by
  apply IsPullback.of_isLimit' ⟨d.condition m⟩
  apply PullbackCone.isLimitAux'
  intro s
  let l := d.liftWithProof m s.fst (d.lands_in_image m s.fst s.snd s.condition)
  refine ⟨l.val, l.property, ?_, fun h _ ↦ (cancel_mono m).mp (h.trans l.property.symm)⟩
  exact IsTerminal.hom_ext (terminalCone d.terminal d.terminal_pass_iff).isLimit _ _

/-- Admissible image tests and image inverses supply the classifier field of an elementary topos. -/
def classifier : CategoryTheory.Classifier (DecisionProblem S t f) where
  Ω₀ := d.terminal
  Ω := d.omega
  truth := d.truth
  mono_truth := IsTerminal.mono_from
    (terminalCone d.terminal d.terminal_pass_iff).isLimit _
  χ₀ := d.toTerminal
  χ m _ := d.chi m
  isPullback m _ := d.isPullback m
  uniq m _ _ _ hp := by
    apply d.chi_unique m
    intro y
    have he := image_iff_of_isPullback d.constants _ _ _ _ hp
      ⟨t, (d.terminal_pass_iff t).mpr rfl⟩
      (fun b ↦ Subtype.ext ((d.terminal_pass_iff b.val).mp b.property)) y
    exact (Subtype.ext_iff.symm.trans he).trans
      ⟨fun ⟨x, hx⟩ ↦ ⟨x, congrArg Subtype.val hx⟩,
        fun ⟨x, hx⟩ ↦ ⟨x, Subtype.ext hx⟩⟩

end ClassifierData

/-- Classification data supplies existence of a subobject classifier. -/
instance hasSubobjectClassifier [d : Nonempty (ClassifierData S t f)] :
    HasClassifier (DecisionProblem S t f) := by
  obtain ⟨d⟩ := d
  exact ⟨⟨d.classifier⟩⟩

end Classifiers

/-- The two-valued classifier package and pair coding already obstruct cartesian closure:
the false singleton's image checker supplies an endomorphism without fixed points. -/
theorem not_monoidalClosed_of_classifierData (d : ClassifierData S t f)
    (p : ProductCoding S t f) :
    letI := cartesianMonoidalCategory d.terminal d.terminal_pass_iff p
    ¬Nonempty (MonoidalClosed (DecisionProblem S t f)) := by
  obtain ⟨a, ha⟩ := d.exists_fixed_point_free
  let U : DecisionProblem S t f :=
    ⟨⟨fun _ ↦ t, d.constants t⟩, ⟨d.terminal.twoValued.1, fun _ ↦ Or.inl rfl⟩⟩
  exact not_monoidalClosed d.terminal d.terminal_pass_iff p U (fun _ ↦ rfl) a ha

/-- Assemble the sufficient conditions into the elementary-topos interface. This is conditional
bookkeeping: {name}`not_monoidalClosed_of_classifierData` rules out simultaneous inputs. -/
@[instance_reducible]
def elementaryTopos (d : ClassifierData S t f) (p : ProductCoding S t f)
    (c : CoproductCoding S t f) (e : EqualizerCheckers S t f)
    (n : CoequalizerNormalForms S t f) (h : ∀ X Y, ExponentialCoding p X Y) :
    ElementaryTopos (DecisionProblem S t f) where
  cartesian := cartesianMonoidalCategory d.terminal d.terminal_pass_iff p
  closed := monoidalClosed d.terminal d.terminal_pass_iff p h
  initialCocone := initialCocone ⟨d.terminal.twoValued.1, d.constants f⟩
  binaryCoproductCocone := binaryCoproductCocone c
  equalizerCone := equalizerCone e
  coequalizerCocone r s := coequalizerCocone e (n r s)
  classifier := d.classifier

/-- When every admissible injection is surjective, the everywhere-accepting object has no
binary product with itself. -/
theorem not_hasLimit_pair_self
    (hS : ∀ r : S, Function.Injective r.val → Function.Surjective r.val)
    (U : DecisionProblem S t f) (hU : ∀ x, U.checker.val x = t) :
    ¬HasLimit (pair U U) := by
  intro h
  let := h
  obtain ⟨r, hinj, hsurj⟩ := exists_injective_not_surjective U (Limits.prod U U) hU
    Limits.prod.fst Limits.prod.snd
    (fun r s ↦ ⟨Limits.prod.lift r s, Limits.prod.lift_fst r s, Limits.prod.lift_snd r s⟩)
  exact hsurj (hS r hinj)

/-- Unary size-bounded algebras admitting an everywhere-accepting problem lack binary
products, regardless of their completeness for decision problems. -/
theorem not_hasBinaryProducts_of_sizeBounded
    {S : Submonoid (Function.End (List Bool))} {t f : List Bool}
    (hS : ∀ r : S, ∃ e : Geb.SizeBounded.SOf 1, ∀ w, e.sem (fun _ ↦ w) = r.val w)
    (U : DecisionProblem S t f) (hU : ∀ x, U.checker.val x = t) :
    ¬HasBinaryProducts (DecisionProblem S t f) := by
  intro h
  let := h
  exact not_pairing_of_sizeBounded hS U (Limits.prod U U) hU Limits.prod.fst Limits.prod.snd
    (fun r s ↦ ⟨Limits.prod.lift r s, Limits.prod.lift_fst r s, Limits.prod.lift_snd r s⟩)

/-- When every admissible injection is surjective, the everywhere-accepting object has no
binary coproduct with itself. -/
theorem not_hasColimit_pair_self
    (hS : ∀ r : S, Function.Injective r.val → Function.Surjective r.val)
    (U : DecisionProblem S t f) (hU : ∀ x, U.checker.val x = t) :
    ¬HasColimit (pair U U) := by
  intro h
  let := h
  obtain ⟨r, hinj, hsurj⟩ := exists_injective_not_surjective_of_copairing U (Limits.coprod U U)
    hU Limits.coprod.inl Limits.coprod.inr
    (fun r s ↦ ⟨Limits.coprod.desc r s, Limits.coprod.inl_desc r s, Limits.coprod.inr_desc r s⟩)
  exact hsurj (hS r hinj)

/-- Unary size-bounded algebras admitting an everywhere-accepting problem lack binary
coproducts, regardless of their completeness for decision problems. -/
theorem not_hasBinaryCoproducts_of_sizeBounded
    {S : Submonoid (Function.End (List Bool))} {t f : List Bool}
    (hS : ∀ r : S, ∃ e : Geb.SizeBounded.SOf 1, ∀ w, e.sem (fun _ ↦ w) = r.val w)
    (U : DecisionProblem S t f) (hU : ∀ x, U.checker.val x = t) :
    ¬HasBinaryCoproducts (DecisionProblem S t f) := by
  intro h
  let := h
  exact not_copairing_of_sizeBounded hS U (Limits.coprod U U) hU
    Limits.coprod.inl Limits.coprod.inr
    (fun r s ↦ ⟨Limits.coprod.desc r s, Limits.coprod.inl_desc r s, Limits.coprod.inr_desc r s⟩)

end GebProto.EndomorphismCategory.DecisionProblem
