/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Typechecker.Equalizers
public import Mathlib.Logic.Relation


set_option doc.verso true in
/-!
# Coequalizers from admissible class normalizers

A parallel pair generates an equivalence relation on its accepted target fiber.
An admissible normalizer chooses a member of each generated class and is constant
on the generating pairs. It is consequently constant on whole classes and
idempotent on accepted inputs. Agreement filtering recognizes its fixed points.
These fixed points form a coequalizer, with normalization as the projection.

Maps out of the coequalizer apply the original admissible function to the chosen
representative. A coequalizing map is constant on every generated class, which
proves the factorization law. Every fixed point projects to itself, which proves
uniqueness. No encoded proof of class membership is passed to these maps.

## Main definitions

* {lit}`CoequalizerStep` records the generating pairs on accepted inputs.
* {lit}`CoequalizerRel` is their equivalence closure.
* {lit}`ClassNormalizer` records an admissible choice of class representatives.
* {lit}`CoequalizerNormalForms` supplies these choices for every parallel pair.
* {lit}`ClassNormalizer.coequalizer` recognizes accepted fixed points.

## Main statements

* {lit}`CoequalizerRel.map_eq` propagates a coequalizing equation along generated classes.
* {lit}`coequalizer_kernel_iff` characterizes the identifications of any coequalizer
  by the admissible coequalizing maps.
* {lit}`ClassNormalizer.normalize_eq_iff` characterizes classes by their normal forms.
* {lit}`ClassNormalizer.comp_π`, {lit}`ClassNormalizer.π_desc`, and
  {lit}`ClassNormalizer.hom_ext` establish the coequalizer universal property.

## Implementation notes

The conditions are sufficient: an arbitrary categorical coequalizer need not
have an admissible section selecting representatives in the original target.
The generated relation uses quotient morphisms directly, so it does not depend
on a choice of their representatives. The closure proofs use the recursor of
{name}`Relation.EqvGen`; its proof objects are propositions in the metalanguage.

## Certificates and complexity

A finitary indexed W-type can describe finite derivations using generating edges,
reflexivity, symmetry, and transitivity. Recognizing an encoded derivation does
not decide whether a derivation exists or supply a canonical class representative.
Different proof trees also remain different base values: quotienting morphisms
does not quotient the elements of an object's accepted fiber.

For an explicitly given finite undirected graph, connectivity is decidable in
logspace \[Reingold2008\]. Scanning its numbered vertices for the least
connected one then computes a normal form in logspace. Applying this observation
to string-valued diagrams needs a uniformly accessible finite graph presentation
with polynomial size in the input length, and consistent representative labels
across each component. Finite classes alone do not provide such a presentation.

There is a stronger obstruction for unrestricted diagrams over bitstrings.
Let the source accept valid halting computation histories of a fixed universal
machine, including its input {lit}`e`. The two maps output {lit}`(e, 0)` and
{lit}`(e, 1)` into an everywhere-accepting target. Checking a supplied history and
extracting these endpoints can be done in logspace by rescanning adjacent
configurations; no bound on the length of a possible history is assumed.
Thus the only nonsingleton classes are the pairs whose machine halts, a relation
also used in the proof of Proposition 7.6 of \[GaoGerdes2010\].

A coequalizer projection must identify each halting pair. For a nonhalting input,
the singleton indicator of {lit}`(e, 0)` coequalizes the diagram and separates
its endpoints; {lit}`coequalizer_kernel_iff` forces the projection to separate
them too. Equality of projection outputs would therefore decide halting.
Consequently, no submonoid of total computable string functions containing these
history checkers, endpoint maps, constants, and singleton indicators has all
coequalizers. This includes the full logspace function class. This application
to machine encodings is an informal deduction; the abstract construction and
kernel criterion below are formalized. Recognizing W-type certificates alone
cannot remove this obstruction in the present category.

## Tags

decision problem, coequalizer, equivalence closure, normal form, quotient
-/
set_option doc.verso true

@[expose] public section

universe u

namespace GebProto.EndomorphismCategory.DecisionProblem

open CategoryTheory

variable {B : Type u} {S : Submonoid (Function.End B)} {t f : B}
  {X Y Z : DecisionProblem S t f}

/-- One generating identification between the images of an accepted source input. -/
def CoequalizerStep (r s : X ⟶ Y) (y z : Fiber Y) : Prop :=
  ∃ x : Fiber X, r.restrict x = y ∧ s.restrict x = z

/-- The equivalence relation generated on the accepted target fiber by a parallel pair. -/
def CoequalizerRel (r s : X ⟶ Y) : Fiber Y → Fiber Y → Prop :=
  Relation.EqvGen (CoequalizerStep r s)

/-- A coequalizing morphism is constant on every generated equivalence class. -/
theorem CoequalizerRel.map_eq {r s : X ⟶ Y} (k : Y ⟶ Z) (h : r ≫ k = s ≫ k)
    {y z : Fiber Y} (hyz : CoequalizerRel r s y z) : k.restrict y = k.restrict z := by
  refine Relation.EqvGen.rec (motive := fun y z _ ↦ k.restrict y = k.restrict z)
    ?_ (fun _ ↦ rfl) (fun _ _ _ ih ↦ ih.symm) (fun _ _ _ _ _ ih₁ ih₂ ↦ ih₁.trans ih₂) hyz
  rintro _ _ ⟨x, rfl, rfl⟩
  have hx := congrArg (fun m : X ⟶ Z ↦ m.restrict x) h
  simpa only [Hom.restrict_comp, Function.comp_apply] using hx

/-- Any coequalizer identifies exactly the inputs that all admissible coequalizing
maps identify. Only existence of factorizations is needed for this necessary condition. -/
theorem coequalizer_kernel_iff {Q : DecisionProblem S t f} {r s : X ⟶ Y} (q : Y ⟶ Q)
    (hq : r ≫ q = s ≫ q)
    (factor : ∀ {Z : DecisionProblem S t f} (k : Y ⟶ Z), r ≫ k = s ≫ k →
      ∃ l : Q ⟶ Z, q ≫ l = k) (y z : Fiber Y) :
    q.restrict y = q.restrict z ↔
      ∀ {Z : DecisionProblem S t f} (k : Y ⟶ Z), r ≫ k = s ≫ k →
        k.restrict y = k.restrict z := by
  constructor
  · intro he Z k hk
    obtain ⟨l, hl⟩ := factor k hk
    rw [← hl, Hom.restrict_comp]
    exact congrArg l.restrict he
  · intro h
    exact h q hq

/-- An admissible normalizer sends each accepted input to its generated class and
identifies every generating pair. Together these laws select one member per class. -/
@[ext]
structure ClassNormalizer (r s : X ⟶ Y) : Type u where
  /-- An admissible endomorphism preserving the accepted target fiber. -/
  normalize : Representative Y Y
  /-- Normalization stays within the input's generated equivalence class. -/
  related : ∀ y : Fiber Y, CoequalizerRel r s y (normalize.restrict y)
  /-- Both images of an accepted source input receive the same normal form. -/
  identifies : ∀ x : Fiber X, normalize.restrict (r.restrict x) =
    normalize.restrict (s.restrict x)

/-- Admissible class normalization is available for every parallel pair of morphisms. -/
abbrev CoequalizerNormalForms (S : Submonoid (Function.End B)) (t f : B) : Type u :=
  ∀ {X Y : DecisionProblem S t f} (r s : X ⟶ Y), ClassNormalizer r s

namespace ClassNormalizer

variable {r s : X ⟶ Y} (n : ClassNormalizer r s)

/-- Normalization coequalizes the generating parallel pair. -/
theorem normalizes : r ≫ n.normalize.toHom = s ≫ n.normalize.toHom := by
  apply Hom.ext
  funext x
  simp only [Hom.restrict_comp, Function.comp_apply]
  exact n.identifies x

/-- Two accepted inputs have equal normal forms exactly when they are in the same class. -/
theorem normalize_eq_iff (y z : Fiber Y) :
    n.normalize.restrict y = n.normalize.restrict z ↔ CoequalizerRel r s y z := by
  constructor
  · intro h
    exact Relation.EqvGen.trans _ _ _ (n.related y)
      (h ▸ Relation.EqvGen.symm _ _ (n.related z))
  · intro h
    exact h.map_eq n.normalize.toHom n.normalizes

/-- Normalizing twice has the same result as normalizing once on accepted inputs. -/
theorem idempotent (y : B) (hy : Y.checker.val y = t) :
    n.normalize.val.val (n.normalize.val.val y) = n.normalize.val.val y :=
  (congrArg Subtype.val ((n.related ⟨y, hy⟩).map_eq n.normalize.toHom n.normalizes)).symm

variable (d : EqualizerCheckers S t f)

/-- The decision problem whose accepted inputs are the accepted normal forms. -/
def coequalizer : DecisionProblem S t f := d.filter Y n.normalize.val 1

/-- The coequalizer accepts exactly the fixed points of normalization in the target fiber. -/
theorem coequalizer_pass_iff (y : B) :
    (n.coequalizer d).checker.val y = t ↔
      Y.checker.val y = t ∧ n.normalize.val.val y = y :=
  d.filter_pass_iff Y n.normalize.val 1 y

/-- Normalization lands in the accepted fixed points. -/
def πRep : Representative Y (n.coequalizer d) :=
  ⟨n.normalize.val, fun y hy ↦ (n.coequalizer_pass_iff d _).mpr
    ⟨n.normalize.property y hy, n.idempotent y hy⟩⟩

/-- The coequalizer projection as a quotient morphism. -/
def π : Y ⟶ n.coequalizer d := (n.πRep d).toHom

/-- The projection coequalizes the given parallel morphisms. -/
theorem comp_π : r ≫ n.π d = s ≫ n.π d := by
  apply Hom.ext
  funext x
  simp only [Hom.restrict_comp, Function.comp_apply]
  apply Subtype.ext
  exact congrArg (fun y : Fiber Y ↦ y.val) (n.identifies x)

/-- Restrict a target representative to the accepted normal forms. -/
def descRep (k : Representative Y Z) : Representative (n.coequalizer d) Z :=
  ⟨k.val, fun y hy ↦ k.property y ((n.coequalizer_pass_iff d y).mp hy).1⟩

/-- Restriction to normal forms descends to quotient morphisms. The map is defined
for every morphism; the factorization equation requires it to coequalize the pair. -/
def desc : (Y ⟶ Z) → (n.coequalizer d ⟶ Z) :=
  Quotient.map (n.descRep d) (fun k k' h ↦ (homSetoid_iff _ _).mpr fun y hy ↦
    (homSetoid_iff k k').mp h y ((n.coequalizer_pass_iff d y).mp hy).1)

/-- Projection followed by the induced map recovers every coequalizing morphism. -/
@[simp]
theorem π_desc (k : Y ⟶ Z) (h : r ≫ k = s ≫ k) : n.π d ≫ n.desc d k = k := by
  refine Quotient.inductionOn k (fun k h ↦ ?_) h
  apply (Representative.toHom_eq_iff _ _).mpr
  intro y hy
  exact (congrArg Subtype.val ((n.related ⟨y, hy⟩).map_eq k.toHom h)).symm

/-- Every accepted normal form projects to itself, so projection detects equality
of morphisms out of the coequalizer. -/
theorem hom_ext {k l : n.coequalizer d ⟶ Z} (h : n.π d ≫ k = n.π d ≫ l) : k = l := by
  refine Quotient.inductionOn₂ k l (fun k l h ↦ ?_) h
  apply (Representative.toHom_eq_iff _ _).mpr
  intro y hy
  obtain ⟨hy, hfix⟩ := (n.coequalizer_pass_iff d y).mp hy
  have he := (Representative.toHom_eq_iff ((n.πRep d).comp k) ((n.πRep d).comp l)).mp h y hy
  change k.val.val (n.normalize.val.val y) = l.val.val (n.normalize.val.val y) at he
  simpa only [hfix] using he

end ClassNormalizer

end GebProto.EndomorphismCategory.DecisionProblem
