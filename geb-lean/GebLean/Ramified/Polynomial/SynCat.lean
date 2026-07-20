import GebLean.Ramified.Polynomial.Interp
import Mathlib.CategoryTheory.Category.Basic

/-!
# The primed syntactic category

A second realization of the generic syntactic category
(`GebLean/Ramified/SynCat.lean`) on the primed term layer `Tm'`
(`GebLean/Ramified/Polynomial/Term.lean`) and its evaluation `Tm'.eval`
(`GebLean/Ramified/Polynomial/Interp.lean`), quotiented by a `QuotRel'`. Its
objects are contexts; a morphism `Γ ⟶ Δ` is a codomain-indexed tuple of
domain terms, `∀ i, Tm' P.sig Γ (Δ.get i)`, modulo the pointwise closure of a
`QuotRel'`; identity is the variable tuple and composition is substitution.
The in-scope instantiation of the quotient relation is `interpQuotRel' P`.
This module mirrors the first half of the legacy `GebLean.Ramified.SynCat`
(through the `Category` instance and the `Hom.eval` layer); the finite-products
half is not reimplemented here.

## Main definitions

* `HomTuple'` — raw morphism data: a codomain-indexed tuple of domain terms.
* `homSetoid'` — the pointwise closure of a `QuotRel'` on morphism tuples.
* `Hom'` — morphisms of the primed syntactic category: morphism tuples modulo
  `homSetoid'`.
* `SynCat'` — the primed syntactic category's carrier (a type synonym for
  `Ctx`).
* `SynCat'.instCategory` — the `Category` instance: `Hom'` is the tuple
  quotient, identity the variable tuple, composition substitution.
* `HomTuple'.eval` — componentwise `Tm'.eval` of a morphism tuple at an
  environment.
* `Hom'.eval` — evaluation of a hom class at the standard model, the lift of
  `HomTuple'.eval` along `interpQuotRel'`.

## Main statements

* `Hom'.eval_mk` — evaluation of a class is componentwise evaluation of its
  representative.
* `Hom'.eval_comp` — evaluation respects composition (the semantic clone law
  `Tm'.eval_subst` componentwise).
* `Hom'.eval_id` — evaluation of the identity morphism is the environment.

## References

The free multi-sorted Lawvere theory / term-clone conventions realized here
follow D. Leivant, "Ramified recurrence and computational complexity III:
Higher type recurrence and elementary complexity", Annals of Pure and Applied
Logic 96 (1999) 209-229, DOI `10.1016/S0168-0072(98)00040-2`, section 2.1,
transcribed by the legacy `GebLean/Ramified/SynCat.lean`. The quotient-category
assembly follows the repository precedent `GebLean.LawvereERCat`
(`GebLean/LawvereERQuot.lean`).

## Tags

ramified recurrence, syntactic category, Lawvere theory, term clone, quotient
category, free monad, slice category
-/

namespace GebLean.Ramified.Polynomial

open CategoryTheory GebLean.Ramified

variable {S : Type}

/-- Reindexing at a propositionally equal codomain position. Mirrors the
legacy `Tm.reind_index`. -/
theorem Tm'.reind_index {sig : SortedSig S} {Γ Δ : Ctx S}
    (g : ∀ j : Fin Δ.length, Tm' sig Γ (Δ.get j)) {j j' : Fin Δ.length}
    (hj : j' = j) {b : S} (h : Δ.get j' = b) :
    Tm'.reind h (g j') = Tm'.reind (hj ▸ h) (g j) := by
  subst hj; rfl

/-- Raw morphism data of the primed syntactic category from `Γ` to `Δ`: a
tuple assigning to each position of the codomain context a primed term over
the domain context, of that position's sort. Mirrors the legacy `HomTuple`. -/
def HomTuple' (P : Presentation) (Γ Δ : Ctx P.S) : Type :=
  ∀ i : Fin Δ.length, Tm' P.sig Γ (Δ.get i)

/-- The identity tuple: the variable at each codomain position. Mirrors the
legacy `HomTuple.id`. -/
def HomTuple'.id (P : Presentation) (Γ : Ctx P.S) : HomTuple' P Γ Γ :=
  fun i => Tm'.var i

/-- The composite tuple: substitute the second tuple's terms by the first (the
slice free monad's bind). Mirrors the legacy `HomTuple.comp`. -/
def HomTuple'.comp {P : Presentation} {Γ Δ E : Ctx P.S}
    (f : HomTuple' P Γ Δ) (g : HomTuple' P Δ E) : HomTuple' P Γ E :=
  fun i => (g i).subst f

/-- The pointwise closure of a `QuotRel'` on morphism tuples: two tuples are
related when they are related position by position. The dependent-function
setoid `piSetoid` of the per-position setoids `r.rel Γ (Δ.get i)`. Mirrors
the legacy `homSetoid`. -/
def homSetoid' (P : Presentation) (r : QuotRel' P.sig) (Γ Δ : Ctx P.S) :
    Setoid (HomTuple' P Γ Δ) :=
  @piSetoid _ _ (fun i => r.rel Γ (Δ.get i))

/-- Morphisms of the primed syntactic category: morphism tuples modulo
`homSetoid'`. Mirrors the legacy `Hom`. -/
def Hom' (P : Presentation) (r : QuotRel' P.sig) (Γ Δ : Ctx P.S) : Type :=
  Quotient (homSetoid' P r Γ Δ)

/-- The identity morphism: the class of the variable tuple. Mirrors the
legacy `Hom.id`. -/
def Hom'.id (P : Presentation) (r : QuotRel' P.sig) (Γ : Ctx P.S) :
    Hom' P r Γ Γ :=
  Quotient.mk _ (HomTuple'.id P Γ)

/-- Composition of morphisms, lifted from `HomTuple'.comp`; well-defined by
the `QuotRel'`'s substitution congruence. Mirrors the legacy `Hom.comp`. -/
def Hom'.comp {P : Presentation} {r : QuotRel' P.sig} {Γ Δ E : Ctx P.S}
    (f : Hom' P r Γ Δ) (g : Hom' P r Δ E) : Hom' P r Γ E :=
  Quotient.liftOn₂ f g (fun f' g' => Quotient.mk _ (HomTuple'.comp f' g'))
    (fun f₁ g₁ f₂ g₂ hf hg => Quotient.sound
      (fun i => r.subst_congr (g₁ i) (g₂ i) f₁ f₂ (hg i) hf))

/-- Left identity law. -/
theorem Hom'.id_comp {P : Presentation} {r : QuotRel' P.sig} {Γ Δ : Ctx P.S}
    (f : Hom' P r Γ Δ) : (Hom'.id P r Γ).comp f = f := by
  induction f using Quotient.ind with
  | _ f' => exact congrArg (Quotient.mk _) (funext fun i => Tm'.subst_id (f' i))

/-- Right identity law. -/
theorem Hom'.comp_id {P : Presentation} {r : QuotRel' P.sig} {Γ Δ : Ctx P.S}
    (f : Hom' P r Γ Δ) : f.comp (Hom'.id P r Δ) = f := by
  induction f using Quotient.ind with
  | _ f' => exact congrArg (Quotient.mk _) (funext fun i => Tm'.var_subst i f')

/-- Associativity law. -/
theorem Hom'.assoc {P : Presentation} {r : QuotRel' P.sig} {Γ Δ E W : Ctx P.S}
    (f : Hom' P r Γ Δ) (g : Hom' P r Δ E) (h : Hom' P r E W) :
    (f.comp g).comp h = f.comp (g.comp h) := by
  induction f using Quotient.ind with
  | _ f' =>
  induction g using Quotient.ind with
  | _ g' =>
  induction h using Quotient.ind with
  | _ h' =>
    exact congrArg (Quotient.mk _)
      (funext fun i => (Tm'.subst_subst (h' i) g' f').symm)

/-- Evaluate a hom-tuple at an environment of the model `M`: componentwise
`Tm'.eval`, giving a value at each codomain position. Mirrors the legacy
`HomTuple.eval`. -/
def HomTuple'.eval {P : Presentation} {Γ Δ : Ctx P.S} (f : HomTuple' P Γ Δ)
    (M : SortedModel P.sig) (ρ : M.Env Γ) : M.Env Δ :=
  fun i => (f i).eval M ρ

/-- Evaluate a hom (a `homSetoid'`-class over `interpQuotRel' P`) at the
standard model over an environment: componentwise `Tm'.eval` of any
representative. The lift is well-defined because `interpQuotRel' P` relates
two tuples exactly when their `Tm'.eval` at the standard model agree on every
environment. Mirrors the legacy `Hom.eval`. -/
def Hom'.eval {P : Presentation} {Γ Δ : Ctx P.S}
    (f : Hom' P (interpQuotRel' P) Γ Δ) (ρ : (standardModel P).Env Γ) :
    (standardModel P).Env Δ :=
  Quotient.liftOn f (fun f' => HomTuple'.eval f' (standardModel P) ρ)
    (fun _ _ h => funext (fun i => h i ρ))

/-- Evaluation of a hom class is componentwise evaluation of its representative
tuple. -/
@[simp] theorem Hom'.eval_mk {P : Presentation} {Γ Δ : Ctx P.S}
    (f : HomTuple' P Γ Δ) (ρ : (standardModel P).Env Γ) :
    Hom'.eval (Quotient.mk _ f) ρ = HomTuple'.eval f (standardModel P) ρ :=
  rfl

/-- Evaluation respects composition (`≫`, i.e. `Hom'.comp`): evaluating a
composite at an environment evaluates the second hom at the value of the
first. The semantic clone law `Tm'.eval_subst` componentwise. -/
theorem Hom'.eval_comp {P : Presentation} {Γ Δ E : Ctx P.S}
    (f : Hom' P (interpQuotRel' P) Γ Δ) (g : Hom' P (interpQuotRel' P) Δ E)
    (ρ : (standardModel P).Env Γ) :
    (f.comp g).eval ρ = g.eval (f.eval ρ) := by
  induction f using Quotient.ind with
  | _ f' =>
  induction g using Quotient.ind with
  | _ g' => exact funext (fun i => Tm'.eval_subst (standardModel P) (g' i) f' ρ)

/-- Evaluation of the identity morphism is the environment (the fold's
left-unit computation rule componentwise). Mirrors the legacy `Hom.eval_id`
(`GebLean/Ramified/Soundness/Collapse.lean`). -/
theorem Hom'.eval_id {P : Presentation} {Γ : Ctx P.S}
    (ρ : (standardModel P).Env Γ) :
    (Hom'.id P (interpQuotRel' P) Γ).eval ρ = ρ := by
  funext i
  simp only [Hom'.id, Hom'.eval_mk, HomTuple'.eval, HomTuple'.id, Tm'.eval_var]

/-- The carrier of the primed syntactic category of a presentation `P` under a
quotient relation `r`: a type synonym for `Ctx P.S` carrying the category
instance. The relation `r` is a phantom parameter: it does not occur in the
carrier but distinguishes the instances, so that the `Category` structures
for different relations do not collide. Mirrors the legacy `SynCat`. -/
@[nolint unusedArguments]
def SynCat' (P : Presentation) (_r : QuotRel' P.sig) : Type := Ctx P.S

/-- The primed syntactic category: objects are contexts, a morphism `Γ ⟶ Δ`
is a tuple of primed terms modulo `r`, identity is the variable tuple, and
composition is substitution. Mirrors the legacy `SynCat.instCategory`. -/
instance SynCat'.instCategory (P : Presentation) (r : QuotRel' P.sig) :
    Category (SynCat' P r) where
  Hom Γ Δ := Hom' P r Γ Δ
  id Γ := Hom'.id P r Γ
  comp f g := Hom'.comp f g
  id_comp f := Hom'.id_comp f
  comp_id f := Hom'.comp_id f
  assoc f g h := Hom'.assoc f g h

end GebLean.Ramified.Polynomial
