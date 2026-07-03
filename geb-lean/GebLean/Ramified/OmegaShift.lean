import GebLean.Ramified.HigherOrder

/-!
# The sort-level Omega shift and the auxiliary coercion kappa-hat

The Omega shift on ramified types — the base substitution `τ[o := Ω o]` —
and the object-sort instances of the auxiliary coercion kappa-hat of
Leivant III section 2.4(1), `kappa-hat_τ : Ω τ → τ`. The paper defines
kappa-hat at every r-type `τ = σ-vec → θ`, by ramified recurrence whose
step functions are the pointwise constructor lifts `c_i^τ` (explicit
definitions); at an object sort the lift is the constructor operation
itself and the instance is extensionally the identity on the carrier.
This module constructs those object-sort instances. The shift is
sort-level only; neither an endofunctor of the syntactic category over
the shift nor the assembly of the kappa-hat components into its copoint
is claimed (spec open question 3).

## Main definitions

* `RType.omegaShift` — the Omega shift on sorts: the base substitution
  `τ[o := Ω o]`.
* `kappaHatStep` — the step function of kappa-hat's defining recurrence at
  one constructor label.
* `kappaHatIdent` — kappa-hat as a schema identifier: the ramified
  monotonic recurrence reconstructing its recurrence argument.
* `kappaHatTuple` — the morphism tuple applying `kappaHatIdent` to the
  sole variable of the context `[Ω τ]`.
* `kappaHat` — kappa-hat as a morphism `[Ω τ] ⟶ [τ]` of `RMRecCat`.

## Main statements

* `kappaHatIdent_interp` — the denotation of `kappaHatIdent` is the
  identity on the carrier copy.
* `kappaHat_interp` — the standard-model denotation of the underlying
  morphism tuple of `kappaHat` is the identity on the carrier copy.

## Implementation notes

The shift is a substitution at the base type, not postcomposition with
`Omega`: postcomposition fails to respect arrow sorts, whereas the base
substitution commutes with `arrow` and `omega`.

`kappaHat` carries an object-sort hypothesis `hτ : τ.IsObj`: the
constructions here are the object-sort instances of the paper's
kappa-hat, whose domain is all r-types. At an object sort `τ` the
pointwise constructor lift `c_i^τ` of section 2.4(1) is the constructor
operation itself (`constructorSig` at `RType.IsObj`), the recurrence
reconstructs its argument, and the instance is extensionally the
identity on the carrier — type-correct under the standard semantics
(Leivant III section 2.7): every object sort denotes a copy of the
algebra's carrier, so `Ω τ` and `τ` denote the same carrier. At an
arrow sort `σ → ρ`, the sort `Ω (σ → ρ)` denotes the carrier while
`σ → ρ` denotes a function space; the paper's kappa-hat there is not an
identity but the recurrence through the lifts `c_i^{σ → ρ}`, which are
explicit definitions over previously defined identifiers. The paper's
"extensionally the identity" characterization describes the coercions
`kappa_τ : Ω τ → θ` and `delta_θ : θ → o`, functions between object
types, not kappa-hat at arrow sorts. No identity-realizing raising
coercion exists in the system (constant maps of type `o → Ω o` exist;
an identity-realizing one does not).

`kappaHat`'s type is stated through the syntactic category's hom-type
`Hom (higherOrder A) (interpQuotRel (higherOrder A))`, definitionally the
type `([Ω τ] : RMRecCat A) ⟶ [τ]`; stating the arrow directly would
require named object ascriptions, since a bare context literal elaborates
at the underlying `Ctx` type, on which the `Category` instance is not
keyed.

## References

D. Leivant, "Ramified recurrence and computational complexity III:
Higher type recurrence and elementary complexity", Annals of Pure and
Applied Logic 96 (1999) 209-229, DOI `10.1016/S0168-0072(98)00040-2`.
The auxiliary coercion kappa-hat, defined at every r-type by ramified
recurrence through the pointwise constructor lifts `c_i^τ`, and the
coercions `kappa` and `delta` between object types, each extensionally
the identity, are section 2.4(1); every object sort denotes a copy of
the base carrier in section 2.7. The Omega shift as a base substitution
and the restriction to the object-sort instances of kappa-hat are novel
packaging on this development's realization (decision 8: `PolyFix.ind`
recursion in place of Lean-native inductives).

## Tags

ramified recurrence, omega shift, coercion, kappa-hat, object sort,
syntactic category
-/

namespace GebLean.Ramified

open CategoryTheory

/-- The Omega shift on sorts: the base substitution `τ[o := Ω o]`, sending
the base type `o` to `Ω o` and commuting with `arrow` and `omega`. A
substitution at the base type, not postcomposition with `Omega`, which
fails to respect arrow sorts. Sort-level only: no endofunctor of the
syntactic category is claimed (spec open question 3). Realized by the
dependent eliminator `PolyFix.ind` (decision 8), following
`RType.interp`'s pattern. Novel packaging. -/
def RType.omegaShift (t : RType) : RType :=
  PolyFix.ind (P := rTypeSig.polyEndo) (motive := fun {_} _ => RType)
    (fun i childx ih =>
      match i, childx, ih with
      | RTypeShape.o, _, _ => RType.omega RType.o
      | RTypeShape.arrow, _, ih =>
        RType.arrow (ih (⟨0, by decide⟩ : Fin (rTypeSig.ar RTypeShape.arrow)))
          (ih (⟨1, by decide⟩ : Fin (rTypeSig.ar RTypeShape.arrow)))
      | RTypeShape.omega, _, ih =>
        RType.omega (ih (⟨0, by decide⟩ : Fin (rTypeSig.ar RTypeShape.omega)))) t

/-- The step function of kappa-hat's defining recurrence at the
constructor label `i` (Leivant III section 2.4(1)): an explicit definition
applying the constructor at the object sort `τ` to the recursive results —
the pointwise constructor lift `c_i^τ` of section 2.4(1), which at an
object sort is the constructor operation itself. The kappa-hat recurrence
reconstructs its recurrence argument constructor by constructor; the
constructor operation at `τ` exists by the object-sort hypothesis `hτ`. -/
def kappaHatStep (A : AlgSig) (τ : RType) (hτ : τ.IsObj) (i : A.B) :
    RIdent A (List.replicate (A.ar i) τ) τ :=
  RIdent.defn ⟨0, finZeroElim,
    Tm.op (sig := defnSig A 0 finZeroElim) (Sum.inl (Sum.inl (Sum.inl (⟨τ, hτ⟩, i))))
      (fun k => Tm.var k)⟩ finZeroElim

/-- Leivant III section 2.4(1)'s auxiliary coercion kappa-hat,
`kappa-hat_τ : Ω τ → τ`, at an object sort `τ`, as a schema identifier:
the ramified monotonic recurrence whose recurrence argument sits at `Ω τ`
and whose step function at each constructor applies that constructor at
`τ` to the recursive results, reconstructing the argument; extensionally
the identity on the carrier (`kappaHatIdent_interp`). The paper defines
kappa-hat at every r-type through the pointwise constructor lifts
`c_i^τ`; the object-sort hypothesis `hτ` selects the instances at which
the lift is the constructor operation itself (every object sort denotes
a copy of the algebra's carrier — section 2.7 — so `Ω τ` and `τ` denote
the same carrier, and the constructor operations exist exactly at the
object sorts). At an arrow sort, `Ω (σ → ρ)` denotes the carrier while
`σ → ρ` denotes a function space, so kappa-hat there is not an identity
and no identity-realizing coercion exists. -/
def kappaHatIdent (A : AlgSig) (τ : RType) (hτ : τ.IsObj) :
    RIdent A [RType.omega τ] τ :=
  RIdent.mrec [] τ (fun i => kappaHatStep A τ hτ i)

/-- The morphism tuple underlying `kappaHat`: at the sole position of the
codomain context `[τ]`, the identifier operation `kappaHatIdent` applied
to the sole variable of the domain context `[Ω τ]`. Novel packaging. -/
def kappaHatTuple (A : AlgSig) (τ : RType) (hτ : τ.IsObj) :
    HomTuple (higherOrder A) [RType.omega τ] [τ] :=
  Fin.cons
    (Tm.op (sig := (higherOrder A).sig)
      (Sum.inl (Sum.inr ⟨[RType.omega τ], τ, kappaHatIdent A τ hτ⟩))
      (fun k => Tm.var k))
    finZeroElim

/-- Leivant III section 2.4(1)'s auxiliary coercion kappa-hat, at an
object sort `τ`, as a morphism `[Ω τ] ⟶ [τ]` of the syntactic category
`RMRecCat A` at the singleton contexts: the class of `kappaHatTuple`.
Defined by ramified recurrence (`kappaHatIdent`) and extensionally the
identity on the carrier (`kappaHat_interp`); see `kappaHatIdent` for the
relation of the object-sort instances to the paper's kappa-hat, defined
at every r-type. Whether the kappa-hat components assemble into a copoint
of a shift endofunctor is spec open question 3, deliberately not claimed
here. -/
def kappaHat (A : AlgSig) (τ : RType) (hτ : τ.IsObj) :
    Hom (higherOrder A) (interpQuotRel (higherOrder A)) [RType.omega τ] [τ] :=
  Quotient.mk _ (kappaHatTuple A τ hτ)

/-- The denotation of a kappa-hat step: the constructor applied to the
recursive results, each read on the carrier copy, transported along the
carrier-copy equality of the object sort. -/
theorem kappaHatStep_interp (A : AlgSig) (τ : RType) (hτ : τ.IsObj) (b : A.B)
    (xvec : ∀ i : Fin ([] : Ctx RType).length,
      RType.interp (FreeAlg A) (([] : Ctx RType).get i))
    (phi : Fin (A.ar b) → RType.interp (FreeAlg A) τ) :
    (kappaHatStep A τ hτ b).interp (childEnv [] τ (A.ar b) xvec phi)
      = cast (RType.interp_isObj (FreeAlg A) hτ).symm
          (FreeAlg.mk b fun j =>
            cast (RType.interp_isObj (FreeAlg A) hτ) (phi j)) := by
  refine congrArg (cast (RType.interp_isObj (FreeAlg A) hτ).symm) ?_
  refine congrArg (FreeAlg.mk b) (funext fun j => ?_)
  exact eq_of_heq
    (((cast_heq _ _).trans (cast_heq _ _)).trans (cast_heq _ _).symm)

/-- Kappa-hat's defining recurrence reconstructs its recurrence argument:
on every carrier element it is the identity, transported along the
carrier-copy equality of the object sort. Proved by structural induction
via `PolyFix.ind` (decision 8). -/
theorem kappaHat_recurse_id (A : AlgSig) (τ : RType) (hτ : τ.IsObj)
    (xvec : ∀ i : Fin ([] : Ctx RType).length,
      RType.interp (FreeAlg A) (([] : Ctx RType).get i))
    (t : FreeAlg A) :
    FreeAlg.recurse (A := A) (P := Unit)
      (fun i _ _sub phi =>
        (kappaHatStep A τ hτ i).interp (childEnv [] τ (A.ar i) xvec phi))
      () t
      = cast (RType.interp_isObj (FreeAlg A) hτ).symm t := by
  refine PolyFix.ind (P := A.polyEndo)
    (motive := fun {_} t =>
      FreeAlg.recurse (A := A) (P := Unit)
        (fun i _ _sub phi =>
          (kappaHatStep A τ hτ i).interp (childEnv [] τ (A.ar i) xvec phi))
        () t
        = cast (RType.interp_isObj (FreeAlg A) hτ).symm t)
    (fun b children ihc => ?_) t
  refine Eq.trans (kappaHatStep_interp A τ hτ b xvec
      (fun e => FreeAlg.recurse (A := A) (P := Unit)
        (fun i _ _sub phi =>
          (kappaHatStep A τ hτ i).interp (childEnv [] τ (A.ar i) xvec phi))
        () (children e))) ?_
  refine congrArg (cast (RType.interp_isObj (FreeAlg A) hτ).symm) ?_
  refine congrArg (FreeAlg.mk b) (funext fun j => ?_)
  rw [ihc j, cast_cast, cast_eq]

/-- The denotation of `kappaHatIdent` is the identity on the carrier copy
(Leivant III section 2.4(1): the coercions are extensionally the
identity): its value on an environment is the environment's sole entry —
the recurrence argument, a carrier element — transported along the
carrier-copy equality of the object sort. -/
theorem kappaHatIdent_interp (A : AlgSig) (τ : RType) (hτ : τ.IsObj)
    (ρ : ∀ i : Fin ([RType.omega τ] : Ctx RType).length,
      RType.interp (FreeAlg A) (([RType.omega τ] : Ctx RType).get i)) :
    (kappaHatIdent A τ hτ).interp ρ
      = cast (RType.interp_isObj (FreeAlg A) hτ).symm (ρ 0) :=
  kappaHat_recurse_id A τ hτ (envHead [] (RType.omega τ) ρ)
    (envLast [] (RType.omega τ) ρ)

/-- The standard-model denotation of the morphism tuple underlying
`kappaHat` is the identity on the carrier copy (Leivant III section
2.4(1)): the value of its sole term on an environment is the
environment's sole entry, transported along the carrier-copy equality of
the object sort. -/
theorem kappaHat_interp (A : AlgSig) (τ : RType) (hτ : τ.IsObj)
    (ρ : (standardModel (higherOrder A)).Env [RType.omega τ]) :
    (kappaHatTuple A τ hτ 0).eval (standardModel (higherOrder A)) ρ
      = cast (RType.interp_isObj (FreeAlg A) hτ).symm (ρ 0) :=
  kappaHatIdent_interp A τ hτ ρ

end GebLean.Ramified
