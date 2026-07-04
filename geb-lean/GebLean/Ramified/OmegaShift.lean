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
* `RType.objTarget`, `RType.domains` — the object target `θ` and domain
  list `σ-vec` of the decomposition `τ = σ-vec → θ`.
* `cLift`, `cLiftArrow`, `cLiftAux` — the pointwise constructor lift
  `c_i^τ` at every r-type, and its arrow-sort construction.
* `kappaHatFull` — kappa-hat at every r-type, the ramified monotonic
  recurrence with steps `cLift`.
* `canonIdent` — the canonical functional `C^τ = λ x-vec. α^θ`.
* `applyCanon`, `kappaIdent` — the coercion `κ_τ : Ω τ → θ`, kappa-hat
  fed the canonical functionals.
* `deltaAux`, `deltaIdent` — the downward coercion `δ_θ : θ → o`.
* `defnApp`, `appPrefixVars`, `appArgs` — term-level application helpers.

## Main statements

* `kappaHatIdent_interp` — the denotation of `kappaHatIdent` is the
  identity on the carrier copy.
* `kappaHat_interp` — the standard-model denotation of the underlying
  morphism tuple of `kappaHat` is the identity on the carrier copy.
* `RType.objTarget_isObj`, `RType.objTarget_of_isObj`,
  `RType.curried_domains` — the object target is an object sort, is the
  identity at object sorts, and witnesses the curried decomposition.
* `kappaHatFull_eq_kappaHatIdent` — the full kappa-hat agrees with the
  object-sort instance at object sorts.
* `kappaHatFull_interp` — the recurrence semantics of the full kappa-hat.
* `cLiftArrow_interp` — the denotation of the arrow-sort pointwise
  constructor lift.
* `kappaIdent_interp` — the coercion `κ_τ` denotes the identity on the
  carrier copy.
* `deltaAux_interp`, `deltaIdent_interp` — the downward coercion `δ_θ`
  denotes the identity on the carrier copy.

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

/-- The final object sort of an r-type (Leivant III section 2.4, p. 213: "every
r-type `τ` is of the form `σ-vec → θ`"): `o` and every `Omega τ` are their own
target, and an arrow's target is its codomain's. Realized by the dependent
eliminator `PolyFix.ind` (decision 8), mirroring `RType.omegaShift`. Novel
packaging. -/
def RType.objTarget (t : RType) : RType :=
  PolyFix.ind (P := rTypeSig.polyEndo) (motive := fun {_} _ => RType)
    (fun i childx ih =>
      match i, childx, ih with
      | RTypeShape.o, _, _ => RType.o
      | RTypeShape.arrow, _, ih =>
        ih (⟨1, by decide⟩ : Fin (rTypeSig.ar RTypeShape.arrow))
      | RTypeShape.omega, childx, _ =>
        RType.omega (childx (⟨0, by decide⟩ : Fin (rTypeSig.ar RTypeShape.omega)))) t

/-- The final object sort of an r-type is always an object sort (Leivant III
section 2.3: `o` and every `Omega τ`). Proved by structural induction via
`PolyFix.ind` (decision 8). -/
theorem RType.objTarget_isObj (τ : RType) : (RType.objTarget τ).IsObj :=
  PolyFix.ind (P := rTypeSig.polyEndo)
    (motive := fun {_} t => (RType.objTarget t).IsObj)
    (fun i childx ih =>
      match i, childx, ih with
      | RTypeShape.o, _, _ => Or.inl rfl
      | RTypeShape.arrow, _, ih => ih ⟨1, by decide⟩
      | RTypeShape.omega, _, _ => Or.inr rfl) τ

/-- The domain sorts of an r-type `τ = σ-vec → θ` (Leivant III section 2.4,
p. 213): the list `σ-vec`, empty at an object sort and `σ` prepended to the
codomain's domains at an arrow `σ → ρ`. Together with `RType.objTarget` it
witnesses `τ = RType.curried τ.domains τ.objTarget` (`RType.curried_domains`).
Realized by the dependent eliminator `PolyFix.ind` (decision 8). Novel
packaging. -/
def RType.domains (t : RType) : List RType :=
  PolyFix.ind (P := rTypeSig.polyEndo) (motive := fun {_} _ => List RType)
    (fun i childx ih =>
      match i, childx, ih with
      | RTypeShape.o, _, _ => []
      | RTypeShape.arrow, childx, ih =>
        childx (⟨0, by decide⟩ : Fin (rTypeSig.ar RTypeShape.arrow))
          :: ih (⟨1, by decide⟩ : Fin (rTypeSig.ar RTypeShape.arrow))
      | RTypeShape.omega, _, _ => []) t

/-- Reconstruction of an `arrow`-shaped free-algebra node as the derived
constructor `RType.arrow` on its two children. A fact local to the recursions on
r-type structure. -/
theorem RType.mk_arrow_eq (childx : Fin (rTypeSig.ar RTypeShape.arrow) → RType) :
    (FreeAlg.mk (A := rTypeSig) RTypeShape.arrow childx)
      = RType.arrow (childx ⟨0, by decide⟩) (childx ⟨1, by decide⟩) := by
  refine congrArg (FreeAlg.mk (A := rTypeSig) RTypeShape.arrow) (funext fun k => ?_)
  refine Fin.cases ?_ (fun j => ?_) k
  · rfl
  · exact Fin.cases rfl (fun j' => j'.elim0) j

/-- Reconstruction of an `omega`-shaped free-algebra node as the derived
constructor `RType.omega` on its child. A fact local to the recursions on r-type
structure. -/
theorem RType.mk_omega_eq (childx : Fin (rTypeSig.ar RTypeShape.omega) → RType) :
    (FreeAlg.mk (A := rTypeSig) RTypeShape.omega childx)
      = RType.omega (childx ⟨0, by decide⟩) := by
  refine congrArg (FreeAlg.mk (A := rTypeSig) RTypeShape.omega) (funext fun k => ?_)
  exact Fin.cases rfl (fun j => j.elim0) k

/-- Reconstruction of an `o`-shaped free-algebra node as the base type `o`. A
fact local to the recursions on r-type structure. -/
theorem RType.mk_o_eq (childx : Fin (rTypeSig.ar RTypeShape.o) → RType) :
    (FreeAlg.mk (A := rTypeSig) RTypeShape.o childx) = RType.o :=
  congrArg (FreeAlg.mk (A := rTypeSig) RTypeShape.o) (funext fun k => k.elim0)

/-- Every r-type factors as its domains curried over its object target
(Leivant III section 2.4, p. 213): `τ = σ-vec → θ` with `σ-vec = τ.domains` and
`θ = τ.objTarget`. Proved by structural induction via `PolyFix.ind`
(decision 8). -/
theorem RType.curried_domains (t : RType) :
    t = RType.curried (RType.domains t) (RType.objTarget t) :=
  PolyFix.ind (P := rTypeSig.polyEndo)
    (motive := fun {_} t => t = RType.curried (RType.domains t) (RType.objTarget t))
    (fun i childx ih =>
      match i, childx, ih with
      | RTypeShape.o, childx, _ => RType.mk_o_eq childx
      | RTypeShape.arrow, childx, ih =>
        (RType.mk_arrow_eq childx).trans (by rw [ih ⟨1, by decide⟩]; rfl)
      | RTypeShape.omega, childx, _ => RType.mk_omega_eq childx) t

/-- The sort at any position of a replicated context is the replicated sort. A
fact local to the pointwise constructor lift `cLift`. -/
theorem get_replicate {α : Type} (n : Nat) (a : α)
    (j : Fin (List.replicate n a).length) : (List.replicate n a).get j = a := by
  simp [List.get_eq_getElem, List.getElem_replicate]

/-- Application of a function term to an argument term over an explicit
definition's base signature: the application former of `appSig` at `(a, b)`
applied to `c : a → b` and `x : a`, yielding a value at `b`. The term-level
counterpart of `stdAppInterp`, used to build the pointwise constructor lift at
arrow sorts. Novel packaging. -/
def defnApp {A : AlgSig} {n : Nat} {holeIdx : Fin n → List RType × RType}
    {Γ : Ctx RType} (a b : RType)
    (c : Tm (defnSig A n holeIdx) Γ (RType.arrow a b))
    (x : Tm (defnSig A n holeIdx) Γ a) :
    Tm (defnSig A n holeIdx) Γ b :=
  Tm.op (sig := defnSig A n holeIdx) (Sum.inl (Sum.inl (Sum.inr (a, b))))
    (Fin.cons c (Fin.cons x finZeroElim))

/-- The application chain applying a combinator term at the curried sort
`RType.curried (pre ++ post) ρ_` to the variables of `pre` in turn, leaving a
value at `RType.curried post ρ_`. Realized by structural recursion on `pre`
through the application former `defnApp`. Novel packaging: the term-level
partial-application idiom of the pointwise constructor lift. -/
def appPrefixVars {A : AlgSig} {n : Nat} {holeIdx : Fin n → List RType × RType}
    {Γ : Ctx RType} (ρ_ : RType) :
    (pre : List RType) → (post : List RType) →
    Tm (defnSig A n holeIdx) Γ (RType.curried (pre ++ post) ρ_) →
    ((k : Fin pre.length) → Tm (defnSig A n holeIdx) Γ (pre.get k)) →
    Tm (defnSig A n holeIdx) Γ (RType.curried post ρ_)
  | [], _post, c, _vars => c
  | a :: pre', post, c, vars =>
      appPrefixVars ρ_ pre' post
        (defnApp a (RType.curried (pre' ++ post) ρ_) c (vars ⟨0, Nat.succ_pos _⟩))
        (fun k => vars k.succ)

/-- The pointwise constructor lift at an arrow sort (Leivant III section 2.4(1),
p. 216): `c_i^{σ → ρ}(u-vec)(x) = c_i^ρ(u₁ x … u_r x)`, given the lift `c_i^ρ`
at the codomain (`ihρ`). Built as two nested explicit definitions: an inner
identifier `gArrow` over the context `replicate r (σ → ρ) ++ [σ]` whose body
applies `c_i^ρ` to the pointwise applications `u_j x`, and an outer definition
whose body is the curried combinator of `gArrow` partially applied to the `r`
recurrence-result variables (`appPrefixVars`), leaving a value at `σ → ρ`. Novel
packaging: the `ramExpStep` curried-hole idiom generalized to arbitrary arity
and codomain. -/
def cLiftArrow (A : AlgSig) (σ ρ : RType) (i : A.B)
    (ihρ : RIdent A (List.replicate (A.ar i) ρ) ρ) :
    RIdent A (List.replicate (A.ar i) (RType.arrow σ ρ)) (RType.arrow σ ρ) :=
  let holeIdxG : Fin 1 → List RType × RType := fun _ => (List.replicate (A.ar i) ρ, ρ)
  let bodyG : Tm (defnSig A 1 holeIdxG)
      (List.replicate (A.ar i) (RType.arrow σ ρ) ++ [σ]) ρ :=
    Tm.op (sig := defnSig A 1 holeIdxG) (Sum.inl (Sum.inr ⟨0, by decide⟩))
      (fun j =>
        let jr : Fin (List.replicate (A.ar i) (RType.arrow σ ρ)).length :=
          ⟨j.val, by
            have h : j.val < (List.replicate (A.ar i) ρ).length := j.isLt
            rw [List.length_replicate] at h
            rw [List.length_replicate]
            exact h⟩
        Tm.reind (get_replicate (A.ar i) ρ j).symm
          (defnApp σ ρ
            (Tm.reind
              ((get_finAppL _ [σ] jr).trans (get_replicate (A.ar i) (RType.arrow σ ρ) jr))
              (Tm.var (finAppL _ [σ] jr)))
            (Tm.reind
              (get_finAppR (List.replicate (A.ar i) (RType.arrow σ ρ)) [σ]
                ⟨0, Nat.zero_lt_one⟩)
              (Tm.var (finAppR _ [σ] ⟨0, Nat.zero_lt_one⟩)))))
  let gArrow : RIdent A (List.replicate (A.ar i) (RType.arrow σ ρ) ++ [σ]) ρ :=
    RIdent.defn ⟨1, holeIdxG, bodyG⟩ (fun _ => ihρ)
  let holeIdxO : Fin 1 → List RType × RType :=
    fun _ => (List.replicate (A.ar i) (RType.arrow σ ρ) ++ [σ], ρ)
  let combinator : Tm (defnSig A 1 holeIdxO)
      (List.replicate (A.ar i) (RType.arrow σ ρ))
      (RType.curried (List.replicate (A.ar i) (RType.arrow σ ρ) ++ [σ]) ρ) :=
    Tm.op (sig := defnSig A 1 holeIdxO) (Sum.inr ⟨0, by decide⟩) finZeroElim
  let outerBody : Tm (defnSig A 1 holeIdxO)
      (List.replicate (A.ar i) (RType.arrow σ ρ)) (RType.arrow σ ρ) :=
    appPrefixVars ρ (List.replicate (A.ar i) (RType.arrow σ ρ)) [σ] combinator
      (fun k => Tm.var k)
  RIdent.defn ⟨1, holeIdxO, outerBody⟩ (fun _ => gArrow)

/-- The pointwise constructor lift over the curried decomposition `σ-vec → θ` of
an r-type (Leivant III section 2.4(1)): `kappaHatStep` at the object target `θ`
when `σ-vec` is empty, and `cLiftArrow` peeling one domain otherwise. Realized by
structural recursion on the domain list. Novel packaging. -/
def cLiftAux (A : AlgSig) :
    (D : List RType) → (θ : RType) → θ.IsObj → (i : A.B) →
    RIdent A (List.replicate (A.ar i) (RType.curried D θ)) (RType.curried D θ)
  | [], θ, hθ, i => kappaHatStep A θ hθ i
  | σ :: D', θ, hθ, i => cLiftArrow A σ (RType.curried D' θ) i (cLiftAux A D' θ hθ i)

/-- The pointwise constructor lift `c_i^τ` at an arbitrary r-type (Leivant III
section 2.4(1), p. 216): at an object sort it is the constructor operation
itself (the committed `kappaHatStep`), and at an arrow `σ-vec → θ` it is the
pointwise lift `c_i^τ(u-vec)(x-vec) = c_i^θ(u₁(x-vec) … u_r(x-vec))`, built by
`cLiftArrow` over the curried decomposition `τ = RType.curried τ.domains
τ.objTarget`. The step function of the full kappa-hat recurrence `kappaHatFull`.
Novel packaging. -/
def cLift (A : AlgSig) (τ : RType) (i : A.B) :
    RIdent A (List.replicate (A.ar i) τ) τ :=
  if h : τ.IsObj then kappaHatStep A τ h i
  else
    cast (congrArg (fun s => RIdent A (List.replicate (A.ar i) s) s)
        (RType.curried_domains τ).symm)
      (cLiftAux A (RType.domains τ) (RType.objTarget τ) (RType.objTarget_isObj τ) i)

/-- Leivant III section 2.4(1)'s auxiliary coercion kappa-hat at every r-type
`τ`, `kappa-hat_τ : Ω τ → τ`, as a schema identifier: the ramified monotonic
recurrence whose step functions are the pointwise constructor lifts `cLift`.
Agrees with the object-sort instance `kappaHatIdent` at object sorts
(`kappaHatFull_eq_kappaHatIdent`); its recurrence semantics is
`kappaHatFull_interp`. Novel packaging. -/
def kappaHatFull (A : AlgSig) (τ : RType) : RIdent A [RType.omega τ] τ :=
  RIdent.mrec [] τ (fun i => cLift A τ i)

/-- At an object sort, the full kappa-hat coincides with the committed
object-sort instance `kappaHatIdent` (Leivant III section 2.4(1)): the pointwise
constructor lift is the constructor operation itself there. Proved from
`cLift`'s object-sort branch by proof irrelevance on the object-sort
hypothesis. -/
theorem kappaHatFull_eq_kappaHatIdent (A : AlgSig) (τ : RType) (hτ : τ.IsObj) :
    kappaHatFull A τ = kappaHatIdent A τ hτ :=
  congrArg (RIdent.mrec [] τ) (funext fun i => by
    show cLift A τ i = kappaHatStep A τ hτ i
    rw [cLift, dif_pos hτ])

/-- The recurrence semantics of the full kappa-hat (Leivant III section 2.4(1)):
its denotation on an environment is the free-algebra recurrence over the
pointwise constructor lifts `cLift`, run on the recurrence argument. Holds by
definitional unfolding of the ramified monotonic recurrence. -/
theorem kappaHatFull_interp (A : AlgSig) (τ : RType)
    (ρ : ∀ i : Fin ([RType.omega τ] : Ctx RType).length,
      RType.interp (FreeAlg A) (([RType.omega τ] : Ctx RType).get i)) :
    (kappaHatFull A τ).interp ρ
      = FreeAlg.recurse (A := A) (P := Unit)
          (fun i _ _sub phi => (cLift A τ i).interp
            (childEnv [] τ (A.ar i) (envHead [] (RType.omega τ) ρ) phi))
          () (envLast [] (RType.omega τ) ρ) :=
  rfl

/-- The canonical functional `C^τ = λ x-vec. α^θ` (Leivant III section 2.4, p.
215): the constant functional at an r-type `τ = σ-vec → θ` returning the 0-ary
constructor `α^θ = c_{b₀}^θ` of the algebra at the object target `θ`. The 0-ary
constructor is carried as the label `b₀` with its nullary-arity witness `h₀ :
A.ar b₀ = 0` (the paper's standing convention on algebras). Built as an explicit
definition: the curried combinator of an inner identifier over the domain
context `τ.domains` whose body is `α^θ`. Novel packaging. -/
def canonIdent (A : AlgSig) (b₀ : A.B) (h₀ : A.ar b₀ = 0) (τ : RType) :
    RIdent A [] τ :=
  let holeIdxC : Fin 1 → List RType × RType :=
    fun _ => (RType.domains τ, RType.objTarget τ)
  let gBody : Tm (defnSig A 0 finZeroElim) (RType.domains τ) (RType.objTarget τ) :=
    Tm.op (sig := defnSig A 0 finZeroElim)
      (Sum.inl (Sum.inl (Sum.inl (⟨RType.objTarget τ, RType.objTarget_isObj τ⟩, b₀))))
      (fun k => Fin.elim0 (Fin.cast
        (by change (List.replicate (A.ar b₀) (RType.objTarget τ)).length = 0
            rw [List.length_replicate]; exact h₀) k))
  let g : RIdent A (RType.domains τ) (RType.objTarget τ) :=
    RIdent.defn ⟨0, finZeroElim, gBody⟩ finZeroElim
  let cBody : Tm (defnSig A 1 holeIdxC) []
      (RType.curried (RType.domains τ) (RType.objTarget τ)) :=
    Tm.op (sig := defnSig A 1 holeIdxC) (Sum.inr ⟨0, by decide⟩) finZeroElim
  cast (congrArg (RIdent A []) (RType.curried_domains τ).symm)
    (RIdent.defn (Γ := []) ⟨1, holeIdxC, cBody⟩ (fun _ => g))

/-- The application chain applying a combinator term at the curried sort
`RType.curried D θ` to a full argument tuple, yielding a value at the object
target `θ`. Realized by structural recursion on `D` through the application
former `defnApp`. Novel packaging: the term-level saturation idiom for the
coercion `kappaIdent`. -/
def appArgs {A : AlgSig} {n : Nat} {holeIdx : Fin n → List RType × RType}
    {Γ : Ctx RType} (θ : RType) :
    (D : List RType) →
    Tm (defnSig A n holeIdx) Γ (RType.curried D θ) →
    ((k : Fin D.length) → Tm (defnSig A n holeIdx) Γ (D.get k)) →
    Tm (defnSig A n holeIdx) Γ θ
  | [], c, _args => c
  | a :: D', c, args =>
      appArgs θ D'
        (defnApp a (RType.curried D' θ) c (args ⟨0, Nat.succ_pos _⟩))
        (fun k => args k.succ)

/-- Application of a `τ`-valued function to the canonical functionals of `τ`'s
domains (Leivant III section 2.4(1)): `λ f. f(C^{σ₁} … C^{σ_k})`, at context
`[τ]` and result the object target `θ`. The saturating half of the coercion
`kappaIdent`: an explicit definition whose holes are the canonical functionals
`canonIdent` at each domain sort, its body applying the input variable (read at
the curried decomposition of `τ`) to their combinator forms via `appArgs`. Novel
packaging. -/
def applyCanon (A : AlgSig) (b₀ : A.B) (h₀ : A.ar b₀ = 0) (τ : RType) :
    RIdent A [τ] (RType.objTarget τ) :=
  let holeIdx : Fin (RType.domains τ).length → List RType × RType :=
    fun j => ([], (RType.domains τ).get j)
  let body : Tm (defnSig A (RType.domains τ).length holeIdx) [τ] (RType.objTarget τ) :=
    appArgs (RType.objTarget τ) (RType.domains τ)
      (Tm.reind (RType.curried_domains τ) (Tm.var 0))
      (fun j => Tm.op (sig := defnSig A (RType.domains τ).length holeIdx)
        (Sum.inr j) finZeroElim)
  RIdent.defn ⟨(RType.domains τ).length, holeIdx, body⟩
    (fun j => canonIdent A b₀ h₀ ((RType.domains τ).get j))

/-- Leivant III section 2.4(1)'s coercion `κ_τ : Ω τ → θ` (with `θ = τ.objTarget`):
the full kappa-hat `kappaHatFull` postcomposed with `applyCanon`, i.e.
`κ_τ(u) = (kappa-hat_τ u)(C^{σ₁} … C^{σ_k})`, lowering the arrow structure of `τ`
by feeding the canonical functionals. Extensionally the identity on the carrier.
Novel packaging. -/
def kappaIdent (A : AlgSig) (b₀ : A.B) (h₀ : A.ar b₀ = 0) (τ : RType) :
    RIdent A [RType.omega τ] (RType.objTarget τ) :=
  let holeIdx : Fin 2 → List RType × RType :=
    fun j => match j with
      | ⟨0, _⟩ => ([RType.omega τ], τ)
      | ⟨1, _⟩ => ([τ], RType.objTarget τ)
  let body : Tm (defnSig A 2 holeIdx) [RType.omega τ] (RType.objTarget τ) :=
    Tm.op (sig := defnSig A 2 holeIdx) (Sum.inl (Sum.inr ⟨1, by decide⟩))
      (Fin.cons
        (Tm.op (sig := defnSig A 2 holeIdx) (Sum.inl (Sum.inr ⟨0, by decide⟩))
          (Fin.cons (Tm.var 0) finZeroElim))
        finZeroElim)
  RIdent.defn ⟨2, holeIdx, body⟩
    (fun j => match j with
      | ⟨0, _⟩ => kappaHatFull A τ
      | ⟨1, _⟩ => applyCanon A b₀ h₀ τ)

/-- An object sort is its own object target (Leivant III section 2.3): for
`θ.IsObj`, `RType.objTarget θ = θ`. -/
theorem RType.objTarget_of_isObj {θ : RType} (hθ : θ.IsObj) :
    RType.objTarget θ = θ := by
  rcases θ with ⟨_, i, childx⟩
  rcases hθ with h | h <;>
    (simp only [RType.shape, PolyFix.index] at h; subst h)
  · exact (RType.mk_o_eq childx).symm
  · exact (RType.mk_omega_eq childx).symm

/-- The downward coercion at every r-type, targeting the base sort: `RIdent A
[θ.objTarget] o`, composing the coercion `kappaIdent` downward through the
structure of `θ` (Leivant III section 2.4(1)). At `o` it is the identity, at an
arrow it is the coercion of the codomain, and at `Ω σ` it composes the coercion
at `σ.objTarget` after `kappaIdent` at `σ`. Realized by structural recursion via
`PolyFix.ind` (decision 8). Novel packaging. -/
def deltaAux (A : AlgSig) (b₀ : A.B) (h₀ : A.ar b₀ = 0) (τ : RType) :
    RIdent A [RType.objTarget τ] RType.o :=
  PolyFix.ind (P := rTypeSig.polyEndo)
    (motive := fun {_} t => RIdent A [RType.objTarget t] RType.o)
    (fun i childx ih =>
      match i, childx, ih with
      | RTypeShape.o, _, _ => RIdent.defn ⟨0, finZeroElim, Tm.var 0⟩ finZeroElim
      | RTypeShape.arrow, _, ih => ih ⟨1, by decide⟩
      | RTypeShape.omega, childx, ih =>
        let σ := childx (⟨0, by decide⟩ : Fin (rTypeSig.ar RTypeShape.omega))
        let holeIdxD : Fin 2 → List RType × RType :=
          fun j => match j with
            | ⟨0, _⟩ => ([RType.objTarget σ], RType.o)
            | ⟨1, _⟩ => ([RType.omega σ], RType.objTarget σ)
        let bodyD : Tm (defnSig A 2 holeIdxD) [RType.omega σ] RType.o :=
          Tm.op (sig := defnSig A 2 holeIdxD) (Sum.inl (Sum.inr ⟨0, by decide⟩))
            (Fin.cons
              (Tm.op (sig := defnSig A 2 holeIdxD) (Sum.inl (Sum.inr ⟨1, by decide⟩))
                (Fin.cons (Tm.var 0) finZeroElim))
              finZeroElim)
        RIdent.defn ⟨2, holeIdxD, bodyD⟩
          (fun j => match j with
            | ⟨0, _⟩ => ih ⟨0, by decide⟩
            | ⟨1, _⟩ => kappaIdent A b₀ h₀ σ)) τ

/-- Leivant III section 2.4(1)'s coercion `δ_θ : θ → o` at an object sort `θ`:
the composite of the coercions `kappaIdent` down to the base sort, extensionally
the identity on the carrier. Generalizes the tower-sort `ramDeltaIdent`. Realized
as `deltaAux` transported along `θ.objTarget = θ`. Novel packaging. -/
def deltaIdent (A : AlgSig) (b₀ : A.B) (h₀ : A.ar b₀ = 0) (θ : RType)
    (hθ : θ.IsObj) : RIdent A [θ] RType.o :=
  cast (congrArg (fun s => RIdent A [s] RType.o) (RType.objTarget_of_isObj hθ))
    (deltaAux A b₀ h₀ θ)

/-- The denotation of an explicit definition unfolds to the evaluation of its
body against the model whose holes are read by the denotations of the referenced
identifiers. A definitional reduction of `RIdent.interp` at a `defn` node. -/
theorem RIdent.interp_defn {A : AlgSig} {Γ : List RType} {τ : RType}
    (d : DefnShape A Γ τ)
    (children : (j : Fin d.numHoles) → RIdent A (d.holeIdx j).1 (d.holeIdx j).2)
    (ρ : ∀ i : Fin Γ.length, RType.interp (FreeAlg A) (Γ.get i)) :
    (RIdent.defn d children).interp ρ
      = d.body.eval (defnModel A d.numHoles d.holeIdx (fun j => (children j).interp)) ρ :=
  rfl

/-- Evaluation of an operation term applies the model's interpretation of the
operation to the recursively evaluated arguments. A definitional reduction of
`Tm.eval` at an operation node. -/
theorem Tm.eval_op {S : Type} {sig : SortedSig S} {Γ : Ctx S} (M : SortedModel sig)
    (ρ : M.Env Γ) (o : sig.Op)
    (args : ∀ i : Fin (sig.arity o).length, Tm sig Γ ((sig.arity o).get i)) :
    (Tm.op o args).eval M ρ = M.interpOp o (fun i => (args i).eval M ρ) :=
  rfl

/-- Evaluation of a variable term reads the environment at its position. A
definitional reduction of `Tm.eval` at a variable node. -/
theorem Tm.eval_var {S : Type} {sig : SortedSig S} {Γ : Ctx S} (M : SortedModel sig)
    (ρ : M.Env Γ) (i : Fin Γ.length) : (Tm.var i).eval M ρ = ρ i :=
  rfl

/-- The curried arrow sort of a concatenated context splits as the currying of
the prefix over the currying of the suffix: `curried (pre ++ post) ρ =
curried pre (curried post ρ)`. The `List.foldr_append` law transported to
`RType.curried`. -/
theorem RType.curried_append (pre post : List RType) (ρ_ : RType) :
    RType.curried (pre ++ post) ρ_ = RType.curried pre (RType.curried post ρ_) := by
  simp only [RType.curried, List.foldr_append]

/-- Casting a function value along a codomain-sort equality of an arrow sort and
applying it equals applying it and casting the result. A cast-commutation fact
local to the pointwise constructor lift. -/
theorem cast_arrow_apply {A : AlgSig} {a b b' : RType} (h : b = b')
    (f : RType.interp (FreeAlg A) (RType.arrow a b))
    (x : RType.interp (FreeAlg A) a) :
    (cast (congrArg (RType.interp (FreeAlg A)) (congrArg (RType.arrow a) h)) f) x
      = cast (congrArg (RType.interp (FreeAlg A)) h) (f x) := by
  subst h; rfl

/-- Evaluation of an application term against a definition model reads the
function-position value as a function and applies it to the argument-position
value. A definitional reduction local to the pointwise constructor lift. -/
theorem defnApp_eval {A : AlgSig} {n : Nat} {holeIdx : Fin n → List RType × RType}
    {Γ : Ctx RType}
    (ih : ∀ j : Fin n, (∀ i : Fin (holeIdx j).1.length,
        RType.interp (FreeAlg A) ((holeIdx j).1.get i)) →
        RType.interp (FreeAlg A) (holeIdx j).2)
    (a b : RType) (c : Tm (defnSig A n holeIdx) Γ (RType.arrow a b))
    (x : Tm (defnSig A n holeIdx) Γ a)
    (ρ : (defnModel A n holeIdx ih).Env Γ) :
    (defnApp a b c x).eval (defnModel A n holeIdx ih) ρ
      = (c.eval (defnModel A n holeIdx ih) ρ) (x.eval (defnModel A n holeIdx ih) ρ) :=
  rfl

/-- Evaluation of the prefix-application chain: applying a combinator at the
curried sort `curried (pre ++ post) ρ` to the prefix variables denotes the
partial application chain `appChain` of the combinator's value over the prefix,
transported along `RType.curried_append`. Proved by structural recursion on
`pre` through `defnApp_eval` and the cast-commutation `cast_arrow_apply`. -/
theorem appPrefixVars_eval {A : AlgSig} {n : Nat} {holeIdx : Fin n → List RType × RType}
    {Γ : Ctx RType}
    (ih : ∀ j : Fin n, (∀ i : Fin (holeIdx j).1.length,
        RType.interp (FreeAlg A) ((holeIdx j).1.get i)) →
        RType.interp (FreeAlg A) (holeIdx j).2)
    (ρ_ : RType) (ρ : (defnModel A n holeIdx ih).Env Γ) :
    (pre post : List RType) →
    (c : Tm (defnSig A n holeIdx) Γ (RType.curried (pre ++ post) ρ_)) →
    (vars : (k : Fin pre.length) → Tm (defnSig A n holeIdx) Γ (pre.get k)) →
    (appPrefixVars ρ_ pre post c vars).eval (defnModel A n holeIdx ih) ρ
      = appChain A pre (RType.curried post ρ_)
          (cast (congrArg (RType.interp (FreeAlg A)) (RType.curried_append pre post ρ_))
            (c.eval (defnModel A n holeIdx ih) ρ))
          (fun k => (vars k).eval (defnModel A n holeIdx ih) ρ)
  | [], _post, c, _vars => (eq_of_heq (cast_heq _ _)).symm
  | a :: pre', post, c, vars => by
    have hIH := appPrefixVars_eval ih ρ_ ρ pre' post
      (defnApp a (RType.curried (pre' ++ post) ρ_) c (vars ⟨0, Nat.succ_pos _⟩))
      (fun k => vars k.succ)
    refine hIH.trans ?_
    refine congrArg (fun X => appChain A pre' (RType.curried post ρ_) X
      (fun k => (vars k.succ).eval (defnModel A n holeIdx ih) ρ)) ?_
    rw [defnApp_eval]
    exact (cast_arrow_apply (RType.curried_append pre' post ρ_)
      (c.eval (defnModel A n holeIdx ih) ρ)
      ((vars ⟨0, Nat.succ_pos _⟩).eval (defnModel A n holeIdx ih) ρ)).symm

/-- The recurrence-context environment reads its parameter values at the
left-injected positions. A fact local to the pointwise constructor lift. -/
theorem childEnv_finAppL {C : RType → Type} {params : List RType} {σ : RType}
    {n : Nat} (xvec : ∀ i : Fin params.length, C (params.get i))
    (rest : Fin n → C σ) (i : Fin params.length) :
    childEnv params σ n xvec rest (finAppL params (List.replicate n σ) i)
      = cast (congrArg C (get_finAppL params (List.replicate n σ) i).symm) (xvec i) := by
  unfold childEnv
  have h : (finAppL params (List.replicate n σ) i).val < params.length := i.isLt
  rw [dif_pos h]
  exact eq_of_heq ((cast_heq _ _).trans (cast_heq _ _).symm)

/-- The recurrence-context environment reads its recursive-result values at the
right-injected positions. A fact local to the pointwise constructor lift. -/
theorem childEnv_finAppR {C : RType → Type} {params : List RType} {σ : RType}
    {n : Nat} (xvec : ∀ i : Fin params.length, C (params.get i))
    (rest : Fin n → C σ) (j : Fin (List.replicate n σ).length) (hj : j.val < n) :
    childEnv params σ n xvec rest (finAppR params (List.replicate n σ) j)
      = cast (congrArg C (get_finAppR params (List.replicate n σ) j).symm)
          (cast (congrArg C (get_replicate n σ j).symm) (rest ⟨j.val, hj⟩)) := by
  unfold childEnv
  have h : ¬ (finAppR params (List.replicate n σ) j).val < params.length := by
    simp only [finAppR]; omega
  rw [dif_neg h]
  refine eq_of_heq (HEq.trans (cast_heq _ _) ?_)
  refine HEq.trans ?_ (HEq.symm (HEq.trans (cast_heq _ _) (cast_heq _ _)))
  exact heq_of_eq (congrArg rest (Fin.ext (by simp only [finAppR]; omega)))

/-- A full application chain over `Γ ++ [σ]` splits as the prefix chain over `Γ`
applied to the final argument, with the combinator transported along
`RType.curried_append`. Proved by structural recursion on `Γ` through the
cast-commutation `cast_arrow_apply`. -/
theorem appChain_snoc (A : AlgSig) (σ ρ : RType) :
    (Γ : List RType) →
    (c : RType.interp (FreeAlg A) (RType.curried (Γ ++ [σ]) ρ)) →
    (E : ∀ k : Fin (Γ ++ [σ]).length, RType.interp (FreeAlg A) ((Γ ++ [σ]).get k)) →
    appChain A (Γ ++ [σ]) ρ c E
      = (appChain A Γ (RType.arrow σ ρ)
          (cast (congrArg (RType.interp (FreeAlg A)) (RType.curried_append Γ [σ] ρ)) c)
          (fun i => cast (congrArg (RType.interp (FreeAlg A)) (get_finAppL Γ [σ] i))
            (E (finAppL Γ [σ] i))))
        (cast (congrArg (RType.interp (FreeAlg A)) (get_finAppR Γ [σ] ⟨0, Nat.zero_lt_one⟩))
          (E (finAppR Γ [σ] ⟨0, Nat.zero_lt_one⟩)))
  | [], c, E => by
    change c (E ⟨0, Nat.zero_lt_one⟩) = _
    refine congr ?_ ?_
    · exact (eq_of_heq (cast_heq _ _)).symm
    · exact (eq_of_heq (cast_heq _ _)).symm
  | b :: Γ', c, E => by
    change appChain A (Γ' ++ [σ]) ρ (c (E ⟨0, Nat.succ_pos _⟩)) (fun i => E i.succ) = _
    rw [appChain_snoc A σ ρ Γ' (c (E ⟨0, Nat.succ_pos _⟩)) (fun i => E i.succ)]
    refine congr (congr (congrArg _ ?_) ?_) ?_
    · refine (cast_arrow_apply (RType.curried_append Γ' [σ] ρ) c
        (E ⟨0, Nat.succ_pos _⟩)).symm.trans ?_
      refine congrArg (cast _ c) ?_
      exact (eq_of_heq (cast_heq _ _)).symm
    · funext i
      exact eq_of_heq ((cast_heq _ _).trans (cast_heq _ _).symm)
    · exact eq_of_heq ((cast_heq _ _).trans (cast_heq _ _).symm)

/-- The environment over `Γ ++ [σ]` extending an environment over `Γ` by one
value at the end. Defined by recursion on `Γ` (through `Fin.cons`) so that the
cons step is definitional, avoiding position-arithmetic transports. Novel
packaging. -/
def snocEnv {C : RType → Type} : (Γ : List RType) → (σ : RType) →
    (∀ v : Fin Γ.length, C (Γ.get v)) → C σ →
    ∀ k : Fin (Γ ++ [σ]).length, C ((Γ ++ [σ]).get k)
  | [], _σ, _ρ, x => Fin.cons x finZeroElim
  | _γ :: Γ', σ, ρ, x => Fin.cons (ρ 0) (snocEnv Γ' σ (fun v => ρ v.succ) x)

/-- The extended environment reads the appended value at every position at or
beyond `Γ.length`, heterogeneously (the append transport erased). -/
theorem snocEnv_heq_right {C : RType → Type} : (Γ : List RType) → (σ : RType) →
    (ρ : ∀ v : Fin Γ.length, C (Γ.get v)) → (x : C σ) →
    (k : Fin (Γ ++ [σ]).length) → Γ.length ≤ k.val →
    snocEnv Γ σ ρ x k ≍ x
  | [], _σ, _ρ, _x, k, _hk => by
    induction k using Fin.cases with
    | zero => exact HEq.rfl
    | succ k' => exact k'.elim0
  | _γ :: Γ', σ, ρ, x, k, hk => by
    induction k using Fin.cases with
    | zero => exact absurd hk (by simp)
    | succ k' =>
      refine (heq_of_eq (Fin.cons_succ _ _ k')).trans ?_
      exact snocEnv_heq_right Γ' σ (fun v => ρ v.succ) x k' (by simpa using hk)

/-- The extended environment reads the source environment at every position
below `Γ.length`, heterogeneously (the append transport erased). -/
theorem snocEnv_heq_left {C : RType → Type} : (Γ : List RType) → (σ : RType) →
    (ρ : ∀ v : Fin Γ.length, C (Γ.get v)) → (x : C σ) → (i : Fin Γ.length) →
    (k : Fin (Γ ++ [σ]).length) → k.val = i.val →
    snocEnv Γ σ ρ x k ≍ ρ i
  | [], _σ, _ρ, _x, i, _k, _hk => i.elim0
  | _γ :: Γ', σ, ρ, x, i, k, hk => by
    induction k using Fin.cases with
    | zero =>
      obtain ⟨iv, hiv⟩ := i
      obtain rfl : iv = 0 := by simpa using hk.symm
      exact HEq.rfl
    | succ k' =>
      obtain ⟨iv, hiv⟩ := i
      cases iv with
      | zero => exact absurd hk (by simp)
      | succ iv' =>
        refine (heq_of_eq (Fin.cons_succ _ _ k')).trans ?_
        exact snocEnv_heq_left Γ' σ (fun v => ρ v.succ) x
          ⟨iv', by have h := hiv; simp only [List.length_cons] at h; omega⟩ k'
          (by simpa using hk)

/-- Currying at an append transports to the currying of the extended
environment: the transport of `curryInterp` along `RType.curried_append`
curries the source context and consumes the appended sort as the final
argument, read through `snocEnv`. -/
theorem cast_curryInterp_snoc (A : AlgSig) : (Γ : List RType) → (σ τ : RType) →
    (g : (∀ k : Fin (Γ ++ [σ]).length,
        RType.interp (FreeAlg A) ((Γ ++ [σ]).get k)) → RType.interp (FreeAlg A) τ) →
    cast (congrArg (RType.interp (FreeAlg A)) (RType.curried_append Γ [σ] τ))
        (curryInterp A (Γ ++ [σ]) τ g)
      = curryInterp A Γ (RType.arrow σ τ) (fun ρ x => g (snocEnv Γ σ ρ x))
  | [], σ, τ, g =>
    eq_of_heq ((cast_heq _ _).trans (heq_of_eq (funext (fun _x => rfl))))
  | γ :: Γ', σ, τ, g => by
    funext a
    refine (cast_arrow_apply (A := A)
      (RType.curried_append Γ' [σ] τ)
      (curryInterp A ((γ :: Γ') ++ [σ]) τ g) a).trans ?_
    exact cast_curryInterp_snoc A Γ' σ τ (fun ρ' => g (Fin.cons a ρ'))

theorem cLiftArrow_interp (A : AlgSig) (σ ρ : RType) (i : A.B)
    (ihρ : RIdent A (List.replicate (A.ar i) ρ) ρ)
    (phi : ∀ j : Fin (List.replicate (A.ar i) (RType.arrow σ ρ)).length,
      RType.interp (FreeAlg A) ((List.replicate (A.ar i) (RType.arrow σ ρ)).get j))
    (x : RType.interp (FreeAlg A) σ) :
    (cLiftArrow A σ ρ i ihρ).interp phi x
      = ihρ.interp (fun j =>
          cast (congrArg (RType.interp (FreeAlg A)) (get_replicate (A.ar i) ρ j).symm)
            ((cast (congrArg (RType.interp (FreeAlg A))
                (get_replicate (A.ar i) (RType.arrow σ ρ)
                  (Fin.cast (by rw [List.length_replicate, List.length_replicate]) j)))
              (phi (Fin.cast (by rw [List.length_replicate, List.length_replicate]) j))) x)) := by
  refine (congrArg (fun f => f x)
    (appPrefixVars_eval _ ρ phi _ [σ] _ (fun k => Tm.var k))).trans ?_
  refine (congrFun (congrArg (fun z => appChain A (List.replicate (A.ar i) (RType.arrow σ ρ))
      (RType.arrow σ ρ) z phi)
      (cast_curryInterp_snoc A (List.replicate (A.ar i) (RType.arrow σ ρ)) σ ρ _)) x).trans ?_
  refine (congrFun (appChain_curryInterp A (List.replicate (A.ar i) (RType.arrow σ ρ))
      (RType.arrow σ ρ) _ phi) x).trans ?_
  refine congrArg ihρ.interp (funext fun j => ?_)
  change Tm.eval _ _ (Tm.reind _ (defnApp _ _ _ _)) = _
  erw [Tm.eval_transport, defnApp_eval, Tm.eval_transport, Tm.eval_transport,
    Tm.eval_var, Tm.eval_var]
  refine congrArg (cast _) (congr ?_ ?_)
  · exact eq_of_heq ((cast_heq _ _).trans
      ((snocEnv_heq_left _ σ phi x _ _ rfl).trans (cast_heq _ _).symm))
  · exact eq_of_heq ((cast_heq _ _).trans
      (snocEnv_heq_right _ σ phi x _ (Nat.le_add_right _ _)))

/-- The recurrence-context environment over an empty parameter list reads the
recursive-result family at each replicated position, heterogeneously. A fact
local to the pointwise constructor lift. -/
theorem childEnv_nil_heq {C : RType → Type} (σ : RType) (n : Nat)
    (xvec : ∀ i : Fin ([] : List RType).length, C (([] : List RType).get i))
    (rest : Fin n → C σ) (k : Fin ([] ++ List.replicate n σ).length) (m : Fin n)
    (hkm : k.val = m.val) :
    childEnv [] σ n xvec rest k ≍ rest m := by
  unfold childEnv
  rw [dif_neg (by simp : ¬ k.val < ([] : List RType).length)]
  exact (cast_heq _ _).trans (heq_of_eq (congrArg rest (Fin.ext (by simpa using hkm))))

/-- A recurrence-result read through the arrow lift's cast of an empty-parameter
recurrence environment recovers the family entry at the matching position. A
cast-commutation fact local to the arrow-sort lift recurrence. -/
theorem cLiftArrow_arg_eq (A : AlgSig) (σ ρ : RType) (n : Nat)
    (xvec : ∀ i : Fin ([] : Ctx RType).length,
      RType.interp (FreeAlg A) (([] : Ctx RType).get i))
    (rest : Fin n → RType.interp (FreeAlg A) (RType.arrow σ ρ))
    (j : Fin (List.replicate n ρ).length) (hjb : j.val < n)
    (p1 : (List.replicate n ρ).length = (List.replicate n (RType.arrow σ ρ)).length) :
    cast (congrArg (RType.interp (FreeAlg A))
        (get_replicate n (RType.arrow σ ρ) (Fin.cast p1 j)))
      (childEnv [] (RType.arrow σ ρ) n xvec rest (Fin.cast p1 j))
      = rest ⟨j.val, hjb⟩ :=
  eq_of_heq ((cast_heq _ _).trans
    (childEnv_nil_heq (RType.arrow σ ρ) n xvec rest _ ⟨j.val, hjb⟩ rfl))

/-- Applying the arrow-sort lift recurrence to an argument reduces to the
codomain lift recurrence (Leivant III section 2.4(1)): the recurrence over the
lifts `cLiftArrow A σ ρ i`, run on a recurrence argument and applied to `x`,
equals the recurrence over the codomain lifts `ihρ i`. The reconstructed value
is independent of `x`; the argument is threaded through the pointwise lifts
without affecting the object-target reconstruction. Proved by structural
induction via `PolyFix.ind` through `cLiftArrow_interp`. -/
theorem cLiftArrow_recurse_apply (A : AlgSig) (σ ρ : RType)
    (ihρ : (i : A.B) → RIdent A (List.replicate (A.ar i) ρ) ρ)
    (xvec : ∀ i : Fin ([] : Ctx RType).length,
      RType.interp (FreeAlg A) (([] : Ctx RType).get i))
    (x : RType.interp (FreeAlg A) σ) (t : FreeAlg A) :
    (FreeAlg.recurse (A := A) (P := Unit)
        (fun i _ _sub phi =>
          (cLiftArrow A σ ρ i (ihρ i)).interp
            (childEnv [] (RType.arrow σ ρ) (A.ar i) xvec phi))
        () t) x
      = FreeAlg.recurse (A := A) (P := Unit)
          (fun i _ _sub phi => (ihρ i).interp (childEnv [] ρ (A.ar i) xvec phi))
          () t := by
  refine PolyFix.ind (P := A.polyEndo)
    (motive := fun {_} t =>
      (FreeAlg.recurse (A := A) (P := Unit)
          (fun i _ _sub phi =>
            (cLiftArrow A σ ρ i (ihρ i)).interp
              (childEnv [] (RType.arrow σ ρ) (A.ar i) xvec phi))
          () t) x
        = FreeAlg.recurse (A := A) (P := Unit)
            (fun i _ _sub phi => (ihρ i).interp (childEnv [] ρ (A.ar i) xvec phi))
            () t)
    (fun b children ihc => ?_) t
  refine Eq.trans (cLiftArrow_interp A σ ρ b (ihρ b)
    (childEnv [] (RType.arrow σ ρ) (A.ar b) xvec
      (fun e => FreeAlg.recurse (A := A) (P := Unit)
        (fun i _ _sub phi =>
          (cLiftArrow A σ ρ i (ihρ i)).interp
            (childEnv [] (RType.arrow σ ρ) (A.ar i) xvec phi))
        () (children e))) x) ?_
  refine congrArg (ihρ b).interp (funext fun j => ?_)
  have hjb : j.val < A.ar b := by simpa using j.isLt
  refine eq_of_heq ((cast_heq _ _).trans
    (HEq.trans ?_ (childEnv_nil_heq ρ (A.ar b) xvec _ j ⟨j.val, hjb⟩ rfl).symm))
  exact heq_of_eq
    ((congrArg (fun f => f x) (cLiftArrow_arg_eq A σ ρ (A.ar b) xvec _ j hjb _)).trans
      (ihc ⟨j.val, hjb⟩))

/-- The full lift recurrence over a curried decomposition reconstructs its
recurrence argument on the carrier copy (Leivant III section 2.4(1)): applying
the recurrence over the lifts `cLiftAux A D θ hθ` to any argument tuple over the
domains `D` recovers the recurrence argument `t`, transported along the
carrier-copy equality of the object target `θ`. Proved by structural induction on
`D`: the empty case is `kappaHat_recurse_id`, and the cons step peels one domain
via `cLiftArrow_recurse_apply`. -/
theorem cLiftAux_recurse_appChain (A : AlgSig) (θ : RType) (hθ : θ.IsObj)
    (xvec : ∀ i : Fin ([] : Ctx RType).length,
      RType.interp (FreeAlg A) (([] : Ctx RType).get i)) :
    (D : List RType) → (t : FreeAlg A) →
    (args : ∀ k : Fin D.length, RType.interp (FreeAlg A) (D.get k)) →
    appChain A D θ
        (FreeAlg.recurse (A := A) (P := Unit)
          (fun i _ _sub phi => (cLiftAux A D θ hθ i).interp
            (childEnv [] (RType.curried D θ) (A.ar i) xvec phi))
          () t)
        args
      = cast (RType.interp_isObj (FreeAlg A) hθ).symm t
  | [], t, _args => kappaHat_recurse_id A θ hθ xvec t
  | σ :: D', t, args =>
    Eq.trans
      (congrArg (fun z => appChain A D' θ z (fun k => args k.succ))
        (cLiftArrow_recurse_apply A σ (RType.curried D' θ)
          (fun i => cLiftAux A D' θ hθ i) xvec (args 0) t))
      (cLiftAux_recurse_appChain A θ hθ xvec D' t (fun k => args k.succ))

/-- Evaluation of a saturated-hole occurrence against a definition model reads
the referenced identifier's denotation on the recursively evaluated argument
tuple. A definitional reduction local to the coercion identifiers. -/
theorem defnHole_eval {A : AlgSig} {n : Nat} {holeIdx : Fin n → List RType × RType}
    {Γ : Ctx RType}
    (ih : ∀ j : Fin n, (∀ i : Fin (holeIdx j).1.length,
        RType.interp (FreeAlg A) ((holeIdx j).1.get i)) →
        RType.interp (FreeAlg A) (holeIdx j).2)
    (j : Fin n)
    (args : ∀ i : Fin (holeIdx j).1.length, Tm (defnSig A n holeIdx) Γ ((holeIdx j).1.get i))
    (ρ : (defnModel A n holeIdx ih).Env Γ) :
    (Tm.op (sig := defnSig A n holeIdx) (Sum.inl (Sum.inr j)) args).eval
        (defnModel A n holeIdx ih) ρ
      = ih j (fun i => (args i).eval (defnModel A n holeIdx ih) ρ) :=
  rfl

/-- Evaluation of the full saturating application chain: applying a combinator at
the curried sort `curried D θ` to a full argument tuple denotes `appChain` of the
combinator's value over `D`. Proved by structural recursion on `D` through
`defnApp_eval`. -/
theorem appArgs_eval {A : AlgSig} {n : Nat} {holeIdx : Fin n → List RType × RType}
    {Γ : Ctx RType}
    (ih : ∀ j : Fin n, (∀ i : Fin (holeIdx j).1.length,
        RType.interp (FreeAlg A) ((holeIdx j).1.get i)) →
        RType.interp (FreeAlg A) (holeIdx j).2)
    (θ : RType) (ρ : (defnModel A n holeIdx ih).Env Γ) :
    (D : List RType) →
    (c : Tm (defnSig A n holeIdx) Γ (RType.curried D θ)) →
    (args : (k : Fin D.length) → Tm (defnSig A n holeIdx) Γ (D.get k)) →
    (appArgs θ D c args).eval (defnModel A n holeIdx ih) ρ
      = appChain A D θ (c.eval (defnModel A n holeIdx ih) ρ)
          (fun k => (args k).eval (defnModel A n holeIdx ih) ρ)
  | [], _c, _args => rfl
  | a :: D', c, args => by
    rw [show appArgs θ (a :: D') c args
        = appArgs θ D' (defnApp a (RType.curried D' θ) c (args ⟨0, Nat.succ_pos _⟩))
            (fun k => args k.succ) from rfl,
      appArgs_eval ih θ ρ D'
        (defnApp a (RType.curried D' θ) c (args ⟨0, Nat.succ_pos _⟩)) (fun k => args k.succ),
      defnApp_eval]
    rfl

/-- The coercion `applyCanon` feeds its input, read at the curried decomposition
of `τ`, to the canonical functionals at each domain sort (Leivant III section
2.4(1)): its denotation is the application chain of the transported input over
the domains `RType.domains τ`. The canonical functionals appear only as the
argument tuple. Proved by unfolding the explicit definition through
`appArgs_eval`. -/
theorem applyCanon_interp (A : AlgSig) (b₀ : A.B) (h₀ : A.ar b₀ = 0) (τ : RType)
    (env : ∀ i : Fin ([τ] : Ctx RType).length,
      RType.interp (FreeAlg A) (([τ] : Ctx RType).get i)) :
    (applyCanon A b₀ h₀ τ).interp env
      = appChain A (RType.domains τ) (RType.objTarget τ)
          (cast (congrArg (RType.interp (FreeAlg A)) (RType.curried_domains τ)) (env 0))
          (fun j => curryInterp A [] ((RType.domains τ).get j)
            ((canonIdent A b₀ h₀ ((RType.domains τ).get j)).interp)) := by
  rw [applyCanon, RIdent.interp_defn, appArgs_eval, Tm.eval_transport]
  rfl

/-- A monotonic recurrence identifier transported along a sort equality of its
recurrence sort equals the recurrence over the transported step functions. A
cast-commutation fact local to the full kappa-hat. -/
theorem RIdent.mrec_cast {A : AlgSig} {s₀ s₁ : RType} (e : s₀ = s₁)
    (steps : (i : A.B) → RIdent A (List.replicate (A.ar i) s₀) s₀) :
    cast (congrArg (fun s => RIdent A [RType.omega s] s) e) (RIdent.mrec [] s₀ steps)
      = RIdent.mrec [] s₁ (fun i =>
          cast (congrArg (fun s => RIdent A (List.replicate (A.ar i) s) s) e) (steps i)) := by
  subst e; rfl

/-- The denotation of a monotonic recurrence transported along a sort equality of
its recurrence sort reads its recurrence argument on the carrier copy and
transports the recurrence value. A cast-commutation fact local to the full
kappa-hat; the recurrence argument sits at an omega sort, whose denotation is the
carrier regardless of the sort. -/
theorem RIdent.interp_omega_cast {A : AlgSig} {s₀ s₁ : RType} (e : s₀ = s₁)
    (g : RIdent A [RType.omega s₀] s₀)
    (env : ∀ i : Fin ([RType.omega s₁] : Ctx RType).length,
      RType.interp (FreeAlg A) (([RType.omega s₁] : Ctx RType).get i))
    (env' : ∀ i : Fin ([RType.omega s₀] : Ctx RType).length,
      RType.interp (FreeAlg A) (([RType.omega s₀] : Ctx RType).get i))
    (henv : env 0 ≍ env' 0) :
    (cast (congrArg (fun s => RIdent A [RType.omega s] s) e) g).interp env
      = cast (congrArg (RType.interp (FreeAlg A)) e) (g.interp env') := by
  subst e
  refine congrArg g.interp (funext fun i => ?_)
  refine Fin.cases ?_ (fun j => j.elim0) i
  exact eq_of_heq henv

/-- The recurrence semantics of a monotonic recurrence at the empty parameter
context (Leivant III section 2.3, eq. (4)): its denotation is the free-algebra
recurrence over the step functions, run on the recurrence argument. Holds by
definitional unfolding. -/
theorem RIdent.mrec_interp (A : AlgSig) (s : RType)
    (steps : (i : A.B) → RIdent A (List.replicate (A.ar i) s) s)
    (ρ : ∀ i : Fin ([RType.omega s] : Ctx RType).length,
      RType.interp (FreeAlg A) (([RType.omega s] : Ctx RType).get i)) :
    (RIdent.mrec [] s steps).interp ρ
      = FreeAlg.recurse (A := A) (P := Unit)
          (fun i _ _sub phi => (steps i).interp
            (childEnv [] s (A.ar i) (envHead [] (RType.omega s) ρ) phi))
          () (envLast [] (RType.omega s) ρ) :=
  rfl

/-- An object sort has an empty domain list (Leivant III section 2.3): for
`θ.IsObj`, `RType.domains θ = []`. -/
theorem RType.domains_of_isObj {θ : RType} (hθ : θ.IsObj) : RType.domains θ = [] := by
  rcases θ with ⟨_, i, childx⟩
  rcases hθ with h | h <;> (simp only [RType.shape, PolyFix.index] at h; subst h) <;> rfl

/-- The pointwise constructor lift at an object sort agrees, up to the curried
decomposition transport, with the lift over the empty domain list. A
cast-commutation fact local to the full kappa-hat, via proof irrelevance on the
object-sort hypothesis. -/
theorem cLiftAux_heq_kappaHatStep (A : AlgSig) (D : List RType) (θ : RType)
    (hθ : θ.IsObj) (i : A.B) (hd : D = []) :
    cLiftAux A D θ hθ i ≍ kappaHatStep A θ hθ i := by
  subst hd; exact HEq.rfl

/-- A kappa-hat step is heterogeneously invariant under a sort equality of its
object sort. A cast-commutation fact local to the full kappa-hat. -/
theorem kappaHatStep_heq (A : AlgSig) (θ τ : RType) (hθ : θ.IsObj) (hτ : τ.IsObj)
    (i : A.B) (ht : θ = τ) : kappaHatStep A θ hθ i ≍ kappaHatStep A τ hτ i := by
  subst ht; rfl

/-- The pointwise constructor lift at every r-type equals its lift over the
curried decomposition, transported along the decomposition equality (Leivant III
section 2.4(1)): at an arrow sort by definition, and at an object sort through the
empty-domain agreement. Proved by cases on the object-sort hypothesis. -/
theorem cLift_eq_cast_cLiftAux (A : AlgSig) (τ : RType) (i : A.B) :
    cLift A τ i
      = cast (congrArg (fun s => RIdent A (List.replicate (A.ar i) s) s)
          (RType.curried_domains τ).symm)
          (cLiftAux A (RType.domains τ) (RType.objTarget τ) (RType.objTarget_isObj τ) i) := by
  rw [cLift]
  by_cases h : τ.IsObj
  · rw [dif_pos h]
    refine eq_of_heq (HEq.trans ?_ (cast_heq _ _).symm)
    exact (kappaHatStep_heq A (RType.objTarget τ) τ (RType.objTarget_isObj τ) h i
        (RType.objTarget_of_isObj h)).symm.trans
      (cLiftAux_heq_kappaHatStep A (RType.domains τ) (RType.objTarget τ) (RType.objTarget_isObj τ) i
        (RType.domains_of_isObj h)).symm
  · rw [dif_neg h]

/-- The full kappa-hat equals the recurrence over the curried-decomposition lifts,
transported along the decomposition equality of its recurrence sort (Leivant III
section 2.4(1)). Proved from `cLift_eq_cast_cLiftAux` through `RIdent.mrec_cast`. -/
theorem kappaHatFull_eq_cast_mrecAux (A : AlgSig) (τ : RType) :
    kappaHatFull A τ
      = cast (congrArg (fun s => RIdent A [RType.omega s] s) (RType.curried_domains τ).symm)
          (RIdent.mrec [] (RType.curried (RType.domains τ) (RType.objTarget τ))
            (cLiftAux A (RType.domains τ) (RType.objTarget τ) (RType.objTarget_isObj τ))) := by
  rw [kappaHatFull, RIdent.mrec_cast (A := A) (RType.curried_domains τ).symm]
  exact congrArg (RIdent.mrec [] τ) (funext fun i => cLift_eq_cast_cLiftAux A τ i)

/-- The full kappa-hat, transported to its curried decomposition and applied to
any argument tuple over its domains, reconstructs its recurrence argument on the
carrier copy (Leivant III section 2.4(1)). Assembles the bridge to the
curried-decomposition lifts with the master reconstruction lemma
`cLiftAux_recurse_appChain`. -/
theorem kappaHatFull_appChain (A : AlgSig) (τ : RType)
    (σ' : ∀ i : Fin ([RType.omega τ] : Ctx RType).length,
      RType.interp (FreeAlg A) (([RType.omega τ] : Ctx RType).get i))
    (args : ∀ k : Fin (RType.domains τ).length,
      RType.interp (FreeAlg A) ((RType.domains τ).get k)) :
    appChain A (RType.domains τ) (RType.objTarget τ)
        (cast (congrArg (RType.interp (FreeAlg A)) (RType.curried_domains τ))
          ((kappaHatFull A τ).interp σ'))
        args
      = cast (RType.interp_isObj (FreeAlg A) (RType.objTarget_isObj τ)).symm (σ' 0) := by
  have hcomb :
      cast (congrArg (RType.interp (FreeAlg A)) (RType.curried_domains τ))
          ((kappaHatFull A τ).interp σ')
        = (RIdent.mrec [] (RType.curried (RType.domains τ) (RType.objTarget τ))
            (cLiftAux A (RType.domains τ) (RType.objTarget τ) (RType.objTarget_isObj τ))).interp
            (Fin.cons (σ' 0) finZeroElim) := by
    rw [kappaHatFull_eq_cast_mrecAux,
      RIdent.interp_omega_cast (RType.curried_domains τ).symm _ σ'
        (Fin.cons (σ' 0) finZeroElim) HEq.rfl, cast_cast]
    exact eq_of_heq (cast_heq _ _)
  rw [hcomb, RIdent.mrec_interp]
  refine (cLiftAux_recurse_appChain A (RType.objTarget τ) (RType.objTarget_isObj τ) _
    (RType.domains τ) _ args).trans ?_
  refine congrArg (cast (RType.interp_isObj (FreeAlg A) (RType.objTarget_isObj τ)).symm) ?_
  unfold envLast
  exact eq_of_heq (cast_heq _ _)

/-- Leivant III section 2.4(1): the coercion `κ_τ : Ω τ → θ` (with
`θ = τ.objTarget`) denotes the identity on the carrier copy. Its value on an
environment is the recurrence argument, a carrier element, transported along the
carrier-copy equality of the object target. -/
theorem kappaIdent_interp (A : AlgSig) (b₀ : A.B) (h₀ : A.ar b₀ = 0) (τ : RType)
    (ρ : ∀ i : Fin ([RType.omega τ] : Ctx RType).length,
      RType.interp (FreeAlg A) (([RType.omega τ] : Ctx RType).get i)) :
    (kappaIdent A b₀ h₀ τ).interp ρ
      = cast (RType.interp_isObj (FreeAlg A) (RType.objTarget_isObj τ)).symm (ρ 0) := by
  rw [kappaIdent, RIdent.interp_defn]
  dsimp only
  erw [defnHole_eval]
  dsimp only
  rw [applyCanon_interp]
  erw [defnHole_eval]
  dsimp only
  exact kappaHatFull_appChain A τ _ _

/-- The downward coercion `deltaAux` at every r-type denotes the identity on the
carrier copy (Leivant III section 2.4(1)): its value on an environment is the
recurrence argument, a carrier element, transported along the carrier-copy
equality of the object target. Proved by structural induction via `PolyFix.ind`;
the omega step composes the identity denotation of the coercion at the child with
that of `kappaIdent`. -/
theorem deltaAux_interp (A : AlgSig) (b₀ : A.B) (h₀ : A.ar b₀ = 0) :
    (τ : RType) → (ρ : ∀ i : Fin ([RType.objTarget τ] : Ctx RType).length,
      RType.interp (FreeAlg A) (([RType.objTarget τ] : Ctx RType).get i)) →
    (deltaAux A b₀ h₀ τ).interp ρ
      = cast (RType.interp_isObj (FreeAlg A) (RType.objTarget_isObj τ)) (ρ 0) :=
  fun τ => PolyFix.ind (P := rTypeSig.polyEndo)
    (motive := fun {_} t => ∀ ρ, (deltaAux A b₀ h₀ t).interp ρ
      = cast (RType.interp_isObj (FreeAlg A) (RType.objTarget_isObj t)) (ρ 0))
    (fun i childx ih =>
      match i, childx, ih with
      | RTypeShape.o, childx, _ => fun ρ => eq_of_heq (cast_heq _ _).symm
      | RTypeShape.arrow, childx, ih => fun ρ => ih ⟨1, by decide⟩ ρ
      | RTypeShape.omega, childx, ih => fun ρ => by
        erw [RIdent.interp_defn]
        dsimp only
        erw [defnHole_eval]
        dsimp only
        refine (ih ⟨0, by decide⟩ _).trans ?_
        erw [defnHole_eval]
        dsimp only
        rw [kappaIdent_interp]
        exact eq_of_heq ((cast_heq _ _).trans ((cast_heq _ _).trans (cast_heq _ _).symm))) τ

/-- An identifier over a singleton context transported along a sort equality of
that context reads the transported environment. A cast-commutation fact local to
the downward coercion. -/
theorem RIdent.interp_single_cast {A : AlgSig} {s₀ s₁ : RType} (e : s₀ = s₁)
    (g : RIdent A [s₀] RType.o)
    (env : ∀ i : Fin ([s₁] : Ctx RType).length,
      RType.interp (FreeAlg A) (([s₁] : Ctx RType).get i))
    (env' : ∀ i : Fin ([s₀] : Ctx RType).length,
      RType.interp (FreeAlg A) (([s₀] : Ctx RType).get i))
    (henv : env 0 ≍ env' 0) :
    (cast (congrArg (fun s => RIdent A [s] RType.o) e) g).interp env = g.interp env' := by
  subst e
  refine congrArg g.interp (funext fun i => ?_)
  refine Fin.cases ?_ (fun j => j.elim0) i
  exact eq_of_heq henv

/-- Leivant III section 2.4(1)'s coercion `δ_θ : θ → o` at an object sort `θ`
denotes the identity on the carrier copy: its value on an environment is the
recurrence argument, a carrier element, read on the carrier copy of the object
sort. Generalizes the tower-sort `ramDeltaIdent_interp` to an arbitrary object
sort. -/
theorem deltaIdent_interp (A : AlgSig) (b₀ : A.B) (h₀ : A.ar b₀ = 0) (θ : RType)
    (hθ : θ.IsObj)
    (ρ : ∀ i : Fin ([θ] : Ctx RType).length,
      RType.interp (FreeAlg A) (([θ] : Ctx RType).get i)) :
    (deltaIdent A b₀ h₀ θ hθ).interp ρ = cast (RType.interp_isObj (FreeAlg A) hθ) (ρ 0) := by
  rw [deltaIdent,
    RIdent.interp_single_cast (RType.objTarget_of_isObj hθ) (deltaAux A b₀ h₀ θ) ρ
      (Fin.cons
        (cast (congrArg (RType.interp (FreeAlg A)) (RType.objTarget_of_isObj hθ).symm) (ρ 0))
        finZeroElim)
      (cast_heq _ _).symm,
    deltaAux_interp]
  exact eq_of_heq ((cast_heq _ _).trans ((cast_heq _ _).trans (cast_heq _ _).symm))

end GebLean.Ramified
