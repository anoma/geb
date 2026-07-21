import GebLean.Ramified.Polynomial.Ident
import GebLean.Ramified.Polynomial.SynCat
import GebLean.Ramified.Polynomial.Interp
import GebLean.Ramified.Polynomial.RType
import GebLean.Ramified.SortedSig
import GebLean.Ramified.Interp

/-!
# The primed higher-order presentation and schema identifiers

A second realization of the higher-order presentation
(`GebLean/Ramified/HigherOrder.lean`) on the primed identifier layer
`RIdent'` (`GebLean/Ramified/Polynomial/Ident.lean`): the application chain
inverting the currying, the saturated and constant identifier summands, and
the multi-sorted presentation `higherOrder'` assembling the constructor
summand, application, and the identifiers, over the standard carriers
`RType'.interp (FreeAlg' A)`. The syntactic category `RMRecCat'` instantiates
the generic primed syntactic category `SynCat'`
(`GebLean/Ramified/Polynomial/SynCat.lean`) at `higherOrder'`; `identHom'`
applies a primed identifier to its context's variables as a morphism of that
category.

This module mirrors the legacy `GebLean/Ramified/HigherOrder.lean` from
`appChain` onward; the earlier signature layer (`appSig'`,
`stdConstructorInterp'`, `stdAppInterp'`, `RType'.curried`, `curryInterp'`)
already lives in `GebLean/Ramified/Polynomial/Ident.lean`.

## Main definitions

* `appChain'` — the application chain: iterated application of a value at a
  curried sort to an argument environment.
* `identSig'` — the saturated identifier summand: operations are the
  identifiers, each of its context as arity and result sort as result.
* `identConstSig'` — the identifier-constant summand: one nullary operation
  per identifier, of its curried arrow sort as result.
* `higherOrderModel'` — the standard model of the primed higher-order
  presentation over `A`.
* `higherOrder'` — the primed higher-order presentation over `A`.
* `RMRecCat'` — the syntactic category of the primed higher-order system.
* `identHom'` — the morphism `Γ' ⟶ [τ']` of `RMRecCat' A` applying an
  identifier to the context's variables.

## Main statements

* `appChain_curryInterp'` — the application chain inverts the currying.
* `RIdent'.interp_eq_appChain_curryInterp'` — coherence: the saturated
  identifier's denotation equals the application chain of its constant's
  denotation.
* `identHom_eval'` — the standard-model evaluation of `identHom' f` reads off
  `RIdent'.interp`.

## References

D. Leivant, "Ramified recurrence and computational complexity III: Higher
type recurrence and elementary complexity", Annals of Pure and Applied Logic
96 (1999) 209-229, DOI `10.1016/S0168-0072(98)00040-2`. The schema of
higher-type identifiers -- explicit definitions, ramified monotonic
recurrence (eq. (4)), and flat recurrence (eq. (5)) -- is section 2.3; every
object sort denotes a copy of the base carrier in section 2.7. The
data-types-a-la-carte factoring follows W. Swierstra, "Data types a la
carte", Journal of Functional Programming 18 (2008) 423-436, DOI
`10.1017/S0956796808006758`.

## Tags

ramified recurrence, higher type, application, schema identifier,
presentation, syntactic category, slice category, W-type
-/

namespace GebLean.Ramified.Polynomial

open GebLean.Ramified CategoryTheory

/-- The application chain: iterated application of a value at a curried sort
`RType'.curried Γ' τ'` to an argument environment `Env Γ'`, yielding a value at
`τ'`. The application former's action on an identifier's constant, recovering
the saturated identifier's denotation. Mirror of the legacy `appChain`. -/
def appChain' (A : AlgSig) : (Γ' : List RType') → (τ' : RType') →
    RType'.interp (FreeAlg' A) (RType'.curried Γ' τ') →
    (∀ i : Fin Γ'.length, RType'.interp (FreeAlg' A) (Γ'.get i)) →
    RType'.interp (FreeAlg' A) τ'
  | [], _τ', c, _ρ => c
  | σ' :: Γ'', τ', c, ρ =>
      appChain' A Γ'' τ' ((c : RType'.interp (FreeAlg' A) σ' →
        RType'.interp (FreeAlg' A) (RType'.curried Γ'' τ')) (ρ 0)) (fun i => ρ i.succ)

/-- The application chain inverts the currying: applying `curryInterp' A Γ' τ'
g` to an environment `ρ` recovers `g ρ`. Proved by induction on `Γ'`; the step
folds the leading argument back into the environment via
`Fin.cons_self_tail`. Mirror of the legacy `appChain_curryInterp`. -/
theorem appChain_curryInterp' (A : AlgSig) : (Γ' : List RType') → (τ' : RType') →
    (g : (∀ i : Fin Γ'.length, RType'.interp (FreeAlg' A) (Γ'.get i)) →
      RType'.interp (FreeAlg' A) τ') →
    (ρ : ∀ i : Fin Γ'.length, RType'.interp (FreeAlg' A) (Γ'.get i)) →
    appChain' A Γ' τ' (curryInterp' A Γ' τ' g) ρ = g ρ
  | [], _τ', g, _ρ => congrArg g (funext (fun i => i.elim0))
  | σ' :: Γ'', τ', g, ρ => by
    change appChain' A Γ'' τ' (curryInterp' A Γ'' τ' (fun ρ' => g (Fin.cons (ρ 0) ρ')))
        (fun i => ρ i.succ) = g ρ
    rw [appChain_curryInterp' A Γ'' τ' (fun ρ' => g (Fin.cons (ρ 0) ρ')) (fun i => ρ i.succ)]
    exact congrArg g (Fin.cons_self_tail ρ)

/-- Coherence of the two identifier surfacings (Leivant III section 2.3, the
higher-order system): the saturated identifier's denotation equals the
application chain of its constant's denotation. The constant of `f` denotes
`curryInterp' A Γ' τ' f.interp`; applying it along the argument environment via
`appChain'` recovers `f.interp`. Mirror of the legacy
`RIdent.interp_eq_appChain_curryInterp`. -/
theorem RIdent'.interp_eq_appChain_curryInterp' {A : AlgSig} {Γ' : List RType'}
    {τ' : RType'} (f : RIdent' A Γ' τ')
    (ρ : ∀ i : Fin Γ'.length, RType'.interp (FreeAlg' A) (Γ'.get i)) :
    f.interp ρ = appChain' A Γ' τ' (curryInterp' A Γ' τ' f.interp) ρ :=
  (appChain_curryInterp' A Γ' τ' f.interp ρ).symm

/-- The saturated identifier summand of the primed higher-order presentation:
operations are the schema-generated identifiers, of context as arity and
result sort as result. Each identifier also has a nullary constant form in
`identConstSig'`; the two surfacings agree by
`RIdent'.interp_eq_appChain_curryInterp'`. Mirror of the legacy `identSig`. -/
def identSig' (A : AlgSig) : SortedSig RType' where
  Op := Σ Γ' : List RType', Σ τ' : RType', RIdent' A Γ' τ'
  arity op := op.1
  result op := op.2.1

/-- The identifier-constant summand of the primed higher-order presentation
(Leivant III section 2.3, the higher-order system, DOI
`10.1016/S0168-0072(98)00040-2`): one nullary operation per identifier
`f : RIdent' A Γ' τ'`, with result the curried arrow sort
`RType'.curried Γ' τ'`. Mirror of the legacy `identConstSig`. -/
def identConstSig' (A : AlgSig) : SortedSig RType' where
  Op := Σ Γ' : List RType', Σ τ' : RType', RIdent' A Γ' τ'
  arity _op := []
  result op := RType'.curried op.1 op.2.1

/-- The standard model of the primed higher-order presentation over `A`: the
standard carriers, with constructors and application read as usual, each
saturated identifier read by its own denotation, and each identifier constant
read by the currying of that denotation. Mirror of the legacy
`higherOrderModel`. -/
def higherOrderModel' (A : AlgSig) :
    SortedModel
      ((((constructorSig A RType'.IsObj).sum appSig').sum (identSig' A)).sum
        (identConstSig' A)) where
  carrier := RType'.interp (FreeAlg' A)
  interpOp op args :=
    match op with
    | Sum.inl (Sum.inl (Sum.inl cop)) => stdConstructorInterp' A cop args
    | Sum.inl (Sum.inl (Sum.inr aop)) => stdAppInterp' A aop args
    | Sum.inl (Sum.inr iop) => iop.2.2.interp args
    | Sum.inr icop => curryInterp' A icop.1 icop.2.1 icop.2.2.interp

/-- The primed higher-order presentation over `A` (Leivant III section 2.3):
the constructor summand at every object sort, application, the
schema-generated identifiers as saturated operations, and their nullary
constants at the curried arrow sorts, summed by `SortedSig.sum`, with the
standard model interpreting each operation over the standard carriers. Mirror
of the legacy `higherOrder`. -/
def higherOrder' (A : AlgSig) : Presentation where
  S := RType'
  sig :=
    ((((constructorSig A RType'.IsObj).sum appSig').sum (identSig' A)).sum
      (identConstSig' A))
  IsObj := RType'.IsObj
  alg := A
  std := higherOrderModel' A

/-- The syntactic category of the primed higher-order system over `A`: the
generic primed syntactic category of `higherOrder' A` under interpretative
equality at the standard model. Mirror of the legacy `RMRecCat`. -/
abbrev RMRecCat' (A : AlgSig) :=
  SynCat' (higherOrder' A) (interpQuotRel' (higherOrder' A))

/-- The morphism `Γ' ⟶ [τ']` of `RMRecCat' A` applying an identifier `f` to the
context's variables: the class of the tuple whose sole component is the
identifier operation `Sum.inl (Sum.inr ⟨Γ', τ', f⟩)` of `(higherOrder' A).sig`
applied to the domain variables. Mirror of the legacy `identHom`. -/
def identHom' {A : AlgSig} {Γ' : List RType'} {τ' : RType'} (f : RIdent' A Γ' τ') :
    Hom' (higherOrder' A) (interpQuotRel' (higherOrder' A)) Γ' [τ'] :=
  Quotient.mk _ (Fin.cons
    (Tm'.op (sig := (higherOrder' A).sig)
      (Sum.inl (Sum.inr ⟨Γ', τ', f⟩))
      (fun k => Tm'.var k))
    finZeroElim)

/-- The standard-model evaluation of `identHom' f` reads off `RIdent'.interp`:
the sole entry of the evaluated environment is `f.interp` at the argument
environment. Mirror of the legacy `identHom_eval`. -/
theorem identHom_eval' {A : AlgSig} {Γ' : List RType'} {τ' : RType'}
    (f : RIdent' A Γ' τ') (ρ : (standardModel (higherOrder' A)).Env Γ') :
    (identHom' f).eval ρ 0 = f.interp ρ :=
  rfl

end GebLean.Ramified.Polynomial
