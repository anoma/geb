import GebLean.Ramified.Polynomial.HigherOrder
import GebLean.Ramified.Polynomial.IdentEquiv
import GebLean.Ramified.Polynomial.SynCatEquiv
import GebLean.Ramified.HigherOrder

/-!
# The primed-to-legacy higher-order category equivalence

The payoff of the primed higher-order layer: the syntactic category `RMRecCat'`
of the primed higher-order presentation (`GebLean/Ramified/Polynomial/
HigherOrder.lean`) is equivalent to the legacy `RMRecCat`
(`GebLean/Ramified/HigherOrder.lean`). The equivalence factors through the
legacy term layer over the primed presentation: the term-layer equivalence
`synCatSliceEquiv` (`GebLean/Ramified/Polynomial/SynCatEquiv.lean`) followed by
the syntactic-category equivalence `PresentationEquiv.synCatEquiv`
(`GebLean/Ramified/PresentationEquiv.lean`) of the presentation equivalence
`higherOrderPresEquiv` assembled here.

## Main definitions

* `identOpSliceEquiv` — the identifier-operation equivalence: the sigma
  congruence over the context, result-sort, and identifier bridges.
* `identSigEquiv`, `identConstSigEquiv` — the identifier summand signature
  isomorphisms.
* `higherOrderSigEquiv` — the signature isomorphism between the primed and
  legacy higher-order signatures, the `SortedSigEquiv.sum` of `baseSigEquiv`
  with the two identifier summands.
* `higherOrderPresEquiv` — the presentation equivalence between the primed and
  legacy higher-order presentations.
* `rmRecCatSliceEquiv` — the equivalence of syntactic categories
  `RMRecCat' A ≌ RMRecCat A`.

## References

D. Leivant, "Ramified recurrence and computational complexity III: Higher type
recurrence and elementary complexity", Annals of Pure and Applied Logic 96
(1999) 209-229, DOI `10.1016/S0168-0072(98)00040-2`, section 2.3 (the schema of
higher-type identifiers) and section 2.7 (every object sort denotes a copy of
the base carrier). Signature isomorphisms, presentation isomorphisms, and their
reducts follow D. Sannella, A. Tarlecki, "Foundations of Algebraic
Specification and Formal Software Development", Springer, 2012, DOI
`10.1007/978-3-642-17336-3`, Chapter 1.

## Tags

ramified recurrence, higher type, schema identifier, signature isomorphism,
presentation isomorphism, syntactic category, equivalence of categories, W-type
-/

namespace GebLean.Ramified.Polynomial

open GebLean.Ramified CategoryTheory

/-- The identifier-operation equivalence between the primed and legacy
identifier summands: the sigma congruence of the context bridge
`Equiv.listEquivOfEquiv rTypeSliceEquiv`, the result-sort bridge
`rTypeSliceEquiv`, and the identifier bridge `identSliceEquiv`. Both the
saturated summand `identSig'` and the constant summand `identConstSig'` carry
this same operation type. -/
def identOpSliceEquiv (A : AlgSig) :
    (Σ Γ' : List RType', Σ τ' : RType', RIdent' A Γ' τ') ≃
      Σ Γ : List RType, Σ τ : RType, RIdent A Γ τ :=
  Equiv.sigmaCongr (Equiv.listEquivOfEquiv rTypeSliceEquiv) (fun _Γ' =>
    Equiv.sigmaCongr rTypeSliceEquiv (fun _τ' => identSliceEquiv))

/-- The signature isomorphism between the primed and legacy saturated
identifier summands: `rTypeSliceEquiv` on sorts and `identOpSliceEquiv` on
operations, the arity and result being the transported identifier index. -/
def identSigEquiv (A : AlgSig) : SortedSigEquiv (identSig' A) (identSig A) where
  sortEquiv := rTypeSliceEquiv
  opEquiv := identOpSliceEquiv A
  arity_comm := fun _ => rfl
  result_comm := fun _ => rfl

/-- The signature isomorphism between the primed and legacy identifier-constant
summands: `rTypeSliceEquiv` on sorts and `identOpSliceEquiv` on operations, with
the result sort transported by `rTypeSliceEquiv_curried`. -/
def identConstSigEquiv (A : AlgSig) :
    SortedSigEquiv (identConstSig' A) (identConstSig A) where
  sortEquiv := rTypeSliceEquiv
  opEquiv := identOpSliceEquiv A
  arity_comm := fun _ => rfl
  result_comm := fun i => (rTypeSliceEquiv_curried i.1 i.2.1).symm

/-- The signature isomorphism between the primed and legacy higher-order
signatures: the summand-wise sum of `baseSigEquiv`, `identSigEquiv`, and
`identConstSigEquiv`. -/
def higherOrderSigEquiv (A : AlgSig) :
    SortedSigEquiv (higherOrder' A).sig (higherOrder A).sig :=
  ((baseSigEquiv A).sum (identSigEquiv A) rfl).sum (identConstSigEquiv A) rfl

/-- The presentation equivalence between the primed and legacy higher-order
presentations: the signature isomorphism `higherOrderSigEquiv` together with the
carrier bridge `carrierSliceEquiv`. The commutation with the operation
interpretations splits over the four summands: the constructors by
`stdConstructorInterp_agree`, application by `carrierSliceEquiv_arrow`, the
saturated identifiers by `identSliceEquiv_interp`, and the identifier constants
by `curryInterp'_agree` at that same agreement. -/
def higherOrderPresEquiv (A : AlgSig) :
    PresentationEquiv (higherOrder' A) (higherOrder A) where
  sigEquiv := higherOrderSigEquiv A
  carrierEquiv := carrierSliceEquiv A
  interpOp_comm := by
    rintro (((c | a) | i) | i) args
    · exact stdConstructorInterp_agree c args
        ((higherOrderSigEquiv A).arity_length (Sum.inl (Sum.inl (Sum.inl c))))
        (fun j => (higherOrderSigEquiv A).get_arity (Sum.inl (Sum.inl (Sum.inl c))) j)
    · exact carrierSliceEquiv_arrow a.1 a.2 (args ⟨0, Nat.succ_pos 1⟩) (args ⟨1, Nat.le_refl 2⟩)
    · exact identSliceEquiv_interp i.2.2 args
    · exact (congrArg (cast _)
        (curryInterp'_agree A i.1 i.2.1 i.2.2.interp (identSliceEquiv i.2.2).interp
          (fun ρ' => identSliceEquiv_interp i.2.2 ρ'))).trans
        ((cast_cast _ _ _).trans (cast_eq _ _))

/-- The equivalence of syntactic categories of the primed and legacy
higher-order systems: the term-layer equivalence `synCatSliceEquiv` at the
primed presentation followed by the syntactic-category equivalence of the
presentation equivalence `higherOrderPresEquiv`. -/
def rmRecCatSliceEquiv (A : AlgSig) : RMRecCat' A ≌ RMRecCat A :=
  (synCatSliceEquiv (higherOrder' A)).trans (higherOrderPresEquiv A).synCatEquiv

end GebLean.Ramified.Polynomial
