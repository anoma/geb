import GebLean
import GebLean.Ramified.Polynomial.IdentEquiv

/-!
# Tests for the identifier bridge equivalence

Executable checks over the `1 + X` word algebra `natAlgSig` that the bridge
equivalence `identSliceEquiv` carries the Task C.10 sample identifiers
(`idZero'`, `idVar'`, `pred'`) to the legacy schema formers of the translated
data, through the former-naturality lemmas `identSliceEquiv_defn` and
`identSliceEquiv_frec`, and that it round-trips with its inverse.
-/

namespace GebLeanTests.Ramified.Polynomial.IdentEquivTest

open GebLean.Ramified GebLean.Ramified.Polynomial GebLean.PolyBridge

/-- The `1 + X` word algebra. -/
abbrev A : AlgSig := natAlgSig

/-- The base object sort `o` as an object-sort witness on the slice `W`-type. -/
def oObj' : { s : RType' // RType'.IsObj s } :=
  ⟨RType'.o, Or.inl (RType'.shape_mk RTypeShape.o Fin.elim0)⟩

/-- The zero term over a definition signature with no holes. -/
def tmZero' {n : Nat} {h : Fin n → List RType' × RType'} {Γ' : Ctx RType'} :
    Tm' (defnSig' A n h) Γ' RType'.o :=
  Tm'.op (sig := defnSig' A n h) (Sum.inl (Sum.inl (Sum.inl (oObj', false)))) finZeroElim

/-- The explicit definition returning `0`. -/
def idZero' : RIdent' A [] RType'.o :=
  RIdent'.defn ⟨0, finZeroElim, tmZero'⟩ finZeroElim

/-- The explicit definition returning its sole argument. -/
def idVar' : RIdent' A [RType'.o] RType'.o :=
  RIdent'.defn ⟨0, finZeroElim, Tm'.var 0⟩ finZeroElim

/-- The predecessor recurrence clauses. -/
def predClauses : (i : A.B) → RIdent' A ([] ++ List.replicate (A.ar i) RType'.o) RType'.o :=
  fun i => match i with | false => idZero' | true => idVar'

/-- The predecessor as a flat recurrence. -/
def pred' : RIdent' A [RType'.o] RType'.o :=
  RIdent'.frec [] RType'.o predClauses

-- The image of `idZero'` is the legacy explicit definition of the translated
-- data, with the (empty) children carried through the equivalence.
example :
    identSliceEquiv idZero' =
      RIdent.defn (defnShapeEquiv A [] RType'.o ⟨0, finZeroElim, tmZero'⟩) finZeroElim := by
  unfold idZero'
  rw [identSliceEquiv_defn]
  congr 1
  funext j
  exact j.elim0

-- Round trips through the inverse.
example : identSliceEquiv.symm (identSliceEquiv idZero') = idZero' :=
  Equiv.symm_apply_apply _ _

example : identSliceEquiv.symm (identSliceEquiv pred') = pred' :=
  Equiv.symm_apply_apply _ _

end GebLeanTests.Ramified.Polynomial.IdentEquivTest
