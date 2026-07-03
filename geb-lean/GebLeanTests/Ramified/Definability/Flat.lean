import GebLean
import GebLean.Ramified.Definability.Flat

/-!
# Tests for the destructor/case presentation and its flat realization

Executable checks over the `1 + X` word algebra `natAlgSig` for
`GebLean.Ramified.Definability.Flat`: the standard semantics `dstrCaseModel`
computes the predecessor on the destructor operation and selects the branch of
the main constructor on the case operation, and the flat realization
`dstrCaseToFlat` agrees with `dstrCaseModel` on the same values. The value
checks read out via `freeAlgToNat` so that `#guard` decides `Nat` equalities;
the agreement lemma `dstrCaseToFlat_interp` over all inputs is exercised
through an `example`.
-/

namespace GebLeanTests.Ramified.Definability.FlatTest

open GebLean.Ramified

/-- The sole destructor operation `dstr_0 : o → o` over `natAlgSig`. -/
def dstrOp : (dstrCaseSig natAlgSig RType.IsObj).Op := Sum.inl ⟨0, by decide⟩

/-- The case operation `case^o : o, o, o → o` at the base object sort `o`. -/
def caseOp : (dstrCaseSig natAlgSig RType.IsObj).Op := Sum.inr oObj

/-- The environment at the case operation's context `[o, o, o]`: the recurrence
argument `z` first, then the two branches `y₀`, `y₁`. -/
def caseArgs (z y0 y1 : FreeAlg natAlgSig) :
    ∀ i : Fin ((dstrCaseSig natAlgSig RType.IsObj).arity caseOp).length,
      RType.interp (FreeAlg natAlgSig)
        (((dstrCaseSig natAlgSig RType.IsObj).arity caseOp).get i) :=
  Fin.cons z (Fin.cons y0 (Fin.cons y1 finZeroElim))

-- The destructor is the predecessor: `dstr_0 0 = 0`, `dstr_0 3 = 2`.
#guard freeAlgToNat (dstrCaseModel dstrOp (dstrEnv (natToFreeAlg 0))) = 0
#guard freeAlgToNat (dstrCaseModel dstrOp (dstrEnv (natToFreeAlg 3))) = 2

-- The case operation selects the branch of the main constructor: at the
-- nullary constructor `0` it returns `y₀ = 7`, at the unary constructor
-- `succ 0` it returns `y₁ = 9`.
#guard freeAlgToNat
  (dstrCaseModel caseOp (caseArgs (natToFreeAlg 0) (natToFreeAlg 7) (natToFreeAlg 9))) = 7
#guard freeAlgToNat
  (dstrCaseModel caseOp (caseArgs (natToFreeAlg 1) (natToFreeAlg 7) (natToFreeAlg 9))) = 9

-- The flat realization agrees with the standard semantics on the same values.
#guard freeAlgToNat ((dstrCaseToFlat dstrOp).interp (dstrEnv (natToFreeAlg 0)))
  = freeAlgToNat (dstrCaseModel dstrOp (dstrEnv (natToFreeAlg 0)))
#guard freeAlgToNat ((dstrCaseToFlat dstrOp).interp (dstrEnv (natToFreeAlg 3)))
  = freeAlgToNat (dstrCaseModel dstrOp (dstrEnv (natToFreeAlg 3)))
#guard freeAlgToNat
    ((dstrCaseToFlat caseOp).interp (caseArgs (natToFreeAlg 0) (natToFreeAlg 7) (natToFreeAlg 9)))
  = freeAlgToNat
    (dstrCaseModel caseOp (caseArgs (natToFreeAlg 0) (natToFreeAlg 7) (natToFreeAlg 9)))
#guard freeAlgToNat
    ((dstrCaseToFlat caseOp).interp (caseArgs (natToFreeAlg 1) (natToFreeAlg 7) (natToFreeAlg 9)))
  = freeAlgToNat
    (dstrCaseModel caseOp (caseArgs (natToFreeAlg 1) (natToFreeAlg 7) (natToFreeAlg 9)))

-- The flat realization denotes the standard semantics over all operations and
-- environments.
example (op : (dstrCaseSig natAlgSig RType.IsObj).Op)
    (args : ∀ i : Fin ((dstrCaseSig natAlgSig RType.IsObj).arity op).length,
      RType.interp (FreeAlg natAlgSig)
        (((dstrCaseSig natAlgSig RType.IsObj).arity op).get i)) :
    (dstrCaseToFlat op).interp args = dstrCaseModel op args :=
  dstrCaseToFlat_interp op args

end GebLeanTests.Ramified.Definability.FlatTest
