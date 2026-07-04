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

The O-variant presentation is exercised by a doubling function built as an
O-variant ramified monotonic recurrence (`RIdentO.mrec`) over
destructor/case-free steps, a case split and a predecessor built through the
primitive case and destructor operations of the destructor/case summand, and
the `Category` instance of `GebLean.Ramified.RMRecCatO` on a concrete
morphism.
-/

namespace GebLeanTests.Ramified.Definability.FlatTest

open GebLean.Ramified CategoryTheory

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

/-- The zero term over an O-variant definition signature. -/
def tmZeroO {n : Nat} {h : Fin n → List RType × RType} {Γ : Ctx RType} :
    Tm (defnSigO natAlgSig n h) Γ RType.o :=
  Tm.op (sig := defnSigO natAlgSig n h)
    (Sum.inl (Sum.inl (Sum.inl (Sum.inl (oObj, false))))) finZeroElim

/-- The successor of a base term over an O-variant definition signature. -/
def tmSuccO {n : Nat} {h : Fin n → List RType × RType} {Γ : Ctx RType}
    (t : Tm (defnSigO natAlgSig n h) Γ RType.o) :
    Tm (defnSigO natAlgSig n h) Γ RType.o :=
  Tm.op (sig := defnSigO natAlgSig n h)
    (Sum.inl (Sum.inl (Sum.inl (Sum.inl (oObj, true))))) (Fin.cons t finZeroElim)

/-- The O-variant explicit definition returning `0` (context `[]`). -/
def idZeroO : RIdentO natAlgSig [] RType.o :=
  RIdentO.defn ⟨0, finZeroElim, tmZeroO⟩ finZeroElim

/-- The O-variant doubling step at `succ`: `succ ∘ succ` of the recursive
result. -/
def doubleStepO : RIdentO natAlgSig [RType.o] RType.o :=
  RIdentO.defn ⟨0, finZeroElim, tmSuccO (tmSuccO (Tm.var 0))⟩ finZeroElim

/-- The doubling function as an O-variant ramified monotonic recurrence: base
`0`, step `succ ∘ succ` of the recursive result, over destructor/case-free
steps. -/
def doublingO : RIdentO natAlgSig [RType.omega RType.o] RType.o :=
  RIdentO.mrec [] RType.o
    (fun i => match i with | false => idZeroO | true => doubleStepO)

/-- A one-element environment at the doubling recurrence-argument sort `Ω o`. -/
def envDoubleO (n : Nat) :
    ∀ i : Fin [RType.omega RType.o].length,
      RType.interp (FreeAlg natAlgSig) ([RType.omega RType.o].get i) :=
  Fin.cons (natToFreeAlg n) finZeroElim

-- Doubling in the O-variant at small inputs: `double 0 = 0`, `double 1 = 2`,
-- `double 3 = 6`.
#guard freeAlgToNat (doublingO.interp (envDoubleO 0)) = 0
#guard freeAlgToNat (doublingO.interp (envDoubleO 1)) = 2
#guard freeAlgToNat (doublingO.interp (envDoubleO 3)) = 6

/-- A case split through the primitive case operation of the destructor/case
summand: the explicit definition at context `[o, o, o]` (scrutinee first, then
one branch per constructor) whose body applies `case^o` to the three
variables. -/
def caseSplitO : RIdentO natAlgSig [RType.o, RType.o, RType.o] RType.o :=
  RIdentO.defn ⟨0, finZeroElim,
    Tm.op (sig := defnSigO natAlgSig 0 finZeroElim)
      (Sum.inl (Sum.inl (Sum.inr (Sum.inr oObj))))
      (Fin.cons (Tm.var 0) (Fin.cons (Tm.var 1) (Fin.cons (Tm.var 2) finZeroElim)))⟩
    finZeroElim

/-- The environment at the case split's context `[o, o, o]`: the scrutinee `z`
and the two branches `y₀`, `y₁`. -/
def caseSplitEnv (z y0 y1 : FreeAlg natAlgSig) :
    ∀ i : Fin ([RType.o, RType.o, RType.o] : Ctx RType).length,
      RType.interp (FreeAlg natAlgSig)
        (([RType.o, RType.o, RType.o] : Ctx RType).get i) :=
  Fin.cons z (Fin.cons y0 (Fin.cons y1 finZeroElim))

-- The case split selects the branch of the scrutinee's main constructor: at
-- the nullary constructor `0` it returns `y₀ = 7`, at the unary constructor
-- `succ 0` it returns `y₁ = 9`.
#guard freeAlgToNat
  (caseSplitO.interp (caseSplitEnv (natToFreeAlg 0) (natToFreeAlg 7) (natToFreeAlg 9))) = 7
#guard freeAlgToNat
  (caseSplitO.interp (caseSplitEnv (natToFreeAlg 1) (natToFreeAlg 7) (natToFreeAlg 9))) = 9

/-- The predecessor through the primitive destructor operation: the explicit
definition at context `[o]` whose body applies `dstr_0` to the sole
variable. -/
def predO : RIdentO natAlgSig [RType.o] RType.o :=
  RIdentO.defn ⟨0, finZeroElim,
    Tm.op (sig := defnSigO natAlgSig 0 finZeroElim)
      (Sum.inl (Sum.inl (Sum.inr (Sum.inl ⟨0, by decide⟩))))
      (Fin.cons (Tm.var 0) finZeroElim)⟩
    finZeroElim

-- The primitive destructor is the predecessor: `pred 0 = 0`, `pred 3 = 2`.
#guard freeAlgToNat (predO.interp (dstrEnv (natToFreeAlg 0))) = 0
#guard freeAlgToNat (predO.interp (dstrEnv (natToFreeAlg 3))) = 2

/-- A context of the O-variant syntactic category. -/
abbrev ctxOO : RMRecCatO := [RType.o]

/-- A concrete morphism `[o] ⟶ [o]` of the O-variant syntactic category: the
successor term applied to the sole variable. -/
abbrev succMorO : (ctxOO : RMRecCatO) ⟶ ctxOO :=
  Quotient.mk _
    (Fin.cons
      (Tm.op (sig := higherOrderO.sig)
        (Sum.inl (Sum.inl (Sum.inl (Sum.inl (oObj, true)))))
        (Fin.cons (Tm.var (sig := higherOrderO.sig) 0) finZeroElim))
      finZeroElim : HomTuple higherOrderO ctxOO ctxOO)

-- The Phase 1 `Category` instance fires on the `RMRecCatO` abbreviation.
example : 𝟙 ctxOO ≫ succMorO = succMorO := Category.id_comp _
example : succMorO ≫ 𝟙 ctxOO = succMorO := Category.comp_id _

end GebLeanTests.Ramified.Definability.FlatTest
