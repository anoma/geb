import GebLean
import GebLean.Ramified.HigherOrder

/-!
# Tests for the higher-order presentation and schema identifiers

Executable checks over the `1 + X` word algebra `natAlgSig` (a nullary `zero`
and a unary `succ`). A doubling function is built as a ramified monotonic
recurrence (`RIdent.mrec`) with base `0` and step `succ ∘ succ` of the recursive
result, and its interpretation is checked at small inputs. A predecessor is
built as a flat recurrence (`RIdent.frec`) whose successor clause returns the
subterm, and its interpretation is checked. The `Category` instance of
`GebLean.Ramified.RMRecCat` is exercised on a concrete morphism.

The identifier interpretations land in the base carrier `FreeAlg natAlgSig`;
the checks convert to `Nat` via `freeAlgToNat` (`GebLean/Ramified/AlgSig.lean`)
so that `#guard` decides `Nat` equalities.
-/

namespace GebLeanTests.Ramified.HigherOrderTest

open GebLean.Ramified CategoryTheory

/-- The `1 + X` word algebra: `false` is the nullary constructor, `true` the
unary one. -/
abbrev A : AlgSig := natAlgSig

/-- The zero term over a definition signature. -/
def tmZero {n : Nat} {h : Fin n → List RType × RType} {Γ : Ctx RType} :
    Tm (defnSig A n h) Γ RType.o :=
  Tm.op (sig := defnSig A n h) (Sum.inl (Sum.inl (Sum.inl (oObj, false)))) finZeroElim

/-- The successor of a base term over a definition signature. -/
def tmSucc {n : Nat} {h : Fin n → List RType × RType} {Γ : Ctx RType}
    (t : Tm (defnSig A n h) Γ RType.o) : Tm (defnSig A n h) Γ RType.o :=
  Tm.op (sig := defnSig A n h) (Sum.inl (Sum.inl (Sum.inl (oObj, true)))) (Fin.cons t finZeroElim)

/-- The explicit definition returning `0` (context `[]`). -/
def idZero : RIdent A [] RType.o :=
  RIdent.defn ⟨0, finZeroElim, tmZero⟩ finZeroElim

/-- The doubling step at `succ`: `succ ∘ succ` of the recursive result. -/
def doubleStep : RIdent A [RType.o] RType.o :=
  RIdent.defn ⟨0, finZeroElim, tmSucc (tmSucc (Tm.var 0))⟩ finZeroElim

/-- The predecessor clause at `succ`: the subterm. -/
def predStep : RIdent A [RType.o] RType.o :=
  RIdent.defn ⟨0, finZeroElim, Tm.var 0⟩ finZeroElim

/-- The doubling function as a ramified monotonic recurrence: base `0`, step
`succ ∘ succ` of the recursive result. -/
def doubling : RIdent A [RType.omega RType.o] RType.o :=
  RIdent.mrec [] RType.o
    (fun i => match i with | false => idZero | true => doubleStep)

/-- The predecessor as a flat recurrence: `0` at `zero`, the subterm at
`succ`. -/
def pred : RIdent A [RType.o] RType.o :=
  RIdent.frec [] RType.o
    (fun i => match i with | false => idZero | true => predStep)

/-- A one-element environment at the doubling recurrence-argument sort `Ω o`. -/
def envDouble (n : Nat) :
    ∀ i : Fin [RType.omega RType.o].length,
      RType.interp (FreeAlg A) ([RType.omega RType.o].get i) :=
  Fin.cons (natToFreeAlg n) finZeroElim

/-- A one-element environment at the predecessor recurrence-argument sort `o`. -/
def envPred (n : Nat) :
    ∀ i : Fin [RType.o].length, RType.interp (FreeAlg A) ([RType.o].get i) :=
  Fin.cons (natToFreeAlg n) finZeroElim

-- Doubling at small inputs: `double 0 = 0`, `double 1 = 2`, `double 3 = 6`.
#guard freeAlgToNat (doubling.interp (envDouble 0)) = 0
#guard freeAlgToNat (doubling.interp (envDouble 1)) = 2
#guard freeAlgToNat (doubling.interp (envDouble 3)) = 6

-- Predecessor: `pred 0 = 0`, `pred 2 = 1`.
#guard freeAlgToNat (pred.interp (envPred 0)) = 0
#guard freeAlgToNat (pred.interp (envPred 2)) = 1

/-- A context of the higher-order syntactic category. -/
abbrev ctxO : RMRecCat A := [RType.o]

/-- A concrete morphism `[o] ⟶ [o]`: the successor term applied to the sole
variable. -/
abbrev succMor : (ctxO : RMRecCat A) ⟶ ctxO :=
  Quotient.mk _
    (Fin.cons
      (Tm.op (sig := (higherOrder A).sig) (Sum.inl (Sum.inl (Sum.inl (oObj, true))))
        (Fin.cons (Tm.var (sig := (higherOrder A).sig) 0) finZeroElim))
      finZeroElim : HomTuple (higherOrder A) ctxO ctxO)

-- The Phase 1 `Category` instance fires on the `RMRecCat` abbreviation.
example : 𝟙 ctxO ≫ succMor = succMor := Category.id_comp _
example : succMor ≫ 𝟙 ctxO = succMor := Category.comp_id _

/-- The application of the doubling identifier's constant to the sole variable:
a term over `(higherOrder A).sig` that partially saturates the constant (a value
at the curried sort `Ω o → o`) by the application former, at the doubling
recurrence-argument context `[Ω o]`. -/
def doublingConstApp :
    Tm (higherOrder A).sig [RType.omega RType.o] RType.o :=
  Tm.op (sig := (higherOrder A).sig)
    (Sum.inl (Sum.inl (Sum.inr (RType.omega RType.o, RType.o))))
    (Fin.cons
      (Tm.op (sig := (higherOrder A).sig)
        (Sum.inr ⟨[RType.omega RType.o], RType.o, doubling⟩) finZeroElim)
      (Fin.cons (Tm.var 0) finZeroElim))

-- Coherence at a concrete instance: the doubling constant applied via the
-- application former denotes the same value as the saturated doubling operation.
example (n : Nat) :
    (doublingConstApp).eval (standardModel (higherOrder A)) (envDouble n)
      = doubling.interp (envDouble n) := by
  simpa [doublingConstApp, doubling] using
    (RIdent.interp_eq_appChain_curryInterp doubling (envDouble n)).symm

-- The doubling constant applied via the application former: `2 * 3 = 6`.
#guard freeAlgToNat ((doublingConstApp).eval (standardModel (higherOrder A)) (envDouble 3)) = 6

-- The semantic constructor node rule (`appChain_stdConstructorInterp`) at a
-- concrete successor node: the curried `succ` constructor applied to the
-- one-element spine `[2]`, read at the base object sort, is the node
-- `succ 2 = 3`.
#guard
  freeAlgToNat
      (cast (RType.interp_isObj (FreeAlg A) (show RType.o.IsObj from Or.inl rfl))
        (appChain A (List.replicate (A.ar true) RType.o) RType.o
          (curryInterp A (List.replicate (A.ar true) RType.o) RType.o
            (stdConstructorInterp A (⟨RType.o, Or.inl rfl⟩, true)))
          (Fin.cons (natToFreeAlg 2) finZeroElim))) = 3

end GebLeanTests.Ramified.HigherOrderTest
