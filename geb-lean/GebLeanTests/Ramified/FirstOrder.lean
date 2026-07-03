import GebLean
import GebLean.Ramified.FirstOrder

/-!
# Tests for the first-order sub-theories and the inclusion functor

Executable checks over the `1 + X` word algebra `natAlgSig` that the section
2.4(2) examples — addition `+ : o, Omega o -> o` and multiplication
`x : (Omega o)^2 -> o` — are first-order (`RIdent.FirstOrder`, both live at tower
sorts), that they can be restated as morphisms of the first-order sub-theory's
syntactic category, and that mapping those morphisms through the inclusion functor
`GebLean.Ramified.foInclusion` into the host `RMRecCat` computes the same
arithmetic. The functor's action on a morphism `Quotient.mk t` is the
`foTm`-translated tuple (checked by `rfl`), so the value checks — evaluating the
translated term at the standard model — are the interpretations through
`foInclusion`.

The denotations land in the base carrier `FreeAlg natAlgSig`; the value checks
read out via `freeAlgToNat` so that `#guard` decides `Nat` equalities. Value
checks stay on small inputs; the tower-sort membership is decided through the
`DecidablePred RType.IsTower` instance.
-/

namespace GebLeanTests.Ramified.FirstOrderTest

open GebLean.Ramified CategoryTheory

-- The tower-sort predicate decides on small tower sorts and rejects arrow sorts.
#guard decide (RType.IsTower RType.o) = true
#guard decide (RType.IsTower (RType.omega RType.o)) = true
#guard decide (RType.IsTower (RType.arrow RType.o RType.o)) = false

/-- Addition is first-order: its context `[o, Omega o]` and result `o` are tower
sorts, and its step functions stay within the tower sorts. -/
theorem ramAdd_fo : ramAdd.FirstOrder := by
  have hz : (Tm.var (sig := defnSig natAlgSig 0 finZeroElim) (Γ := [RType.o]) 0).towerSorts :=
    RType.tower_isTower 0
  have hs : (tmSucc (Tm.var 1) :
      Tm (defnSig natAlgSig 0 finZeroElim) [RType.o, RType.o] RType.o).towerSorts := by
    refine ⟨by decide, fun (e : Fin 1) => ?_⟩
    fin_cases e
    exact RType.tower_isTower 0
  refine ⟨by decide, by decide, trivial, ?_⟩
  intro e
  cases e with
  | false => exact ⟨by decide, by decide, hz, fun e => e.elim0⟩
  | true => exact ⟨by decide, by decide, hs, fun e => e.elim0⟩

/-- Multiplication is first-order: its context `[Omega o, Omega o]` and result
`o` are tower sorts, its step invokes the first-order `ramAdd` through a hole at
tower sorts, and no higher type occurs. -/
theorem ramMul_fo : ramMul.FirstOrder := by
  have hz : (tmZero :
      Tm (defnSig natAlgSig 0 finZeroElim) [RType.omega RType.o] RType.o).towerSorts :=
    ⟨by decide, fun (e : Fin 0) => e.elim0⟩
  have hs : (Tm.op (sig := defnSig natAlgSig 1 mulHoleIdx)
        (Sum.inl (Sum.inr ⟨0, by decide⟩))
        (Fin.cons (Tm.var 1) (Fin.cons (Tm.var 0) finZeroElim)) :
        Tm (defnSig natAlgSig 1 mulHoleIdx)
          [RType.omega RType.o, RType.o] RType.o).towerSorts := by
    refine ⟨by decide, fun (e : Fin 2) => ?_⟩
    fin_cases e
    · exact RType.tower_isTower 0
    · exact RType.tower_isTower 1
  refine ⟨by decide, by decide, trivial, ?_⟩
  intro e
  cases e with
  | false => exact ⟨by decide, by decide, hz, fun e => e.elim0⟩
  | true => exact ⟨by decide, by decide, hs, fun _e => ramAdd_fo⟩

/-- The addition context `[o, Omega o]`, as an object of the first-order
syntactic category. -/
abbrev foAddSrc : SynCat (firstOrderPresentation natAlgSig)
    (interpQuotRel (firstOrderPresentation natAlgSig)) := [RType.o, RType.omega RType.o]

/-- The addition result context `[o]`, as an object of the first-order syntactic
category. -/
abbrev foAddTgt : SynCat (firstOrderPresentation natAlgSig)
    (interpQuotRel (firstOrderPresentation natAlgSig)) := [RType.o]

/-- Addition restated inside the sub-theory: the morphism tuple applying the
first-order addition operation to the two variables of its context. -/
def foRamAddTuple : HomTuple (firstOrderPresentation natAlgSig)
    [RType.o, RType.omega RType.o] [RType.o] :=
  Fin.cons
    (Tm.op (sig := firstOrderSig natAlgSig)
      (Sum.inl (Sum.inr ⟨[RType.o, RType.omega RType.o], RType.o, ⟨ramAdd, ramAdd_fo⟩⟩))
      (fun k => Tm.var k))
    finZeroElim

/-- Addition as a morphism `[o, Omega o] ⟶ [o]` of the first-order syntactic
category. -/
def foRamAddMor : foAddSrc ⟶ foAddTgt := Quotient.mk _ foRamAddTuple

/-- The multiplication context `[Omega o, Omega o]`, as an object of the
first-order syntactic category. -/
abbrev foMulSrc : SynCat (firstOrderPresentation natAlgSig)
    (interpQuotRel (firstOrderPresentation natAlgSig)) :=
  [RType.omega RType.o, RType.omega RType.o]

/-- Multiplication restated inside the sub-theory: the morphism tuple applying the
first-order multiplication operation to the two variables of its context. -/
def foRamMulTuple : HomTuple (firstOrderPresentation natAlgSig)
    [RType.omega RType.o, RType.omega RType.o] [RType.o] :=
  Fin.cons
    (Tm.op (sig := firstOrderSig natAlgSig)
      (Sum.inl (Sum.inr ⟨[RType.omega RType.o, RType.omega RType.o], RType.o,
        ⟨ramMul, ramMul_fo⟩⟩))
      (fun k => Tm.var k))
    finZeroElim

/-- Multiplication as a morphism `[Omega o, Omega o] ⟶ [o]` of the first-order
syntactic category. -/
def foRamMulMor : foMulSrc ⟶ foAddTgt := Quotient.mk _ foRamMulTuple

-- The inclusion functor's action on a first-order morphism is the
-- `foTm`-translated representative tuple.
example : (foInclusion natAlgSig).map foRamAddMor
    = Quotient.mk _ (fun i => foTm natAlgSig (foRamAddTuple i)) := rfl

example : (foInclusion natAlgSig).map foRamMulMor
    = Quotient.mk _ (fun i => foTm natAlgSig (foRamMulTuple i)) := rfl

-- Addition, interpreted through `foInclusion`: `2 + 3 = 5`.
#guard freeAlgToNat ((foTm natAlgSig (foRamAddTuple 0)).eval
  (standardModel (higherOrder natAlgSig)) (addEnv (natToFreeAlg 2) (natToFreeAlg 3))) = 5

-- Multiplication, interpreted through `foInclusion`: `2 * 3 = 6`.
#guard freeAlgToNat ((foTm natAlgSig (foRamMulTuple 0)).eval
  (standardModel (higherOrder natAlgSig)) (mulEnv (natToFreeAlg 2) (natToFreeAlg 3))) = 6

-- The inclusion preserves interpretation on the nose: the translated addition
-- morphism denotes the same as the host `ramAdd`, over all inputs.
example (a b : Nat) :
    freeAlgToNat ((foTm natAlgSig (foRamAddTuple 0)).eval
        (standardModel (higherOrder natAlgSig))
        (addEnv (natToFreeAlg a) (natToFreeAlg b))) = a + b := by
  rw [show (foTm natAlgSig (foRamAddTuple 0)).eval (standardModel (higherOrder natAlgSig))
        (addEnv (natToFreeAlg a) (natToFreeAlg b))
      = (foRamAddTuple 0).eval (standardModel (firstOrderPresentation natAlgSig))
        (addEnv (natToFreeAlg a) (natToFreeAlg b))
    from foTm_eval natAlgSig (foRamAddTuple 0) _]
  exact ramAdd_interp a b

end GebLeanTests.Ramified.FirstOrderTest
