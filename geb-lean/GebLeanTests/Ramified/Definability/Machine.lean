import GebLean
import GebLean.Ramified.Definability.Machine

/-!
# Tests for the machine-state simulation of the zero-test URM

Executable checks over the `1 + X` word algebra `natAlgSig` for
`GebLean.Ramified.Definability.Machine`: the simultaneous family `urmSteps`
tracks the state of `URMState.runFor` for two small zero-test URM programs. The
two-instruction program `[inc 0, stop]` exercises the increment and the stop
self-loop; the one-instruction program `[inc 0]` exercises the implicit-halt
state and the `chooseIdent` fall-through — after one step the program counter
leaves the instruction range and the state freezes. The value checks read out
via `freeAlgToNat` so that `#guard` decides `Nat` equalities against the
reference `URMState.runFor`.
-/

namespace GebLeanTests.Ramified.Definability.MachineTest

open GebLean.Ramified
open GebLean.ZeroTestURM

/-- The two-instruction program `[inc 0, stop]` on one register and no inputs:
the register is incremented, then the machine halts. -/
def progIncStop : URMProgram 0 where
  numRegs := 1
  instrs := #[URMInstr.inc 0, URMInstr.stop]
  outputReg := 0
  inputRegs := finZeroElim
  inputRegs_inj := fun a _ _ => a.elim0
  outputReg_not_input := fun i => i.elim0

/-- The one-instruction program `[inc 0]` on one register and no inputs: after
one step the program counter reaches `1`, past the single instruction, and the
machine freezes at the implicit-halt state. -/
def progIncOnly : URMProgram 0 where
  numRegs := 1
  instrs := #[URMInstr.inc 0]
  outputReg := 0
  inputRegs := finZeroElim
  inputRegs_inj := fun a _ _ => a.elim0
  outputReg_not_input := fun i => i.elim0

-- The register component of `[inc 0, stop]` matches `runFor`'s register at
-- counts `0, 1, 2` (values `0, 1, 1`); the pc component freezes at the stop
-- instruction (`0, 1, 1`).
#guard freeAlgToNat (simulSol [] RType.o (urmSteps progIncStop)
    (urmParamEnv finZeroElim) 0 ⟨1, by decide⟩)
  = (URMState.runFor progIncStop (URMState.init progIncStop finZeroElim) 0).regs ⟨0, by decide⟩
#guard freeAlgToNat (simulSol [] RType.o (urmSteps progIncStop)
    (urmParamEnv finZeroElim) 1 ⟨1, by decide⟩)
  = (URMState.runFor progIncStop (URMState.init progIncStop finZeroElim) 1).regs ⟨0, by decide⟩
#guard freeAlgToNat (simulSol [] RType.o (urmSteps progIncStop)
    (urmParamEnv finZeroElim) 2 ⟨1, by decide⟩)
  = (URMState.runFor progIncStop (URMState.init progIncStop finZeroElim) 2).regs ⟨0, by decide⟩
#guard freeAlgToNat (simulSol [] RType.o (urmSteps progIncStop)
    (urmParamEnv finZeroElim) 2 ⟨0, by decide⟩)
  = (URMState.runFor progIncStop (URMState.init progIncStop finZeroElim) 2).pc

-- The implicit-halt fixture `[inc 0]`: after one step the pc leaves the
-- instruction range and the register component freezes; at counts `1, 2, 3`
-- the register is `1`. This exercises the identity arm and the `chooseIdent`
-- fall-through.
#guard freeAlgToNat (simulSol [] RType.o (urmSteps progIncOnly)
    (urmParamEnv finZeroElim) 1 ⟨1, by decide⟩) = 1
#guard freeAlgToNat (simulSol [] RType.o (urmSteps progIncOnly)
    (urmParamEnv finZeroElim) 2 ⟨1, by decide⟩) = 1
#guard freeAlgToNat (simulSol [] RType.o (urmSteps progIncOnly)
    (urmParamEnv finZeroElim) 3 ⟨1, by decide⟩) = 1
#guard freeAlgToNat (simulSol [] RType.o (urmSteps progIncOnly)
    (urmParamEnv finZeroElim) 1 ⟨1, by decide⟩)
  = (URMState.runFor progIncOnly (URMState.init progIncOnly finZeroElim) 1).regs ⟨0, by decide⟩
#guard freeAlgToNat (simulSol [] RType.o (urmSteps progIncOnly)
    (urmParamEnv finZeroElim) 3 ⟨1, by decide⟩)
  = (URMState.runFor progIncOnly (URMState.init progIncOnly finZeroElim) 3).regs ⟨0, by decide⟩

-- The simulation invariant `urm_simul_interp` holds at every step count `t`: the
-- program-counter and register components track `URMState.runFor` symbolically,
-- not only at the numeral counts the `#guard` fixtures decide.
example (t : ℕ) :
    freeAlgToNat ((sttIdent progIncOnly).interp (urmEnv progIncOnly finZeroElim t))
        = (URMState.runFor progIncOnly (URMState.init progIncOnly finZeroElim) t).pc
      ∧ ∀ r : Fin progIncOnly.numRegs,
        freeAlgToNat ((regIdent progIncOnly r).interp (urmEnv progIncOnly finZeroElim t))
          = (URMState.runFor progIncOnly (URMState.init progIncOnly finZeroElim) t).regs r :=
  urm_simul_interp progIncOnly finZeroElim t

-- The eq. (8) realizer for `[inc 0, stop]`. With `c = q = 1` the clock
-- `1 · 2_1(sz)` is at least `1`, past the machine's halt time, so the output
-- register stabilizes at `1`. The realizer's denotation is read off through
-- `urm_ramified_definable`; the clocked composite is never `#guard`-ed.
theorem incStop_faithful : ∀ (v : Fin 0 → ℕ) (t : ℕ),
    1 * GebLean.tower 1 (GebLean.Fin.maxOfNat 0 v) ≤ t →
    (URMState.runFor progIncStop (URMState.init progIncStop v) t).regs progIncStop.outputReg
      = 1 := by
  intro v t ht
  obtain rfl : v = finZeroElim := Subsingleton.elim _ _
  have h1 : 1 ≤ t := le_trans (by decide) ht
  obtain ⟨n, rfl⟩ : ∃ n, t = n + 1 := ⟨t - 1, by omega⟩
  rw [URMState.runFor_succ, URMState.runFor_stop progIncStop _ n (by decide) (by decide)]
  decide

/-- The full eq. (8) realizer for `[inc 0, stop]` denotes the machine's output
`1`, read through `freeAlgToNat` via `urm_ramified_definable`. -/
example :
    freeAlgToNat ((machineRealizer progIncStop 1 1).eval (machineEnv 1 finZeroElim) 0) = 1 :=
  urm_ramified_definable progIncStop (fun _ => 1) 1 1 incStop_faithful finZeroElim

end GebLeanTests.Ramified.Definability.MachineTest
