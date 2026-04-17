import Mathlib.Data.Fin.Basic
import Mathlib.Data.Nat.Basic
import GebLean.Utilities.Tower

set_option linter.dupNamespace false

/-!
# Abstract Register Machines over ℕ

A register machine has a finite set of states and a finite set of
ℕ-valued registers.  A transition function maps each
(state, register vector) to the next (state, register vector).
Iteration for a specified number of steps is `run`; basic reduction
lemmas (`run_zero`, `run_succ`) characterize its behaviour.

The `ElementaryBound` structure witnesses that a step-count function
is dominated by a tower of exponentials, identifying it as a time
bound for elementary-recursive simulation.

The blueprint is used downstream to realize arithmetic primitives on
Szudzik-encoded binary trees via register-machine simulation, where
each machine step is expressible as a constant-depth tree operation.
-/

namespace GebLean
namespace RegisterMachine

/-- Interface part of a register machine: state and register arities
together with a transition function.  Separated from the outer
`RegisterMachine` typeclass/structure pattern so the transition
function can be manipulated as a mathematical object. -/
structure RegisterMachine where
  /-- Number of control states.  `Fin numStates` enumerates them. -/
  numStates : ℕ
  /-- Number of registers.  Each register holds a `ℕ`. -/
  numRegs : ℕ
  /-- The starting state.  Execution begins here. -/
  startState : Fin numStates
  /-- Transition function mapping (state, register vector) to
  (state, register vector).  A machine is halted by mapping a state
  to itself with identity register update; there is no distinguished
  halt state in the interface. -/
  transition :
    Fin numStates → (Fin numRegs → ℕ) →
      Fin numStates × (Fin numRegs → ℕ)

/-- A configuration of a register machine: current state and
current register vector. -/
abbrev Config (M : RegisterMachine) : Type :=
  Fin M.numStates × (Fin M.numRegs → ℕ)

/-- One step of the register machine: apply the transition
function to the current configuration. -/
def step (M : RegisterMachine) (c : Config M) : Config M :=
  M.transition c.1 c.2

/-- Run the register machine for `n` steps starting from the
given configuration.  Unfolded by `Nat.rec`, so each successor
applies one `step`. -/
def runFromConfig (M : RegisterMachine) :
    Config M → ℕ → Config M
  | c, 0     => c
  | c, n + 1 => step M (runFromConfig M c n)

@[simp] theorem runFromConfig_zero
    (M : RegisterMachine) (c : Config M) :
    runFromConfig M c 0 = c := rfl

@[simp] theorem runFromConfig_succ
    (M : RegisterMachine) (c : Config M) (n : ℕ) :
    runFromConfig M c (n + 1) =
      step M (runFromConfig M c n) := rfl

/-- Run the register machine for `n` steps starting from the
initial state `M.startState` and the given register vector.
Returns the final configuration. -/
def run (M : RegisterMachine) (regs : Fin M.numRegs → ℕ)
    (n : ℕ) : Config M :=
  runFromConfig M (M.startState, regs) n

@[simp] theorem run_zero
    (M : RegisterMachine) (regs : Fin M.numRegs → ℕ) :
    run M regs 0 = (M.startState, regs) := rfl

@[simp] theorem run_succ
    (M : RegisterMachine) (regs : Fin M.numRegs → ℕ) (n : ℕ) :
    run M regs (n + 1) =
      step M (run M regs n) := rfl

/-- Running for `m + n` steps equals running for `m` steps, then
continuing `n` more from that configuration. -/
theorem runFromConfig_add
    (M : RegisterMachine) (c : Config M) (m n : ℕ) :
    runFromConfig M c (m + n) =
      runFromConfig M (runFromConfig M c m) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change runFromConfig M c (m + n + 1) =
      step M (runFromConfig M
        (runFromConfig M c m) n)
    rw [runFromConfig_succ, ih]

/-- A witness that a step-count function `f : ℕ → ℕ` is dominated
by a fixed-height tower of exponentials.  The height `k` does not
depend on the input; only the base does.  Matches the bound
Leivant 1999 Lemma 6 uses to characterize `E_3` simulations. -/
structure ElementaryBound where
  /-- The step-count function being bounded. -/
  f : ℕ → ℕ
  /-- Height of the dominating tower. -/
  height : ℕ
  /-- Constant offset added to the input before the tower. -/
  offset : ℕ
  /-- Domination: `f n ≤ tower height (n + offset)`. -/
  dominated : ∀ n : ℕ, f n ≤ tower height (n + offset)

/-- The identity tower bound: `fun n => n` is bounded by the
height-0 tower of itself. -/
def ElementaryBound.id : ElementaryBound where
  f := fun n => n
  height := 0
  offset := 0
  dominated := fun n => by simp [tower_zero]

/-- A constant-plus-linear tower bound: if `f n ≤ c + n`, then
`f` is bounded by the height-0 tower on offset `c`. -/
def ElementaryBound.ofLinear
    {f : ℕ → ℕ} {c : ℕ}
    (h : ∀ n, f n ≤ n + c) : ElementaryBound where
  f := f
  height := 0
  offset := c
  dominated := fun n => by
    simpa [tower_zero] using h n

/-- An exponential tower bound: if `f n ≤ 2 ^ (n + c)`, then `f`
is bounded by the height-1 tower on offset `c`. -/
def ElementaryBound.ofExp
    {f : ℕ → ℕ} {c : ℕ}
    (h : ∀ n, f n ≤ 2 ^ (n + c)) : ElementaryBound where
  f := f
  height := 1
  offset := c
  dominated := fun n => by
    simpa [tower_succ, tower_zero] using h n

/-- Read off the `i`-th register of the final configuration
after running for `n` steps.  Specialized form of `run`
convenient for downstream simulation agreement theorems. -/
def runReg (M : RegisterMachine)
    (regs : Fin M.numRegs → ℕ) (n : ℕ)
    (i : Fin M.numRegs) : ℕ :=
  (run M regs n).2 i

@[simp] theorem runReg_zero
    (M : RegisterMachine) (regs : Fin M.numRegs → ℕ)
    (i : Fin M.numRegs) :
    runReg M regs 0 i = regs i := rfl

@[simp] theorem runReg_succ
    (M : RegisterMachine) (regs : Fin M.numRegs → ℕ)
    (n : ℕ) (i : Fin M.numRegs) :
    runReg M regs (n + 1) i =
      (step M (run M regs n)).2 i := rfl

end RegisterMachine
end GebLean
