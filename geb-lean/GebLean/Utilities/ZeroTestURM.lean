import Mathlib.Data.List.FinRange
import Mathlib.Logic.Function.Basic

/-!
# Zero-test URM kernel

An unbounded register machine (URM) with five primitive
instructions, matching Tourlakis 2018 `PR-complexity-topics.pdf`
§0.1.0.37 (pp. 15–16):

- `assign i c` (Tourlakis `V_i ← c`): write the constant
  `c` to register `i`; advance PC.
- `inc i` (Tourlakis `V_i ← V_i + 1`): increment register
  `i`; advance PC.
- `dec i` (Tourlakis `V_i ← V_i ∸ 1`): truncated decrement
  of register `i`; advance PC.
- `jumpZ i l₁ l₂` (Tourlakis
  `if V_i = 0 goto l₁ else goto l₂`): two-target
  conditional jump on register `i` being zero.
- `stop`: halt (self-loop on PC and registers).

This URM is structurally distinct from CSLib's
Shepherdson–Sturgis URM (`Cslib.Computability.URM.*`),
which uses an equality jump `J m n q` (level 2 in K^sim)
rather than a zero-test jump (level 1 in K^sim). See spec
§2.1 for the rationale.

## Main definitions

- `URMInstr`: the five-instruction inductive type,
  parameterised by a register count `r : ℕ`.
- `URMProgram`: program structure carrying instruction
  array, register count, input register assignment
  (with injectivity invariant), and output register
  (with disjoint-from-inputs invariant).
- `URMState`: machine state (PC + registers), indexed by
  the program whose registers it tracks.
- `URMState.step`: one-step transition per Tourlakis
  2018 §0.1.0.37 (p. 16). Self-loops past end of
  instruction array.
- `URMState.runFor`: step-counted iteration of `step`;
  past the halt state, self-loops.

## Main statements

- `URMState.runFor_zero`, `URMState.runFor_succ`,
  `URMState.runFor_add`: reduction lemmas for `runFor`;
  the first two are `@[simp]`.

## References

- Tourlakis 2018 §0.1.0.37 (pp. 15–16): simulation
  lemma, source of the five-instruction set and the
  initial-state convention.
- Spec §4:
  `docs/superpowers/specs/2026-05-16-er-to-k-via-cslib-urm-design.md`.

## Tags

URM, register machine, Tourlakis, zero-test
-/

namespace GebLean

namespace ZeroTestURM

/-- URM instructions matching Tourlakis 2018 §0.1.0.37
(p. 16): assign a constant, increment, truncated
decrement, two-target zero-test jump, halt.

The parameter `r : ℕ` is the register count; `Fin r`
keeps register indices in-range. -/
inductive URMInstr (r : ℕ) : Type
  /-- `assign i c` is Tourlakis's `V_i ← c`: write the
  constant `c` to register `i`; advance PC. -/
  | assign (i : Fin r) (c : ℕ) : URMInstr r
  /-- `inc i` is Tourlakis's `V_i ← V_i + 1`. -/
  | inc (i : Fin r) : URMInstr r
  /-- `dec i` is Tourlakis's `V_i ← V_i ∸ 1` (truncated
  decrement). -/
  | dec (i : Fin r) : URMInstr r
  /-- `jumpZ i l₁ l₂` is Tourlakis's
  `if V_i = 0 goto l₁ else goto l₂`. -/
  | jumpZ (i : Fin r) (l₁ l₂ : ℕ) : URMInstr r
  /-- `stop` is Tourlakis's halt instruction:
  PC and registers unchanged when executed (self-loop). -/
  | stop : URMInstr r
  deriving Repr, DecidableEq, Inhabited

/-- A URM program: instruction array plus
input/output register convention.

Per Tourlakis 2018 §0.1.0.37 (p. 15): "V_1 is the output
variable while the V_i, for i = 2, …, n+1, are input
variables." `outputReg` and `inputRegs` make this
convention explicit; the two structural invariants
`inputRegs_inj` and `outputReg_not_input` are
independent (distinct input slots map to distinct
registers; the output register is disjoint from every
input register).

PC labels range over `{0, …, instrs.size − 1}`. PC ≥
`instrs.size` is the implicit halt state (Tourlakis
p. 15: stop "continues forever 'trivially', without
changing either the V_i or the instruction number"). -/
@[ext] structure URMProgram where
  /-- Number of registers. -/
  numRegs : ℕ
  /-- Number of inputs. -/
  numInputs : ℕ
  /-- Program instructions, indexed by PC. -/
  instrs : Array (URMInstr numRegs)
  /-- The output register (Tourlakis V_1 convention). -/
  outputReg : Fin numRegs
  /-- Input register assignment: input slot `i` writes
  to register `inputRegs i`. -/
  inputRegs : Fin numInputs → Fin numRegs
  /-- Distinct input slots map to distinct registers. -/
  inputRegs_inj : Function.Injective inputRegs
  /-- The output register is disjoint from every input
  register. -/
  outputReg_not_input : ∀ i, inputRegs i ≠ outputReg

/-- Machine state during URM execution: PC and register
contents.  Indexed by the program whose registers are
being tracked (the `numRegs` field of `P` fixes the
register-vector arity). -/
@[ext]
structure URMState (P : URMProgram) where
  /-- Program counter (0-indexed; Tourlakis's I(0) = 1
  is mapped to 0 here). -/
  pc : ℕ
  /-- Register contents, indexed by `Fin P.numRegs`. -/
  regs : Fin P.numRegs → ℕ

/-- One step of URM execution.  Pattern-matches on the
instruction at the current PC and updates state per
Tourlakis 2018 §0.1.0.37 (p. 16).  Past the end of the
instruction array, `step` is the identity (matching the
stop self-loop convention). -/
def URMState.step (P : URMProgram) (s : URMState P) :
    URMState P :=
  if h : s.pc < P.instrs.size then
    match P.instrs[s.pc]'h with
    | URMInstr.assign i c =>
        { pc := s.pc + 1
          regs := Function.update s.regs i c }
    | URMInstr.inc i =>
        { pc := s.pc + 1
          regs := Function.update s.regs i (s.regs i + 1) }
    | URMInstr.dec i =>
        { pc := s.pc + 1
          regs := Function.update s.regs i (s.regs i - 1) }
    | URMInstr.jumpZ i l₁ l₂ =>
        { pc := if s.regs i = 0 then l₁ else l₂
          regs := s.regs }
    | URMInstr.stop => s
  else s

/-- Run the URM for `n` steps starting from `s`.
Constructive (no `Classical.choose`); `n` steps past
the halt state self-loop (Tourlakis p. 15).

`P` is explicit (matching spec §4.2). -/
def URMState.runFor (P : URMProgram) (s : URMState P) :
    ℕ → URMState P
  | 0 => s
  | n + 1 => URMState.runFor P (URMState.step P s) n

/-- Reduction lemma: zero-step execution returns the
initial state. -/
@[simp] theorem URMState.runFor_zero
    (P : URMProgram) (s : URMState P) :
    URMState.runFor P s 0 = s := rfl

/-- Reduction lemma: `runFor (n+1)` peels one step at
the front. -/
@[simp] theorem URMState.runFor_succ
    (P : URMProgram) (s : URMState P) (n : ℕ) :
    URMState.runFor P s (n + 1)
      = URMState.runFor P (URMState.step P s) n := rfl

/-- Step-additivity: running for `m + n` steps equals
running for `m`, then continuing `n` more from there. -/
theorem URMState.runFor_add
    (P : URMProgram) (s : URMState P) (m n : ℕ) :
    URMState.runFor P s (m + n)
      = URMState.runFor P (URMState.runFor P s m) n := by
  induction m generalizing s with
  | zero => simp only [Nat.zero_add, URMState.runFor]
  | succ m ih =>
    rw [Nat.add_right_comm m 1 n, Nat.add_one]
    change URMState.runFor P (URMState.step P s) (m + n)
      = URMState.runFor P (URMState.runFor P (URMState.step P s) m) n
    exact ih (URMState.step P s)

end ZeroTestURM

end GebLean
