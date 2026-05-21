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
- `URMProgram`: arity-indexed (by `numInputs`) program
  structure carrying instruction array, register count,
  input register assignment (with injectivity
  invariant), and output register (with
  disjoint-from-inputs invariant).
- `URMState`: machine state (PC + registers), indexed by
  the program whose registers it tracks.
- `URMState.step`: one-step transition per Tourlakis
  2018 §0.1.0.37 (p. 16). Self-loops past end of
  instruction array.
- `URMState.runFor`: step-counted iteration of `step`;
  past the halt state, self-loops.
- `URMState.init`: initial state from input vector `v`
  via constructive `List.find?` lookup; PC starts at 0;
  registers default to 0 with inputs placed at
  `P.inputRegs i`.

## Main statements

- `URMState.runFor_zero`, `URMState.runFor_succ`,
  `URMState.runFor_add`: reduction lemmas for `runFor`;
  the first two are `@[simp]`.
- `URMState.runFor_halted_invariant`: past the end of
  the instruction array, `runFor` is the identity.
- `URMState.runFor_stop`: at a `stop` instruction,
  `runFor` is the identity.
- `URMProgram.WellBounded`: every `jumpZ` target in the
  program is at most `instrs.size`.
- `URMState.step_pc_le_size`: one step of a well-bounded
  program from a PC ≤ `instrs.size` keeps the PC
  ≤ `instrs.size`.
- `URMState.runFor_pc_le_size`: any step count from such
  a starting state keeps the PC ≤ `instrs.size`.

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
@[ext] structure URMProgram (numInputs : ℕ) where
  /-- Number of registers. -/
  numRegs : ℕ
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
structure URMState {a : ℕ} (P : URMProgram a) where
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
def URMState.step {a : ℕ} (P : URMProgram a) (s : URMState P) :
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
def URMState.runFor {a : ℕ} (P : URMProgram a) (s : URMState P) :
    ℕ → URMState P
  | 0 => s
  | n + 1 => URMState.runFor P (URMState.step P s) n

/-- Reduction lemma: zero-step execution returns the
initial state. -/
@[simp] theorem URMState.runFor_zero {a : ℕ}
    (P : URMProgram a) (s : URMState P) :
    URMState.runFor P s 0 = s := rfl

/-- Reduction lemma: `runFor (n+1)` peels one step at
the front. -/
@[simp] theorem URMState.runFor_succ {a : ℕ}
    (P : URMProgram a) (s : URMState P) (n : ℕ) :
    URMState.runFor P s (n + 1)
      = URMState.runFor P (URMState.step P s) n := rfl

/-- Step-additivity: running for `m + n` steps equals
running for `m`, then continuing `n` more from there. -/
theorem URMState.runFor_add {a : ℕ}
    (P : URMProgram a) (s : URMState P) (m n : ℕ) :
    URMState.runFor P s (m + n)
      = URMState.runFor P (URMState.runFor P s m) n := by
  induction m generalizing s with
  | zero => simp only [Nat.zero_add, URMState.runFor]
  | succ m ih =>
    rw [Nat.add_right_comm m 1 n, Nat.add_one]
    change URMState.runFor P (URMState.step P s) (m + n)
      = URMState.runFor P (URMState.runFor P (URMState.step P s) m) n
    exact ih (URMState.step P s)

/-- If the PC is past the end of the instruction array,
`runFor` is the identity for any step count. -/
theorem URMState.runFor_halted_invariant {a : ℕ}
    (P : URMProgram a) (s : URMState P) (n : ℕ)
    (h : s.pc ≥ P.instrs.size) :
    URMState.runFor P s n = s := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hstep : URMState.step P s = s := by
      simp only [URMState.step, dif_neg (Nat.not_lt_of_ge h)]
    rw [URMState.runFor_succ, hstep, ih]

/-- If the instruction at the current PC is `stop`,
`runFor` is the identity for any step count. -/
theorem URMState.runFor_stop {a : ℕ}
    (P : URMProgram a) (s : URMState P) (n : ℕ)
    (h_pc : s.pc < P.instrs.size)
    (h_stop : P.instrs[s.pc]'h_pc = URMInstr.stop) :
    URMState.runFor P s n = s := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hstep : URMState.step P s = s := by
      simp only [URMState.step, dif_pos h_pc, h_stop]
    rw [URMState.runFor_succ, hstep, ih]

/-- Initial state for program `P` with input vector `v`:
PC = 0; registers default to 0, with input slots `i`
placed at `P.inputRegs i`.

Uses Lean core's `List.find?` over `List.finRange
P.numInputs` (constructive search returning
`Option (Fin P.numInputs)`) rather than
`Classical.choose`, per the constructive discipline.
`P.inputRegs_inj` ensures the returned `some i` value is
unique when it exists; when `r` is not in `P.inputRegs`'
image, `find?` returns `none` and the register defaults
to 0.

The choice `pc := 0` shifts Tourlakis's 1-indexed
`I(0) = 1` to 0-indexed `I(0) = 0`.  The shift is
consistent across all later constructions. -/
def URMState.init {a : ℕ} (P : URMProgram a)
    (v : Fin a → ℕ) : URMState P where
  pc := 0
  regs := fun r =>
    match (List.finRange a).find?
        (fun i => decide (P.inputRegs i = r)) with
    | some i => v i
    | none   => 0

/-- Well-bounded URM program: every `jumpZ` in
`P.instrs` has both targets at most `P.instrs.size`.
A PC equal to `P.instrs.size` is the implicit halt
state, so this is the loosest bound that keeps execution
inside the program-plus-halt region.

The other four instructions (`assign`, `inc`, `dec`,
`stop`) advance the PC by one or self-loop; the bound on
their successor PC follows from `s.pc < P.instrs.size`
alone, so they impose no extra obligation here. -/
def URMProgram.WellBounded {a : ℕ} (P : URMProgram a) : Prop :=
  ∀ (i : ℕ) (hi : i < P.instrs.size) (r : Fin P.numRegs) (l₁ l₂ : ℕ),
    P.instrs[i]'hi = URMInstr.jumpZ r l₁ l₂ →
      l₁ ≤ P.instrs.size ∧ l₂ ≤ P.instrs.size

/-- One step of a well-bounded program from a state with
`pc ≤ instrs.size` produces a state with
`pc ≤ instrs.size`. -/
theorem URMState.step_pc_le_size {a : ℕ}
    (P : URMProgram a) (s : URMState P)
    (h_well : P.WellBounded)
    (h_pc : s.pc ≤ P.instrs.size) :
    (URMState.step P s).pc ≤ P.instrs.size := by
  by_cases hlt : s.pc < P.instrs.size
  · -- PC inside the array: case-split on the instruction.
    match hcase : P.instrs[s.pc]'hlt with
    | URMInstr.assign i c =>
      have : URMState.step P s =
          { pc := s.pc + 1
            regs := Function.update s.regs i c } := by
        simp only [URMState.step, dif_pos hlt, hcase]
      rw [this]
      change s.pc + 1 ≤ P.instrs.size
      omega
    | URMInstr.inc i =>
      have : URMState.step P s =
          { pc := s.pc + 1
            regs := Function.update s.regs i (s.regs i + 1) } := by
        simp only [URMState.step, dif_pos hlt, hcase]
      rw [this]
      change s.pc + 1 ≤ P.instrs.size
      omega
    | URMInstr.dec i =>
      have : URMState.step P s =
          { pc := s.pc + 1
            regs := Function.update s.regs i (s.regs i - 1) } := by
        simp only [URMState.step, dif_pos hlt, hcase]
      rw [this]
      change s.pc + 1 ≤ P.instrs.size
      omega
    | URMInstr.jumpZ r l₁ l₂ =>
      have hstep : URMState.step P s =
          { pc := if s.regs r = 0 then l₁ else l₂
            regs := s.regs } := by
        simp only [URMState.step, dif_pos hlt, hcase]
      have hbnd := h_well s.pc hlt r l₁ l₂ hcase
      rw [hstep]
      change (if s.regs r = 0 then l₁ else l₂) ≤ P.instrs.size
      by_cases hz : s.regs r = 0
      · simp only [hz, ↓reduceIte]; exact hbnd.1
      · simp only [hz, ↓reduceIte]; exact hbnd.2
    | URMInstr.stop =>
      have : URMState.step P s = s := by
        simp only [URMState.step, dif_pos hlt, hcase]
      rw [this]; exact h_pc
  · -- PC at or past the end: `step` is the identity.
    have : URMState.step P s = s := by
      simp only [URMState.step, dif_neg hlt]
    rw [this]; exact h_pc

/-- Any step count of a well-bounded program from a
state with `pc ≤ instrs.size` keeps the PC
≤ `instrs.size`. -/
theorem URMState.runFor_pc_le_size {a : ℕ}
    (P : URMProgram a) (s : URMState P)
    (h_well : P.WellBounded)
    (h_pc : s.pc ≤ P.instrs.size) (n : ℕ) :
    (URMState.runFor P s n).pc ≤ P.instrs.size := by
  induction n generalizing s with
  | zero => exact h_pc
  | succ n ih =>
    rw [URMState.runFor_succ]
    exact ih (URMState.step P s)
      (URMState.step_pc_le_size P s h_well h_pc)

end ZeroTestURM

end GebLean
