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

end ZeroTestURM

end GebLean
