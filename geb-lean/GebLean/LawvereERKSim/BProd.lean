import GebLean.LawvereERKSim.BSum

/-!
# LawvereERKSim — bprod PC-layout infrastructure

Named PC-layout constants for `compileFrag_bprod` and the size-reduction
lemma the later bprod pre-stop sub-tasks consume. Mirrors `BSum.lean`'s
PC-layout infrastructure block for `compileFrag_bsum`; differences come
from the multiplicative accumulator update (Tourlakis 2018 p. 19's
R^XY_Z template, 21 instructions vs bsum's 4) and the additional
`incR vAcc` prelude step that initialises the multiplicative
accumulator to 1.

The raw instruction list of `compileFrag_bprod` is:

```
prelude ++ loopTop ++ zeroSweep ++ prologue ++ fBody
  ++ accUpdate ++ epilogue
```

with lengths `14 + 2 + frag_f.numRegs + 9 * (k + 1)
+ (frag_f.instrs.size - 1) + 21 + 3`. The constants here name the
absolute PCs at which each segment begins and ends, and the absolute
PCs of the inner-mul loop's boundaries within the accUpdate block.

## Main definitions

- `bprod_topPC`, `bprod_bodyStartPC`, `bprod_zeroSweepBase`,
  `bprod_prologueBase`, `bprod_bodyPCBase`, `bprod_trBase`,
  `bprod_mul_innerTopPC`, `bprod_mul_innerBodyStartPC`,
  `bprod_mul_resetPC`, `bprod_incIPC`, `bprod_gotoTopPC`,
  `bprod_exitPC`: absolute PCs of the segment boundaries of
  `compileFrag_bprod`.

## Main statements

- `bprod_exitPC_eq_size_pred`: the exit PC is one less than the size
  of the emitted instruction array.
- `compileFrag_bprod_zeroSweep_correct`,
  `compileFrag_bprod_zeroSweep_pc_strict_bound`: bprod-flavoured
  aliases of `compileFrag_bsum_zeroSweep_correct` and
  `compileFrag_bsum_zeroSweep_pc_strict_bound`, with the bprod-specific
  PC base `bprod_zeroSweepBase` and reindex-shift base `k + 10` plugged
  in. The per-iteration zero-sweep of f's reindexed register block is
  structurally identical between `compileFrag_bsum` and
  `compileFrag_bprod`.

## References

- Tourlakis 2018 `PR-complexity-topics.pdf` §0.1.0.37 (URM kernel);
  pp. 19-21 R^XY_Z multiplication template.
- Spec: `docs/superpowers/specs/2026-05-16-er-to-k-via-cslib-urm-design.md`
  §5.1.1.
- Sub-division plan:
  `docs/superpowers/plans/2026-05-20-step-t2-t11-bprod-prestop-subdivision.md`,
  sub-task 11e.6.a.iii-bprod.0.

## Tags

bprod, URM, PC layout, compiler
-/

namespace GebLean
namespace LawvereERKSim

open GebLean.ZeroTestURM

/-- Absolute PC of `compileFrag_bprod`'s loop-top instruction
(`.jumpZR vX exitPC bodyStartPC`). Constant across `k` and `frag_f`. -/
private def bprod_topPC : ℕ := 14

/-- Absolute PC of `compileFrag_bprod`'s body-start instruction
(`.decR vX`). Constant across `k` and `frag_f`. -/
private def bprod_bodyStartPC : ℕ := 15

/-- Absolute PC of the first instruction of the per-iteration
zero-sweep over f's reindexed register block in
`compileFrag_bprod`. Constant across `k` and `frag_f`. -/
private def bprod_zeroSweepBase : ℕ := 16

/-- Absolute PC of the first instruction of the per-iteration
prologue (`k + 1` `preservingTransfer` blocks copying outer sources
into f's input slots) in `compileFrag_bprod`. -/
private def bprod_prologueBase {k : ℕ}
    (frag_f : CompiledFragment (k + 1)) : ℕ :=
  16 + frag_f.numRegs

/-- Absolute PC of the first instruction of f's reindexed body in
`compileFrag_bprod`. -/
private def bprod_bodyPCBase {k : ℕ}
    (frag_f : CompiledFragment (k + 1)) : ℕ :=
  16 + frag_f.numRegs + 9 * (k + 1)

/-- Absolute PC of the first instruction of the accumulator-update
block (21-instruction R^XY_Z multiplication template) in
`compileFrag_bprod`. -/
private def bprod_trBase {k : ℕ}
    (frag_f : CompiledFragment (k + 1)) : ℕ :=
  bprod_bodyPCBase frag_f + (frag_f.instrs.size - 1)

/-- Absolute PC of the inner-mul loop's top instruction
(`.jumpZR vFactor (trBase + 20) (trBase + 9)`) inside the
accumulator-update block of `compileFrag_bprod`. -/
private def bprod_mul_innerTopPC {k : ℕ}
    (frag_f : CompiledFragment (k + 1)) : ℕ :=
  bprod_trBase frag_f + 8

/-- Absolute PC of the inner-mul loop's body-start instruction
(`.decR vFactor`) inside the accumulator-update block of
`compileFrag_bprod`. -/
private def bprod_mul_innerBodyStartPC {k : ℕ}
    (frag_f : CompiledFragment (k + 1)) : ℕ :=
  bprod_trBase frag_f + 9

/-- Absolute PC of the accumulator-update block's
`.assignR vAccClone 0` reset instruction in `compileFrag_bprod`. -/
private def bprod_mul_resetPC {k : ℕ}
    (frag_f : CompiledFragment (k + 1)) : ℕ :=
  bprod_trBase frag_f + 20

/-- Absolute PC of `compileFrag_bprod`'s `.incR vI` instruction at the
end of one iteration's body. -/
private def bprod_incIPC {k : ℕ}
    (frag_f : CompiledFragment (k + 1)) : ℕ :=
  bprod_trBase frag_f + 21

/-- Absolute PC of `compileFrag_bprod`'s `goto topPC` instruction at
the end of one iteration's body. -/
private def bprod_gotoTopPC {k : ℕ}
    (frag_f : CompiledFragment (k + 1)) : ℕ :=
  bprod_trBase frag_f + 22

/-- Absolute PC of `compileFrag_bprod`'s terminating `.stopR`
instruction; equal to one less than the size of the emitted
instruction array. -/
private def bprod_exitPC {k : ℕ}
    (frag_f : CompiledFragment (k + 1)) : ℕ :=
  bprod_trBase frag_f + 23

/-- `bprod_exitPC frag_f` is one less than the size of the instruction
array of `compileFrag_bprod frag_f`. Follows from
`compileFrag_bprod_size` by arithmetic. -/
private theorem bprod_exitPC_eq_size_pred {k : ℕ}
    (frag_f : CompiledFragment (k + 1)) :
    bprod_exitPC frag_f
      = (compileFrag_bprod frag_f).instrs.size - 1 := by
  have h_size_pos : 1 ≤ frag_f.instrs.size :=
    CompiledFragment.size_pos frag_f
  rw [compileFrag_bprod_size]
  change bprod_trBase frag_f + 23 = _
  rw [bprod_trBase, bprod_bodyPCBase]
  omega

/-- Per-iteration zero-sweep correctness for `compileFrag_bprod`:
running the URM for `frag_f.numRegs` steps from a state at
`bprod_zeroSweepBase` through the contiguous block of
`assignR ((k + 10) + r) 0` instructions advances the PC to
`bprod_zeroSweepBase + frag_f.numRegs`, writes `0` to every register
`⟨(k + 10) + r, _⟩` in the swept range, and leaves all other
registers unchanged. The instruction-presence hypothesis `hSweep`
packages the in-range witness alongside the `getElem?` equation. -/
private theorem compileFrag_bprod_zeroSweep_correct
    {k : ℕ}
    (frag_f : CompiledFragment (k + 1))
    (hSweep : ∀ r : Fin frag_f.numRegs,
      ∃ h : (k + 10) + r.val
            < (compileFrag_bprod frag_f).toURMProgram.numRegs,
        (compileFrag_bprod frag_f).toURMProgram.instrs[
          bprod_zeroSweepBase + r.val]?
          = some (URMInstr.assign ⟨(k + 10) + r.val, h⟩ 0))
    (s : URMState (compileFrag_bprod frag_f).toURMProgram)
    (h_pc : s.pc = bprod_zeroSweepBase) :
    let s' := URMState.runFor _ s frag_f.numRegs
    s'.pc = bprod_zeroSweepBase + frag_f.numRegs ∧
    (∀ r : Fin frag_f.numRegs,
        ∀ h : (k + 10) + r.val
              < (compileFrag_bprod frag_f).toURMProgram.numRegs,
        s'.regs ⟨(k + 10) + r.val, h⟩ = 0) ∧
    (∀ q : Fin (compileFrag_bprod frag_f).toURMProgram.numRegs,
        (∀ r : Fin frag_f.numRegs,
          q.val ≠ (k + 10) + r.val) →
        s'.regs q = s.regs q) :=
  compileFrag_bsum_zeroSweep_correct _ bprod_zeroSweepBase (k + 10)
    frag_f.numRegs hSweep s h_pc

/-- Per-step strict PC bound for `compileFrag_bprod_zeroSweep_correct`:
during the `frag_f.numRegs` zero-sweep steps, the intermediate PC
stays strictly less than `bprod_zeroSweepBase + frag_f.numRegs`. -/
private theorem compileFrag_bprod_zeroSweep_pc_strict_bound
    {k : ℕ}
    (frag_f : CompiledFragment (k + 1))
    (hSweep : ∀ r : Fin frag_f.numRegs,
      ∃ h : (k + 10) + r.val
            < (compileFrag_bprod frag_f).toURMProgram.numRegs,
        (compileFrag_bprod frag_f).toURMProgram.instrs[
          bprod_zeroSweepBase + r.val]?
          = some (URMInstr.assign ⟨(k + 10) + r.val, h⟩ 0))
    (s : URMState (compileFrag_bprod frag_f).toURMProgram)
    (h_pc : s.pc = bprod_zeroSweepBase)
    (k' : ℕ) (h_k' : k' < frag_f.numRegs) :
    (URMState.runFor _ s k').pc
      < bprod_zeroSweepBase + frag_f.numRegs :=
  compileFrag_bsum_zeroSweep_pc_strict_bound _ bprod_zeroSweepBase
    (k + 10) frag_f.numRegs hSweep s h_pc k' h_k'

end LawvereERKSim
end GebLean
