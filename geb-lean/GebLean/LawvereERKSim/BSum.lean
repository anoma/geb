import GebLean.LawvereERKSim.Atoms

/-!
# LawvereERKSim — bsum PC-layout infrastructure

Named PC-layout constants for `compileFrag_bsum` and the size-reduction
lemma the later bsum pre-stop sub-tasks consume. The PC-layout
constants reflect the inline comment block in `compileFrag_bsum`
(`Compiler.lean`): the raw instruction list is

```
prelude ++ loopTop ++ zeroSweep ++ prologue ++ fBody
  ++ accUpdate ++ epilogue
```

with lengths `13 + 2 + frag_f.numRegs + 9 * (k + 1)
+ (frag_f.instrs.size - 1) + 4 + 3`. The constants here name the
absolute PCs at which each segment begins and ends.

## Main definitions

- `bsum_topPC`, `bsum_bodyStartPC`, `bsum_zeroSweepBase`,
  `bsum_prologueBase`, `bsum_bodyPCBase`, `bsum_trBase`,
  `bsum_incIPC`, `bsum_gotoTopPC`, `bsum_exitPC`: absolute PCs of the
  segment boundaries of `compileFrag_bsum`.

## Main statements

- `bsum_exitPC_eq_size_pred`: the exit PC is one less than the size of
  the emitted instruction array.

## References

- Tourlakis 2018 `PR-complexity-topics.pdf` §0.1.0.37.
- Spec: `docs/superpowers/specs/2026-05-16-er-to-k-via-cslib-urm-design.md`
  §5.1.1.
- Sub-division plan:
  `docs/superpowers/plans/2026-05-19-step-t2-t11-bsum-prestop-subdivision.md`,
  sub-task 11e.6.a.iii-bsum.0.

## Tags

bsum, URM, PC layout, compiler
-/

namespace GebLean
namespace LawvereERKSim

open GebLean.ZeroTestURM

/-- Absolute PC of `compileFrag_bsum`'s loop-top instruction
(`.jumpZR vX exitPC bodyStartPC`). Constant across `k` and `frag_f`. -/
private def bsum_topPC : ℕ := 13

/-- Absolute PC of `compileFrag_bsum`'s body-start instruction
(`.decR vX`). Constant across `k` and `frag_f`. -/
private def bsum_bodyStartPC : ℕ := 14

/-- Absolute PC of the first instruction of the per-iteration
zero-sweep over f's reindexed register block in
`compileFrag_bsum`. Constant across `k` and `frag_f`. -/
private def bsum_zeroSweepBase : ℕ := 15

/-- Absolute PC of the first instruction of the per-iteration
prologue (`k + 1` `preservingTransfer` blocks copying outer sources
into f's input slots) in `compileFrag_bsum`. -/
private def bsum_prologueBase {k : ℕ}
    (frag_f : CompiledFragment (k + 1)) : ℕ :=
  15 + frag_f.numRegs

/-- Absolute PC of the first instruction of f's reindexed body in
`compileFrag_bsum`. -/
private def bsum_bodyPCBase {k : ℕ}
    (frag_f : CompiledFragment (k + 1)) : ℕ :=
  15 + frag_f.numRegs + 9 * (k + 1)

/-- Absolute PC of the first instruction of the accumulator-update
`transferLoop` (f-output → vAcc) in `compileFrag_bsum`. -/
private def bsum_trBase {k : ℕ}
    (frag_f : CompiledFragment (k + 1)) : ℕ :=
  bsum_bodyPCBase frag_f + (frag_f.instrs.size - 1)

/-- Absolute PC of `compileFrag_bsum`'s `.incR vI` instruction at the
end of one iteration's body. -/
private def bsum_incIPC {k : ℕ}
    (frag_f : CompiledFragment (k + 1)) : ℕ :=
  bsum_trBase frag_f + 4

/-- Absolute PC of `compileFrag_bsum`'s `goto topPC` instruction at
the end of one iteration's body. -/
private def bsum_gotoTopPC {k : ℕ}
    (frag_f : CompiledFragment (k + 1)) : ℕ :=
  bsum_trBase frag_f + 5

/-- Absolute PC of `compileFrag_bsum`'s terminating `.stopR`
instruction; equal to one less than the size of the emitted
instruction array. -/
private def bsum_exitPC {k : ℕ}
    (frag_f : CompiledFragment (k + 1)) : ℕ :=
  bsum_trBase frag_f + 6

/-- `bsum_exitPC frag_f` is one less than the size of the instruction
array of `compileFrag_bsum frag_f`. Follows from
`compileFrag_bsum_size` by arithmetic. -/
private theorem bsum_exitPC_eq_size_pred {k : ℕ}
    (frag_f : CompiledFragment (k + 1)) :
    bsum_exitPC frag_f
      = (compileFrag_bsum frag_f).instrs.size - 1 := by
  rw [compileFrag_bsum_size]
  change bsum_trBase frag_f + 6 = _
  rw [bsum_trBase, bsum_bodyPCBase]
  omega

end LawvereERKSim
end GebLean
