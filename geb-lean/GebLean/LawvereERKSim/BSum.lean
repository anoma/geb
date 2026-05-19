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
array of `compileFrag_bsum frag_f`. Computes by unfolding the raw
instruction list of `compileFrag_bsum` and summing block lengths. -/
private theorem bsum_exitPC_eq_size_pred {k : ℕ}
    (frag_f : CompiledFragment (k + 1)) :
    bsum_exitPC frag_f
      = (compileFrag_bsum frag_f).instrs.size - 1 := by
  -- Replicate Compiler.lean's private `URMInstrRaw.toBoundedArray_size`
  -- locally: the array size equals the source list's length.
  have h_toBdArr_size : ∀ (r : ℕ) (l : List URMInstrRaw)
      (hb : URMInstrRaw.boundedBy r l),
      (URMInstrRaw.toBoundedArray r l hb).size = l.length := by
    intro r l hb
    change ((l.attach.map _).toArray).size = _
    rw [List.size_toArray, List.length_map, List.length_attach]
  -- The size of the bsum instruction array equals the raw list length:
  -- prelude (13) + loopTop (2) + zeroSweep (frag_f.numRegs)
  -- + prologue (9 * (k + 1)) + fBody (frag_f.instrs.size - 1)
  -- + accUpdate (4) + epilogue (3) = bsum_trBase + 7.
  have h_size : (compileFrag_bsum frag_f).instrs.size
      = bsum_trBase frag_f + 7 := by
    change ((compileFrag_bsum frag_f).instrs).size = _
    rw [show (compileFrag_bsum frag_f).instrs
        = URMInstrRaw.toBoundedArray _ _ _ from rfl,
      h_toBdArr_size]
    -- Now compute the raw-list length by `change`ing
    -- `compileFrag_bsum`'s `rawList` into the explicit
    -- `prelude ++ loopTop ++ zeroSweep ++ prologue ++ fBody
    -- ++ accUpdate ++ epilogue` form (the let-bindings inside
    -- compileFrag_bsum are reducible).
    change (([URMInstrRaw.assignR 0 0, URMInstrRaw.assignR 1 0,
        URMInstrRaw.assignR (k + 3) 0, URMInstrRaw.assignR (k + 4) 0]
          ++ URMRaw.preservingTransfer 4 2 (k + 3) (k + 6))
        ++ [URMInstrRaw.jumpZR (k + 3)
              (15 + frag_f.numRegs + 9 * (k + 1)
                + (frag_f.instrs.size - 1) + 6) 14,
            URMInstrRaw.decR (k + 3)]
        ++ bsum_zeroSweep frag_f (k + 7)
        ++ ((List.finRange (k + 1)).flatMap fun s =>
              URMRaw.preservingTransfer
                (15 + frag_f.numRegs + 9 * s.val)
                (if s.val = 0 then k + 4 else s.val + 2)
                (k + 7 + (frag_f.inputRegs s).val) (k + 5))
        ++ (frag_f.instrs.pop.toList.map fun ins =>
              URMInstrRaw.reindexShift (k + 7)
                (15 + frag_f.numRegs + 9 * (k + 1))
                (toRawOfBounded ins))
        ++ URMRaw.transferLoop
            (15 + frag_f.numRegs + 9 * (k + 1)
              + (frag_f.instrs.size - 1))
            (k + 7 + (frag_f.outputReg).val) 1
        ++ [URMInstrRaw.incR (k + 4),
            URMRaw.goto 13, URMInstrRaw.stopR]).length = _
    -- Sum up segment lengths.
    have h_prologue_block_len : ∀ s : Fin (k + 1),
        (URMRaw.preservingTransfer
            (15 + frag_f.numRegs + 9 * (s.val : ℕ))
            (if (s.val : ℕ) = 0 then k + 4 else (s.val : ℕ) + 2)
            (k + 7 + ((frag_f.inputRegs s).val : ℕ)) (k + 5)).length
          = 9 := by
      intro _
      simp only [URMRaw.preservingTransfer, URMRaw.goto,
        List.length_cons, List.length_nil]
    have h_prologue_len :
        ((List.finRange (k + 1)).flatMap fun s =>
            URMRaw.preservingTransfer
              (15 + frag_f.numRegs + 9 * (s.val : ℕ))
              (if (s.val : ℕ) = 0 then k + 4 else (s.val : ℕ) + 2)
              (k + 7 + ((frag_f.inputRegs s).val : ℕ))
              (k + 5)).length
          = 9 * (k + 1) := by
      rw [List.length_flatMap, List.map_congr_left
        (fun s _ => h_prologue_block_len s)]
      rw [List.map_const', List.length_finRange,
        List.sum_replicate_nat, Nat.mul_comm]
    -- Prelude tail uses preservingTransfer; precompute its length.
    have h_prelude_pT_len : (URMRaw.preservingTransfer 4 2 (k + 3)
        (k + 6)).length = 9 := by
      simp only [URMRaw.preservingTransfer, URMRaw.goto,
        List.length_cons, List.length_nil]
    -- accUpdate uses transferLoop; precompute its length.
    have h_accUpdate_len :
        (URMRaw.transferLoop
            (15 + frag_f.numRegs + 9 * (k + 1)
              + (frag_f.instrs.size - 1))
            (k + 7 + (frag_f.outputReg).val) 1).length = 4 := by
      simp only [URMRaw.transferLoop, URMRaw.goto,
        List.length_cons, List.length_nil]
    simp only [bsum_trBase, bsum_bodyPCBase, bsum_zeroSweep,
      List.length_append, List.length_cons, List.length_nil,
      List.length_map, List.length_finRange,
      Array.length_toList, Array.size_pop,
      h_prologue_len, h_prelude_pT_len, h_accUpdate_len]
  change bsum_trBase frag_f + 6
    = (compileFrag_bsum frag_f).instrs.size - 1
  rw [h_size]
  omega

end LawvereERKSim
end GebLean
