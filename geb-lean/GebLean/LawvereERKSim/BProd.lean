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
- `compileFrag_bprod_prologue_correct`,
  `compileFrag_bprod_prologue_pc_strict_bound`: bprod-flavoured
  aliases of `compileFrag_bsum_prologue_correct` and
  `compileFrag_bsum_prologue_pc_strict_bound`, with the bprod-specific
  PC base `bprod_prologueBase` plugged in. The per-iteration prologue
  (`k + 1` `preservingTransfer` blocks copying outer sources into f's
  input slots) is structurally identical between `compileFrag_bsum`
  and `compileFrag_bprod`.
- `compileFrag_bprod_accUpdate_prep_instr_at`: instruction-presence
  discharger producing the two `transferLoopInstrs` witnesses for the
  prep segment (PCs `bprod_trBase frag_f + 0..7`) of
  `compileFrag_bprod`'s accumulator-update block.
- `compileFrag_bprod_accUpdate_prep_correct`,
  `compileFrag_bprod_accUpdate_prep_pc_strict_bound`: correctness and
  strict per-step PC bound for the two leading `transferLoop` blocks of
  the bprod accumulator-update segment (destructive transfers `V_acc →
  V_acc_clone` and `V_f_out → V_factor`).
- `compileFrag_bprod_mul_partial_invariant`: per-iteration partial
  invariant of the inner-mul loop (PC at `bprod_mul_innerTopPC`, factor
  counted down to `vFOut - j`, accumulator equal to `vAccIn * j`, with
  the destructive accumulator clone, the multiply scratch, and `zReg`
  pinned to their fixed values).
- `compileFrag_bprod_mul_partial_base`: base case (`j = 0`) of the
  inner-mul partial invariant, obtained from
  `compileFrag_bprod_accUpdate_prep_post` plus the caller-supplied
  `zReg` witness.
- `compileFrag_bprod_accUpdate_innerBody_instr_at`:
  instruction-presence discharger for the inner-multiply body region
  (PCs `bprod_trBase frag_f + 8..19`), bundling the inner-top
  `jumpZR`, the `decR vFactor`, the nine-instruction
  `preservingTransferInstrs` block, and the return-to-top
  `URMRaw.goto`.
- `compileFrag_bprod_mul_partial_step`: per-iteration step
  (`j → j + 1`) of the inner-mul partial invariant. Advances
  `9 * vAccIn + 5` URM steps from `bprod_mul_innerTopPC` back to
  itself, decrementing `V_factor`, adding `vAccIn` into the live
  accumulator, and re-establishing the invariant at `j + 1`. The
  intermediate PC stays strictly below `bprod_mul_resetPC frag_f`
  throughout.
- `compileFrag_bprod_mul_partial_aux`: outer iteration of the
  inner-mul loop. For every `j ≤ vFOut`, exhibits a closed-form
  step count `T0 = j * (9 * vAccIn + 5)` after which the partial
  invariant holds at index `j`, and across these `T0` steps the
  intermediate PC stays strictly below `bprod_mul_resetPC frag_f`.
  Induction on `j` chaining the base case with
  `compileFrag_bprod_mul_partial_step`.
- `compileFrag_bprod_mul_partial`: specialisation of
  `compileFrag_bprod_mul_partial_aux` at `j = vFOut`, augmented
  with a preservation conjunct stating that every register other
  than the live accumulator (register `1`), the multiplicative
  factor (register `k + 8`), and the inner-multiply scratch
  (register `k + 9`) retains its pre-state value. Threaded into
  the bprod.1.c.4 accumulator-update assembly as the
  inner-multiply postcondition.
- `compileFrag_bprod_accUpdate_reset_instr_at`: instruction-presence
  discharger producing the `URMInstr.assign ⟨k + 7, _⟩ 0` witness at
  PC `bprod_mul_resetPC frag_f` (= `bprod_trBase frag_f + 20`).
- `compileFrag_bprod_accUpdate_correct`,
  `compileFrag_bprod_accUpdate_pc_strict_bound`: full multiplicative
  `R^XY_Z` correctness and per-step strict PC bound for the
  accumulator-update block of `compileFrag_bprod`. Compose the prep
  segment, the inner-multiply loop, the exit `jumpZR` (taken to
  `bprod_mul_resetPC`), and the reset `assignR` (advancing the PC to
  `bprod_incIPC`); land the live accumulator at `vAccIn * vFOut` and
  reset every scratch register touched by the block to `0`.
- `ProgramEmbedsFragment_compileFrag_bprod_fBody`: the outer program
  emitted by `compileFrag_bprod` embeds the first `frag_f.instrs.size
  - 1` instructions of `frag_f` at register offset `k + 10` and PC
  offset `16 + frag_f.numRegs + 9 * (k + 1)`. The embedded length
  drops `frag_f`'s trailing stop instruction (excluded by the
  `.pop`-emitted f-body).

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

/-- Per-iteration prologue correctness for `compileFrag_bprod`:
running the URM through `k + 1` consecutive `preservingTransfer`
blocks starting at `bprod_prologueBase frag_f` copies the outer
source registers `srcs` into the destination registers `dsts`,
advances the PC to `bprod_prologueBase frag_f + 9 * (k + 1)`, and
preserves `tmp`, `zReg`, the source registers, and all other
registers outside the destination block. Bprod-flavoured alias of
`compileFrag_bsum_prologue_correct`. -/
private theorem compileFrag_bprod_prologue_correct
    {k : ℕ}
    (frag_f : CompiledFragment (k + 1))
    (zReg tmp : Fin (compileFrag_bprod frag_f).toURMProgram.numRegs)
    (srcs dsts : Fin (k + 1) →
      Fin (compileFrag_bprod frag_f).toURMProgram.numRegs)
    (h_disj : inputCopies_disj
      (compileFrag_bprod frag_f).toURMProgram zReg tmp srcs dsts)
    (H : ∀ j : Fin (k + 1),
      preservingTransferInstrs
        (compileFrag_bprod frag_f).toURMProgram
        (bprod_prologueBase frag_f + 9 * j.val)
        (srcs j) (dsts j) tmp zReg)
    (v : Fin (k + 1) → ℕ)
    (s : URMState (compileFrag_bprod frag_f).toURMProgram)
    (h_pc : s.pc = bprod_prologueBase frag_f)
    (h_z : s.regs zReg = 0) (h_tmp0 : s.regs tmp = 0)
    (h_srcs : ∀ j : Fin (k + 1), s.regs (srcs j) = v j)
    (h_dsts0 : ∀ j : Fin (k + 1), s.regs (dsts j) = 0) :
    let totalSteps : ℕ := 9 * vPrefixSum v (k + 1) + 2 * (k + 1)
    let s' := URMState.runFor _ s totalSteps
    s'.pc = bprod_prologueBase frag_f + 9 * (k + 1) ∧
    s'.regs zReg = 0 ∧
    s'.regs tmp = 0 ∧
    (∀ j : Fin (k + 1), s'.regs (dsts j) = v j) ∧
    (∀ j : Fin (k + 1), s'.regs (srcs j) = v j) ∧
    (∀ r : Fin _,
        (∀ j : Fin (k + 1), r ≠ dsts j) → r ≠ tmp →
        s'.regs r = s.regs r) :=
  compileFrag_bsum_prologue_correct _ (bprod_prologueBase frag_f)
    zReg tmp srcs dsts h_disj H v s h_pc h_z h_tmp0 h_srcs h_dsts0

/-- Per-step strict PC bound for `compileFrag_bprod_prologue_correct`:
during the `9 * vPrefixSum v (k + 1) + 2 * (k + 1)` prologue steps,
the intermediate PC stays strictly less than
`bprod_prologueBase frag_f + 9 * (k + 1)`. Bprod-flavoured alias of
`compileFrag_bsum_prologue_pc_strict_bound`. -/
private theorem compileFrag_bprod_prologue_pc_strict_bound
    {k : ℕ}
    (frag_f : CompiledFragment (k + 1))
    (zReg tmp : Fin (compileFrag_bprod frag_f).toURMProgram.numRegs)
    (srcs dsts : Fin (k + 1) →
      Fin (compileFrag_bprod frag_f).toURMProgram.numRegs)
    (h_disj : inputCopies_disj
      (compileFrag_bprod frag_f).toURMProgram zReg tmp srcs dsts)
    (H : ∀ j : Fin (k + 1),
      preservingTransferInstrs
        (compileFrag_bprod frag_f).toURMProgram
        (bprod_prologueBase frag_f + 9 * j.val)
        (srcs j) (dsts j) tmp zReg)
    (v : Fin (k + 1) → ℕ)
    (s : URMState (compileFrag_bprod frag_f).toURMProgram)
    (h_pc : s.pc = bprod_prologueBase frag_f)
    (h_z : s.regs zReg = 0) (h_tmp0 : s.regs tmp = 0)
    (h_srcs : ∀ j : Fin (k + 1), s.regs (srcs j) = v j)
    (h_dsts0 : ∀ j : Fin (k + 1), s.regs (dsts j) = 0)
    (k' : ℕ) (h_k' : k' < 9 * vPrefixSum v (k + 1) + 2 * (k + 1)) :
    (URMState.runFor _ s k').pc
      < bprod_prologueBase frag_f + 9 * (k + 1) :=
  compileFrag_bsum_prologue_pc_strict_bound _ (bprod_prologueBase frag_f)
    zReg tmp srcs dsts h_disj H v s h_pc h_z h_tmp0 h_srcs h_dsts0 k' h_k'

/-- Instruction-presence discharger for the two `transferLoop` blocks of
`compileFrag_bprod`'s accumulator-update prep segment (PCs
`bprod_trBase frag_f + 0..7`). The first 4-instruction block is the
destructive transfer `V_acc → V_acc_clone` (with reserved zero register
`V_z`); the second 4-instruction block is the destructive transfer
`V_f_out → V_factor` (with the same reserved zero). Both witnesses are
bundled into a single helper because they share the segment-peeling
arithmetic; the bound witnesses on `Fin (compileFrag_bprod
frag_f).toURMProgram.numRegs` are returned so callers can construct
`Fin`-handles for `transferLoop_correct`. -/
private theorem compileFrag_bprod_accUpdate_prep_instr_at
    {k : ℕ}
    (frag_f : CompiledFragment (k + 1)) :
    let outer := (compileFrag_bprod frag_f).toURMProgram
    ∃ (h_acc : (1 : ℕ) < outer.numRegs)
      (h_accClone : k + 7 < outer.numRegs)
      (h_z : (0 : ℕ) < outer.numRegs)
      (h_fOut : (k + 10) + frag_f.outputReg.val < outer.numRegs)
      (h_factor : k + 8 < outer.numRegs),
      transferLoopInstrs outer (bprod_trBase frag_f)
          ⟨1, h_acc⟩
          ⟨k + 7, h_accClone⟩
          ⟨0, h_z⟩
        ∧ transferLoopInstrs outer (bprod_trBase frag_f + 4)
            ⟨(k + 10) + frag_f.outputReg.val, h_fOut⟩
            ⟨k + 8, h_factor⟩
            ⟨0, h_z⟩ := by
  intro outer
  -- Abbreviations matching the constructor of `compileFrag_bprod`.
  let vAcc : ℕ := 1
  let vBoundIn : ℕ := 2
  let vX : ℕ := k + 3
  let vI : ℕ := k + 4
  let tmp1 : ℕ := k + 5
  let tmp2 : ℕ := k + 6
  let vAccClone : ℕ := k + 7
  let vFactor : ℕ := k + 8
  let vMulTmp : ℕ := k + 9
  let fBase : ℕ := k + 10
  let nR : ℕ := fBase + frag_f.numRegs
  let topPC : ℕ := 14
  let bodyStartPC : ℕ := 15
  let prologueBase : ℕ := 16 + frag_f.numRegs
  let bodyPCBase : ℕ := 16 + frag_f.numRegs + 9 * (k + 1)
  let fBodyLen : ℕ := frag_f.instrs.size - 1
  let trBase : ℕ := bodyPCBase + fBodyLen
  let exitPC : ℕ := trBase + 23
  let prelude : List URMInstrRaw :=
    [ .assignR 0 0,
      .assignR vAcc 0,
      .assignR vX 0,
      .assignR vI 0 ]
        ++ URMRaw.preservingTransfer 4 vBoundIn vX tmp2
        ++ [ .incR vAcc ]
  let loopTop : List URMInstrRaw :=
    [ .jumpZR vX exitPC bodyStartPC,
      .decR vX ]
  let zeroSweep : List URMInstrRaw :=
    bsum_zeroSweep frag_f fBase
  let prologue : List URMInstrRaw :=
    (List.finRange (k + 1)).flatMap fun s =>
      bsum_prologueBlock frag_f fBase tmp1 prologueBase s
  let fBody : List URMInstrRaw :=
    frag_f.instrs.pop.toList.map fun ins =>
      URMInstrRaw.reindexShift fBase bodyPCBase (toRawOfBounded ins)
  let accUpdate : List URMInstrRaw :=
    URMRaw.transferLoop trBase vAcc vAccClone
      ++ URMRaw.transferLoop (trBase + 4)
          (fBase + frag_f.outputReg.val) vFactor
      ++ [ .jumpZR vFactor (trBase + 20) (trBase + 9),
           .decR vFactor ]
      ++ URMRaw.preservingTransfer (trBase + 10)
          vAccClone vAcc vMulTmp
      ++ [ URMRaw.goto (trBase + 8),
           .assignR vAccClone 0 ]
  let epilogue : List URMInstrRaw :=
    [ .incR vI, URMRaw.goto topPC, .stopR ]
  let rawList : List URMInstrRaw :=
    prelude ++ loopTop ++ zeroSweep ++ prologue ++ fBody
      ++ accUpdate ++ epilogue
  -- Segment lengths.
  have h_prelude_len : prelude.length = 14 := by
    change ([URMInstrRaw.assignR 0 0, URMInstrRaw.assignR vAcc 0,
        URMInstrRaw.assignR vX 0, URMInstrRaw.assignR vI 0]
        ++ URMRaw.preservingTransfer 4 vBoundIn vX tmp2
        ++ [URMInstrRaw.incR vAcc]).length = 14
    simp only [List.length_append, List.length_cons, List.length_nil,
      URMRaw.preservingTransfer, URMRaw.goto]
  have h_loopTop_len : loopTop.length = 2 := by
    change ([URMInstrRaw.jumpZR vX exitPC bodyStartPC,
      URMInstrRaw.decR vX] : List URMInstrRaw).length = 2
    simp only [List.length_cons, List.length_nil]
  have h_zeroSweep_len : zeroSweep.length = frag_f.numRegs := by
    change ((List.finRange frag_f.numRegs).map _).length = _
    rw [List.length_map, List.length_finRange]
  have h_prologue_len : prologue.length = 9 * (k + 1) := by
    change ((List.finRange (k + 1)).flatMap fun s =>
        bsum_prologueBlock frag_f fBase tmp1 prologueBase s).length
        = 9 * (k + 1)
    have h_each : ∀ s : Fin (k + 1),
        (bsum_prologueBlock frag_f fBase tmp1 prologueBase s).length = 9 :=
      fun _ => rfl
    have h_aux : ∀ (l : List (Fin (k + 1))),
        (l.flatMap fun s =>
            bsum_prologueBlock frag_f fBase tmp1 prologueBase s).length
          = 9 * l.length := by
      intro l
      induction l with
      | nil => rfl
      | cons hd tl ih_in =>
        rw [List.flatMap_cons, List.length_append, ih_in, h_each hd,
          List.length_cons]
        omega
    rw [h_aux, List.length_finRange]
  have h_fBody_len : fBody.length = frag_f.instrs.size - 1 := by
    change (frag_f.instrs.pop.toList.map fun ins =>
        URMInstrRaw.reindexShift fBase bodyPCBase
          (toRawOfBounded ins)).length = _
    rw [List.length_map, Array.length_toList, Array.size_pop]
  have h_accUpdate_len : accUpdate.length = 21 := by
    change (URMRaw.transferLoop trBase vAcc vAccClone
        ++ URMRaw.transferLoop (trBase + 4)
            (fBase + frag_f.outputReg.val) vFactor
        ++ [URMInstrRaw.jumpZR vFactor (trBase + 20) (trBase + 9),
            URMInstrRaw.decR vFactor]
        ++ URMRaw.preservingTransfer (trBase + 10)
            vAccClone vAcc vMulTmp
        ++ [URMRaw.goto (trBase + 8),
            URMInstrRaw.assignR vAccClone 0]).length = 21
    simp only [URMRaw.transferLoop, URMRaw.preservingTransfer,
      URMRaw.goto, List.length_append, List.length_cons,
      List.length_nil]
  have h_epilogue_len : epilogue.length = 3 := by
    change ([URMInstrRaw.incR vI, URMRaw.goto topPC,
      URMInstrRaw.stopR] : List URMInstrRaw).length = 3
    simp only [List.length_cons, List.length_nil]
  -- outer.numRegs = nR.
  have h_numRegs_eq : outer.numRegs = nR := rfl
  -- Bound proofs for the named registers.
  have h_acc_lt : (1 : ℕ) < outer.numRegs := by
    rw [h_numRegs_eq]
    have : 0 < frag_f.numRegs := frag_f.numRegs_pos
    change 1 < fBase + frag_f.numRegs; omega
  have h_accClone_lt : k + 7 < outer.numRegs := by
    rw [h_numRegs_eq]
    have : 0 < frag_f.numRegs := frag_f.numRegs_pos
    change k + 7 < fBase + frag_f.numRegs; omega
  have h_z_lt : (0 : ℕ) < outer.numRegs :=
    (compileFrag_bprod frag_f).numRegs_pos
  have h_fOut_lt : (k + 10) + frag_f.outputReg.val < outer.numRegs := by
    have hO : frag_f.outputReg.val < frag_f.numRegs :=
      frag_f.outputReg.isLt
    rw [h_numRegs_eq]
    change (k + 10) + frag_f.outputReg.val < fBase + frag_f.numRegs
    omega
  have h_factor_lt : k + 8 < outer.numRegs := by
    rw [h_numRegs_eq]
    have : 0 < frag_f.numRegs := frag_f.numRegs_pos
    change k + 8 < fBase + frag_f.numRegs; omega
  refine ⟨h_acc_lt, h_accClone_lt, h_z_lt, h_fOut_lt, h_factor_lt, ?_⟩
  -- Reconstruct the boundedness witness on rawList.
  have hAcc : vAcc + 1 ≤ nR := by
    change 1 + 1 ≤ k + 10 + frag_f.numRegs
    have : 0 < frag_f.numRegs := frag_f.numRegs_pos; omega
  have hBoundIn : vBoundIn + 1 ≤ nR := by
    change 2 + 1 ≤ k + 10 + frag_f.numRegs
    have : 0 < frag_f.numRegs := frag_f.numRegs_pos; omega
  have hVX : vX + 1 ≤ nR := by
    change k + 3 + 1 ≤ k + 10 + frag_f.numRegs
    have : 0 < frag_f.numRegs := frag_f.numRegs_pos; omega
  have hVI : vI + 1 ≤ nR := by
    change k + 4 + 1 ≤ k + 10 + frag_f.numRegs
    have : 0 < frag_f.numRegs := frag_f.numRegs_pos; omega
  have hTmp1 : tmp1 + 1 ≤ nR := by
    change k + 5 + 1 ≤ k + 10 + frag_f.numRegs
    have : 0 < frag_f.numRegs := frag_f.numRegs_pos; omega
  have hTmp2 : tmp2 + 1 ≤ nR := by
    change k + 6 + 1 ≤ k + 10 + frag_f.numRegs
    have : 0 < frag_f.numRegs := frag_f.numRegs_pos; omega
  have hAccClone : vAccClone + 1 ≤ nR := by
    change k + 7 + 1 ≤ k + 10 + frag_f.numRegs
    have : 0 < frag_f.numRegs := frag_f.numRegs_pos; omega
  have hFactor : vFactor + 1 ≤ nR := by
    change k + 8 + 1 ≤ k + 10 + frag_f.numRegs
    have : 0 < frag_f.numRegs := frag_f.numRegs_pos; omega
  have hMulTmp : vMulTmp + 1 ≤ nR := by
    change k + 9 + 1 ≤ k + 10 + frag_f.numRegs
    have : 0 < frag_f.numRegs := frag_f.numRegs_pos; omega
  have hFOut : fBase + frag_f.outputReg.val + 1 ≤ nR := by
    have : frag_f.outputReg.val < frag_f.numRegs :=
      frag_f.outputReg.isLt
    change fBase + frag_f.outputReg.val + 1 ≤ fBase + frag_f.numRegs
    omega
  have hPrologueSrc : ∀ s : Fin (k + 1),
      bsum_prologueSrc k s + 1 ≤ nR := by
    intro s
    have hs : s.val < k + 1 := s.isLt
    simp only [bsum_prologueSrc, nR, fBase]
    split <;> omega
  have hFIn : ∀ s : Fin (k + 1),
      fBase + (frag_f.inputRegs s).val + 1 ≤ nR := by
    intro s
    have : (frag_f.inputRegs s).val < frag_f.numRegs :=
      (frag_f.inputRegs s).isLt
    change fBase + (frag_f.inputRegs s).val + 1
        ≤ fBase + frag_f.numRegs
    omega
  have hPreludeBound : URMInstrRaw.boundedBy nR prelude := by
    intro ins hmem
    simp only [prelude, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hmem
    rcases hmem with ((h | h | h | h) | hpT) | h
    · rw [h]; simp only [URMInstrRaw.regBound]; omega
    · rw [h]; simp only [URMInstrRaw.regBound]; exact hAcc
    · rw [h]; simp only [URMInstrRaw.regBound]; exact hVX
    · rw [h]; simp only [URMInstrRaw.regBound]; exact hVI
    · exact boundedBy_preservingTransfer nR _ _ _ _
        hBoundIn hVX hTmp2 ins hpT
    · rw [h]; simp only [URMInstrRaw.regBound]; exact hAcc
  have hLoopTopBound : URMInstrRaw.boundedBy nR loopTop := by
    intro ins hmem
    simp only [loopTop, List.mem_cons, List.not_mem_nil,
      or_false] at hmem
    rcases hmem with h | h <;>
      (rw [h]; simp only [URMInstrRaw.regBound]; exact hVX)
  have hZeroSweepBound : URMInstrRaw.boundedBy nR zeroSweep := by
    have hBlock : fBase + frag_f.numRegs ≤ nR := Nat.le_refl _
    exact boundedBy_bsum_zeroSweep frag_f fBase nR hBlock
  have hPrologueBound : URMInstrRaw.boundedBy nR prologue := by
    intro ins hmem
    simp only [prologue, List.mem_flatMap] at hmem
    rcases hmem with ⟨s, _, hs⟩
    exact boundedBy_bsum_prologueBlock frag_f fBase tmp1
      prologueBase nR s (hPrologueSrc s) (hFIn s) hTmp1 ins hs
  have hFBodyBound : URMInstrRaw.boundedBy nR fBody := by
    intro ins hmem
    simp only [fBody, List.mem_map] at hmem
    rcases hmem with ⟨ins', _, heq⟩
    rw [← heq]
    have hb : (toRawOfBounded ins').regBound ≤ frag_f.numRegs :=
      regBound_toRawOfBounded_le ins'
    have hr := regBound_reindexShift_le_offset_add fBase
      bodyPCBase frag_f.numRegs (toRawOfBounded ins') hb
    change _ ≤ fBase + frag_f.numRegs
    omega
  have hAccUpdateBound : URMInstrRaw.boundedBy nR accUpdate := by
    intro ins hmem
    simp only [accUpdate, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hmem
    rcases hmem with
      ((((hTr1 | hTr2) | hOuter) | hInner) | hTail)
    · exact boundedBy_transferLoop nR _ _ _
        hAcc hAccClone ins hTr1
    · exact boundedBy_transferLoop nR _ _ _
        hFOut hFactor ins hTr2
    · rcases hOuter with h | h
      · rw [h]; simp only [URMInstrRaw.regBound]; exact hFactor
      · rw [h]; simp only [URMInstrRaw.regBound]; exact hFactor
    · exact boundedBy_preservingTransfer nR _ _ _ _
        hAccClone hAcc hMulTmp ins hInner
    · rcases hTail with h | h
      · rw [h]; simp only [URMRaw.goto, URMInstrRaw.regBound]
        omega
      · rw [h]; simp only [URMInstrRaw.regBound]; exact hAccClone
  have hEpilogueBound : URMInstrRaw.boundedBy nR epilogue := by
    intro ins hmem
    simp only [epilogue, URMRaw.goto, List.mem_cons,
      List.not_mem_nil, or_false] at hmem
    rcases hmem with h | h | h
    · rw [h]; simp only [URMInstrRaw.regBound]; exact hVI
    · rw [h]; simp only [URMInstrRaw.regBound]; omega
    · rw [h]; simp only [URMInstrRaw.regBound]; omega
  have hBoundOuter : URMInstrRaw.boundedBy nR rawList := by
    intro ins hmem
    simp only [rawList, List.mem_append] at hmem
    rcases hmem with
      (((((hP | hL') | hZ) | hPr) | hF) | hA) | hE
    · exact hPreludeBound ins hP
    · exact hLoopTopBound ins hL'
    · exact hZeroSweepBound ins hZ
    · exact hPrologueBound ins hPr
    · exact hFBodyBound ins hF
    · exact hAccUpdateBound ins hA
    · exact hEpilogueBound ins hE
  -- Combined accUpdate ++ epilogue at positions 0..7 are the two
  -- transferLoop blocks; specifically:
  --   d = 0: jumpZR vAcc (trBase + 4) (trBase + 1)
  --   d = 1: decR vAcc
  --   d = 2: incR vAccClone
  --   d = 3: jumpZR 0 trBase trBase
  --   d = 4: jumpZR (fBase + outputReg.val) (trBase + 8) (trBase + 5)
  --   d = 5: decR (fBase + outputReg.val)
  --   d = 6: incR vFactor
  --   d = 7: jumpZR 0 (trBase + 4) (trBase + 4)
  -- The prefix preAc = prelude ++ loopTop ++ zeroSweep ++ prologue ++
  -- fBody has length 14 + 2 + numRegs + 9*(k+1) + (instrs.size - 1)
  -- = trBase.
  set preAc : List URMInstrRaw :=
    prelude ++ loopTop ++ zeroSweep ++ prologue ++ fBody
    with h_preAc_def
  have h_preAc_len : preAc.length = trBase := by
    rw [h_preAc_def]
    simp only [List.length_append]
    rw [h_prelude_len, h_loopTop_len, h_zeroSweep_len, h_prologue_len,
      h_fBody_len]
  -- Per-position lookup helper: rawList at PC trBase + d (for d < 8)
  -- equals the corresponding entry of accUpdate ++ epilogue.
  have h_lookup_raw : ∀ (d : ℕ) (_hd : d < 8) (h_idx_lt : trBase + d
      < rawList.length),
      rawList[trBase + d]'h_idx_lt
        = (accUpdate ++ epilogue)[d]'(by
            rw [List.length_append, h_accUpdate_len, h_epilogue_len]
            omega) := by
    intro d hd h_idx_lt
    have h_rawList_split :
        rawList = preAc ++ (accUpdate ++ epilogue) := by
      change prelude ++ loopTop ++ zeroSweep ++ prologue ++ fBody
        ++ accUpdate ++ epilogue = _
      rw [h_preAc_def]
      simp only [List.append_assoc]
    have h_pref_le : preAc.length ≤ trBase + d := by
      rw [h_preAc_len]; omega
    have h_idx_lt' :
        trBase + d < (preAc ++ (accUpdate ++ epilogue)).length := by
      simp only [List.length_append]
      rw [h_preAc_len, h_accUpdate_len, h_epilogue_len]
      omega
    have h_step1 :
        rawList[trBase + d]'h_idx_lt
          = (preAc ++ (accUpdate ++ epilogue))[trBase + d]'h_idx_lt' := by
      congr 1
    rw [h_step1, List.getElem_append_right h_pref_le]
    have h_idx_eq : trBase + d - preAc.length = d := by
      rw [h_preAc_len]; omega
    congr 1
  -- Membership for the bound witness.
  have h_ae_d_in_rawList : ∀ (d : ℕ) (_hd : d < 8),
      ((accUpdate ++ epilogue)[d]'(by
        rw [List.length_append, h_accUpdate_len, h_epilogue_len]
        omega)) ∈ rawList := by
    intro d hd
    have h_mem_ae :
        (accUpdate ++ epilogue)[d]'(by
          rw [List.length_append, h_accUpdate_len, h_epilogue_len]
          omega) ∈ accUpdate ++ epilogue :=
      List.getElem_mem _
    rcases List.mem_append.mp h_mem_ae with hA | hE
    · apply List.mem_append.mpr; left
      apply List.mem_append.mpr; right; exact hA
    · apply List.mem_append.mpr; right; exact hE
  -- Per-position outer.instrs[trBase + d]? lookup at d.
  have h_outerInstr_lookup :
      ∀ (d : ℕ) (hd : d < 8),
        outer.instrs[trBase + d]?
          = some (URMInstrRaw.toBounded nR
              ((accUpdate ++ epilogue)[d]'(by
                rw [List.length_append, h_accUpdate_len, h_epilogue_len]
                omega))
              (hBoundOuter _ (h_ae_d_in_rawList d hd))) := by
    intro d hd
    have h_idx_lt_outer : trBase + d < rawList.length := by
      have h_raw_len : rawList.length = preAc.length + 21 + 3 := by
        change (prelude ++ loopTop ++ zeroSweep ++ prologue ++ fBody
          ++ accUpdate ++ epilogue).length = preAc.length + 21 + 3
        rw [h_preAc_def]
        simp only [List.length_append]
        rw [h_accUpdate_len, h_epilogue_len]
      rw [h_raw_len, h_preAc_len]; omega
    change (URMInstrRaw.toBoundedArray nR rawList hBoundOuter)[
        trBase + d]? = _
    rw [URMInstrRaw.toBoundedArray_getElem? nR rawList hBoundOuter
        (trBase + d) h_idx_lt_outer]
    have h_raw_eq := h_lookup_raw d hd h_idx_lt_outer
    apply congrArg some
    exact URMInstrRaw.toBounded_congr nR h_raw_eq _ _
  -- Concrete entries of accUpdate ++ epilogue at d = 0..7.
  have h_ae_0 : (accUpdate ++ epilogue)[(0 : ℕ)]'(by
      rw [List.length_append, h_accUpdate_len, h_epilogue_len]; decide)
      = URMInstrRaw.jumpZR vAcc (trBase + 4) (trBase + 1) := rfl
  have h_ae_1 : (accUpdate ++ epilogue)[(1 : ℕ)]'(by
      rw [List.length_append, h_accUpdate_len, h_epilogue_len]; decide)
      = URMInstrRaw.decR vAcc := rfl
  have h_ae_2 : (accUpdate ++ epilogue)[(2 : ℕ)]'(by
      rw [List.length_append, h_accUpdate_len, h_epilogue_len]; decide)
      = URMInstrRaw.incR vAccClone := rfl
  have h_ae_3 : (accUpdate ++ epilogue)[(3 : ℕ)]'(by
      rw [List.length_append, h_accUpdate_len, h_epilogue_len]; decide)
      = URMInstrRaw.jumpZR 0 trBase trBase := rfl
  have h_ae_4 : (accUpdate ++ epilogue)[(4 : ℕ)]'(by
      rw [List.length_append, h_accUpdate_len, h_epilogue_len]; decide)
      = URMInstrRaw.jumpZR (fBase + frag_f.outputReg.val)
          (trBase + 4 + 4) (trBase + 4 + 1) := rfl
  have h_ae_5 : (accUpdate ++ epilogue)[(5 : ℕ)]'(by
      rw [List.length_append, h_accUpdate_len, h_epilogue_len]; decide)
      = URMInstrRaw.decR (fBase + frag_f.outputReg.val) := rfl
  have h_ae_6 : (accUpdate ++ epilogue)[(6 : ℕ)]'(by
      rw [List.length_append, h_accUpdate_len, h_epilogue_len]; decide)
      = URMInstrRaw.incR vFactor := rfl
  have h_ae_7 : (accUpdate ++ epilogue)[(7 : ℕ)]'(by
      rw [List.length_append, h_accUpdate_len, h_epilogue_len]; decide)
      = URMInstrRaw.jumpZR 0 (trBase + 4) (trBase + 4) := rfl
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩
  · -- transferLoopInstrs (first block).h0.
    change outer.instrs[bprod_trBase frag_f + 0]? = _
    rw [show bprod_trBase frag_f + 0 = trBase + 0 from rfl]
    have h := h_outerInstr_lookup 0 (by decide)
    rw [h]
    apply congrArg some
    exact URMInstrRaw.toBounded_congr nR h_ae_0 _ _
  · -- transferLoopInstrs (first block).h1.
    change outer.instrs[bprod_trBase frag_f + 1]? = _
    rw [show bprod_trBase frag_f + 1 = trBase + 1 from rfl]
    have h := h_outerInstr_lookup 1 (by decide)
    rw [h]
    apply congrArg some
    exact URMInstrRaw.toBounded_congr nR h_ae_1 _ _
  · -- transferLoopInstrs (first block).h2.
    change outer.instrs[bprod_trBase frag_f + 2]? = _
    rw [show bprod_trBase frag_f + 2 = trBase + 2 from rfl]
    have h := h_outerInstr_lookup 2 (by decide)
    rw [h]
    apply congrArg some
    exact URMInstrRaw.toBounded_congr nR h_ae_2 _ _
  · -- transferLoopInstrs (first block).h3.
    change outer.instrs[bprod_trBase frag_f + 3]? = _
    rw [show bprod_trBase frag_f + 3 = trBase + 3 from rfl]
    have h := h_outerInstr_lookup 3 (by decide)
    rw [h]
    apply congrArg some
    exact URMInstrRaw.toBounded_congr nR h_ae_3 _ _
  · -- transferLoopInstrs (second block).h0.
    change outer.instrs[bprod_trBase frag_f + 4 + 0]? = _
    rw [show bprod_trBase frag_f + 4 + 0 = trBase + 4 from rfl]
    have h := h_outerInstr_lookup 4 (by decide)
    rw [show trBase + 4 = trBase + 4 from rfl, h]
    apply congrArg some
    exact URMInstrRaw.toBounded_congr nR h_ae_4 _ _
  · -- transferLoopInstrs (second block).h1.
    change outer.instrs[bprod_trBase frag_f + 4 + 1]? = _
    rw [show bprod_trBase frag_f + 4 + 1 = trBase + 5 from rfl]
    have h := h_outerInstr_lookup 5 (by decide)
    rw [h]
    apply congrArg some
    exact URMInstrRaw.toBounded_congr nR h_ae_5 _ _
  · -- transferLoopInstrs (second block).h2.
    change outer.instrs[bprod_trBase frag_f + 4 + 2]? = _
    rw [show bprod_trBase frag_f + 4 + 2 = trBase + 6 from rfl]
    have h := h_outerInstr_lookup 6 (by decide)
    rw [h]
    apply congrArg some
    exact URMInstrRaw.toBounded_congr nR h_ae_6 _ _
  · -- transferLoopInstrs (second block).h3.
    change outer.instrs[bprod_trBase frag_f + 4 + 3]? = _
    rw [show bprod_trBase frag_f + 4 + 3 = trBase + 7 from rfl]
    have h := h_outerInstr_lookup 7 (by decide)
    rw [h]
    apply congrArg some
    exact URMInstrRaw.toBounded_congr nR h_ae_7 _ _

/-- Post-state of `compileFrag_bprod`'s accumulator-update prep segment:
after the two leading `transferLoop` blocks at PCs `bprod_trBase
frag_f + 0..7`, the PC sits at `bprod_mul_innerTopPC frag_f`, the
accumulator (register 1) is `0`, the destructive accumulator clone
(register `k + 7`) holds the pre-state accumulator value `vAccIn`, the
reindexed `f`-output slot is `0`, the multiplicative factor (register
`k + 8`) holds the pre-state `f`-output value `vFOut`, and the inner
multiply scratch (register `k + 9`) is `0`. Consumed by the
inner-multiply phase as its pre-condition. -/
private structure compileFrag_bprod_accUpdate_prep_post
    {k : ℕ}
    (frag_f : CompiledFragment (k + 1))
    (vAccIn vFOut : ℕ)
    (s : URMState (compileFrag_bprod frag_f).toURMProgram)
    : Prop where
  /-- PC sits at the inner-multiply loop's top instruction. -/
  pc_eq : s.pc = bprod_mul_innerTopPC frag_f
  /-- Accumulator (register 1) is consumed to `0`. -/
  acc_zero : s.regs ⟨1, by
    have : 0 < frag_f.numRegs := frag_f.numRegs_pos
    change 1 < k + 10 + frag_f.numRegs; omega⟩ = 0
  /-- The accumulator clone (register `k + 7`) holds the input
  accumulator value. -/
  acc_clone_eq : s.regs ⟨k + 7, by
    have : 0 < frag_f.numRegs := frag_f.numRegs_pos
    change k + 7 < k + 10 + frag_f.numRegs; omega⟩ = vAccIn
  /-- The reindexed `f`-output slot (register `(k + 10) +
  frag_f.outputReg.val`) is consumed to `0`. -/
  fOut_zero : s.regs ⟨(k + 10) + frag_f.outputReg.val, by
    have hO : frag_f.outputReg.val < frag_f.numRegs :=
      frag_f.outputReg.isLt
    change (k + 10) + frag_f.outputReg.val < k + 10 + frag_f.numRegs
    omega⟩ = 0
  /-- The multiplicative factor (register `k + 8`) holds the input
  `f`-output value. -/
  factor_eq : s.regs ⟨k + 8, by
    have : 0 < frag_f.numRegs := frag_f.numRegs_pos
    change k + 8 < k + 10 + frag_f.numRegs; omega⟩ = vFOut
  /-- The inner multiply scratch (register `k + 9`) is `0`. -/
  mulTmp_zero : s.regs ⟨k + 9, by
    have : 0 < frag_f.numRegs := frag_f.numRegs_pos
    change k + 9 < k + 10 + frag_f.numRegs; omega⟩ = 0

/-- Correctness of the prep segment of `compileFrag_bprod`'s
accumulator-update block: starting at `bprod_trBase frag_f` with the
pre-state register witnesses, running for `(4 * vAccIn + 1) + (4 *
vFOut + 1)` steps (the two leading `transferLoop` blocks) lands the
state in `compileFrag_bprod_accUpdate_prep_post`, and preserves every
register whose value is not one of the four named destinations
(`1`, `k + 7`, `k + 8`, `(k + 10) + frag_f.outputReg.val`). The
preservation conjunct does not exclude register `0` (which is the
shared reserved-zero `zReg` for both transferLoops and is therefore
preserved at value `0`); nor does it exclude the f-body's
non-output registers (those are preserved by both `transferLoop`s as
well, and the carry-over is delegated to the outer partial invariant
of `compileFrag_bprod` as `f_other_zero`). -/
private theorem compileFrag_bprod_accUpdate_prep_correct
    {k : ℕ}
    (frag_f : CompiledFragment (k + 1))
    (vAccIn vFOut : ℕ)
    (sPre : URMState (compileFrag_bprod frag_f).toURMProgram)
    (h_pc : sPre.pc = bprod_trBase frag_f)
    (h_zReg_zero : sPre.regs ⟨0,
        (compileFrag_bprod frag_f).numRegs_pos⟩ = 0)
    (h_acc : sPre.regs ⟨1, by
      have : 0 < frag_f.numRegs := frag_f.numRegs_pos
      change 1 < k + 10 + frag_f.numRegs; omega⟩ = vAccIn)
    (h_acc_clone_zero : sPre.regs ⟨k + 7, by
      have : 0 < frag_f.numRegs := frag_f.numRegs_pos
      change k + 7 < k + 10 + frag_f.numRegs; omega⟩ = 0)
    (h_fOut : sPre.regs ⟨(k + 10) + frag_f.outputReg.val, by
      have hO : frag_f.outputReg.val < frag_f.numRegs :=
        frag_f.outputReg.isLt
      change (k + 10) + frag_f.outputReg.val
        < k + 10 + frag_f.numRegs
      omega⟩ = vFOut)
    (h_factor_zero : sPre.regs ⟨k + 8, by
      have : 0 < frag_f.numRegs := frag_f.numRegs_pos
      change k + 8 < k + 10 + frag_f.numRegs; omega⟩ = 0)
    (h_mulTmp_zero : sPre.regs ⟨k + 9, by
      have : 0 < frag_f.numRegs := frag_f.numRegs_pos
      change k + 9 < k + 10 + frag_f.numRegs; omega⟩ = 0) :
    let totalSteps : ℕ := (4 * vAccIn + 1) + (4 * vFOut + 1)
    let s' := URMState.runFor _ sPre totalSteps
    compileFrag_bprod_accUpdate_prep_post frag_f vAccIn vFOut s' ∧
    (∀ q : Fin (compileFrag_bprod frag_f).toURMProgram.numRegs,
      q.val ≠ 1 →
      q.val ≠ k + 7 →
      q.val ≠ k + 8 →
      q.val ≠ (k + 10) + frag_f.outputReg.val →
      s'.regs q = sPre.regs q) := by
  change compileFrag_bprod_accUpdate_prep_post frag_f vAccIn vFOut
      (URMState.runFor _ sPre ((4 * vAccIn + 1) + (4 * vFOut + 1))) ∧
    (∀ q : Fin (compileFrag_bprod frag_f).toURMProgram.numRegs,
      q.val ≠ 1 →
      q.val ≠ k + 7 →
      q.val ≠ k + 8 →
      q.val ≠ (k + 10) + frag_f.outputReg.val →
      (URMState.runFor _ sPre ((4 * vAccIn + 1) + (4 * vFOut + 1))).regs q
        = sPre.regs q)
  -- Instruction-presence bundle.
  obtain ⟨h_acc_lt, h_accClone_lt, h_z_lt, h_fOut_lt, h_factor_lt,
      H1, H2⟩ :=
    compileFrag_bprod_accUpdate_prep_instr_at frag_f
  -- Fin handles for the two transferLoops.
  let accFin : Fin (compileFrag_bprod frag_f).toURMProgram.numRegs :=
    ⟨1, h_acc_lt⟩
  let accCloneFin : Fin (compileFrag_bprod frag_f).toURMProgram.numRegs :=
    ⟨k + 7, h_accClone_lt⟩
  let zFin : Fin (compileFrag_bprod frag_f).toURMProgram.numRegs :=
    ⟨0, h_z_lt⟩
  let fOutFin : Fin (compileFrag_bprod frag_f).toURMProgram.numRegs :=
    ⟨(k + 10) + frag_f.outputReg.val, h_fOut_lt⟩
  let factorFin : Fin (compileFrag_bprod frag_f).toURMProgram.numRegs :=
    ⟨k + 8, h_factor_lt⟩
  -- Disjointness for the first transferLoop (acc → accClone, zReg = 0).
  have h_disj1_sd : accFin ≠ accCloneFin := by
    intro hh
    have : (1 : ℕ) = k + 7 := congrArg Fin.val hh; omega
  have h_disj1_zs : zFin ≠ accFin := by
    intro hh
    have : (0 : ℕ) = 1 := congrArg Fin.val hh; omega
  have h_disj1_zd : zFin ≠ accCloneFin := by
    intro hh
    have : (0 : ℕ) = k + 7 := congrArg Fin.val hh; omega
  -- Disjointness for the second transferLoop (fOut → factor, zReg = 0).
  have h_disj2_sd : fOutFin ≠ factorFin := by
    intro hh
    have : ((k + 10) + frag_f.outputReg.val : ℕ) = k + 8 :=
      congrArg Fin.val hh
    omega
  have h_disj2_zs : zFin ≠ fOutFin := by
    intro hh
    have : (0 : ℕ) = (k + 10) + frag_f.outputReg.val :=
      congrArg Fin.val hh
    omega
  have h_disj2_zd : zFin ≠ factorFin := by
    intro hh
    have : (0 : ℕ) = k + 8 := congrArg Fin.val hh; omega
  -- Step A: first transferLoop over (4 * vAccIn + 1) steps.
  have h_sPre_z : sPre.regs zFin = 0 := by
    have h_eq : (⟨0, (compileFrag_bprod frag_f).numRegs_pos⟩
        : Fin (compileFrag_bprod frag_f).toURMProgram.numRegs)
        = zFin := Fin.ext rfl
    rw [← h_eq]; exact h_zReg_zero
  have h_sPre_acc : sPre.regs accFin = vAccIn := by
    have h_eq : (⟨1, by
        have : 0 < frag_f.numRegs := frag_f.numRegs_pos
        change 1 < k + 10 + frag_f.numRegs; omega⟩
        : Fin (compileFrag_bprod frag_f).toURMProgram.numRegs)
        = accFin := Fin.ext rfl
    rw [← h_eq]; exact h_acc
  have h_sPre_fOut : sPre.regs fOutFin = vFOut := by
    have h_eq : (⟨(k + 10) + frag_f.outputReg.val, by
        have hO : frag_f.outputReg.val < frag_f.numRegs :=
          frag_f.outputReg.isLt
        change (k + 10) + frag_f.outputReg.val
          < k + 10 + frag_f.numRegs
        omega⟩
        : Fin (compileFrag_bprod frag_f).toURMProgram.numRegs)
        = fOutFin := Fin.ext rfl
    rw [← h_eq]; exact h_fOut
  have h_sPre_factor : sPre.regs factorFin = 0 := by
    have h_eq : (⟨k + 8, by
        have : 0 < frag_f.numRegs := frag_f.numRegs_pos
        change k + 8 < k + 10 + frag_f.numRegs; omega⟩
        : Fin (compileFrag_bprod frag_f).toURMProgram.numRegs)
        = factorFin := Fin.ext rfl
    rw [← h_eq]; exact h_factor_zero
  have h_sPre_accClone : sPre.regs accCloneFin = 0 := by
    have h_eq : (⟨k + 7, by
        have : 0 < frag_f.numRegs := frag_f.numRegs_pos
        change k + 7 < k + 10 + frag_f.numRegs; omega⟩
        : Fin (compileFrag_bprod frag_f).toURMProgram.numRegs)
        = accCloneFin := Fin.ext rfl
    rw [← h_eq]; exact h_acc_clone_zero
  have h_sPre_pc : sPre.pc = bprod_trBase frag_f := h_pc
  obtain ⟨hA_pc, hA_dst, hA_src, hA_z, hA_oth⟩ :=
    transferLoop_correct (compileFrag_bprod frag_f).toURMProgram
      (bprod_trBase frag_f) accFin accCloneFin zFin
      h_disj1_sd h_disj1_zs h_disj1_zd H1 sPre h_sPre_pc h_sPre_z
      vAccIn h_sPre_acc
  set sMid : URMState (compileFrag_bprod frag_f).toURMProgram :=
    URMState.runFor (compileFrag_bprod frag_f).toURMProgram sPre
      (4 * vAccIn + 1)
  have hsMid_pc : sMid.pc = bprod_trBase frag_f + 4 := hA_pc
  have hsMid_acc_zero : sMid.regs accFin = 0 := hA_src
  have hsMid_z : sMid.regs zFin = 0 := hA_z
  have hsMid_accClone : sMid.regs accCloneFin = vAccIn := by
    rw [hA_dst, h_sPre_accClone]; omega
  have hsMid_oth : ∀ r, r ≠ accCloneFin → r ≠ accFin → r ≠ zFin →
      sMid.regs r = sPre.regs r := hA_oth
  -- Step B: second transferLoop over (4 * vFOut + 1) steps from sMid.
  have h_ne_fOut_accClone : fOutFin ≠ accCloneFin := by
    intro hh
    have : ((k + 10) + frag_f.outputReg.val : ℕ) = k + 7 :=
      congrArg Fin.val hh
    omega
  have h_ne_fOut_acc : fOutFin ≠ accFin := by
    intro hh
    have : ((k + 10) + frag_f.outputReg.val : ℕ) = 1 :=
      congrArg Fin.val hh
    omega
  have h_ne_factor_accClone : factorFin ≠ accCloneFin := by
    intro hh
    have : (k + 8 : ℕ) = k + 7 := congrArg Fin.val hh; omega
  have h_ne_factor_acc : factorFin ≠ accFin := by
    intro hh
    have : (k + 8 : ℕ) = 1 := congrArg Fin.val hh; omega
  have hsMid_fOut : sMid.regs fOutFin = vFOut := by
    rw [hsMid_oth fOutFin h_ne_fOut_accClone h_ne_fOut_acc h_disj2_zs.symm,
      h_sPre_fOut]
  have hsMid_factor_zero : sMid.regs factorFin = 0 := by
    rw [hsMid_oth factorFin h_ne_factor_accClone h_ne_factor_acc
        h_disj2_zd.symm, h_sPre_factor]
  obtain ⟨hB_pc, hB_dst, hB_src, hB_z, hB_oth⟩ :=
    transferLoop_correct (compileFrag_bprod frag_f).toURMProgram
      (bprod_trBase frag_f + 4) fOutFin factorFin
      zFin h_disj2_sd h_disj2_zs h_disj2_zd H2 sMid hsMid_pc hsMid_z
      vFOut hsMid_fOut
  set sFinal : URMState (compileFrag_bprod frag_f).toURMProgram :=
    URMState.runFor (compileFrag_bprod frag_f).toURMProgram sMid
      (4 * vFOut + 1)
  have hsFinal_pc : sFinal.pc = bprod_trBase frag_f + 4 + 4 := hB_pc
  have hsFinal_fOut_zero : sFinal.regs fOutFin = 0 := hB_src
  have hsFinal_z : sFinal.regs zFin = 0 := hB_z
  have hsFinal_factor : sFinal.regs factorFin = vFOut := by
    rw [hB_dst, hsMid_factor_zero]; omega
  have hsFinal_oth : ∀ r, r ≠ factorFin → r ≠ fOutFin → r ≠ zFin →
      sFinal.regs r = sMid.regs r := hB_oth
  -- Compose: s' = runFor _ sPre ((4*vAccIn+1) + (4*vFOut+1)) = sFinal.
  have h_runFor_eq :
      URMState.runFor (compileFrag_bprod frag_f).toURMProgram sPre
          ((4 * vAccIn + 1) + (4 * vFOut + 1)) = sFinal := by
    rw [URMState.runFor_add]
  change compileFrag_bprod_accUpdate_prep_post frag_f vAccIn vFOut
      (URMState.runFor (compileFrag_bprod frag_f).toURMProgram sPre
        ((4 * vAccIn + 1) + (4 * vFOut + 1))) ∧ _
  rw [h_runFor_eq]
  -- Boundedness reindexing helpers: rebind the structure-field
  -- Fin literals to match accFin, accCloneFin, fOutFin, factorFin
  -- by Fin.ext.
  have h_acc_fin_eq :
      (⟨1, by
        have : 0 < frag_f.numRegs := frag_f.numRegs_pos
        change 1 < k + 10 + frag_f.numRegs; omega⟩
        : Fin (compileFrag_bprod frag_f).toURMProgram.numRegs)
        = accFin := Fin.ext rfl
  have h_accClone_fin_eq :
      (⟨k + 7, by
        have : 0 < frag_f.numRegs := frag_f.numRegs_pos
        change k + 7 < k + 10 + frag_f.numRegs; omega⟩
        : Fin (compileFrag_bprod frag_f).toURMProgram.numRegs)
        = accCloneFin := Fin.ext rfl
  have h_fOut_fin_eq :
      (⟨(k + 10) + frag_f.outputReg.val, by
        have hO : frag_f.outputReg.val < frag_f.numRegs :=
          frag_f.outputReg.isLt
        change (k + 10) + frag_f.outputReg.val < k + 10 + frag_f.numRegs
        omega⟩ : Fin (compileFrag_bprod frag_f).toURMProgram.numRegs)
        = fOutFin := Fin.ext rfl
  have h_factor_fin_eq :
      (⟨k + 8, by
        have : 0 < frag_f.numRegs := frag_f.numRegs_pos
        change k + 8 < k + 10 + frag_f.numRegs; omega⟩
        : Fin (compileFrag_bprod frag_f).toURMProgram.numRegs)
        = factorFin := Fin.ext rfl
  -- The inner-mul scratch (k + 9) is not touched by either transferLoop;
  -- both rounds of `_oth` preserve it.
  let mulTmpFin :
      Fin (compileFrag_bprod frag_f).toURMProgram.numRegs :=
    ⟨k + 9, by
      have : 0 < frag_f.numRegs := frag_f.numRegs_pos
      change k + 9 < k + 10 + frag_f.numRegs; omega⟩
  have h_ne_mulTmp_accClone : mulTmpFin ≠ accCloneFin := by
    intro hh
    have : (k + 9 : ℕ) = k + 7 := congrArg Fin.val hh; omega
  have h_ne_mulTmp_acc : mulTmpFin ≠ accFin := by
    intro hh
    have : (k + 9 : ℕ) = 1 := congrArg Fin.val hh; omega
  have h_ne_mulTmp_z : mulTmpFin ≠ zFin := by
    intro hh
    have : (k + 9 : ℕ) = 0 := congrArg Fin.val hh; omega
  have h_ne_mulTmp_factor : mulTmpFin ≠ factorFin := by
    intro hh
    have : (k + 9 : ℕ) = k + 8 := congrArg Fin.val hh; omega
  have h_ne_mulTmp_fOut : mulTmpFin ≠ fOutFin := by
    intro hh
    have : (k + 9 : ℕ) = (k + 10) + frag_f.outputReg.val :=
      congrArg Fin.val hh
    omega
  have hsFinal_mulTmp_zero : sFinal.regs mulTmpFin = 0 := by
    rw [hsFinal_oth mulTmpFin h_ne_mulTmp_factor h_ne_mulTmp_fOut
        h_ne_mulTmp_z,
      hsMid_oth mulTmpFin h_ne_mulTmp_accClone h_ne_mulTmp_acc
        h_ne_mulTmp_z,
      h_mulTmp_zero]
  -- Also need acc_zero on sFinal: acc is preserved by second loop.
  have h_ne_acc_factor : accFin ≠ factorFin := by
    intro hh
    have : (1 : ℕ) = k + 8 := congrArg Fin.val hh; omega
  have h_ne_acc_fOut : accFin ≠ fOutFin := by
    intro hh
    have : (1 : ℕ) = (k + 10) + frag_f.outputReg.val :=
      congrArg Fin.val hh
    omega
  have h_ne_acc_z : accFin ≠ zFin := by
    intro hh
    have : (1 : ℕ) = 0 := congrArg Fin.val hh; omega
  have hsFinal_acc_zero : sFinal.regs accFin = 0 := by
    rw [hsFinal_oth accFin h_ne_acc_factor h_ne_acc_fOut h_ne_acc_z,
      hsMid_acc_zero]
  -- And accClone is preserved by second loop.
  have h_ne_accClone_factor : accCloneFin ≠ factorFin := by
    intro hh
    have : (k + 7 : ℕ) = k + 8 := congrArg Fin.val hh; omega
  have h_ne_accClone_fOut : accCloneFin ≠ fOutFin := by
    intro hh
    have : (k + 7 : ℕ) = (k + 10) + frag_f.outputReg.val :=
      congrArg Fin.val hh
    omega
  have h_ne_accClone_z : accCloneFin ≠ zFin := by
    intro hh
    have : (k + 7 : ℕ) = 0 := congrArg Fin.val hh; omega
  have hsFinal_accClone : sFinal.regs accCloneFin = vAccIn := by
    rw [hsFinal_oth accCloneFin h_ne_accClone_factor h_ne_accClone_fOut
        h_ne_accClone_z, hsMid_accClone]
  refine ⟨?_, ?_⟩
  · refine
      { pc_eq := ?_
        acc_zero := ?_
        acc_clone_eq := ?_
        fOut_zero := ?_
        factor_eq := ?_
        mulTmp_zero := ?_ }
    · -- pc_eq: sFinal.pc = bprod_mul_innerTopPC frag_f.
      rw [hsFinal_pc]
      change bprod_trBase frag_f + 4 + 4 = bprod_trBase frag_f + 8
      omega
    · -- acc_zero.
      rw [h_acc_fin_eq]; exact hsFinal_acc_zero
    · -- acc_clone_eq.
      rw [h_accClone_fin_eq]; exact hsFinal_accClone
    · -- fOut_zero.
      rw [h_fOut_fin_eq]; exact hsFinal_fOut_zero
    · -- factor_eq.
      rw [h_factor_fin_eq]; exact hsFinal_factor
    · -- mulTmp_zero.
      change sFinal.regs (⟨k + 9, by
        have : 0 < frag_f.numRegs := frag_f.numRegs_pos
        change k + 9 < k + 10 + frag_f.numRegs; omega⟩
        : Fin (compileFrag_bprod frag_f).toURMProgram.numRegs) = 0
      exact hsFinal_mulTmp_zero
  · -- Preservation of all other registers.
    intro q h_ne_1 h_ne_kp7 h_ne_kp8 h_ne_fOut
    have h_q_ne_acc : q ≠ accFin := by
      intro hh; apply h_ne_1; exact congrArg Fin.val hh
    have h_q_ne_accClone : q ≠ accCloneFin := by
      intro hh; apply h_ne_kp7; exact congrArg Fin.val hh
    have h_q_ne_factor : q ≠ factorFin := by
      intro hh; apply h_ne_kp8; exact congrArg Fin.val hh
    have h_q_ne_fOut : q ≠ fOutFin := by
      intro hh; apply h_ne_fOut; exact congrArg Fin.val hh
    by_cases h_q_z : q = zFin
    · -- Both transferLoops preserve zReg (which is zFin); transitively
      -- sFinal.regs zFin = sPre.regs zFin.
      rw [h_q_z, show sFinal.regs zFin = 0 from hsFinal_z, h_sPre_z]
    · rw [hsFinal_oth q h_q_ne_factor h_q_ne_fOut h_q_z,
        hsMid_oth q h_q_ne_accClone h_q_ne_acc h_q_z]

/-- Strict per-step PC bound for `compileFrag_bprod_accUpdate_prep_correct`:
during the `(4 * vAccIn + 1) + (4 * vFOut + 1)` prep-segment steps,
the intermediate PC stays strictly less than `bprod_mul_innerTopPC
frag_f` (= `bprod_trBase frag_f + 8`). -/
private theorem compileFrag_bprod_accUpdate_prep_pc_strict_bound
    {k : ℕ}
    (frag_f : CompiledFragment (k + 1))
    (vAccIn vFOut : ℕ)
    (sPre : URMState (compileFrag_bprod frag_f).toURMProgram)
    (h_pc : sPre.pc = bprod_trBase frag_f)
    (h_zReg_zero : sPre.regs ⟨0,
        (compileFrag_bprod frag_f).numRegs_pos⟩ = 0)
    (h_acc : sPre.regs ⟨1, by
      have : 0 < frag_f.numRegs := frag_f.numRegs_pos
      change 1 < k + 10 + frag_f.numRegs; omega⟩ = vAccIn)
    (_h_acc_clone_zero : sPre.regs ⟨k + 7, by
      have : 0 < frag_f.numRegs := frag_f.numRegs_pos
      change k + 7 < k + 10 + frag_f.numRegs; omega⟩ = 0)
    (h_fOut : sPre.regs ⟨(k + 10) + frag_f.outputReg.val, by
      have hO : frag_f.outputReg.val < frag_f.numRegs :=
        frag_f.outputReg.isLt
      change (k + 10) + frag_f.outputReg.val
        < k + 10 + frag_f.numRegs
      omega⟩ = vFOut)
    (_h_factor_zero : sPre.regs ⟨k + 8, by
      have : 0 < frag_f.numRegs := frag_f.numRegs_pos
      change k + 8 < k + 10 + frag_f.numRegs; omega⟩ = 0)
    (k' : ℕ) (h_k' : k' < (4 * vAccIn + 1) + (4 * vFOut + 1)) :
    (URMState.runFor _ sPre k').pc
      < bprod_mul_innerTopPC frag_f := by
  let P : URMProgram (k + 1) := (compileFrag_bprod frag_f).toURMProgram
  change (URMState.runFor P sPre k').pc < bprod_mul_innerTopPC frag_f
  -- Instruction-presence bundle.
  obtain ⟨h_acc_lt, h_accClone_lt, h_z_lt, h_fOut_lt, h_factor_lt,
      H1, H2⟩ :=
    compileFrag_bprod_accUpdate_prep_instr_at frag_f
  let accFin : Fin P.numRegs := ⟨1, h_acc_lt⟩
  let accCloneFin : Fin P.numRegs := ⟨k + 7, h_accClone_lt⟩
  let zFin : Fin P.numRegs := ⟨0, h_z_lt⟩
  let fOutFin : Fin P.numRegs :=
    ⟨(k + 10) + frag_f.outputReg.val, h_fOut_lt⟩
  let factorFin : Fin P.numRegs := ⟨k + 8, h_factor_lt⟩
  have h_disj1_sd : accFin ≠ accCloneFin := by
    intro hh
    have : (1 : ℕ) = k + 7 := congrArg Fin.val hh; omega
  have h_disj1_zs : zFin ≠ accFin := by
    intro hh
    have : (0 : ℕ) = 1 := congrArg Fin.val hh; omega
  have h_disj1_zd : zFin ≠ accCloneFin := by
    intro hh
    have : (0 : ℕ) = k + 7 := congrArg Fin.val hh; omega
  have h_disj2_sd : fOutFin ≠ factorFin := by
    intro hh
    have : ((k + 10) + frag_f.outputReg.val : ℕ) = k + 8 :=
      congrArg Fin.val hh
    omega
  have h_disj2_zs : zFin ≠ fOutFin := by
    intro hh
    have : (0 : ℕ) = (k + 10) + frag_f.outputReg.val :=
      congrArg Fin.val hh
    omega
  have h_disj2_zd : zFin ≠ factorFin := by
    intro hh
    have : (0 : ℕ) = k + 8 := congrArg Fin.val hh; omega
  have h_sPre_z : sPre.regs zFin = 0 := by
    have h_eq : (⟨0, (compileFrag_bprod frag_f).numRegs_pos⟩
        : Fin P.numRegs) = zFin := Fin.ext rfl
    rw [← h_eq]; exact h_zReg_zero
  have h_sPre_acc : sPre.regs accFin = vAccIn := by
    have h_eq : (⟨1, by
        have : 0 < frag_f.numRegs := frag_f.numRegs_pos
        change 1 < k + 10 + frag_f.numRegs; omega⟩
        : Fin P.numRegs) = accFin := Fin.ext rfl
    rw [← h_eq]; exact h_acc
  have h_sPre_fOut : sPre.regs fOutFin = vFOut := by
    have h_eq : (⟨(k + 10) + frag_f.outputReg.val, by
        have hO : frag_f.outputReg.val < frag_f.numRegs :=
          frag_f.outputReg.isLt
        change (k + 10) + frag_f.outputReg.val
          < k + 10 + frag_f.numRegs
        omega⟩
        : Fin P.numRegs) = fOutFin := Fin.ext rfl
    rw [← h_eq]; exact h_fOut
  have h_pc_P : sPre.pc = bprod_trBase frag_f := h_pc
  by_cases h_le : k' ≤ 4 * vAccIn
  · -- During the first transferLoop's strict bound.
    have h_bd := transferLoop_correct_pc_strict_bound P
      (bprod_trBase frag_f) accFin accCloneFin zFin
      h_disj1_sd h_disj1_zs h_disj1_zd H1 sPre h_pc_P h_sPre_z
      vAccIn h_sPre_acc k' h_le
    have h_top_eq : bprod_mul_innerTopPC frag_f
        = bprod_trBase frag_f + 8 := rfl
    rw [h_top_eq]; omega
  · -- k' ≥ 4 * vAccIn + 1: peel the first transferLoop's exit step
    -- and re-target the second transferLoop's strict bound.
    push_neg at h_le
    obtain ⟨d, hd_eq⟩ : ∃ d, k' = (4 * vAccIn + 1) + d :=
      ⟨k' - (4 * vAccIn + 1), by omega⟩
    have h_d_lt : d < 4 * vFOut + 1 := by omega
    rw [hd_eq]
    change (URMState.runFor P sPre ((4 * vAccIn + 1) + d)).pc
      < bprod_mul_innerTopPC frag_f
    rw [URMState.runFor_add]
    -- After 4 * vAccIn + 1 steps, the first transferLoop is at pcBase + 4
    -- with src = 0, dst = vAccIn, zReg = 0; preservation gives factor,
    -- fOut, etc.
    obtain ⟨hA_pc, hA_dst, hA_src, hA_z, hA_oth⟩ :=
      transferLoop_correct P (bprod_trBase frag_f) accFin accCloneFin
        zFin h_disj1_sd h_disj1_zs h_disj1_zd H1 sPre h_pc_P h_sPre_z
        vAccIn h_sPre_acc
    set sMid : URMState P := URMState.runFor P sPre (4 * vAccIn + 1)
    have hsMid_pc : sMid.pc = bprod_trBase frag_f + 4 := hA_pc
    have hsMid_z : sMid.regs zFin = 0 := hA_z
    have h_ne_fOut_accClone : fOutFin ≠ accCloneFin := by
      intro hh
      have : ((k + 10) + frag_f.outputReg.val : ℕ) = k + 7 :=
        congrArg Fin.val hh
      omega
    have h_ne_fOut_acc : fOutFin ≠ accFin := by
      intro hh
      have : ((k + 10) + frag_f.outputReg.val : ℕ) = 1 :=
        congrArg Fin.val hh
      omega
    have hsMid_fOut : sMid.regs fOutFin = vFOut := by
      rw [hA_oth fOutFin h_ne_fOut_accClone h_ne_fOut_acc
          h_disj2_zs.symm, h_sPre_fOut]
    by_cases h_d_top : d ≤ 4 * vFOut
    · have h_bd_strict := transferLoop_correct_pc_strict_bound P
        (bprod_trBase frag_f + 4) fOutFin factorFin zFin
        h_disj2_sd h_disj2_zs h_disj2_zd H2 sMid hsMid_pc hsMid_z
        vFOut hsMid_fOut d h_d_top
      have h_top_eq : bprod_mul_innerTopPC frag_f
          = bprod_trBase frag_f + 8 := rfl
      rw [h_top_eq]; omega
    · -- d ≥ 4 * vFOut + 1; impossible since d < 4 * vFOut + 1.
      exfalso; omega

/-- Per-iteration partial invariant of `compileFrag_bprod`'s
inner-mul loop. At iteration index `j ≤ vFOut`, the PC sits at
`bprod_mul_innerTopPC frag_f`, the destructive accumulator clone
(register `k + 7`) still holds the input accumulator `vAccIn`, the
multiplicative factor (register `k + 8`) has been counted down to
`vFOut - j`, the inner multiply scratch (register `k + 9`) is `0`,
the shared reserved-zero `zReg` (register `0`) is `0`, and the live
accumulator (register `1`) holds the running product `vAccIn * j`.
The base case (`j = 0`) is delivered by
`compileFrag_bprod_mul_partial_base`; subsequent sub-tasks supply
the inductive step and the outer iteration. -/
private structure compileFrag_bprod_mul_partial_invariant
    {k : ℕ}
    (frag_f : CompiledFragment (k + 1))
    (vAccIn vFOut : ℕ)
    (j : ℕ) (hj : j ≤ vFOut)
    (s : URMState (compileFrag_bprod frag_f).toURMProgram)
    : Prop where
  /-- The iteration index does not exceed the factor bound. -/
  hj_le : j ≤ vFOut := hj
  /-- PC sits at the inner-mul loop's top instruction. -/
  pc_eq : s.pc = bprod_mul_innerTopPC frag_f
  /-- The shared reserved-zero `zReg` (register `0`) is `0`. -/
  zReg_zero : s.regs ⟨0,
    (compileFrag_bprod frag_f).numRegs_pos⟩ = 0
  /-- The destructive accumulator clone (register `k + 7`) holds
  the input accumulator value. -/
  acc_clone_eq : s.regs ⟨k + 7, by
    have : 0 < frag_f.numRegs := frag_f.numRegs_pos
    change k + 7 < k + 10 + frag_f.numRegs; omega⟩ = vAccIn
  /-- The multiplicative factor (register `k + 8`) has been
  counted down to `vFOut - j`. -/
  factor_eq : s.regs ⟨k + 8, by
    have : 0 < frag_f.numRegs := frag_f.numRegs_pos
    change k + 8 < k + 10 + frag_f.numRegs; omega⟩ = vFOut - j
  /-- The inner multiply scratch (register `k + 9`) is `0`. -/
  mulTmp_zero : s.regs ⟨k + 9, by
    have : 0 < frag_f.numRegs := frag_f.numRegs_pos
    change k + 9 < k + 10 + frag_f.numRegs; omega⟩ = 0
  /-- The live accumulator (register `1`) holds the running
  product `vAccIn * j`. -/
  acc_eq : s.regs ⟨1, by
    have : 0 < frag_f.numRegs := frag_f.numRegs_pos
    change 1 < k + 10 + frag_f.numRegs; omega⟩ = vAccIn * j

/-- Base case (`j = 0`) of the inner-mul partial invariant of
`compileFrag_bprod`. Takes the post-state of the accumulator-update
prep segment plus the caller-supplied `h_sPrep_z` witness that
`zReg` is `0`; the latter is required because
`compileFrag_bprod_accUpdate_prep_post` does not carry the
`zReg_zero` clause and the caller (the bprod.1.c.4 assembly)
supplies it from the outer partial invariant. Zero URM steps:
the result is a field-by-field projection from `h_post`
specialised at `j = 0`. -/
private theorem compileFrag_bprod_mul_partial_base
    {k : ℕ}
    (frag_f : CompiledFragment (k + 1))
    (vAccIn vFOut : ℕ)
    (sPrep : URMState (compileFrag_bprod frag_f).toURMProgram)
    (h_sPrep_z : sPrep.regs ⟨0,
        (compileFrag_bprod frag_f).numRegs_pos⟩ = 0)
    (h_post : compileFrag_bprod_accUpdate_prep_post
                frag_f vAccIn vFOut sPrep) :
    compileFrag_bprod_mul_partial_invariant frag_f vAccIn vFOut
      0 (Nat.zero_le _) sPrep := by
  refine
    { pc_eq := ?_
      zReg_zero := ?_
      acc_clone_eq := ?_
      factor_eq := ?_
      mulTmp_zero := ?_
      acc_eq := ?_ }
  · exact h_post.pc_eq
  · exact h_sPrep_z
  · exact h_post.acc_clone_eq
  · rw [h_post.factor_eq, Nat.sub_zero]
  · exact h_post.mulTmp_zero
  · rw [h_post.acc_zero, Nat.mul_zero]

/-- Instruction-presence discharger for the inner-multiply body region of
`compileFrag_bprod`'s accumulator-update block, PCs `bprod_trBase frag_f
+ 8..19`. Produces:

* `h_top`: the `jumpZR vFactor (trBase + 20) (trBase + 9)` instruction at
  `bprod_mul_innerTopPC frag_f` (= `trBase + 8`);
* `h_dec`: the `decR vFactor` instruction at `bprod_mul_innerBodyStartPC
  frag_f` (= `trBase + 9`);
* `h_pT`: a `preservingTransferInstrs` bundle for the nine
  `preservingTransfer (trBase + 10) vAccClone vAcc vMulTmp` instructions
  at PCs `trBase + 10..18`, with `src = ⟨k + 7, _⟩` (`vAccClone`),
  `dst = ⟨1, _⟩` (`vAcc`), `tmp = ⟨k + 9, _⟩` (`vMulTmp`), and
  `zReg = ⟨0, _⟩`;
* `h_goto`: the `jumpZR 0 (bprod_mul_innerTopPC frag_f)
  (bprod_mul_innerTopPC frag_f)` instruction at `trBase + 19` (the
  unconditional return-to-top `URMRaw.goto`).

The bound witnesses on `Fin (compileFrag_bprod frag_f).toURMProgram.numRegs`
are returned so callers can construct `Fin`-handles for
`preservingTransfer_correct`. -/
private theorem compileFrag_bprod_accUpdate_innerBody_instr_at
    {k : ℕ}
    (frag_f : CompiledFragment (k + 1)) :
    let outer := (compileFrag_bprod frag_f).toURMProgram
    ∃ (h_acc : (1 : ℕ) < outer.numRegs)
      (h_accClone : k + 7 < outer.numRegs)
      (h_z : (0 : ℕ) < outer.numRegs)
      (h_factor : k + 8 < outer.numRegs)
      (h_mulTmp : k + 9 < outer.numRegs),
      outer.instrs[bprod_mul_innerTopPC frag_f]?
          = some (URMInstr.jumpZ ⟨k + 8, h_factor⟩
              (bprod_mul_resetPC frag_f)
              (bprod_mul_innerBodyStartPC frag_f))
        ∧ outer.instrs[bprod_mul_innerBodyStartPC frag_f]?
            = some (URMInstr.dec ⟨k + 8, h_factor⟩)
        ∧ preservingTransferInstrs outer (bprod_trBase frag_f + 10)
            ⟨k + 7, h_accClone⟩
            ⟨1, h_acc⟩
            ⟨k + 9, h_mulTmp⟩
            ⟨0, h_z⟩
        ∧ outer.instrs[bprod_trBase frag_f + 19]?
            = some (URMInstr.jumpZ ⟨0, h_z⟩
                (bprod_mul_innerTopPC frag_f)
                (bprod_mul_innerTopPC frag_f)) := by
  intro outer
  -- Abbreviations matching the constructor of `compileFrag_bprod`.
  let vAcc : ℕ := 1
  let vBoundIn : ℕ := 2
  let vX : ℕ := k + 3
  let vI : ℕ := k + 4
  let tmp1 : ℕ := k + 5
  let tmp2 : ℕ := k + 6
  let vAccClone : ℕ := k + 7
  let vFactor : ℕ := k + 8
  let vMulTmp : ℕ := k + 9
  let fBase : ℕ := k + 10
  let nR : ℕ := fBase + frag_f.numRegs
  let topPC : ℕ := 14
  let bodyStartPC : ℕ := 15
  let prologueBase : ℕ := 16 + frag_f.numRegs
  let bodyPCBase : ℕ := 16 + frag_f.numRegs + 9 * (k + 1)
  let fBodyLen : ℕ := frag_f.instrs.size - 1
  let trBase : ℕ := bodyPCBase + fBodyLen
  let exitPC : ℕ := trBase + 23
  let prelude : List URMInstrRaw :=
    [ .assignR 0 0,
      .assignR vAcc 0,
      .assignR vX 0,
      .assignR vI 0 ]
        ++ URMRaw.preservingTransfer 4 vBoundIn vX tmp2
        ++ [ .incR vAcc ]
  let loopTop : List URMInstrRaw :=
    [ .jumpZR vX exitPC bodyStartPC,
      .decR vX ]
  let zeroSweep : List URMInstrRaw :=
    bsum_zeroSweep frag_f fBase
  let prologue : List URMInstrRaw :=
    (List.finRange (k + 1)).flatMap fun s =>
      bsum_prologueBlock frag_f fBase tmp1 prologueBase s
  let fBody : List URMInstrRaw :=
    frag_f.instrs.pop.toList.map fun ins =>
      URMInstrRaw.reindexShift fBase bodyPCBase (toRawOfBounded ins)
  let accUpdate : List URMInstrRaw :=
    URMRaw.transferLoop trBase vAcc vAccClone
      ++ URMRaw.transferLoop (trBase + 4)
          (fBase + frag_f.outputReg.val) vFactor
      ++ [ .jumpZR vFactor (trBase + 20) (trBase + 9),
           .decR vFactor ]
      ++ URMRaw.preservingTransfer (trBase + 10)
          vAccClone vAcc vMulTmp
      ++ [ URMRaw.goto (trBase + 8),
           .assignR vAccClone 0 ]
  let epilogue : List URMInstrRaw :=
    [ .incR vI, URMRaw.goto topPC, .stopR ]
  let rawList : List URMInstrRaw :=
    prelude ++ loopTop ++ zeroSweep ++ prologue ++ fBody
      ++ accUpdate ++ epilogue
  -- Segment lengths.
  have h_prelude_len : prelude.length = 14 := by
    change ([URMInstrRaw.assignR 0 0, URMInstrRaw.assignR vAcc 0,
        URMInstrRaw.assignR vX 0, URMInstrRaw.assignR vI 0]
        ++ URMRaw.preservingTransfer 4 vBoundIn vX tmp2
        ++ [URMInstrRaw.incR vAcc]).length = 14
    simp only [List.length_append, List.length_cons, List.length_nil,
      URMRaw.preservingTransfer, URMRaw.goto]
  have h_loopTop_len : loopTop.length = 2 := by
    change ([URMInstrRaw.jumpZR vX exitPC bodyStartPC,
      URMInstrRaw.decR vX] : List URMInstrRaw).length = 2
    simp only [List.length_cons, List.length_nil]
  have h_zeroSweep_len : zeroSweep.length = frag_f.numRegs := by
    change ((List.finRange frag_f.numRegs).map _).length = _
    rw [List.length_map, List.length_finRange]
  have h_prologue_len : prologue.length = 9 * (k + 1) := by
    change ((List.finRange (k + 1)).flatMap fun s =>
        bsum_prologueBlock frag_f fBase tmp1 prologueBase s).length
        = 9 * (k + 1)
    have h_each : ∀ s : Fin (k + 1),
        (bsum_prologueBlock frag_f fBase tmp1 prologueBase s).length = 9 :=
      fun _ => rfl
    have h_aux : ∀ (l : List (Fin (k + 1))),
        (l.flatMap fun s =>
            bsum_prologueBlock frag_f fBase tmp1 prologueBase s).length
          = 9 * l.length := by
      intro l
      induction l with
      | nil => rfl
      | cons hd tl ih_in =>
        rw [List.flatMap_cons, List.length_append, ih_in, h_each hd,
          List.length_cons]
        omega
    rw [h_aux, List.length_finRange]
  have h_fBody_len : fBody.length = frag_f.instrs.size - 1 := by
    change (frag_f.instrs.pop.toList.map fun ins =>
        URMInstrRaw.reindexShift fBase bodyPCBase
          (toRawOfBounded ins)).length = _
    rw [List.length_map, Array.length_toList, Array.size_pop]
  have h_accUpdate_len : accUpdate.length = 21 := by
    change (URMRaw.transferLoop trBase vAcc vAccClone
        ++ URMRaw.transferLoop (trBase + 4)
            (fBase + frag_f.outputReg.val) vFactor
        ++ [URMInstrRaw.jumpZR vFactor (trBase + 20) (trBase + 9),
            URMInstrRaw.decR vFactor]
        ++ URMRaw.preservingTransfer (trBase + 10)
            vAccClone vAcc vMulTmp
        ++ [URMRaw.goto (trBase + 8),
            URMInstrRaw.assignR vAccClone 0]).length = 21
    simp only [URMRaw.transferLoop, URMRaw.preservingTransfer,
      URMRaw.goto, List.length_append, List.length_cons,
      List.length_nil]
  have h_epilogue_len : epilogue.length = 3 := by
    change ([URMInstrRaw.incR vI, URMRaw.goto topPC,
      URMInstrRaw.stopR] : List URMInstrRaw).length = 3
    simp only [List.length_cons, List.length_nil]
  -- outer.numRegs = nR.
  have h_numRegs_eq : outer.numRegs = nR := rfl
  -- Bound proofs for the named registers.
  have h_acc_lt : (1 : ℕ) < outer.numRegs := by
    rw [h_numRegs_eq]
    have : 0 < frag_f.numRegs := frag_f.numRegs_pos
    change 1 < fBase + frag_f.numRegs; omega
  have h_accClone_lt : k + 7 < outer.numRegs := by
    rw [h_numRegs_eq]
    have : 0 < frag_f.numRegs := frag_f.numRegs_pos
    change k + 7 < fBase + frag_f.numRegs; omega
  have h_z_lt : (0 : ℕ) < outer.numRegs :=
    (compileFrag_bprod frag_f).numRegs_pos
  have h_factor_lt : k + 8 < outer.numRegs := by
    rw [h_numRegs_eq]
    have : 0 < frag_f.numRegs := frag_f.numRegs_pos
    change k + 8 < fBase + frag_f.numRegs; omega
  have h_mulTmp_lt : k + 9 < outer.numRegs := by
    rw [h_numRegs_eq]
    have : 0 < frag_f.numRegs := frag_f.numRegs_pos
    change k + 9 < fBase + frag_f.numRegs; omega
  refine ⟨h_acc_lt, h_accClone_lt, h_z_lt, h_factor_lt, h_mulTmp_lt, ?_⟩
  -- Reconstruct the boundedness witness on rawList.
  have hAcc : vAcc + 1 ≤ nR := by
    change 1 + 1 ≤ k + 10 + frag_f.numRegs
    have : 0 < frag_f.numRegs := frag_f.numRegs_pos; omega
  have hBoundIn : vBoundIn + 1 ≤ nR := by
    change 2 + 1 ≤ k + 10 + frag_f.numRegs
    have : 0 < frag_f.numRegs := frag_f.numRegs_pos; omega
  have hVX : vX + 1 ≤ nR := by
    change k + 3 + 1 ≤ k + 10 + frag_f.numRegs
    have : 0 < frag_f.numRegs := frag_f.numRegs_pos; omega
  have hVI : vI + 1 ≤ nR := by
    change k + 4 + 1 ≤ k + 10 + frag_f.numRegs
    have : 0 < frag_f.numRegs := frag_f.numRegs_pos; omega
  have hTmp1 : tmp1 + 1 ≤ nR := by
    change k + 5 + 1 ≤ k + 10 + frag_f.numRegs
    have : 0 < frag_f.numRegs := frag_f.numRegs_pos; omega
  have hTmp2 : tmp2 + 1 ≤ nR := by
    change k + 6 + 1 ≤ k + 10 + frag_f.numRegs
    have : 0 < frag_f.numRegs := frag_f.numRegs_pos; omega
  have hAccClone : vAccClone + 1 ≤ nR := by
    change k + 7 + 1 ≤ k + 10 + frag_f.numRegs
    have : 0 < frag_f.numRegs := frag_f.numRegs_pos; omega
  have hFactor : vFactor + 1 ≤ nR := by
    change k + 8 + 1 ≤ k + 10 + frag_f.numRegs
    have : 0 < frag_f.numRegs := frag_f.numRegs_pos; omega
  have hMulTmp : vMulTmp + 1 ≤ nR := by
    change k + 9 + 1 ≤ k + 10 + frag_f.numRegs
    have : 0 < frag_f.numRegs := frag_f.numRegs_pos; omega
  have hFOut : fBase + frag_f.outputReg.val + 1 ≤ nR := by
    have : frag_f.outputReg.val < frag_f.numRegs :=
      frag_f.outputReg.isLt
    change fBase + frag_f.outputReg.val + 1 ≤ fBase + frag_f.numRegs
    omega
  have hPrologueSrc : ∀ s : Fin (k + 1),
      bsum_prologueSrc k s + 1 ≤ nR := by
    intro s
    have hs : s.val < k + 1 := s.isLt
    simp only [bsum_prologueSrc, nR, fBase]
    split <;> omega
  have hFIn : ∀ s : Fin (k + 1),
      fBase + (frag_f.inputRegs s).val + 1 ≤ nR := by
    intro s
    have : (frag_f.inputRegs s).val < frag_f.numRegs :=
      (frag_f.inputRegs s).isLt
    change fBase + (frag_f.inputRegs s).val + 1
        ≤ fBase + frag_f.numRegs
    omega
  have hPreludeBound : URMInstrRaw.boundedBy nR prelude := by
    intro ins hmem
    simp only [prelude, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hmem
    rcases hmem with ((h | h | h | h) | hpT) | h
    · rw [h]; simp only [URMInstrRaw.regBound]; omega
    · rw [h]; simp only [URMInstrRaw.regBound]; exact hAcc
    · rw [h]; simp only [URMInstrRaw.regBound]; exact hVX
    · rw [h]; simp only [URMInstrRaw.regBound]; exact hVI
    · exact boundedBy_preservingTransfer nR _ _ _ _
        hBoundIn hVX hTmp2 ins hpT
    · rw [h]; simp only [URMInstrRaw.regBound]; exact hAcc
  have hLoopTopBound : URMInstrRaw.boundedBy nR loopTop := by
    intro ins hmem
    simp only [loopTop, List.mem_cons, List.not_mem_nil,
      or_false] at hmem
    rcases hmem with h | h <;>
      (rw [h]; simp only [URMInstrRaw.regBound]; exact hVX)
  have hZeroSweepBound : URMInstrRaw.boundedBy nR zeroSweep := by
    have hBlock : fBase + frag_f.numRegs ≤ nR := Nat.le_refl _
    exact boundedBy_bsum_zeroSweep frag_f fBase nR hBlock
  have hPrologueBound : URMInstrRaw.boundedBy nR prologue := by
    intro ins hmem
    simp only [prologue, List.mem_flatMap] at hmem
    rcases hmem with ⟨s, _, hs⟩
    exact boundedBy_bsum_prologueBlock frag_f fBase tmp1
      prologueBase nR s (hPrologueSrc s) (hFIn s) hTmp1 ins hs
  have hFBodyBound : URMInstrRaw.boundedBy nR fBody := by
    intro ins hmem
    simp only [fBody, List.mem_map] at hmem
    rcases hmem with ⟨ins', _, heq⟩
    rw [← heq]
    have hb : (toRawOfBounded ins').regBound ≤ frag_f.numRegs :=
      regBound_toRawOfBounded_le ins'
    have hr := regBound_reindexShift_le_offset_add fBase
      bodyPCBase frag_f.numRegs (toRawOfBounded ins') hb
    change _ ≤ fBase + frag_f.numRegs
    omega
  have hAccUpdateBound : URMInstrRaw.boundedBy nR accUpdate := by
    intro ins hmem
    simp only [accUpdate, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hmem
    rcases hmem with
      ((((hTr1 | hTr2) | hOuter) | hInner) | hTail)
    · exact boundedBy_transferLoop nR _ _ _
        hAcc hAccClone ins hTr1
    · exact boundedBy_transferLoop nR _ _ _
        hFOut hFactor ins hTr2
    · rcases hOuter with h | h
      · rw [h]; simp only [URMInstrRaw.regBound]; exact hFactor
      · rw [h]; simp only [URMInstrRaw.regBound]; exact hFactor
    · exact boundedBy_preservingTransfer nR _ _ _ _
        hAccClone hAcc hMulTmp ins hInner
    · rcases hTail with h | h
      · rw [h]; simp only [URMRaw.goto, URMInstrRaw.regBound]
        omega
      · rw [h]; simp only [URMInstrRaw.regBound]; exact hAccClone
  have hEpilogueBound : URMInstrRaw.boundedBy nR epilogue := by
    intro ins hmem
    simp only [epilogue, URMRaw.goto, List.mem_cons,
      List.not_mem_nil, or_false] at hmem
    rcases hmem with h | h | h
    · rw [h]; simp only [URMInstrRaw.regBound]; exact hVI
    · rw [h]; simp only [URMInstrRaw.regBound]; omega
    · rw [h]; simp only [URMInstrRaw.regBound]; omega
  have hBoundOuter : URMInstrRaw.boundedBy nR rawList := by
    intro ins hmem
    simp only [rawList, List.mem_append] at hmem
    rcases hmem with
      (((((hP | hL') | hZ) | hPr) | hF) | hA) | hE
    · exact hPreludeBound ins hP
    · exact hLoopTopBound ins hL'
    · exact hZeroSweepBound ins hZ
    · exact hPrologueBound ins hPr
    · exact hFBodyBound ins hF
    · exact hAccUpdateBound ins hA
    · exact hEpilogueBound ins hE
  -- preAc = prelude ++ loopTop ++ zeroSweep ++ prologue ++ fBody has
  -- length 14 + 2 + numRegs + 9*(k+1) + (instrs.size - 1) = trBase.
  set preAc : List URMInstrRaw :=
    prelude ++ loopTop ++ zeroSweep ++ prologue ++ fBody
    with h_preAc_def
  have h_preAc_len : preAc.length = trBase := by
    rw [h_preAc_def]
    simp only [List.length_append]
    rw [h_prelude_len, h_loopTop_len, h_zeroSweep_len, h_prologue_len,
      h_fBody_len]
  -- Per-position lookup helper: rawList at PC trBase + d (for d < 20)
  -- equals the corresponding entry of accUpdate ++ epilogue.
  have h_lookup_raw : ∀ (d : ℕ) (_hd : d < 20) (h_idx_lt : trBase + d
      < rawList.length),
      rawList[trBase + d]'h_idx_lt
        = (accUpdate ++ epilogue)[d]'(by
            rw [List.length_append, h_accUpdate_len, h_epilogue_len]
            omega) := by
    intro d hd h_idx_lt
    have h_rawList_split :
        rawList = preAc ++ (accUpdate ++ epilogue) := by
      change prelude ++ loopTop ++ zeroSweep ++ prologue ++ fBody
        ++ accUpdate ++ epilogue = _
      rw [h_preAc_def]
      simp only [List.append_assoc]
    have h_pref_le : preAc.length ≤ trBase + d := by
      rw [h_preAc_len]; omega
    have h_idx_lt' :
        trBase + d < (preAc ++ (accUpdate ++ epilogue)).length := by
      simp only [List.length_append]
      rw [h_preAc_len, h_accUpdate_len, h_epilogue_len]
      omega
    have h_step1 :
        rawList[trBase + d]'h_idx_lt
          = (preAc ++ (accUpdate ++ epilogue))[trBase + d]'h_idx_lt' := by
      congr 1
    rw [h_step1, List.getElem_append_right h_pref_le]
    have h_idx_eq : trBase + d - preAc.length = d := by
      rw [h_preAc_len]; omega
    congr 1
  -- Membership for the bound witness.
  have h_ae_d_in_rawList : ∀ (d : ℕ) (_hd : d < 20),
      ((accUpdate ++ epilogue)[d]'(by
        rw [List.length_append, h_accUpdate_len, h_epilogue_len]
        omega)) ∈ rawList := by
    intro d hd
    have h_mem_ae :
        (accUpdate ++ epilogue)[d]'(by
          rw [List.length_append, h_accUpdate_len, h_epilogue_len]
          omega) ∈ accUpdate ++ epilogue :=
      List.getElem_mem _
    rcases List.mem_append.mp h_mem_ae with hA | hE
    · apply List.mem_append.mpr; left
      apply List.mem_append.mpr; right; exact hA
    · apply List.mem_append.mpr; right; exact hE
  -- Per-position outer.instrs[trBase + d]? lookup at d.
  have h_outerInstr_lookup :
      ∀ (d : ℕ) (hd : d < 20),
        outer.instrs[trBase + d]?
          = some (URMInstrRaw.toBounded nR
              ((accUpdate ++ epilogue)[d]'(by
                rw [List.length_append, h_accUpdate_len, h_epilogue_len]
                omega))
              (hBoundOuter _ (h_ae_d_in_rawList d hd))) := by
    intro d hd
    have h_idx_lt_outer : trBase + d < rawList.length := by
      have h_raw_len : rawList.length = preAc.length + 21 + 3 := by
        change (prelude ++ loopTop ++ zeroSweep ++ prologue ++ fBody
          ++ accUpdate ++ epilogue).length = preAc.length + 21 + 3
        rw [h_preAc_def]
        simp only [List.length_append]
        rw [h_accUpdate_len, h_epilogue_len]
      rw [h_raw_len, h_preAc_len]; omega
    change (URMInstrRaw.toBoundedArray nR rawList hBoundOuter)[
        trBase + d]? = _
    rw [URMInstrRaw.toBoundedArray_getElem? nR rawList hBoundOuter
        (trBase + d) h_idx_lt_outer]
    have h_raw_eq := h_lookup_raw d hd h_idx_lt_outer
    apply congrArg some
    exact URMInstrRaw.toBounded_congr nR h_raw_eq _ _
  -- Concrete entries of accUpdate ++ epilogue at d = 8..19.
  have h_ae_8 : (accUpdate ++ epilogue)[(8 : ℕ)]'(by
      rw [List.length_append, h_accUpdate_len, h_epilogue_len]; decide)
      = URMInstrRaw.jumpZR vFactor (trBase + 20) (trBase + 9) := rfl
  have h_ae_9 : (accUpdate ++ epilogue)[(9 : ℕ)]'(by
      rw [List.length_append, h_accUpdate_len, h_epilogue_len]; decide)
      = URMInstrRaw.decR vFactor := rfl
  have h_ae_10 : (accUpdate ++ epilogue)[(10 : ℕ)]'(by
      rw [List.length_append, h_accUpdate_len, h_epilogue_len]; decide)
      = URMInstrRaw.jumpZR vAccClone (trBase + 10 + 5)
          (trBase + 10 + 1) := rfl
  have h_ae_11 : (accUpdate ++ epilogue)[(11 : ℕ)]'(by
      rw [List.length_append, h_accUpdate_len, h_epilogue_len]; decide)
      = URMInstrRaw.decR vAccClone := rfl
  have h_ae_12 : (accUpdate ++ epilogue)[(12 : ℕ)]'(by
      rw [List.length_append, h_accUpdate_len, h_epilogue_len]; decide)
      = URMInstrRaw.incR vAcc := rfl
  have h_ae_13 : (accUpdate ++ epilogue)[(13 : ℕ)]'(by
      rw [List.length_append, h_accUpdate_len, h_epilogue_len]; decide)
      = URMInstrRaw.incR vMulTmp := rfl
  have h_ae_14 : (accUpdate ++ epilogue)[(14 : ℕ)]'(by
      rw [List.length_append, h_accUpdate_len, h_epilogue_len]; decide)
      = URMInstrRaw.jumpZR 0 (trBase + 10) (trBase + 10) := rfl
  have h_ae_15 : (accUpdate ++ epilogue)[(15 : ℕ)]'(by
      rw [List.length_append, h_accUpdate_len, h_epilogue_len]; decide)
      = URMInstrRaw.jumpZR vMulTmp (trBase + 10 + 9)
          (trBase + 10 + 6) := rfl
  have h_ae_16 : (accUpdate ++ epilogue)[(16 : ℕ)]'(by
      rw [List.length_append, h_accUpdate_len, h_epilogue_len]; decide)
      = URMInstrRaw.decR vMulTmp := rfl
  have h_ae_17 : (accUpdate ++ epilogue)[(17 : ℕ)]'(by
      rw [List.length_append, h_accUpdate_len, h_epilogue_len]; decide)
      = URMInstrRaw.incR vAccClone := rfl
  have h_ae_18 : (accUpdate ++ epilogue)[(18 : ℕ)]'(by
      rw [List.length_append, h_accUpdate_len, h_epilogue_len]; decide)
      = URMInstrRaw.jumpZR 0 (trBase + 10 + 5) (trBase + 10 + 5) := rfl
  have h_ae_19 : (accUpdate ++ epilogue)[(19 : ℕ)]'(by
      rw [List.length_append, h_accUpdate_len, h_epilogue_len]; decide)
      = URMInstrRaw.jumpZR 0 (trBase + 8) (trBase + 8) := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- h_top.
    change outer.instrs[bprod_trBase frag_f + 8]? = _
    rw [show bprod_trBase frag_f + 8 = trBase + 8 from rfl]
    have h := h_outerInstr_lookup 8 (by decide)
    rw [h]
    apply congrArg some
    exact URMInstrRaw.toBounded_congr nR h_ae_8 _ _
  · -- h_dec.
    change outer.instrs[bprod_trBase frag_f + 9]? = _
    rw [show bprod_trBase frag_f + 9 = trBase + 9 from rfl]
    have h := h_outerInstr_lookup 9 (by decide)
    rw [h]
    apply congrArg some
    exact URMInstrRaw.toBounded_congr nR h_ae_9 _ _
  · -- h_pT (preservingTransferInstrs at trBase + 10).
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- h0: PC pcBase = trBase + 10
      change outer.instrs[bprod_trBase frag_f + 10]? = _
      rw [show bprod_trBase frag_f + 10 = trBase + 10 from rfl]
      have h := h_outerInstr_lookup 10 (by decide)
      rw [h]
      apply congrArg some
      exact URMInstrRaw.toBounded_congr nR h_ae_10 _ _
    · -- h1: PC pcBase + 1 = trBase + 11
      change outer.instrs[bprod_trBase frag_f + 10 + 1]? = _
      rw [show bprod_trBase frag_f + 10 + 1 = trBase + 11 from rfl]
      have h := h_outerInstr_lookup 11 (by decide)
      rw [h]
      apply congrArg some
      exact URMInstrRaw.toBounded_congr nR h_ae_11 _ _
    · -- h2: PC pcBase + 2 = trBase + 12
      change outer.instrs[bprod_trBase frag_f + 10 + 2]? = _
      rw [show bprod_trBase frag_f + 10 + 2 = trBase + 12 from rfl]
      have h := h_outerInstr_lookup 12 (by decide)
      rw [h]
      apply congrArg some
      exact URMInstrRaw.toBounded_congr nR h_ae_12 _ _
    · -- h3: PC pcBase + 3 = trBase + 13
      change outer.instrs[bprod_trBase frag_f + 10 + 3]? = _
      rw [show bprod_trBase frag_f + 10 + 3 = trBase + 13 from rfl]
      have h := h_outerInstr_lookup 13 (by decide)
      rw [h]
      apply congrArg some
      exact URMInstrRaw.toBounded_congr nR h_ae_13 _ _
    · -- h4: PC pcBase + 4 = trBase + 14
      change outer.instrs[bprod_trBase frag_f + 10 + 4]? = _
      rw [show bprod_trBase frag_f + 10 + 4 = trBase + 14 from rfl]
      have h := h_outerInstr_lookup 14 (by decide)
      rw [h]
      apply congrArg some
      exact URMInstrRaw.toBounded_congr nR h_ae_14 _ _
    · -- h5: PC pcBase + 5 = trBase + 15
      change outer.instrs[bprod_trBase frag_f + 10 + 5]? = _
      rw [show bprod_trBase frag_f + 10 + 5 = trBase + 15 from rfl]
      have h := h_outerInstr_lookup 15 (by decide)
      rw [h]
      apply congrArg some
      exact URMInstrRaw.toBounded_congr nR h_ae_15 _ _
    · -- h6: PC pcBase + 6 = trBase + 16
      change outer.instrs[bprod_trBase frag_f + 10 + 6]? = _
      rw [show bprod_trBase frag_f + 10 + 6 = trBase + 16 from rfl]
      have h := h_outerInstr_lookup 16 (by decide)
      rw [h]
      apply congrArg some
      exact URMInstrRaw.toBounded_congr nR h_ae_16 _ _
    · -- h7: PC pcBase + 7 = trBase + 17
      change outer.instrs[bprod_trBase frag_f + 10 + 7]? = _
      rw [show bprod_trBase frag_f + 10 + 7 = trBase + 17 from rfl]
      have h := h_outerInstr_lookup 17 (by decide)
      rw [h]
      apply congrArg some
      exact URMInstrRaw.toBounded_congr nR h_ae_17 _ _
    · -- h8: PC pcBase + 8 = trBase + 18
      change outer.instrs[bprod_trBase frag_f + 10 + 8]? = _
      rw [show bprod_trBase frag_f + 10 + 8 = trBase + 18 from rfl]
      have h := h_outerInstr_lookup 18 (by decide)
      rw [h]
      apply congrArg some
      exact URMInstrRaw.toBounded_congr nR h_ae_18 _ _
  · -- h_goto.
    change outer.instrs[bprod_trBase frag_f + 19]? = _
    rw [show bprod_trBase frag_f + 19 = trBase + 19 from rfl]
    have h := h_outerInstr_lookup 19 (by decide)
    rw [h]
    apply congrArg some
    exact URMInstrRaw.toBounded_congr nR h_ae_19 _ _

/-- Inner-multiply per-iteration step (`j → j + 1`) of `compileFrag_bprod`'s
accumulator-update loop. From a pre-state satisfying the partial invariant
at iteration index `j.val < vFOut`, advancing `9 * vAccIn + 5` URM steps
yields a state satisfying the partial invariant at iteration index
`j.val + 1`. The five control steps are:

* a `jumpZR vFactor (resetPC) (innerBodyStartPC)` taking the non-zero
  branch (since `V_factor = vFOut - j.val > 0` for `j.val < vFOut`);
* a `decR vFactor` reducing the factor to `vFOut - (j.val + 1)`;
* a `preservingTransfer vAccClone vAcc vMulTmp` block (9 instructions,
  `9 * vAccIn + 2` steps) adding `vAccIn` from the clone into the live
  accumulator while restoring the clone and zeroing the scratch;
* an unconditional `jumpZR 0 innerTopPC innerTopPC` returning the PC to
  `bprod_mul_innerTopPC frag_f`.

Total: `(9 * vAccIn + 2) + 3 = 9 * vAccIn + 5`. The intermediate PC stays
strictly below `bprod_mul_resetPC frag_f` (= `innerTopPC + 12`)
throughout, so the iteration does not escape the inner-multiply region
before completing. -/
private theorem compileFrag_bprod_mul_partial_step
    {k : ℕ}
    (frag_f : CompiledFragment (k + 1))
    (vAccIn vFOut : ℕ)
    (j : Fin vFOut)
    (sPre : URMState (compileFrag_bprod frag_f).toURMProgram)
    (h_inv : compileFrag_bprod_mul_partial_invariant frag_f
              vAccIn vFOut j.val j.isLt.le sPre) :
    ∃ T0 : ℕ,
      T0 = 9 * vAccIn + 5 ∧
      compileFrag_bprod_mul_partial_invariant frag_f vAccIn vFOut
          (j.val + 1) (Nat.succ_le_of_lt j.isLt)
        (URMState.runFor _ sPre T0) ∧
      (∀ k' < T0,
        (URMState.runFor _ sPre k').pc
          < bprod_mul_resetPC frag_f) := by
  -- Abbreviations.
  let P : URMProgram (k + 1) := (compileFrag_bprod frag_f).toURMProgram
  -- Instruction-presence bundle.
  obtain ⟨h_acc_lt, h_accClone_lt, h_z_lt, h_factor_lt, h_mulTmp_lt,
      h_top, h_dec, h_pT, h_goto⟩ :=
    compileFrag_bprod_accUpdate_innerBody_instr_at frag_f
  -- Fin handles.
  let accFin : Fin P.numRegs := ⟨1, h_acc_lt⟩
  let accCloneFin : Fin P.numRegs := ⟨k + 7, h_accClone_lt⟩
  let zFin : Fin P.numRegs := ⟨0, h_z_lt⟩
  let factorFin : Fin P.numRegs := ⟨k + 8, h_factor_lt⟩
  let mulTmpFin : Fin P.numRegs := ⟨k + 9, h_mulTmp_lt⟩
  -- Rewrite invariant hypotheses against the local Fin handles.
  have h_sPre_pc : sPre.pc = bprod_mul_innerTopPC frag_f := h_inv.pc_eq
  have h_sPre_zReg : sPre.regs zFin = 0 := by
    have h_eq : (⟨0, (compileFrag_bprod frag_f).numRegs_pos⟩
        : Fin P.numRegs) = zFin := Fin.ext rfl
    rw [← h_eq]; exact h_inv.zReg_zero
  have h_sPre_accClone : sPre.regs accCloneFin = vAccIn := by
    have h_eq : (⟨k + 7, by
        have : 0 < frag_f.numRegs := frag_f.numRegs_pos
        change k + 7 < k + 10 + frag_f.numRegs; omega⟩
        : Fin P.numRegs) = accCloneFin := Fin.ext rfl
    rw [← h_eq]; exact h_inv.acc_clone_eq
  have h_sPre_factor : sPre.regs factorFin = vFOut - j.val := by
    have h_eq : (⟨k + 8, by
        have : 0 < frag_f.numRegs := frag_f.numRegs_pos
        change k + 8 < k + 10 + frag_f.numRegs; omega⟩
        : Fin P.numRegs) = factorFin := Fin.ext rfl
    rw [← h_eq]; exact h_inv.factor_eq
  have h_sPre_mulTmp : sPre.regs mulTmpFin = 0 := by
    have h_eq : (⟨k + 9, by
        have : 0 < frag_f.numRegs := frag_f.numRegs_pos
        change k + 9 < k + 10 + frag_f.numRegs; omega⟩
        : Fin P.numRegs) = mulTmpFin := Fin.ext rfl
    rw [← h_eq]; exact h_inv.mulTmp_zero
  have h_sPre_acc : sPre.regs accFin = vAccIn * j.val := by
    have h_eq : (⟨1, by
        have : 0 < frag_f.numRegs := frag_f.numRegs_pos
        change 1 < k + 10 + frag_f.numRegs; omega⟩
        : Fin P.numRegs) = accFin := Fin.ext rfl
    rw [← h_eq]; exact h_inv.acc_eq
  -- Step A: one step (jumpZR vFactor (resetPC) (innerBodyStartPC)).
  -- Since vFactor = vFOut - j.val > 0, takes non-zero branch.
  have h_factor_pos : vFOut - j.val ≠ 0 := by
    have : j.val < vFOut := j.isLt
    omega
  have h_top' : P.instrs[bprod_mul_innerTopPC frag_f]?
      = some (URMInstr.jumpZ factorFin
          (bprod_mul_resetPC frag_f)
          (bprod_mul_innerBodyStartPC frag_f)) := h_top
  set sA : URMState P :=
    { pc := bprod_mul_innerBodyStartPC frag_f
      regs := sPre.regs }
  have h_stepA : URMState.runFor P sPre 1 = sA := by
    change URMState.runFor P sPre (0 + 1) = sA
    rw [URMState.runFor_succ,
      URMState.runFor_zero,
      URMState.step_of_getElem?_jumpZ P sPre
        (bprod_mul_innerTopPC frag_f) factorFin
        (bprod_mul_resetPC frag_f)
        (bprod_mul_innerBodyStartPC frag_f) h_sPre_pc h_top']
    have h_neq : sPre.regs factorFin ≠ 0 := by
      rw [h_sPre_factor]; exact h_factor_pos
    simp only [h_neq, ↓reduceIte]
    rfl
  -- Step B: one step (decR vFactor) from sA.
  have h_sA_pc : sA.pc = bprod_mul_innerBodyStartPC frag_f := rfl
  have h_dec' : P.instrs[bprod_mul_innerBodyStartPC frag_f]?
      = some (URMInstr.dec factorFin) := h_dec
  set sB : URMState P :=
    { pc := bprod_trBase frag_f + 10
      regs := Function.update sA.regs factorFin
        (sA.regs factorFin - 1) }
  have h_stepB : URMState.runFor P sA 1 = sB := by
    change URMState.runFor P sA (0 + 1) = sB
    rw [URMState.runFor_succ,
      URMState.runFor_zero,
      URMState.step_of_getElem?_dec P sA
        (bprod_mul_innerBodyStartPC frag_f) factorFin h_sA_pc h_dec']
    -- sB defines pc as trBase + 10. sA.pc = innerBodyStartPC = trBase + 9.
    -- Step pc = sA.pc + 1 = trBase + 9 + 1 = trBase + 10.
    rfl
  -- preservingTransfer: from sB, run 9 * vAccIn + 2 steps to sC.
  have h_disj_sd : accCloneFin ≠ accFin := by
    intro hh
    have : (k + 7 : ℕ) = 1 := congrArg Fin.val hh; omega
  have h_disj_st : accCloneFin ≠ mulTmpFin := by
    intro hh
    have : (k + 7 : ℕ) = k + 9 := congrArg Fin.val hh; omega
  have h_disj_dt : accFin ≠ mulTmpFin := by
    intro hh
    have : (1 : ℕ) = k + 9 := congrArg Fin.val hh; omega
  have h_disj_zs : zFin ≠ accCloneFin := by
    intro hh
    have : (0 : ℕ) = k + 7 := congrArg Fin.val hh; omega
  have h_disj_zd : zFin ≠ accFin := by
    intro hh
    have : (0 : ℕ) = 1 := congrArg Fin.val hh; omega
  have h_disj_zt : zFin ≠ mulTmpFin := by
    intro hh
    have : (0 : ℕ) = k + 9 := congrArg Fin.val hh; omega
  have h_sB_pc : sB.pc = bprod_trBase frag_f + 10 := rfl
  -- sB.regs zFin = 0 (zFin not updated by step B since zFin ≠ factorFin).
  have h_disj_z_factor : zFin ≠ factorFin := by
    intro hh
    have : (0 : ℕ) = k + 8 := congrArg Fin.val hh; omega
  have h_sB_z : sB.regs zFin = 0 := by
    change Function.update sA.regs factorFin (sA.regs factorFin - 1) zFin = 0
    rw [Function.update_of_ne h_disj_z_factor]; exact h_sPre_zReg
  -- sB.regs mulTmpFin = 0 (mulTmpFin ≠ factorFin).
  have h_disj_mulTmp_factor : mulTmpFin ≠ factorFin := by
    intro hh
    have : (k + 9 : ℕ) = k + 8 := congrArg Fin.val hh; omega
  have h_sB_mulTmp : sB.regs mulTmpFin = 0 := by
    change Function.update sA.regs factorFin (sA.regs factorFin - 1)
        mulTmpFin = 0
    rw [Function.update_of_ne h_disj_mulTmp_factor]; exact h_sPre_mulTmp
  -- sB.regs accCloneFin = vAccIn.
  have h_disj_accClone_factor : accCloneFin ≠ factorFin := by
    intro hh
    have : (k + 7 : ℕ) = k + 8 := congrArg Fin.val hh; omega
  have h_sB_accClone : sB.regs accCloneFin = vAccIn := by
    change Function.update sA.regs factorFin (sA.regs factorFin - 1)
        accCloneFin = vAccIn
    rw [Function.update_of_ne h_disj_accClone_factor]; exact h_sPre_accClone
  -- sB.regs accFin = vAccIn * j.val.
  have h_disj_acc_factor : accFin ≠ factorFin := by
    intro hh
    have : (1 : ℕ) = k + 8 := congrArg Fin.val hh; omega
  have h_sB_acc : sB.regs accFin = vAccIn * j.val := by
    change Function.update sA.regs factorFin (sA.regs factorFin - 1)
        accFin = vAccIn * j.val
    rw [Function.update_of_ne h_disj_acc_factor]; exact h_sPre_acc
  -- sB.regs factorFin = vFOut - (j.val + 1).
  have h_sB_factor : sB.regs factorFin = vFOut - (j.val + 1) := by
    change Function.update sA.regs factorFin (sA.regs factorFin - 1)
        factorFin = vFOut - (j.val + 1)
    rw [Function.update_self]
    change sPre.regs factorFin - 1 = vFOut - (j.val + 1)
    rw [h_sPre_factor]
    have : j.val < vFOut := j.isLt
    omega
  obtain ⟨hC_pc, hC_dst, hC_src, hC_tmp, hC_z, hC_oth⟩ :=
    preservingTransfer_correct P (bprod_trBase frag_f + 10)
      accCloneFin accFin mulTmpFin zFin
      h_disj_sd h_disj_st h_disj_dt h_disj_zs h_disj_zd h_disj_zt
      h_pT sB h_sB_pc h_sB_z h_sB_mulTmp vAccIn h_sB_accClone
  set sC : URMState P :=
    URMState.runFor P sB (9 * vAccIn + 2)
  have h_sC_pc : sC.pc = bprod_trBase frag_f + 19 := by
    change (URMState.runFor P sB (9 * vAccIn + 2)).pc
      = bprod_trBase frag_f + 19
    rw [hC_pc]
  have h_sC_z : sC.regs zFin = 0 := hC_z
  have h_sC_mulTmp : sC.regs mulTmpFin = 0 := hC_tmp
  have h_sC_acc : sC.regs accFin = vAccIn * j.val + vAccIn := by
    rw [hC_dst, h_sB_acc]
  have h_sC_accClone : sC.regs accCloneFin = vAccIn := hC_src
  have h_sC_factor : sC.regs factorFin = vFOut - (j.val + 1) := by
    rw [hC_oth factorFin h_disj_acc_factor.symm, h_sB_factor]
  -- Step D: one step (jumpZR 0 innerTopPC innerTopPC) from sC.
  have h_goto' : P.instrs[bprod_trBase frag_f + 19]?
      = some (URMInstr.jumpZ zFin
          (bprod_mul_innerTopPC frag_f)
          (bprod_mul_innerTopPC frag_f)) := h_goto
  set sD : URMState P :=
    { pc := bprod_mul_innerTopPC frag_f
      regs := sC.regs }
  have h_stepD : URMState.runFor P sC 1 = sD := by
    change URMState.runFor P sC (0 + 1) = sD
    rw [URMState.runFor_succ,
      URMState.runFor_zero,
      URMState.step_of_getElem?_jumpZ P sC
        (bprod_trBase frag_f + 19) zFin
        (bprod_mul_innerTopPC frag_f)
        (bprod_mul_innerTopPC frag_f) h_sC_pc h_goto']
    simp only [h_sC_z, ↓reduceIte]
    rfl
  -- Compose total run: 9 * vAccIn + 5 = 1 + 1 + (9 * vAccIn + 2) + 1.
  have h_runFor_eq :
      URMState.runFor (compileFrag_bprod frag_f).toURMProgram sPre
          (9 * vAccIn + 5) = sD := by
    change URMState.runFor P sPre (9 * vAccIn + 5) = sD
    have h_sum : (9 * vAccIn + 5 : ℕ)
        = 1 + (1 + ((9 * vAccIn + 2) + 1)) := by omega
    rw [h_sum, URMState.runFor_add, h_stepA, URMState.runFor_add,
      h_stepB, URMState.runFor_add]
    change URMState.runFor P (URMState.runFor P sB (9 * vAccIn + 2)) 1 = sD
    exact h_stepD
  refine ⟨9 * vAccIn + 5, rfl, ?_, ?_⟩
  -- Invariant @ (j.val + 1).
  · refine
      { hj_le := Nat.succ_le_of_lt j.isLt
        pc_eq := ?_
        zReg_zero := ?_
        acc_clone_eq := ?_
        factor_eq := ?_
        mulTmp_zero := ?_
        acc_eq := ?_ }
    · -- pc_eq: sD.pc = bprod_mul_innerTopPC frag_f.
      rw [h_runFor_eq]
    · -- zReg_zero.
      rw [h_runFor_eq]
      have h_eq : (⟨0, (compileFrag_bprod frag_f).numRegs_pos⟩
          : Fin P.numRegs) = zFin := Fin.ext rfl
      rw [h_eq]; change sC.regs zFin = 0; exact h_sC_z
    · -- acc_clone_eq.
      rw [h_runFor_eq]
      have h_eq : (⟨k + 7, by
          have : 0 < frag_f.numRegs := frag_f.numRegs_pos
          change k + 7 < k + 10 + frag_f.numRegs; omega⟩
          : Fin P.numRegs) = accCloneFin := Fin.ext rfl
      rw [h_eq]; change sC.regs accCloneFin = vAccIn; exact h_sC_accClone
    · -- factor_eq.
      rw [h_runFor_eq]
      have h_eq : (⟨k + 8, by
          have : 0 < frag_f.numRegs := frag_f.numRegs_pos
          change k + 8 < k + 10 + frag_f.numRegs; omega⟩
          : Fin P.numRegs) = factorFin := Fin.ext rfl
      rw [h_eq]; change sC.regs factorFin = vFOut - (j.val + 1)
      exact h_sC_factor
    · -- mulTmp_zero.
      rw [h_runFor_eq]
      have h_eq : (⟨k + 9, by
          have : 0 < frag_f.numRegs := frag_f.numRegs_pos
          change k + 9 < k + 10 + frag_f.numRegs; omega⟩
          : Fin P.numRegs) = mulTmpFin := Fin.ext rfl
      rw [h_eq]; change sC.regs mulTmpFin = 0; exact h_sC_mulTmp
    · -- acc_eq: vAccIn * (j.val + 1).
      rw [h_runFor_eq]
      have h_eq : (⟨1, by
          have : 0 < frag_f.numRegs := frag_f.numRegs_pos
          change 1 < k + 10 + frag_f.numRegs; omega⟩
          : Fin P.numRegs) = accFin := Fin.ext rfl
      rw [h_eq]; change sC.regs accFin = vAccIn * (j.val + 1)
      rw [h_sC_acc, Nat.mul_succ]
  -- Strict PC bound for all k' < 9 * vAccIn + 5.
  · intro k' h_k'
    change (URMState.runFor P sPre k').pc < bprod_mul_resetPC frag_f
    -- bprod_mul_resetPC = bprod_trBase frag_f + 20.
    have h_reset_eq : bprod_mul_resetPC frag_f
        = bprod_trBase frag_f + 20 := rfl
    have h_innerTop_eq : bprod_mul_innerTopPC frag_f
        = bprod_trBase frag_f + 8 := rfl
    have h_innerBody_eq : bprod_mul_innerBodyStartPC frag_f
        = bprod_trBase frag_f + 9 := rfl
    by_cases h_k0 : k' = 0
    · -- runFor 0 = sPre, pc = innerTopPC = trBase + 8 < trBase + 20.
      rw [h_k0, URMState.runFor_zero, h_sPre_pc, h_reset_eq,
        h_innerTop_eq]
      omega
    by_cases h_k1 : k' = 1
    · -- runFor 1 = sA, pc = innerBodyStartPC = trBase + 9 < trBase + 20.
      rw [h_k1, h_stepA, h_reset_eq]
      change bprod_mul_innerBodyStartPC frag_f < bprod_trBase frag_f + 20
      rw [h_innerBody_eq]
      omega
    -- 2 ≤ k'. Write k' = 2 + d.
    have h_k_ge_2 : 2 ≤ k' := by omega
    obtain ⟨d, rfl⟩ : ∃ d, k' = 2 + d := ⟨k' - 2, by omega⟩
    have h_d_bound : d < 9 * vAccIn + 3 := by omega
    have h_runFor_2 :
        URMState.runFor P sPre 2 = sB := by
      change URMState.runFor P sPre (1 + 1) = sB
      rw [URMState.runFor_add, h_stepA, h_stepB]
    rw [show (2 + d : ℕ) = 2 + d from rfl, URMState.runFor_add,
      h_runFor_2]
    -- Now we need to show (runFor sB d).pc < trBase + 20 for d < 9 * vAccIn + 3.
    -- preservingTransfer block runs for 9 * vAccIn + 2 steps from sB, PC in
    -- [trBase + 10, trBase + 18] during, hitting trBase + 19 at step 9*vAccIn+2.
    -- Then 1 more step (goto) lands at trBase + 8.
    by_cases h_d_pT : d ≤ 9 * vAccIn + 1
    · -- During preservingTransfer's strict-PC range. PC ≤ trBase + 18.
      have h_d_lt_pT : d < 9 * vAccIn + 2 := by omega
      have h_pc_bd := preservingTransfer_correct_pc_strict_bound P
        (bprod_trBase frag_f + 10) accCloneFin accFin mulTmpFin zFin
        h_disj_sd h_disj_st h_disj_dt h_disj_zs h_disj_zd h_disj_zt
        h_pT sB h_sB_pc h_sB_z h_sB_mulTmp vAccIn h_sB_accClone
        d h_d_lt_pT
      -- h_pc_bd : (runFor P sB d).pc ≤ bprod_trBase frag_f + 10 + 8
      rw [h_reset_eq]
      -- Goal : (runFor P sB d).pc < bprod_trBase frag_f + 20
      have h_arith : bprod_trBase frag_f + 10 + 8
          = bprod_trBase frag_f + 18 := by omega
      rw [h_arith] at h_pc_bd
      omega
    -- d ≥ 9*vAccIn + 2, d < 9*vAccIn + 3, so d = 9*vAccIn + 2.
    have h_d_eq : d = 9 * vAccIn + 2 := by omega
    rw [h_d_eq]
    -- runFor sB (9*vAccIn + 2) = sC, pc = trBase + 19 < trBase + 20.
    change sC.pc < bprod_mul_resetPC frag_f
    rw [h_sC_pc, h_reset_eq]
    omega

/-- Outer iteration of `compileFrag_bprod`'s inner-multiply loop: for
every `j ≤ vFOut`, there exists a combined step count
`T0 = j * (9 * vAccIn + 5)` after which
`compileFrag_bprod_mul_partial_invariant @ j` holds and throughout
these `T0` steps the intermediate PC stays strictly below
`bprod_mul_resetPC frag_f`. Induction on `j` chains the base case
`compileFrag_bprod_mul_partial_base` with
`compileFrag_bprod_mul_partial_step`. The `h_sPrep_z` parameter is
added beyond the plan signature because the base case requires the
`zReg = 0` witness, which `compileFrag_bprod_accUpdate_prep_post`
does not carry. Specialising `j := vFOut` recovers the unbounded
form `compileFrag_bprod_mul_partial`. -/
private theorem compileFrag_bprod_mul_partial_aux
    {k : ℕ}
    (frag_f : CompiledFragment (k + 1))
    (vAccIn vFOut : ℕ)
    (sPrep : URMState (compileFrag_bprod frag_f).toURMProgram)
    (h_sPrep_z : sPrep.regs ⟨0,
        (compileFrag_bprod frag_f).numRegs_pos⟩ = 0)
    (h_prep : compileFrag_bprod_accUpdate_prep_post
                frag_f vAccIn vFOut sPrep)
    (j : ℕ) (hj : j ≤ vFOut) :
    ∃ T0 : ℕ,
      T0 = j * (9 * vAccIn + 5) ∧
      compileFrag_bprod_mul_partial_invariant frag_f vAccIn vFOut
          j hj (URMState.runFor _ sPrep T0) ∧
      (∀ k' < T0,
        (URMState.runFor _ sPrep k').pc
          < bprod_mul_resetPC frag_f) := by
  let P : URMProgram (k + 1) := (compileFrag_bprod frag_f).toURMProgram
  induction j with
  | zero =>
    refine ⟨0, ?_, ?_, ?_⟩
    · -- 0 = 0 * (9 * vAccIn + 5).
      omega
    · -- partial_invariant @ 0 from the base case.
      change compileFrag_bprod_mul_partial_invariant frag_f vAccIn vFOut
        0 hj (URMState.runFor _ sPrep 0)
      rw [URMState.runFor_zero]
      exact compileFrag_bprod_mul_partial_base frag_f vAccIn vFOut sPrep
        h_sPrep_z h_prep
    · -- Strict PC bound is vacuous for k' < 0.
      intro k' hk'
      exact absurd hk' (Nat.not_lt_zero k')
  | succ j' ih =>
    have hj' : j' ≤ vFOut := Nat.le_of_succ_le hj
    have hj'_lt : j' < vFOut := hj
    obtain ⟨T_j', hT_j'_eq, h_inv_j', h_strict_j'⟩ := ih hj'
    let j_fin : Fin vFOut := ⟨j', hj'_lt⟩
    let sInv : URMState P := URMState.runFor P sPrep T_j'
    obtain ⟨T_step, hT_step_eq, h_inv_succ, h_strict_step⟩ :=
      compileFrag_bprod_mul_partial_step frag_f vAccIn vFOut j_fin sInv
        h_inv_j'
    refine ⟨T_j' + T_step, ?_, ?_, ?_⟩
    · -- T_j' + T_step = (j' + 1) * (9 * vAccIn + 5).
      rw [hT_j'_eq, hT_step_eq]
      have : (j' + 1) * (9 * vAccIn + 5)
          = j' * (9 * vAccIn + 5) + (9 * vAccIn + 5) := by
        rw [Nat.succ_mul]
      omega
    · -- partial_invariant @ (j' + 1) via runFor_add.
      have h_compose :
          URMState.runFor _ sPrep (T_j' + T_step)
            = URMState.runFor _ sInv T_step := by
        change URMState.runFor P sPrep (T_j' + T_step)
          = URMState.runFor P sInv T_step
        rw [URMState.runFor_add]
      rw [h_compose]
      change compileFrag_bprod_mul_partial_invariant frag_f vAccIn vFOut
        (j' + 1) hj (URMState.runFor P sInv T_step)
      exact h_inv_succ
    · -- Strict PC bound on the combined interval.
      intro k' hk'
      change (URMState.runFor P sPrep k').pc < bprod_mul_resetPC frag_f
      rcases Nat.lt_or_ge k' T_j' with h_lo | h_hi
      · exact h_strict_j' k' h_lo
      · let k'' : ℕ := k' - T_j'
        have hk''_lt : k'' < T_step := by
          change k' - T_j' < T_step; omega
        have h_split : k' = T_j' + k'' := by
          change k' = T_j' + (k' - T_j'); omega
        have h_runFor_split :
            URMState.runFor P sPrep k'
              = URMState.runFor P sInv k'' := by
          rw [h_split, URMState.runFor_add]
        rw [h_runFor_split]
        exact h_strict_step k'' hk''_lt

/-- Outer iteration of `compileFrag_bprod`'s inner-multiply loop at
`j = vFOut`: combines `compileFrag_bprod_mul_partial_aux` specialised
at the unbounded form with a register-preservation conjunct.

The preservation conjunct excludes exactly three register indices:
the live accumulator `1` (target of the per-iteration add), the
multiplicative factor `k + 8` (decremented each iteration), and the
inner-multiply scratch `k + 9` (touched mid-`preservingTransfer` even
though restored to zero at each iteration's end). The destructive
accumulator clone `k + 7` is NOT excluded: each
`preservingTransfer` restores it before exiting, so it carries its
input value `vAccIn` throughout. Preservation is established by
re-inducting on `j` and observing that the per-step body
(`jumpZ` + `dec factorFin` + `preservingTransfer accClone acc mulTmp`
+ `jumpZ`) writes only registers in `{1, k + 8, k + 9}`. -/
private theorem compileFrag_bprod_mul_partial
    {k : ℕ}
    (frag_f : CompiledFragment (k + 1))
    (vAccIn vFOut : ℕ)
    (sPrep : URMState (compileFrag_bprod frag_f).toURMProgram)
    (h_sPrep_z : sPrep.regs ⟨0,
        (compileFrag_bprod frag_f).numRegs_pos⟩ = 0)
    (h_prep : compileFrag_bprod_accUpdate_prep_post
                frag_f vAccIn vFOut sPrep) :
    ∃ T0 : ℕ,
      T0 = vFOut * (9 * vAccIn + 5) ∧
      compileFrag_bprod_mul_partial_invariant frag_f vAccIn vFOut
          vFOut (Nat.le_refl _) (URMState.runFor _ sPrep T0) ∧
      (∀ q : Fin (compileFrag_bprod frag_f).toURMProgram.numRegs,
        q.val ≠ 1 → q.val ≠ k + 8 → q.val ≠ k + 9 →
        (URMState.runFor _ sPrep T0).regs q = sPrep.regs q) ∧
      (∀ k' < T0,
        (URMState.runFor _ sPrep k').pc
          < bprod_mul_resetPC frag_f) := by
  let P : URMProgram (k + 1) := (compileFrag_bprod frag_f).toURMProgram
  -- Strengthened induction on j capturing the preservation conjunct
  -- alongside the existing partial_aux clauses.
  have h_aux : ∀ (j : ℕ) (hj : j ≤ vFOut),
      ∃ T0 : ℕ,
        T0 = j * (9 * vAccIn + 5) ∧
        compileFrag_bprod_mul_partial_invariant frag_f vAccIn vFOut
            j hj (URMState.runFor _ sPrep T0) ∧
        (∀ q : Fin P.numRegs,
          q.val ≠ 1 → q.val ≠ k + 8 → q.val ≠ k + 9 →
          (URMState.runFor _ sPrep T0).regs q = sPrep.regs q) ∧
        (∀ k' < T0,
          (URMState.runFor _ sPrep k').pc
            < bprod_mul_resetPC frag_f) := by
    intro j
    induction j with
    | zero =>
      intro hj
      refine ⟨0, by omega, ?_, ?_, ?_⟩
      · change compileFrag_bprod_mul_partial_invariant frag_f vAccIn vFOut
          0 hj (URMState.runFor _ sPrep 0)
        rw [URMState.runFor_zero]
        exact compileFrag_bprod_mul_partial_base frag_f vAccIn vFOut sPrep
          h_sPrep_z h_prep
      · -- Preservation vacuous: runFor 0 = sPrep.
        intro q _ _ _
        rw [URMState.runFor_zero]
      · intro k' hk'
        exact absurd hk' (Nat.not_lt_zero k')
    | succ j' ih =>
      intro hj
      have hj' : j' ≤ vFOut := Nat.le_of_succ_le hj
      have hj'_lt : j' < vFOut := hj
      obtain ⟨T_j', hT_j'_eq, h_inv_j', h_pres_j', h_strict_j'⟩ := ih hj'
      let j_fin : Fin vFOut := ⟨j', hj'_lt⟩
      let sInv : URMState P := URMState.runFor P sPrep T_j'
      obtain ⟨T_step, hT_step_eq, h_inv_succ, h_strict_step⟩ :=
        compileFrag_bprod_mul_partial_step frag_f vAccIn vFOut j_fin sInv
          h_inv_j'
      refine ⟨T_j' + T_step, ?_, ?_, ?_, ?_⟩
      · rw [hT_j'_eq, hT_step_eq]
        have : (j' + 1) * (9 * vAccIn + 5)
            = j' * (9 * vAccIn + 5) + (9 * vAccIn + 5) := by
          rw [Nat.succ_mul]
        omega
      · have h_compose :
            URMState.runFor _ sPrep (T_j' + T_step)
              = URMState.runFor _ sInv T_step := by
          change URMState.runFor P sPrep (T_j' + T_step)
            = URMState.runFor P sInv T_step
          rw [URMState.runFor_add]
        rw [h_compose]
        change compileFrag_bprod_mul_partial_invariant frag_f vAccIn vFOut
          (j' + 1) hj (URMState.runFor P sInv T_step)
        exact h_inv_succ
      · -- Preservation @ (j' + 1): re-derive the step body's register
        -- writes from instruction-level analysis, then compose with the
        -- IH preservation across [0, T_j'].
        intro q hq1 hq_factor hq_mulTmp
        -- Unfold the combined runFor as runFor sInv T_step composed
        -- with runFor sPrep T_j'.
        have h_compose :
            URMState.runFor _ sPrep (T_j' + T_step)
              = URMState.runFor _ sInv T_step := by
          change URMState.runFor P sPrep (T_j' + T_step)
            = URMState.runFor P sInv T_step
          rw [URMState.runFor_add]
        rw [h_compose]
        -- It suffices to show
        --   (runFor sInv T_step).regs q = sInv.regs q
        -- and then chain with the IH preservation
        --   sInv.regs q = sPrep.regs q.
        have h_pres_step :
            (URMState.runFor _ sInv T_step).regs q = sInv.regs q := by
          -- Reproduce the per-step body analysis from
          -- compileFrag_bprod_mul_partial_step. Re-derive the
          -- intermediate states sA/sB/sC/sD locally.
          obtain ⟨h_acc_lt, h_accClone_lt, h_z_lt, h_factor_lt,
              h_mulTmp_lt, h_top, h_dec, h_pT, h_goto⟩ :=
            compileFrag_bprod_accUpdate_innerBody_instr_at frag_f
          let accFin : Fin P.numRegs := ⟨1, h_acc_lt⟩
          let accCloneFin : Fin P.numRegs := ⟨k + 7, h_accClone_lt⟩
          let zFin : Fin P.numRegs := ⟨0, h_z_lt⟩
          let factorFin : Fin P.numRegs := ⟨k + 8, h_factor_lt⟩
          let mulTmpFin : Fin P.numRegs := ⟨k + 9, h_mulTmp_lt⟩
          -- Recover the invariant projections at sInv.
          have h_sInv_pc : sInv.pc = bprod_mul_innerTopPC frag_f :=
            h_inv_j'.pc_eq
          have h_sInv_zReg : sInv.regs zFin = 0 := by
            have h_eq : (⟨0, (compileFrag_bprod frag_f).numRegs_pos⟩
                : Fin P.numRegs) = zFin := Fin.ext rfl
            rw [← h_eq]; exact h_inv_j'.zReg_zero
          have h_sInv_factor : sInv.regs factorFin = vFOut - j' := by
            have h_eq : (⟨k + 8, by
                have : 0 < frag_f.numRegs := frag_f.numRegs_pos
                change k + 8 < k + 10 + frag_f.numRegs; omega⟩
                : Fin P.numRegs) = factorFin := Fin.ext rfl
            rw [← h_eq]; exact h_inv_j'.factor_eq
          have h_sInv_accClone : sInv.regs accCloneFin = vAccIn := by
            have h_eq : (⟨k + 7, by
                have : 0 < frag_f.numRegs := frag_f.numRegs_pos
                change k + 7 < k + 10 + frag_f.numRegs; omega⟩
                : Fin P.numRegs) = accCloneFin := Fin.ext rfl
            rw [← h_eq]; exact h_inv_j'.acc_clone_eq
          have h_sInv_mulTmp : sInv.regs mulTmpFin = 0 := by
            have h_eq : (⟨k + 9, by
                have : 0 < frag_f.numRegs := frag_f.numRegs_pos
                change k + 9 < k + 10 + frag_f.numRegs; omega⟩
                : Fin P.numRegs) = mulTmpFin := Fin.ext rfl
            rw [← h_eq]; exact h_inv_j'.mulTmp_zero
          -- Disjointness facts on q against the four written registers.
          have h_q_ne_acc : q ≠ accFin := by
            intro hh
            exact hq1 (congrArg Fin.val hh)
          have h_q_ne_factor : q ≠ factorFin := by
            intro hh
            exact hq_factor (congrArg Fin.val hh)
          have h_q_ne_mulTmp : q ≠ mulTmpFin := by
            intro hh
            exact hq_mulTmp (congrArg Fin.val hh)
          -- Step A: jumpZ doesn't write registers.
          have h_factor_pos : vFOut - j' ≠ 0 := by
            have : j' < vFOut := hj'_lt
            omega
          have h_top' : P.instrs[bprod_mul_innerTopPC frag_f]?
              = some (URMInstr.jumpZ factorFin
                  (bprod_mul_resetPC frag_f)
                  (bprod_mul_innerBodyStartPC frag_f)) := h_top
          set sA : URMState P :=
            { pc := bprod_mul_innerBodyStartPC frag_f
              regs := sInv.regs }
          have h_stepA : URMState.runFor P sInv 1 = sA := by
            change URMState.runFor P sInv (0 + 1) = sA
            rw [URMState.runFor_succ,
              URMState.runFor_zero,
              URMState.step_of_getElem?_jumpZ P sInv
                (bprod_mul_innerTopPC frag_f) factorFin
                (bprod_mul_resetPC frag_f)
                (bprod_mul_innerBodyStartPC frag_f) h_sInv_pc h_top']
            have h_neq : sInv.regs factorFin ≠ 0 := by
              rw [h_sInv_factor]; exact h_factor_pos
            simp only [h_neq, ↓reduceIte]
            rfl
          have h_sA_q : sA.regs q = sInv.regs q := rfl
          -- Step B: dec factorFin updates only factorFin.
          have h_sA_pc : sA.pc = bprod_mul_innerBodyStartPC frag_f := rfl
          have h_dec' : P.instrs[bprod_mul_innerBodyStartPC frag_f]?
              = some (URMInstr.dec factorFin) := h_dec
          set sB : URMState P :=
            { pc := bprod_trBase frag_f + 10
              regs := Function.update sA.regs factorFin
                (sA.regs factorFin - 1) }
          have h_stepB : URMState.runFor P sA 1 = sB := by
            change URMState.runFor P sA (0 + 1) = sB
            rw [URMState.runFor_succ,
              URMState.runFor_zero,
              URMState.step_of_getElem?_dec P sA
                (bprod_mul_innerBodyStartPC frag_f) factorFin
                h_sA_pc h_dec']
            rfl
          have h_sB_q : sB.regs q = sInv.regs q := by
            change Function.update sA.regs factorFin
                (sA.regs factorFin - 1) q = sInv.regs q
            rw [Function.update_of_ne h_q_ne_factor]
          -- preservingTransfer block: from sB, run 9 * vAccIn + 2 steps.
          have h_disj_sd : accCloneFin ≠ accFin := by
            intro hh
            have : (k + 7 : ℕ) = 1 := congrArg Fin.val hh; omega
          have h_disj_st : accCloneFin ≠ mulTmpFin := by
            intro hh
            have : (k + 7 : ℕ) = k + 9 := congrArg Fin.val hh; omega
          have h_disj_dt : accFin ≠ mulTmpFin := by
            intro hh
            have : (1 : ℕ) = k + 9 := congrArg Fin.val hh; omega
          have h_disj_zs : zFin ≠ accCloneFin := by
            intro hh
            have : (0 : ℕ) = k + 7 := congrArg Fin.val hh; omega
          have h_disj_zd : zFin ≠ accFin := by
            intro hh
            have : (0 : ℕ) = 1 := congrArg Fin.val hh; omega
          have h_disj_zt : zFin ≠ mulTmpFin := by
            intro hh
            have : (0 : ℕ) = k + 9 := congrArg Fin.val hh; omega
          have h_sB_pc : sB.pc = bprod_trBase frag_f + 10 := rfl
          have h_disj_z_factor : zFin ≠ factorFin := by
            intro hh
            have : (0 : ℕ) = k + 8 := congrArg Fin.val hh; omega
          have h_sB_z : sB.regs zFin = 0 := by
            change Function.update sA.regs factorFin
                (sA.regs factorFin - 1) zFin = 0
            rw [Function.update_of_ne h_disj_z_factor]; exact h_sInv_zReg
          have h_disj_mulTmp_factor : mulTmpFin ≠ factorFin := by
            intro hh
            have : (k + 9 : ℕ) = k + 8 := congrArg Fin.val hh; omega
          have h_sB_mulTmp : sB.regs mulTmpFin = 0 := by
            change Function.update sA.regs factorFin
                (sA.regs factorFin - 1) mulTmpFin = 0
            rw [Function.update_of_ne h_disj_mulTmp_factor]
            exact h_sInv_mulTmp
          have h_disj_accClone_factor : accCloneFin ≠ factorFin := by
            intro hh
            have : (k + 7 : ℕ) = k + 8 := congrArg Fin.val hh; omega
          have h_sB_accClone : sB.regs accCloneFin = vAccIn := by
            change Function.update sA.regs factorFin
                (sA.regs factorFin - 1) accCloneFin = vAccIn
            rw [Function.update_of_ne h_disj_accClone_factor]
            exact h_sInv_accClone
          obtain ⟨hC_pc, _hC_dst, _hC_src, _hC_tmp, _hC_z, hC_oth⟩ :=
            preservingTransfer_correct P (bprod_trBase frag_f + 10)
              accCloneFin accFin mulTmpFin zFin
              h_disj_sd h_disj_st h_disj_dt h_disj_zs h_disj_zd h_disj_zt
              h_pT sB h_sB_pc h_sB_z h_sB_mulTmp vAccIn h_sB_accClone
          set sC : URMState P :=
            URMState.runFor P sB (9 * vAccIn + 2)
          have h_sC_q : sC.regs q = sInv.regs q := by
            change (URMState.runFor P sB (9 * vAccIn + 2)).regs q
              = sInv.regs q
            rw [hC_oth q h_q_ne_acc, h_sB_q]
          have h_sC_pc : sC.pc = bprod_trBase frag_f + 19 := by
            change (URMState.runFor P sB (9 * vAccIn + 2)).pc
              = bprod_trBase frag_f + 19
            rw [hC_pc]
          -- Step D: jumpZ on zFin (which is 0), preserves regs.
          have h_sC_z : sC.regs zFin = 0 := by
            rw [hC_oth zFin h_disj_zd, h_sB_z]
          have h_goto' : P.instrs[bprod_trBase frag_f + 19]?
              = some (URMInstr.jumpZ zFin
                  (bprod_mul_innerTopPC frag_f)
                  (bprod_mul_innerTopPC frag_f)) := h_goto
          set sD : URMState P :=
            { pc := bprod_mul_innerTopPC frag_f
              regs := sC.regs }
          have h_stepD : URMState.runFor P sC 1 = sD := by
            change URMState.runFor P sC (0 + 1) = sD
            rw [URMState.runFor_succ,
              URMState.runFor_zero,
              URMState.step_of_getElem?_jumpZ P sC
                (bprod_trBase frag_f + 19) zFin
                (bprod_mul_innerTopPC frag_f)
                (bprod_mul_innerTopPC frag_f) h_sC_pc h_goto']
            simp only [h_sC_z, ↓reduceIte]
            rfl
          have h_sD_q : sD.regs q = sInv.regs q := h_sC_q
          -- Compose: runFor sInv (9 * vAccIn + 5) = sD.
          have h_runFor_eq :
              URMState.runFor P sInv (9 * vAccIn + 5) = sD := by
            have h_sum : (9 * vAccIn + 5 : ℕ)
                = 1 + (1 + ((9 * vAccIn + 2) + 1)) := by omega
            rw [h_sum, URMState.runFor_add, h_stepA,
              URMState.runFor_add, h_stepB, URMState.runFor_add]
            change URMState.runFor P
              (URMState.runFor P sB (9 * vAccIn + 2)) 1 = sD
            exact h_stepD
          have h_T_step_val : T_step = 9 * vAccIn + 5 := hT_step_eq
          rw [h_T_step_val, h_runFor_eq]
          exact h_sD_q
        -- Chain with IH preservation.
        rw [h_pres_step]
        change sInv.regs q = sPrep.regs q
        exact h_pres_j' q hq1 hq_factor hq_mulTmp
      · -- Strict PC bound on combined interval.
        intro k' hk'
        change (URMState.runFor P sPrep k').pc < bprod_mul_resetPC frag_f
        rcases Nat.lt_or_ge k' T_j' with h_lo | h_hi
        · exact h_strict_j' k' h_lo
        · let k'' : ℕ := k' - T_j'
          have hk''_lt : k'' < T_step := by
            change k' - T_j' < T_step; omega
          have h_split : k' = T_j' + k'' := by
            change k' = T_j' + (k' - T_j'); omega
          have h_runFor_split :
              URMState.runFor P sPrep k'
                = URMState.runFor P sInv k'' := by
            rw [h_split, URMState.runFor_add]
          rw [h_runFor_split]
          exact h_strict_step k'' hk''_lt
  exact h_aux vFOut (Nat.le_refl _)

set_option maxHeartbeats 800000 in
-- Segment-decomposition discharger (boundedness reconstruction plus
-- per-position lookup of `accUpdate ++ epilogue` at offset 20)
-- exceeds the default `whnf` heartbeat budget.
/-- Instruction-presence discharger for the inner-multiply reset
instruction of `compileFrag_bprod`'s accumulator-update block: at PC
`bprod_mul_resetPC frag_f` (= `bprod_trBase frag_f + 20`), the outer
program holds the `URMInstr.assign ⟨k + 7, _⟩ 0` instruction that
zeroes the accumulator clone after the inner-multiply loop exits.
Mirrors the segment-decomposition pattern of
`compileFrag_bprod_accUpdate_innerBody_instr_at`, specialised to a
single instruction at offset `20` within `accUpdate ++ epilogue`. -/
private theorem compileFrag_bprod_accUpdate_reset_instr_at
    {k : ℕ}
    (frag_f : CompiledFragment (k + 1)) :
    let outer := (compileFrag_bprod frag_f).toURMProgram
    ∃ h : k + 7 < outer.numRegs,
      outer.instrs[bprod_mul_resetPC frag_f]?
        = some (URMInstr.assign ⟨k + 7, h⟩ 0) := by
  intro outer
  let vAcc : ℕ := 1
  let vBoundIn : ℕ := 2
  let vX : ℕ := k + 3
  let vI : ℕ := k + 4
  let tmp1 : ℕ := k + 5
  let tmp2 : ℕ := k + 6
  let vAccClone : ℕ := k + 7
  let vFactor : ℕ := k + 8
  let vMulTmp : ℕ := k + 9
  let fBase : ℕ := k + 10
  let nR : ℕ := fBase + frag_f.numRegs
  let topPC : ℕ := 14
  let bodyStartPC : ℕ := 15
  let prologueBase : ℕ := 16 + frag_f.numRegs
  let bodyPCBase : ℕ := 16 + frag_f.numRegs + 9 * (k + 1)
  let fBodyLen : ℕ := frag_f.instrs.size - 1
  let trBase : ℕ := bodyPCBase + fBodyLen
  let exitPC : ℕ := trBase + 23
  let prelude : List URMInstrRaw :=
    [ .assignR 0 0,
      .assignR vAcc 0,
      .assignR vX 0,
      .assignR vI 0 ]
        ++ URMRaw.preservingTransfer 4 vBoundIn vX tmp2
        ++ [ .incR vAcc ]
  let loopTop : List URMInstrRaw :=
    [ .jumpZR vX exitPC bodyStartPC,
      .decR vX ]
  let zeroSweep : List URMInstrRaw :=
    bsum_zeroSweep frag_f fBase
  let prologue : List URMInstrRaw :=
    (List.finRange (k + 1)).flatMap fun s =>
      bsum_prologueBlock frag_f fBase tmp1 prologueBase s
  let fBody : List URMInstrRaw :=
    frag_f.instrs.pop.toList.map fun ins =>
      URMInstrRaw.reindexShift fBase bodyPCBase (toRawOfBounded ins)
  let accUpdate : List URMInstrRaw :=
    URMRaw.transferLoop trBase vAcc vAccClone
      ++ URMRaw.transferLoop (trBase + 4)
          (fBase + frag_f.outputReg.val) vFactor
      ++ [ .jumpZR vFactor (trBase + 20) (trBase + 9),
           .decR vFactor ]
      ++ URMRaw.preservingTransfer (trBase + 10)
          vAccClone vAcc vMulTmp
      ++ [ URMRaw.goto (trBase + 8),
           .assignR vAccClone 0 ]
  let epilogue : List URMInstrRaw :=
    [ .incR vI, URMRaw.goto topPC, .stopR ]
  let rawList : List URMInstrRaw :=
    prelude ++ loopTop ++ zeroSweep ++ prologue ++ fBody
      ++ accUpdate ++ epilogue
  have h_prelude_len : prelude.length = 14 := by
    change ([URMInstrRaw.assignR 0 0, URMInstrRaw.assignR vAcc 0,
        URMInstrRaw.assignR vX 0, URMInstrRaw.assignR vI 0]
        ++ URMRaw.preservingTransfer 4 vBoundIn vX tmp2
        ++ [URMInstrRaw.incR vAcc]).length = 14
    simp only [List.length_append, List.length_cons, List.length_nil,
      URMRaw.preservingTransfer, URMRaw.goto]
  have h_loopTop_len : loopTop.length = 2 := by
    change ([URMInstrRaw.jumpZR vX exitPC bodyStartPC,
      URMInstrRaw.decR vX] : List URMInstrRaw).length = 2
    simp only [List.length_cons, List.length_nil]
  have h_zeroSweep_len : zeroSweep.length = frag_f.numRegs := by
    change ((List.finRange frag_f.numRegs).map _).length = _
    rw [List.length_map, List.length_finRange]
  have h_prologue_len : prologue.length = 9 * (k + 1) := by
    change ((List.finRange (k + 1)).flatMap fun s =>
        bsum_prologueBlock frag_f fBase tmp1 prologueBase s).length
        = 9 * (k + 1)
    have h_each : ∀ s : Fin (k + 1),
        (bsum_prologueBlock frag_f fBase tmp1 prologueBase s).length = 9 :=
      fun _ => rfl
    have h_aux : ∀ (l : List (Fin (k + 1))),
        (l.flatMap fun s =>
            bsum_prologueBlock frag_f fBase tmp1 prologueBase s).length
          = 9 * l.length := by
      intro l
      induction l with
      | nil => rfl
      | cons hd tl ih_in =>
        rw [List.flatMap_cons, List.length_append, ih_in, h_each hd,
          List.length_cons]
        omega
    rw [h_aux, List.length_finRange]
  have h_fBody_len : fBody.length = frag_f.instrs.size - 1 := by
    change (frag_f.instrs.pop.toList.map fun ins =>
        URMInstrRaw.reindexShift fBase bodyPCBase
          (toRawOfBounded ins)).length = _
    rw [List.length_map, Array.length_toList, Array.size_pop]
  have h_accUpdate_len : accUpdate.length = 21 := by
    change (URMRaw.transferLoop trBase vAcc vAccClone
        ++ URMRaw.transferLoop (trBase + 4)
            (fBase + frag_f.outputReg.val) vFactor
        ++ [URMInstrRaw.jumpZR vFactor (trBase + 20) (trBase + 9),
            URMInstrRaw.decR vFactor]
        ++ URMRaw.preservingTransfer (trBase + 10)
            vAccClone vAcc vMulTmp
        ++ [URMRaw.goto (trBase + 8),
            URMInstrRaw.assignR vAccClone 0]).length = 21
    simp only [URMRaw.transferLoop, URMRaw.preservingTransfer,
      URMRaw.goto, List.length_append, List.length_cons,
      List.length_nil]
  have h_epilogue_len : epilogue.length = 3 := by
    change ([URMInstrRaw.incR vI, URMRaw.goto topPC,
      URMInstrRaw.stopR] : List URMInstrRaw).length = 3
    simp only [List.length_cons, List.length_nil]
  have h_numRegs_eq : outer.numRegs = nR := rfl
  have h_accClone_lt : k + 7 < outer.numRegs := by
    rw [h_numRegs_eq]
    have : 0 < frag_f.numRegs := frag_f.numRegs_pos
    change k + 7 < fBase + frag_f.numRegs; omega
  refine ⟨h_accClone_lt, ?_⟩
  -- Reconstruct the boundedness witness on rawList.
  have hAcc : vAcc + 1 ≤ nR := by
    change 1 + 1 ≤ k + 10 + frag_f.numRegs
    have : 0 < frag_f.numRegs := frag_f.numRegs_pos; omega
  have hBoundIn : vBoundIn + 1 ≤ nR := by
    change 2 + 1 ≤ k + 10 + frag_f.numRegs
    have : 0 < frag_f.numRegs := frag_f.numRegs_pos; omega
  have hVX : vX + 1 ≤ nR := by
    change k + 3 + 1 ≤ k + 10 + frag_f.numRegs
    have : 0 < frag_f.numRegs := frag_f.numRegs_pos; omega
  have hVI : vI + 1 ≤ nR := by
    change k + 4 + 1 ≤ k + 10 + frag_f.numRegs
    have : 0 < frag_f.numRegs := frag_f.numRegs_pos; omega
  have hTmp1 : tmp1 + 1 ≤ nR := by
    change k + 5 + 1 ≤ k + 10 + frag_f.numRegs
    have : 0 < frag_f.numRegs := frag_f.numRegs_pos; omega
  have hTmp2 : tmp2 + 1 ≤ nR := by
    change k + 6 + 1 ≤ k + 10 + frag_f.numRegs
    have : 0 < frag_f.numRegs := frag_f.numRegs_pos; omega
  have hAccClone : vAccClone + 1 ≤ nR := by
    change k + 7 + 1 ≤ k + 10 + frag_f.numRegs
    have : 0 < frag_f.numRegs := frag_f.numRegs_pos; omega
  have hFactor : vFactor + 1 ≤ nR := by
    change k + 8 + 1 ≤ k + 10 + frag_f.numRegs
    have : 0 < frag_f.numRegs := frag_f.numRegs_pos; omega
  have hMulTmp : vMulTmp + 1 ≤ nR := by
    change k + 9 + 1 ≤ k + 10 + frag_f.numRegs
    have : 0 < frag_f.numRegs := frag_f.numRegs_pos; omega
  have hFOut : fBase + frag_f.outputReg.val + 1 ≤ nR := by
    have : frag_f.outputReg.val < frag_f.numRegs :=
      frag_f.outputReg.isLt
    change fBase + frag_f.outputReg.val + 1 ≤ fBase + frag_f.numRegs
    omega
  have hPrologueSrc : ∀ s : Fin (k + 1),
      bsum_prologueSrc k s + 1 ≤ nR := by
    intro s
    have hs : s.val < k + 1 := s.isLt
    simp only [bsum_prologueSrc, nR, fBase]
    split <;> omega
  have hFIn : ∀ s : Fin (k + 1),
      fBase + (frag_f.inputRegs s).val + 1 ≤ nR := by
    intro s
    have : (frag_f.inputRegs s).val < frag_f.numRegs :=
      (frag_f.inputRegs s).isLt
    change fBase + (frag_f.inputRegs s).val + 1
        ≤ fBase + frag_f.numRegs
    omega
  have hPreludeBound : URMInstrRaw.boundedBy nR prelude := by
    intro ins hmem
    simp only [prelude, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hmem
    rcases hmem with ((h | h | h | h) | hpT) | h
    · rw [h]; simp only [URMInstrRaw.regBound]; omega
    · rw [h]; simp only [URMInstrRaw.regBound]; exact hAcc
    · rw [h]; simp only [URMInstrRaw.regBound]; exact hVX
    · rw [h]; simp only [URMInstrRaw.regBound]; exact hVI
    · exact boundedBy_preservingTransfer nR _ _ _ _
        hBoundIn hVX hTmp2 ins hpT
    · rw [h]; simp only [URMInstrRaw.regBound]; exact hAcc
  have hLoopTopBound : URMInstrRaw.boundedBy nR loopTop := by
    intro ins hmem
    simp only [loopTop, List.mem_cons, List.not_mem_nil,
      or_false] at hmem
    rcases hmem with h | h <;>
      (rw [h]; simp only [URMInstrRaw.regBound]; exact hVX)
  have hZeroSweepBound : URMInstrRaw.boundedBy nR zeroSweep := by
    have hBlock : fBase + frag_f.numRegs ≤ nR := Nat.le_refl _
    exact boundedBy_bsum_zeroSweep frag_f fBase nR hBlock
  have hPrologueBound : URMInstrRaw.boundedBy nR prologue := by
    intro ins hmem
    simp only [prologue, List.mem_flatMap] at hmem
    rcases hmem with ⟨s, _, hs⟩
    exact boundedBy_bsum_prologueBlock frag_f fBase tmp1
      prologueBase nR s (hPrologueSrc s) (hFIn s) hTmp1 ins hs
  have hFBodyBound : URMInstrRaw.boundedBy nR fBody := by
    intro ins hmem
    simp only [fBody, List.mem_map] at hmem
    rcases hmem with ⟨ins', _, heq⟩
    rw [← heq]
    have hb : (toRawOfBounded ins').regBound ≤ frag_f.numRegs :=
      regBound_toRawOfBounded_le ins'
    have hr := regBound_reindexShift_le_offset_add fBase
      bodyPCBase frag_f.numRegs (toRawOfBounded ins') hb
    change _ ≤ fBase + frag_f.numRegs
    omega
  have hAccUpdateBound : URMInstrRaw.boundedBy nR accUpdate := by
    intro ins hmem
    simp only [accUpdate, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hmem
    rcases hmem with
      ((((hTr1 | hTr2) | hOuter) | hInner) | hTail)
    · exact boundedBy_transferLoop nR _ _ _
        hAcc hAccClone ins hTr1
    · exact boundedBy_transferLoop nR _ _ _
        hFOut hFactor ins hTr2
    · rcases hOuter with h | h
      · rw [h]; simp only [URMInstrRaw.regBound]; exact hFactor
      · rw [h]; simp only [URMInstrRaw.regBound]; exact hFactor
    · exact boundedBy_preservingTransfer nR _ _ _ _
        hAccClone hAcc hMulTmp ins hInner
    · rcases hTail with h | h
      · rw [h]; simp only [URMRaw.goto, URMInstrRaw.regBound]
        omega
      · rw [h]; simp only [URMInstrRaw.regBound]; exact hAccClone
  have hEpilogueBound : URMInstrRaw.boundedBy nR epilogue := by
    intro ins hmem
    simp only [epilogue, URMRaw.goto, List.mem_cons,
      List.not_mem_nil, or_false] at hmem
    rcases hmem with h | h | h
    · rw [h]; simp only [URMInstrRaw.regBound]; exact hVI
    · rw [h]; simp only [URMInstrRaw.regBound]; omega
    · rw [h]; simp only [URMInstrRaw.regBound]; omega
  have hBoundOuter : URMInstrRaw.boundedBy nR rawList := by
    intro ins hmem
    simp only [rawList, List.mem_append] at hmem
    rcases hmem with
      (((((hP | hL') | hZ) | hPr) | hF) | hA) | hE
    · exact hPreludeBound ins hP
    · exact hLoopTopBound ins hL'
    · exact hZeroSweepBound ins hZ
    · exact hPrologueBound ins hPr
    · exact hFBodyBound ins hF
    · exact hAccUpdateBound ins hA
    · exact hEpilogueBound ins hE
  set preAc : List URMInstrRaw :=
    prelude ++ loopTop ++ zeroSweep ++ prologue ++ fBody
    with h_preAc_def
  have h_preAc_len : preAc.length = trBase := by
    rw [h_preAc_def]
    simp only [List.length_append]
    rw [h_prelude_len, h_loopTop_len, h_zeroSweep_len, h_prologue_len,
      h_fBody_len]
  -- The reset instruction is at offset 20 in accUpdate ++ epilogue.
  have h_lookup_raw : ∀ (h_idx_lt : trBase + 20 < rawList.length),
      rawList[trBase + 20]'h_idx_lt
        = (accUpdate ++ epilogue)[(20 : ℕ)]'(by
            rw [List.length_append, h_accUpdate_len, h_epilogue_len]
            decide) := by
    intro h_idx_lt
    have h_rawList_split :
        rawList = preAc ++ (accUpdate ++ epilogue) := by
      change prelude ++ loopTop ++ zeroSweep ++ prologue ++ fBody
        ++ accUpdate ++ epilogue = _
      rw [h_preAc_def]
      simp only [List.append_assoc]
    have h_pref_le : preAc.length ≤ trBase + 20 := by
      rw [h_preAc_len]; omega
    have h_idx_lt' :
        trBase + 20 < (preAc ++ (accUpdate ++ epilogue)).length := by
      simp only [List.length_append]
      rw [h_preAc_len, h_accUpdate_len, h_epilogue_len]
      omega
    have h_step1 :
        rawList[trBase + 20]'h_idx_lt
          = (preAc ++ (accUpdate ++ epilogue))[trBase + 20]'h_idx_lt' := by
      congr 1
    rw [h_step1, List.getElem_append_right h_pref_le]
    have h_idx_eq : trBase + 20 - preAc.length = 20 := by
      rw [h_preAc_len]; omega
    congr 1
  have h_ae_20 : (accUpdate ++ epilogue)[(20 : ℕ)]'(by
      rw [List.length_append, h_accUpdate_len, h_epilogue_len]; decide)
      = URMInstrRaw.assignR vAccClone 0 := rfl
  have h_ae_20_in_rawList :
      (accUpdate ++ epilogue)[(20 : ℕ)]'(by
        rw [List.length_append, h_accUpdate_len, h_epilogue_len]; decide)
        ∈ rawList := by
    have h_mem_ae :
        (accUpdate ++ epilogue)[(20 : ℕ)]'(by
          rw [List.length_append, h_accUpdate_len, h_epilogue_len]; decide)
          ∈ accUpdate ++ epilogue :=
      List.getElem_mem _
    rcases List.mem_append.mp h_mem_ae with hA | hE
    · apply List.mem_append.mpr; left
      apply List.mem_append.mpr; right; exact hA
    · apply List.mem_append.mpr; right; exact hE
  have h_idx_lt_outer : trBase + 20 < rawList.length := by
    have h_raw_len : rawList.length = preAc.length + 21 + 3 := by
      change (prelude ++ loopTop ++ zeroSweep ++ prologue ++ fBody
        ++ accUpdate ++ epilogue).length = preAc.length + 21 + 3
      rw [h_preAc_def]
      simp only [List.length_append]
      rw [h_accUpdate_len, h_epilogue_len]
    rw [h_raw_len, h_preAc_len]; omega
  change outer.instrs[bprod_mul_resetPC frag_f]? = _
  rw [show bprod_mul_resetPC frag_f = trBase + 20 from rfl]
  change (URMInstrRaw.toBoundedArray nR rawList hBoundOuter)[
      trBase + 20]? = _
  rw [URMInstrRaw.toBoundedArray_getElem? nR rawList hBoundOuter
      (trBase + 20) h_idx_lt_outer]
  have h_raw_eq := h_lookup_raw h_idx_lt_outer
  have h_combined : rawList[trBase + 20]'h_idx_lt_outer
      = URMInstrRaw.assignR vAccClone 0 := by
    rw [h_raw_eq]; exact h_ae_20
  apply congrArg some
  exact URMInstrRaw.toBounded_congr nR h_combined _ _

set_option maxHeartbeats 400000 in
-- Four-phase composition (prep + inner-mul loop + jumpZR + assignR)
-- triggers a large number of unfolding/whnf checks on the program's
-- segment structure, exceeding the default heartbeat budget.
/-- Full multiplicative `R^XY_Z` accumulator-update correctness for
`compileFrag_bprod`: starting at `bprod_trBase frag_f` with the
pre-state register witnesses, advancing
`(4 * vAccIn + 1) + (4 * vFOut + 1) + vFOut * (9 * vAccIn + 5) + 1 + 1`
URM steps lands the state at PC `bprod_incIPC frag_f` with the live
accumulator (register `1`) holding the product `vAccIn * vFOut`, the
destructive accumulator clone (register `k + 7`), the multiplicative
factor (register `k + 8`), the reindexed `f`-output slot (register
`(k + 10) + frag_f.outputReg.val`), and the inner-multiply scratch
(register `k + 9`) all reset to `0`, and every other register
preserved at its pre-state value. The four phases composed are: the
prep segment (two `transferLoop` blocks), the inner-multiply loop
(`vFOut` iterations of `9 * vAccIn + 5` steps), the exit `jumpZR
vFactor` (taken to `bprod_mul_resetPC frag_f` since `V_factor = 0`),
and the reset `assignR V_acc_clone 0` (advancing PC to
`bprod_incIPC frag_f`). -/
private theorem compileFrag_bprod_accUpdate_correct
    {k : ℕ}
    (frag_f : CompiledFragment (k + 1))
    (vAccIn vFOut : ℕ)
    (sPre : URMState (compileFrag_bprod frag_f).toURMProgram)
    (h_pc : sPre.pc = bprod_trBase frag_f)
    (h_zReg_zero : sPre.regs ⟨0,
        (compileFrag_bprod frag_f).numRegs_pos⟩ = 0)
    (h_acc : sPre.regs ⟨1, by
      have : 0 < frag_f.numRegs := frag_f.numRegs_pos
      change 1 < k + 10 + frag_f.numRegs; omega⟩ = vAccIn)
    (h_acc_clone_zero : sPre.regs ⟨k + 7, by
      have : 0 < frag_f.numRegs := frag_f.numRegs_pos
      change k + 7 < k + 10 + frag_f.numRegs; omega⟩ = 0)
    (h_fOut : sPre.regs ⟨(k + 10) + frag_f.outputReg.val, by
      have hO : frag_f.outputReg.val < frag_f.numRegs :=
        frag_f.outputReg.isLt
      change (k + 10) + frag_f.outputReg.val
        < k + 10 + frag_f.numRegs
      omega⟩ = vFOut)
    (h_factor_zero : sPre.regs ⟨k + 8, by
      have : 0 < frag_f.numRegs := frag_f.numRegs_pos
      change k + 8 < k + 10 + frag_f.numRegs; omega⟩ = 0)
    (h_mulTmp_zero : sPre.regs ⟨k + 9, by
      have : 0 < frag_f.numRegs := frag_f.numRegs_pos
      change k + 9 < k + 10 + frag_f.numRegs; omega⟩ = 0) :
    let totalSteps : ℕ :=
      (4 * vAccIn + 1) + (4 * vFOut + 1)
        + vFOut * (9 * vAccIn + 5) + 1 + 1
    let s' := URMState.runFor _ sPre totalSteps
    s'.pc = bprod_incIPC frag_f ∧
    s'.regs ⟨1, by
      have : 0 < frag_f.numRegs := frag_f.numRegs_pos
      change 1 < k + 10 + frag_f.numRegs; omega⟩ = vAccIn * vFOut ∧
    s'.regs ⟨k + 7, by
      have : 0 < frag_f.numRegs := frag_f.numRegs_pos
      change k + 7 < k + 10 + frag_f.numRegs; omega⟩ = 0 ∧
    s'.regs ⟨k + 8, by
      have : 0 < frag_f.numRegs := frag_f.numRegs_pos
      change k + 8 < k + 10 + frag_f.numRegs; omega⟩ = 0 ∧
    s'.regs ⟨(k + 10) + frag_f.outputReg.val, by
      have hO : frag_f.outputReg.val < frag_f.numRegs :=
        frag_f.outputReg.isLt
      change (k + 10) + frag_f.outputReg.val
        < k + 10 + frag_f.numRegs
      omega⟩ = 0 ∧
    s'.regs ⟨k + 9, by
      have : 0 < frag_f.numRegs := frag_f.numRegs_pos
      change k + 9 < k + 10 + frag_f.numRegs; omega⟩ = 0 ∧
    (∀ r : Fin (compileFrag_bprod frag_f).toURMProgram.numRegs,
        r.val ≠ 1 →
        r.val ≠ k + 7 →
        r.val ≠ k + 8 →
        r.val ≠ k + 9 →
        r.val ≠ (k + 10) + frag_f.outputReg.val →
        s'.regs r = sPre.regs r) := by
  let P : URMProgram (k + 1) := (compileFrag_bprod frag_f).toURMProgram
  set T_prep : ℕ := (4 * vAccIn + 1) + (4 * vFOut + 1) with h_T_prep_def
  set T_mul : ℕ := vFOut * (9 * vAccIn + 5) with h_T_mul_def
  -- Phase 1: prep segment.
  obtain ⟨h_prep_post, h_prep_pres⟩ :=
    compileFrag_bprod_accUpdate_prep_correct frag_f vAccIn vFOut sPre
      h_pc h_zReg_zero h_acc h_acc_clone_zero h_fOut h_factor_zero
      h_mulTmp_zero
  set sPrep : URMState P := URMState.runFor P sPre T_prep with h_sPrep_def
  -- Phase 2: inner-multiply loop.
  have h_sPrep_z : sPrep.regs ⟨0,
      (compileFrag_bprod frag_f).numRegs_pos⟩ = 0 := by
    -- zReg is preserved by the prep segment: index 0 is not in the
    -- prep preservation exclusion list {1, k+7, k+8, fOut}.
    have h_ne_1 : (0 : ℕ) ≠ 1 := by decide
    have h_ne_kp7 : (0 : ℕ) ≠ k + 7 := by omega
    have h_ne_kp8 : (0 : ℕ) ≠ k + 8 := by omega
    have h_ne_fOut : (0 : ℕ) ≠ (k + 10) + frag_f.outputReg.val := by omega
    have h_eq := h_prep_pres ⟨0, (compileFrag_bprod frag_f).numRegs_pos⟩
      h_ne_1 h_ne_kp7 h_ne_kp8 h_ne_fOut
    rw [h_eq]; exact h_zReg_zero
  obtain ⟨T0, hT0_eq, h_inv_final, h_pres_mul, _h_strict_mul⟩ :=
    compileFrag_bprod_mul_partial frag_f vAccIn vFOut sPrep h_sPrep_z
      h_prep_post
  have h_T0_eq_T_mul : T0 = T_mul := by rw [hT0_eq]
  set sMul : URMState P := URMState.runFor P sPrep T0 with h_sMul_def
  -- Phase 3: exit jumpZR.
  obtain ⟨h_accClone_lt_reset, h_reset_instr⟩ :=
    compileFrag_bprod_accUpdate_reset_instr_at frag_f
  obtain ⟨h_acc_lt, h_accClone_lt_ib, h_z_lt, h_factor_lt,
      h_mulTmp_lt, h_top, _h_dec, _h_pT, _h_goto⟩ :=
    compileFrag_bprod_accUpdate_innerBody_instr_at frag_f
  let factorFin : Fin P.numRegs := ⟨k + 8, h_factor_lt⟩
  have h_sMul_pc : sMul.pc = bprod_mul_innerTopPC frag_f :=
    h_inv_final.pc_eq
  have h_sMul_factor : sMul.regs factorFin = 0 := by
    have h_eq : (⟨k + 8, by
        have : 0 < frag_f.numRegs := frag_f.numRegs_pos
        change k + 8 < k + 10 + frag_f.numRegs; omega⟩
        : Fin P.numRegs) = factorFin := Fin.ext rfl
    rw [← h_eq, h_inv_final.factor_eq, Nat.sub_self]
  have h_top' : P.instrs[bprod_mul_innerTopPC frag_f]?
      = some (URMInstr.jumpZ factorFin
          (bprod_mul_resetPC frag_f)
          (bprod_mul_innerBodyStartPC frag_f)) := h_top
  set sJ : URMState P :=
    { pc := bprod_mul_resetPC frag_f
      regs := sMul.regs } with h_sJ_def
  have h_stepJ : URMState.runFor P sMul 1 = sJ := by
    change URMState.runFor P sMul (0 + 1) = sJ
    rw [URMState.runFor_succ,
      URMState.runFor_zero,
      URMState.step_of_getElem?_jumpZ P sMul
        (bprod_mul_innerTopPC frag_f) factorFin
        (bprod_mul_resetPC frag_f)
        (bprod_mul_innerBodyStartPC frag_f) h_sMul_pc h_top']
    simp only [h_sMul_factor, ↓reduceIte]
    rfl
  -- Phase 4: reset assignR.
  let accCloneFin : Fin P.numRegs := ⟨k + 7, h_accClone_lt_reset⟩
  have h_sJ_pc : sJ.pc = bprod_mul_resetPC frag_f := rfl
  have h_reset' : P.instrs[bprod_mul_resetPC frag_f]?
      = some (URMInstr.assign accCloneFin 0) := h_reset_instr
  set sFin : URMState P :=
    { pc := bprod_mul_resetPC frag_f + 1
      regs := Function.update sJ.regs accCloneFin 0 } with h_sFin_def
  have h_stepFin : URMState.runFor P sJ 1 = sFin := by
    change URMState.runFor P sJ (0 + 1) = sFin
    rw [URMState.runFor_succ,
      URMState.runFor_zero,
      URMState.step_of_getElem?_assign P sJ
        (bprod_mul_resetPC frag_f) accCloneFin 0 h_sJ_pc h_reset']
  -- Compose all four phases.
  have h_compose :
      URMState.runFor P sPre ((4 * vAccIn + 1) + (4 * vFOut + 1)
          + vFOut * (9 * vAccIn + 5) + 1 + 1) = sFin := by
    have h_split :
        ((4 * vAccIn + 1) + (4 * vFOut + 1)
          + vFOut * (9 * vAccIn + 5) + 1 + 1 : ℕ)
            = T_prep + (T_mul + (1 + 1)) := by omega
    rw [h_split, URMState.runFor_add]
    change URMState.runFor P sPrep (T_mul + (1 + 1)) = sFin
    rw [URMState.runFor_add]
    have h_runFor_Tmul :
        URMState.runFor P sPrep T_mul = sMul := by
      change URMState.runFor P sPrep T_mul
        = URMState.runFor P sPrep T0
      rw [h_T0_eq_T_mul]
    rw [h_runFor_Tmul, URMState.runFor_add]
    change URMState.runFor P (URMState.runFor P sMul 1) 1 = sFin
    rw [h_stepJ, h_stepFin]
  change (URMState.runFor P sPre ((4 * vAccIn + 1) + (4 * vFOut + 1)
      + vFOut * (9 * vAccIn + 5) + 1 + 1)).pc = bprod_incIPC frag_f ∧ _
  rw [h_compose]
  -- Conclude the 7 conjuncts.
  let accFin : Fin P.numRegs := ⟨1, h_acc_lt⟩
  let fOutFin : Fin P.numRegs :=
    ⟨(k + 10) + frag_f.outputReg.val, by
      have hO : frag_f.outputReg.val < frag_f.numRegs :=
        frag_f.outputReg.isLt
      change (k + 10) + frag_f.outputReg.val < k + 10 + frag_f.numRegs
      omega⟩
  let mulTmpFin : Fin P.numRegs := ⟨k + 9, h_mulTmp_lt⟩
  let zFin : Fin P.numRegs := ⟨0, h_z_lt⟩
  -- Disjointness lemmas.
  have h_ne_accClone_acc : accCloneFin ≠ accFin := by
    intro hh
    have : (k + 7 : ℕ) = 1 := congrArg Fin.val hh; omega
  have h_ne_accClone_factor : accCloneFin ≠ factorFin := by
    intro hh
    have : (k + 7 : ℕ) = k + 8 := congrArg Fin.val hh; omega
  have h_ne_accClone_fOut : accCloneFin ≠ fOutFin := by
    intro hh
    have : (k + 7 : ℕ) = (k + 10) + frag_f.outputReg.val :=
      congrArg Fin.val hh
    omega
  have h_ne_accClone_mulTmp : accCloneFin ≠ mulTmpFin := by
    intro hh
    have : (k + 7 : ℕ) = k + 9 := congrArg Fin.val hh; omega
  -- Project sMul invariant facts.
  have h_sMul_acc : sMul.regs accFin = vAccIn * vFOut := by
    have h_eq : (⟨1, by
        have : 0 < frag_f.numRegs := frag_f.numRegs_pos
        change 1 < k + 10 + frag_f.numRegs; omega⟩
        : Fin P.numRegs) = accFin := Fin.ext rfl
    rw [← h_eq]; exact h_inv_final.acc_eq
  have h_sMul_mulTmp : sMul.regs mulTmpFin = 0 := by
    have h_eq : (⟨k + 9, by
        have : 0 < frag_f.numRegs := frag_f.numRegs_pos
        change k + 9 < k + 10 + frag_f.numRegs; omega⟩
        : Fin P.numRegs) = mulTmpFin := Fin.ext rfl
    rw [← h_eq]; exact h_inv_final.mulTmp_zero
  -- For sMul.regs fOutFin, use prep_pres + mul_pres preservation.
  -- prep: fOut was reset to 0 by prep (prep_post.fOut_zero); mul_pres
  -- excludes only {1, k+8, k+9}, so fOut is preserved at 0.
  have h_ne_fOut_acc : (fOutFin : Fin P.numRegs).val ≠ 1 := by
    change (k + 10) + frag_f.outputReg.val ≠ 1; omega
  have h_ne_fOut_factor : (fOutFin : Fin P.numRegs).val ≠ k + 8 := by
    change (k + 10) + frag_f.outputReg.val ≠ k + 8; omega
  have h_ne_fOut_mulTmp : (fOutFin : Fin P.numRegs).val ≠ k + 9 := by
    change (k + 10) + frag_f.outputReg.val ≠ k + 9; omega
  have h_sPrep_fOut : sPrep.regs fOutFin = 0 := by
    have h_eq : (⟨(k + 10) + frag_f.outputReg.val, by
        have hO : frag_f.outputReg.val < frag_f.numRegs :=
          frag_f.outputReg.isLt
        change (k + 10) + frag_f.outputReg.val
          < k + 10 + frag_f.numRegs
        omega⟩ : Fin P.numRegs) = fOutFin := Fin.ext rfl
    rw [← h_eq]; exact h_prep_post.fOut_zero
  have h_sMul_fOut : sMul.regs fOutFin = 0 := by
    have h_pres :=
      h_pres_mul fOutFin h_ne_fOut_acc h_ne_fOut_factor h_ne_fOut_mulTmp
    rw [h_pres, h_sPrep_fOut]
  -- For sMul.regs accCloneFin, use the partial invariant.
  have h_sMul_accClone : sMul.regs accCloneFin = vAccIn := by
    have h_eq : (⟨k + 7, by
        have : 0 < frag_f.numRegs := frag_f.numRegs_pos
        change k + 7 < k + 10 + frag_f.numRegs; omega⟩
        : Fin P.numRegs) = accCloneFin := Fin.ext rfl
    rw [← h_eq]; exact h_inv_final.acc_clone_eq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- pc.
    change sFin.pc = bprod_incIPC frag_f
    change bprod_mul_resetPC frag_f + 1 = bprod_incIPC frag_f
    rfl
  · -- acc = vAccIn * vFOut: preserved by jumpZR (no write) and assignR
    -- (writes only accCloneFin).
    change sFin.regs ⟨1, _⟩ = vAccIn * vFOut
    change Function.update sJ.regs accCloneFin 0 ⟨1, h_acc_lt⟩
      = vAccIn * vFOut
    have h_acc_fin_eq : (⟨1, by
        have : 0 < frag_f.numRegs := frag_f.numRegs_pos
        change 1 < k + 10 + frag_f.numRegs; omega⟩
        : Fin P.numRegs) = accFin := Fin.ext rfl
    rw [Function.update_of_ne h_ne_accClone_acc.symm]
    change sMul.regs accFin = vAccIn * vFOut
    exact h_sMul_acc
  · -- accClone = 0 from the assignR write.
    change sFin.regs ⟨k + 7, _⟩ = 0
    change Function.update sJ.regs accCloneFin 0 ⟨k + 7, h_accClone_lt_ib⟩
      = 0
    have h_accClone_fin_eq : (⟨k + 7, h_accClone_lt_ib⟩ : Fin P.numRegs)
        = accCloneFin := Fin.ext rfl
    rw [h_accClone_fin_eq, Function.update_self]
  · -- factor = 0 from the partial invariant (preserved by jumpZR and
    -- assignR).
    change sFin.regs ⟨k + 8, _⟩ = 0
    change Function.update sJ.regs accCloneFin 0 ⟨k + 8, h_factor_lt⟩
      = 0
    have h_factor_fin_eq : (⟨k + 8, h_factor_lt⟩ : Fin P.numRegs)
        = factorFin := Fin.ext rfl
    rw [h_factor_fin_eq,
      Function.update_of_ne h_ne_accClone_factor.symm]
    change sMul.regs factorFin = 0
    exact h_sMul_factor
  · -- fOut = 0 from prep (set to 0) and mul preservation.
    change sFin.regs ⟨(k + 10) + frag_f.outputReg.val, _⟩ = 0
    change Function.update sJ.regs accCloneFin 0
        ⟨(k + 10) + frag_f.outputReg.val, _⟩ = 0
    have h_fOut_fin_eq : (⟨(k + 10) + frag_f.outputReg.val, by
        have hO : frag_f.outputReg.val < frag_f.numRegs :=
          frag_f.outputReg.isLt
        change (k + 10) + frag_f.outputReg.val
          < k + 10 + frag_f.numRegs
        omega⟩ : Fin P.numRegs) = fOutFin := Fin.ext rfl
    rw [h_fOut_fin_eq,
      Function.update_of_ne h_ne_accClone_fOut.symm]
    change sMul.regs fOutFin = 0
    exact h_sMul_fOut
  · -- mulTmp = 0 from the partial invariant.
    change sFin.regs ⟨k + 9, _⟩ = 0
    change Function.update sJ.regs accCloneFin 0
        ⟨k + 9, h_mulTmp_lt⟩ = 0
    have h_mulTmp_fin_eq : (⟨k + 9, h_mulTmp_lt⟩ : Fin P.numRegs)
        = mulTmpFin := Fin.ext rfl
    rw [h_mulTmp_fin_eq,
      Function.update_of_ne h_ne_accClone_mulTmp.symm]
    change sMul.regs mulTmpFin = 0
    exact h_sMul_mulTmp
  · -- Preservation: compose prep_pres with mul_pres, then with the
    -- jumpZR no-write and the assignR (which writes only accCloneFin).
    intro r h_ne_1 h_ne_kp7 h_ne_kp8 h_ne_kp9 h_ne_fOut'
    change sFin.regs r = sPre.regs r
    change Function.update sJ.regs accCloneFin 0 r = sPre.regs r
    have h_r_ne_accClone : r ≠ accCloneFin := by
      intro hh
      apply h_ne_kp7; exact congrArg Fin.val hh
    rw [Function.update_of_ne h_r_ne_accClone]
    change sMul.regs r = sPre.regs r
    -- mul_pres: r ≠ 1, k+8, k+9 ⇒ sMul.regs r = sPrep.regs r.
    have h_r_ne_acc : r.val ≠ 1 := h_ne_1
    have h_r_ne_factor : r.val ≠ k + 8 := h_ne_kp8
    have h_r_ne_mulTmp : r.val ≠ k + 9 := h_ne_kp9
    have h_pres_step :=
      h_pres_mul r h_r_ne_acc h_r_ne_factor h_r_ne_mulTmp
    rw [h_pres_step]
    -- prep_pres: r ≠ 1, k+7, k+8, fOut ⇒ sPrep.regs r = sPre.regs r.
    have h_r_ne_fOut : r.val ≠ (k + 10) + frag_f.outputReg.val :=
      h_ne_fOut'
    exact h_prep_pres r h_ne_1 h_ne_kp7 h_ne_kp8 h_r_ne_fOut

/-- Strict per-step PC bound for `compileFrag_bprod_accUpdate_correct`:
during the `(4 * vAccIn + 1) + (4 * vFOut + 1) + vFOut * (9 * vAccIn
+ 5) + 1 + 1` accumulator-update steps, the intermediate PC stays
strictly less than `bprod_incIPC frag_f` (= `bprod_mul_resetPC frag_f
+ 1`). Case-split across the four phases: prep (PC `< bprod_mul_innerTopPC`
`< bprod_incIPC`), inner-multiply loop (PC `< bprod_mul_resetPC`
`< bprod_incIPC`), exit jumpZR (PC = `bprod_mul_innerTopPC`
`< bprod_incIPC`), and reset assignR (PC = `bprod_mul_resetPC`
`< bprod_incIPC`). -/
private theorem compileFrag_bprod_accUpdate_pc_strict_bound
    {k : ℕ}
    (frag_f : CompiledFragment (k + 1))
    (vAccIn vFOut : ℕ)
    (sPre : URMState (compileFrag_bprod frag_f).toURMProgram)
    (h_pc : sPre.pc = bprod_trBase frag_f)
    (h_zReg_zero : sPre.regs ⟨0,
        (compileFrag_bprod frag_f).numRegs_pos⟩ = 0)
    (h_acc : sPre.regs ⟨1, by
      have : 0 < frag_f.numRegs := frag_f.numRegs_pos
      change 1 < k + 10 + frag_f.numRegs; omega⟩ = vAccIn)
    (h_acc_clone_zero : sPre.regs ⟨k + 7, by
      have : 0 < frag_f.numRegs := frag_f.numRegs_pos
      change k + 7 < k + 10 + frag_f.numRegs; omega⟩ = 0)
    (h_fOut : sPre.regs ⟨(k + 10) + frag_f.outputReg.val, by
      have hO : frag_f.outputReg.val < frag_f.numRegs :=
        frag_f.outputReg.isLt
      change (k + 10) + frag_f.outputReg.val
        < k + 10 + frag_f.numRegs
      omega⟩ = vFOut)
    (h_factor_zero : sPre.regs ⟨k + 8, by
      have : 0 < frag_f.numRegs := frag_f.numRegs_pos
      change k + 8 < k + 10 + frag_f.numRegs; omega⟩ = 0)
    (h_mulTmp_zero : sPre.regs ⟨k + 9, by
      have : 0 < frag_f.numRegs := frag_f.numRegs_pos
      change k + 9 < k + 10 + frag_f.numRegs; omega⟩ = 0)
    (k' : ℕ)
    (h_k' : k' < (4 * vAccIn + 1) + (4 * vFOut + 1)
      + vFOut * (9 * vAccIn + 5) + 1 + 1) :
    (URMState.runFor _ sPre k').pc < bprod_incIPC frag_f := by
  let P : URMProgram (k + 1) := (compileFrag_bprod frag_f).toURMProgram
  change (URMState.runFor P sPre k').pc < bprod_incIPC frag_f
  set T_prep : ℕ := (4 * vAccIn + 1) + (4 * vFOut + 1) with h_T_prep_def
  set T_mul : ℕ := vFOut * (9 * vAccIn + 5) with h_T_mul_def
  -- Boundary constants.
  have h_top_lt_inc : bprod_mul_innerTopPC frag_f < bprod_incIPC frag_f :=
    by change bprod_trBase frag_f + 8 < bprod_trBase frag_f + 21; omega
  have h_reset_lt_inc : bprod_mul_resetPC frag_f < bprod_incIPC frag_f :=
    by change bprod_trBase frag_f + 20 < bprod_trBase frag_f + 21; omega
  -- Phase boundaries.
  rcases Nat.lt_or_ge k' T_prep with h_phase1 | h_phase1
  · -- Prep phase: PC < bprod_mul_innerTopPC < bprod_incIPC.
    have h_bd := compileFrag_bprod_accUpdate_prep_pc_strict_bound
      frag_f vAccIn vFOut sPre h_pc h_zReg_zero h_acc h_acc_clone_zero
      h_fOut h_factor_zero k' h_phase1
    -- h_bd : pc < bprod_mul_innerTopPC < bprod_incIPC.
    exact Nat.lt_trans h_bd h_top_lt_inc
  · -- Compose with prep phase: sPrep := runFor P sPre T_prep.
    obtain ⟨h_prep_post, h_prep_pres⟩ :=
      compileFrag_bprod_accUpdate_prep_correct frag_f vAccIn vFOut sPre
        h_pc h_zReg_zero h_acc h_acc_clone_zero h_fOut h_factor_zero
        h_mulTmp_zero
    set sPrep : URMState P := URMState.runFor P sPre T_prep with h_sPrep_def
    have h_sPrep_z : sPrep.regs ⟨0,
        (compileFrag_bprod frag_f).numRegs_pos⟩ = 0 := by
      have h_ne_1 : (0 : ℕ) ≠ 1 := by decide
      have h_ne_kp7 : (0 : ℕ) ≠ k + 7 := by omega
      have h_ne_kp8 : (0 : ℕ) ≠ k + 8 := by omega
      have h_ne_fOut : (0 : ℕ) ≠ (k + 10) + frag_f.outputReg.val := by
        omega
      have h_eq := h_prep_pres ⟨0, (compileFrag_bprod frag_f).numRegs_pos⟩
        h_ne_1 h_ne_kp7 h_ne_kp8 h_ne_fOut
      rw [h_eq]; exact h_zReg_zero
    obtain ⟨T0, hT0_eq, h_inv_final, h_pres_mul, h_strict_mul⟩ :=
      compileFrag_bprod_mul_partial frag_f vAccIn vFOut sPrep h_sPrep_z
        h_prep_post
    have h_T0_eq_T_mul : T0 = T_mul := by rw [hT0_eq]
    rcases Nat.lt_or_ge k' (T_prep + T_mul) with h_phase2 | h_phase2
    · -- Inner-mul phase.
      let d : ℕ := k' - T_prep
      have h_d_lt : d < T_mul := by change k' - T_prep < T_mul; omega
      have h_split : k' = T_prep + d := by
        change k' = T_prep + (k' - T_prep); omega
      have h_runFor_split :
          URMState.runFor P sPre k'
            = URMState.runFor P sPrep d := by
        rw [h_split, URMState.runFor_add]
      rw [h_runFor_split]
      have h_d_lt_T0 : d < T0 := by rw [h_T0_eq_T_mul]; exact h_d_lt
      have h_bd := h_strict_mul d h_d_lt_T0
      change (URMState.runFor P sPrep d).pc < bprod_incIPC frag_f
      -- h_bd : pc < bprod_mul_resetPC < bprod_incIPC.
      exact Nat.lt_trans h_bd h_reset_lt_inc
    · -- Compose with inner-mul phase: sMul := runFor P sPrep T_mul.
      set sMul : URMState P := URMState.runFor P sPrep T_mul with h_sMul_def
      have h_runFor_sMul :
          URMState.runFor P sPre (T_prep + T_mul) = sMul := by
        rw [URMState.runFor_add]
      have h_sMul_pc : sMul.pc = bprod_mul_innerTopPC frag_f := by
        change (URMState.runFor P sPrep T_mul).pc
          = bprod_mul_innerTopPC frag_f
        have h_eq : URMState.runFor P sPrep T_mul
            = URMState.runFor P sPrep T0 := by rw [h_T0_eq_T_mul]
        rw [h_eq]; exact h_inv_final.pc_eq
      have h_sMul_factor : sMul.regs ⟨k + 8, by
          have : 0 < frag_f.numRegs := frag_f.numRegs_pos
          change k + 8 < k + 10 + frag_f.numRegs; omega⟩ = 0 := by
        have h_eq : URMState.runFor P sPrep T_mul
            = URMState.runFor P sPrep T0 := by rw [h_T0_eq_T_mul]
        change (URMState.runFor P sPrep T_mul).regs _ = 0
        rw [h_eq]
        have := h_inv_final.factor_eq
        rw [this, Nat.sub_self]
      rcases Nat.lt_or_ge k' (T_prep + T_mul + 1) with h_phase3 | h_phase3
      · -- Exit jumpZR phase: k' = T_prep + T_mul (one step).
        have h_k'_eq : k' = T_prep + T_mul := by omega
        rw [h_k'_eq, h_runFor_sMul]
        rw [h_sMul_pc]
        exact h_top_lt_inc
      · -- Reset assignR phase: k' = T_prep + T_mul + 1.
        have h_k'_eq : k' = T_prep + T_mul + 1 := by omega
        rw [h_k'_eq]
        -- runFor P sPre (T_prep + T_mul + 1)
        --   = step P (runFor P sPre (T_prep + T_mul))
        --   = step P sMul.
        -- We need to compute sJ.pc = bprod_mul_resetPC.
        have h_split2 : T_prep + T_mul + 1 = (T_prep + T_mul) + 1 := by
          omega
        rw [h_split2, URMState.runFor_add, h_runFor_sMul]
        -- Now: runFor P sMul 1
        obtain ⟨h_acc_lt, _h_accClone_lt_ib, _h_z_lt, h_factor_lt,
            _h_mulTmp_lt, h_top, _h_dec, _h_pT, _h_goto⟩ :=
          compileFrag_bprod_accUpdate_innerBody_instr_at frag_f
        let factorFin : Fin P.numRegs := ⟨k + 8, h_factor_lt⟩
        have h_top' : P.instrs[bprod_mul_innerTopPC frag_f]?
            = some (URMInstr.jumpZ factorFin
                (bprod_mul_resetPC frag_f)
                (bprod_mul_innerBodyStartPC frag_f)) := h_top
        have h_sMul_factorFin : sMul.regs factorFin = 0 := by
          have h_eq : (⟨k + 8, by
              have : 0 < frag_f.numRegs := frag_f.numRegs_pos
              change k + 8 < k + 10 + frag_f.numRegs; omega⟩
              : Fin P.numRegs) = factorFin := Fin.ext rfl
          rw [← h_eq]; exact h_sMul_factor
        -- runFor P sMul 1 = { pc := bprod_mul_resetPC, regs := sMul.regs }.
        have h_step1 :
            URMState.runFor P sMul 1
              = { pc := bprod_mul_resetPC frag_f
                  regs := sMul.regs } := by
          change URMState.runFor P sMul (0 + 1)
            = { pc := bprod_mul_resetPC frag_f
                regs := sMul.regs }
          rw [URMState.runFor_succ, URMState.runFor_zero,
            URMState.step_of_getElem?_jumpZ P sMul
              (bprod_mul_innerTopPC frag_f) factorFin
              (bprod_mul_resetPC frag_f)
              (bprod_mul_innerBodyStartPC frag_f) h_sMul_pc h_top']
          simp only [h_sMul_factorFin, ↓reduceIte]
        change (URMState.runFor P sMul 1).pc < bprod_incIPC frag_f
        rw [h_step1]
        exact h_reset_lt_inc

/-- For `compileFrag_bprod`'s f-body embedding: at PCs
`bprod_bodyPCBase frag_f .. bprod_bodyPCBase frag_f
+ (frag_f.instrs.size - 1)`, the outer program's instructions are
the `reindexShift`-mapped raw form of `frag_f.instrs.pop`. The
values of `fBase = k + 10` and `bprod_bodyPCBase frag_f
= 16 + frag_f.numRegs + 9 * (k + 1)` are those used by the
constructor of `compileFrag_bprod`; the embedded length excludes
`frag_f`'s trailing stop instruction (dropped via `.pop` when
emitting the f-body). Mirrors
`ProgramEmbedsFragment_compileFrag_bsum_fBody`; the bprod prelude is
14 instructions (vs bsum's 13, with the trailing `incR vAcc`
initialising the multiplicative accumulator to 1), and the bprod
accumulator-update block is 21 instructions (vs bsum's 4) for the
Tourlakis 2018 p. 19 `R^XY_Z` template. -/
private theorem ProgramEmbedsFragment_compileFrag_bprod_fBody
    {k : ℕ}
    (frag_f : CompiledFragment (k + 1)) :
    ProgramEmbedsFragment
      (compileFrag_bprod frag_f).toURMProgram
      frag_f
      (k + 10)
      (16 + frag_f.numRegs + 9 * (k + 1))
      (frag_f.instrs.size - 1) := by
  -- Abbreviations matching the constructor of compileFrag_bprod.
  let vAcc : ℕ := 1
  let vBoundIn : ℕ := 2
  let vX : ℕ := k + 3
  let vI : ℕ := k + 4
  let tmp1 : ℕ := k + 5
  let tmp2 : ℕ := k + 6
  let vAccClone : ℕ := k + 7
  let vFactor : ℕ := k + 8
  let vMulTmp : ℕ := k + 9
  let fBase : ℕ := k + 10
  let nR : ℕ := fBase + frag_f.numRegs
  let topPC : ℕ := 14
  let bodyStartPC : ℕ := 15
  let prologueBase : ℕ := 16 + frag_f.numRegs
  let bodyPCBase : ℕ := 16 + frag_f.numRegs + 9 * (k + 1)
  let fBodyLen : ℕ := frag_f.instrs.size - 1
  let trBase : ℕ := bodyPCBase + fBodyLen
  let exitPC : ℕ := trBase + 23
  let prelude : List URMInstrRaw :=
    [ .assignR 0 0,
      .assignR vAcc 0,
      .assignR vX 0,
      .assignR vI 0 ]
        ++ URMRaw.preservingTransfer 4 vBoundIn vX tmp2
        ++ [ .incR vAcc ]
  let loopTop : List URMInstrRaw :=
    [ .jumpZR vX exitPC bodyStartPC,
      .decR vX ]
  let zeroSweep : List URMInstrRaw :=
    bsum_zeroSweep frag_f fBase
  let prologue : List URMInstrRaw :=
    (List.finRange (k + 1)).flatMap fun s =>
      bsum_prologueBlock frag_f fBase tmp1 prologueBase s
  let fBody : List URMInstrRaw :=
    frag_f.instrs.pop.toList.map fun ins =>
      URMInstrRaw.reindexShift fBase bodyPCBase (toRawOfBounded ins)
  let accUpdate : List URMInstrRaw :=
    URMRaw.transferLoop trBase vAcc vAccClone
      ++ URMRaw.transferLoop (trBase + 4)
          (fBase + frag_f.outputReg.val) vFactor
      ++ [ .jumpZR vFactor (trBase + 20) (trBase + 9),
           .decR vFactor ]
      ++ URMRaw.preservingTransfer (trBase + 10)
          vAccClone vAcc vMulTmp
      ++ [ URMRaw.goto (trBase + 8),
           .assignR vAccClone 0 ]
  let epilogue : List URMInstrRaw :=
    [ .incR vI, URMRaw.goto topPC, .stopR ]
  let rawList : List URMInstrRaw :=
    prelude ++ loopTop ++ zeroSweep ++ prologue ++ fBody
      ++ accUpdate ++ epilogue
  -- Segment lengths.
  have h_prelude_len : prelude.length = 14 := by
    change ([URMInstrRaw.assignR 0 0, URMInstrRaw.assignR vAcc 0,
        URMInstrRaw.assignR vX 0, URMInstrRaw.assignR vI 0]
        ++ URMRaw.preservingTransfer 4 vBoundIn vX tmp2
        ++ [URMInstrRaw.incR vAcc]).length = 14
    simp only [List.length_append, List.length_cons, List.length_nil,
      URMRaw.preservingTransfer, URMRaw.goto]
  have h_loopTop_len : loopTop.length = 2 := by
    change ([URMInstrRaw.jumpZR vX exitPC bodyStartPC,
      URMInstrRaw.decR vX] : List URMInstrRaw).length = 2
    simp only [List.length_cons, List.length_nil]
  have h_zeroSweep_len : zeroSweep.length = frag_f.numRegs := by
    change ((List.finRange frag_f.numRegs).map _).length = _
    rw [List.length_map, List.length_finRange]
  have h_prologueBlock_len : ∀ s : Fin (k + 1),
      (bsum_prologueBlock frag_f fBase tmp1 prologueBase s).length
        = 9 := by
    intro _
    simp only [bsum_prologueBlock, URMRaw.preservingTransfer,
      URMRaw.goto, List.length_cons, List.length_nil]
  have h_prologue_len : prologue.length = 9 * (k + 1) := by
    change ((List.finRange (k + 1)).flatMap _).length = _
    rw [List.length_flatMap, List.map_congr_left
      (fun s _ => h_prologueBlock_len s)]
    rw [List.map_const', List.length_finRange,
      List.sum_replicate_nat, Nat.mul_comm]
  have h_fBody_len : fBody.length = frag_f.instrs.size - 1 := by
    change (frag_f.instrs.pop.toList.map _).length = _
    rw [List.length_map, Array.length_toList, Array.size_pop]
  have h_accUpdate_len : accUpdate.length = 21 := by
    change (URMRaw.transferLoop trBase vAcc vAccClone
        ++ URMRaw.transferLoop (trBase + 4)
            (fBase + frag_f.outputReg.val) vFactor
        ++ [URMInstrRaw.jumpZR vFactor (trBase + 20) (trBase + 9),
            URMInstrRaw.decR vFactor]
        ++ URMRaw.preservingTransfer (trBase + 10)
            vAccClone vAcc vMulTmp
        ++ [URMRaw.goto (trBase + 8),
            URMInstrRaw.assignR vAccClone 0]).length = 21
    simp only [URMRaw.transferLoop, URMRaw.preservingTransfer,
      URMRaw.goto, List.length_append, List.length_cons,
      List.length_nil]
  have h_epilogue_len : epilogue.length = 3 := by
    simp only [epilogue, URMRaw.goto, List.length_cons,
      List.length_nil]
  -- Total length of rawList.
  have h_raw_len : rawList.length
      = prelude.length + loopTop.length + zeroSweep.length
        + prologue.length + fBody.length + accUpdate.length
        + epilogue.length := by
    change (prelude ++ loopTop ++ zeroSweep ++ prologue ++ fBody
      ++ accUpdate ++ epilogue).length = _
    simp only [List.length_append]
  -- Offset to f-body start.
  have h_offset_eq : prelude.length + loopTop.length
      + zeroSweep.length + prologue.length = bodyPCBase := by
    rw [h_prelude_len, h_loopTop_len, h_zeroSweep_len, h_prologue_len]
  -- outer.numRegs = nR (definitional).
  let outer : URMProgram (k + 1) := (compileFrag_bprod frag_f).toURMProgram
  have hReg : fBase + frag_f.numRegs ≤ outer.numRegs := by
    change fBase + frag_f.numRegs ≤ nR
    change fBase + frag_f.numRegs ≤ fBase + frag_f.numRegs
    omega
  have hL : frag_f.instrs.size - 1 ≤ frag_f.instrs.size := Nat.sub_le _ _
  refine ⟨hL, hReg, ?_⟩
  intro i hi
  have hi' : i < frag_f.instrs.size :=
    Nat.lt_of_lt_of_le hi hL
  -- Reconstruct the boundedness witness on rawList.
  have hBoundOuter : URMInstrRaw.boundedBy nR rawList := by
    have hAcc : vAcc + 1 ≤ nR := by
      change 1 + 1 ≤ k + 10 + frag_f.numRegs
      have : 0 < frag_f.numRegs := frag_f.numRegs_pos
      omega
    have hBoundIn : vBoundIn + 1 ≤ nR := by
      change 2 + 1 ≤ k + 10 + frag_f.numRegs
      have : 0 < frag_f.numRegs := frag_f.numRegs_pos
      omega
    have hVX : vX + 1 ≤ nR := by
      change k + 3 + 1 ≤ k + 10 + frag_f.numRegs
      have : 0 < frag_f.numRegs := frag_f.numRegs_pos
      omega
    have hVI : vI + 1 ≤ nR := by
      change k + 4 + 1 ≤ k + 10 + frag_f.numRegs
      have : 0 < frag_f.numRegs := frag_f.numRegs_pos
      omega
    have hTmp1 : tmp1 + 1 ≤ nR := by
      change k + 5 + 1 ≤ k + 10 + frag_f.numRegs
      have : 0 < frag_f.numRegs := frag_f.numRegs_pos
      omega
    have hTmp2 : tmp2 + 1 ≤ nR := by
      change k + 6 + 1 ≤ k + 10 + frag_f.numRegs
      have : 0 < frag_f.numRegs := frag_f.numRegs_pos
      omega
    have hAccClone : vAccClone + 1 ≤ nR := by
      change k + 7 + 1 ≤ k + 10 + frag_f.numRegs
      have : 0 < frag_f.numRegs := frag_f.numRegs_pos
      omega
    have hFactor : vFactor + 1 ≤ nR := by
      change k + 8 + 1 ≤ k + 10 + frag_f.numRegs
      have : 0 < frag_f.numRegs := frag_f.numRegs_pos
      omega
    have hMulTmp : vMulTmp + 1 ≤ nR := by
      change k + 9 + 1 ≤ k + 10 + frag_f.numRegs
      have : 0 < frag_f.numRegs := frag_f.numRegs_pos
      omega
    have hFOut : fBase + frag_f.outputReg.val + 1 ≤ nR := by
      have : frag_f.outputReg.val < frag_f.numRegs :=
        frag_f.outputReg.isLt
      change fBase + frag_f.outputReg.val + 1 ≤ fBase + frag_f.numRegs
      omega
    have hPrologueSrc : ∀ s : Fin (k + 1),
        bsum_prologueSrc k s + 1 ≤ nR := by
      intro s
      have hs : s.val < k + 1 := s.isLt
      simp only [bsum_prologueSrc, nR, fBase]
      split <;> omega
    have hFIn : ∀ s : Fin (k + 1),
        fBase + (frag_f.inputRegs s).val + 1 ≤ nR := by
      intro s
      have : (frag_f.inputRegs s).val < frag_f.numRegs :=
        (frag_f.inputRegs s).isLt
      change fBase + (frag_f.inputRegs s).val + 1
          ≤ fBase + frag_f.numRegs
      omega
    have hPreludeBound : URMInstrRaw.boundedBy nR prelude := by
      intro ins hmem
      simp only [prelude, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false] at hmem
      rcases hmem with ((h | h | h | h) | hpT) | h
      · rw [h]; simp only [URMInstrRaw.regBound]; omega
      · rw [h]; simp only [URMInstrRaw.regBound]; exact hAcc
      · rw [h]; simp only [URMInstrRaw.regBound]; exact hVX
      · rw [h]; simp only [URMInstrRaw.regBound]; exact hVI
      · exact boundedBy_preservingTransfer nR _ _ _ _
          hBoundIn hVX hTmp2 ins hpT
      · rw [h]; simp only [URMInstrRaw.regBound]; exact hAcc
    have hLoopTopBound : URMInstrRaw.boundedBy nR loopTop := by
      intro ins hmem
      simp only [loopTop, List.mem_cons, List.not_mem_nil,
        or_false] at hmem
      rcases hmem with h | h <;>
        (rw [h]; simp only [URMInstrRaw.regBound]; exact hVX)
    have hZeroSweepBound : URMInstrRaw.boundedBy nR zeroSweep := by
      have hBlock : fBase + frag_f.numRegs ≤ nR := Nat.le_refl _
      exact boundedBy_bsum_zeroSweep frag_f fBase nR hBlock
    have hPrologueBound : URMInstrRaw.boundedBy nR prologue := by
      intro ins hmem
      simp only [prologue, List.mem_flatMap] at hmem
      rcases hmem with ⟨s, _, hs⟩
      exact boundedBy_bsum_prologueBlock frag_f fBase tmp1
        prologueBase nR s (hPrologueSrc s) (hFIn s) hTmp1 ins hs
    have hFBodyBound : URMInstrRaw.boundedBy nR fBody := by
      intro ins hmem
      simp only [fBody, List.mem_map] at hmem
      rcases hmem with ⟨ins', _, heq⟩
      rw [← heq]
      have hb : (toRawOfBounded ins').regBound ≤ frag_f.numRegs :=
        regBound_toRawOfBounded_le ins'
      have hr := regBound_reindexShift_le_offset_add fBase
        bodyPCBase frag_f.numRegs (toRawOfBounded ins') hb
      change _ ≤ fBase + frag_f.numRegs
      omega
    have hAccUpdateBound : URMInstrRaw.boundedBy nR accUpdate := by
      intro ins hmem
      simp only [accUpdate, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false] at hmem
      rcases hmem with
        ((((hTr1 | hTr2) | hOuter) | hInner) | hTail)
      · exact boundedBy_transferLoop nR _ _ _
          hAcc hAccClone ins hTr1
      · exact boundedBy_transferLoop nR _ _ _
          hFOut hFactor ins hTr2
      · rcases hOuter with h | h
        · rw [h]; simp only [URMInstrRaw.regBound]; exact hFactor
        · rw [h]; simp only [URMInstrRaw.regBound]; exact hFactor
      · exact boundedBy_preservingTransfer nR _ _ _ _
          hAccClone hAcc hMulTmp ins hInner
      · rcases hTail with h | h
        · rw [h]; simp only [URMRaw.goto, URMInstrRaw.regBound]
          omega
        · rw [h]; simp only [URMInstrRaw.regBound]; exact hAccClone
    have hEpilogueBound : URMInstrRaw.boundedBy nR epilogue := by
      intro ins hmem
      simp only [epilogue, URMRaw.goto, List.mem_cons,
        List.not_mem_nil, or_false] at hmem
      rcases hmem with h | h | h
      · rw [h]; simp only [URMInstrRaw.regBound]; exact hVI
      · rw [h]; simp only [URMInstrRaw.regBound]; omega
      · rw [h]; simp only [URMInstrRaw.regBound]; omega
    intro ins hmem
    simp only [rawList, List.mem_append] at hmem
    rcases hmem with
      (((((hP | hL') | hZ) | hPr) | hF) | hA) | hE
    · exact hPreludeBound ins hP
    · exact hLoopTopBound ins hL'
    · exact hZeroSweepBound ins hZ
    · exact hPrologueBound ins hPr
    · exact hFBodyBound ins hF
    · exact hAccUpdateBound ins hA
    · exact hEpilogueBound ins hE
  -- Index of bodyPCBase + i in rawList.
  have h_idx_lt : bodyPCBase + i < rawList.length := by
    rw [h_raw_len, h_prelude_len, h_loopTop_len, h_zeroSweep_len,
      h_prologue_len, h_fBody_len, h_accUpdate_len, h_epilogue_len]
    change 16 + frag_f.numRegs + 9 * (k + 1) + i
      < 14 + 2 + frag_f.numRegs + 9 * (k + 1)
        + (frag_f.instrs.size - 1) + 21 + 3
    omega
  -- Reduce outer.instrs[bodyPCBase + i]? to toBoundedArray's lookup.
  change (URMInstrRaw.toBoundedArray nR rawList hBoundOuter)[
      bodyPCBase + i]?
    = some (URMInstrRaw.toBounded nR
        (URMInstrRaw.reindexShift fBase bodyPCBase
          (toRawOfBounded (frag_f.instrs[i]'hi'))) _)
  rw [URMInstrRaw.toBoundedArray_getElem? nR rawList hBoundOuter
      (bodyPCBase + i) h_idx_lt]
  -- Raw equality: rawList[bodyPCBase + i] = reindexShift fBase bodyPCBase
  --   (toRawOfBounded frag_f.instrs[i]).
  have h_raw_eq :
      rawList[bodyPCBase + i]'h_idx_lt
        = URMInstrRaw.reindexShift fBase bodyPCBase
          (toRawOfBounded (frag_f.instrs[i]'hi')) := by
    have h_in_prefix6 :
        bodyPCBase + i
          < ((((((prelude ++ loopTop) ++ zeroSweep) ++ prologue)
              ++ fBody) ++ accUpdate)).length := by
      simp only [List.length_append]
      rw [h_prelude_len, h_loopTop_len, h_zeroSweep_len,
        h_prologue_len, h_fBody_len, h_accUpdate_len]
      change 16 + frag_f.numRegs + 9 * (k + 1) + i
        < 14 + 2 + frag_f.numRegs + 9 * (k + 1)
          + (frag_f.instrs.size - 1) + 21
      omega
    have h_in_prefix5 :
        bodyPCBase + i
          < (((((prelude ++ loopTop) ++ zeroSweep) ++ prologue)
              ++ fBody)).length := by
      simp only [List.length_append]
      rw [h_prelude_len, h_loopTop_len, h_zeroSweep_len,
        h_prologue_len, h_fBody_len]
      change 16 + frag_f.numRegs + 9 * (k + 1) + i
        < 14 + 2 + frag_f.numRegs + 9 * (k + 1)
          + (frag_f.instrs.size - 1)
      omega
    -- Peel epilogue.
    have h_step1 :
        rawList[bodyPCBase + i]'h_idx_lt
          = ((((((prelude ++ loopTop) ++ zeroSweep) ++ prologue)
                ++ fBody) ++ accUpdate))[bodyPCBase + i]'h_in_prefix6 := by
      change (((((((prelude ++ loopTop) ++ zeroSweep) ++ prologue)
            ++ fBody) ++ accUpdate) ++ epilogue))[bodyPCBase + i]'h_idx_lt
        = _
      rw [List.getElem_append_left h_in_prefix6]
    rw [h_step1]
    -- Peel accUpdate.
    have h_step2 :
        ((((((prelude ++ loopTop) ++ zeroSweep) ++ prologue)
              ++ fBody) ++ accUpdate))[bodyPCBase + i]'h_in_prefix6
          = (((((prelude ++ loopTop) ++ zeroSweep) ++ prologue)
                ++ fBody))[bodyPCBase + i]'h_in_prefix5 := by
      rw [List.getElem_append_left h_in_prefix5]
    rw [h_step2]
    -- Peel fBody: index ≥ (prelude++loopTop++zeroSweep++prologue).length.
    have h_pref4_le :
        ((((prelude ++ loopTop) ++ zeroSweep) ++ prologue)).length
          ≤ bodyPCBase + i := by
      simp only [List.length_append]
      rw [h_prelude_len, h_loopTop_len, h_zeroSweep_len,
        h_prologue_len]
      change 14 + 2 + frag_f.numRegs + 9 * (k + 1)
        ≤ 16 + frag_f.numRegs + 9 * (k + 1) + i
      omega
    set prefix4 : List URMInstrRaw :=
      prelude ++ loopTop ++ zeroSweep ++ prologue with h_prefix4_def
    have h_prefix4_len : prefix4.length = bodyPCBase := by
      change (prelude ++ loopTop ++ zeroSweep ++ prologue).length
        = bodyPCBase
      simp only [List.length_append]
      exact h_offset_eq
    have h_pref4_le' : prefix4.length ≤ bodyPCBase + i := by
      rw [h_prefix4_len]; omega
    have h_idx_in_fBody :
        bodyPCBase + i - prefix4.length < fBody.length := by
      rw [h_prefix4_len, h_fBody_len]
      have h_sub : bodyPCBase + i - bodyPCBase = i := by omega
      rw [h_sub]; exact hi
    have h_step3 :
        ((prefix4 ++ fBody))[bodyPCBase + i]'(by
            rw [List.length_append, h_prefix4_len, h_fBody_len]
            omega)
          = fBody[bodyPCBase + i - prefix4.length]'h_idx_in_fBody := by
      rw [List.getElem_append_right h_pref4_le']
    have h_step3' :
        (((((prelude ++ loopTop) ++ zeroSweep) ++ prologue)
              ++ fBody))[bodyPCBase + i]'h_in_prefix5
          = fBody[bodyPCBase + i - prefix4.length]'h_idx_in_fBody := by
      exact h_step3
    rw [h_step3']
    have h_idx_eq : bodyPCBase + i - prefix4.length = i := by
      rw [h_prefix4_len]; omega
    have h_i_lt_fBody : i < fBody.length := by
      rw [h_fBody_len]; exact hi
    have h_step4 :
        fBody[bodyPCBase + i - prefix4.length]'h_idx_in_fBody
          = fBody[i]'h_i_lt_fBody := by
      congr 1
    rw [h_step4]
    change (frag_f.instrs.pop.toList.map (fun ins =>
        URMInstrRaw.reindexShift fBase bodyPCBase
          (toRawOfBounded ins)))[i]'_
      = _
    rw [List.getElem_map]
    have h_i_lt_pop : i < frag_f.instrs.pop.toList.length := by
      rw [Array.length_toList, Array.size_pop]; exact hi
    have h_i_lt_dl : i < frag_f.instrs.toList.dropLast.length := by
      rw [List.length_dropLast, Array.length_toList]; exact hi
    have h_i_lt_tl : i < frag_f.instrs.toList.length := by
      rw [Array.length_toList]; exact hi'
    have h_step_a :
        frag_f.instrs.pop.toList[i]'h_i_lt_pop
          = frag_f.instrs.toList.dropLast[i]'h_i_lt_dl := by
      have h_pop_to_dl :
          frag_f.instrs.pop.toList = frag_f.instrs.toList.dropLast :=
        Array.toList_pop
      have hopt : frag_f.instrs.pop.toList[i]?
          = frag_f.instrs.toList.dropLast[i]? := by
        rw [h_pop_to_dl]
      rw [List.getElem?_eq_getElem h_i_lt_pop,
        List.getElem?_eq_getElem h_i_lt_dl] at hopt
      exact Option.some_injective _ hopt
    have h_step_b :
        frag_f.instrs.toList.dropLast[i]'h_i_lt_dl
          = frag_f.instrs.toList[i]'h_i_lt_tl := by
      have h_dl_getElem? :
          frag_f.instrs.toList.dropLast[i]?
            = frag_f.instrs.toList[i]? := by
        rw [List.getElem?_dropLast]
        have h_cond : i < frag_f.instrs.toList.length - 1 := by
          rw [Array.length_toList]; exact hi
        rw [if_pos h_cond]
      rw [List.getElem?_eq_getElem h_i_lt_dl,
        List.getElem?_eq_getElem h_i_lt_tl] at h_dl_getElem?
      exact Option.some_injective _ h_dl_getElem?
    have h_step_c :
        frag_f.instrs.toList[i]'h_i_lt_tl
          = frag_f.instrs[i]'hi' :=
      Array.getElem_toList hi'
    have h_pop_eq :
        frag_f.instrs.pop.toList[i]'h_i_lt_pop
          = frag_f.instrs[i]'hi' := by
      rw [h_step_a, h_step_b, h_step_c]
    rw [h_pop_eq]
  -- Push through `toBounded` and `some`.
  apply congrArg some
  exact URMInstrRaw.toBounded_congr nR h_raw_eq _ _

/-- Partial-iteration invariant for `compileFrag_bprod`. Describes
the state at the top of the outer loop (PC = `bprod_topPC` = 14)
after `i` complete iterations (with `i ≤ v 0`). Mirrors
`compileFrag_bsum_partial_invariant` in `BSum.lean`, adapted to
bprod's register layout (`V_z = ⟨0, _⟩`, `V_acc = ⟨1, _⟩`, outer
inputs at slots `2..k+2`, `V_x = ⟨k+3, _⟩`, `V_i = ⟨k+4, _⟩`,
scratch `tmp1 = ⟨k+5, _⟩`, `tmp2 = ⟨k+6, _⟩`, multiplicative
scratch `V_acc_clone = ⟨k+7, _⟩`, `V_factor = ⟨k+8, _⟩`,
`V_mul_tmp = ⟨k+9, _⟩`, f's reindexed register block at slots
`k+10 .. k+10 + frag_f.numRegs - 1`). The structure carries the
running value of `i` and proofs about the outer scaffolding
registers; f's reindexed block is not tracked (Phase i.0's
zero-sweep re-establishes it at the start of each iteration). -/
private structure compileFrag_bprod_partial_invariant
    {k : ℕ}
    (frag_f : CompiledFragment (k + 1))
    (f : ERMor1 (k + 1))
    (v : Fin (k + 1) → ℕ)
    (i : ℕ) (hi : i ≤ v 0)
    (s : URMState (compileFrag_bprod frag_f).toURMProgram)
    : Prop where
  /-- `i ≤ v 0`, packaged for downstream consumers. -/
  hi_le : i ≤ v 0 := hi
  /-- PC sits at the loop-top instruction (absolute PC
  `bprod_topPC` = 14). -/
  pc_eq : s.pc = bprod_topPC
  /-- `V_z` (register 0) holds `0`. -/
  zReg_zero : s.regs ⟨0, (compileFrag_bprod frag_f).numRegs_pos⟩ = 0
  /-- Outer input slots `2..k+2` hold the input vector. -/
  outer_inputs : ∀ (j : Fin (k + 1)),
    s.regs ⟨2 + j.val, by
      have hj : j.val < k + 1 := j.isLt
      change 2 + j.val < k + 10 + frag_f.numRegs
      have : 0 < frag_f.numRegs := frag_f.numRegs_pos
      omega⟩ = v j
  /-- `V_x` (register `k + 3`) holds `v 0 - i`, the remaining
  iteration count. -/
  vX_eq : s.regs ⟨k + 3, by
    change k + 3 < k + 10 + frag_f.numRegs
    have : 0 < frag_f.numRegs := frag_f.numRegs_pos
    omega⟩ = v 0 - i
  /-- `V_i` (register `k + 4`) holds the iteration counter `i`. -/
  vI_eq : s.regs ⟨k + 4, by
    change k + 4 < k + 10 + frag_f.numRegs
    have : 0 < frag_f.numRegs := frag_f.numRegs_pos
    omega⟩ = i
  /-- Scratch register `tmp1` (register `k + 5`) is `0`. -/
  tmp1_zero : s.regs ⟨k + 5, by
    change k + 5 < k + 10 + frag_f.numRegs
    have : 0 < frag_f.numRegs := frag_f.numRegs_pos
    omega⟩ = 0
  /-- Scratch register `tmp2` (register `k + 6`) is `0`. -/
  tmp2_zero : s.regs ⟨k + 6, by
    change k + 6 < k + 10 + frag_f.numRegs
    have : 0 < frag_f.numRegs := frag_f.numRegs_pos
    omega⟩ = 0
  /-- Multiplicative scratch `V_acc_clone` (register `k + 7`)
  is `0`. -/
  accClone_zero : s.regs ⟨k + 7, by
    change k + 7 < k + 10 + frag_f.numRegs
    have : 0 < frag_f.numRegs := frag_f.numRegs_pos
    omega⟩ = 0
  /-- Multiplicative scratch `V_factor` (register `k + 8`) is `0`. -/
  factor_zero : s.regs ⟨k + 8, by
    change k + 8 < k + 10 + frag_f.numRegs
    have : 0 < frag_f.numRegs := frag_f.numRegs_pos
    omega⟩ = 0
  /-- Multiplicative scratch `V_mul_tmp` (register `k + 9`) is `0`. -/
  mulTmp_zero : s.regs ⟨k + 9, by
    change k + 9 < k + 10 + frag_f.numRegs
    have : 0 < frag_f.numRegs := frag_f.numRegs_pos
    omega⟩ = 0
  /-- The accumulator (register 1) holds the partial product
  `Π_{j < i} f.interp (j :: tail v)`. At `i = 0` this is `1`
  (the empty product). -/
  acc_eq : s.regs ⟨1, by
    change 1 < k + 10 + frag_f.numRegs
    have : 0 < frag_f.numRegs := frag_f.numRegs_pos
    omega⟩
      = natBProd i (fun j => f.interp (Fin.cons j (Fin.tail v)))

set_option maxHeartbeats 1000000 in
-- The base-case proof discharges 12 invariant fields after a
-- six-step `URMState.runFor` chain through the prelude; the
-- elaborator's default budget is exhausted by the cumulative
-- whnf load.
/-- Base case of the bprod outer-iteration induction: after running
the prelude of `compileFrag_bprod`
(`assignR 0 0; assignR vAcc 0; assignR vX 0; assignR vI 0;`
`preservingTransfer 4 vBoundIn vX tmp2; incR vAcc`) for
`7 + 9 * (v 0)` URM steps from `URMState.init outer v`, the
partial invariant holds at `i = 0`. The four `assignR`
instructions occupy PCs `0..3`, each consuming one URM step; the
`preservingTransfer` block at PC 4 consumes `9 * (v 0) + 2`
further steps; the final `incR vAcc` at PC 13 consumes one more
step, leaving the PC at `14 = bprod_topPC` (the loop-top
instruction) with `V_x = v 0 - 0`, `V_i = 0`, accumulator `1`
(= `natBProd 0 _`), the three multiplicative scratch registers
`V_acc_clone`, `V_factor`, `V_mul_tmp` all `0`, scratches `tmp1`,
`tmp2` both `0`, outer inputs preserved, and f's reindexed block
untouched at `0`. -/
private theorem compileFrag_bprod_partial_base
    {k : ℕ}
    (f : ERMor1 (k + 1))
    (v : Fin (k + 1) → ℕ) :
    let outer := (compileFrag_bprod (compileERFrag f)).toURMProgram
    let s_init := URMState.init outer v
    compileFrag_bprod_partial_invariant (compileERFrag f) f v 0
      (Nat.zero_le _)
      (URMState.runFor outer s_init (7 + 9 * (v 0))) := by
  intro outer s_init
  -- Abbreviations.
  set frag_f : CompiledFragment (k + 1) := compileERFrag f
  set outerFrag : CompiledFragment (k + 1) :=
    compileFrag_bprod frag_f
  set P : URMProgram (k + 1) := outerFrag.toURMProgram
  set s0 : URMState P := URMState.init P v
  -- Outer numRegs equals `(k + 10) + frag_f.numRegs`.
  have h_numRegs_eq : P.numRegs = (k + 10) + frag_f.numRegs := rfl
  have h_numRegs_pos : 0 < P.numRegs := outerFrag.numRegs_pos
  -- Boundedness witnesses for the named registers.
  have h_z_lt : 0 < P.numRegs := h_numRegs_pos
  have h_acc_lt : 1 < P.numRegs := by
    rw [h_numRegs_eq]
    have : 0 < frag_f.numRegs := frag_f.numRegs_pos; omega
  have h_bIn_lt : 2 < P.numRegs := by
    rw [h_numRegs_eq]
    have : 0 < frag_f.numRegs := frag_f.numRegs_pos; omega
  have h_vX_lt : k + 3 < P.numRegs := by
    rw [h_numRegs_eq]
    have : 0 < frag_f.numRegs := frag_f.numRegs_pos; omega
  have h_vI_lt : k + 4 < P.numRegs := by
    rw [h_numRegs_eq]
    have : 0 < frag_f.numRegs := frag_f.numRegs_pos; omega
  have h_tmp1_lt : k + 5 < P.numRegs := by
    rw [h_numRegs_eq]
    have : 0 < frag_f.numRegs := frag_f.numRegs_pos; omega
  have h_tmp2_lt : k + 6 < P.numRegs := by
    rw [h_numRegs_eq]
    have : 0 < frag_f.numRegs := frag_f.numRegs_pos; omega
  have h_accClone_lt : k + 7 < P.numRegs := by
    rw [h_numRegs_eq]
    have : 0 < frag_f.numRegs := frag_f.numRegs_pos; omega
  have h_factor_lt : k + 8 < P.numRegs := by
    rw [h_numRegs_eq]
    have : 0 < frag_f.numRegs := frag_f.numRegs_pos; omega
  have h_mulTmp_lt : k + 9 < P.numRegs := by
    rw [h_numRegs_eq]
    have : 0 < frag_f.numRegs := frag_f.numRegs_pos; omega
  -- Fin-wrapped register handles.
  set rZ : Fin P.numRegs := ⟨0, h_z_lt⟩
  set rAcc : Fin P.numRegs := ⟨1, h_acc_lt⟩
  set rBoundIn : Fin P.numRegs := ⟨2, h_bIn_lt⟩
  set rVX : Fin P.numRegs := ⟨k + 3, h_vX_lt⟩
  set rVI : Fin P.numRegs := ⟨k + 4, h_vI_lt⟩
  set rTmp1 : Fin P.numRegs := ⟨k + 5, h_tmp1_lt⟩
  set rTmp2 : Fin P.numRegs := ⟨k + 6, h_tmp2_lt⟩
  set rAccClone : Fin P.numRegs := ⟨k + 7, h_accClone_lt⟩
  set rFactor : Fin P.numRegs := ⟨k + 8, h_factor_lt⟩
  set rMulTmp : Fin P.numRegs := ⟨k + 9, h_mulTmp_lt⟩
  -- Outer's `inputRegs` maps slot `j` to outer register `2 + j.val`.
  have h_outer_inputRegs : ∀ (j : Fin (k + 1)),
      (P.inputRegs j).val = 2 + j.val := fun _ => rfl
  -- Prelude instruction lookups at PCs 0..3 (each `assignR`)
  -- and at PC 13 (the `incR vAcc`).
  have h_outer_at_0 : P.instrs[(0 : ℕ)]? = some (URMInstr.assign rZ 0) := rfl
  have h_outer_at_1 : P.instrs[(1 : ℕ)]? = some (URMInstr.assign rAcc 0) := rfl
  have h_outer_at_2 : P.instrs[(2 : ℕ)]? = some (URMInstr.assign rVX 0) := rfl
  have h_outer_at_3 : P.instrs[(3 : ℕ)]? = some (URMInstr.assign rVI 0) := rfl
  have h_outer_at_13 : P.instrs[(13 : ℕ)]? = some (URMInstr.inc rAcc) := rfl
  -- preservingTransferInstrs at PC 4 with src=vBoundIn, dst=vX, tmp=tmp2,
  -- zReg=⟨0, _⟩.
  have H_pT : preservingTransferInstrs P 4 rBoundIn rVX rTmp2 rZ := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rfl
  -- Disjointness witnesses for preservingTransfer_correct.
  have h_disj_sd : rBoundIn ≠ rVX := by
    intro h
    have : (2 : ℕ) = k + 3 := congrArg Fin.val h; omega
  have h_disj_st : rBoundIn ≠ rTmp2 := by
    intro h
    have : (2 : ℕ) = k + 6 := congrArg Fin.val h; omega
  have h_disj_dt : rVX ≠ rTmp2 := by
    intro h
    have : (k + 3 : ℕ) = k + 6 := congrArg Fin.val h; omega
  have h_disj_zs : rZ ≠ rBoundIn := by
    intro h
    have : (0 : ℕ) = 2 := congrArg Fin.val h; omega
  have h_disj_zd : rZ ≠ rVX := by
    intro h
    have : (0 : ℕ) = k + 3 := congrArg Fin.val h; omega
  have h_disj_zt : rZ ≠ rTmp2 := by
    intro h
    have : (0 : ℕ) = k + 6 := congrArg Fin.val h; omega
  -- Step 1 (PC 0): assignR 0 0.  s0 → s1.
  have hs0_pc : s0.pc = 0 := rfl
  have h_step0 :
      URMState.step P s0 =
        { pc := 1
          regs := Function.update s0.regs rZ 0 } := by
    have h := URMState.step_of_getElem?_assign P s0 0 rZ 0 hs0_pc h_outer_at_0
    rw [h]
    have : s0.pc + 1 = 1 := by rw [hs0_pc]
    rw [this]
  set s1 : URMState P :=
      { pc := 1
        regs := Function.update s0.regs rZ 0 }
  have h_runFor_1 : URMState.runFor P s0 1 = s1 := by
    change URMState.runFor P (URMState.step P s0) 0 = _
    rw [URMState.runFor_zero, h_step0]
  -- Step 2 (PC 1): assignR vAcc 0.  s1 → s2.
  have hs1_pc : s1.pc = 1 := rfl
  have h_step1 :
      URMState.step P s1 =
        { pc := 2
          regs := Function.update s1.regs rAcc 0 } := by
    have h := URMState.step_of_getElem?_assign P s1 1 rAcc 0 hs1_pc h_outer_at_1
    rw [h]
  set s2 : URMState P :=
      { pc := 2
        regs := Function.update s1.regs rAcc 0 }
  -- Step 3 (PC 2): assignR vX 0.  s2 → s3.
  have hs2_pc : s2.pc = 2 := rfl
  have h_step2 :
      URMState.step P s2 =
        { pc := 3
          regs := Function.update s2.regs rVX 0 } := by
    have h := URMState.step_of_getElem?_assign P s2 2 rVX 0 hs2_pc h_outer_at_2
    rw [h]
  set s3 : URMState P :=
      { pc := 3
        regs := Function.update s2.regs rVX 0 }
  -- Step 4 (PC 3): assignR vI 0.  s3 → s4.
  have hs3_pc : s3.pc = 3 := rfl
  have h_step3 :
      URMState.step P s3 =
        { pc := 4
          regs := Function.update s3.regs rVI 0 } := by
    have h := URMState.step_of_getElem?_assign P s3 3 rVI 0 hs3_pc h_outer_at_3
    rw [h]
  set s4 : URMState P :=
      { pc := 4
        regs := Function.update s3.regs rVI 0 }
  -- runFor P s0 4 = s4.
  have h_runFor_4 : URMState.runFor P s0 4 = s4 := by
    have h_eq : (4 : ℕ) = 1 + 1 + 1 + 1 := by omega
    rw [h_eq]
    rw [URMState.runFor_add, URMState.runFor_add, URMState.runFor_add]
    rw [h_runFor_1]
    have h_runFor_s1_1 : URMState.runFor P s1 1 = s2 := by
      change URMState.runFor P (URMState.step P s1) 0 = _
      rw [URMState.runFor_zero, h_step1]
    rw [h_runFor_s1_1]
    have h_runFor_s2_1 : URMState.runFor P s2 1 = s3 := by
      change URMState.runFor P (URMState.step P s2) 0 = _
      rw [URMState.runFor_zero, h_step2]
    rw [h_runFor_s2_1]
    change URMState.runFor P (URMState.step P s3) 0 = _
    rw [URMState.runFor_zero, h_step3]
  -- s4 register values.
  have hs4_pc : s4.pc = 4 := rfl
  -- The four updated registers are pairwise distinct.
  have h_ne_rZ_rAcc : rZ ≠ rAcc := by
    intro h; have : (0 : ℕ) = 1 := congrArg Fin.val h; omega
  have h_ne_rZ_rVX : rZ ≠ rVX := by
    intro h; have : (0 : ℕ) = k + 3 := congrArg Fin.val h; omega
  have h_ne_rZ_rVI : rZ ≠ rVI := by
    intro h; have : (0 : ℕ) = k + 4 := congrArg Fin.val h; omega
  have h_ne_rAcc_rVX : rAcc ≠ rVX := by
    intro h; have : (1 : ℕ) = k + 3 := congrArg Fin.val h; omega
  have h_ne_rAcc_rVI : rAcc ≠ rVI := by
    intro h; have : (1 : ℕ) = k + 4 := congrArg Fin.val h; omega
  have h_ne_rVX_rVI : rVX ≠ rVI := by
    intro h; have : (k + 3 : ℕ) = k + 4 := congrArg Fin.val h; omega
  -- Compute s4.regs at each named register.
  have hs4_rZ : s4.regs rZ = 0 := by
    change Function.update s3.regs rVI 0 rZ = 0
    rw [Function.update_of_ne h_ne_rZ_rVI]
    change Function.update s2.regs rVX 0 rZ = 0
    rw [Function.update_of_ne h_ne_rZ_rVX]
    change Function.update s1.regs rAcc 0 rZ = 0
    rw [Function.update_of_ne h_ne_rZ_rAcc]
    change Function.update s0.regs rZ 0 rZ = 0
    rw [Function.update_self]
  have hs4_rAcc : s4.regs rAcc = 0 := by
    change Function.update s3.regs rVI 0 rAcc = 0
    rw [Function.update_of_ne h_ne_rAcc_rVI]
    change Function.update s2.regs rVX 0 rAcc = 0
    rw [Function.update_of_ne h_ne_rAcc_rVX]
    change Function.update s1.regs rAcc 0 rAcc = 0
    rw [Function.update_self]
  have hs4_rVX : s4.regs rVX = 0 := by
    change Function.update s3.regs rVI 0 rVX = 0
    rw [Function.update_of_ne h_ne_rVX_rVI]
    change Function.update s2.regs rVX 0 rVX = 0
    rw [Function.update_self]
  have hs4_rVI : s4.regs rVI = 0 := by
    change Function.update s3.regs rVI 0 rVI = 0
    rw [Function.update_self]
  -- For registers other than rZ/rAcc/rVX/rVI, s4 agrees with s0.
  have hs4_other : ∀ r : Fin P.numRegs,
      r ≠ rZ → r ≠ rAcc → r ≠ rVX → r ≠ rVI →
      s4.regs r = s0.regs r := by
    intro r hZ hAcc hVX hVI
    change Function.update s3.regs rVI 0 r = _
    rw [Function.update_of_ne hVI]
    change Function.update s2.regs rVX 0 r = _
    rw [Function.update_of_ne hVX]
    change Function.update s1.regs rAcc 0 r = _
    rw [Function.update_of_ne hAcc]
    change Function.update s0.regs rZ 0 r = _
    rw [Function.update_of_ne hZ]
  -- s4 at vBoundIn = v 0.
  have h_ne_BIn_rZ : rBoundIn ≠ rZ := by
    intro h; have : (2 : ℕ) = 0 := congrArg Fin.val h; omega
  have h_ne_BIn_rAcc : rBoundIn ≠ rAcc := by
    intro h; have : (2 : ℕ) = 1 := congrArg Fin.val h; omega
  have h_ne_BIn_rVI : rBoundIn ≠ rVI := by
    intro h; have : (2 : ℕ) = k + 4 := congrArg Fin.val h; omega
  have hs0_rBoundIn : s0.regs rBoundIn = v 0 := by
    have h_eq : (P.inputRegs 0 : Fin P.numRegs) = rBoundIn := by
      apply Fin.ext; exact h_outer_inputRegs 0
    change (URMState.init P v).regs rBoundIn = v 0
    rw [← h_eq]
    exact URMState.init_regs_inputRegs P v 0
  have hs4_rBoundIn : s4.regs rBoundIn = v 0 := by
    rw [hs4_other rBoundIn h_ne_BIn_rZ h_ne_BIn_rAcc h_disj_sd h_ne_BIn_rVI]
    exact hs0_rBoundIn
  have hs4_rTmp2 : s4.regs rTmp2 = 0 := by
    have h_ne_T2_rZ : rTmp2 ≠ rZ := by
      intro h; have : (k + 6 : ℕ) = 0 := congrArg Fin.val h; omega
    have h_ne_T2_rAcc : rTmp2 ≠ rAcc := by
      intro h; have : (k + 6 : ℕ) = 1 := congrArg Fin.val h; omega
    have h_ne_T2_rVI : rTmp2 ≠ rVI := by
      intro h; have : (k + 6 : ℕ) = k + 4 := congrArg Fin.val h; omega
    rw [hs4_other rTmp2 h_ne_T2_rZ h_ne_T2_rAcc h_disj_dt.symm h_ne_T2_rVI]
    change (URMState.init P v).regs rTmp2 = 0
    apply URMState.init_regs_zero_outside_inputs P v h_outer_inputRegs
    right; right
    change 2 + (k + 1) ≤ k + 6; omega
  -- Apply preservingTransfer_correct at pcBase = 4.
  obtain ⟨pt_pc, pt_dst, pt_src, pt_tmp, pt_z, pt_oth⟩ :=
    preservingTransfer_correct P 4 rBoundIn rVX rTmp2 rZ
      h_disj_sd h_disj_st h_disj_dt h_disj_zs h_disj_zd h_disj_zt
      H_pT s4 hs4_pc hs4_rZ hs4_rTmp2 (v 0) hs4_rBoundIn
  set s5 : URMState P := URMState.runFor P s4 (9 * (v 0) + 2)
  -- s5 register values.
  have hs5_pc : s5.pc = 13 := by
    have : (4 + 9 : ℕ) = 13 := by omega
    rw [← this]; exact pt_pc
  have hs5_rVX : s5.regs rVX = v 0 := by
    rw [pt_dst, hs4_rVX]; omega
  have hs5_rBoundIn : s5.regs rBoundIn = v 0 := by
    rw [pt_src]
  have hs5_rTmp2 : s5.regs rTmp2 = 0 := pt_tmp
  have hs5_rZ : s5.regs rZ = 0 := pt_z
  have hs5_other_of_ne_rVX : ∀ r : Fin P.numRegs, r ≠ rVX →
      s5.regs r = s4.regs r := pt_oth
  -- Step 6 (PC 13): incR vAcc.  s5 → s6.
  have h_step5 :
      URMState.step P s5 =
        { pc := 14
          regs := Function.update s5.regs rAcc (s5.regs rAcc + 1) } := by
    have h := URMState.step_of_getElem?_inc P s5 13 rAcc hs5_pc h_outer_at_13
    rw [h]
    have : s5.pc + 1 = 14 := by rw [hs5_pc]
    rw [this]
  set s6 : URMState P :=
      { pc := 14
        regs := Function.update s5.regs rAcc (s5.regs rAcc + 1) }
  -- Collapse `runFor` to land at `s6`.
  have h_runFor_s5_1 : URMState.runFor P s5 1 = s6 := by
    change URMState.runFor P (URMState.step P s5) 0 = _
    rw [URMState.runFor_zero, h_step5]
  have h_runFor_total :
      URMState.runFor P s0 (7 + 9 * (v 0)) = s6 := by
    have h_split :
        (7 + 9 * (v 0) : ℕ) = 4 + (9 * (v 0) + 2) + 1 := by omega
    rw [h_split, URMState.runFor_add, URMState.runFor_add, h_runFor_4,
      h_runFor_s5_1]
  rw [h_runFor_total]
  -- s5.regs rAcc = 0 (since rAcc ≠ rVX).
  have hs5_rAcc : s5.regs rAcc = 0 := by
    rw [hs5_other_of_ne_rVX rAcc h_ne_rAcc_rVX]
    exact hs4_rAcc
  -- s6.regs rAcc = 1.
  have hs6_rAcc : s6.regs rAcc = 1 := by
    change Function.update s5.regs rAcc (s5.regs rAcc + 1) rAcc = 1
    rw [Function.update_self, hs5_rAcc]
  -- For any r ≠ rAcc, s6.regs r = s5.regs r.
  have hs6_other_of_ne_rAcc : ∀ r : Fin P.numRegs, r ≠ rAcc →
      s6.regs r = s5.regs r := by
    intro r h
    change Function.update s5.regs rAcc (s5.regs rAcc + 1) r = _
    exact Function.update_of_ne h _ _
  -- Discharge each invariant clause.
  refine
    { hi_le := Nat.zero_le _
      pc_eq := ?_
      zReg_zero := ?_
      outer_inputs := ?_
      vX_eq := ?_
      vI_eq := ?_
      tmp1_zero := ?_
      tmp2_zero := ?_
      accClone_zero := ?_
      factor_zero := ?_
      mulTmp_zero := ?_
      acc_eq := ?_ }
  · -- PC = bprod_topPC = 14.
    change s6.pc = bprod_topPC
    change (14 : ℕ) = bprod_topPC
    rfl
  · -- V_z = 0.
    have h_ne_rZ_rAcc' : rZ ≠ rAcc := h_ne_rZ_rAcc
    rw [hs6_other_of_ne_rAcc rZ h_ne_rZ_rAcc']
    exact hs5_rZ
  · -- Outer inputs preserved.
    intro j
    have hj : j.val < k + 1 := j.isLt
    have h_ne_rAcc' :
        (⟨2 + j.val, by
          change 2 + j.val < k + 10 + frag_f.numRegs
          have : 0 < frag_f.numRegs := frag_f.numRegs_pos; omega⟩ :
          Fin P.numRegs) ≠ rAcc := by
      intro h
      have : (2 + j.val : ℕ) = 1 := congrArg Fin.val h
      omega
    rw [hs6_other_of_ne_rAcc _ h_ne_rAcc']
    have h_ne_rVX :
        (⟨2 + j.val, by
          change 2 + j.val < k + 10 + frag_f.numRegs
          have : 0 < frag_f.numRegs := frag_f.numRegs_pos; omega⟩ :
          Fin P.numRegs) ≠ rVX := by
      intro h
      have : (2 + j.val : ℕ) = k + 3 := congrArg Fin.val h
      omega
    rw [hs5_other_of_ne_rVX _ h_ne_rVX]
    have h_ne_rZ :
        (⟨2 + j.val, by
          change 2 + j.val < k + 10 + frag_f.numRegs
          have : 0 < frag_f.numRegs := frag_f.numRegs_pos; omega⟩ :
          Fin P.numRegs) ≠ rZ := by
      intro h; have : (2 + j.val : ℕ) = 0 := congrArg Fin.val h; omega
    have h_ne_rVI :
        (⟨2 + j.val, by
          change 2 + j.val < k + 10 + frag_f.numRegs
          have : 0 < frag_f.numRegs := frag_f.numRegs_pos; omega⟩ :
          Fin P.numRegs) ≠ rVI := by
      intro h; have : (2 + j.val : ℕ) = k + 4 := congrArg Fin.val h; omega
    rw [hs4_other _ h_ne_rZ h_ne_rAcc' h_ne_rVX h_ne_rVI]
    have h_eq : (P.inputRegs j : Fin P.numRegs)
        = ⟨2 + j.val, by
          change 2 + j.val < k + 10 + frag_f.numRegs
          have : 0 < frag_f.numRegs := frag_f.numRegs_pos; omega⟩ := by
      apply Fin.ext; exact h_outer_inputRegs j
    change s0.regs _ = v j
    rw [← h_eq]
    exact URMState.init_regs_inputRegs P v j
  · -- V_x = v 0 - 0 = v 0.
    change s6.regs rVX = v 0 - 0
    have h_ne_rVX_rAcc : rVX ≠ rAcc := h_ne_rAcc_rVX.symm
    rw [hs6_other_of_ne_rAcc rVX h_ne_rVX_rAcc, hs5_rVX]
    omega
  · -- V_i = 0.
    change s6.regs rVI = 0
    have h_ne_rVI_rAcc : rVI ≠ rAcc := h_ne_rAcc_rVI.symm
    rw [hs6_other_of_ne_rAcc rVI h_ne_rVI_rAcc]
    have h_ne_rVI_rVX : rVI ≠ rVX := h_ne_rVX_rVI.symm
    rw [hs5_other_of_ne_rVX rVI h_ne_rVI_rVX]
    exact hs4_rVI
  · -- tmp1 = 0.
    change s6.regs rTmp1 = 0
    have h_ne_rTmp1_rAcc : rTmp1 ≠ rAcc := by
      intro h; have : (k + 5 : ℕ) = 1 := congrArg Fin.val h; omega
    rw [hs6_other_of_ne_rAcc rTmp1 h_ne_rTmp1_rAcc]
    have h_ne_rTmp1_rVX : rTmp1 ≠ rVX := by
      intro h; have : (k + 5 : ℕ) = k + 3 := congrArg Fin.val h; omega
    rw [hs5_other_of_ne_rVX rTmp1 h_ne_rTmp1_rVX]
    have h_ne_rTmp1_rZ : rTmp1 ≠ rZ := by
      intro h; have : (k + 5 : ℕ) = 0 := congrArg Fin.val h; omega
    have h_ne_rTmp1_rVI : rTmp1 ≠ rVI := by
      intro h; have : (k + 5 : ℕ) = k + 4 := congrArg Fin.val h; omega
    rw [hs4_other rTmp1 h_ne_rTmp1_rZ h_ne_rTmp1_rAcc h_ne_rTmp1_rVX
      h_ne_rTmp1_rVI]
    change (URMState.init P v).regs rTmp1 = 0
    apply URMState.init_regs_zero_outside_inputs P v h_outer_inputRegs
    right; right
    change 2 + (k + 1) ≤ k + 5; omega
  · -- tmp2 = 0.
    change s6.regs rTmp2 = 0
    have h_ne_rTmp2_rAcc : rTmp2 ≠ rAcc := by
      intro h; have : (k + 6 : ℕ) = 1 := congrArg Fin.val h; omega
    rw [hs6_other_of_ne_rAcc rTmp2 h_ne_rTmp2_rAcc]
    exact hs5_rTmp2
  · -- V_acc_clone = 0.
    change s6.regs rAccClone = 0
    have h_ne_rAC_rAcc : rAccClone ≠ rAcc := by
      intro h; have : (k + 7 : ℕ) = 1 := congrArg Fin.val h; omega
    rw [hs6_other_of_ne_rAcc rAccClone h_ne_rAC_rAcc]
    have h_ne_rAC_rVX : rAccClone ≠ rVX := by
      intro h; have : (k + 7 : ℕ) = k + 3 := congrArg Fin.val h; omega
    rw [hs5_other_of_ne_rVX rAccClone h_ne_rAC_rVX]
    have h_ne_rAC_rZ : rAccClone ≠ rZ := by
      intro h; have : (k + 7 : ℕ) = 0 := congrArg Fin.val h; omega
    have h_ne_rAC_rVI : rAccClone ≠ rVI := by
      intro h; have : (k + 7 : ℕ) = k + 4 := congrArg Fin.val h; omega
    rw [hs4_other rAccClone h_ne_rAC_rZ h_ne_rAC_rAcc h_ne_rAC_rVX
      h_ne_rAC_rVI]
    change (URMState.init P v).regs rAccClone = 0
    apply URMState.init_regs_zero_outside_inputs P v h_outer_inputRegs
    right; right
    change 2 + (k + 1) ≤ k + 7; omega
  · -- V_factor = 0.
    change s6.regs rFactor = 0
    have h_ne_rF_rAcc : rFactor ≠ rAcc := by
      intro h; have : (k + 8 : ℕ) = 1 := congrArg Fin.val h; omega
    rw [hs6_other_of_ne_rAcc rFactor h_ne_rF_rAcc]
    have h_ne_rF_rVX : rFactor ≠ rVX := by
      intro h; have : (k + 8 : ℕ) = k + 3 := congrArg Fin.val h; omega
    rw [hs5_other_of_ne_rVX rFactor h_ne_rF_rVX]
    have h_ne_rF_rZ : rFactor ≠ rZ := by
      intro h; have : (k + 8 : ℕ) = 0 := congrArg Fin.val h; omega
    have h_ne_rF_rVI : rFactor ≠ rVI := by
      intro h; have : (k + 8 : ℕ) = k + 4 := congrArg Fin.val h; omega
    rw [hs4_other rFactor h_ne_rF_rZ h_ne_rF_rAcc h_ne_rF_rVX
      h_ne_rF_rVI]
    change (URMState.init P v).regs rFactor = 0
    apply URMState.init_regs_zero_outside_inputs P v h_outer_inputRegs
    right; right
    change 2 + (k + 1) ≤ k + 8; omega
  · -- V_mul_tmp = 0.
    change s6.regs rMulTmp = 0
    have h_ne_rMT_rAcc : rMulTmp ≠ rAcc := by
      intro h; have : (k + 9 : ℕ) = 1 := congrArg Fin.val h; omega
    rw [hs6_other_of_ne_rAcc rMulTmp h_ne_rMT_rAcc]
    have h_ne_rMT_rVX : rMulTmp ≠ rVX := by
      intro h; have : (k + 9 : ℕ) = k + 3 := congrArg Fin.val h; omega
    rw [hs5_other_of_ne_rVX rMulTmp h_ne_rMT_rVX]
    have h_ne_rMT_rZ : rMulTmp ≠ rZ := by
      intro h; have : (k + 9 : ℕ) = 0 := congrArg Fin.val h; omega
    have h_ne_rMT_rVI : rMulTmp ≠ rVI := by
      intro h; have : (k + 9 : ℕ) = k + 4 := congrArg Fin.val h; omega
    rw [hs4_other rMulTmp h_ne_rMT_rZ h_ne_rMT_rAcc h_ne_rMT_rVX
      h_ne_rMT_rVI]
    change (URMState.init P v).regs rMulTmp = 0
    apply URMState.init_regs_zero_outside_inputs P v h_outer_inputRegs
    right; right
    change 2 + (k + 1) ≤ k + 9; omega
  · -- Accumulator = natBProd 0 ... = 1.
    change s6.regs rAcc = natBProd 0 _
    rw [hs6_rAcc]
    rfl

/-- Zero-sweep instruction-presence discharger for `compileFrag_bprod`:
at PCs `bprod_zeroSweepBase + r.val` for `r : Fin frag_f.numRegs`, the
outer program's instruction is `URMInstr.assign ⟨(k + 10) + r.val, _⟩ 0`.
Mirrors `compileFrag_bsum_zeroSweep_instr_at`, specialised to bprod's
prelude (`14` instructions: four `assignR`s, the nine-instruction
`preservingTransfer` block, and the trailing `incR vAcc`) and bprod's
`fBase = k + 10`. -/
private theorem compileFrag_bprod_zeroSweep_instr_at
    {k : ℕ}
    (frag_f : CompiledFragment (k + 1))
    (r : Fin frag_f.numRegs) :
    ∃ h : (k + 10) + r.val
        < (compileFrag_bprod frag_f).toURMProgram.numRegs,
      (compileFrag_bprod frag_f).toURMProgram.instrs[
          bprod_zeroSweepBase + r.val]?
        = some (URMInstr.assign
            ⟨(k + 10) + r.val, h⟩ 0) := by
  -- Abbreviations matching the constructor of `compileFrag_bprod`.
  let vAcc : ℕ := 1
  let vBoundIn : ℕ := 2
  let vX : ℕ := k + 3
  let vI : ℕ := k + 4
  let tmp1 : ℕ := k + 5
  let tmp2 : ℕ := k + 6
  let vAccClone : ℕ := k + 7
  let vFactor : ℕ := k + 8
  let vMulTmp : ℕ := k + 9
  let fBase : ℕ := k + 10
  let nR : ℕ := fBase + frag_f.numRegs
  let topPC : ℕ := 14
  let bodyStartPC : ℕ := 15
  let prologueBase : ℕ := 16 + frag_f.numRegs
  let bodyPCBase : ℕ := 16 + frag_f.numRegs + 9 * (k + 1)
  let fBodyLen : ℕ := frag_f.instrs.size - 1
  let trBase : ℕ := bodyPCBase + fBodyLen
  let exitPC : ℕ := trBase + 23
  let prelude : List URMInstrRaw :=
    [ .assignR 0 0,
      .assignR vAcc 0,
      .assignR vX 0,
      .assignR vI 0 ]
        ++ URMRaw.preservingTransfer 4 vBoundIn vX tmp2
        ++ [ .incR vAcc ]
  let loopTop : List URMInstrRaw :=
    [ .jumpZR vX exitPC bodyStartPC,
      .decR vX ]
  let zeroSweep : List URMInstrRaw :=
    bsum_zeroSweep frag_f fBase
  let prologue : List URMInstrRaw :=
    (List.finRange (k + 1)).flatMap fun s =>
      bsum_prologueBlock frag_f fBase tmp1 prologueBase s
  let fBody : List URMInstrRaw :=
    frag_f.instrs.pop.toList.map fun ins =>
      URMInstrRaw.reindexShift fBase bodyPCBase (toRawOfBounded ins)
  let accUpdate : List URMInstrRaw :=
    URMRaw.transferLoop trBase vAcc vAccClone
      ++ URMRaw.transferLoop (trBase + 4)
          (fBase + frag_f.outputReg.val) vFactor
      ++ [ .jumpZR vFactor (trBase + 20) (trBase + 9),
           .decR vFactor ]
      ++ URMRaw.preservingTransfer (trBase + 10)
          vAccClone vAcc vMulTmp
      ++ [ URMRaw.goto (trBase + 8),
           .assignR vAccClone 0 ]
  let epilogue : List URMInstrRaw :=
    [ .incR vI, URMRaw.goto topPC, .stopR ]
  let rawList : List URMInstrRaw :=
    prelude ++ loopTop ++ zeroSweep ++ prologue ++ fBody
      ++ accUpdate ++ epilogue
  -- Segment lengths.
  have h_prelude_len : prelude.length = 14 := by
    change ([URMInstrRaw.assignR 0 0, URMInstrRaw.assignR vAcc 0,
        URMInstrRaw.assignR vX 0, URMInstrRaw.assignR vI 0]
        ++ URMRaw.preservingTransfer 4 vBoundIn vX tmp2
        ++ [URMInstrRaw.incR vAcc]).length = 14
    simp only [List.length_append, List.length_cons, List.length_nil,
      URMRaw.preservingTransfer, URMRaw.goto]
  have h_loopTop_len : loopTop.length = 2 := by
    change ([URMInstrRaw.jumpZR vX exitPC bodyStartPC,
      URMInstrRaw.decR vX] : List URMInstrRaw).length = 2
    simp only [List.length_cons, List.length_nil]
  have h_zeroSweep_len : zeroSweep.length = frag_f.numRegs := by
    change ((List.finRange frag_f.numRegs).map _).length = _
    rw [List.length_map, List.length_finRange]
  -- outer.numRegs = nR.
  let outer : URMProgram (k + 1) := (compileFrag_bprod frag_f).toURMProgram
  have h_lt : (k + 10) + r.val < outer.numRegs := by
    have hr : r.val < frag_f.numRegs := r.isLt
    change (k + 10) + r.val < (k + 10) + frag_f.numRegs
    omega
  refine ⟨h_lt, ?_⟩
  -- Reconstruct the boundedness witness on rawList.
  have hAcc : vAcc + 1 ≤ nR := by
    change 1 + 1 ≤ k + 10 + frag_f.numRegs
    have : 0 < frag_f.numRegs := frag_f.numRegs_pos; omega
  have hBoundIn : vBoundIn + 1 ≤ nR := by
    change 2 + 1 ≤ k + 10 + frag_f.numRegs
    have : 0 < frag_f.numRegs := frag_f.numRegs_pos; omega
  have hVX : vX + 1 ≤ nR := by
    change k + 3 + 1 ≤ k + 10 + frag_f.numRegs
    have : 0 < frag_f.numRegs := frag_f.numRegs_pos; omega
  have hVI : vI + 1 ≤ nR := by
    change k + 4 + 1 ≤ k + 10 + frag_f.numRegs
    have : 0 < frag_f.numRegs := frag_f.numRegs_pos; omega
  have hTmp1 : tmp1 + 1 ≤ nR := by
    change k + 5 + 1 ≤ k + 10 + frag_f.numRegs
    have : 0 < frag_f.numRegs := frag_f.numRegs_pos; omega
  have hTmp2 : tmp2 + 1 ≤ nR := by
    change k + 6 + 1 ≤ k + 10 + frag_f.numRegs
    have : 0 < frag_f.numRegs := frag_f.numRegs_pos; omega
  have hAccClone : vAccClone + 1 ≤ nR := by
    change k + 7 + 1 ≤ k + 10 + frag_f.numRegs
    have : 0 < frag_f.numRegs := frag_f.numRegs_pos; omega
  have hFactor : vFactor + 1 ≤ nR := by
    change k + 8 + 1 ≤ k + 10 + frag_f.numRegs
    have : 0 < frag_f.numRegs := frag_f.numRegs_pos; omega
  have hMulTmp : vMulTmp + 1 ≤ nR := by
    change k + 9 + 1 ≤ k + 10 + frag_f.numRegs
    have : 0 < frag_f.numRegs := frag_f.numRegs_pos; omega
  have hFOut : fBase + frag_f.outputReg.val + 1 ≤ nR := by
    have : frag_f.outputReg.val < frag_f.numRegs :=
      frag_f.outputReg.isLt
    change fBase + frag_f.outputReg.val + 1 ≤ fBase + frag_f.numRegs
    omega
  have hPrologueSrc : ∀ s : Fin (k + 1),
      bsum_prologueSrc k s + 1 ≤ nR := by
    intro s
    have hs : s.val < k + 1 := s.isLt
    simp only [bsum_prologueSrc, nR, fBase]
    split <;> omega
  have hFIn : ∀ s : Fin (k + 1),
      fBase + (frag_f.inputRegs s).val + 1 ≤ nR := by
    intro s
    have : (frag_f.inputRegs s).val < frag_f.numRegs :=
      (frag_f.inputRegs s).isLt
    change fBase + (frag_f.inputRegs s).val + 1
        ≤ fBase + frag_f.numRegs
    omega
  have hPreludeBound : URMInstrRaw.boundedBy nR prelude := by
    intro ins hmem
    simp only [prelude, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hmem
    rcases hmem with ((h | h | h | h) | hpT) | h
    · rw [h]; simp only [URMInstrRaw.regBound]; omega
    · rw [h]; simp only [URMInstrRaw.regBound]; exact hAcc
    · rw [h]; simp only [URMInstrRaw.regBound]; exact hVX
    · rw [h]; simp only [URMInstrRaw.regBound]; exact hVI
    · exact boundedBy_preservingTransfer nR _ _ _ _
        hBoundIn hVX hTmp2 ins hpT
    · rw [h]; simp only [URMInstrRaw.regBound]; exact hAcc
  have hLoopTopBound : URMInstrRaw.boundedBy nR loopTop := by
    intro ins hmem
    simp only [loopTop, List.mem_cons, List.not_mem_nil,
      or_false] at hmem
    rcases hmem with h | h <;>
      (rw [h]; simp only [URMInstrRaw.regBound]; exact hVX)
  have hZeroSweepBound : URMInstrRaw.boundedBy nR zeroSweep := by
    have hBlock : fBase + frag_f.numRegs ≤ nR := Nat.le_refl _
    exact boundedBy_bsum_zeroSweep frag_f fBase nR hBlock
  have hPrologueBound : URMInstrRaw.boundedBy nR prologue := by
    intro ins hmem
    simp only [prologue, List.mem_flatMap] at hmem
    rcases hmem with ⟨s, _, hs⟩
    exact boundedBy_bsum_prologueBlock frag_f fBase tmp1
      prologueBase nR s (hPrologueSrc s) (hFIn s) hTmp1 ins hs
  have hFBodyBound : URMInstrRaw.boundedBy nR fBody := by
    intro ins hmem
    simp only [fBody, List.mem_map] at hmem
    rcases hmem with ⟨ins', _, heq⟩
    rw [← heq]
    have hb : (toRawOfBounded ins').regBound ≤ frag_f.numRegs :=
      regBound_toRawOfBounded_le ins'
    have hr := regBound_reindexShift_le_offset_add fBase
      bodyPCBase frag_f.numRegs (toRawOfBounded ins') hb
    change _ ≤ fBase + frag_f.numRegs
    omega
  have hAccUpdateBound : URMInstrRaw.boundedBy nR accUpdate := by
    intro ins hmem
    simp only [accUpdate, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hmem
    rcases hmem with
      ((((hTr1 | hTr2) | hOuter) | hInner) | hTail)
    · exact boundedBy_transferLoop nR _ _ _
        hAcc hAccClone ins hTr1
    · exact boundedBy_transferLoop nR _ _ _
        hFOut hFactor ins hTr2
    · rcases hOuter with h | h
      · rw [h]; simp only [URMInstrRaw.regBound]; exact hFactor
      · rw [h]; simp only [URMInstrRaw.regBound]; exact hFactor
    · exact boundedBy_preservingTransfer nR _ _ _ _
        hAccClone hAcc hMulTmp ins hInner
    · rcases hTail with h | h
      · rw [h]; simp only [URMRaw.goto, URMInstrRaw.regBound]
        omega
      · rw [h]; simp only [URMInstrRaw.regBound]; exact hAccClone
  have hEpilogueBound : URMInstrRaw.boundedBy nR epilogue := by
    intro ins hmem
    simp only [epilogue, URMRaw.goto, List.mem_cons,
      List.not_mem_nil, or_false] at hmem
    rcases hmem with h | h | h
    · rw [h]; simp only [URMInstrRaw.regBound]; exact hVI
    · rw [h]; simp only [URMInstrRaw.regBound]; omega
    · rw [h]; simp only [URMInstrRaw.regBound]; omega
  have hBoundOuter : URMInstrRaw.boundedBy nR rawList := by
    intro ins hmem
    simp only [rawList, List.mem_append] at hmem
    rcases hmem with
      (((((hP | hL') | hZ) | hPr) | hF) | hA) | hE
    · exact hPreludeBound ins hP
    · exact hLoopTopBound ins hL'
    · exact hZeroSweepBound ins hZ
    · exact hPrologueBound ins hPr
    · exact hFBodyBound ins hF
    · exact hAccUpdateBound ins hA
    · exact hEpilogueBound ins hE
  -- outer.instrs is definitionally toBoundedArray nR rawList hBoundOuter.
  -- Index of `bprod_zeroSweepBase + r.val` (= `16 + r.val`) in rawList:
  -- lies inside the zero-sweep segment, which starts at
  -- `prelude.length + loopTop.length = 14 + 2 = 16`.
  have hr : r.val < frag_f.numRegs := r.isLt
  have h_idx_lt : bprod_zeroSweepBase + r.val < rawList.length := by
    have h_raw_len : rawList.length
        = prelude.length + loopTop.length + zeroSweep.length
          + prologue.length + fBody.length + accUpdate.length
          + epilogue.length := by
      change (prelude ++ loopTop ++ zeroSweep ++ prologue ++ fBody
        ++ accUpdate ++ epilogue).length = _
      simp only [List.length_append]
    rw [h_raw_len, h_prelude_len, h_loopTop_len, h_zeroSweep_len]
    change 16 + r.val < _
    omega
  change (URMInstrRaw.toBoundedArray nR rawList hBoundOuter)[
      bprod_zeroSweepBase + r.val]?
    = some (URMInstrRaw.toBounded nR
        (URMInstrRaw.assignR (fBase + r.val) 0)
        (by simp only [URMInstrRaw.regBound]; omega))
  rw [URMInstrRaw.toBoundedArray_getElem? nR rawList hBoundOuter
      (bprod_zeroSweepBase + r.val) h_idx_lt]
  -- Establish the raw equality:
  --   rawList[bprod_zeroSweepBase + r.val] = .assignR (fBase + r.val) 0.
  have h_raw_eq :
      rawList[bprod_zeroSweepBase + r.val]'h_idx_lt
        = URMInstrRaw.assignR (fBase + r.val) 0 := by
    have h_in_prefix6 :
        bprod_zeroSweepBase + r.val
          < ((((((prelude ++ loopTop) ++ zeroSweep) ++ prologue)
              ++ fBody) ++ accUpdate)).length := by
      simp only [List.length_append]
      rw [h_prelude_len, h_loopTop_len, h_zeroSweep_len]
      change 16 + r.val < _
      omega
    have h_in_prefix5 :
        bprod_zeroSweepBase + r.val
          < (((((prelude ++ loopTop) ++ zeroSweep) ++ prologue)
              ++ fBody)).length := by
      simp only [List.length_append]
      rw [h_prelude_len, h_loopTop_len, h_zeroSweep_len]
      change 16 + r.val < _
      omega
    have h_in_prefix4 :
        bprod_zeroSweepBase + r.val
          < ((((prelude ++ loopTop) ++ zeroSweep) ++ prologue)).length := by
      simp only [List.length_append]
      rw [h_prelude_len, h_loopTop_len, h_zeroSweep_len]
      change 16 + r.val < _
      omega
    have h_in_prefix3 :
        bprod_zeroSweepBase + r.val
          < (((prelude ++ loopTop) ++ zeroSweep)).length := by
      simp only [List.length_append]
      rw [h_prelude_len, h_loopTop_len, h_zeroSweep_len]
      change 16 + r.val < _
      omega
    have h_step1 :
        rawList[bprod_zeroSweepBase + r.val]'h_idx_lt
          = ((((((prelude ++ loopTop) ++ zeroSweep) ++ prologue)
                ++ fBody) ++ accUpdate))[
              bprod_zeroSweepBase + r.val]'h_in_prefix6 := by
      change (((((((prelude ++ loopTop) ++ zeroSweep) ++ prologue)
            ++ fBody) ++ accUpdate) ++ epilogue))[
          bprod_zeroSweepBase + r.val]'h_idx_lt
        = _
      rw [List.getElem_append_left h_in_prefix6]
    rw [h_step1]
    have h_step2 :
        ((((((prelude ++ loopTop) ++ zeroSweep) ++ prologue)
              ++ fBody) ++ accUpdate))[
            bprod_zeroSweepBase + r.val]'h_in_prefix6
          = (((((prelude ++ loopTop) ++ zeroSweep) ++ prologue)
                ++ fBody))[bprod_zeroSweepBase + r.val]'h_in_prefix5 := by
      rw [List.getElem_append_left h_in_prefix5]
    rw [h_step2]
    have h_step3 :
        (((((prelude ++ loopTop) ++ zeroSweep) ++ prologue)
              ++ fBody))[bprod_zeroSweepBase + r.val]'h_in_prefix5
          = ((((prelude ++ loopTop) ++ zeroSweep) ++ prologue))[
              bprod_zeroSweepBase + r.val]'h_in_prefix4 := by
      rw [List.getElem_append_left h_in_prefix4]
    rw [h_step3]
    have h_step4 :
        ((((prelude ++ loopTop) ++ zeroSweep) ++ prologue))[
            bprod_zeroSweepBase + r.val]'h_in_prefix4
          = (((prelude ++ loopTop) ++ zeroSweep))[
              bprod_zeroSweepBase + r.val]'h_in_prefix3 := by
      rw [List.getElem_append_left h_in_prefix3]
    rw [h_step4]
    -- Peel prelude++loopTop: index ≥ (prelude++loopTop).length = 16.
    have h_pref2_le :
        ((prelude ++ loopTop)).length ≤ bprod_zeroSweepBase + r.val := by
      simp only [List.length_append]
      rw [h_prelude_len, h_loopTop_len]
      change _ ≤ 16 + r.val
      omega
    have h_idx_in_sweep :
        bprod_zeroSweepBase + r.val - (prelude ++ loopTop).length
        < zeroSweep.length := by
      simp only [List.length_append]
      rw [h_prelude_len, h_loopTop_len, h_zeroSweep_len]
      change 16 + r.val - _ < _
      omega
    have h_step5 :
        (((prelude ++ loopTop) ++ zeroSweep))[
            bprod_zeroSweepBase + r.val]'h_in_prefix3
          = zeroSweep[
              bprod_zeroSweepBase + r.val
                - (prelude ++ loopTop).length]'h_idx_in_sweep := by
      rw [List.getElem_append_right h_pref2_le]
    rw [h_step5]
    -- Simplify the index inside zeroSweep to r.val.
    have h_idx_eq :
        bprod_zeroSweepBase + r.val - (prelude ++ loopTop).length = r.val := by
      simp only [List.length_append]
      rw [h_prelude_len, h_loopTop_len]
      change 16 + r.val - 16 = _
      omega
    have h_r_lt_sweep : r.val < zeroSweep.length := by
      rw [h_zeroSweep_len]; exact hr
    have h_step6 :
        zeroSweep[
            bprod_zeroSweepBase + r.val
              - (prelude ++ loopTop).length]'h_idx_in_sweep
          = zeroSweep[r.val]'h_r_lt_sweep := by
      congr 1
    rw [h_step6]
    -- zeroSweep[r.val] = (.assignR (fBase + r.val) 0).
    have h_r_lt_fin : r.val < (List.finRange frag_f.numRegs).length := by
      rw [List.length_finRange]; exact hr
    change ((List.finRange frag_f.numRegs).map (fun s =>
        (URMInstrRaw.assignR (fBase + s.val) 0 : URMInstrRaw)))[r.val]'_
      = _
    rw [List.getElem_map]
    have h_finRange_at : (List.finRange frag_f.numRegs)[r.val]'h_r_lt_fin
        = ⟨r.val, hr⟩ := by
      apply List.getElem_finRange
    rw [h_finRange_at]
  -- Push through `toBounded` and `some`.
  apply congrArg some
  exact URMInstrRaw.toBounded_congr nR h_raw_eq _ _

/-- Post-state predicate for Phase i.0 of one bprod iteration: the state
immediately after executing the loop-top `jumpZR vX` (taking the
non-zero branch, since `i.val < v 0` means `s.regs vX = v 0 - i.val
> 0`), the body-start `decR vX`, and the `frag_f.numRegs`
`assignR ((k + 10) + r) 0` zero-sweep instructions. PC sits at
`bprod_prologueBase frag_f = 16 + frag_f.numRegs`, the first
instruction of the per-iteration prologue. The `vX_eq` clause records
the decrement (`v 0 - i.val - 1`), and `fBody_zero` records that f's
reindexed block has just been re-flushed to `0`. All other clauses
(`hi_lt`, `zReg_zero`, `outer_inputs`, `vI_eq`, `tmp1_zero`,
`tmp2_zero`, `accClone_zero`, `factor_zero`, `mulTmp_zero`, `acc_eq`)
carry over verbatim from `compileFrag_bprod_partial_invariant
@ i.val`. -/
private structure compileFrag_bprod_phase_i0_post
    {k : ℕ}
    (frag_f : CompiledFragment (k + 1))
    (f : ERMor1 (k + 1))
    (v : Fin (k + 1) → ℕ)
    (i : Fin (v 0))
    (s : URMState (compileFrag_bprod frag_f).toURMProgram)
    : Prop where
  /-- `i.val < v 0`, packaged for downstream consumers. -/
  hi_lt : i.val < v 0 := i.isLt
  /-- PC sits one past the zero-sweep, at the start of the
  per-iteration prologue. -/
  pc_eq : s.pc = bprod_prologueBase frag_f
  /-- `V_z` (register 0) holds `0`. -/
  zReg_zero : s.regs ⟨0, (compileFrag_bprod frag_f).numRegs_pos⟩ = 0
  /-- Outer input slots `2..k+2` hold the input vector. -/
  outer_inputs : ∀ (j : Fin (k + 1)),
    s.regs ⟨2 + j.val, by
      have hj : j.val < k + 1 := j.isLt
      change 2 + j.val < k + 10 + frag_f.numRegs
      have : 0 < frag_f.numRegs := frag_f.numRegs_pos
      omega⟩ = v j
  /-- `V_x` (register `k + 3`) holds `v 0 - i.val - 1` after the
  body-start `decR vX`. -/
  vX_eq : s.regs ⟨k + 3, by
    change k + 3 < k + 10 + frag_f.numRegs
    have : 0 < frag_f.numRegs := frag_f.numRegs_pos
    omega⟩ = v 0 - i.val - 1
  /-- `V_i` (register `k + 4`) still holds the pre-iteration counter
  `i.val`; the body's `incR vI` lives in Phase i.3. -/
  vI_eq : s.regs ⟨k + 4, by
    change k + 4 < k + 10 + frag_f.numRegs
    have : 0 < frag_f.numRegs := frag_f.numRegs_pos
    omega⟩ = i.val
  /-- Scratch register `tmp1` (register `k + 5`) is `0`. -/
  tmp1_zero : s.regs ⟨k + 5, by
    change k + 5 < k + 10 + frag_f.numRegs
    have : 0 < frag_f.numRegs := frag_f.numRegs_pos
    omega⟩ = 0
  /-- Scratch register `tmp2` (register `k + 6`) is `0`. -/
  tmp2_zero : s.regs ⟨k + 6, by
    change k + 6 < k + 10 + frag_f.numRegs
    have : 0 < frag_f.numRegs := frag_f.numRegs_pos
    omega⟩ = 0
  /-- Multiplicative scratch `V_acc_clone` (register `k + 7`) is `0`. -/
  accClone_zero : s.regs ⟨k + 7, by
    change k + 7 < k + 10 + frag_f.numRegs
    have : 0 < frag_f.numRegs := frag_f.numRegs_pos
    omega⟩ = 0
  /-- Multiplicative scratch `V_factor` (register `k + 8`) is `0`. -/
  factor_zero : s.regs ⟨k + 8, by
    change k + 8 < k + 10 + frag_f.numRegs
    have : 0 < frag_f.numRegs := frag_f.numRegs_pos
    omega⟩ = 0
  /-- Multiplicative scratch `V_mul_tmp` (register `k + 9`) is `0`. -/
  mulTmp_zero : s.regs ⟨k + 9, by
    change k + 9 < k + 10 + frag_f.numRegs
    have : 0 < frag_f.numRegs := frag_f.numRegs_pos
    omega⟩ = 0
  /-- The accumulator (register 1) still holds the pre-iteration
  partial product `Π_{j < i.val} f.interp (j :: tail v)`. -/
  acc_eq : s.regs ⟨1, by
    change 1 < k + 10 + frag_f.numRegs
    have : 0 < frag_f.numRegs := frag_f.numRegs_pos
    omega⟩
      = natBProd i.val (fun j => f.interp (Fin.cons j (Fin.tail v)))
  /-- f's reindexed register block has just been flushed to `0`
  by the zero-sweep. -/
  fBody_zero : ∀ r : Fin frag_f.numRegs,
    s.regs ⟨(k + 10) + r.val, by
      have hr : r.val < frag_f.numRegs := r.isLt
      change (k + 10) + r.val < k + 10 + frag_f.numRegs
      omega⟩ = 0

set_option maxHeartbeats 1000000 in
-- The proof discharges a 12-field structure through three sub-stages
-- (jumpZ, dec, zero-sweep) on a heartbeat-heavy `compileFrag_bprod`
-- numRegs profile; the elaborator's default budget is exhausted by
-- the cumulative whnf load.
/-- Phase i.0 preservation lemma: from
`compileFrag_bprod_partial_invariant @ i.val`, running for
`2 + (compileERFrag f).numRegs` further steps (the loop-top
`jumpZR vX` non-zero branch, the body-start `decR vX`, and the
`numRegs_f` zero-sweep `assignR` instructions) lands the state
in `compileFrag_bprod_phase_i0_post @ i`. The accompanying strict PC
bound states that during these `2 + numRegs_f` steps the intermediate
PC stays below `bprod_prologueBase (compileERFrag f) = 16 + numRegs_f`. -/
private theorem compileFrag_bprod_partial_phase_i0
    {k : ℕ}
    (f : ERMor1 (k + 1))
    (v : Fin (k + 1) → ℕ)
    (i : Fin (v 0))
    (sPre : URMState
      (compileFrag_bprod (compileERFrag f)).toURMProgram)
    (h_inv : compileFrag_bprod_partial_invariant
              (compileERFrag f) f v i.val i.isLt.le sPre) :
    compileFrag_bprod_phase_i0_post (compileERFrag f) f v i
      (URMState.runFor (compileFrag_bprod (compileERFrag f)).toURMProgram
        sPre (2 + (compileERFrag f).numRegs)) ∧
    (∀ k' < 2 + (compileERFrag f).numRegs,
      (URMState.runFor (compileFrag_bprod (compileERFrag f)).toURMProgram
        sPre k').pc
        < bprod_prologueBase (compileERFrag f)) := by
  -- Abbreviations matching the outer program.
  let frag_f : CompiledFragment (k + 1) := compileERFrag f
  let outerFrag : CompiledFragment (k + 1) := compileFrag_bprod frag_f
  let P : URMProgram (k + 1) := outerFrag.toURMProgram
  change compileFrag_bprod_phase_i0_post frag_f f v i
      (URMState.runFor P sPre (2 + frag_f.numRegs)) ∧
    (∀ k' < 2 + frag_f.numRegs,
      (URMState.runFor P sPre k').pc < bprod_prologueBase frag_f)
  have h_numRegs_eq : P.numRegs = (k + 10) + frag_f.numRegs := rfl
  have h_numRegs_pos : 0 < P.numRegs := outerFrag.numRegs_pos
  -- Bound proofs for the named registers.
  have h_vX_lt : k + 3 < P.numRegs := by
    rw [h_numRegs_eq]
    have : 0 < frag_f.numRegs := frag_f.numRegs_pos; omega
  -- Fin-wrapped vX handle.
  let rVX : Fin P.numRegs := ⟨k + 3, h_vX_lt⟩
  -- Instruction-presence lookups at PCs 14 and 15. The literal exitPC
  -- value at PC 14 inside `compileFrag_bprod` is `bprod_exitPC frag_f`.
  let exitPC_lit : ℕ :=
    16 + frag_f.numRegs + 9 * (k + 1) + (frag_f.instrs.size - 1) + 23
  have h_at_14 : P.instrs[(14 : ℕ)]?
      = some (URMInstr.jumpZ rVX exitPC_lit 15) := rfl
  have h_at_15 : P.instrs[(15 : ℕ)]? = some (URMInstr.dec rVX) := rfl
  -- Instruction-presence bundle for the zero-sweep block at PC 16.
  have h_sweep : ∀ r : Fin frag_f.numRegs,
      ∃ h : (k + 10) + r.val < P.numRegs,
        P.instrs[bprod_zeroSweepBase + r.val]?
          = some (URMInstr.assign ⟨(k + 10) + r.val, h⟩ 0) :=
    fun r => compileFrag_bprod_zeroSweep_instr_at frag_f r
  -- Pre-state hypotheses from the i.val-invariant.
  have h_s_pc : sPre.pc = bprod_topPC := h_inv.pc_eq
  have h_s_pc' : sPre.pc = 14 := h_s_pc
  have h_s_vX : sPre.regs rVX = v 0 - i.val := h_inv.vX_eq
  refine ⟨?_, ?_⟩
  · -- Phase i.0 post-state.
    -- Step 1 (PC 14): the jumpZ takes the non-zero branch, landing
    -- at PC 15 (= bodyStartPC).
    have h_vX_pos : sPre.regs rVX ≠ 0 := by
      rw [h_s_vX]
      have h_lt : i.val < v 0 := i.isLt
      omega
    have h_step0 :
        URMState.step P sPre =
          { pc := 15
            regs := sPre.regs } := by
      have h := URMState.step_of_getElem?_jumpZ P sPre 14 rVX
        exitPC_lit 15 h_s_pc' h_at_14
      rw [h]
      simp only [if_neg h_vX_pos]
    set s1 : URMState P :=
        { pc := 15
          regs := sPre.regs }
    have h_runFor_1 : URMState.runFor P sPre 1 = s1 := by
      change URMState.runFor P (URMState.step P sPre) 0 = _
      rw [URMState.runFor_zero, h_step0]
    have hs1_pc : s1.pc = 15 := rfl
    have hs1_vX : s1.regs rVX = v 0 - i.val := h_s_vX
    -- Step 2 (PC 15): decR vX.
    have h_step1 :
        URMState.step P s1 =
          { pc := 16
            regs := Function.update s1.regs rVX (s1.regs rVX - 1) } := by
      have h := URMState.step_of_getElem?_dec P s1 15 rVX hs1_pc h_at_15
      rw [h]
    set s2 : URMState P :=
        { pc := 16
          regs := Function.update s1.regs rVX (s1.regs rVX - 1) }
    have h_runFor_2 : URMState.runFor P sPre 2 = s2 := by
      have h_two : (2 : ℕ) = 1 + 1 := by omega
      rw [h_two, URMState.runFor_add, h_runFor_1]
      change URMState.runFor P (URMState.step P s1) 0 = _
      rw [URMState.runFor_zero, h_step1]
    -- s2 register values.
    have hs2_pc : s2.pc = bprod_zeroSweepBase := rfl
    have hs2_rVX : s2.regs rVX = v 0 - i.val - 1 := by
      change Function.update s1.regs rVX (s1.regs rVX - 1) rVX = _
      rw [Function.update_self, hs1_vX]
    have hs2_other_of_ne_rVX : ∀ r : Fin P.numRegs, r ≠ rVX →
        s2.regs r = sPre.regs r := by
      intro r h_ne
      change Function.update s1.regs rVX (s1.regs rVX - 1) r = _
      rw [Function.update_of_ne h_ne]
    -- Apply zero-sweep correctness.
    rw [URMState.runFor_add, h_runFor_2]
    obtain ⟨sw_pc, sw_zero, sw_other⟩ :=
      compileFrag_bprod_zeroSweep_correct frag_f h_sweep s2 hs2_pc
    set s3 : URMState P := URMState.runFor P s2 frag_f.numRegs
    have hs3_pc : s3.pc = bprod_zeroSweepBase + frag_f.numRegs := sw_pc
    have hs3_fBody : ∀ r : Fin frag_f.numRegs,
        ∀ h : (k + 10) + r.val < P.numRegs,
          s3.regs ⟨(k + 10) + r.val, h⟩ = 0 := sw_zero
    have hs3_other : ∀ q : Fin P.numRegs,
        (∀ r : Fin frag_f.numRegs, q.val ≠ (k + 10) + r.val) →
        s3.regs q = s2.regs q := sw_other
    have hs3_outside_block : ∀ q : Fin P.numRegs,
        q.val < k + 10 → s3.regs q = s2.regs q := by
      intro q hq
      apply hs3_other
      intro r heq
      have hr : r.val < frag_f.numRegs := r.isLt
      omega
    refine
      { hi_lt := i.isLt
        pc_eq := ?_
        zReg_zero := ?_
        outer_inputs := ?_
        vX_eq := ?_
        vI_eq := ?_
        tmp1_zero := ?_
        tmp2_zero := ?_
        accClone_zero := ?_
        factor_zero := ?_
        mulTmp_zero := ?_
        acc_eq := ?_
        fBody_zero := ?_ }
    · -- pc = bprod_prologueBase frag_f.
      change s3.pc = bprod_prologueBase frag_f
      rw [hs3_pc]
      rfl
    · -- zReg = 0.
      have h_outside : (⟨0, h_numRegs_pos⟩ : Fin P.numRegs).val < k + 10 := by
        change (0 : ℕ) < k + 10; omega
      rw [hs3_outside_block ⟨0, h_numRegs_pos⟩ h_outside]
      have h_ne_rVX : (⟨0, h_numRegs_pos⟩ : Fin P.numRegs) ≠ rVX := by
        intro h; have : (0 : ℕ) = k + 3 := congrArg Fin.val h; omega
      rw [hs2_other_of_ne_rVX _ h_ne_rVX]
      exact h_inv.zReg_zero
    · -- outer_inputs.
      intro j
      have hj : j.val < k + 1 := j.isLt
      have h_lt : 2 + j.val < P.numRegs := by
        rw [h_numRegs_eq]
        have : 0 < frag_f.numRegs := frag_f.numRegs_pos; omega
      have h_outside : (⟨2 + j.val, h_lt⟩ : Fin P.numRegs).val < k + 10 := by
        change 2 + j.val < k + 10; omega
      rw [hs3_outside_block ⟨2 + j.val, h_lt⟩ h_outside]
      have h_ne_rVX : (⟨2 + j.val, h_lt⟩ : Fin P.numRegs) ≠ rVX := by
        intro h; have : (2 + j.val : ℕ) = k + 3 := congrArg Fin.val h; omega
      rw [hs2_other_of_ne_rVX _ h_ne_rVX]
      exact h_inv.outer_inputs j
    · -- vX = v 0 - i.val - 1.
      have h_outside : rVX.val < k + 10 := by change k + 3 < k + 10; omega
      rw [hs3_outside_block rVX h_outside]
      exact hs2_rVX
    · -- vI = i.val.
      have h_vI_lt : k + 4 < P.numRegs := by
        rw [h_numRegs_eq]
        have : 0 < frag_f.numRegs := frag_f.numRegs_pos; omega
      have h_outside : (⟨k + 4, h_vI_lt⟩ : Fin P.numRegs).val < k + 10 := by
        change k + 4 < k + 10; omega
      rw [hs3_outside_block ⟨k + 4, h_vI_lt⟩ h_outside]
      have h_ne_rVX : (⟨k + 4, h_vI_lt⟩ : Fin P.numRegs) ≠ rVX := by
        intro h; have : (k + 4 : ℕ) = k + 3 := congrArg Fin.val h; omega
      rw [hs2_other_of_ne_rVX _ h_ne_rVX]
      exact h_inv.vI_eq
    · -- tmp1 = 0.
      have h_tmp1_lt : k + 5 < P.numRegs := by
        rw [h_numRegs_eq]
        have : 0 < frag_f.numRegs := frag_f.numRegs_pos; omega
      have h_outside : (⟨k + 5, h_tmp1_lt⟩ : Fin P.numRegs).val < k + 10 := by
        change k + 5 < k + 10; omega
      rw [hs3_outside_block ⟨k + 5, h_tmp1_lt⟩ h_outside]
      have h_ne_rVX : (⟨k + 5, h_tmp1_lt⟩ : Fin P.numRegs) ≠ rVX := by
        intro h; have : (k + 5 : ℕ) = k + 3 := congrArg Fin.val h; omega
      rw [hs2_other_of_ne_rVX _ h_ne_rVX]
      exact h_inv.tmp1_zero
    · -- tmp2 = 0.
      have h_tmp2_lt : k + 6 < P.numRegs := by
        rw [h_numRegs_eq]
        have : 0 < frag_f.numRegs := frag_f.numRegs_pos; omega
      have h_outside : (⟨k + 6, h_tmp2_lt⟩ : Fin P.numRegs).val < k + 10 := by
        change k + 6 < k + 10; omega
      rw [hs3_outside_block ⟨k + 6, h_tmp2_lt⟩ h_outside]
      have h_ne_rVX : (⟨k + 6, h_tmp2_lt⟩ : Fin P.numRegs) ≠ rVX := by
        intro h; have : (k + 6 : ℕ) = k + 3 := congrArg Fin.val h; omega
      rw [hs2_other_of_ne_rVX _ h_ne_rVX]
      exact h_inv.tmp2_zero
    · -- accClone = 0.
      have h_aC_lt : k + 7 < P.numRegs := by
        rw [h_numRegs_eq]
        have : 0 < frag_f.numRegs := frag_f.numRegs_pos; omega
      have h_outside : (⟨k + 7, h_aC_lt⟩ : Fin P.numRegs).val < k + 10 := by
        change k + 7 < k + 10; omega
      rw [hs3_outside_block ⟨k + 7, h_aC_lt⟩ h_outside]
      have h_ne_rVX : (⟨k + 7, h_aC_lt⟩ : Fin P.numRegs) ≠ rVX := by
        intro h; have : (k + 7 : ℕ) = k + 3 := congrArg Fin.val h; omega
      rw [hs2_other_of_ne_rVX _ h_ne_rVX]
      exact h_inv.accClone_zero
    · -- factor = 0.
      have h_f_lt : k + 8 < P.numRegs := by
        rw [h_numRegs_eq]
        have : 0 < frag_f.numRegs := frag_f.numRegs_pos; omega
      have h_outside : (⟨k + 8, h_f_lt⟩ : Fin P.numRegs).val < k + 10 := by
        change k + 8 < k + 10; omega
      rw [hs3_outside_block ⟨k + 8, h_f_lt⟩ h_outside]
      have h_ne_rVX : (⟨k + 8, h_f_lt⟩ : Fin P.numRegs) ≠ rVX := by
        intro h; have : (k + 8 : ℕ) = k + 3 := congrArg Fin.val h; omega
      rw [hs2_other_of_ne_rVX _ h_ne_rVX]
      exact h_inv.factor_zero
    · -- mulTmp = 0.
      have h_mT_lt : k + 9 < P.numRegs := by
        rw [h_numRegs_eq]
        have : 0 < frag_f.numRegs := frag_f.numRegs_pos; omega
      have h_outside : (⟨k + 9, h_mT_lt⟩ : Fin P.numRegs).val < k + 10 := by
        change k + 9 < k + 10; omega
      rw [hs3_outside_block ⟨k + 9, h_mT_lt⟩ h_outside]
      have h_ne_rVX : (⟨k + 9, h_mT_lt⟩ : Fin P.numRegs) ≠ rVX := by
        intro h; have : (k + 9 : ℕ) = k + 3 := congrArg Fin.val h; omega
      rw [hs2_other_of_ne_rVX _ h_ne_rVX]
      exact h_inv.mulTmp_zero
    · -- acc = natBProd i.val ...
      have h_acc_lt : 1 < P.numRegs := by
        rw [h_numRegs_eq]
        have : 0 < frag_f.numRegs := frag_f.numRegs_pos; omega
      have h_outside : (⟨1, h_acc_lt⟩ : Fin P.numRegs).val < k + 10 := by
        change (1 : ℕ) < k + 10; omega
      rw [hs3_outside_block ⟨1, h_acc_lt⟩ h_outside]
      have h_ne_rVX : (⟨1, h_acc_lt⟩ : Fin P.numRegs) ≠ rVX := by
        intro h; have : (1 : ℕ) = k + 3 := congrArg Fin.val h; omega
      rw [hs2_other_of_ne_rVX _ h_ne_rVX]
      exact h_inv.acc_eq
    · -- fBody_zero: every block register is 0.
      intro r
      have hr : r.val < frag_f.numRegs := r.isLt
      have h_idx_lt : (k + 10) + r.val < P.numRegs := by
        rw [h_numRegs_eq]; omega
      exact hs3_fBody r h_idx_lt
  · -- Strict PC bound: ∀ k' < 2 + numRegs_f, (runFor sPre k').pc
    -- < bprod_prologueBase frag_f.
    intro k' hk'
    -- Case split on k' ≤ 1 (PC 14 or 15) versus k' ≥ 2 (in the sweep).
    rcases Nat.lt_or_ge k' 2 with hlt | hge
    · -- k' ∈ {0, 1}: PC = 14 or 15.
      rcases Nat.lt_or_ge k' 1 with hlt1 | hge1
      · -- k' = 0: PC = sPre.pc = 14.
        have hk'_eq : k' = 0 := Nat.lt_one_iff.mp hlt1
        rw [hk'_eq, URMState.runFor_zero, h_s_pc']
        change (14 : ℕ) < bprod_prologueBase frag_f
        change (14 : ℕ) < 16 + frag_f.numRegs
        have : 0 < frag_f.numRegs := frag_f.numRegs_pos; omega
      · -- k' = 1: runFor sPre 1 has pc = 15.
        have hk'_eq : k' = 1 := by omega
        rw [hk'_eq]
        have h_vX_pos : sPre.regs rVX ≠ 0 := by
          rw [h_s_vX]
          have h_lt : i.val < v 0 := i.isLt
          omega
        have h_step0 :
            URMState.step P sPre =
              { pc := 15
                regs := sPre.regs } := by
          have h := URMState.step_of_getElem?_jumpZ P sPre 14 rVX
            exitPC_lit 15 h_s_pc' h_at_14
          rw [h]
          simp only [if_neg h_vX_pos]
        change (URMState.runFor P (URMState.step P sPre) 0).pc
          < bprod_prologueBase frag_f
        rw [URMState.runFor_zero, h_step0]
        change (15 : ℕ) < bprod_prologueBase frag_f
        change (15 : ℕ) < 16 + frag_f.numRegs
        have : 0 < frag_f.numRegs := frag_f.numRegs_pos; omega
    · -- k' ≥ 2: runFor sPre k' = runFor s2 (k' - 2), inside the
      -- zero-sweep; apply the strict PC bound for the zero-sweep.
      have hk'_eq : k' = 2 + (k' - 2) := by omega
      have h_k_minus_2_lt : k' - 2 < frag_f.numRegs := by omega
      have h_vX_pos : sPre.regs rVX ≠ 0 := by
        rw [h_s_vX]
        have h_lt : i.val < v 0 := i.isLt
        omega
      have h_step0 :
          URMState.step P sPre =
            { pc := 15
              regs := sPre.regs } := by
        have h := URMState.step_of_getElem?_jumpZ P sPre 14 rVX
          exitPC_lit 15 h_s_pc' h_at_14
        rw [h]
        simp only [if_neg h_vX_pos]
      set s1' : URMState P :=
          { pc := 15
            regs := sPre.regs }
      have h_runFor_1 : URMState.runFor P sPre 1 = s1' := by
        change URMState.runFor P (URMState.step P sPre) 0 = _
        rw [URMState.runFor_zero, h_step0]
      have hs1_pc : s1'.pc = 15 := rfl
      have h_step1 :
          URMState.step P s1' =
            { pc := 16
              regs := Function.update s1'.regs rVX (s1'.regs rVX - 1) } := by
        have h := URMState.step_of_getElem?_dec P s1' 15 rVX hs1_pc h_at_15
        rw [h]
      set s2' : URMState P :=
          { pc := 16
            regs := Function.update s1'.regs rVX (s1'.regs rVX - 1) }
      have h_runFor_2 : URMState.runFor P sPre 2 = s2' := by
        have h_two : (2 : ℕ) = 1 + 1 := by omega
        rw [h_two, URMState.runFor_add, h_runFor_1]
        change URMState.runFor P (URMState.step P s1') 0 = _
        rw [URMState.runFor_zero, h_step1]
      have hs2_pc : s2'.pc = bprod_zeroSweepBase := rfl
      rw [hk'_eq, URMState.runFor_add, h_runFor_2]
      have h_bound :=
        compileFrag_bprod_zeroSweep_pc_strict_bound frag_f h_sweep s2'
          hs2_pc (k' - 2) h_k_minus_2_lt
      change (URMState.runFor P s2' (k' - 2)).pc < bprod_prologueBase frag_f
      change (URMState.runFor P s2' (k' - 2)).pc < 16 + frag_f.numRegs
      exact h_bound

end LawvereERKSim
end GebLean
