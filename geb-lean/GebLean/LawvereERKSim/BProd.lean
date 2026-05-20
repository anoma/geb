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

end LawvereERKSim
end GebLean
