import GebLean.LawvereERKSim.Comp

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
- `compileFrag_bsum_zeroSweep_correct`,
  `compileFrag_bsum_zeroSweep_pc_strict_bound`: per-iteration
  zero-sweep correctness and per-step strict PC bound.
- `compileFrag_bsum_prologue_correct`,
  `compileFrag_bsum_prologue_pc_strict_bound`: bsum-flavoured aliases
  of the input-copies correctness and per-step strict PC bound lemmas
  from `Comp.lean` (the bsum per-iteration prologue is structurally
  identical to comp's input-copies phase).
- `compileFrag_bsum_accUpdate_correct`,
  `compileFrag_bsum_accUpdate_pc_strict_bound`: bsum-flavoured aliases
  of `transferLoop_correct` and `transferLoop_correct_pc_strict_bound`
  from `Loops.lean` (the bsum per-iteration accumulator-update block
  is a `transferLoop` from f's output register into the accumulator).
- `ProgramEmbedsFragment_compileFrag_bsum_fBody`: f-body embedding
  witness; at PCs `bsum_bodyPCBase frag_f ..
  bsum_bodyPCBase frag_f + (frag_f.instrs.size - 1)`, the outer
  program's instructions are the `reindexShift`-mapped raw form of
  `frag_f.instrs.pop`. Mirrors
  `ProgramEmbedsFragment_compileFrag_comp_gsBody` in `Comp.lean`,
  reflecting that the bsum f-body excludes `frag_f`'s trailing stop
  instruction (dropped via `.pop` when emitting the body).

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

/-- Per-iteration zero-sweep correctness for `compileFrag_bsum`: running
the URM for `numRegs_f` steps from a state at `pcBase` through a
contiguous block of `assignR (fBase + r) 0` instructions advances the
PC to `pcBase + numRegs_f`, writes `0` to every register
`⟨fBase + r, _⟩` in the swept range, and leaves all other registers
unchanged. The instruction-presence hypothesis `hSweep` packages the
in-range witness alongside the `getElem?` equation. -/
private theorem compileFrag_bsum_zeroSweep_correct
    {a : ℕ}
    (P : URMProgram a) (pcBase fBase : ℕ)
    (numRegs_f : ℕ)
    (hSweep : ∀ r : Fin numRegs_f,
      ∃ h : fBase + r.val < P.numRegs,
        P.instrs[pcBase + r.val]?
          = some (URMInstr.assign ⟨fBase + r.val, h⟩ 0))
    (s : URMState P) (h_pc : s.pc = pcBase) :
    let s' := URMState.runFor P s numRegs_f
    s'.pc = pcBase + numRegs_f ∧
    (∀ r : Fin numRegs_f,
      ∀ h : fBase + r.val < P.numRegs,
        s'.regs ⟨fBase + r.val, h⟩ = 0) ∧
    (∀ q : Fin P.numRegs,
      (∀ r : Fin numRegs_f, q.val ≠ fBase + r.val) →
      s'.regs q = s.regs q) := by
  simp only []
  induction numRegs_f with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · rw [URMState.runFor_zero, h_pc]; omega
    · intro r; exact r.elim0
    · intros _ _; rw [URMState.runFor_zero]
  | succ n ih =>
    -- IH for the first `n` registers (use the original `pcBase`).
    have hSweep_n : ∀ r : Fin n,
        ∃ h : fBase + r.val < P.numRegs,
          P.instrs[pcBase + r.val]?
            = some (URMInstr.assign ⟨fBase + r.val, h⟩ 0) := by
      intro r
      exact hSweep ⟨r.val, Nat.lt_succ_of_lt r.isLt⟩
    obtain ⟨ih_pc, ih_zero, ih_other⟩ := ih hSweep_n
    -- Peel one step at the end: runFor (n + 1) = step ∘ runFor n.
    rw [show n + 1 = n + 1 from rfl, URMState.runFor_add]
    set s1 : URMState P := URMState.runFor P s n with hs1_def
    have hs1_pc : s1.pc = pcBase + n := ih_pc
    -- Instruction at PC `pcBase + n` is `assign ⟨fBase + n, _⟩ 0`.
    obtain ⟨h_lt, h_instr⟩ := hSweep ⟨n, Nat.lt_succ_self n⟩
    -- One assign step transition.
    have h_step :
        URMState.step P s1 =
          { pc := s1.pc + 1
            regs := Function.update s1.regs ⟨fBase + n, h_lt⟩ 0 } :=
      URMState.step_of_getElem?_assign P s1 (pcBase + n)
        ⟨fBase + n, h_lt⟩ 0 hs1_pc h_instr
    -- Compute s2 := runFor P s1 1.
    have hs2_eq :
        URMState.runFor P s1 1
          = { pc := s1.pc + 1
              regs := Function.update s1.regs ⟨fBase + n, h_lt⟩ 0 } := by
      rw [show (1 : ℕ) = 0 + 1 from rfl, URMState.runFor_succ,
        URMState.runFor_zero, h_step]
    rw [hs2_eq]
    refine ⟨?_, ?_, ?_⟩
    · -- pc = pcBase + (n + 1).
      change s1.pc + 1 = pcBase + (n + 1)
      rw [hs1_pc]; omega
    · -- All swept registers are zero.
      intro r h
      by_cases hr : r.val = n
      · -- Last register: just written by the peeled step.
        have hreg_eq : (⟨fBase + r.val, h⟩ : Fin P.numRegs)
            = ⟨fBase + n, h_lt⟩ := by
          apply Fin.ext
          change fBase + r.val = fBase + n
          omega
        rw [hreg_eq]
        change Function.update s1.regs ⟨fBase + n, h_lt⟩ 0
          ⟨fBase + n, h_lt⟩ = 0
        rw [Function.update_self]
      · -- Earlier registers: r.val < n, unaffected by the peeled step.
        have hr_lt : r.val < n := by
          have hr_succ : r.val < n + 1 := r.isLt
          omega
        have hne : (⟨fBase + r.val, h⟩ : Fin P.numRegs)
            ≠ ⟨fBase + n, h_lt⟩ := by
          intro heq
          have : fBase + r.val = fBase + n := congrArg Fin.val heq
          omega
        change Function.update s1.regs ⟨fBase + n, h_lt⟩ 0
          ⟨fBase + r.val, h⟩ = 0
        rw [Function.update_of_ne hne]
        exact ih_zero ⟨r.val, hr_lt⟩ h
    · -- Other registers preserved.
      intro q h_ne
      have hne_last : q ≠ ⟨fBase + n, h_lt⟩ := by
        intro heq
        have hval : q.val = fBase + n := congrArg Fin.val heq
        have h_ne_n : q.val ≠ fBase + (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)).val :=
          h_ne ⟨n, Nat.lt_succ_self n⟩
        change q.val ≠ fBase + n at h_ne_n
        exact h_ne_n hval
      change Function.update s1.regs ⟨fBase + n, h_lt⟩ 0 q = s.regs q
      rw [Function.update_of_ne hne_last]
      apply ih_other
      intro r
      exact h_ne ⟨r.val, Nat.lt_succ_of_lt r.isLt⟩

/-- Per-step strict PC bound for `compileFrag_bsum_zeroSweep_correct`:
during the `numRegs_f` zero-sweep steps, the intermediate PC stays
strictly less than `pcBase + numRegs_f`. -/
private theorem compileFrag_bsum_zeroSweep_pc_strict_bound
    {a : ℕ} (P : URMProgram a) (pcBase fBase : ℕ)
    (numRegs_f : ℕ)
    (hSweep : ∀ r : Fin numRegs_f,
      ∃ h : fBase + r.val < P.numRegs,
        P.instrs[pcBase + r.val]?
          = some (URMInstr.assign ⟨fBase + r.val, h⟩ 0))
    (s : URMState P) (h_pc : s.pc = pcBase)
    (k' : ℕ) (h_k' : k' < numRegs_f) :
    (URMState.runFor P s k').pc < pcBase + numRegs_f := by
  -- Strengthened invariant: after k' < numRegs_f steps the PC is exactly
  -- pcBase + k', so it is strictly less than pcBase + numRegs_f.
  suffices h_pc_eq : (URMState.runFor P s k').pc = pcBase + k' by
    rw [h_pc_eq]; omega
  -- Restrict `hSweep` to the first `k'` registers.
  have hSweep_k : ∀ r : Fin k',
      ∃ h : fBase + r.val < P.numRegs,
        P.instrs[pcBase + r.val]?
          = some (URMInstr.assign ⟨fBase + r.val, h⟩ 0) := by
    intro r
    exact hSweep ⟨r.val, Nat.lt_trans r.isLt h_k'⟩
  obtain ⟨pc_eq, _, _⟩ :=
    compileFrag_bsum_zeroSweep_correct P pcBase fBase k' hSweep_k s h_pc
  exact pc_eq

/-- Per-iteration prologue correctness for `compileFrag_bsum`:
running the URM through `a` consecutive `preservingTransfer` blocks
copies the outer source registers `srcs` into the destination
registers `dsts`, advances the PC to `pcBase + 9 * a`, and preserves
`tmp`, `zReg`, the source registers, and all other registers outside
the destination block. Bsum-flavoured alias of
`compileFrag_comp_subBlock_inputCopies_correct`. -/
private theorem compileFrag_bsum_prologue_correct
    {a : ℕ}
    (P : URMProgram a) (pcBase : ℕ)
    (zReg tmp : Fin P.numRegs)
    (srcs dsts : Fin a → Fin P.numRegs)
    (h_disj : inputCopies_disj P zReg tmp srcs dsts)
    (H : ∀ j : Fin a,
      preservingTransferInstrs P (pcBase + 9 * j.val)
        (srcs j) (dsts j) tmp zReg)
    (v : Fin a → ℕ)
    (s : URMState P) (h_pc : s.pc = pcBase)
    (h_z : s.regs zReg = 0) (h_tmp0 : s.regs tmp = 0)
    (h_srcs : ∀ j : Fin a, s.regs (srcs j) = v j)
    (h_dsts0 : ∀ j : Fin a, s.regs (dsts j) = 0) :
    let totalSteps : ℕ := 9 * vPrefixSum v a + 2 * a
    let s' := URMState.runFor P s totalSteps
    s'.pc = pcBase + 9 * a ∧
    s'.regs zReg = 0 ∧
    s'.regs tmp = 0 ∧
    (∀ j : Fin a, s'.regs (dsts j) = v j) ∧
    (∀ j : Fin a, s'.regs (srcs j) = v j) ∧
    (∀ r : Fin P.numRegs,
        (∀ j : Fin a, r ≠ dsts j) → r ≠ tmp →
        s'.regs r = s.regs r) :=
  compileFrag_comp_subBlock_inputCopies_correct
    P pcBase zReg tmp srcs dsts h_disj H v s h_pc h_z h_tmp0
    h_srcs h_dsts0

/-- Per-step strict PC bound for `compileFrag_bsum_prologue_correct`:
during the `9 * vPrefixSum v a + 2 * a` prologue steps, the
intermediate PC stays strictly less than `pcBase + 9 * a`.
Bsum-flavoured alias of
`compileFrag_comp_subBlock_inputCopies_pc_strict_bound`. -/
private theorem compileFrag_bsum_prologue_pc_strict_bound
    {a : ℕ}
    (P : URMProgram a) (pcBase : ℕ)
    (zReg tmp : Fin P.numRegs)
    (srcs dsts : Fin a → Fin P.numRegs)
    (h_disj : inputCopies_disj P zReg tmp srcs dsts)
    (H : ∀ j : Fin a,
      preservingTransferInstrs P (pcBase + 9 * j.val)
        (srcs j) (dsts j) tmp zReg)
    (v : Fin a → ℕ)
    (s : URMState P) (h_pc : s.pc = pcBase)
    (h_z : s.regs zReg = 0) (h_tmp0 : s.regs tmp = 0)
    (h_srcs : ∀ j : Fin a, s.regs (srcs j) = v j)
    (h_dsts0 : ∀ j : Fin a, s.regs (dsts j) = 0)
    (k : ℕ) (h_k : k < 9 * vPrefixSum v a + 2 * a) :
    (URMState.runFor P s k).pc < pcBase + 9 * a :=
  compileFrag_comp_subBlock_inputCopies_pc_strict_bound
    P pcBase zReg tmp srcs dsts h_disj H v s h_pc h_z h_tmp0
    h_srcs h_dsts0 k h_k

/-- Per-iteration accumulator-update correctness for `compileFrag_bsum`:
running the URM through the 4-instruction `transferLoop` block at
`pcBase` destructively transfers `vSrc` units from `src` (f's output
register) into `dst` (the accumulator), advances the PC to `pcBase + 4`,
zeros `src`, leaves the reserved zero register `zReg` at `0`, and
preserves every other register. Bsum-flavoured alias of
`transferLoop_correct`. -/
private theorem compileFrag_bsum_accUpdate_correct
    {a : ℕ}
    (P : URMProgram a) (pcBase : ℕ)
    (src dst zReg : Fin P.numRegs)
    (h_disj_sd : src ≠ dst) (h_disj_zs : zReg ≠ src)
    (h_disj_zd : zReg ≠ dst)
    (H : transferLoopInstrs P pcBase src dst zReg)
    (vSrc : ℕ)
    (s : URMState P) (h_pc : s.pc = pcBase)
    (h_z : s.regs zReg = 0)
    (h_src : s.regs src = vSrc) :
    let s' := URMState.runFor P s (4 * vSrc + 1)
    s'.pc = pcBase + 4 ∧
    s'.regs dst = s.regs dst + vSrc ∧
    s'.regs src = 0 ∧
    s'.regs zReg = 0 ∧
    ∀ r, r ≠ dst → r ≠ src → r ≠ zReg →
      s'.regs r = s.regs r :=
  transferLoop_correct P pcBase src dst zReg h_disj_sd h_disj_zs
    h_disj_zd H s h_pc h_z vSrc h_src

/-- Per-step strict PC bound for `compileFrag_bsum_accUpdate_correct`:
during the `4 * vSrc` steps strictly before the final exit step, the
intermediate PC is at most `pcBase + 3`. Bsum-flavoured alias of
`transferLoop_correct_pc_strict_bound`. -/
private theorem compileFrag_bsum_accUpdate_pc_strict_bound
    {a : ℕ}
    (P : URMProgram a) (pcBase : ℕ)
    (src dst zReg : Fin P.numRegs)
    (h_disj_sd : src ≠ dst) (h_disj_zs : zReg ≠ src)
    (h_disj_zd : zReg ≠ dst)
    (H : transferLoopInstrs P pcBase src dst zReg)
    (vSrc : ℕ)
    (s : URMState P) (h_pc : s.pc = pcBase)
    (h_z : s.regs zReg = 0)
    (h_src : s.regs src = vSrc)
    (k : ℕ) (h_k : k ≤ 4 * vSrc) :
    (URMState.runFor P s k).pc ≤ pcBase + 3 :=
  transferLoop_correct_pc_strict_bound P pcBase src dst zReg
    h_disj_sd h_disj_zs h_disj_zd H s h_pc h_z vSrc h_src k h_k

/-- For `compileFrag_bsum`'s f-body embedding: at PCs
`bsum_bodyPCBase frag_f .. bsum_bodyPCBase frag_f
+ (frag_f.instrs.size - 1)`, the outer program's instructions are
the `reindexShift`-mapped raw form of `frag_f.instrs.pop`. The
values of `fBase = k + 7` and `bsum_bodyPCBase frag_f
= 15 + frag_f.numRegs + 9 * (k + 1)` are those used by the
constructor of `compileFrag_bsum`; the embedded length excludes
`frag_f`'s trailing stop instruction (dropped via `.pop` when
emitting the f-body). -/
private theorem ProgramEmbedsFragment_compileFrag_bsum_fBody
    {k : ℕ}
    (frag_f : CompiledFragment (k + 1)) :
    ProgramEmbedsFragment
      (compileFrag_bsum frag_f).toURMProgram
      frag_f
      (k + 7)
      (15 + frag_f.numRegs + 9 * (k + 1))
      (frag_f.instrs.size - 1) := by
  -- Abbreviations matching the constructor of compileFrag_bsum.
  let vAcc : ℕ := 1
  let vBoundIn : ℕ := 2
  let vX : ℕ := k + 3
  let vI : ℕ := k + 4
  let tmp1 : ℕ := k + 5
  let tmp2 : ℕ := k + 6
  let fBase : ℕ := k + 7
  let nR : ℕ := fBase + frag_f.numRegs
  let topPC : ℕ := 13
  let bodyStartPC : ℕ := 14
  let prologueBase : ℕ := 15 + frag_f.numRegs
  let bodyPCBase : ℕ := 15 + frag_f.numRegs + 9 * (k + 1)
  let fBodyLen : ℕ := frag_f.instrs.size - 1
  let trBase : ℕ := bodyPCBase + fBodyLen
  let exitPC : ℕ := trBase + 6
  let prelude : List URMInstrRaw :=
    [ .assignR 0 0,
      .assignR vAcc 0,
      .assignR vX 0,
      .assignR vI 0 ]
        ++ URMRaw.preservingTransfer 4 vBoundIn vX tmp2
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
    URMRaw.transferLoop trBase
      (fBase + frag_f.outputReg.val) vAcc
  let epilogue : List URMInstrRaw :=
    [ .incR vI, URMRaw.goto topPC, .stopR ]
  let rawList : List URMInstrRaw :=
    prelude ++ loopTop ++ zeroSweep ++ prologue ++ fBody
      ++ accUpdate ++ epilogue
  -- Segment lengths.
  have h_prelude_len : prelude.length = 13 := by
    change ([URMInstrRaw.assignR 0 0, URMInstrRaw.assignR vAcc 0,
        URMInstrRaw.assignR vX 0, URMInstrRaw.assignR vI 0]
        ++ URMRaw.preservingTransfer 4 vBoundIn vX tmp2).length = 13
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
  have h_accUpdate_len : accUpdate.length = 4 := by
    simp only [accUpdate, URMRaw.transferLoop, URMRaw.goto,
      List.length_cons, List.length_nil]
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
  let outer : URMProgram (k + 1) := (compileFrag_bsum frag_f).toURMProgram
  have hReg : fBase + frag_f.numRegs ≤ outer.numRegs := by
    change fBase + frag_f.numRegs ≤ nR
    change fBase + frag_f.numRegs ≤ fBase + frag_f.numRegs
    omega
  have hL : frag_f.instrs.size - 1 ≤ frag_f.instrs.size := Nat.sub_le _ _
  refine ⟨hL, hReg, ?_⟩
  intro i hi
  have hi' : i < frag_f.instrs.size :=
    Nat.lt_of_lt_of_le hi hL
  -- The boundedness witness used by compileFrag_bsum.
  -- We extract it via outer.instrs = toBoundedArray nR rawList hBound;
  -- since the let-bindings are definitional, both sides are the same
  -- array up to proof-irrelevance of the boundedness witness.
  have hBoundOuter : URMInstrRaw.boundedBy nR rawList := by
    -- We need a boundedness witness for our locally-named rawList.
    -- It exists by the same construction as inside compileFrag_bsum.
    -- Reconstruct via the per-segment boundedness facts.
    have hAcc : vAcc + 1 ≤ nR := by
      change vAcc + 1 ≤ fBase + frag_f.numRegs
      have : 0 < frag_f.numRegs := frag_f.numRegs_pos
      change 1 + 1 ≤ k + 7 + frag_f.numRegs
      omega
    have hBoundIn : vBoundIn + 1 ≤ nR := by
      change 2 + 1 ≤ k + 7 + frag_f.numRegs
      have : 0 < frag_f.numRegs := frag_f.numRegs_pos
      omega
    have hVX : vX + 1 ≤ nR := by
      change k + 3 + 1 ≤ k + 7 + frag_f.numRegs
      have : 0 < frag_f.numRegs := frag_f.numRegs_pos
      omega
    have hVI : vI + 1 ≤ nR := by
      change k + 4 + 1 ≤ k + 7 + frag_f.numRegs
      have : 0 < frag_f.numRegs := frag_f.numRegs_pos
      omega
    have hTmp1 : tmp1 + 1 ≤ nR := by
      change k + 5 + 1 ≤ k + 7 + frag_f.numRegs
      have : 0 < frag_f.numRegs := frag_f.numRegs_pos
      omega
    have hTmp2 : tmp2 + 1 ≤ nR := by
      change k + 6 + 1 ≤ k + 7 + frag_f.numRegs
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
      rcases hmem with (h | h | h | h) | hpT
      · rw [h]; simp only [URMInstrRaw.regBound]; omega
      · rw [h]; simp only [URMInstrRaw.regBound]; exact hAcc
      · rw [h]; simp only [URMInstrRaw.regBound]; exact hVX
      · rw [h]; simp only [URMInstrRaw.regBound]; exact hVI
      · exact boundedBy_preservingTransfer nR _ _ _ _
          hBoundIn hVX hTmp2 ins hpT
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
    have hAccUpdateBound : URMInstrRaw.boundedBy nR accUpdate :=
      boundedBy_transferLoop nR _ _ _ hFOut hAcc
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
  -- outer.instrs is definitionally toBoundedArray nR rawList hBoundOuter.
  -- Index of bodyPCBase + i in rawList.
  have h_idx_lt : bodyPCBase + i < rawList.length := by
    rw [h_raw_len, h_prelude_len, h_loopTop_len, h_zeroSweep_len,
      h_prologue_len, h_fBody_len, h_accUpdate_len, h_epilogue_len]
    change 15 + frag_f.numRegs + 9 * (k + 1) + i
      < 13 + 2 + frag_f.numRegs + 9 * (k + 1)
        + (frag_f.instrs.size - 1) + 4 + 3
    omega
  -- Reduce outer.instrs[bodyPCBase + i]? to toBoundedArray's lookup.
  change (URMInstrRaw.toBoundedArray nR rawList hBoundOuter)[
      bodyPCBase + i]?
    = some (URMInstrRaw.toBounded nR
        (URMInstrRaw.reindexShift fBase bodyPCBase
          (toRawOfBounded (frag_f.instrs[i]'hi'))) _)
  rw [URMInstrRaw.toBoundedArray_getElem? nR rawList hBoundOuter
      (bodyPCBase + i) h_idx_lt]
  -- Establish the raw equality:
  --   rawList[bodyPCBase + i] = reindexShift fBase bodyPCBase
  --     (toRawOfBounded frag_f.instrs[i]).
  have h_raw_eq :
      rawList[bodyPCBase + i]'h_idx_lt
        = URMInstrRaw.reindexShift fBase bodyPCBase
          (toRawOfBounded (frag_f.instrs[i]'hi')) := by
    -- Step 1: rewrite the index in the form
    --   (prelude.length + loopTop.length + zeroSweep.length
    --     + prologue.length) + i, so the segment skip is via
    --   `getElem_append_right` four times.
    -- rawList = ((((((prelude ++ loopTop) ++ zeroSweep) ++ prologue)
    --   ++ fBody) ++ accUpdate) ++ epilogue).
    -- For the first append peel:
    --   prefix length = prelude.length + loopTop.length
    --     + zeroSweep.length + prologue.length + fBody.length
    --     + accUpdate.length;
    --   our index bodyPCBase + i < that prefix length.
    have h_in_prefix6 :
        bodyPCBase + i
          < ((((((prelude ++ loopTop) ++ zeroSweep) ++ prologue)
              ++ fBody) ++ accUpdate)).length := by
      simp only [List.length_append]
      rw [h_prelude_len, h_loopTop_len, h_zeroSweep_len,
        h_prologue_len, h_fBody_len, h_accUpdate_len]
      change 15 + frag_f.numRegs + 9 * (k + 1) + i
        < 13 + 2 + frag_f.numRegs + 9 * (k + 1)
          + (frag_f.instrs.size - 1) + 4
      omega
    have h_in_prefix5 :
        bodyPCBase + i
          < (((((prelude ++ loopTop) ++ zeroSweep) ++ prologue)
              ++ fBody)).length := by
      simp only [List.length_append]
      rw [h_prelude_len, h_loopTop_len, h_zeroSweep_len,
        h_prologue_len, h_fBody_len]
      change 15 + frag_f.numRegs + 9 * (k + 1) + i
        < 13 + 2 + frag_f.numRegs + 9 * (k + 1)
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
      change 13 + 2 + frag_f.numRegs + 9 * (k + 1)
        ≤ 15 + frag_f.numRegs + 9 * (k + 1) + i
      omega
    -- The "prefix4" is prelude++loopTop++zeroSweep++prologue;
    -- its length equals bodyPCBase via h_offset_eq, so the index
    -- inside fBody simplifies to i.
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
    -- The original h_in_prefix5 indexes prelude++loopTop++zeroSweep
    -- ++prologue++fBody; that's prefix4 ++ fBody.
    have h_step3' :
        (((((prelude ++ loopTop) ++ zeroSweep) ++ prologue)
              ++ fBody))[bodyPCBase + i]'h_in_prefix5
          = fBody[bodyPCBase + i - prefix4.length]'h_idx_in_fBody := by
      exact h_step3
    rw [h_step3']
    -- Simplify the index inside fBody to i.
    have h_idx_eq : bodyPCBase + i - prefix4.length = i := by
      rw [h_prefix4_len]; omega
    have h_i_lt_fBody : i < fBody.length := by
      rw [h_fBody_len]; exact hi
    have h_step4 :
        fBody[bodyPCBase + i - prefix4.length]'h_idx_in_fBody
          = fBody[i]'h_i_lt_fBody := by
      congr 1
    rw [h_step4]
    -- fBody[i] = (frag_f.instrs.pop.toList.map _)[i]
    --         = reindexShift fBase bodyPCBase
    --             (toRawOfBounded frag_f.instrs.pop.toList[i]).
    change (frag_f.instrs.pop.toList.map (fun ins =>
        URMInstrRaw.reindexShift fBase bodyPCBase
          (toRawOfBounded ins)))[i]'_
      = _
    rw [List.getElem_map]
    -- Reduce frag_f.instrs.pop.toList[i] to frag_f.instrs[i] via
    --   pop.toList = dropLast, then dropLast[i] = toList[i] for
    --   i < size - 1, then toList[i] = instrs[i].
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

/-- Partial-iteration invariant for `compileFrag_bsum`. Describes
the state at the top of the outer loop (PC = 13) after `i` complete
iterations (with `i ≤ v 0`). Mirrors `compileFrag_comp_partial_invariant`
in `Comp.lean`, adapted to bsum's register layout
(`V_z = ⟨0, _⟩`, `V_acc = ⟨1, _⟩`, outer inputs at slots
`2..k+2`, `V_x = ⟨k+3, _⟩`, `V_i = ⟨k+4, _⟩`, scratch
`tmp1 = ⟨k+5, _⟩`, `tmp2 = ⟨k+6, _⟩`, f's reindexed register
block at slots `k+7 .. k+7 + frag_f.numRegs - 1`). The structure
carries the running value of `i` and proofs about every register
class. -/
private structure compileFrag_bsum_partial_invariant
    {k : ℕ}
    (frag_f : CompiledFragment (k + 1))
    (f : ERMor1 (k + 1))
    (v : Fin (k + 1) → ℕ)
    (i : ℕ) (hi : i ≤ v 0)
    (s : URMState (compileFrag_bsum frag_f).toURMProgram)
    : Prop where
  /-- `i ≤ v 0`, packaged for downstream consumers. -/
  hi_le : i ≤ v 0 := hi
  /-- PC sits at the loop-top instruction (absolute PC 13). -/
  pc_eq : s.pc = 13
  /-- `V_z` (register 0) holds `0`. -/
  zReg_zero : s.regs ⟨0, (compileFrag_bsum frag_f).numRegs_pos⟩ = 0
  /-- Outer input slots `2..k+2` hold the input vector. -/
  outer_inputs : ∀ (j : Fin (k + 1)),
    s.regs ⟨2 + j.val, by
      have hj : j.val < k + 1 := j.isLt
      change 2 + j.val < k + 7 + frag_f.numRegs
      have : 0 < frag_f.numRegs := frag_f.numRegs_pos
      omega⟩ = v j
  /-- `V_x` (register `k + 3`) holds `v 0 - i`, the remaining
  iteration count. -/
  vX_eq : s.regs ⟨k + 3, by
    change k + 3 < k + 7 + frag_f.numRegs
    have : 0 < frag_f.numRegs := frag_f.numRegs_pos
    omega⟩ = v 0 - i
  /-- `V_i` (register `k + 4`) holds the iteration counter `i`. -/
  vI_eq : s.regs ⟨k + 4, by
    change k + 4 < k + 7 + frag_f.numRegs
    have : 0 < frag_f.numRegs := frag_f.numRegs_pos
    omega⟩ = i
  /-- Scratch register `tmp1` (register `k + 5`) is `0`. -/
  tmp1_zero : s.regs ⟨k + 5, by
    change k + 5 < k + 7 + frag_f.numRegs
    have : 0 < frag_f.numRegs := frag_f.numRegs_pos
    omega⟩ = 0
  /-- Scratch register `tmp2` (register `k + 6`) is `0`. -/
  tmp2_zero : s.regs ⟨k + 6, by
    change k + 6 < k + 7 + frag_f.numRegs
    have : 0 < frag_f.numRegs := frag_f.numRegs_pos
    omega⟩ = 0
  /-- The accumulator (register 1) holds the partial sum
  `Σ_{j < i} f.interp (j :: tail v)`. -/
  acc_eq : s.regs ⟨1, by
    change 1 < k + 7 + frag_f.numRegs
    have : 0 < frag_f.numRegs := frag_f.numRegs_pos
    omega⟩
      = natBSum i (fun j => f.interp (Fin.cons j (Fin.tail v)))
  /-- f's reindexed register block (outer registers
  `k + 7 .. k + 7 + frag_f.numRegs - 1`) is uniformly `0`. -/
  fBody_zero : ∀ r : Fin frag_f.numRegs,
    s.regs ⟨(k + 7) + r.val, by
      have hr : r.val < frag_f.numRegs := r.isLt
      change (k + 7) + r.val < k + 7 + frag_f.numRegs
      omega⟩ = 0

/-- Base case of the bsum outer-iteration induction: after running
the prelude of `compileFrag_bsum`
(`assignR 0 0; assignR vAcc 0; assignR vX 0; assignR vI 0;`
`preservingTransfer 4 vBoundIn vX tmp2`) for `6 + 9 * (v 0)` URM
steps from `URMState.init outer v`, the partial invariant holds
at `i = 0`. The four `assignR` instructions occupy PCs `0..3`,
each consuming one URM step; the `preservingTransfer` block at
PC 4 consumes `9 * (v 0) + 2` further steps, leaving the PC at
`13 = 4 + 9` (the loop-top instruction) with `V_x = v 0 - 0`,
`V_i = 0`, accumulator `0`, scratches `0`, outer inputs
preserved, and f's reindexed block untouched at `0`. -/
private theorem compileFrag_bsum_partial_base
    {k : ℕ}
    (f : ERMor1 (k + 1))
    (v : Fin (k + 1) → ℕ) :
    let outer := (compileFrag_bsum (compileERFrag f)).toURMProgram
    let s_init := URMState.init outer v
    compileFrag_bsum_partial_invariant (compileERFrag f) f v 0
      (Nat.zero_le _)
      (URMState.runFor outer s_init (6 + 9 * (v 0))) := by
  intro outer s_init
  -- Abbreviations.
  set frag_f : CompiledFragment (k + 1) := compileERFrag f
  set outerFrag : CompiledFragment (k + 1) :=
    compileFrag_bsum frag_f
  set P : URMProgram (k + 1) := outerFrag.toURMProgram
  set s0 : URMState P := URMState.init P v
  -- Outer numRegs equals `(k + 7) + frag_f.numRegs`.
  have h_numRegs_eq : P.numRegs = (k + 7) + frag_f.numRegs := rfl
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
  have h_tmp2_lt : k + 6 < P.numRegs := by
    rw [h_numRegs_eq]
    have : 0 < frag_f.numRegs := frag_f.numRegs_pos; omega
  -- Fin-wrapped register handles.
  set rZ : Fin P.numRegs := ⟨0, h_z_lt⟩
  set rAcc : Fin P.numRegs := ⟨1, h_acc_lt⟩
  set rBoundIn : Fin P.numRegs := ⟨2, h_bIn_lt⟩
  set rVX : Fin P.numRegs := ⟨k + 3, h_vX_lt⟩
  set rVI : Fin P.numRegs := ⟨k + 4, h_vI_lt⟩
  set rTmp2 : Fin P.numRegs := ⟨k + 6, h_tmp2_lt⟩
  -- Outer's `inputRegs` maps slot `j` to outer register `2 + j.val`.
  have h_outer_inputRegs : ∀ (j : Fin (k + 1)),
      (P.inputRegs j).val = 2 + j.val := fun _ => rfl
  -- Prelude instruction lookups at PCs 0..3 (each `assignR`).
  have h_outer_at_0 : P.instrs[(0 : ℕ)]? = some (URMInstr.assign rZ 0) := rfl
  have h_outer_at_1 : P.instrs[(1 : ℕ)]? = some (URMInstr.assign rAcc 0) := rfl
  have h_outer_at_2 : P.instrs[(2 : ℕ)]? = some (URMInstr.assign rVX 0) := rfl
  have h_outer_at_3 : P.instrs[(3 : ℕ)]? = some (URMInstr.assign rVI 0) := rfl
  -- preservingTransferInstrs at PC 4 with src=vBoundIn, dst=vX, tmp=tmp2,
  -- zReg=⟨0, _⟩.
  have H_pT : preservingTransferInstrs P 4 rBoundIn rVX rTmp2 rZ := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rfl
  -- Disjointness of the four register handles.
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
    -- runFor P s1 1 = s2.
    have h_runFor_s1_1 : URMState.runFor P s1 1 = s2 := by
      change URMState.runFor P (URMState.step P s1) 0 = _
      rw [URMState.runFor_zero, h_step1]
    rw [h_runFor_s1_1]
    -- runFor P s2 1 = s3.
    have h_runFor_s2_1 : URMState.runFor P s2 1 = s3 := by
      change URMState.runFor P (URMState.step P s2) 0 = _
      rw [URMState.runFor_zero, h_step2]
    rw [h_runFor_s2_1]
    -- runFor P s3 1 = s4.
    change URMState.runFor P (URMState.step P s3) 0 = _
    rw [URMState.runFor_zero, h_step3]
  -- s4 register values.
  have hs4_pc : s4.pc = 4 := rfl
  -- The four updated registers are pairwise distinct (rZ, rAcc, rVX, rVI).
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
  -- s4 at vBoundIn = v 0 (since vBoundIn is outer input 0, and rZ/rAcc/rVX/rVI
  -- are not equal to rBoundIn).
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
    -- s0.regs rTmp2 = 0 (init outside inputs).
    change (URMState.init P v).regs rTmp2 = 0
    apply URMState.init_regs_zero_outside_inputs P v h_outer_inputRegs
    right; right
    change 2 + (k + 1) ≤ k + 6; omega
  -- Now apply preservingTransfer_correct at pcBase = 4.
  rw [show 6 + 9 * (v 0) = 4 + (9 * (v 0) + 2) by omega, URMState.runFor_add,
    h_runFor_4]
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
  -- Other registers (those ≠ rVX) preserved from s4.
  have hs5_other_of_ne_rVX : ∀ r : Fin P.numRegs, r ≠ rVX →
      s5.regs r = s4.regs r := pt_oth
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
      acc_eq := ?_
      fBody_zero := ?_ }
  · -- PC = 13.
    exact hs5_pc
  · -- V_z = 0.
    exact hs5_rZ
  · -- Outer inputs preserved: s5.regs ⟨2 + j.val, _⟩ = v j.
    intro j
    -- ⟨2 + j.val, _⟩ ≠ rVX since 2 + j.val ≤ k + 2 < k + 3.
    have hj : j.val < k + 1 := j.isLt
    have h_ne_rVX :
        (⟨2 + j.val, by
          change 2 + j.val < k + 7 + frag_f.numRegs
          have : 0 < frag_f.numRegs := frag_f.numRegs_pos; omega⟩ :
          Fin P.numRegs) ≠ rVX := by
      intro h
      have : (2 + j.val : ℕ) = k + 3 := congrArg Fin.val h
      omega
    rw [hs5_other_of_ne_rVX _ h_ne_rVX]
    -- And s4.regs ⟨2 + j.val, _⟩ = s0.regs ⟨2 + j.val, _⟩ since
    -- 2 + j.val ∉ {0, 1, k+3, k+4}.
    have h_ne_rZ :
        (⟨2 + j.val, by
          change 2 + j.val < k + 7 + frag_f.numRegs
          have : 0 < frag_f.numRegs := frag_f.numRegs_pos; omega⟩ :
          Fin P.numRegs) ≠ rZ := by
      intro h; have : (2 + j.val : ℕ) = 0 := congrArg Fin.val h; omega
    have h_ne_rAcc :
        (⟨2 + j.val, by
          change 2 + j.val < k + 7 + frag_f.numRegs
          have : 0 < frag_f.numRegs := frag_f.numRegs_pos; omega⟩ :
          Fin P.numRegs) ≠ rAcc := by
      intro h; have : (2 + j.val : ℕ) = 1 := congrArg Fin.val h; omega
    have h_ne_rVI :
        (⟨2 + j.val, by
          change 2 + j.val < k + 7 + frag_f.numRegs
          have : 0 < frag_f.numRegs := frag_f.numRegs_pos; omega⟩ :
          Fin P.numRegs) ≠ rVI := by
      intro h; have : (2 + j.val : ℕ) = k + 4 := congrArg Fin.val h; omega
    rw [hs4_other _ h_ne_rZ h_ne_rAcc h_ne_rVX h_ne_rVI]
    -- s0.regs ⟨2 + j.val, _⟩ = v j via P.inputRegs j.
    have h_eq : (P.inputRegs j : Fin P.numRegs)
        = ⟨2 + j.val, by
          change 2 + j.val < k + 7 + frag_f.numRegs
          have : 0 < frag_f.numRegs := frag_f.numRegs_pos; omega⟩ := by
      apply Fin.ext; exact h_outer_inputRegs j
    change s0.regs _ = v j
    rw [← h_eq]
    exact URMState.init_regs_inputRegs P v j
  · -- V_x = v 0 - 0 = v 0.
    change s5.regs rVX = v 0 - 0
    rw [hs5_rVX]; omega
  · -- V_i = 0.
    change s5.regs rVI = 0
    have h_ne_rVI_rVX : rVI ≠ rVX := h_ne_rVX_rVI.symm
    rw [hs5_other_of_ne_rVX rVI h_ne_rVI_rVX]
    exact hs4_rVI
  · -- tmp1 = 0.
    have h_tmp1_lt : k + 5 < P.numRegs := by
      rw [h_numRegs_eq]
      have : 0 < frag_f.numRegs := frag_f.numRegs_pos; omega
    set rTmp1 : Fin P.numRegs := ⟨k + 5, h_tmp1_lt⟩
    change s5.regs rTmp1 = 0
    have h_ne_rTmp1_rVX : rTmp1 ≠ rVX := by
      intro h; have : (k + 5 : ℕ) = k + 3 := congrArg Fin.val h; omega
    rw [hs5_other_of_ne_rVX rTmp1 h_ne_rTmp1_rVX]
    have h_ne_rTmp1_rZ : rTmp1 ≠ rZ := by
      intro h; have : (k + 5 : ℕ) = 0 := congrArg Fin.val h; omega
    have h_ne_rTmp1_rAcc : rTmp1 ≠ rAcc := by
      intro h; have : (k + 5 : ℕ) = 1 := congrArg Fin.val h; omega
    have h_ne_rTmp1_rVI : rTmp1 ≠ rVI := by
      intro h; have : (k + 5 : ℕ) = k + 4 := congrArg Fin.val h; omega
    rw [hs4_other rTmp1 h_ne_rTmp1_rZ h_ne_rTmp1_rAcc h_ne_rTmp1_rVX
      h_ne_rTmp1_rVI]
    change (URMState.init P v).regs rTmp1 = 0
    apply URMState.init_regs_zero_outside_inputs P v h_outer_inputRegs
    right; right
    change 2 + (k + 1) ≤ k + 5; omega
  · -- tmp2 = 0.
    exact hs5_rTmp2
  · -- Accumulator = natBSum 0 ... = 0.
    change s5.regs rAcc = natBSum 0 _
    have h_ne_rAcc_rVX' : rAcc ≠ rVX := h_ne_rAcc_rVX
    rw [hs5_other_of_ne_rVX rAcc h_ne_rAcc_rVX']
    rw [hs4_rAcc]
    rfl
  · -- f's reindexed block is all 0.
    intro r
    have hr : r.val < frag_f.numRegs := r.isLt
    have h_idx_lt : (k + 7) + r.val < P.numRegs := by
      rw [h_numRegs_eq]; omega
    set rBlock : Fin P.numRegs := ⟨(k + 7) + r.val, h_idx_lt⟩
    change s5.regs rBlock = 0
    have h_ne_rBlock_rVX : rBlock ≠ rVX := by
      intro h
      have : ((k + 7) + r.val : ℕ) = k + 3 := congrArg Fin.val h
      omega
    rw [hs5_other_of_ne_rVX rBlock h_ne_rBlock_rVX]
    have h_ne_rBlock_rZ : rBlock ≠ rZ := by
      intro h
      have : ((k + 7) + r.val : ℕ) = 0 := congrArg Fin.val h
      omega
    have h_ne_rBlock_rAcc : rBlock ≠ rAcc := by
      intro h
      have : ((k + 7) + r.val : ℕ) = 1 := congrArg Fin.val h
      omega
    have h_ne_rBlock_rVI : rBlock ≠ rVI := by
      intro h
      have : ((k + 7) + r.val : ℕ) = k + 4 := congrArg Fin.val h
      omega
    rw [hs4_other rBlock h_ne_rBlock_rZ h_ne_rBlock_rAcc h_ne_rBlock_rVX
      h_ne_rBlock_rVI]
    change (URMState.init P v).regs rBlock = 0
    apply URMState.init_regs_zero_outside_inputs P v h_outer_inputRegs
    right; right
    change 2 + (k + 1) ≤ (k + 7) + r.val; omega

end LawvereERKSim
end GebLean
