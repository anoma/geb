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
- `compileFrag_bsum_partial_invariant`,
  `compileFrag_bsum_partial_base`: top-of-loop partial-iteration
  invariant for `compileFrag_bsum` and its base case at `i = 0`
  after the prelude.
- `compileFrag_bsum_phase_i0_post`,
  `compileFrag_bsum_partial_phase_i0`: post-state predicate at the
  end of one iteration's zero-sweep (PC = `15 + frag_f.numRegs`)
  and the Phase i.0 preservation theorem from
  `compileFrag_bsum_partial_invariant @ i.val`.
- `compileFrag_bsum_prologueBlock_instr_at`: per-slot
  instruction-presence bundle for the per-iteration prologue,
  producing a `preservingTransferInstrs` witness at each prologue
  slot.
- `compileFrag_bsum_phase_i1_post`,
  `compileFrag_bsum_partial_phase_i1`: post-state predicate at the
  end of one iteration's prologue (PC = `15 + frag_f.numRegs
  + 9 * (k + 1)`) and the Phase i.1 preservation theorem from
  `compileFrag_bsum_phase_i0_post @ i`.
- `compileFrag_bsum_accUpdateBlock_instr_at`: instruction-presence
  discharger for the per-iteration accumulator-update block plus the
  epilogue's `.incR vI` and `URMRaw.goto bsum_topPC`, packaging the
  six lookups at PCs `bsum_trBase frag_f .. bsum_gotoTopPC frag_f` as
  a `transferLoopInstrs` witness alongside two raw `getElem?`
  equations.
- `compileFrag_bsum_partial_phase_i3`: Phase i.3 preservation theorem
  from `compileFrag_bsum_phase_i2_post @ i`, transitioning to
  `compileFrag_bsum_partial_invariant @ (i.val + 1)` after running
  the accumulator-update transferLoop, the `incR vI`, and the
  `goto topPC`.
- `compileER_pre_stop_correct_bsum`: pre-stop correctness theorem for
  `.bsum f`. Given the inductive hypothesis on `f` in the standard
  pre-stop existential form, produces a `T0 ≤ compileER_runtime (.bsum f) v`
  such that at step `T0` the URM is at the trailing `.stopR`
  (`PC = instrs.size - 1`), the output register holds
  `(.bsum f).interp v`, and on every earlier step the PC is strictly
  below `instrs.size - 1`. Final step of the bsum pre-stop chain
  consumed by the bsum runFor wrapper via
  `compileER_pre_stop_to_runFor` (`Embedding.lean`).

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

/-- Zero-sweep instruction-presence discharger for `compileFrag_bsum`:
at PCs `15 .. 15 + frag_f.numRegs - 1`, the outer program's
instruction is `assignR (k + 7 + r.val) 0`, expressed in bounded
form as `URMInstr.assign ⟨k + 7 + r.val, _⟩ 0`. Mirrors the
peeling style of `ProgramEmbedsFragment_compileFrag_bsum_fBody`,
specialised to the zero-sweep segment. -/
private theorem compileFrag_bsum_zeroSweep_instr_at
    {k : ℕ}
    (frag_f : CompiledFragment (k + 1))
    (r : Fin frag_f.numRegs) :
    ∃ h : (k + 7) + r.val
        < (compileFrag_bsum frag_f).toURMProgram.numRegs,
      (compileFrag_bsum frag_f).toURMProgram.instrs[15 + r.val]?
        = some (URMInstr.assign
            ⟨(k + 7) + r.val, h⟩ 0) := by
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
  -- outer.numRegs = nR.
  let outer : URMProgram (k + 1) := (compileFrag_bsum frag_f).toURMProgram
  have h_lt : (k + 7) + r.val < outer.numRegs := by
    have hr : r.val < frag_f.numRegs := r.isLt
    change (k + 7) + r.val < (k + 7) + frag_f.numRegs
    omega
  refine ⟨h_lt, ?_⟩
  -- Reconstruct the boundedness witness on rawList.
  have hAcc : vAcc + 1 ≤ nR := by
    change 1 + 1 ≤ k + 7 + frag_f.numRegs
    have : 0 < frag_f.numRegs := frag_f.numRegs_pos; omega
  have hBoundIn : vBoundIn + 1 ≤ nR := by
    change 2 + 1 ≤ k + 7 + frag_f.numRegs
    have : 0 < frag_f.numRegs := frag_f.numRegs_pos; omega
  have hVX : vX + 1 ≤ nR := by
    change k + 3 + 1 ≤ k + 7 + frag_f.numRegs
    have : 0 < frag_f.numRegs := frag_f.numRegs_pos; omega
  have hVI : vI + 1 ≤ nR := by
    change k + 4 + 1 ≤ k + 7 + frag_f.numRegs
    have : 0 < frag_f.numRegs := frag_f.numRegs_pos; omega
  have hTmp1 : tmp1 + 1 ≤ nR := by
    change k + 5 + 1 ≤ k + 7 + frag_f.numRegs
    have : 0 < frag_f.numRegs := frag_f.numRegs_pos; omega
  have hTmp2 : tmp2 + 1 ≤ nR := by
    change k + 6 + 1 ≤ k + 7 + frag_f.numRegs
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
  -- Index of 15 + r.val in rawList: lies inside the zero-sweep segment,
  -- which starts at prelude.length + loopTop.length = 13 + 2 = 15.
  have hr : r.val < frag_f.numRegs := r.isLt
  have h_idx_lt : 15 + r.val < rawList.length := by
    have h_raw_len : rawList.length
        = prelude.length + loopTop.length + zeroSweep.length
          + prologue.length + fBody.length + accUpdate.length
          + epilogue.length := by
      change (prelude ++ loopTop ++ zeroSweep ++ prologue ++ fBody
        ++ accUpdate ++ epilogue).length = _
      simp only [List.length_append]
    rw [h_raw_len, h_prelude_len, h_loopTop_len, h_zeroSweep_len]
    omega
  change (URMInstrRaw.toBoundedArray nR rawList hBoundOuter)[15 + r.val]?
    = some (URMInstrRaw.toBounded nR
        (URMInstrRaw.assignR (fBase + r.val) 0)
        (by simp only [URMInstrRaw.regBound]; omega))
  rw [URMInstrRaw.toBoundedArray_getElem? nR rawList hBoundOuter
      (15 + r.val) h_idx_lt]
  -- Establish the raw equality:
  --   rawList[15 + r.val] = URMInstrRaw.assignR (fBase + r.val) 0.
  have h_raw_eq :
      rawList[15 + r.val]'h_idx_lt
        = URMInstrRaw.assignR (fBase + r.val) 0 := by
    -- rawList = prelude ++ loopTop ++ zeroSweep ++ prologue ++ fBody
    --            ++ accUpdate ++ epilogue.
    -- Peel epilogue: index < (prelude ++ loopTop ++ zeroSweep
    --   ++ prologue ++ fBody ++ accUpdate).length.
    have h_in_prefix6 :
        15 + r.val
          < ((((((prelude ++ loopTop) ++ zeroSweep) ++ prologue)
              ++ fBody) ++ accUpdate)).length := by
      simp only [List.length_append]
      rw [h_prelude_len, h_loopTop_len, h_zeroSweep_len]
      omega
    have h_in_prefix5 :
        15 + r.val
          < (((((prelude ++ loopTop) ++ zeroSweep) ++ prologue)
              ++ fBody)).length := by
      simp only [List.length_append]
      rw [h_prelude_len, h_loopTop_len, h_zeroSweep_len]
      omega
    have h_in_prefix4 :
        15 + r.val
          < ((((prelude ++ loopTop) ++ zeroSweep) ++ prologue)).length := by
      simp only [List.length_append]
      rw [h_prelude_len, h_loopTop_len, h_zeroSweep_len]
      omega
    have h_in_prefix3 :
        15 + r.val
          < (((prelude ++ loopTop) ++ zeroSweep)).length := by
      simp only [List.length_append]
      rw [h_prelude_len, h_loopTop_len, h_zeroSweep_len]
      omega
    -- Peel each suffix.
    have h_step1 :
        rawList[15 + r.val]'h_idx_lt
          = ((((((prelude ++ loopTop) ++ zeroSweep) ++ prologue)
                ++ fBody) ++ accUpdate))[15 + r.val]'h_in_prefix6 := by
      change (((((((prelude ++ loopTop) ++ zeroSweep) ++ prologue)
            ++ fBody) ++ accUpdate) ++ epilogue))[15 + r.val]'h_idx_lt
        = _
      rw [List.getElem_append_left h_in_prefix6]
    rw [h_step1]
    have h_step2 :
        ((((((prelude ++ loopTop) ++ zeroSweep) ++ prologue)
              ++ fBody) ++ accUpdate))[15 + r.val]'h_in_prefix6
          = (((((prelude ++ loopTop) ++ zeroSweep) ++ prologue)
                ++ fBody))[15 + r.val]'h_in_prefix5 := by
      rw [List.getElem_append_left h_in_prefix5]
    rw [h_step2]
    have h_step3 :
        (((((prelude ++ loopTop) ++ zeroSweep) ++ prologue)
              ++ fBody))[15 + r.val]'h_in_prefix5
          = ((((prelude ++ loopTop) ++ zeroSweep) ++ prologue))[15 + r.val]'
              h_in_prefix4 := by
      rw [List.getElem_append_left h_in_prefix4]
    rw [h_step3]
    have h_step4 :
        ((((prelude ++ loopTop) ++ zeroSweep) ++ prologue))[15 + r.val]'
            h_in_prefix4
          = (((prelude ++ loopTop) ++ zeroSweep))[15 + r.val]'h_in_prefix3 := by
      rw [List.getElem_append_left h_in_prefix3]
    rw [h_step4]
    -- Peel prelude++loopTop: index ≥ (prelude++loopTop).length = 15.
    have h_pref2_le : ((prelude ++ loopTop)).length ≤ 15 + r.val := by
      simp only [List.length_append]
      rw [h_prelude_len, h_loopTop_len]
      omega
    have h_idx_in_sweep : 15 + r.val - (prelude ++ loopTop).length
        < zeroSweep.length := by
      simp only [List.length_append]
      rw [h_prelude_len, h_loopTop_len, h_zeroSweep_len]
      omega
    have h_step5 :
        (((prelude ++ loopTop) ++ zeroSweep))[15 + r.val]'h_in_prefix3
          = zeroSweep[15 + r.val - (prelude ++ loopTop).length]'
              h_idx_in_sweep := by
      rw [List.getElem_append_right h_pref2_le]
    rw [h_step5]
    -- Simplify the index inside zeroSweep to r.val.
    have h_idx_eq : 15 + r.val - (prelude ++ loopTop).length = r.val := by
      simp only [List.length_append]
      rw [h_prelude_len, h_loopTop_len]
      omega
    have h_r_lt_sweep : r.val < zeroSweep.length := by
      rw [h_zeroSweep_len]; exact hr
    have h_step6 :
        zeroSweep[15 + r.val - (prelude ++ loopTop).length]'h_idx_in_sweep
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
    -- (List.finRange n)[i] = ⟨i, hi⟩.
    have h_finRange_at : (List.finRange frag_f.numRegs)[r.val]'h_r_lt_fin
        = ⟨r.val, hr⟩ := by
      apply List.getElem_finRange
    rw [h_finRange_at]
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
carries the running value of `i` and proofs about the outer
scaffolding registers; f's reindexed block is not tracked
(Phase i.0's zero-sweep re-establishes it at the start of each
iteration). -/
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
      acc_eq := ?_ }
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

/-- Post-state predicate for Phase i.0 of one bsum iteration:
the state immediately after executing the loop-top `jumpZR vX`
(taking the non-zero branch, since `i.val < v 0` means
`s.regs vX = v 0 - i.val > 0`), the body-start `decR vX`, and
the `frag_f.numRegs` `assignR (fBase + r) 0` zero-sweep
instructions. PC sits at `15 + frag_f.numRegs` — the first
instruction of the per-iteration prologue. The `vX_eq` clause
records the decrement (`v 0 - i.val - 1`), and `fBody_zero`
records that f's reindexed block has just been re-flushed to
`0`. All other clauses (`hi_le`, `zReg_zero`, `outer_inputs`,
`vI_eq`, `tmp1_zero`, `tmp2_zero`, `acc_eq`) carry over
verbatim from `compileFrag_bsum_partial_invariant @ i.val`. -/
private structure compileFrag_bsum_phase_i0_post
    {k : ℕ}
    (frag_f : CompiledFragment (k + 1))
    (f : ERMor1 (k + 1))
    (v : Fin (k + 1) → ℕ)
    (i : Fin (v 0))
    (s : URMState (compileFrag_bsum frag_f).toURMProgram)
    : Prop where
  /-- `i.val < v 0`, packaged for downstream consumers. -/
  hi_lt : i.val < v 0 := i.isLt
  /-- PC sits one past the zero-sweep, at the start of the
  per-iteration prologue. -/
  pc_eq : s.pc = 15 + frag_f.numRegs
  /-- `V_z` (register 0) holds `0`. -/
  zReg_zero : s.regs ⟨0, (compileFrag_bsum frag_f).numRegs_pos⟩ = 0
  /-- Outer input slots `2..k+2` hold the input vector. -/
  outer_inputs : ∀ (j : Fin (k + 1)),
    s.regs ⟨2 + j.val, by
      have hj : j.val < k + 1 := j.isLt
      change 2 + j.val < k + 7 + frag_f.numRegs
      have : 0 < frag_f.numRegs := frag_f.numRegs_pos
      omega⟩ = v j
  /-- `V_x` (register `k + 3`) holds `v 0 - i.val - 1` after the
  body-start `decR vX`. -/
  vX_eq : s.regs ⟨k + 3, by
    change k + 3 < k + 7 + frag_f.numRegs
    have : 0 < frag_f.numRegs := frag_f.numRegs_pos
    omega⟩ = v 0 - i.val - 1
  /-- `V_i` (register `k + 4`) still holds the pre-iteration counter
  `i.val`; the body's `incR vI` lives in Phase i.3. -/
  vI_eq : s.regs ⟨k + 4, by
    change k + 4 < k + 7 + frag_f.numRegs
    have : 0 < frag_f.numRegs := frag_f.numRegs_pos
    omega⟩ = i.val
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
  /-- The accumulator (register 1) still holds the pre-iteration
  partial sum `Σ_{j < i.val} f.interp (j :: tail v)`. -/
  acc_eq : s.regs ⟨1, by
    change 1 < k + 7 + frag_f.numRegs
    have : 0 < frag_f.numRegs := frag_f.numRegs_pos
    omega⟩
      = natBSum i.val (fun j => f.interp (Fin.cons j (Fin.tail v)))
  /-- f's reindexed register block has just been flushed to `0`
  by the zero-sweep. -/
  fBody_zero : ∀ r : Fin frag_f.numRegs,
    s.regs ⟨(k + 7) + r.val, by
      have hr : r.val < frag_f.numRegs := r.isLt
      change (k + 7) + r.val < k + 7 + frag_f.numRegs
      omega⟩ = 0

/-- Phase i.0 preservation lemma: from
`compileFrag_bsum_partial_invariant @ i.val`, running for
`2 + (compileERFrag f).numRegs` further steps (the loop-top
`jumpZR vX` non-zero branch, the body-start `decR vX`, and the
`numRegs_f` zero-sweep `assignR` instructions) lands the state
in `compileFrag_bsum_phase_i0_post @ i`. The accompanying
strict PC bound states that during these `2 + numRegs_f`
steps the intermediate PC stays below `15 + numRegs_f`. -/
private theorem compileFrag_bsum_partial_phase_i0
    {k : ℕ}
    (f : ERMor1 (k + 1))
    (v : Fin (k + 1) → ℕ)
    (i : Fin (v 0))
    (sPre : URMState
      (compileFrag_bsum (compileERFrag f)).toURMProgram)
    (h_inv : compileFrag_bsum_partial_invariant
              (compileERFrag f) f v i.val i.isLt.le sPre) :
    compileFrag_bsum_phase_i0_post (compileERFrag f) f v i
      (URMState.runFor (compileFrag_bsum (compileERFrag f)).toURMProgram
        sPre (2 + (compileERFrag f).numRegs)) ∧
    (∀ k' < 2 + (compileERFrag f).numRegs,
      (URMState.runFor (compileFrag_bsum (compileERFrag f)).toURMProgram
        sPre k').pc
        < 15 + (compileERFrag f).numRegs) := by
  -- Abbreviations matching the outer program; introduced via `let`
  -- so the goal is rewritten in terms of `P`, `frag_f`, etc.
  let frag_f : CompiledFragment (k + 1) := compileERFrag f
  let outerFrag : CompiledFragment (k + 1) := compileFrag_bsum frag_f
  let P : URMProgram (k + 1) := outerFrag.toURMProgram
  change compileFrag_bsum_phase_i0_post frag_f f v i
      (URMState.runFor P sPre (2 + frag_f.numRegs)) ∧
    (∀ k' < 2 + frag_f.numRegs,
      (URMState.runFor P sPre k').pc < 15 + frag_f.numRegs)
  have h_numRegs_eq : P.numRegs = (k + 7) + frag_f.numRegs := rfl
  have h_numRegs_pos : 0 < P.numRegs := outerFrag.numRegs_pos
  -- Bound proofs for the named registers.
  have h_vX_lt : k + 3 < P.numRegs := by
    rw [h_numRegs_eq]
    have : 0 < frag_f.numRegs := frag_f.numRegs_pos; omega
  -- Fin-wrapped vX handle.
  let rVX : Fin P.numRegs := ⟨k + 3, h_vX_lt⟩
  -- Instruction-presence lookups at PCs 13 and 14. The literal exitPC
  -- value at PC 13 inside `compileFrag_bsum` is
  -- `15 + frag_f.numRegs + 9 * (k + 1) + (frag_f.instrs.size - 1) + 6`;
  -- we capture it as `exitPC_lit` so the `jumpZ` lookup reduces by `rfl`.
  let exitPC_lit : ℕ :=
    15 + frag_f.numRegs + 9 * (k + 1) + (frag_f.instrs.size - 1) + 6
  have h_at_13 : P.instrs[(13 : ℕ)]?
      = some (URMInstr.jumpZ rVX exitPC_lit 14) := rfl
  have h_at_14 : P.instrs[(14 : ℕ)]? = some (URMInstr.dec rVX) := rfl
  -- Instruction-presence bundle for the zero-sweep block at PC 15.
  have h_sweep : ∀ r : Fin frag_f.numRegs,
      ∃ h : (k + 7) + r.val < P.numRegs,
        P.instrs[15 + r.val]?
          = some (URMInstr.assign ⟨(k + 7) + r.val, h⟩ 0) :=
    fun r => compileFrag_bsum_zeroSweep_instr_at frag_f r
  -- Pre-state hypotheses from the i.val-invariant.
  have h_s_pc : sPre.pc = 13 := h_inv.pc_eq
  have h_s_vX : sPre.regs rVX = v 0 - i.val := h_inv.vX_eq
  -- Total step count T0 := 2 + frag_f.numRegs.
  refine ⟨?_, ?_⟩
  · -- Phase i.0 post-state.
    -- Step 1 (PC 13): the jumpZ takes the non-zero branch, landing
    -- at PC 14 (= bodyStartPC).
    have h_vX_pos : sPre.regs rVX ≠ 0 := by
      rw [h_s_vX]
      have h_lt : i.val < v 0 := i.isLt
      omega
    have h_step0 :
        URMState.step P sPre =
          { pc := 14
            regs := sPre.regs } := by
      have h := URMState.step_of_getElem?_jumpZ P sPre 13 rVX
        exitPC_lit 14 h_s_pc h_at_13
      rw [h]
      simp only [if_neg h_vX_pos]
    set s1 : URMState P :=
        { pc := 14
          regs := sPre.regs }
    have h_runFor_1 : URMState.runFor P sPre 1 = s1 := by
      change URMState.runFor P (URMState.step P sPre) 0 = _
      rw [URMState.runFor_zero, h_step0]
    have hs1_pc : s1.pc = 14 := rfl
    have hs1_vX : s1.regs rVX = v 0 - i.val := h_s_vX
    -- Step 2 (PC 14): decR vX.
    have h_step1 :
        URMState.step P s1 =
          { pc := 15
            regs := Function.update s1.regs rVX (s1.regs rVX - 1) } := by
      have h := URMState.step_of_getElem?_dec P s1 14 rVX hs1_pc h_at_14
      rw [h]
    set s2 : URMState P :=
        { pc := 15
          regs := Function.update s1.regs rVX (s1.regs rVX - 1) }
    have h_runFor_2 : URMState.runFor P sPre 2 = s2 := by
      have h_two : (2 : ℕ) = 1 + 1 := by omega
      rw [h_two, URMState.runFor_add, h_runFor_1]
      change URMState.runFor P (URMState.step P s1) 0 = _
      rw [URMState.runFor_zero, h_step1]
    -- s2 register values.
    have hs2_pc : s2.pc = 15 := rfl
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
      compileFrag_bsum_zeroSweep_correct P 15 (k + 7) frag_f.numRegs
        h_sweep s2 hs2_pc
    set s3 : URMState P := URMState.runFor P s2 frag_f.numRegs
    -- s3 PC.
    have hs3_pc : s3.pc = 15 + frag_f.numRegs := sw_pc
    -- s3 fBody (all swept registers).
    have hs3_fBody : ∀ r : Fin frag_f.numRegs,
        ∀ h : (k + 7) + r.val < P.numRegs,
          s3.regs ⟨(k + 7) + r.val, h⟩ = 0 := sw_zero
    -- s3 other-of-rVX-and-block: agrees with s2.
    have hs3_other : ∀ q : Fin P.numRegs,
        (∀ r : Fin frag_f.numRegs, q.val ≠ (k + 7) + r.val) →
        s3.regs q = s2.regs q := sw_other
    -- Helper: for a register q outside the f-body block (q.val < k + 7),
    -- s3.regs q = s2.regs q.
    have hs3_outside_block : ∀ q : Fin P.numRegs,
        q.val < k + 7 → s3.regs q = s2.regs q := by
      intro q hq
      apply hs3_other
      intro r heq
      have hr : r.val < frag_f.numRegs := r.isLt
      omega
    -- Discharge each phase_i0_post clause.
    refine
      { hi_lt := i.isLt
        pc_eq := ?_
        zReg_zero := ?_
        outer_inputs := ?_
        vX_eq := ?_
        vI_eq := ?_
        tmp1_zero := ?_
        tmp2_zero := ?_
        acc_eq := ?_
        fBody_zero := ?_ }
    · -- pc = 15 + frag_f.numRegs.
      exact hs3_pc
    · -- zReg = 0.
      have h_outside : (⟨0, h_numRegs_pos⟩ : Fin P.numRegs).val < k + 7 := by
        change (0 : ℕ) < k + 7; omega
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
      have h_outside : (⟨2 + j.val, h_lt⟩ : Fin P.numRegs).val < k + 7 := by
        change 2 + j.val < k + 7; omega
      rw [hs3_outside_block ⟨2 + j.val, h_lt⟩ h_outside]
      have h_ne_rVX : (⟨2 + j.val, h_lt⟩ : Fin P.numRegs) ≠ rVX := by
        intro h; have : (2 + j.val : ℕ) = k + 3 := congrArg Fin.val h; omega
      rw [hs2_other_of_ne_rVX _ h_ne_rVX]
      exact h_inv.outer_inputs j
    · -- vX = v 0 - i.val - 1.
      have h_outside : rVX.val < k + 7 := by change k + 3 < k + 7; omega
      rw [hs3_outside_block rVX h_outside]
      exact hs2_rVX
    · -- vI = i.val.
      have h_vI_lt : k + 4 < P.numRegs := by
        rw [h_numRegs_eq]
        have : 0 < frag_f.numRegs := frag_f.numRegs_pos; omega
      have h_outside : (⟨k + 4, h_vI_lt⟩ : Fin P.numRegs).val < k + 7 := by
        change k + 4 < k + 7; omega
      rw [hs3_outside_block ⟨k + 4, h_vI_lt⟩ h_outside]
      have h_ne_rVX : (⟨k + 4, h_vI_lt⟩ : Fin P.numRegs) ≠ rVX := by
        intro h; have : (k + 4 : ℕ) = k + 3 := congrArg Fin.val h; omega
      rw [hs2_other_of_ne_rVX _ h_ne_rVX]
      exact h_inv.vI_eq
    · -- tmp1 = 0.
      have h_tmp1_lt : k + 5 < P.numRegs := by
        rw [h_numRegs_eq]
        have : 0 < frag_f.numRegs := frag_f.numRegs_pos; omega
      have h_outside : (⟨k + 5, h_tmp1_lt⟩ : Fin P.numRegs).val < k + 7 := by
        change k + 5 < k + 7; omega
      rw [hs3_outside_block ⟨k + 5, h_tmp1_lt⟩ h_outside]
      have h_ne_rVX : (⟨k + 5, h_tmp1_lt⟩ : Fin P.numRegs) ≠ rVX := by
        intro h; have : (k + 5 : ℕ) = k + 3 := congrArg Fin.val h; omega
      rw [hs2_other_of_ne_rVX _ h_ne_rVX]
      exact h_inv.tmp1_zero
    · -- tmp2 = 0.
      have h_tmp2_lt : k + 6 < P.numRegs := by
        rw [h_numRegs_eq]
        have : 0 < frag_f.numRegs := frag_f.numRegs_pos; omega
      have h_outside : (⟨k + 6, h_tmp2_lt⟩ : Fin P.numRegs).val < k + 7 := by
        change k + 6 < k + 7; omega
      rw [hs3_outside_block ⟨k + 6, h_tmp2_lt⟩ h_outside]
      have h_ne_rVX : (⟨k + 6, h_tmp2_lt⟩ : Fin P.numRegs) ≠ rVX := by
        intro h; have : (k + 6 : ℕ) = k + 3 := congrArg Fin.val h; omega
      rw [hs2_other_of_ne_rVX _ h_ne_rVX]
      exact h_inv.tmp2_zero
    · -- acc = natBSum i.val ...
      have h_acc_lt : 1 < P.numRegs := by
        rw [h_numRegs_eq]
        have : 0 < frag_f.numRegs := frag_f.numRegs_pos; omega
      have h_outside : (⟨1, h_acc_lt⟩ : Fin P.numRegs).val < k + 7 := by
        change (1 : ℕ) < k + 7; omega
      rw [hs3_outside_block ⟨1, h_acc_lt⟩ h_outside]
      have h_ne_rVX : (⟨1, h_acc_lt⟩ : Fin P.numRegs) ≠ rVX := by
        intro h; have : (1 : ℕ) = k + 3 := congrArg Fin.val h; omega
      rw [hs2_other_of_ne_rVX _ h_ne_rVX]
      exact h_inv.acc_eq
    · -- fBody_zero: every block register is 0.
      intro r
      have hr : r.val < frag_f.numRegs := r.isLt
      have h_idx_lt : (k + 7) + r.val < P.numRegs := by
        rw [h_numRegs_eq]; omega
      exact hs3_fBody r h_idx_lt
  · -- Strict PC bound: ∀ k' < 2 + numRegs_f, (runFor sPre k').pc
    -- < 15 + numRegs_f.
    intro k' hk'
    -- Case split on k' ≤ 1 (PC 13 or PC 14) versus k' ≥ 2 (in the sweep).
    rcases Nat.lt_or_ge k' 2 with hlt | hge
    · -- k' ∈ {0, 1}: PC = 13 or 14.
      rcases Nat.lt_or_ge k' 1 with hlt1 | hge1
      · -- k' = 0: PC = sPre.pc = 13.
        have hk'_eq : k' = 0 := Nat.lt_one_iff.mp hlt1
        rw [hk'_eq, URMState.runFor_zero, h_s_pc]
        have : 0 < frag_f.numRegs := frag_f.numRegs_pos; omega
      · -- k' = 1: runFor sPre 1 has pc = 14.
        have hk'_eq : k' = 1 := by omega
        rw [hk'_eq]
        -- Re-derive step 0 transition.
        have h_vX_pos : sPre.regs rVX ≠ 0 := by
          rw [h_s_vX]
          have h_lt : i.val < v 0 := i.isLt
          omega
        have h_step0 :
            URMState.step P sPre =
              { pc := 14
                regs := sPre.regs } := by
          have h := URMState.step_of_getElem?_jumpZ P sPre 13 rVX
            exitPC_lit 14 h_s_pc h_at_13
          rw [h]
          simp only [if_neg h_vX_pos]
        change (URMState.runFor P (URMState.step P sPre) 0).pc
          < 15 + frag_f.numRegs
        rw [URMState.runFor_zero, h_step0]
        change (14 : ℕ) < 15 + frag_f.numRegs
        have : 0 < frag_f.numRegs := frag_f.numRegs_pos; omega
    · -- k' ≥ 2: runFor sPre k' = runFor s2 (k' - 2), which is inside
      -- the zero-sweep; apply the strict PC bound for the zero-sweep.
      have hk'_eq : k' = 2 + (k' - 2) := by omega
      have h_k_minus_2_lt : k' - 2 < frag_f.numRegs := by omega
      -- Re-derive s2 = runFor sPre 2.
      have h_vX_pos : sPre.regs rVX ≠ 0 := by
        rw [h_s_vX]
        have h_lt : i.val < v 0 := i.isLt
        omega
      have h_step0 :
          URMState.step P sPre =
            { pc := 14
              regs := sPre.regs } := by
        have h := URMState.step_of_getElem?_jumpZ P sPre 13 rVX
          exitPC_lit 14 h_s_pc h_at_13
        rw [h]
        simp only [if_neg h_vX_pos]
      set s1' : URMState P :=
          { pc := 14
            regs := sPre.regs }
      have h_runFor_1 : URMState.runFor P sPre 1 = s1' := by
        change URMState.runFor P (URMState.step P sPre) 0 = _
        rw [URMState.runFor_zero, h_step0]
      have hs1_pc : s1'.pc = 14 := rfl
      have h_step1 :
          URMState.step P s1' =
            { pc := 15
              regs := Function.update s1'.regs rVX (s1'.regs rVX - 1) } := by
        have h := URMState.step_of_getElem?_dec P s1' 14 rVX hs1_pc h_at_14
        rw [h]
      set s2' : URMState P :=
          { pc := 15
            regs := Function.update s1'.regs rVX (s1'.regs rVX - 1) }
      have h_runFor_2 : URMState.runFor P sPre 2 = s2' := by
        have h_two : (2 : ℕ) = 1 + 1 := by omega
        rw [h_two, URMState.runFor_add, h_runFor_1]
        change URMState.runFor P (URMState.step P s1') 0 = _
        rw [URMState.runFor_zero, h_step1]
      have hs2_pc : s2'.pc = 15 := rfl
      -- Apply zero-sweep strict PC bound.
      rw [hk'_eq, URMState.runFor_add, h_runFor_2]
      have h_bound :=
        compileFrag_bsum_zeroSweep_pc_strict_bound P 15 (k + 7)
          frag_f.numRegs h_sweep s2' hs2_pc (k' - 2) h_k_minus_2_lt
      omega

set_option maxHeartbeats 4000000 in
-- The nine-fold `first | exact h_outerInstr_lookup d (by decide)` ladder
-- below requires reducing `URMRaw.preservingTransfer ... [d]` against
-- `preservingTransferInstrs`'s nine field shapes; the unification cost
-- exceeds the default budget.
/-- Per-slot prologue instruction-presence bundle for `compileFrag_bsum`:
at PCs `15 + frag_f.numRegs + 9 * s.val .. 15 + frag_f.numRegs
+ 9 * s.val + 8`, the outer program's instructions match the nine raw
instructions of `URMRaw.preservingTransfer` with source register
`bsum_prologueSrc k s`, destination register `(k + 7) +
(frag_f.inputRegs s).val`, scratch register `k + 5` (`tmp1`), and
reserved-zero register `0`. Mirrors
`PreservingTransferInstrs_compileFrag_comp_inputCopies` in `Loops.lean`,
specialised to bsum's per-iteration prologue. -/
private theorem compileFrag_bsum_prologueBlock_instr_at
    {k : ℕ}
    (frag_f : CompiledFragment (k + 1))
    (s : Fin (k + 1)) :
    let outer := (compileFrag_bsum frag_f).toURMProgram
    ∃ (h_src : bsum_prologueSrc k s < outer.numRegs)
      (h_dst : (k + 7) + (frag_f.inputRegs s).val < outer.numRegs)
      (h_tmp : k + 5 < outer.numRegs)
      (h_z : 0 < outer.numRegs),
      preservingTransferInstrs outer (15 + frag_f.numRegs + 9 * s.val)
        ⟨bsum_prologueSrc k s, h_src⟩
        ⟨(k + 7) + (frag_f.inputRegs s).val, h_dst⟩
        ⟨k + 5, h_tmp⟩
        ⟨0, h_z⟩ := by
  intro outer
  -- Abbreviations mirroring the constructor of `compileFrag_bsum`.
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
  -- outer.numRegs = nR.
  have h_numRegs_eq : outer.numRegs = nR := rfl
  -- Bound proofs for the four registers.
  have h_src_lt : bsum_prologueSrc k s < outer.numRegs := by
    have hs : s.val < k + 1 := s.isLt
    rw [h_numRegs_eq]
    change bsum_prologueSrc k s < fBase + frag_f.numRegs
    have h_pos : 0 < frag_f.numRegs := frag_f.numRegs_pos
    simp only [bsum_prologueSrc]
    split <;> omega
  have h_dst_lt : (k + 7) + (frag_f.inputRegs s).val < outer.numRegs := by
    have hI : (frag_f.inputRegs s).val < frag_f.numRegs :=
      (frag_f.inputRegs s).isLt
    rw [h_numRegs_eq]
    change (k + 7) + (frag_f.inputRegs s).val < fBase + frag_f.numRegs
    omega
  have h_tmp_lt : k + 5 < outer.numRegs := by
    rw [h_numRegs_eq]
    have h_pos : 0 < frag_f.numRegs := frag_f.numRegs_pos
    change k + 5 < fBase + frag_f.numRegs; omega
  have h_z_lt : 0 < outer.numRegs := (compileFrag_bsum frag_f).numRegs_pos
  refine ⟨h_src_lt, h_dst_lt, h_tmp_lt, h_z_lt, ?_⟩
  -- Reconstruct the boundedness witness on rawList.
  have hAcc : vAcc + 1 ≤ nR := by
    change 1 + 1 ≤ k + 7 + frag_f.numRegs
    have : 0 < frag_f.numRegs := frag_f.numRegs_pos; omega
  have hBoundIn : vBoundIn + 1 ≤ nR := by
    change 2 + 1 ≤ k + 7 + frag_f.numRegs
    have : 0 < frag_f.numRegs := frag_f.numRegs_pos; omega
  have hVX : vX + 1 ≤ nR := by
    change k + 3 + 1 ≤ k + 7 + frag_f.numRegs
    have : 0 < frag_f.numRegs := frag_f.numRegs_pos; omega
  have hVI : vI + 1 ≤ nR := by
    change k + 4 + 1 ≤ k + 7 + frag_f.numRegs
    have : 0 < frag_f.numRegs := frag_f.numRegs_pos; omega
  have hTmp1 : tmp1 + 1 ≤ nR := by
    change k + 5 + 1 ≤ k + 7 + frag_f.numRegs
    have : 0 < frag_f.numRegs := frag_f.numRegs_pos; omega
  have hTmp2 : tmp2 + 1 ≤ nR := by
    change k + 6 + 1 ≤ k + 7 + frag_f.numRegs
    have : 0 < frag_f.numRegs := frag_f.numRegs_pos; omega
  have hFOut : fBase + frag_f.outputReg.val + 1 ≤ nR := by
    have : frag_f.outputReg.val < frag_f.numRegs :=
      frag_f.outputReg.isLt
    change fBase + frag_f.outputReg.val + 1 ≤ fBase + frag_f.numRegs
    omega
  have hPrologueSrc : ∀ s' : Fin (k + 1),
      bsum_prologueSrc k s' + 1 ≤ nR := by
    intro s'
    have hs' : s'.val < k + 1 := s'.isLt
    simp only [bsum_prologueSrc, nR, fBase]
    split <;> omega
  have hFIn : ∀ s' : Fin (k + 1),
      fBase + (frag_f.inputRegs s').val + 1 ≤ nR := by
    intro s'
    have : (frag_f.inputRegs s').val < frag_f.numRegs :=
      (frag_f.inputRegs s').isLt
    change fBase + (frag_f.inputRegs s').val + 1
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
    rcases hmem with ⟨s', _, hs⟩
    exact boundedBy_bsum_prologueBlock frag_f fBase tmp1
      prologueBase nR s' (hPrologueSrc s') (hFIn s') hTmp1 ins hs
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
  -- Concrete preservingTransfer block at slot s.
  let pt_s : List URMInstrRaw :=
    URMRaw.preservingTransfer (prologueBase + 9 * s.val)
      (bsum_prologueSrc k s)
      (fBase + (frag_f.inputRegs s).val) tmp1
  have h_pt_s_len : pt_s.length = 9 := rfl
  -- Split prologue at slot s.
  obtain ⟨pre_s, suf_s, h_prologue_split, h_pre_s_len⟩ :=
    flatMap_finRange_split (k + 1)
      (fun s' : Fin (k + 1) =>
        bsum_prologueBlock frag_f fBase tmp1 prologueBase s') s
  have h_each_pb_len : ∀ s' : Fin (k + 1),
      (bsum_prologueBlock frag_f fBase tmp1 prologueBase s').length = 9 :=
    fun _ => rfl
  have h_pre_s_len_eq : pre_s.length = 9 * s.val := by
    rw [h_pre_s_len]
    have h_foldr_const :
        ((List.finRange (k + 1)).filter
            (fun n => decide (n.val < s.val))).foldr
          (fun s' acc => acc +
            (bsum_prologueBlock frag_f fBase tmp1 prologueBase s').length) 0
          = ((List.finRange (k + 1)).filter
              (fun n => decide (n.val < s.val))).foldr
            (fun _ acc => acc + 9) 0 := by
      induction (List.filter (fun n : Fin (k + 1) =>
          decide (n.val < s.val)) (List.finRange (k + 1))) with
      | nil => rfl
      | cons hd tl ih_inner =>
        simp only [List.foldr_cons, ih_inner, h_each_pb_len hd]
    rw [h_foldr_const]
    have h_foldr_const_9 : ∀ (l : List (Fin (k + 1))),
        l.foldr (fun _ acc => acc + 9) 0 = 9 * l.length := by
      intro l
      induction l with
      | nil => rfl
      | cons _ tl ih_inner =>
        simp only [List.foldr_cons, List.length_cons, ih_inner]
        omega
    have h_filter_len :
        ((List.finRange (k + 1)).filter
          (fun n => decide (n.val < s.val))).length = s.val := by
      suffices h_aux : ∀ (a' m : ℕ) (_ : m ≤ a'),
          ((List.finRange a').filter
            (fun n => decide (n.val < m))).length = m by
        exact h_aux (k + 1) s.val (Nat.le_of_lt s.isLt)
      intro a' m hm
      induction a' generalizing m with
      | zero =>
        have : m = 0 := Nat.le_zero.mp hm
        subst this
        rfl
      | succ a'' ih_aux =>
        rw [List.finRange_succ, List.filter_cons]
        rcases Nat.lt_or_ge 0 m with hm_pos | hm_zero
        · obtain ⟨m'', rfl⟩ := Nat.exists_eq_succ_of_ne_zero
            (Nat.pos_iff_ne_zero.mp hm_pos)
          have hm' : m'' ≤ a'' := Nat.le_of_succ_le_succ hm
          have h_true : decide ((0 : Fin (a'' + 1)).val < m'' + 1) = true := by
            change decide (0 < m'' + 1) = true
            exact decide_eq_true (Nat.succ_pos _)
          rw [if_pos h_true]
          rw [List.length_cons, List.filter_map]
          have h_pred :
              ((fun n : Fin (a'' + 1) => decide (n.val < m'' + 1)) ∘ Fin.succ)
                = (fun y : Fin a'' => decide (y.val < m'')) := by
            funext y
            change decide (y.val + 1 < m'' + 1) = decide (y.val < m'')
            rcases Nat.lt_or_ge y.val m'' with h | h
            · rw [decide_eq_true h, decide_eq_true (Nat.succ_lt_succ h)]
            · rw [decide_eq_false (Nat.not_lt.mpr h),
                decide_eq_false (Nat.not_lt.mpr (Nat.succ_le_succ h))]
          rw [h_pred, List.length_map, ih_aux m'' hm']
        · have hm_zero' : m = 0 := Nat.le_zero.mp hm_zero
          subst hm_zero'
          have h_false : decide ((0 : Fin (a'' + 1)).val < 0) = false :=
            decide_eq_false (Nat.not_lt_zero _)
          rw [if_neg (by rw [h_false]; exact Bool.false_ne_true)]
          rw [List.filter_map]
          have h_pred :
              ((fun n : Fin (a'' + 1) => decide (n.val < 0)) ∘ Fin.succ)
                = fun _ : Fin a'' => false := by
            funext y
            change decide (y.val + 1 < 0) = false
            exact decide_eq_false (Nat.not_lt_zero _)
          rw [h_pred, List.length_map]
          have h_empty : ∀ (l : List (Fin a'')),
              (l.filter (fun _ => false)).length = 0 := by
            intro l
            induction l with
            | nil => rfl
            | cons _ tl ih_in =>
              rw [List.filter_cons]
              simp only [Bool.false_eq_true, ↓reduceIte]
              exact ih_in
          exact h_empty _
    rw [h_foldr_const_9, h_filter_len]
  -- Concrete prologue = pre_s ++ pt_s ++ suf_s.
  have h_prologue_full :
      prologue = pre_s ++ pt_s ++ suf_s := by
    change (List.finRange (k + 1)).flatMap _ = _
    exact h_prologue_split
  have h_prologue_len_eq : prologue.length
      = pre_s.length + pt_s.length + suf_s.length := by
    rw [h_prologue_full]
    rw [List.length_append, List.length_append]
  -- Lookup helper: rawList at PC prologueBase + 9*s.val + d equals pt_s[d].
  have h_lookup_pt :
      ∀ (d : ℕ) (hd : d < 9),
      let pos : ℕ := prelude.length + loopTop.length + zeroSweep.length
        + (pre_s.length + d)
      have h_idx_lt : pos < rawList.length := by
        have h_raw_len : rawList.length
            = prelude.length + loopTop.length + zeroSweep.length
              + prologue.length + fBody.length + accUpdate.length
              + epilogue.length := by
          change (prelude ++ loopTop ++ zeroSweep ++ prologue ++ fBody
            ++ accUpdate ++ epilogue).length = _
          simp only [List.length_append]
        rw [h_raw_len, h_prologue_len_eq, h_pt_s_len]
        change prelude.length + loopTop.length + zeroSweep.length
          + (pre_s.length + d) < _
        omega
      rawList[pos]'h_idx_lt
        = pt_s[d]'(by rw [h_pt_s_len]; exact hd) := by
    intro d hd pos h_idx_lt
    -- Peel each suffix block.
    have h_in_prefix6 :
        pos < ((((((prelude ++ loopTop) ++ zeroSweep) ++ prologue)
              ++ fBody) ++ accUpdate)).length := by
      simp only [List.length_append]
      change prelude.length + loopTop.length + zeroSweep.length
        + (pre_s.length + d) < _
      rw [h_prelude_len, h_loopTop_len, h_zeroSweep_len,
        h_prologue_len_eq, h_pt_s_len]
      omega
    have h_in_prefix5 :
        pos < (((((prelude ++ loopTop) ++ zeroSweep) ++ prologue)
              ++ fBody)).length := by
      simp only [List.length_append]
      change prelude.length + loopTop.length + zeroSweep.length
        + (pre_s.length + d) < _
      rw [h_prelude_len, h_loopTop_len, h_zeroSweep_len,
        h_prologue_len_eq, h_pt_s_len]
      omega
    have h_in_prefix4 :
        pos < ((((prelude ++ loopTop) ++ zeroSweep) ++ prologue)).length := by
      simp only [List.length_append]
      change prelude.length + loopTop.length + zeroSweep.length
        + (pre_s.length + d) < _
      rw [h_prelude_len, h_loopTop_len, h_zeroSweep_len,
        h_prologue_len_eq, h_pt_s_len]
      omega
    have h_step1 :
        rawList[pos]'h_idx_lt
          = ((((((prelude ++ loopTop) ++ zeroSweep) ++ prologue)
                ++ fBody) ++ accUpdate))[pos]'h_in_prefix6 := by
      change (((((((prelude ++ loopTop) ++ zeroSweep) ++ prologue)
            ++ fBody) ++ accUpdate) ++ epilogue))[pos]'h_idx_lt = _
      rw [List.getElem_append_left h_in_prefix6]
    rw [h_step1]
    have h_step2 :
        ((((((prelude ++ loopTop) ++ zeroSweep) ++ prologue)
              ++ fBody) ++ accUpdate))[pos]'h_in_prefix6
          = (((((prelude ++ loopTop) ++ zeroSweep) ++ prologue)
                ++ fBody))[pos]'h_in_prefix5 := by
      rw [List.getElem_append_left h_in_prefix5]
    rw [h_step2]
    have h_step3 :
        (((((prelude ++ loopTop) ++ zeroSweep) ++ prologue)
              ++ fBody))[pos]'h_in_prefix5
          = ((((prelude ++ loopTop) ++ zeroSweep) ++ prologue))[pos]'
              h_in_prefix4 := by
      rw [List.getElem_append_left h_in_prefix4]
    rw [h_step3]
    -- Peel prelude++loopTop++zeroSweep: index ≥ their combined length.
    have h_pref3_le :
        (((prelude ++ loopTop) ++ zeroSweep)).length ≤ pos := by
      simp only [List.length_append]
      rw [h_prelude_len, h_loopTop_len, h_zeroSweep_len]
      change _ ≤ prelude.length + loopTop.length + zeroSweep.length
        + (pre_s.length + d)
      rw [h_prelude_len, h_loopTop_len, h_zeroSweep_len]
      omega
    have h_idx_in_prologue :
        pos - (((prelude ++ loopTop) ++ zeroSweep)).length
          < prologue.length := by
      simp only [List.length_append]
      change prelude.length + loopTop.length + zeroSweep.length
        + (pre_s.length + d) - _ < _
      rw [h_prelude_len, h_loopTop_len, h_zeroSweep_len,
        h_prologue_len_eq, h_pt_s_len]
      omega
    have h_step4 :
        ((((prelude ++ loopTop) ++ zeroSweep) ++ prologue))[pos]'
            h_in_prefix4
          = prologue[pos - (((prelude ++ loopTop) ++ zeroSweep)).length]'
              h_idx_in_prologue := by
      rw [List.getElem_append_right h_pref3_le]
    rw [h_step4]
    -- Simplify the index inside prologue.
    have h_idx_eq :
        pos - (((prelude ++ loopTop) ++ zeroSweep)).length
          = pre_s.length + d := by
      simp only [List.length_append]
      rw [h_prelude_len, h_loopTop_len, h_zeroSweep_len]
      change prelude.length + loopTop.length + zeroSweep.length
        + (pre_s.length + d) - _ = _
      rw [h_prelude_len, h_loopTop_len, h_zeroSweep_len]
      omega
    have h_pre_s_plus_d_lt : pre_s.length + d < prologue.length := by
      rw [h_prologue_len_eq, h_pt_s_len]
      omega
    have h_step5 :
        prologue[pos - (((prelude ++ loopTop) ++ zeroSweep)).length]'
            h_idx_in_prologue
          = prologue[pre_s.length + d]'h_pre_s_plus_d_lt := by
      congr 1
    rw [h_step5]
    -- Substitute prologue via h_prologue_full.
    have h_pre_s_plus_d_lt_full :
        pre_s.length + d < (pre_s ++ pt_s ++ suf_s).length := by
      rw [List.length_append, List.length_append, h_pt_s_len]
      omega
    have h_step6 :
        prologue[pre_s.length + d]'h_pre_s_plus_d_lt
          = (pre_s ++ pt_s ++ suf_s)[pre_s.length + d]'
              h_pre_s_plus_d_lt_full := by
      congr 1
    rw [h_step6]
    have h_pos3_lt :
        pre_s.length + d < (pre_s ++ pt_s).length := by
      rw [List.length_append, h_pt_s_len]
      omega
    rw [List.getElem_append_left h_pos3_lt]
    have h_pos3_ge : pre_s.length ≤ pre_s.length + d := by omega
    rw [List.getElem_append_right h_pos3_ge]
    have h_d_eq : pre_s.length + d - pre_s.length = d := by omega
    have h_d_lt : pre_s.length + d - pre_s.length < pt_s.length := by
      rw [h_d_eq, h_pt_s_len]; exact hd
    have h_step7 :
        pt_s[pre_s.length + d - pre_s.length]'h_d_lt
          = pt_s[d]'(by rw [h_pt_s_len]; exact hd) := by
      congr 1
    exact h_step7
  -- Membership of pt_s[d] in rawList for the bound witness.
  have h_pt_d_in_rawList : ∀ (d : ℕ) (hd : d < 9),
      (pt_s[d]'(by rw [h_pt_s_len]; exact hd)) ∈ rawList := by
    intro d hd
    have h_mem_pt :
        pt_s[d]'(by rw [h_pt_s_len]; exact hd) ∈ pt_s :=
      List.getElem_mem _
    have h_mem_prologue :
        pt_s[d]'(by rw [h_pt_s_len]; exact hd) ∈ prologue := by
      rw [h_prologue_full]
      exact List.mem_append.mpr
        (Or.inl (List.mem_append.mpr (Or.inr h_mem_pt)))
    -- rawList = prelude ++ loopTop ++ zeroSweep ++ prologue ++ ...
    apply List.mem_append.mpr; left
    apply List.mem_append.mpr; left
    apply List.mem_append.mpr; left
    apply List.mem_append.mpr; right
    exact h_mem_prologue
  -- Per-position getElem? lookup at PC prologueBase + 9*s.val + d.
  have h_outerInstr_lookup :
      ∀ (d : ℕ) (hd : d < 9),
        outer.instrs[prologueBase + 9 * s.val + d]?
          = some (URMInstrRaw.toBounded nR
              (pt_s[d]'(by rw [h_pt_s_len]; exact hd))
              (hBoundOuter _ (h_pt_d_in_rawList d hd))) := by
    intro d hd
    have h_idx_lt_outer :
        prologueBase + 9 * s.val + d < rawList.length := by
      have h_raw_len : rawList.length
          = prelude.length + loopTop.length + zeroSweep.length
            + prologue.length + fBody.length + accUpdate.length
            + epilogue.length := by
        change (prelude ++ loopTop ++ zeroSweep ++ prologue ++ fBody
          ++ accUpdate ++ epilogue).length = _
        simp only [List.length_append]
      rw [h_raw_len, h_prelude_len, h_loopTop_len, h_zeroSweep_len,
        h_prologue_len_eq, h_pt_s_len, h_pre_s_len_eq]
      change 15 + frag_f.numRegs + 9 * s.val + d < _
      have hs : s.val < k + 1 := s.isLt
      omega
    -- Reduce via toBoundedArray_getElem?.
    change (URMInstrRaw.toBoundedArray nR rawList hBoundOuter)[
        prologueBase + 9 * s.val + d]? = _
    rw [URMInstrRaw.toBoundedArray_getElem? nR rawList hBoundOuter
        (prologueBase + 9 * s.val + d) h_idx_lt_outer]
    -- Convert the index to the canonical pos form.
    have h_pcs_eq : prologueBase + 9 * s.val + d
        = prelude.length + loopTop.length + zeroSweep.length
          + (pre_s.length + d) := by
      rw [h_prelude_len, h_loopTop_len, h_zeroSweep_len, h_pre_s_len_eq]
      change 15 + frag_f.numRegs + 9 * s.val + d = _
      omega
    have h_raw_eq :
        rawList[prologueBase + 9 * s.val + d]'h_idx_lt_outer
          = pt_s[d]'(by rw [h_pt_s_len]; exact hd) := by
      have h_step :
          rawList[prologueBase + 9 * s.val + d]'h_idx_lt_outer
            = rawList[prelude.length + loopTop.length + zeroSweep.length
                + (pre_s.length + d)]'(by rw [← h_pcs_eq]; exact h_idx_lt_outer) := by
        congr 1
      rw [h_step]
      exact h_lookup_pt d hd
    apply congrArg some
    exact URMInstrRaw.toBounded_congr nR h_raw_eq _ _
  -- Now build the preservingTransferInstrs witness using the nine
  -- concrete entries of pt_s.  Each h_inst_d follows by specialising
  -- h_outerInstr_lookup at d and matching the raw entry to the
  -- toBounded form expected by the structure.
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals (
    first
      | exact h_outerInstr_lookup 0 (by decide)
      | exact h_outerInstr_lookup 1 (by decide)
      | exact h_outerInstr_lookup 2 (by decide)
      | exact h_outerInstr_lookup 3 (by decide)
      | exact h_outerInstr_lookup 4 (by decide)
      | exact h_outerInstr_lookup 5 (by decide)
      | exact h_outerInstr_lookup 6 (by decide)
      | exact h_outerInstr_lookup 7 (by decide)
      | exact h_outerInstr_lookup 8 (by decide))

/-- Post-state predicate at the end of one iteration's prologue
(PC = `15 + frag_f.numRegs + 9 * (k + 1)`, the start of f's body).
Strengthens `compileFrag_bsum_phase_i0_post` by recording that f's
input slots now hold `Fin.cons i.val (Fin.tail v)`, the iteration's
input vector for f; all other clauses (`zReg_zero`, `outer_inputs`,
`vX_eq`, `vI_eq`, `tmp1_zero`, `tmp2_zero`, `acc_eq`) carry over
verbatim from `compileFrag_bsum_phase_i0_post @ i`. The `f_other_zero`
clause records that f's reindexed block outside the now-filled input
slots remains 0 (preserved from phase_i0's `fBody_zero` since the
prologue's preservingTransfer touches only the input-slot destinations
and `tmp1`). -/
private structure compileFrag_bsum_phase_i1_post
    {k : ℕ}
    (frag_f : CompiledFragment (k + 1))
    (f : ERMor1 (k + 1))
    (v : Fin (k + 1) → ℕ)
    (i : Fin (v 0))
    (s : URMState (compileFrag_bsum frag_f).toURMProgram)
    : Prop where
  /-- `i.val < v 0`, packaged for downstream consumers. -/
  hi_lt : i.val < v 0 := i.isLt
  /-- PC sits one past the per-iteration prologue, at the start of
  f's body. -/
  pc_eq : s.pc = 15 + frag_f.numRegs + 9 * (k + 1)
  /-- `V_z` (register 0) holds `0`. -/
  zReg_zero : s.regs ⟨0, (compileFrag_bsum frag_f).numRegs_pos⟩ = 0
  /-- Outer input slots `2..k+2` hold the input vector. -/
  outer_inputs : ∀ (j : Fin (k + 1)),
    s.regs ⟨2 + j.val, by
      have hj : j.val < k + 1 := j.isLt
      change 2 + j.val < k + 7 + frag_f.numRegs
      have : 0 < frag_f.numRegs := frag_f.numRegs_pos
      omega⟩ = v j
  /-- `V_x` (register `k + 3`) still holds `v 0 - i.val - 1`. -/
  vX_eq : s.regs ⟨k + 3, by
    change k + 3 < k + 7 + frag_f.numRegs
    have : 0 < frag_f.numRegs := frag_f.numRegs_pos
    omega⟩ = v 0 - i.val - 1
  /-- `V_i` (register `k + 4`) still holds the pre-iteration counter
  `i.val`. -/
  vI_eq : s.regs ⟨k + 4, by
    change k + 4 < k + 7 + frag_f.numRegs
    have : 0 < frag_f.numRegs := frag_f.numRegs_pos
    omega⟩ = i.val
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
  /-- The accumulator (register 1) still holds the pre-iteration
  partial sum. -/
  acc_eq : s.regs ⟨1, by
    change 1 < k + 7 + frag_f.numRegs
    have : 0 < frag_f.numRegs := frag_f.numRegs_pos
    omega⟩
      = natBSum i.val (fun j => f.interp (Fin.cons j (Fin.tail v)))
  /-- f's input slots hold the iteration's input vector
  `Fin.cons i.val (Fin.tail v)`. -/
  f_inputs : ∀ (j : Fin (k + 1)),
    s.regs ⟨(k + 7) + (frag_f.inputRegs j).val, by
      have hI : (frag_f.inputRegs j).val < frag_f.numRegs :=
        (frag_f.inputRegs j).isLt
      change (k + 7) + (frag_f.inputRegs j).val
        < k + 7 + frag_f.numRegs
      omega⟩ = Fin.cons i.val (Fin.tail v) j
  /-- f's reindexed block remains `0` outside the input slots. -/
  f_other_zero : ∀ (r : Fin frag_f.numRegs),
    (∀ j : Fin (k + 1), r ≠ frag_f.inputRegs j) →
    s.regs ⟨(k + 7) + r.val, by
      have hr : r.val < frag_f.numRegs := r.isLt
      change (k + 7) + r.val < k + 7 + frag_f.numRegs
      omega⟩ = 0

/-- Phase i.1 preservation lemma: from
`compileFrag_bsum_phase_i0_post @ i`, running for `T0 :=
9 * vPrefixSum (Fin.cons i.val (Fin.tail v)) (k + 1) + 2 * (k + 1)`
further steps (the per-iteration prologue) lands the state in
`compileFrag_bsum_phase_i1_post @ i`. The accompanying strict PC
bound states that during these `T0` steps the intermediate PC stays
strictly less than `15 + frag_f.numRegs + 9 * (k + 1)`. -/
private theorem compileFrag_bsum_partial_phase_i1
    {k : ℕ}
    (f : ERMor1 (k + 1))
    (v : Fin (k + 1) → ℕ)
    (i : Fin (v 0))
    (sPre : URMState
      (compileFrag_bsum (compileERFrag f)).toURMProgram)
    (h_i0 : compileFrag_bsum_phase_i0_post (compileERFrag f) f v i sPre) :
    let T0 : ℕ := 9 * vPrefixSum (Fin.cons i.val (Fin.tail v)) (k + 1)
      + 2 * (k + 1)
    compileFrag_bsum_phase_i1_post (compileERFrag f) f v i
        (URMState.runFor
          (compileFrag_bsum (compileERFrag f)).toURMProgram sPre T0)
      ∧ (∀ k' < T0,
        (URMState.runFor (compileFrag_bsum (compileERFrag f)).toURMProgram
          sPre k').pc
          < 15 + (compileERFrag f).numRegs + 9 * (k + 1)) := by
  let frag_f : CompiledFragment (k + 1) := compileERFrag f
  let outerFrag : CompiledFragment (k + 1) := compileFrag_bsum frag_f
  let P : URMProgram (k + 1) := outerFrag.toURMProgram
  let v_iter : Fin (k + 1) → ℕ := Fin.cons i.val (Fin.tail v)
  let pcBase : ℕ := 15 + frag_f.numRegs
  change
    compileFrag_bsum_phase_i1_post frag_f f v i
        (URMState.runFor P sPre
          (9 * vPrefixSum v_iter (k + 1) + 2 * (k + 1)))
      ∧ (∀ k' < 9 * vPrefixSum v_iter (k + 1) + 2 * (k + 1),
        (URMState.runFor P sPre k').pc < pcBase + 9 * (k + 1))
  have h_numRegs_eq : P.numRegs = (k + 7) + frag_f.numRegs := rfl
  have h_numRegs_pos : 0 < P.numRegs := outerFrag.numRegs_pos
  -- Bound proofs.
  have h_src_lt : ∀ (j : Fin (k + 1)),
      bsum_prologueSrc k j < P.numRegs := by
    intro j
    rw [h_numRegs_eq]
    have h_pos : 0 < frag_f.numRegs := frag_f.numRegs_pos
    have hj : j.val < k + 1 := j.isLt
    simp only [bsum_prologueSrc]
    split <;> omega
  have h_dst_lt : ∀ (j : Fin (k + 1)),
      (k + 7) + (frag_f.inputRegs j).val < P.numRegs := by
    intro j
    have hI : (frag_f.inputRegs j).val < frag_f.numRegs :=
      (frag_f.inputRegs j).isLt
    rw [h_numRegs_eq]
    omega
  have h_tmp_lt : k + 5 < P.numRegs := by
    rw [h_numRegs_eq]
    have h_pos : 0 < frag_f.numRegs := frag_f.numRegs_pos
    omega
  -- Concrete register packs.
  let zReg : Fin P.numRegs := ⟨0, h_numRegs_pos⟩
  let tmpFin : Fin P.numRegs := ⟨k + 5, h_tmp_lt⟩
  let srcs : Fin (k + 1) → Fin P.numRegs :=
    fun j => ⟨bsum_prologueSrc k j, h_src_lt j⟩
  let dsts : Fin (k + 1) → Fin P.numRegs :=
    fun j => ⟨(k + 7) + (frag_f.inputRegs j).val, h_dst_lt j⟩
  -- Disjointness bundle.
  have h_disj : inputCopies_disj P zReg tmpFin srcs dsts := by
    refine
      { z_src := ?_, z_dst := ?_, z_tmp := ?_,
        src_dst := ?_, src_tmp := ?_, dst_tmp := ?_,
        src_inj := ?_, dst_inj := ?_, src_dst_cross := ?_ }
    · intro j hh
      have h_val : (0 : ℕ) = bsum_prologueSrc k j := congrArg Fin.val hh
      simp only [bsum_prologueSrc] at h_val
      split at h_val <;> omega
    · intro j hh
      have h_val : (0 : ℕ) = (k + 7) + (frag_f.inputRegs j).val :=
        congrArg Fin.val hh
      omega
    · intro hh
      have h_val : (0 : ℕ) = k + 5 := congrArg Fin.val hh
      omega
    · intro j hh
      have h_val : bsum_prologueSrc k j = (k + 7) + (frag_f.inputRegs j).val :=
        congrArg Fin.val hh
      simp only [bsum_prologueSrc] at h_val
      have hI : (frag_f.inputRegs j).val < frag_f.numRegs :=
        (frag_f.inputRegs j).isLt
      have hj : j.val < k + 1 := j.isLt
      split at h_val <;> omega
    · intro j hh
      have h_val : bsum_prologueSrc k j = k + 5 := congrArg Fin.val hh
      simp only [bsum_prologueSrc] at h_val
      have hj : j.val < k + 1 := j.isLt
      split at h_val <;> omega
    · intro j hh
      have h_val : (k + 7) + (frag_f.inputRegs j).val = k + 5 :=
        congrArg Fin.val hh
      omega
    · intro j₁ j₂ hne hh
      have h_val : bsum_prologueSrc k j₁ = bsum_prologueSrc k j₂ :=
        congrArg Fin.val hh
      simp only [bsum_prologueSrc] at h_val
      have hj1 : j₁.val < k + 1 := j₁.isLt
      have hj2 : j₂.val < k + 1 := j₂.isLt
      -- Case split on whether each is 0; bsum_prologueSrc is injective.
      have h_eq_val : j₁.val = j₂.val := by
        split at h_val <;> split at h_val <;> omega
      exact hne (Fin.ext h_eq_val)
    · intro j₁ j₂ hne hh
      have h_val :
          (k + 7) + (frag_f.inputRegs j₁).val
            = (k + 7) + (frag_f.inputRegs j₂).val :=
        congrArg Fin.val hh
      have hI_eq : (frag_f.inputRegs j₁).val
          = (frag_f.inputRegs j₂).val := by omega
      have hI_eq' : frag_f.inputRegs j₁ = frag_f.inputRegs j₂ :=
        Fin.ext hI_eq
      exact hne (frag_f.inputRegs_inj hI_eq')
    · intro j₁ j₂ hh
      have h_val : bsum_prologueSrc k j₁
          = (k + 7) + (frag_f.inputRegs j₂).val :=
        congrArg Fin.val hh
      simp only [bsum_prologueSrc] at h_val
      have hI : (frag_f.inputRegs j₂).val < frag_f.numRegs :=
        (frag_f.inputRegs j₂).isLt
      have hj1 : j₁.val < k + 1 := j₁.isLt
      split at h_val <;> omega
  -- Instruction-presence bundle from the helper.
  have h_H : ∀ (j : Fin (k + 1)),
      preservingTransferInstrs P (pcBase + 9 * j.val)
        (srcs j) (dsts j) tmpFin zReg := by
    intro j
    obtain ⟨_, _, _, _, hPT⟩ :=
      compileFrag_bsum_prologueBlock_instr_at frag_f j
    exact hPT
  -- Pre-state hypotheses from `compileFrag_bsum_phase_i0_post`.
  have h_s_pc : sPre.pc = pcBase := h_i0.pc_eq
  have h_s_z : sPre.regs zReg = 0 := h_i0.zReg_zero
  have h_s_tmp : sPre.regs tmpFin = 0 := h_i0.tmp1_zero
  -- Source-register values: case-split on `j.val`.
  have h_s_srcs : ∀ (j : Fin (k + 1)),
      sPre.regs (srcs j) = v_iter j := by
    intro j
    rcases Nat.eq_zero_or_pos j.val with hj0 | hjpos
    · -- j.val = 0: srcs 0 = ⟨k + 4, _⟩; sPre value = i.val.
      have h_kp1_pos : 0 < k + 1 := Nat.succ_pos _
      have h_j_eq : j = ⟨0, h_kp1_pos⟩ := Fin.ext hj0
      rw [h_j_eq]
      have h_srcs_eq :
          srcs ⟨0, h_kp1_pos⟩ = ⟨k + 4, by
            rw [h_numRegs_eq]
            have : 0 < frag_f.numRegs := frag_f.numRegs_pos; omega⟩ := by
        apply Fin.ext
        change bsum_prologueSrc k ⟨0, h_kp1_pos⟩ = k + 4
        simp only [bsum_prologueSrc, if_true]
      rw [h_srcs_eq]
      have h_v_iter_eq : v_iter ⟨0, h_kp1_pos⟩ = i.val := by
        change Fin.cons i.val (Fin.tail v) ⟨0, h_kp1_pos⟩ = i.val
        have h_fin0 : (⟨0, h_kp1_pos⟩ : Fin (k + 1)) = 0 := Fin.ext rfl
        rw [h_fin0, Fin.cons_zero]
      rw [h_v_iter_eq]
      exact h_i0.vI_eq
    · -- j.val = s + 1: srcs ⟨s+1, _⟩ source value = v ⟨s+1, _⟩.
      set s' : ℕ := j.val - 1 with hs'_def
      have h_jval_eq : j.val = s' + 1 := by omega
      have hj : s' + 1 < k + 1 := h_jval_eq ▸ j.isLt
      have hs' : s' < k := Nat.lt_of_succ_lt_succ hj
      have h_j_eq : j = ⟨s' + 1, hj⟩ := Fin.ext h_jval_eq
      rw [h_j_eq]
      have h_srcs_eq :
          srcs ⟨s' + 1, hj⟩ = ⟨2 + (s' + 1), by
            rw [h_numRegs_eq]
            have : 0 < frag_f.numRegs := frag_f.numRegs_pos; omega⟩ := by
        apply Fin.ext
        change bsum_prologueSrc k ⟨s' + 1, hj⟩ = 2 + (s' + 1)
        simp only [bsum_prologueSrc]
        split <;> omega
      rw [h_srcs_eq]
      have h_v_iter_eq :
          v_iter ⟨s' + 1, hj⟩ = v ⟨s' + 1, hj⟩ := by
        change Fin.cons i.val (Fin.tail v) ⟨s' + 1, hj⟩ = v ⟨s' + 1, hj⟩
        have h_eq : (⟨s' + 1, hj⟩ : Fin (k + 1))
            = Fin.succ ⟨s', hs'⟩ := Fin.ext rfl
        rw [h_eq, Fin.cons_succ]
        change Fin.tail v ⟨s', hs'⟩ = _
        rfl
      rw [h_v_iter_eq]
      exact h_i0.outer_inputs ⟨s' + 1, hj⟩
  -- Destination registers are all zero (from phase_i0 fBody_zero).
  have h_s_dsts : ∀ (j : Fin (k + 1)), sPre.regs (dsts j) = 0 := by
    intro j
    exact h_i0.fBody_zero (frag_f.inputRegs j)
  -- Apply the prologue correctness lemma.
  obtain ⟨h_pc_post, h_z_post, h_tmp_post, h_dsts_post,
          h_srcs_post, h_oth_post⟩ :=
    compileFrag_bsum_prologue_correct P pcBase zReg tmpFin srcs dsts
      h_disj h_H v_iter sPre h_s_pc h_s_z h_s_tmp h_s_srcs h_s_dsts
  refine ⟨?_, ?_⟩
  · -- Discharge each `compileFrag_bsum_phase_i1_post` clause.
    refine
      { hi_lt := i.isLt
        pc_eq := ?_
        zReg_zero := ?_
        outer_inputs := ?_
        vX_eq := ?_
        vI_eq := ?_
        tmp1_zero := ?_
        tmp2_zero := ?_
        acc_eq := ?_
        f_inputs := ?_
        f_other_zero := ?_ }
    · -- pc_eq.
      exact h_pc_post
    · -- zReg_zero.
      have h_idx_eq : (⟨0, (compileFrag_bsum frag_f).numRegs_pos⟩
            : Fin P.numRegs) = zReg := rfl
      rw [h_idx_eq]; exact h_z_post
    · -- outer_inputs preserved via h_oth_post.
      intro j
      let r : Fin P.numRegs := ⟨2 + j.val, by
        have hj : j.val < k + 1 := j.isLt
        rw [h_numRegs_eq]
        have : 0 < frag_f.numRegs := frag_f.numRegs_pos
        omega⟩
      have h_ne_dsts : ∀ (j' : Fin (k + 1)), r ≠ dsts j' := by
        intro j' hh
        have h_val : 2 + j.val = (k + 7) + (frag_f.inputRegs j').val :=
          congrArg Fin.val hh
        have hj : j.val < k + 1 := j.isLt
        omega
      have h_ne_tmp : r ≠ tmpFin := by
        intro hh
        have h_val : 2 + j.val = k + 5 := congrArg Fin.val hh
        have hj : j.val < k + 1 := j.isLt
        omega
      have h_oth := h_oth_post r h_ne_dsts h_ne_tmp
      have h_idx_eq :
          (⟨2 + j.val, by
            have hj : j.val < k + 1 := j.isLt
            change 2 + j.val < k + 7 + frag_f.numRegs
            have : 0 < frag_f.numRegs := frag_f.numRegs_pos
            omega⟩ : Fin P.numRegs) = r := Fin.ext rfl
      rw [h_idx_eq, h_oth]
      exact h_i0.outer_inputs j
    · -- vX_eq.
      let r : Fin P.numRegs := ⟨k + 3, by
        rw [h_numRegs_eq]
        have : 0 < frag_f.numRegs := frag_f.numRegs_pos; omega⟩
      have h_ne_dsts : ∀ (j' : Fin (k + 1)), r ≠ dsts j' := by
        intro j' hh
        have h_val : k + 3 = (k + 7) + (frag_f.inputRegs j').val :=
          congrArg Fin.val hh
        omega
      have h_ne_tmp : r ≠ tmpFin := by
        intro hh
        have h_val : k + 3 = k + 5 := congrArg Fin.val hh
        omega
      have h_oth := h_oth_post r h_ne_dsts h_ne_tmp
      have h_idx_eq :
          (⟨k + 3, by
            change k + 3 < k + 7 + frag_f.numRegs
            have : 0 < frag_f.numRegs := frag_f.numRegs_pos
            omega⟩ : Fin P.numRegs) = r := Fin.ext rfl
      rw [h_idx_eq, h_oth]
      exact h_i0.vX_eq
    · -- vI_eq.
      let r : Fin P.numRegs := ⟨k + 4, by
        rw [h_numRegs_eq]
        have : 0 < frag_f.numRegs := frag_f.numRegs_pos; omega⟩
      have h_ne_dsts : ∀ (j' : Fin (k + 1)), r ≠ dsts j' := by
        intro j' hh
        have h_val : k + 4 = (k + 7) + (frag_f.inputRegs j').val :=
          congrArg Fin.val hh
        omega
      have h_ne_tmp : r ≠ tmpFin := by
        intro hh
        have h_val : k + 4 = k + 5 := congrArg Fin.val hh
        omega
      have h_oth := h_oth_post r h_ne_dsts h_ne_tmp
      have h_idx_eq :
          (⟨k + 4, by
            change k + 4 < k + 7 + frag_f.numRegs
            have : 0 < frag_f.numRegs := frag_f.numRegs_pos
            omega⟩ : Fin P.numRegs) = r := Fin.ext rfl
      rw [h_idx_eq, h_oth]
      exact h_i0.vI_eq
    · -- tmp1_zero.
      have h_idx_eq :
          (⟨k + 5, by
            change k + 5 < k + 7 + frag_f.numRegs
            have : 0 < frag_f.numRegs := frag_f.numRegs_pos
            omega⟩ : Fin P.numRegs) = tmpFin := Fin.ext rfl
      rw [h_idx_eq]; exact h_tmp_post
    · -- tmp2_zero preserved via h_oth_post.
      let r : Fin P.numRegs := ⟨k + 6, by
        rw [h_numRegs_eq]
        have : 0 < frag_f.numRegs := frag_f.numRegs_pos; omega⟩
      have h_ne_dsts : ∀ (j' : Fin (k + 1)), r ≠ dsts j' := by
        intro j' hh
        have h_val : k + 6 = (k + 7) + (frag_f.inputRegs j').val :=
          congrArg Fin.val hh
        omega
      have h_ne_tmp : r ≠ tmpFin := by
        intro hh
        have h_val : k + 6 = k + 5 := congrArg Fin.val hh
        omega
      have h_oth := h_oth_post r h_ne_dsts h_ne_tmp
      have h_idx_eq :
          (⟨k + 6, by
            change k + 6 < k + 7 + frag_f.numRegs
            have : 0 < frag_f.numRegs := frag_f.numRegs_pos
            omega⟩ : Fin P.numRegs) = r := Fin.ext rfl
      rw [h_idx_eq, h_oth]
      exact h_i0.tmp2_zero
    · -- acc_eq preserved via h_oth_post.
      let r : Fin P.numRegs := ⟨1, by
        rw [h_numRegs_eq]
        have : 0 < frag_f.numRegs := frag_f.numRegs_pos; omega⟩
      have h_ne_dsts : ∀ (j' : Fin (k + 1)), r ≠ dsts j' := by
        intro j' hh
        have h_val : (1 : ℕ) = (k + 7) + (frag_f.inputRegs j').val :=
          congrArg Fin.val hh
        omega
      have h_ne_tmp : r ≠ tmpFin := by
        intro hh
        have h_val : (1 : ℕ) = k + 5 := congrArg Fin.val hh
        omega
      have h_oth := h_oth_post r h_ne_dsts h_ne_tmp
      have h_idx_eq :
          (⟨1, by
            change 1 < k + 7 + frag_f.numRegs
            have : 0 < frag_f.numRegs := frag_f.numRegs_pos
            omega⟩ : Fin P.numRegs) = r := Fin.ext rfl
      rw [h_idx_eq, h_oth]
      exact h_i0.acc_eq
    · -- f_inputs: dsts j filled with v_iter j.
      intro j
      have h_idx_eq :
          (⟨(k + 7) + (frag_f.inputRegs j).val, by
            have hI : (frag_f.inputRegs j).val < frag_f.numRegs :=
              (frag_f.inputRegs j).isLt
            change (k + 7) + (frag_f.inputRegs j).val
              < k + 7 + frag_f.numRegs
            omega⟩ : Fin P.numRegs) = dsts j := Fin.ext rfl
      rw [h_idx_eq]
      exact h_dsts_post j
    · -- f_other_zero: r outside the filled input slots stays at 0
      -- via h_oth_post applied to (k+7)+r.val.
      intro r h_not_input
      let R : Fin P.numRegs := ⟨(k + 7) + r.val, by
        have hr : r.val < frag_f.numRegs := r.isLt
        rw [h_numRegs_eq]; omega⟩
      have h_ne_dsts : ∀ (j' : Fin (k + 1)), R ≠ dsts j' := by
        intro j' hh
        have h_val : (k + 7) + r.val
            = (k + 7) + (frag_f.inputRegs j').val :=
          congrArg Fin.val hh
        have h_r_eq : r.val = (frag_f.inputRegs j').val := by omega
        exact h_not_input j' (Fin.ext h_r_eq)
      have h_ne_tmp : R ≠ tmpFin := by
        intro hh
        have h_val : (k + 7) + r.val = k + 5 := congrArg Fin.val hh
        omega
      have h_oth := h_oth_post R h_ne_dsts h_ne_tmp
      have h_idx_eq :
          (⟨(k + 7) + r.val, by
            have hr : r.val < frag_f.numRegs := r.isLt
            change (k + 7) + r.val < k + 7 + frag_f.numRegs
            omega⟩ : Fin P.numRegs) = R := Fin.ext rfl
      rw [h_idx_eq, h_oth]
      exact h_i0.fBody_zero r
  · -- Strict PC bound during the T0 prologue steps.
    intro k' hk'
    have h_bound :=
      compileFrag_bsum_prologue_pc_strict_bound P pcBase zReg tmpFin
        srcs dsts h_disj h_H v_iter sPre h_s_pc h_s_z h_s_tmp
        h_s_srcs h_s_dsts k' hk'
    exact h_bound

/-- Post-state predicate for Phase i.2 of one bsum iteration: the state
immediately after f's reindexed body has executed to its trailing
`stopR`. PC sits one past the prologue at
`15 + frag_f.numRegs + 9 * (k + 1) + (frag_f.instrs.size - 1)`, the
first instruction of the per-iteration accumulator-update transferLoop.
The `f_output` clause records that f's reindexed output register holds
`f.interp (Fin.cons i.val (Fin.tail v))`. All outer-scaffolding clauses
(`hi_lt`, `zReg_zero`, `outer_inputs`, `vX_eq`, `vI_eq`, `tmp1_zero`,
`tmp2_zero`, `acc_eq`) carry over verbatim from
`compileFrag_bsum_phase_i1_post @ i`, since every outer-scaffolding
register lives at an index `< k + 7` outside f's reindexed block
`[k + 7, k + 7 + frag_f.numRegs)`. -/
private structure compileFrag_bsum_phase_i2_post
    {k : ℕ}
    (frag_f : CompiledFragment (k + 1))
    (f : ERMor1 (k + 1))
    (v : Fin (k + 1) → ℕ)
    (i : Fin (v 0))
    (s : URMState (compileFrag_bsum frag_f).toURMProgram)
    : Prop where
  /-- `i.val < v 0`, packaged for downstream consumers. -/
  hi_lt : i.val < v 0 := i.isLt
  /-- PC sits one past f's reindexed body, at the start of the
  per-iteration accumulator-update transferLoop. -/
  pc_eq : s.pc = 15 + frag_f.numRegs + 9 * (k + 1)
                  + (frag_f.instrs.size - 1)
  /-- `V_z` (register 0) holds `0`. -/
  zReg_zero : s.regs ⟨0, (compileFrag_bsum frag_f).numRegs_pos⟩ = 0
  /-- Outer input slots `2..k+2` hold the input vector. -/
  outer_inputs : ∀ (j : Fin (k + 1)),
    s.regs ⟨2 + j.val, by
      have hj : j.val < k + 1 := j.isLt
      change 2 + j.val < k + 7 + frag_f.numRegs
      have : 0 < frag_f.numRegs := frag_f.numRegs_pos
      omega⟩ = v j
  /-- `V_x` (register `k + 3`) still holds `v 0 - i.val - 1`. -/
  vX_eq : s.regs ⟨k + 3, by
    change k + 3 < k + 7 + frag_f.numRegs
    have : 0 < frag_f.numRegs := frag_f.numRegs_pos
    omega⟩ = v 0 - i.val - 1
  /-- `V_i` (register `k + 4`) still holds the pre-iteration counter
  `i.val`. -/
  vI_eq : s.regs ⟨k + 4, by
    change k + 4 < k + 7 + frag_f.numRegs
    have : 0 < frag_f.numRegs := frag_f.numRegs_pos
    omega⟩ = i.val
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
  /-- The accumulator (register 1) still holds the pre-iteration
  partial sum. -/
  acc_eq : s.regs ⟨1, by
    change 1 < k + 7 + frag_f.numRegs
    have : 0 < frag_f.numRegs := frag_f.numRegs_pos
    omega⟩
      = natBSum i.val (fun j => f.interp (Fin.cons j (Fin.tail v)))
  /-- f's reindexed output register holds
  `f.interp (Fin.cons i.val (Fin.tail v))`, the iteration's f-value. -/
  f_output : s.regs ⟨(k + 7) + frag_f.outputReg.val, by
    have hO : frag_f.outputReg.val < frag_f.numRegs :=
      frag_f.outputReg.isLt
    change (k + 7) + frag_f.outputReg.val < k + 7 + frag_f.numRegs
    omega⟩ = f.interp (Fin.cons i.val (Fin.tail v))

/-- Phase i.2 preservation lemma: from `compileFrag_bsum_phase_i1_post
@ i` plus the structural IH on `f` instantiated at the iteration input
vector `Fin.cons i.val (Fin.tail v)`, there exists some
`T0 ≤ compileER_runtime f (Fin.cons i.val (Fin.tail v))` such that
running f's reindexed body for `T0` steps lands the state in
`compileFrag_bsum_phase_i2_post @ i`. The accompanying strict PC bound
states that during these `T0` steps the intermediate PC stays
strictly less than `15 + frag_f.numRegs + 9 * (k + 1)
+ (frag_f.instrs.size - 1)`. The proof instantiates
`ProgramEmbedsFragment_compileFrag_bsum_fBody` and packages
`compileFrag_bsum_phase_i1_post`'s `f_inputs` and `f_other_zero`
clauses into a `StateEmbedsFrag` witness matching
`URMState.init (compileER f) (Fin.cons i.val (Fin.tail v))`; the IH
then transports through `stateEmbedsFrag_runFor`, and the outer
scaffolding's preservation through
`stateEmbedsFrag_runFor_outside_preserved`. -/
private theorem compileFrag_bsum_partial_phase_i2
    {k : ℕ}
    (f : ERMor1 (k + 1))
    (ih_f : ∀ (v' : Fin (k + 1) → ℕ),
      ∃ T0 : ℕ,
        T0 ≤ compileER_runtime f v' ∧
        (URMState.runFor (compileER f)
              (URMState.init (compileER f) v') T0).pc
            = (compileER f).instrs.size - 1 ∧
        (URMState.runFor (compileER f)
              (URMState.init (compileER f) v') T0).regs
            (compileER f).outputReg
          = f.interp v' ∧
        (∀ k' < T0,
          (URMState.runFor (compileER f)
              (URMState.init (compileER f) v') k').pc
            < (compileER f).instrs.size - 1))
    (v : Fin (k + 1) → ℕ)
    (i : Fin (v 0))
    (sPre : URMState
      (compileFrag_bsum (compileERFrag f)).toURMProgram)
    (h_i1 : compileFrag_bsum_phase_i1_post (compileERFrag f) f v i sPre) :
    ∃ T0 : ℕ,
      T0 ≤ compileER_runtime f (Fin.cons i.val (Fin.tail v)) ∧
      compileFrag_bsum_phase_i2_post (compileERFrag f) f v i
        (URMState.runFor
          (compileFrag_bsum (compileERFrag f)).toURMProgram sPre T0)
      ∧ (∀ k' < T0,
        (URMState.runFor
          (compileFrag_bsum (compileERFrag f)).toURMProgram sPre k').pc
          < 15 + (compileERFrag f).numRegs + 9 * (k + 1)
            + ((compileERFrag f).instrs.size - 1)) := by
  let frag_f : CompiledFragment (k + 1) := compileERFrag f
  let outerFrag : CompiledFragment (k + 1) := compileFrag_bsum frag_f
  let P : URMProgram (k + 1) := outerFrag.toURMProgram
  let v_iter : Fin (k + 1) → ℕ := Fin.cons i.val (Fin.tail v)
  let fBase : ℕ := k + 7
  let pcBase : ℕ := 15 + frag_f.numRegs + 9 * (k + 1)
  let L : ℕ := frag_f.instrs.size - 1
  have h_numRegs_eq : P.numRegs = (k + 7) + frag_f.numRegs := rfl
  have h_numRegs_pos : 0 < P.numRegs := outerFrag.numRegs_pos
  -- Program embedding of f's reindexed body inside the outer.
  have h_emb_prog :
      ProgramEmbedsFragment P frag_f fBase pcBase L :=
    ProgramEmbedsFragment_compileFrag_bsum_fBody frag_f
  -- Pre-state hypotheses from `compileFrag_bsum_phase_i1_post`.
  have h_pc_pre : sPre.pc = pcBase := h_i1.pc_eq
  -- The init state of f's program at the iteration input vector.
  -- Inline (no `let`) to avoid blocking `URMState.init`'s reduction.
  -- Pre-state registers inside f's block match
  -- `(URMState.init frag_f.toURMProgram v_iter).regs`.
  have h_pre_regs_in :
      ∀ (r : Fin frag_f.numRegs),
        sPre.regs ⟨fBase + r.val, by
          have hr : r.val < frag_f.numRegs := r.isLt
          rw [h_numRegs_eq]; omega⟩
          = (URMState.init frag_f.toURMProgram v_iter).regs r := by
    intro r
    -- Reduce RHS via `URMState.init`'s definitional unfolding,
    -- then beta-reduce the struct projection.
    unfold URMState.init
    simp only []
    cases hFind :
        (List.finRange (k + 1)).find?
          (fun j => decide (frag_f.inputRegs j = r)) with
    | none =>
      have h_not_input : ∀ j : Fin (k + 1), r ≠ frag_f.inputRegs j := by
        intro j hj
        have h_mem : j ∈ List.finRange (k + 1) := List.mem_finRange j
        have h_dec :
            decide (frag_f.inputRegs j = r) = true :=
          decide_eq_true hj.symm
        have h_ex := List.find?_eq_none.mp hFind j h_mem
        rw [h_dec] at h_ex
        exact absurd h_ex (by decide)
      exact h_i1.f_other_zero r h_not_input
    | some j =>
      have h_eq : frag_f.inputRegs j = r := by
        have h_some := List.find?_some hFind
        have : decide (frag_f.inputRegs j = r) = true := h_some
        exact of_decide_eq_true this
      have h_inputs := h_i1.f_inputs j
      have h_idx_eq :
          (⟨fBase + (frag_f.inputRegs j).val, by
            have hI : (frag_f.inputRegs j).val < frag_f.numRegs :=
              (frag_f.inputRegs j).isLt
            change (k + 7) + (frag_f.inputRegs j).val
              < k + 7 + frag_f.numRegs
            omega⟩ : Fin P.numRegs)
            = ⟨fBase + r.val, by
              have hr : r.val < frag_f.numRegs := r.isLt
              rw [h_numRegs_eq]; omega⟩ := by
        apply Fin.ext
        change fBase + (frag_f.inputRegs j).val = fBase + r.val
        omega
      rw [h_idx_eq] at h_inputs
      exact h_inputs
  -- Now name the init state via `let` (after the regs-equation is
  -- proven; `let` would block `URMState.init`'s reduction otherwise).
  let f_init : URMState frag_f.toURMProgram :=
    URMState.init frag_f.toURMProgram v_iter
  -- State embedding at the pre-state.
  have h_state_emb :
      StateEmbedsFrag sPre f_init fBase pcBase h_emb_prog.hReg := by
    refine ⟨?_, ?_⟩
    · change sPre.pc = pcBase + 0
      exact h_pc_pre.trans (Nat.add_zero _).symm
    · intro j hj
      exact h_pre_regs_in ⟨j, hj⟩
  -- Instantiate the IH at the iteration input vector. `compileER f`
  -- and `frag_f.toURMProgram` are definitionally equal; recast the
  -- IH into `frag_f.toURMProgram` form for use with the embedding.
  have ih_frag : ∃ T0 : ℕ,
      T0 ≤ compileER_runtime f v_iter ∧
      (URMState.runFor frag_f.toURMProgram f_init T0).pc
          = frag_f.instrs.size - 1 ∧
      (URMState.runFor frag_f.toURMProgram f_init T0).regs
          frag_f.outputReg = f.interp v_iter ∧
      (∀ k' < T0,
        (URMState.runFor frag_f.toURMProgram f_init k').pc
          < frag_f.instrs.size - 1) := ih_f v_iter
  obtain ⟨T0, hT0_le, h_pc_inner, h_out_inner, h_f_strict⟩ := ih_frag
  -- State embedding after T0 steps.
  have h_emb_after :
      StateEmbedsFrag (URMState.runFor P sPre T0)
          (URMState.runFor frag_f.toURMProgram f_init T0)
          fBase pcBase h_emb_prog.hReg :=
    stateEmbedsFrag_runFor P frag_f fBase pcBase L
      h_emb_prog sPre f_init h_state_emb T0 h_f_strict
  obtain ⟨h_pc_after, h_regs_after⟩ := h_emb_after
  -- Outside-the-block register preservation after T0 steps.
  have h_outside_preserved :
      ∀ (r : Fin P.numRegs),
        r.val < fBase ∨ fBase + frag_f.numRegs ≤ r.val →
        (URMState.runFor P sPre T0).regs r = sPre.regs r := by
    intro r h_out
    exact stateEmbedsFrag_runFor_outside_preserved P frag_f
      sPre f_init fBase pcBase L h_emb_prog h_state_emb T0
      h_f_strict r h_out
  refine ⟨T0, hT0_le, ?_, ?_⟩
  · -- Discharge each `compileFrag_bsum_phase_i2_post` clause.
    refine
      { hi_lt := i.isLt
        pc_eq := ?_
        zReg_zero := ?_
        outer_inputs := ?_
        vX_eq := ?_
        vI_eq := ?_
        tmp1_zero := ?_
        tmp2_zero := ?_
        acc_eq := ?_
        f_output := ?_ }
    · -- pc_eq: PC after T0 = pcBase + (frag_f.instrs.size - 1).
      rw [h_pc_after, h_pc_inner]
    · -- zReg_zero: register 0 is outside f's block (0 < k + 7).
      let z : Fin P.numRegs := ⟨0, h_numRegs_pos⟩
      have h_out : z.val < fBase ∨ fBase + frag_f.numRegs ≤ z.val := by
        left; change 0 < k + 7; omega
      have h_pres := h_outside_preserved z h_out
      have h_idx_eq :
          (⟨0, (compileFrag_bsum frag_f).numRegs_pos⟩ : Fin P.numRegs)
            = z := Fin.ext rfl
      rw [h_idx_eq, h_pres]; exact h_i1.zReg_zero
    · -- outer_inputs: each `2 + j.val < k + 7` (since j.val < k + 1).
      intro j
      have hj : j.val < k + 1 := j.isLt
      let r : Fin P.numRegs := ⟨2 + j.val, by
        rw [h_numRegs_eq]
        have : 0 < frag_f.numRegs := frag_f.numRegs_pos
        omega⟩
      have h_out : r.val < fBase ∨ fBase + frag_f.numRegs ≤ r.val := by
        left; change 2 + j.val < k + 7; omega
      have h_pres := h_outside_preserved r h_out
      have h_idx_eq :
          (⟨2 + j.val, by
            change 2 + j.val < k + 7 + frag_f.numRegs
            have : 0 < frag_f.numRegs := frag_f.numRegs_pos
            omega⟩ : Fin P.numRegs) = r := Fin.ext rfl
      rw [h_idx_eq, h_pres]; exact h_i1.outer_inputs j
    · -- vX_eq: register `k + 3 < k + 7`.
      let r : Fin P.numRegs := ⟨k + 3, by
        rw [h_numRegs_eq]
        have : 0 < frag_f.numRegs := frag_f.numRegs_pos; omega⟩
      have h_out : r.val < fBase ∨ fBase + frag_f.numRegs ≤ r.val := by
        left; change k + 3 < k + 7; omega
      have h_pres := h_outside_preserved r h_out
      have h_idx_eq :
          (⟨k + 3, by
            change k + 3 < k + 7 + frag_f.numRegs
            have : 0 < frag_f.numRegs := frag_f.numRegs_pos
            omega⟩ : Fin P.numRegs) = r := Fin.ext rfl
      rw [h_idx_eq, h_pres]; exact h_i1.vX_eq
    · -- vI_eq: register `k + 4 < k + 7`.
      let r : Fin P.numRegs := ⟨k + 4, by
        rw [h_numRegs_eq]
        have : 0 < frag_f.numRegs := frag_f.numRegs_pos; omega⟩
      have h_out : r.val < fBase ∨ fBase + frag_f.numRegs ≤ r.val := by
        left; change k + 4 < k + 7; omega
      have h_pres := h_outside_preserved r h_out
      have h_idx_eq :
          (⟨k + 4, by
            change k + 4 < k + 7 + frag_f.numRegs
            have : 0 < frag_f.numRegs := frag_f.numRegs_pos
            omega⟩ : Fin P.numRegs) = r := Fin.ext rfl
      rw [h_idx_eq, h_pres]; exact h_i1.vI_eq
    · -- tmp1_zero: register `k + 5 < k + 7`.
      let r : Fin P.numRegs := ⟨k + 5, by
        rw [h_numRegs_eq]
        have : 0 < frag_f.numRegs := frag_f.numRegs_pos; omega⟩
      have h_out : r.val < fBase ∨ fBase + frag_f.numRegs ≤ r.val := by
        left; change k + 5 < k + 7; omega
      have h_pres := h_outside_preserved r h_out
      have h_idx_eq :
          (⟨k + 5, by
            change k + 5 < k + 7 + frag_f.numRegs
            have : 0 < frag_f.numRegs := frag_f.numRegs_pos
            omega⟩ : Fin P.numRegs) = r := Fin.ext rfl
      rw [h_idx_eq, h_pres]; exact h_i1.tmp1_zero
    · -- tmp2_zero: register `k + 6 < k + 7`.
      let r : Fin P.numRegs := ⟨k + 6, by
        rw [h_numRegs_eq]
        have : 0 < frag_f.numRegs := frag_f.numRegs_pos; omega⟩
      have h_out : r.val < fBase ∨ fBase + frag_f.numRegs ≤ r.val := by
        left; change k + 6 < k + 7; omega
      have h_pres := h_outside_preserved r h_out
      have h_idx_eq :
          (⟨k + 6, by
            change k + 6 < k + 7 + frag_f.numRegs
            have : 0 < frag_f.numRegs := frag_f.numRegs_pos
            omega⟩ : Fin P.numRegs) = r := Fin.ext rfl
      rw [h_idx_eq, h_pres]; exact h_i1.tmp2_zero
    · -- acc_eq: register `1 < k + 7`.
      let r : Fin P.numRegs := ⟨1, by
        rw [h_numRegs_eq]
        have : 0 < frag_f.numRegs := frag_f.numRegs_pos; omega⟩
      have h_out : r.val < fBase ∨ fBase + frag_f.numRegs ≤ r.val := by
        left; change 1 < k + 7; omega
      have h_pres := h_outside_preserved r h_out
      have h_idx_eq :
          (⟨1, by
            change 1 < k + 7 + frag_f.numRegs
            have : 0 < frag_f.numRegs := frag_f.numRegs_pos
            omega⟩ : Fin P.numRegs) = r := Fin.ext rfl
      rw [h_idx_eq, h_pres]; exact h_i1.acc_eq
    · -- f_output: f's reindexed outputReg holds f.interp v_iter.
      have hOutLt : frag_f.outputReg.val < frag_f.numRegs :=
        frag_f.outputReg.isLt
      have h_eq := h_regs_after frag_f.outputReg.val hOutLt
      have h_inner_idx :
          (⟨frag_f.outputReg.val, hOutLt⟩ : Fin frag_f.numRegs)
            = frag_f.outputReg := Fin.ext rfl
      rw [h_inner_idx] at h_eq
      have h_idx_eq :
          (⟨(k + 7) + frag_f.outputReg.val, by
            have hO : frag_f.outputReg.val < frag_f.numRegs :=
              frag_f.outputReg.isLt
            change (k + 7) + frag_f.outputReg.val
              < k + 7 + frag_f.numRegs
            omega⟩ : Fin P.numRegs)
            = ⟨fBase + frag_f.outputReg.val, by
              have hO : frag_f.outputReg.val < frag_f.numRegs :=
                frag_f.outputReg.isLt
              rw [h_numRegs_eq]; omega⟩ := Fin.ext rfl
      rw [h_idx_eq, h_eq]
      exact h_out_inner
  · -- Per-step strict PC bound on the outer side.
    intro k' hk'
    have h_f_strict_k' :
        ∀ k'' < k',
          (URMState.runFor frag_f.toURMProgram f_init k'').pc < L := by
      intro k'' hk''
      exact h_f_strict k'' (Nat.lt_trans hk'' hk')
    have h_emb_k' :
        StateEmbedsFrag (URMState.runFor P sPre k')
            (URMState.runFor frag_f.toURMProgram f_init k')
            fBase pcBase h_emb_prog.hReg :=
      stateEmbedsFrag_runFor P frag_f fBase pcBase L
        h_emb_prog sPre f_init h_state_emb k' h_f_strict_k'
    obtain ⟨h_pc_k', _⟩ := h_emb_k'
    have h_frag_k' :
        (URMState.runFor frag_f.toURMProgram f_init k').pc < L :=
      h_f_strict k' hk'
    rw [h_pc_k']
    change pcBase + (URMState.runFor frag_f.toURMProgram f_init k').pc
        < pcBase + L
    omega

/-- AccUpdate-and-epilogue instruction-presence discharger for
`compileFrag_bsum`: at PCs `bsum_trBase frag_f + 0 .. bsum_trBase
frag_f + 5`, the outer program's instructions match the four raw
entries of `URMRaw.transferLoop` (f-output → V_acc, with reserved
zero register `0`), followed by `.incR vI` (= `⟨k + 4, _⟩`) at
PC `bsum_incIPC` and `URMRaw.goto bsum_topPC = .jumpZR 0 13 13` at
PC `bsum_gotoTopPC`. Packaged as a `transferLoopInstrs` witness for
the accUpdate block plus two raw `getElem?` equations for the
epilogue prefix. Mirrors `compileFrag_bsum_zeroSweep_instr_at` and
`compileFrag_bsum_prologueBlock_instr_at`, specialised to the
accUpdate + epilogue-prefix segment. -/
private theorem compileFrag_bsum_accUpdateBlock_instr_at
    {k : ℕ}
    (frag_f : CompiledFragment (k + 1)) :
    let outer := (compileFrag_bsum frag_f).toURMProgram
    ∃ (h_src : (k + 7) + frag_f.outputReg.val < outer.numRegs)
      (h_dst : (1 : ℕ) < outer.numRegs)
      (h_z : (0 : ℕ) < outer.numRegs)
      (h_vI : k + 4 < outer.numRegs),
      transferLoopInstrs outer (bsum_trBase frag_f)
          ⟨(k + 7) + frag_f.outputReg.val, h_src⟩
          ⟨1, h_dst⟩
          ⟨0, h_z⟩
        ∧ outer.instrs[bsum_incIPC frag_f]?
            = some (URMInstr.inc ⟨k + 4, h_vI⟩)
        ∧ outer.instrs[bsum_gotoTopPC frag_f]?
            = some (URMInstr.jumpZ ⟨0, h_z⟩ 13 13) := by
  intro outer
  -- Abbreviations matching the constructor of `compileFrag_bsum`.
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
  have h_accUpdate_len : accUpdate.length = 4 := by
    change (URMRaw.transferLoop trBase
        (fBase + frag_f.outputReg.val) vAcc).length = 4
    simp only [URMRaw.transferLoop, URMRaw.goto, List.length_cons,
      List.length_nil]
  have h_epilogue_len : epilogue.length = 3 := by
    change ([URMInstrRaw.incR vI, URMRaw.goto topPC,
      URMInstrRaw.stopR] : List URMInstrRaw).length = 3
    simp only [List.length_cons, List.length_nil]
  -- outer.numRegs = nR.
  have h_numRegs_eq : outer.numRegs = nR := rfl
  -- Bound proofs for the named registers.
  have h_src_lt : (k + 7) + frag_f.outputReg.val < outer.numRegs := by
    have hO : frag_f.outputReg.val < frag_f.numRegs :=
      frag_f.outputReg.isLt
    rw [h_numRegs_eq]
    change (k + 7) + frag_f.outputReg.val < fBase + frag_f.numRegs
    omega
  have h_dst_lt : (1 : ℕ) < outer.numRegs := by
    rw [h_numRegs_eq]
    have : 0 < frag_f.numRegs := frag_f.numRegs_pos
    change 1 < fBase + frag_f.numRegs; omega
  have h_z_lt : (0 : ℕ) < outer.numRegs :=
    (compileFrag_bsum frag_f).numRegs_pos
  have h_vI_lt : k + 4 < outer.numRegs := by
    rw [h_numRegs_eq]
    have : 0 < frag_f.numRegs := frag_f.numRegs_pos
    change k + 4 < fBase + frag_f.numRegs; omega
  refine ⟨h_src_lt, h_dst_lt, h_z_lt, h_vI_lt, ?_⟩
  -- Reconstruct the boundedness witness on rawList.
  have hAcc : vAcc + 1 ≤ nR := by
    change 1 + 1 ≤ k + 7 + frag_f.numRegs
    have : 0 < frag_f.numRegs := frag_f.numRegs_pos; omega
  have hBoundIn : vBoundIn + 1 ≤ nR := by
    change 2 + 1 ≤ k + 7 + frag_f.numRegs
    have : 0 < frag_f.numRegs := frag_f.numRegs_pos; omega
  have hVX : vX + 1 ≤ nR := by
    change k + 3 + 1 ≤ k + 7 + frag_f.numRegs
    have : 0 < frag_f.numRegs := frag_f.numRegs_pos; omega
  have hVI : vI + 1 ≤ nR := by
    change k + 4 + 1 ≤ k + 7 + frag_f.numRegs
    have : 0 < frag_f.numRegs := frag_f.numRegs_pos; omega
  have hTmp1 : tmp1 + 1 ≤ nR := by
    change k + 5 + 1 ≤ k + 7 + frag_f.numRegs
    have : 0 < frag_f.numRegs := frag_f.numRegs_pos; omega
  have hTmp2 : tmp2 + 1 ≤ nR := by
    change k + 6 + 1 ≤ k + 7 + frag_f.numRegs
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
  -- For each instruction position trBase + d (0 ≤ d < 6), establish
  -- the raw entry directly. The combined accUpdate ++ epilogue at
  -- positions 0..5 is:
  --   [jumpZR (fBase+oR.val) (trBase+4) (trBase+1),
  --    decR (fBase+oR.val), incR vAcc, jumpZR 0 trBase trBase,
  --    incR vI, jumpZR 0 13 13].
  -- The rawList equals
  --   prelude ++ loopTop ++ zeroSweep ++ prologue ++ fBody
  --     ++ accUpdate ++ epilogue;
  -- the prefix preAc = prelude ++ loopTop ++ zeroSweep ++ prologue ++
  -- fBody has length 13 + 2 + numRegs + 9*(k+1) + (instrs.size - 1)
  -- = trBase.
  set preAc : List URMInstrRaw :=
    prelude ++ loopTop ++ zeroSweep ++ prologue ++ fBody
    with h_preAc_def
  have h_preAc_len : preAc.length = trBase := by
    rw [h_preAc_def]
    simp only [List.length_append]
    rw [h_prelude_len, h_loopTop_len, h_zeroSweep_len, h_prologue_len,
      h_fBody_len]
  -- Per-position lookup helper: rawList at PC trBase + d (for d < 6)
  -- equals the corresponding entry of accUpdate ++ epilogue.
  have h_lookup_raw : ∀ (d : ℕ) (hd : d < 6) (h_idx_lt : trBase + d
      < rawList.length),
      rawList[trBase + d]'h_idx_lt
        = (accUpdate ++ epilogue)[d]'(by
            rw [List.length_append, h_accUpdate_len, h_epilogue_len]
            omega) := by
    intro d hd h_idx_lt
    -- rawList = preAc ++ accUpdate ++ epilogue = preAc ++ (accUpdate
    -- ++ epilogue) by associativity.
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
    have h_idx_in_acEp :
        trBase + d - preAc.length
          < (accUpdate ++ epilogue).length := by
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
  have h_ae_d_in_rawList : ∀ (d : ℕ) (hd : d < 6),
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
      ∀ (d : ℕ) (hd : d < 6),
        outer.instrs[trBase + d]?
          = some (URMInstrRaw.toBounded nR
              ((accUpdate ++ epilogue)[d]'(by
                rw [List.length_append, h_accUpdate_len, h_epilogue_len]
                omega))
              (hBoundOuter _ (h_ae_d_in_rawList d hd))) := by
    intro d hd
    have h_idx_lt_outer : trBase + d < rawList.length := by
      have h_raw_len : rawList.length = preAc.length + 4 + 3 := by
        change (prelude ++ loopTop ++ zeroSweep ++ prologue ++ fBody
          ++ accUpdate ++ epilogue).length = preAc.length + 4 + 3
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
  -- Concrete entries of accUpdate ++ epilogue at d = 0..5.
  have h_ae_0 : (accUpdate ++ epilogue)[(0 : ℕ)]'(by
      rw [List.length_append, h_accUpdate_len, h_epilogue_len]; decide)
      = URMInstrRaw.jumpZR (fBase + frag_f.outputReg.val)
          (trBase + 4) (trBase + 1) := rfl
  have h_ae_1 : (accUpdate ++ epilogue)[(1 : ℕ)]'(by
      rw [List.length_append, h_accUpdate_len, h_epilogue_len]; decide)
      = URMInstrRaw.decR (fBase + frag_f.outputReg.val) := rfl
  have h_ae_2 : (accUpdate ++ epilogue)[(2 : ℕ)]'(by
      rw [List.length_append, h_accUpdate_len, h_epilogue_len]; decide)
      = URMInstrRaw.incR vAcc := rfl
  have h_ae_3 : (accUpdate ++ epilogue)[(3 : ℕ)]'(by
      rw [List.length_append, h_accUpdate_len, h_epilogue_len]; decide)
      = URMInstrRaw.jumpZR 0 trBase trBase := rfl
  have h_ae_4 : (accUpdate ++ epilogue)[(4 : ℕ)]'(by
      rw [List.length_append, h_accUpdate_len, h_epilogue_len]; decide)
      = URMInstrRaw.incR vI := rfl
  have h_ae_5 : (accUpdate ++ epilogue)[(5 : ℕ)]'(by
      rw [List.length_append, h_accUpdate_len, h_epilogue_len]; decide)
      = URMInstrRaw.jumpZR 0 13 13 := rfl
  -- Use each h_ae_d via toBounded_congr through the lookup.
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · -- transferLoopInstrs.h0.
    change outer.instrs[bsum_trBase frag_f + 0]? = _
    rw [show bsum_trBase frag_f + 0 = trBase + 0 from rfl]
    have h := h_outerInstr_lookup 0 (by decide)
    rw [h]
    apply congrArg some
    exact URMInstrRaw.toBounded_congr nR h_ae_0 _ _
  · -- transferLoopInstrs.h1.
    change outer.instrs[bsum_trBase frag_f + 1]? = _
    rw [show bsum_trBase frag_f + 1 = trBase + 1 from rfl]
    have h := h_outerInstr_lookup 1 (by decide)
    rw [h]
    apply congrArg some
    exact URMInstrRaw.toBounded_congr nR h_ae_1 _ _
  · -- transferLoopInstrs.h2.
    change outer.instrs[bsum_trBase frag_f + 2]? = _
    rw [show bsum_trBase frag_f + 2 = trBase + 2 from rfl]
    have h := h_outerInstr_lookup 2 (by decide)
    rw [h]
    apply congrArg some
    exact URMInstrRaw.toBounded_congr nR h_ae_2 _ _
  · -- transferLoopInstrs.h3.
    change outer.instrs[bsum_trBase frag_f + 3]? = _
    rw [show bsum_trBase frag_f + 3 = trBase + 3 from rfl]
    have h := h_outerInstr_lookup 3 (by decide)
    rw [h]
    apply congrArg some
    exact URMInstrRaw.toBounded_congr nR h_ae_3 _ _
  · -- Epilogue lookup at incIPC = trBase + 4.
    change outer.instrs[bsum_incIPC frag_f]? = _
    rw [show bsum_incIPC frag_f = trBase + 4 from rfl]
    have h := h_outerInstr_lookup 4 (by decide)
    rw [h]
    apply congrArg some
    exact URMInstrRaw.toBounded_congr nR h_ae_4 _ _
  · -- Epilogue lookup at gotoTopPC = trBase + 5.
    change outer.instrs[bsum_gotoTopPC frag_f]? = _
    rw [show bsum_gotoTopPC frag_f = trBase + 5 from rfl]
    have h := h_outerInstr_lookup 5 (by decide)
    rw [h]
    apply congrArg some
    exact URMInstrRaw.toBounded_congr nR h_ae_5 _ _

/-- Phase i.3 preservation lemma: from
`compileFrag_bsum_phase_i2_post @ i`, running for `T0 :=
4 * f.interp (Fin.cons i.val (Fin.tail v)) + 3` further steps
(the per-iteration accumulator-update `transferLoop`, the `incR vI`,
and the `goto topPC`) lands the state in
`compileFrag_bsum_partial_invariant @ (i.val + 1)`. The accompanying
strict PC bound states that during these `T0` steps the intermediate
PC stays strictly less than `(compileFrag_bsum frag_f).instrs.size
- 1` (= `bsum_exitPC frag_f`). The proof composes
`compileFrag_bsum_accUpdate_correct` over `4 * vSrc + 1` steps with
single `step` reductions for the `incR vI` and `goto topPC`
instructions; the instruction-presence dischargers come from
`compileFrag_bsum_accUpdateBlock_instr_at`. -/
private theorem compileFrag_bsum_partial_phase_i3
    {k : ℕ}
    (f : ERMor1 (k + 1))
    (v : Fin (k + 1) → ℕ)
    (i : Fin (v 0))
    (sPre : URMState
      (compileFrag_bsum (compileERFrag f)).toURMProgram)
    (h_i2 : compileFrag_bsum_phase_i2_post (compileERFrag f) f v i sPre) :
    let T0 : ℕ := 4 * f.interp (Fin.cons i.val (Fin.tail v)) + 3
    let outer := (compileFrag_bsum (compileERFrag f)).toURMProgram
    compileFrag_bsum_partial_invariant (compileERFrag f) f v (i.val + 1)
        (Nat.succ_le_of_lt i.isLt)
        (URMState.runFor outer sPre T0)
      ∧ (∀ k' < T0,
        (URMState.runFor outer sPre k').pc
          < (compileFrag_bsum (compileERFrag f)).instrs.size - 1) := by
  intro T0 outer
  -- Abbreviations matching the outer program.
  let frag_f : CompiledFragment (k + 1) := compileERFrag f
  let outerFrag : CompiledFragment (k + 1) := compileFrag_bsum frag_f
  let P : URMProgram (k + 1) := outerFrag.toURMProgram
  let v_iter : Fin (k + 1) → ℕ := Fin.cons i.val (Fin.tail v)
  let fOutVal : ℕ := f.interp v_iter
  let pcBase : ℕ := bsum_trBase frag_f
  change compileFrag_bsum_partial_invariant frag_f f v (i.val + 1)
      (Nat.succ_le_of_lt i.isLt)
      (URMState.runFor P sPre (4 * fOutVal + 3)) ∧
    (∀ k' < 4 * fOutVal + 3,
      (URMState.runFor P sPre k').pc
        < (compileFrag_bsum frag_f).instrs.size - 1)
  have h_numRegs_eq : P.numRegs = (k + 7) + frag_f.numRegs := rfl
  have h_numRegs_pos : 0 < P.numRegs := outerFrag.numRegs_pos
  -- Instruction-presence bundle.
  obtain ⟨h_src_lt, h_dst_lt, h_z_lt, h_vI_lt, H_acc, h_inc_at, h_goto_at⟩ :=
    compileFrag_bsum_accUpdateBlock_instr_at frag_f
  -- Fin handles.
  let srcFin : Fin P.numRegs :=
    ⟨(k + 7) + frag_f.outputReg.val, h_src_lt⟩
  let dstFin : Fin P.numRegs := ⟨1, h_dst_lt⟩
  let zFin : Fin P.numRegs := ⟨0, h_z_lt⟩
  let vIFin : Fin P.numRegs := ⟨k + 4, h_vI_lt⟩
  -- Disjointness.
  have h_disj_sd : srcFin ≠ dstFin := by
    intro hh
    have : ((k + 7) + frag_f.outputReg.val : ℕ) = 1 := congrArg Fin.val hh
    omega
  have h_disj_zs : zFin ≠ srcFin := by
    intro hh
    have : (0 : ℕ) = (k + 7) + frag_f.outputReg.val := congrArg Fin.val hh
    omega
  have h_disj_zd : zFin ≠ dstFin := by
    intro hh
    have : (0 : ℕ) = 1 := congrArg Fin.val hh
    omega
  -- Pre-state hypotheses from h_i2.
  have h_s_pc : sPre.pc = pcBase := by
    have h := h_i2.pc_eq
    change sPre.pc = bsum_trBase frag_f
    change sPre.pc
      = 15 + frag_f.numRegs + 9 * (k + 1)
          + (frag_f.instrs.size - 1) at h
    change sPre.pc
      = bsum_bodyPCBase frag_f + (frag_f.instrs.size - 1)
    exact h
  have h_s_z : sPre.regs zFin = 0 := by
    have h := h_i2.zReg_zero
    have h_idx_eq :
        (⟨0, (compileFrag_bsum frag_f).numRegs_pos⟩ : Fin P.numRegs)
          = zFin := Fin.ext rfl
    rw [h_idx_eq] at h
    exact h
  have h_s_src : sPre.regs srcFin = fOutVal := by
    have h := h_i2.f_output
    have h_idx_eq :
        (⟨(k + 7) + frag_f.outputReg.val, by
          have hO : frag_f.outputReg.val < frag_f.numRegs :=
            frag_f.outputReg.isLt
          change (k + 7) + frag_f.outputReg.val
            < k + 7 + frag_f.numRegs
          omega⟩ : Fin P.numRegs) = srcFin := Fin.ext rfl
    rw [h_idx_eq] at h
    exact h
  -- Step A: accUpdate transferLoop over (4 * fOutVal + 1) steps.
  obtain ⟨hA_pc, hA_dst, hA_src, hA_z, hA_oth⟩ :=
    compileFrag_bsum_accUpdate_correct P pcBase srcFin dstFin zFin
      h_disj_sd h_disj_zs h_disj_zd H_acc fOutVal sPre h_s_pc h_s_z
      h_s_src
  set sA : URMState P := URMState.runFor P sPre (4 * fOutVal + 1)
  -- sA register values at named registers (relative to sPre).
  have hsA_pc : sA.pc = pcBase + 4 := hA_pc
  have hsA_src : sA.regs srcFin = 0 := hA_src
  have hsA_z : sA.regs zFin = 0 := hA_z
  have hsA_dst : sA.regs dstFin = sPre.regs dstFin + fOutVal := hA_dst
  have hsA_oth : ∀ r, r ≠ dstFin → r ≠ srcFin → r ≠ zFin →
      sA.regs r = sPre.regs r := hA_oth
  -- Step B: incR vI (1 step). PC = bsum_incIPC = pcBase + 4 = trBase + 4.
  have h_incIPC_eq : bsum_incIPC frag_f = pcBase + 4 := by
    change bsum_trBase frag_f + 4 = pcBase + 4; rfl
  have hsA_pc_inc : sA.pc = bsum_incIPC frag_f := by
    rw [hsA_pc, h_incIPC_eq]
  have h_inc_at' :
      P.instrs[sA.pc]? = some (URMInstr.inc vIFin) := by
    rw [hsA_pc_inc]; exact h_inc_at
  have hB_step :
      URMState.step P sA =
        { pc := sA.pc + 1
          regs := Function.update sA.regs vIFin (sA.regs vIFin + 1) } :=
    URMState.step_of_getElem?_inc P sA sA.pc vIFin rfl h_inc_at'
  set sB : URMState P :=
    { pc := sA.pc + 1
      regs := Function.update sA.regs vIFin (sA.regs vIFin + 1) }
  have h_runFor_A_B : URMState.runFor P sA 1 = sB := by
    change URMState.runFor P (URMState.step P sA) 0 = _
    rw [URMState.runFor_zero, hB_step]
  have hsB_pc : sB.pc = bsum_gotoTopPC frag_f := by
    change sA.pc + 1 = bsum_gotoTopPC frag_f
    rw [hsA_pc]
    change pcBase + 4 + 1 = bsum_trBase frag_f + 5
    change bsum_trBase frag_f + 4 + 1 = _
    omega
  have hsB_vI : sB.regs vIFin = sA.regs vIFin + 1 := by
    change Function.update sA.regs vIFin (sA.regs vIFin + 1) vIFin = _
    rw [Function.update_self]
  have hsB_other_of_ne_vI : ∀ r : Fin P.numRegs, r ≠ vIFin →
      sB.regs r = sA.regs r := by
    intro r h_ne
    change Function.update sA.regs vIFin (sA.regs vIFin + 1) r = _
    rw [Function.update_of_ne h_ne]
  have hsB_z : sB.regs zFin = 0 := by
    have h_ne : zFin ≠ vIFin := by
      intro hh; have : (0 : ℕ) = k + 4 := congrArg Fin.val hh; omega
    rw [hsB_other_of_ne_vI zFin h_ne, hsA_z]
  -- Step C: goto topPC (1 step).
  -- URMRaw.goto topPC = .jumpZR 0 13 13; both branches go to 13.
  have h_goto_at' :
      P.instrs[sB.pc]? = some (URMInstr.jumpZ zFin 13 13) := by
    rw [hsB_pc]; exact h_goto_at
  have hC_step :
      URMState.step P sB =
        { pc := if sB.regs zFin = 0 then 13 else 13
          regs := sB.regs } :=
    URMState.step_of_getElem?_jumpZ P sB sB.pc zFin 13 13 rfl h_goto_at'
  set sC : URMState P :=
    { pc := if sB.regs zFin = 0 then 13 else 13
      regs := sB.regs }
  have h_runFor_B_C : URMState.runFor P sB 1 = sC := by
    change URMState.runFor P (URMState.step P sB) 0 = _
    rw [URMState.runFor_zero, hC_step]
  have hsC_pc : sC.pc = 13 := by
    change (if sB.regs zFin = 0 then 13 else 13) = 13
    split <;> rfl
  -- runFor P sPre (4*fOutVal + 3) = sC via runFor_add.
  have h_runFor_total : URMState.runFor P sPre (4 * fOutVal + 3) = sC := by
    have h_eq : 4 * fOutVal + 3 = (4 * fOutVal + 1) + 1 + 1 := by omega
    rw [h_eq, URMState.runFor_add, URMState.runFor_add]
    -- runFor P (runFor P sPre (4*fOutVal+1)) 1 = sA → sB after 1 step;
    -- runFor P sA 1 = sB; runFor P sB 1 = sC.
    change URMState.runFor P (URMState.runFor P sA 1) 1 = sC
    rw [h_runFor_A_B]
    exact h_runFor_B_C
  -- Now discharge the two conjuncts.
  refine ⟨?_, ?_⟩
  · -- compileFrag_bsum_partial_invariant @ (i.val + 1).
    rw [h_runFor_total]
    -- Pre-Step preservation auxiliaries: vI distinct from src, dst, z.
    have h_ne_vI_src : vIFin ≠ srcFin := by
      intro hh
      have : (k + 4 : ℕ) = (k + 7) + frag_f.outputReg.val :=
        congrArg Fin.val hh
      omega
    have h_ne_vI_dst : vIFin ≠ dstFin := by
      intro hh
      have : (k + 4 : ℕ) = 1 := congrArg Fin.val hh; omega
    have h_ne_vI_z : vIFin ≠ zFin := by
      intro hh
      have : (k + 4 : ℕ) = 0 := congrArg Fin.val hh; omega
    -- sA.regs vIFin = sPre.regs vIFin (vI ∉ {dst, src, z}).
    have hsA_vI : sA.regs vIFin = sPre.regs vIFin :=
      hsA_oth vIFin h_ne_vI_dst h_ne_vI_src h_ne_vI_z
    -- Pre-iteration vI value: i.val.
    have hsPre_vI : sPre.regs vIFin = i.val := by
      have h := h_i2.vI_eq
      have h_idx_eq :
          (⟨k + 4, by
            change k + 4 < k + 7 + frag_f.numRegs
            have : 0 < frag_f.numRegs := frag_f.numRegs_pos
            omega⟩ : Fin P.numRegs) = vIFin := Fin.ext rfl
      rw [h_idx_eq] at h
      exact h
    -- Refine the invariant fields.
    refine
      { hi_le := Nat.succ_le_of_lt i.isLt
        pc_eq := ?_
        zReg_zero := ?_
        outer_inputs := ?_
        vX_eq := ?_
        vI_eq := ?_
        tmp1_zero := ?_
        tmp2_zero := ?_
        acc_eq := ?_ }
    · -- pc_eq: sC.pc = 13.
      exact hsC_pc
    · -- zReg_zero: sC.regs ⟨0, _⟩ = 0.
      have h_idx_eq :
          (⟨0, (compileFrag_bsum frag_f).numRegs_pos⟩ : Fin P.numRegs)
            = zFin := Fin.ext rfl
      rw [h_idx_eq]
      change sB.regs zFin = 0
      exact hsB_z
    · -- outer_inputs: each input slot ⟨2 + j.val, _⟩ is preserved
      -- (distinct from src/dst/z and from vIFin).
      intro j
      have hj : j.val < k + 1 := j.isLt
      let r : Fin P.numRegs := ⟨2 + j.val, by
        have : 0 < frag_f.numRegs := frag_f.numRegs_pos
        rw [h_numRegs_eq]; omega⟩
      have h_ne_dst : r ≠ dstFin := by
        intro hh
        have : (2 + j.val : ℕ) = 1 := congrArg Fin.val hh; omega
      have h_ne_src : r ≠ srcFin := by
        intro hh
        have : (2 + j.val : ℕ) = (k + 7) + frag_f.outputReg.val :=
          congrArg Fin.val hh
        omega
      have h_ne_z : r ≠ zFin := by
        intro hh
        have : (2 + j.val : ℕ) = 0 := congrArg Fin.val hh; omega
      have h_ne_vI : r ≠ vIFin := by
        intro hh
        have : (2 + j.val : ℕ) = k + 4 := congrArg Fin.val hh; omega
      have hsA_r := hsA_oth r h_ne_dst h_ne_src h_ne_z
      have hsB_r := hsB_other_of_ne_vI r h_ne_vI
      have h_idx_eq :
          (⟨2 + j.val, by
            have hj' : j.val < k + 1 := j.isLt
            change 2 + j.val < k + 7 + frag_f.numRegs
            have : 0 < frag_f.numRegs := frag_f.numRegs_pos
            omega⟩ : Fin P.numRegs) = r := Fin.ext rfl
      rw [h_idx_eq]
      change sC.regs r = v j
      change sB.regs r = v j
      rw [hsB_r, hsA_r]
      exact h_i2.outer_inputs j
    · -- vX_eq: sC.regs ⟨k+3, _⟩ = v 0 - (i.val + 1).
      let r : Fin P.numRegs := ⟨k + 3, by
        have : 0 < frag_f.numRegs := frag_f.numRegs_pos
        rw [h_numRegs_eq]; omega⟩
      have h_ne_dst : r ≠ dstFin := by
        intro hh
        have : (k + 3 : ℕ) = 1 := congrArg Fin.val hh; omega
      have h_ne_src : r ≠ srcFin := by
        intro hh
        have : (k + 3 : ℕ) = (k + 7) + frag_f.outputReg.val :=
          congrArg Fin.val hh
        omega
      have h_ne_z : r ≠ zFin := by
        intro hh
        have : (k + 3 : ℕ) = 0 := congrArg Fin.val hh; omega
      have h_ne_vI : r ≠ vIFin := by
        intro hh
        have : (k + 3 : ℕ) = k + 4 := congrArg Fin.val hh; omega
      have hsA_r := hsA_oth r h_ne_dst h_ne_src h_ne_z
      have hsB_r := hsB_other_of_ne_vI r h_ne_vI
      have h_idx_eq :
          (⟨k + 3, by
            change k + 3 < k + 7 + frag_f.numRegs
            have : 0 < frag_f.numRegs := frag_f.numRegs_pos
            omega⟩ : Fin P.numRegs) = r := Fin.ext rfl
      rw [h_idx_eq]
      change sC.regs r = v 0 - (i.val + 1)
      change sB.regs r = v 0 - (i.val + 1)
      rw [hsB_r, hsA_r]
      have h_pre := h_i2.vX_eq
      have h_idx_eq' :
          (⟨k + 3, by
            change k + 3 < k + 7 + frag_f.numRegs
            have : 0 < frag_f.numRegs := frag_f.numRegs_pos
            omega⟩ : Fin P.numRegs) = r := Fin.ext rfl
      rw [h_idx_eq'] at h_pre
      rw [h_pre]
      omega
    · -- vI_eq: sC.regs vIFin = i.val + 1.
      have h_idx_eq :
          (⟨k + 4, by
            change k + 4 < k + 7 + frag_f.numRegs
            have : 0 < frag_f.numRegs := frag_f.numRegs_pos
            omega⟩ : Fin P.numRegs) = vIFin := Fin.ext rfl
      rw [h_idx_eq]
      change sC.regs vIFin = i.val + 1
      change sB.regs vIFin = i.val + 1
      rw [hsB_vI, hsA_vI, hsPre_vI]
    · -- tmp1_zero: sC.regs ⟨k+5, _⟩ = 0.
      let r : Fin P.numRegs := ⟨k + 5, by
        have : 0 < frag_f.numRegs := frag_f.numRegs_pos
        rw [h_numRegs_eq]; omega⟩
      have h_ne_dst : r ≠ dstFin := by
        intro hh
        have : (k + 5 : ℕ) = 1 := congrArg Fin.val hh; omega
      have h_ne_src : r ≠ srcFin := by
        intro hh
        have : (k + 5 : ℕ) = (k + 7) + frag_f.outputReg.val :=
          congrArg Fin.val hh
        omega
      have h_ne_z : r ≠ zFin := by
        intro hh
        have : (k + 5 : ℕ) = 0 := congrArg Fin.val hh; omega
      have h_ne_vI : r ≠ vIFin := by
        intro hh
        have : (k + 5 : ℕ) = k + 4 := congrArg Fin.val hh; omega
      have hsA_r := hsA_oth r h_ne_dst h_ne_src h_ne_z
      have hsB_r := hsB_other_of_ne_vI r h_ne_vI
      have h_idx_eq :
          (⟨k + 5, by
            change k + 5 < k + 7 + frag_f.numRegs
            have : 0 < frag_f.numRegs := frag_f.numRegs_pos
            omega⟩ : Fin P.numRegs) = r := Fin.ext rfl
      rw [h_idx_eq]
      change sC.regs r = 0
      change sB.regs r = 0
      rw [hsB_r, hsA_r]
      exact h_i2.tmp1_zero
    · -- tmp2_zero: sC.regs ⟨k+6, _⟩ = 0.
      let r : Fin P.numRegs := ⟨k + 6, by
        have : 0 < frag_f.numRegs := frag_f.numRegs_pos
        rw [h_numRegs_eq]; omega⟩
      have h_ne_dst : r ≠ dstFin := by
        intro hh
        have : (k + 6 : ℕ) = 1 := congrArg Fin.val hh; omega
      have h_ne_src : r ≠ srcFin := by
        intro hh
        have : (k + 6 : ℕ) = (k + 7) + frag_f.outputReg.val :=
          congrArg Fin.val hh
        omega
      have h_ne_z : r ≠ zFin := by
        intro hh
        have : (k + 6 : ℕ) = 0 := congrArg Fin.val hh; omega
      have h_ne_vI : r ≠ vIFin := by
        intro hh
        have : (k + 6 : ℕ) = k + 4 := congrArg Fin.val hh; omega
      have hsA_r := hsA_oth r h_ne_dst h_ne_src h_ne_z
      have hsB_r := hsB_other_of_ne_vI r h_ne_vI
      have h_idx_eq :
          (⟨k + 6, by
            change k + 6 < k + 7 + frag_f.numRegs
            have : 0 < frag_f.numRegs := frag_f.numRegs_pos
            omega⟩ : Fin P.numRegs) = r := Fin.ext rfl
      rw [h_idx_eq]
      change sC.regs r = 0
      change sB.regs r = 0
      rw [hsB_r, hsA_r]
      exact h_i2.tmp2_zero
    · -- acc_eq: sC.regs ⟨1, _⟩ = natBSum (i.val + 1) (...).
      have h_idx_eq :
          (⟨1, by
            change 1 < k + 7 + frag_f.numRegs
            have : 0 < frag_f.numRegs := frag_f.numRegs_pos
            omega⟩ : Fin P.numRegs) = dstFin := Fin.ext rfl
      rw [h_idx_eq]
      change sC.regs dstFin
        = natBSum (i.val + 1) (fun j => f.interp (Fin.cons j (Fin.tail v)))
      have h_ne_dst_vI : dstFin ≠ vIFin := by
        intro hh; have : (1 : ℕ) = k + 4 := congrArg Fin.val hh; omega
      change sB.regs dstFin
        = natBSum (i.val + 1) (fun j => f.interp (Fin.cons j (Fin.tail v)))
      rw [hsB_other_of_ne_vI dstFin h_ne_dst_vI, hsA_dst]
      -- sPre.regs dstFin = natBSum i.val (...) from h_i2.acc_eq.
      have h_pre := h_i2.acc_eq
      have h_idx_eq' :
          (⟨1, by
            change 1 < k + 7 + frag_f.numRegs
            have : 0 < frag_f.numRegs := frag_f.numRegs_pos
            omega⟩ : Fin P.numRegs) = dstFin := Fin.ext rfl
      rw [h_idx_eq'] at h_pre
      rw [h_pre]
      -- natBSum (i.val + 1) g = natBSum i.val g + g i.val by Nat.rec.
      change _ = natBSum i.val
        (fun j => f.interp (Fin.cons j (Fin.tail v))) + fOutVal
      rfl
  · -- Per-step strict PC bound: ∀ k' < T0, runFor P sPre k').pc
    -- < (compileFrag_bsum frag_f).instrs.size - 1.
    intro k' hk'
    -- size - 1 = bsum_exitPC frag_f = trBase + 6.
    have h_size_eq : (compileFrag_bsum frag_f).instrs.size - 1
        = bsum_exitPC frag_f :=
      (bsum_exitPC_eq_size_pred frag_f).symm
    have h_exit_eq : bsum_exitPC frag_f = pcBase + 6 := rfl
    rw [h_size_eq, h_exit_eq]
    -- Case-split on k' relative to 4*fOutVal + 1, 4*fOutVal + 2.
    rcases Nat.lt_or_ge k' (4 * fOutVal + 1) with hk'_lt_A | hk'_ge_A
    · -- 0 ≤ k' < 4*fOutVal + 1: inside accUpdate (or just before it).
      -- Use compileFrag_bsum_accUpdate_pc_strict_bound.
      have h_le : k' ≤ 4 * fOutVal := Nat.lt_succ_iff.mp hk'_lt_A
      have h_bound :=
        compileFrag_bsum_accUpdate_pc_strict_bound P pcBase srcFin dstFin
          zFin h_disj_sd h_disj_zs h_disj_zd H_acc fOutVal sPre h_s_pc
          h_s_z h_s_src k' h_le
      -- h_bound: runFor ... k').pc ≤ pcBase + 3 < pcBase + 6.
      omega
    · -- 4*fOutVal + 1 ≤ k' < 4*fOutVal + 3.
      rcases Nat.lt_or_ge k' (4 * fOutVal + 2) with hk'_lt_B | hk'_ge_B
      · -- k' = 4*fOutVal + 1: state is sA, pc = pcBase + 4 < pcBase + 6.
        have h_eq : k' = 4 * fOutVal + 1 := by omega
        rw [h_eq]
        change sA.pc < pcBase + 6
        rw [hsA_pc]
        omega
      · -- k' = 4*fOutVal + 2: state is sB, pc = bsum_gotoTopPC = pcBase + 5.
        have h_eq : k' = 4 * fOutVal + 2 := by omega
        rw [h_eq]
        have h_two : (4 * fOutVal + 2 : ℕ) = (4 * fOutVal + 1) + 1 := by omega
        rw [h_two, URMState.runFor_add, h_runFor_A_B]
        change sB.pc < pcBase + 6
        rw [hsB_pc]
        change pcBase + 5 < pcBase + 6
        omega

/-- Per-iteration induction glue: from
`compileFrag_bsum_partial_invariant @ i.val`, there exists a combined
step count `T0` after which `compileFrag_bsum_partial_invariant @
(i.val + 1)` holds, and throughout these `T0` steps the intermediate
PC stays strictly below `(compileFrag_bsum frag_f).instrs.size - 1`
(= `bsum_exitPC frag_f`). The witness `T0` decomposes as `T1 + T2 +
T3 + T4`: phase i.0 (`2 + numRegs_f`), phase i.1
(`9 * vPrefixSum (Fin.cons i.val (Fin.tail v)) (k + 1) + 2 * (k + 1)`),
phase i.2 (existential, `≤ compileER_runtime f (Fin.cons i.val
(Fin.tail v))`), and phase i.3 (`4 * f.interp (Fin.cons i.val
(Fin.tail v)) + 3`). The structural induction hypothesis on `f` is
threaded into phase i.2; the other phases are deterministic. -/
private theorem compileFrag_bsum_partial_step
    {k : ℕ}
    (f : ERMor1 (k + 1))
    (ih_f : ∀ (v' : Fin (k + 1) → ℕ),
      ∃ T0 : ℕ,
        T0 ≤ compileER_runtime f v' ∧
        (URMState.runFor (compileER f)
              (URMState.init (compileER f) v') T0).pc
            = (compileER f).instrs.size - 1 ∧
        (URMState.runFor (compileER f)
              (URMState.init (compileER f) v') T0).regs
            (compileER f).outputReg
          = f.interp v' ∧
        (∀ k' < T0,
          (URMState.runFor (compileER f)
              (URMState.init (compileER f) v') k').pc
            < (compileER f).instrs.size - 1))
    (v : Fin (k + 1) → ℕ)
    (i : Fin (v 0))
    (sPre : URMState
      (compileFrag_bsum (compileERFrag f)).toURMProgram)
    (h_inv : compileFrag_bsum_partial_invariant
              (compileERFrag f) f v i.val i.isLt.le sPre) :
    ∃ T0 : ℕ,
      T0 ≤ (2 + (compileERFrag f).numRegs)
            + (9 * vPrefixSum (Fin.cons i.val (Fin.tail v)) (k + 1)
                + 2 * (k + 1))
            + compileER_runtime f (Fin.cons i.val (Fin.tail v))
            + (4 * f.interp (Fin.cons i.val (Fin.tail v)) + 3)
      ∧ compileFrag_bsum_partial_invariant (compileERFrag f) f v
          (i.val + 1) (Nat.succ_le_of_lt i.isLt)
          (URMState.runFor _ sPre T0)
      ∧ (∀ k' < T0,
          (URMState.runFor _ sPre k').pc
            < (compileFrag_bsum (compileERFrag f)).instrs.size - 1) := by
  let frag_f : CompiledFragment (k + 1) := compileERFrag f
  let outer : URMProgram (k + 1) :=
    (compileFrag_bsum frag_f).toURMProgram
  let v_iter : Fin (k + 1) → ℕ := Fin.cons i.val (Fin.tail v)
  let T1 : ℕ := 2 + frag_f.numRegs
  let T2 : ℕ := 9 * vPrefixSum v_iter (k + 1) + 2 * (k + 1)
  let T4 : ℕ := 4 * f.interp v_iter + 3
  -- Rewrite the goal to use the local `let`-bindings.
  change ∃ T0 : ℕ,
      T0 ≤ T1 + T2 + compileER_runtime f v_iter + T4
    ∧ compileFrag_bsum_partial_invariant frag_f f v
        (i.val + 1) (Nat.succ_le_of_lt i.isLt)
        (URMState.runFor outer sPre T0)
    ∧ (∀ k' < T0,
        (URMState.runFor outer sPre k').pc
          < (compileFrag_bsum frag_f).instrs.size - 1)
  -- Phase i.0: deterministic step count, partial @ i.val → phase_i0_post.
  obtain ⟨h_i0_post, h_strict_i0⟩ :=
    compileFrag_bsum_partial_phase_i0 f v i sPre h_inv
  set s1 : URMState outer := URMState.runFor outer sPre T1
  -- Phase i.1: deterministic step count, phase_i0_post → phase_i1_post.
  obtain ⟨h_i1_post, h_strict_i1⟩ :=
    compileFrag_bsum_partial_phase_i1 f v i s1 h_i0_post
  set s2 : URMState outer := URMState.runFor outer s1 T2
  -- Phase i.2: existential T3, phase_i1_post → phase_i2_post.
  obtain ⟨T3, hT3_le, h_i2_post, h_strict_i2⟩ :=
    compileFrag_bsum_partial_phase_i2 f ih_f v i s2 h_i1_post
  set s3 : URMState outer := URMState.runFor outer s2 T3
  -- Phase i.3: deterministic step count, phase_i2_post → partial @ (i.val + 1).
  obtain ⟨h_inv_succ, h_strict_i3⟩ :=
    compileFrag_bsum_partial_phase_i3 f v i s3 h_i2_post
  -- Total step count.
  refine ⟨T1 + T2 + T3 + T4, ?_, ?_, ?_⟩
  · -- Bound: T1 + T2 + T3 + T4 ≤ T1 + T2 + compileER_runtime + T4.
    have h_rt : T3 ≤ compileER_runtime f v_iter := hT3_le
    omega
  · -- compileFrag_bsum_partial_invariant @ (i.val + 1).
    have h_compose :
        URMState.runFor outer sPre (T1 + T2 + T3 + T4)
          = URMState.runFor outer s3 T4 := by
      change URMState.runFor outer sPre (T1 + T2 + T3 + T4)
        = URMState.runFor outer
            (URMState.runFor outer
              (URMState.runFor outer
                (URMState.runFor outer sPre T1) T2) T3) T4
      rw [← URMState.runFor_add outer
            (URMState.runFor outer
              (URMState.runFor outer sPre T1) T2) T3 T4,
          ← URMState.runFor_add outer
            (URMState.runFor outer sPre T1) T2 (T3 + T4),
          ← URMState.runFor_add outer sPre T1 (T2 + (T3 + T4))]
      congr 1
      omega
    rw [h_compose]
    exact h_inv_succ
  · -- Per-step strict PC bound on the combined interval.
    intro k' hk'
    -- PC layout: bsum_prologueBase ≤ bsum_bodyPCBase ≤ bsum_trBase ≤ bsum_exitPC.
    have h_exitPC_size :
        bsum_exitPC frag_f
          = (compileFrag_bsum frag_f).instrs.size - 1 :=
      bsum_exitPC_eq_size_pred frag_f
    -- Numeric expansion of bsum_exitPC.
    have h_exitPC_expand :
        (compileFrag_bsum frag_f).instrs.size - 1
          = 15 + frag_f.numRegs + 9 * (k + 1)
              + (frag_f.instrs.size - 1) + 6 := by
      rw [← h_exitPC_size]
      change bsum_trBase frag_f + 6 = _
      change bsum_bodyPCBase frag_f + (frag_f.instrs.size - 1) + 6 = _
      rfl
    -- Phase i.0 strict bound: k' < T1.
    rcases Nat.lt_or_ge k' T1 with h1 | h1
    · have h_bound : (URMState.runFor outer sPre k').pc
          < 15 + frag_f.numRegs := h_strict_i0 k' h1
      -- h_bound: pc < 15 + frag_f.numRegs.
      rw [h_exitPC_expand]
      omega
    · rcases Nat.lt_or_ge k' (T1 + T2) with h2 | h2
      · -- Phase i.1 strict bound: T1 ≤ k' < T1 + T2.
        let k'' : ℕ := k' - T1
        have hk''_lt : k'' < T2 := by
          change k' - T1 < T2; omega
        have h_split : k' = T1 + k'' := by
          change k' = T1 + (k' - T1); omega
        have h_runFor_split :
            URMState.runFor outer sPre k'
              = URMState.runFor outer s1 k'' := by
          rw [h_split, URMState.runFor_add]
        have h_bound : (URMState.runFor outer s1 k'').pc
            < 15 + frag_f.numRegs + 9 * (k + 1) := h_strict_i1 k'' hk''_lt
        rw [h_runFor_split, h_exitPC_expand]
        -- h_bound: pc < 15 + frag_f.numRegs + 9 * (k + 1).
        omega
      · rcases Nat.lt_or_ge k' (T1 + T2 + T3) with h3 | h3
        · -- Phase i.2 strict bound: T1 + T2 ≤ k' < T1 + T2 + T3.
          let k'' : ℕ := k' - T1 - T2
          have hk''_lt : k'' < T3 := by
            change k' - T1 - T2 < T3; omega
          have h_split : k' = T1 + T2 + k'' := by
            change k' = T1 + T2 + (k' - T1 - T2); omega
          have h_runFor_split :
              URMState.runFor outer sPre k'
                = URMState.runFor outer s2 k'' := by
            rw [h_split]
            change URMState.runFor outer sPre (T1 + T2 + k'')
              = URMState.runFor outer
                  (URMState.runFor outer
                    (URMState.runFor outer sPre T1) T2) k''
            rw [← URMState.runFor_add outer
                  (URMState.runFor outer sPre T1) T2 k'',
                ← URMState.runFor_add outer sPre T1 (T2 + k'')]
            congr 1
            omega
          have h_bound : (URMState.runFor outer s2 k'').pc
              < 15 + frag_f.numRegs + 9 * (k + 1)
                + (frag_f.instrs.size - 1) := h_strict_i2 k'' hk''_lt
          rw [h_runFor_split, h_exitPC_expand]
          -- h_bound: pc < 15 + frag_f.numRegs + 9 * (k + 1) + (instrs.size - 1).
          omega
        · -- Phase i.3 strict bound: T1 + T2 + T3 ≤ k' < T1 + T2 + T3 + T4.
          let k'' : ℕ := k' - T1 - T2 - T3
          have hk''_lt : k'' < T4 := by
            change k' - T1 - T2 - T3 < T4; omega
          have h_split : k' = T1 + T2 + T3 + k'' := by
            change k' = T1 + T2 + T3 + (k' - T1 - T2 - T3); omega
          have h_runFor_split :
              URMState.runFor outer sPre k'
                = URMState.runFor outer s3 k'' := by
            rw [h_split]
            change URMState.runFor outer sPre (T1 + T2 + T3 + k'')
              = URMState.runFor outer
                  (URMState.runFor outer
                    (URMState.runFor outer
                      (URMState.runFor outer sPre T1) T2) T3) k''
            rw [← URMState.runFor_add outer
                  (URMState.runFor outer
                    (URMState.runFor outer sPre T1) T2) T3 k'',
                ← URMState.runFor_add outer
                  (URMState.runFor outer sPre T1) T2 (T3 + k''),
                ← URMState.runFor_add outer sPre T1 (T2 + (T3 + k''))]
            congr 1
            omega
          have h_bound := h_strict_i3 k'' hk''_lt
          rw [h_runFor_split]
          exact h_bound

/-- Per-step strict PC bound for the `compileFrag_bsum` prelude:
for every `k' < 6 + 9 * (v 0)`, the PC of `URMState.runFor outer
s_init k'` is strictly below `(compileFrag_bsum (compileERFrag
f)).instrs.size - 1` (= `bsum_exitPC frag_f`). The prelude has
four `assignR` steps at PCs `0..3` followed by a
`preservingTransfer` block at PC `4` of `9 * (v 0) + 2` steps,
keeping the PC in `[0, 12]` throughout — strictly below
`bsum_exitPC frag_f ≥ 31`. -/
private theorem compileFrag_bsum_prelude_pc_strict_bound
    {k : ℕ}
    (f : ERMor1 (k + 1))
    (v : Fin (k + 1) → ℕ)
    (k' : ℕ) (hk' : k' < 6 + 9 * (v 0)) :
    let outer := (compileFrag_bsum (compileERFrag f)).toURMProgram
    let s_init := URMState.init outer v
    (URMState.runFor outer s_init k').pc
      < (compileFrag_bsum (compileERFrag f)).instrs.size - 1 := by
  intro outer s_init
  -- Abbreviations matching `compileFrag_bsum_partial_base`.
  let frag_f : CompiledFragment (k + 1) := compileERFrag f
  let outerFrag : CompiledFragment (k + 1) := compileFrag_bsum frag_f
  let P : URMProgram (k + 1) := outerFrag.toURMProgram
  let s0 : URMState P := URMState.init P v
  change (URMState.runFor P s0 k').pc < (compileFrag_bsum frag_f).instrs.size - 1
  -- Numeric expansion of the exit PC.
  have h_exitPC_size :
      bsum_exitPC frag_f
        = (compileFrag_bsum frag_f).instrs.size - 1 :=
    bsum_exitPC_eq_size_pred frag_f
  have h_exitPC_expand :
      (compileFrag_bsum frag_f).instrs.size - 1
        = 15 + frag_f.numRegs + 9 * (k + 1)
            + (frag_f.instrs.size - 1) + 6 := by
    rw [← h_exitPC_size]
    change bsum_trBase frag_f + 6 = _
    change bsum_bodyPCBase frag_f + (frag_f.instrs.size - 1) + 6 = _
    rfl
  rw [h_exitPC_expand]
  -- Outer numRegs equals `(k + 7) + frag_f.numRegs`.
  have h_numRegs_eq : P.numRegs = (k + 7) + frag_f.numRegs := rfl
  have h_numRegs_pos : 0 < P.numRegs := outerFrag.numRegs_pos
  -- Boundedness witnesses for the four named registers used by the prelude.
  have h_z_lt : 0 < P.numRegs := h_numRegs_pos
  have h_bIn_lt : 2 < P.numRegs := by
    rw [h_numRegs_eq]
    have : 0 < frag_f.numRegs := frag_f.numRegs_pos; omega
  have h_vX_lt : k + 3 < P.numRegs := by
    rw [h_numRegs_eq]
    have : 0 < frag_f.numRegs := frag_f.numRegs_pos; omega
  have h_acc_lt : 1 < P.numRegs := by
    rw [h_numRegs_eq]
    have : 0 < frag_f.numRegs := frag_f.numRegs_pos; omega
  have h_vI_lt : k + 4 < P.numRegs := by
    rw [h_numRegs_eq]
    have : 0 < frag_f.numRegs := frag_f.numRegs_pos; omega
  have h_tmp2_lt : k + 6 < P.numRegs := by
    rw [h_numRegs_eq]
    have : 0 < frag_f.numRegs := frag_f.numRegs_pos; omega
  let rZ : Fin P.numRegs := ⟨0, h_z_lt⟩
  let rAcc : Fin P.numRegs := ⟨1, h_acc_lt⟩
  let rBoundIn : Fin P.numRegs := ⟨2, h_bIn_lt⟩
  let rVX : Fin P.numRegs := ⟨k + 3, h_vX_lt⟩
  let rVI : Fin P.numRegs := ⟨k + 4, h_vI_lt⟩
  let rTmp2 : Fin P.numRegs := ⟨k + 6, h_tmp2_lt⟩
  -- Prelude instruction lookups at PCs 0..3 (each `assignR`).
  have h_outer_at_0 : P.instrs[(0 : ℕ)]? = some (URMInstr.assign rZ 0) := rfl
  have h_outer_at_1 : P.instrs[(1 : ℕ)]? = some (URMInstr.assign rAcc 0) := rfl
  have h_outer_at_2 : P.instrs[(2 : ℕ)]? = some (URMInstr.assign rVX 0) := rfl
  have h_outer_at_3 : P.instrs[(3 : ℕ)]? = some (URMInstr.assign rVI 0) := rfl
  -- preservingTransferInstrs at PC 4.
  have H_pT : preservingTransferInstrs P 4 rBoundIn rVX rTmp2 rZ := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rfl
  -- Disjointness of the four register handles for preservingTransfer.
  have h_disj_sd : rBoundIn ≠ rVX := by
    intro h; have : (2 : ℕ) = k + 3 := congrArg Fin.val h; omega
  have h_disj_st : rBoundIn ≠ rTmp2 := by
    intro h; have : (2 : ℕ) = k + 6 := congrArg Fin.val h; omega
  have h_disj_dt : rVX ≠ rTmp2 := by
    intro h; have : (k + 3 : ℕ) = k + 6 := congrArg Fin.val h; omega
  have h_disj_zs : rZ ≠ rBoundIn := by
    intro h; have : (0 : ℕ) = 2 := congrArg Fin.val h; omega
  have h_disj_zd : rZ ≠ rVX := by
    intro h; have : (0 : ℕ) = k + 3 := congrArg Fin.val h; omega
  have h_disj_zt : rZ ≠ rTmp2 := by
    intro h; have : (0 : ℕ) = k + 6 := congrArg Fin.val h; omega
  -- Outer's `inputRegs` maps slot `j` to outer register `2 + j.val`.
  have h_outer_inputRegs : ∀ (j : Fin (k + 1)),
      (P.inputRegs j).val = 2 + j.val := fun _ => rfl
  -- Step ladder s0 → s1 → s2 → s3 → s4.
  have hs0_pc : s0.pc = 0 := rfl
  have h_step0 :
      URMState.step P s0 =
        { pc := 1
          regs := Function.update s0.regs rZ 0 } := by
    have h := URMState.step_of_getElem?_assign P s0 0 rZ 0 hs0_pc h_outer_at_0
    rw [h]
    have : s0.pc + 1 = 1 := by rw [hs0_pc]
    rw [this]
  let s1 : URMState P :=
    { pc := 1
      regs := Function.update s0.regs rZ 0 }
  have h_runFor_1 : URMState.runFor P s0 1 = s1 := by
    change URMState.runFor P (URMState.step P s0) 0 = _
    rw [URMState.runFor_zero, h_step0]
  have hs1_pc : s1.pc = 1 := rfl
  have h_step1 :
      URMState.step P s1 =
        { pc := 2
          regs := Function.update s1.regs rAcc 0 } := by
    have h := URMState.step_of_getElem?_assign P s1 1 rAcc 0 hs1_pc h_outer_at_1
    rw [h]
  let s2 : URMState P :=
    { pc := 2
      regs := Function.update s1.regs rAcc 0 }
  have hs2_pc : s2.pc = 2 := rfl
  have h_step2 :
      URMState.step P s2 =
        { pc := 3
          regs := Function.update s2.regs rVX 0 } := by
    have h := URMState.step_of_getElem?_assign P s2 2 rVX 0 hs2_pc h_outer_at_2
    rw [h]
  let s3 : URMState P :=
    { pc := 3
      regs := Function.update s2.regs rVX 0 }
  have hs3_pc : s3.pc = 3 := rfl
  have h_step3 :
      URMState.step P s3 =
        { pc := 4
          regs := Function.update s3.regs rVI 0 } := by
    have h := URMState.step_of_getElem?_assign P s3 3 rVI 0 hs3_pc h_outer_at_3
    rw [h]
  let s4 : URMState P :=
    { pc := 4
      regs := Function.update s3.regs rVI 0 }
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
  have hs4_pc : s4.pc = 4 := rfl
  -- s4 register values at rZ, rTmp2, rBoundIn.
  have h_ne_rZ_rAcc : rZ ≠ rAcc := by
    intro h; have : (0 : ℕ) = 1 := congrArg Fin.val h; omega
  have h_ne_rZ_rVX : rZ ≠ rVX := by
    intro h; have : (0 : ℕ) = k + 3 := congrArg Fin.val h; omega
  have h_ne_rZ_rVI : rZ ≠ rVI := by
    intro h; have : (0 : ℕ) = k + 4 := congrArg Fin.val h; omega
  have hs4_rZ : s4.regs rZ = 0 := by
    change Function.update s3.regs rVI 0 rZ = 0
    rw [Function.update_of_ne h_ne_rZ_rVI]
    change Function.update s2.regs rVX 0 rZ = 0
    rw [Function.update_of_ne h_ne_rZ_rVX]
    change Function.update s1.regs rAcc 0 rZ = 0
    rw [Function.update_of_ne h_ne_rZ_rAcc]
    change Function.update s0.regs rZ 0 rZ = 0
    rw [Function.update_self]
  have h_ne_T2_rZ : rTmp2 ≠ rZ := by
    intro h; have : (k + 6 : ℕ) = 0 := congrArg Fin.val h; omega
  have h_ne_T2_rAcc : rTmp2 ≠ rAcc := by
    intro h; have : (k + 6 : ℕ) = 1 := congrArg Fin.val h; omega
  have h_ne_T2_rVX : rTmp2 ≠ rVX := by
    intro h; have : (k + 6 : ℕ) = k + 3 := congrArg Fin.val h; omega
  have h_ne_T2_rVI : rTmp2 ≠ rVI := by
    intro h; have : (k + 6 : ℕ) = k + 4 := congrArg Fin.val h; omega
  have hs4_rTmp2 : s4.regs rTmp2 = 0 := by
    change Function.update s3.regs rVI 0 rTmp2 = 0
    rw [Function.update_of_ne h_ne_T2_rVI]
    change Function.update s2.regs rVX 0 rTmp2 = 0
    rw [Function.update_of_ne h_ne_T2_rVX]
    change Function.update s1.regs rAcc 0 rTmp2 = 0
    rw [Function.update_of_ne h_ne_T2_rAcc]
    change Function.update s0.regs rZ 0 rTmp2 = 0
    rw [Function.update_of_ne h_ne_T2_rZ]
    change (URMState.init P v).regs rTmp2 = 0
    apply URMState.init_regs_zero_outside_inputs P v h_outer_inputRegs
    right; right
    change 2 + (k + 1) ≤ k + 6; omega
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
    change Function.update s3.regs rVI 0 rBoundIn = v 0
    rw [Function.update_of_ne h_ne_BIn_rVI]
    change Function.update s2.regs rVX 0 rBoundIn = v 0
    rw [Function.update_of_ne h_disj_sd]
    change Function.update s1.regs rAcc 0 rBoundIn = v 0
    rw [Function.update_of_ne h_ne_BIn_rAcc]
    change Function.update s0.regs rZ 0 rBoundIn = v 0
    rw [Function.update_of_ne h_ne_BIn_rZ]
    exact hs0_rBoundIn
  -- Case split on k' < 4 or 4 ≤ k' < 6 + 9 * (v 0).
  rcases Nat.lt_or_ge k' 4 with h_lo | h_hi
  · -- k' ∈ {0, 1, 2, 3}: PC at step k' is k', strictly below the exit PC.
    have h_pos_numRegs : 0 < frag_f.numRegs := frag_f.numRegs_pos
    -- The four assignR steps drive the PC `0 → 1 → 2 → 3 → 4`; PC at step
    -- k' ∈ {0, 1, 2, 3} is k', strictly below `4`.
    have h_runFor_s1_1 : URMState.runFor P s1 1 = s2 := by
      change URMState.runFor P (URMState.step P s1) 0 = _
      rw [URMState.runFor_zero, h_step1]
    have h_runFor_s2_1 : URMState.runFor P s2 1 = s3 := by
      change URMState.runFor P (URMState.step P s2) 0 = _
      rw [URMState.runFor_zero, h_step2]
    have h_pc_lt : (URMState.runFor P s0 k').pc < 4 := by
      match k', h_lo with
      | 0, _ => rw [URMState.runFor_zero]; change (0 : ℕ) < 4; omega
      | 1, _ => rw [h_runFor_1]; change (1 : ℕ) < 4; omega
      | 2, _ =>
        have h_eq : (2 : ℕ) = 1 + 1 := by omega
        rw [h_eq, URMState.runFor_add, h_runFor_1, h_runFor_s1_1]
        change (2 : ℕ) < 4; omega
      | 3, _ =>
        have h_eq : (3 : ℕ) = 1 + 1 + 1 := by omega
        rw [h_eq, URMState.runFor_add, URMState.runFor_add,
          h_runFor_1, h_runFor_s1_1, h_runFor_s2_1]
        change (3 : ℕ) < 4; omega
    -- Atomise pc and numRegs/instrs.size for omega.
    set pc_atom : ℕ := (URMState.runFor P s0 k').pc
    set nR : ℕ := frag_f.numRegs
    set sz : ℕ := frag_f.instrs.size - 1
    omega
  · -- 4 ≤ k' < 6 + 9 * (v 0): split as k' = 4 + (k' - 4) and apply
    -- preservingTransfer_correct_pc_strict_bound at pcBase = 4.
    let k'' : ℕ := k' - 4
    have hk''_lt : k'' < 9 * (v 0) + 2 := by
      change k' - 4 < 9 * (v 0) + 2; omega
    have h_split : k' = 4 + k'' := by
      change k' = 4 + (k' - 4); omega
    have h_runFor_split :
        URMState.runFor P s0 k'
          = URMState.runFor P s4 k'' := by
      rw [h_split, URMState.runFor_add, h_runFor_4]
    rw [h_runFor_split]
    have h_bound :
        (URMState.runFor P s4 k'').pc ≤ 4 + 8 :=
      preservingTransfer_correct_pc_strict_bound P 4 rBoundIn rVX rTmp2 rZ
        h_disj_sd h_disj_st h_disj_dt h_disj_zs h_disj_zd h_disj_zt
        H_pT s4 hs4_pc hs4_rZ hs4_rTmp2 (v 0) hs4_rBoundIn k'' hk''_lt
    have h_pos_numRegs : 0 < frag_f.numRegs := frag_f.numRegs_pos
    set pc_atom : ℕ := (URMState.runFor P s4 k'').pc
    set nR : ℕ := frag_f.numRegs
    set sz : ℕ := frag_f.instrs.size - 1
    omega

/-- Strengthened outer iteration of `compileFrag_bsum`'s pre-stop
trace: for every `i ≤ v 0`, there exists a combined step count
`T0` after which `compileFrag_bsum_partial_invariant @ i` holds
and throughout these `T0` steps the intermediate PC stays
strictly below `(compileFrag_bsum (compileERFrag f)).instrs.size
- 1` (= `bsum_exitPC frag_f`). The bound `T0 ≤ (6 + 9 * (v 0))
+ Σ_{j < i} perIter j` decomposes as the prelude cost (from
`compileFrag_bsum_partial_base`) plus a `List.range i`-indexed
sum of per-iteration costs (each iteration's cost from
`compileFrag_bsum_partial_step`). Specialising `i := v 0`
recovers the unbounded form `compileFrag_bsum_partial`. -/
private theorem compileFrag_bsum_partial_aux
    {k : ℕ}
    (f : ERMor1 (k + 1))
    (ih_f : ∀ (v' : Fin (k + 1) → ℕ),
      ∃ T0 : ℕ,
        T0 ≤ compileER_runtime f v' ∧
        (URMState.runFor (compileER f)
              (URMState.init (compileER f) v') T0).pc
            = (compileER f).instrs.size - 1 ∧
        (URMState.runFor (compileER f)
              (URMState.init (compileER f) v') T0).regs
            (compileER f).outputReg
          = f.interp v' ∧
        (∀ k' < T0,
          (URMState.runFor (compileER f)
              (URMState.init (compileER f) v') k').pc
            < (compileER f).instrs.size - 1))
    (v : Fin (k + 1) → ℕ)
    (i : ℕ) (hi : i ≤ v 0) :
    let outer := (compileFrag_bsum (compileERFrag f)).toURMProgram
    let s_init := URMState.init outer v
    let perIter : ℕ → ℕ := fun j =>
      (2 + (compileERFrag f).numRegs)
        + (9 * vPrefixSum (Fin.cons j (Fin.tail v)) (k + 1)
            + 2 * (k + 1))
        + compileER_runtime f (Fin.cons j (Fin.tail v))
        + (4 * f.interp (Fin.cons j (Fin.tail v)) + 3)
    ∃ T0 : ℕ,
      T0 ≤ (6 + 9 * (v 0))
            + ((List.range i).map perIter).foldl (· + ·) 0
      ∧ compileFrag_bsum_partial_invariant (compileERFrag f) f v
          i hi (URMState.runFor outer s_init T0)
      ∧ (∀ k' < T0,
          (URMState.runFor outer s_init k').pc
            < (compileFrag_bsum (compileERFrag f)).instrs.size - 1) := by
  intro outer s_init perIter
  let frag_f : CompiledFragment (k + 1) := compileERFrag f
  induction i with
  | zero =>
    refine ⟨6 + 9 * (v 0), ?_, ?_, ?_⟩
    · -- Bound: List.range 0 = []; foldl on empty is 0.
      change 6 + 9 * (v 0) ≤ (6 + 9 * (v 0))
        + (([] : List ℕ).map perIter).foldl (· + ·) 0
      simp
    · -- partial_invariant @ 0 from the base case.
      exact compileFrag_bsum_partial_base f v
    · -- Strict PC bound across the prelude.
      intro k' hk'
      exact compileFrag_bsum_prelude_pc_strict_bound f v k' hk'
  | succ i' ih =>
    have hi' : i' ≤ v 0 := Nat.le_of_succ_le hi
    have hi'_lt : i' < v 0 := hi
    obtain ⟨T_i', hT_i'_bound, h_inv_i', h_strict_i'⟩ := ih hi'
    let i_fin : Fin (v 0) := ⟨i', hi'_lt⟩
    let sPre : URMState outer := URMState.runFor outer s_init T_i'
    obtain ⟨T_step, hT_step_bound, h_inv_succ, h_strict_step⟩ :=
      compileFrag_bsum_partial_step f ih_f v i_fin sPre h_inv_i'
    refine ⟨T_i' + T_step, ?_, ?_, ?_⟩
    · -- Bound: T_i' + T_step ≤ (6 + 9 * (v 0))
      -- + ((List.range (i' + 1)).map perIter).foldl (· + ·) 0.
      -- Unfold List.range (i' + 1) = List.range i' ++ [i'].
      have h_range_snoc :
          List.range (i' + 1) = List.range i' ++ [i'] := List.range_succ
      rw [h_range_snoc, List.map_append, List.map_cons, List.map_nil]
      have h_foldl_snoc : ∀ (l : List ℕ) (x : ℕ),
          (l ++ [x]).foldl (· + ·) 0 = l.foldl (· + ·) 0 + x := by
        intro l x
        rw [List.foldl_append]
        change l.foldl (· + ·) 0 + x = _
        rfl
      rw [h_foldl_snoc]
      -- T_step ≤ perIter i' = perIter i_fin.val (definitionally identical).
      have hT_step_bound' :
          T_step ≤ (2 + frag_f.numRegs)
            + (9 * vPrefixSum (Fin.cons i_fin.val (Fin.tail v)) (k + 1)
                + 2 * (k + 1))
            + compileER_runtime f (Fin.cons i_fin.val (Fin.tail v))
            + (4 * f.interp (Fin.cons i_fin.val (Fin.tail v)) + 3) :=
        hT_step_bound
      have h_perIter_eq :
          perIter i' = (2 + frag_f.numRegs)
            + (9 * vPrefixSum (Fin.cons i_fin.val (Fin.tail v)) (k + 1)
                + 2 * (k + 1))
            + compileER_runtime f (Fin.cons i_fin.val (Fin.tail v))
            + (4 * f.interp (Fin.cons i_fin.val (Fin.tail v)) + 3) := rfl
      omega
    · -- partial_invariant @ (i' + 1) via runFor_add.
      have h_compose :
          URMState.runFor outer s_init (T_i' + T_step)
            = URMState.runFor outer sPre T_step := by
        rw [URMState.runFor_add]
      rw [h_compose]
      exact h_inv_succ
    · -- Strict PC bound on the combined interval.
      intro k' hk'
      rcases Nat.lt_or_ge k' T_i' with h_lo | h_hi
      · exact h_strict_i' k' h_lo
      · let k'' : ℕ := k' - T_i'
        have hk''_lt : k'' < T_step := by
          change k' - T_i' < T_step; omega
        have h_split : k' = T_i' + k'' := by
          change k' = T_i' + (k' - T_i'); omega
        have h_runFor_split :
            URMState.runFor outer s_init k'
              = URMState.runFor outer sPre k'' := by
          rw [h_split, URMState.runFor_add]
        rw [h_runFor_split]
        exact h_strict_step k'' hk''_lt

/-- Outer iteration of `compileFrag_bsum`'s pre-stop trace at
`i = v 0`: thin specialisation of `compileFrag_bsum_partial_aux`
at the unbounded form, producing the `compileFrag_bsum_partial_invariant
@ v 0` state (loop counter exhausted, accumulator equal to the
total `bsum`-sum) ready to be threaded through the trailing
`stopR` by the final assembly `compileER_pre_stop_correct_bsum`. -/
private theorem compileFrag_bsum_partial
    {k : ℕ}
    (f : ERMor1 (k + 1))
    (ih_f : ∀ (v' : Fin (k + 1) → ℕ),
      ∃ T0 : ℕ,
        T0 ≤ compileER_runtime f v' ∧
        (URMState.runFor (compileER f)
              (URMState.init (compileER f) v') T0).pc
            = (compileER f).instrs.size - 1 ∧
        (URMState.runFor (compileER f)
              (URMState.init (compileER f) v') T0).regs
            (compileER f).outputReg
          = f.interp v' ∧
        (∀ k' < T0,
          (URMState.runFor (compileER f)
              (URMState.init (compileER f) v') k').pc
            < (compileER f).instrs.size - 1))
    (v : Fin (k + 1) → ℕ) :
    let outer := (compileFrag_bsum (compileERFrag f)).toURMProgram
    let s_init := URMState.init outer v
    let perIter : ℕ → ℕ := fun j =>
      (2 + (compileERFrag f).numRegs)
        + (9 * vPrefixSum (Fin.cons j (Fin.tail v)) (k + 1)
            + 2 * (k + 1))
        + compileER_runtime f (Fin.cons j (Fin.tail v))
        + (4 * f.interp (Fin.cons j (Fin.tail v)) + 3)
    ∃ T0 : ℕ,
      T0 ≤ (6 + 9 * (v 0))
            + ((List.range (v 0)).map perIter).foldl (· + ·) 0
      ∧ compileFrag_bsum_partial_invariant (compileERFrag f) f v
          (v 0) (Nat.le_refl _) (URMState.runFor outer s_init T0)
      ∧ (∀ k' < T0,
          (URMState.runFor outer s_init k').pc
            < (compileFrag_bsum (compileERFrag f)).instrs.size - 1) :=
  compileFrag_bsum_partial_aux f ih_f v (v 0) (Nat.le_refl _)

/-- Final assembly of the `compileFrag_bsum` pre-stop trace: from the
inductive hypothesis on `f`, produces the standard pre-stop existential
witness for `.bsum f` (a `T0 ≤ compileER_runtime (.bsum f) v` such that
at step `T0` the PC sits at `instrs.size - 1`, the output register
holds `(.bsum f).interp v`, and on every earlier step the PC is
strictly below `instrs.size - 1`). Mirrors
`compileER_pre_stop_correct_comp` (`Comp.lean`); the `bsum`-specific
final step discharges the loop-top `jumpZR vX exitPC bodyStartPC`
instruction at `bsum_topPC = 13` via its zero-branch
(`vX = v 0 - v 0 = 0` from the partial-invariant `vX_eq` clause at
`i = v 0`). -/
private theorem compileER_pre_stop_correct_bsum
    {k : ℕ}
    (f : ERMor1 (k + 1))
    (ih_f : ∀ (v' : Fin (k + 1) → ℕ),
      ∃ T0 : ℕ,
        T0 ≤ compileER_runtime f v' ∧
        (URMState.runFor (compileER f)
              (URMState.init (compileER f) v') T0).pc
            = (compileER f).instrs.size - 1 ∧
        (URMState.runFor (compileER f)
              (URMState.init (compileER f) v') T0).regs
            (compileER f).outputReg
          = f.interp v' ∧
        (∀ k' < T0,
          (URMState.runFor (compileER f)
              (URMState.init (compileER f) v') k').pc
            < (compileER f).instrs.size - 1))
    (v : Fin (k + 1) → ℕ) :
    ∃ T0 : ℕ,
      T0 ≤ compileER_runtime (.bsum f : ERMor1 (k + 1)) v ∧
      (URMState.runFor (compileER (.bsum f : ERMor1 (k + 1)))
            (URMState.init
              (compileER (.bsum f : ERMor1 (k + 1))) v) T0).pc
          = (compileER (.bsum f : ERMor1 (k + 1))).instrs.size - 1 ∧
      (URMState.runFor (compileER (.bsum f : ERMor1 (k + 1)))
            (URMState.init
              (compileER (.bsum f : ERMor1 (k + 1))) v) T0).regs
          (compileER (.bsum f : ERMor1 (k + 1))).outputReg
        = (.bsum f : ERMor1 (k + 1)).interp v ∧
      (∀ k' < T0,
        (URMState.runFor (compileER (.bsum f : ERMor1 (k + 1)))
            (URMState.init
              (compileER (.bsum f : ERMor1 (k + 1))) v) k').pc
          < (compileER (.bsum f : ERMor1 (k + 1))).instrs.size - 1) := by
  let frag_f : CompiledFragment (k + 1) := compileERFrag f
  let outerFrag : CompiledFragment (k + 1) := compileFrag_bsum frag_f
  let outer : URMProgram (k + 1) := outerFrag.toURMProgram
  let s_init : URMState outer := URMState.init outer v
  -- Step 1: invoke bsum.5 to obtain the partial-invariant witness at i = v 0.
  obtain ⟨T_partial, hT_partial_bound, h_inv, h_strict_partial⟩ :=
    compileFrag_bsum_partial f ih_f v
  set sPost : URMState outer := URMState.runFor outer s_init T_partial
  -- Step 2: execute the final `jumpZR vX exitPC bodyStartPC` at PC 13.
  -- At i = v 0, the partial invariant gives s.regs vX = v 0 - v 0 = 0, so
  -- the jumpZ takes the zero branch to `exitPC`.
  have h_numRegs_eq : outer.numRegs = (k + 7) + frag_f.numRegs := rfl
  have h_vX_lt : k + 3 < outer.numRegs := by
    rw [h_numRegs_eq]
    have : 0 < frag_f.numRegs := frag_f.numRegs_pos
    omega
  let rVX : Fin outer.numRegs := ⟨k + 3, h_vX_lt⟩
  let exitPC_lit : ℕ :=
    15 + frag_f.numRegs + 9 * (k + 1) + (frag_f.instrs.size - 1) + 6
  have h_at_13 : outer.instrs[(13 : ℕ)]?
      = some (URMInstr.jumpZ rVX exitPC_lit 14) := rfl
  have h_sPost_pc : sPost.pc = 13 := h_inv.pc_eq
  have h_sPost_vX_zero : sPost.regs rVX = 0 := by
    have h := h_inv.vX_eq
    change sPost.regs rVX = v 0 - v 0 at h
    rw [h]
    omega
  have h_step_final :
      URMState.step outer sPost =
        { pc := exitPC_lit
          regs := sPost.regs } := by
    have h := URMState.step_of_getElem?_jumpZ outer sPost 13 rVX
      exitPC_lit 14 h_sPost_pc h_at_13
    rw [h, if_pos h_sPost_vX_zero]
  -- The final state after T_partial + 1 steps.
  set sFinal : URMState outer :=
    URMState.runFor outer s_init (T_partial + 1)
  have h_runFor_step :
      URMState.runFor outer sPost 1 = URMState.step outer sPost := rfl
  have h_sFinal_decomp :
      sFinal = URMState.step outer sPost := by
    change URMState.runFor outer s_init (T_partial + 1) = _
    rw [URMState.runFor_add]
    exact h_runFor_step
  -- exitPC_lit equals (compileFrag_bsum frag_f).instrs.size - 1.
  have h_size : outerFrag.instrs.size
      = 15 + frag_f.numRegs + 9 * (k + 1)
        + (frag_f.instrs.size - 1) + 4 + 3 :=
    compileFrag_bsum_size frag_f
  have h_exitPC_eq_size_pred :
      exitPC_lit = outerFrag.instrs.size - 1 := by
    rw [h_size]
    change 15 + frag_f.numRegs + 9 * (k + 1)
        + (frag_f.instrs.size - 1) + 6
      = 15 + frag_f.numRegs + 9 * (k + 1)
        + (frag_f.instrs.size - 1) + 4 + 3 - 1
    omega
  -- Output register of `outer` is `⟨1, _⟩`.
  have h_outputReg : outer.outputReg
      = (⟨1, by
        have : 0 < frag_f.numRegs := frag_f.numRegs_pos
        change 1 < (k + 7) + frag_f.numRegs
        omega⟩ : Fin outer.numRegs) := Fin.ext rfl
  -- Final assembly: provide T0 = T_partial + 1.
  refine ⟨T_partial + 1, ?_, ?_, ?_, ?_⟩
  · -- Runtime bound: T_partial + 1 ≤ compileER_runtime (.bsum f) v.
    -- Expand the runtime expression for .bsum f.
    have h_rt :
        compileER_runtime (.bsum f : ERMor1 (k + 1)) v
          = 30 + 10 * (v 0)
            + ((List.range (v 0)).map
                (fun j => compileER_runtime f
                    (Fin.cons j (Fin.tail v))
                  + 50 + 2 * (k + 1) + 10 * (j +
                    ((List.finRange k).map (Fin.tail v)).foldl
                      (· + ·) 0)
                  + 5 * f.interp (Fin.cons j (Fin.tail v))
                  + compileER_numRegs f)).foldl (· + ·) 0 := rfl
    rw [h_rt]
    -- The partial bound:
    --   T_partial ≤ (6 + 9 * v 0) + Σ perIter_actual j
    -- Want: T_partial + 1 ≤ 30 + 10 * v 0 + Σ perIter_runtime j.
    -- Strategy: aux foldl monotonicity over equal-length lists.
    have h_foldl_le : ∀ {β : Type} (l : List β) (g₁ g₂ : β → ℕ)
        (h_le : ∀ x ∈ l, g₁ x ≤ g₂ x) (acc₁ acc₂ : ℕ),
        acc₁ ≤ acc₂ →
        l.foldl (fun s x => s + g₁ x) acc₁
          ≤ l.foldl (fun s x => s + g₂ x) acc₂ := by
      intro β l
      induction l with
      | nil =>
        intro _ _ _ _ _ h
        exact h
      | cons hd tl ih =>
        intro g₁ g₂ h_le acc₁ acc₂ h_acc
        change tl.foldl _ (acc₁ + g₁ hd)
          ≤ tl.foldl _ (acc₂ + g₂ hd)
        apply ih
        · intro x hx; exact h_le x (List.mem_cons_of_mem _ hx)
        · have h_hd := h_le hd (List.mem_cons_self)
          omega
    have h_foldl_map_eq : ∀ {β : Type} (l : List β) (g : β → ℕ)
        (acc : ℕ),
        (l.map g).foldl (· + ·) acc
          = l.foldl (fun s x => s + g x) acc := by
      intro β l
      induction l with
      | nil => intro _ _; rfl
      | cons hd tl ih =>
        intro g acc
        change (tl.map g).foldl (· + ·) (acc + g hd)
          = tl.foldl _ (acc + g hd)
        exact ih g (acc + g hd)
    rw [h_foldl_map_eq]
    rw [h_foldl_map_eq] at hT_partial_bound
    -- vPrefixSum (Fin.cons j (Fin.tail v)) (k+1) = j + outerSum.
    have h_outerSum_eq :
        ∀ j : ℕ,
        vPrefixSum (Fin.cons j (Fin.tail v)) (k + 1)
          = j + ((List.finRange k).map (Fin.tail v)).foldl
              (· + ·) 0 := by
      intro j
      have h_vps_eq :
          vPrefixSum (Fin.cons j (Fin.tail v)) (k + 1)
            = j + vPrefixSum (Fin.tail v) k := by
        have h_step :
            ∀ n : ℕ, n ≤ k →
              vPrefixSum (Fin.cons j (Fin.tail v)) (n + 1)
                = j + vPrefixSum (Fin.tail v) n := by
          intro n hn
          induction n with
          | zero =>
            have h_pos : 0 < k + 1 := Nat.succ_pos k
            have h_cons_zero :
                (Fin.cons j (Fin.tail v) : Fin (k + 1) → ℕ)
                  ⟨0, h_pos⟩ = j := by
              change Fin.cons j (Fin.tail v) 0 = j
              rfl
            calc
              vPrefixSum (Fin.cons j (Fin.tail v)) 1
                  = vPrefixSum (Fin.cons j (Fin.tail v)) 0
                    + (Fin.cons j (Fin.tail v)) ⟨0, h_pos⟩ :=
                  vPrefixSum_succ (Fin.cons j (Fin.tail v)) 0 h_pos
              _ = 0 + (Fin.cons j (Fin.tail v)) ⟨0, h_pos⟩ := rfl
              _ = 0 + j := by rw [h_cons_zero]
              _ = j + vPrefixSum (Fin.tail v) 0 := by
                change 0 + j = j + 0
                omega
          | succ n' ih =>
            have hn' : n' ≤ k := Nat.le_of_succ_le hn
            have hn'_lt : n' < k := hn
            have hn_lt : n' + 1 < k + 1 := Nat.succ_lt_succ hn'_lt
            have h_ih := ih hn'
            have h_cons_succ :
                (Fin.cons j (Fin.tail v) : Fin (k + 1) → ℕ)
                    ⟨n' + 1, hn_lt⟩
                  = (Fin.tail v) ⟨n', hn'_lt⟩ := by
              have h_eq : (⟨n' + 1, hn_lt⟩ : Fin (k + 1))
                  = (⟨n', hn'_lt⟩ : Fin k).succ := by
                apply Fin.ext; rfl
              rw [h_eq, Fin.cons_succ]
            calc
              vPrefixSum (Fin.cons j (Fin.tail v)) (n' + 1 + 1)
                  = vPrefixSum (Fin.cons j (Fin.tail v)) (n' + 1)
                    + (Fin.cons j (Fin.tail v)) ⟨n' + 1, hn_lt⟩ :=
                  vPrefixSum_succ (Fin.cons j (Fin.tail v))
                    (n' + 1) hn_lt
              _ = (j + vPrefixSum (Fin.tail v) n')
                  + (Fin.tail v) ⟨n', hn'_lt⟩ := by
                rw [h_ih, h_cons_succ]
              _ = j + (vPrefixSum (Fin.tail v) n'
                  + (Fin.tail v) ⟨n', hn'_lt⟩) := by omega
              _ = j + vPrefixSum (Fin.tail v) (n' + 1) := by
                rw [vPrefixSum_succ (Fin.tail v) n' hn'_lt]
        exact h_step k (Nat.le_refl k)
      have h_outerSum_eq_foldl :
          vPrefixSum (Fin.tail v) k
            = ((List.finRange k).map (Fin.tail v)).foldl (· + ·) 0 :=
        vPrefixSum_eq_foldl_finRange (Fin.tail v)
      rw [h_vps_eq, h_outerSum_eq_foldl]
    -- Per-iteration ≤ comparison.
    have h_numRegs_eq_f :
        compileER_numRegs f = (compileERFrag f).numRegs :=
      compileER_numRegs_eq_compileERFrag_numRegs f
    have h_g_le : ∀ j ∈ List.range (v 0),
        (2 + (compileERFrag f).numRegs)
            + (9 * vPrefixSum (Fin.cons j (Fin.tail v)) (k + 1)
                + 2 * (k + 1))
            + compileER_runtime f (Fin.cons j (Fin.tail v))
            + (4 * f.interp (Fin.cons j (Fin.tail v)) + 3)
          ≤ compileER_runtime f (Fin.cons j (Fin.tail v))
              + 50 + 2 * (k + 1)
              + 10 * (j +
                ((List.finRange k).map (Fin.tail v)).foldl
                  (· + ·) 0)
              + 5 * f.interp (Fin.cons j (Fin.tail v))
              + compileER_numRegs f := by
      intro j _
      have h_vps := h_outerSum_eq j
      have h_nR := h_numRegs_eq_f
      omega
    have h_main :=
      h_foldl_le (List.range (v 0)) _ _ h_g_le 0 0 (Nat.le_refl 0)
    -- Combine main bound with the constant slack.
    omega
  · -- PC after T_partial + 1 = (compileFrag_bsum frag_f).instrs.size - 1.
    change sFinal.pc = (compileFrag_bsum frag_f).instrs.size - 1
    rw [h_sFinal_decomp, h_step_final]
    change exitPC_lit = (compileFrag_bsum frag_f).instrs.size - 1
    exact h_exitPC_eq_size_pred
  · -- Output register holds (.bsum f).interp v.
    change sFinal.regs outer.outputReg = (.bsum f : ERMor1 (k + 1)).interp v
    rw [h_sFinal_decomp, h_step_final, h_outputReg]
    -- After the jumpZ, regs are unchanged. Use h_inv.acc_eq.
    change sPost.regs ⟨1, _⟩ = (.bsum f : ERMor1 (k + 1)).interp v
    have h_acc := h_inv.acc_eq
    rw [h_acc]
    -- natBSum (v 0) ... = (.bsum f).interp v.
    rfl
  · -- Strict PC bound on [0, T_partial + 1).
    intro k' hk'
    change (URMState.runFor outer s_init k').pc
      < (compileFrag_bsum frag_f).instrs.size - 1
    rcases Nat.lt_or_ge k' T_partial with h_lo | h_hi
    · exact h_strict_partial k' h_lo
    · -- k' = T_partial: PC = 13 < instrs.size - 1.
      have h_k'_eq : k' = T_partial := by omega
      rw [h_k'_eq]
      change sPost.pc < (compileFrag_bsum frag_f).instrs.size - 1
      rw [h_sPost_pc, ← h_exitPC_eq_size_pred]
      have h_size_pos : 0 < frag_f.instrs.size := by
        have hb := frag_f.lastInstr_isStop
        rcases Nat.eq_zero_or_pos frag_f.instrs.size with h_eq | h_pos
        · exfalso
          rw [Array.back?] at hb
          have h_none : frag_f.instrs[frag_f.instrs.size - 1]? = none := by
            apply Array.getElem?_eq_none; omega
          rw [h_none] at hb
          cases hb
        · exact h_pos
      change 13 < 15 + frag_f.numRegs + 9 * (k + 1)
        + (frag_f.instrs.size - 1) + 6
      omega

/-- `≤ t'`-form wrapper around `compileER_pre_stop_correct_bsum`,
analogue of `compileER_runFor_comp`. Given the pre-stop inductive
hypothesis for `f`, running `compileER (.bsum f)` for any
`t' ≥ compileER_runtime (.bsum f) v` produces `(.bsum f).interp v`
in the output register. -/
private theorem compileER_runFor_bsum {k : ℕ}
    (f : ERMor1 (k + 1))
    (ih_f : ∀ (v' : Fin (k + 1) → ℕ),
      ∃ T0 : ℕ,
        T0 ≤ compileER_runtime f v' ∧
        (URMState.runFor (compileER f)
              (URMState.init (compileER f) v') T0).pc
            = (compileER f).instrs.size - 1 ∧
        (URMState.runFor (compileER f)
              (URMState.init (compileER f) v') T0).regs
            (compileER f).outputReg
          = f.interp v' ∧
        (∀ k' < T0,
          (URMState.runFor (compileER f)
              (URMState.init (compileER f) v') k').pc
            < (compileER f).instrs.size - 1))
    (v : Fin (k + 1) → ℕ) (t' : ℕ)
    (ht' : compileER_runtime (.bsum f : ERMor1 (k + 1)) v ≤ t') :
    (URMState.runFor (compileER (.bsum f : ERMor1 (k + 1)))
        (URMState.init (compileER (.bsum f : ERMor1 (k + 1))) v) t').regs
        (compileER (.bsum f : ERMor1 (k + 1))).outputReg
      = (.bsum f : ERMor1 (k + 1)).interp v := by
  obtain ⟨T0, hT0, h_pc, h_out, _⟩ :=
    compileER_pre_stop_correct_bsum f ih_f v
  exact compileER_pre_stop_to_runFor _ v t' ht' ⟨T0, hT0, h_pc, h_out⟩

end LawvereERKSim
end GebLean
