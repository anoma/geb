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

end LawvereERKSim
end GebLean
