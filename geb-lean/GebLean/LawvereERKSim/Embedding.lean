import GebLean.LawvereERKSim.Compiler

/-!
# LawvereERKSim — runtime embedding and the pre-stop bridge

Step-relation lemmas and the `ProgramEmbedsFragment` / `StateEmbedsFrag` framework
used to lift correctness from sub-fragment to enclosing program. Plus the
constructor-agnostic `compileER_pre_stop_to_runFor` bridge that converts the
existential pre-stop form (∃ T₀ ≤ runtime witness, PC at size-1, output correct)
to the output-only `≤ t'` form.

## Main definitions

- `ProgramEmbedsFragment` (structure): predicate asserting that one URM
  program's instructions at PCs `pcBase ..+ L` realise another's.
- `StateEmbedsFrag` (def): per-state instance of `ProgramEmbedsFragment`
  carrying current PC and register alignment.

## Main statements

- `URMState.step_of_getElem?_{jumpZ,dec,inc,assign,stop}`,
  `getElem_of_getElem?_some`: helpers for stepping when the instruction at the
  current PC is known via `getElem?`.
- `stateEmbedsFrag_step`, `stateEmbedsFrag_runFor`: per-step and multi-step
  simulation under embedding.
- `stateEmbedsFrag_step_tail`, `stateEmbedsFrag_runFor_tail`: variants for
  sub-programs whose embedded code ends at the outer's tail.
- `stateEmbedsFrag_step_outside_preserved`,
  `stateEmbedsFrag_runFor_outside_preserved`: register preservation outside the
  embedded sub-program's register block.
- `compileER_runFor_pc_le_size`, `fragment_runFor_pc_le_size`: PC-in-range
  during bounded execution.
- `URMState.init_regs_zero_outside_inputs`: initial register block is zero
  outside the input slots.
- `compileER_pre_stop_to_runFor`: the constructor-agnostic bridge from
  existential pre-stop to `≤ t'` output form.

## References

- Spec: `docs/superpowers/specs/2026-05-19-lawvere-er-k-sim-file-split-design.md`.
-/

namespace GebLean
namespace LawvereERKSim

open GebLean.ZeroTestURM

/-- Convert a `getElem?` equality to an indexed `getElem`
plus the corresponding bound proof. Used to feed the
`step` function's `dif_pos`/`match` form from a hypothesis
stated with `[…]?`. -/
private theorem getElem_of_getElem?_some {α : Type*}
    (xs : Array α) (k : ℕ) (a : α)
    (h : xs[k]? = some a) :
    ∃ hk : k < xs.size, xs[k]'hk = a := by
  by_cases hk : k < xs.size
  · refine ⟨hk, ?_⟩
    rw [Array.getElem?_eq_getElem hk] at h
    exact Option.some.inj h
  · rw [Array.getElem?_eq_none (Nat.le_of_not_lt hk)] at h
    exact absurd h (by simp)

/-- One step from a state at PC `pcBase + k` whose
instruction lookup is hypothesised via `[…]?`. Used to
absorb each instruction in a `preservingTransfer` block
without unfolding the literal program. -/
theorem URMState.step_of_getElem?_jumpZ {a : ℕ}
    (P : URMProgram a) (s : URMState P) (k : ℕ)
    (i : Fin P.numRegs) (l₁ l₂ : ℕ)
    (h_pc : s.pc = k)
    (h_instr : P.instrs[k]? = some (.jumpZ i l₁ l₂)) :
    URMState.step P s =
      { pc := if s.regs i = 0 then l₁ else l₂
        regs := s.regs } := by
  obtain ⟨hk, h_eq⟩ := getElem_of_getElem?_some P.instrs k _ h_instr
  simp only [URMState.step, h_pc, dif_pos hk, h_eq]

theorem URMState.step_of_getElem?_dec {a : ℕ}
    (P : URMProgram a) (s : URMState P) (k : ℕ)
    (i : Fin P.numRegs)
    (h_pc : s.pc = k)
    (h_instr : P.instrs[k]? = some (.dec i)) :
    URMState.step P s =
      { pc := s.pc + 1
        regs := Function.update s.regs i (s.regs i - 1) } := by
  obtain ⟨hk, h_eq⟩ := getElem_of_getElem?_some P.instrs k _ h_instr
  simp only [URMState.step, h_pc, dif_pos hk, h_eq]

theorem URMState.step_of_getElem?_inc {a : ℕ}
    (P : URMProgram a) (s : URMState P) (k : ℕ)
    (i : Fin P.numRegs)
    (h_pc : s.pc = k)
    (h_instr : P.instrs[k]? = some (.inc i)) :
    URMState.step P s =
      { pc := s.pc + 1
        regs := Function.update s.regs i (s.regs i + 1) } := by
  obtain ⟨hk, h_eq⟩ := getElem_of_getElem?_some P.instrs k _ h_instr
  simp only [URMState.step, h_pc, dif_pos hk, h_eq]

/-- One step from a state at PC `pcBase + k` whose
instruction lookup is hypothesised via `[…]?` to be an
assign. -/
theorem URMState.step_of_getElem?_assign {a : ℕ}
    (P : URMProgram a) (s : URMState P) (k : ℕ)
    (i : Fin P.numRegs) (c : ℕ)
    (h_pc : s.pc = k)
    (h_instr : P.instrs[k]? = some (.assign i c)) :
    URMState.step P s =
      { pc := s.pc + 1
        regs := Function.update s.regs i c } := by
  obtain ⟨hk, h_eq⟩ := getElem_of_getElem?_some P.instrs k _ h_instr
  simp only [URMState.step, h_pc, dif_pos hk, h_eq]

/-- One step from a state at PC `pcBase + k` whose
instruction lookup is hypothesised via `[…]?` to be a
stop. The step is the identity. -/
private theorem URMState.step_of_getElem?_stop {a : ℕ}
    (P : URMProgram a) (s : URMState P) (k : ℕ)
    (h_pc : s.pc = k)
    (h_instr : P.instrs[k]? = some .stop) :
    URMState.step P s = s := by
  obtain ⟨hk, h_eq⟩ := getElem_of_getElem?_some P.instrs k _ h_instr
  simp only [URMState.step, h_pc, dif_pos hk, h_eq]

/-! ### Program-embedding lemmas

The following helpers state that a sub-fragment's
execution (standalone) corresponds to its execution
inside a larger program after `URMInstrRaw.reindexShift`
has been applied to its raw instructions. The shape is
parameterised by an embedded prefix length `L` (so
combinators that splice in `frag.instrs.pop` — dropping
the trailing stop — can use `L = frag.instrs.size - 1`,
while combinators that keep the stop use `L = frag.instrs.size`).

Used by `compileER_runFor_{comp,bsum,bprod}` to apply
the inductive hypothesis to a sub-fragment's run after
register-space injection and PC shifting. -/

/-- Predicate: `P_big`'s instructions at PCs
`pcOffset..pcOffset+L` encode the first `L` instructions
of `frag` reindex-shifted by `regOffset` (registers) and
`pcOffset` (jump targets). The flat `∀ i hi hL hR, …`
shape avoids nested `∧` so dependent proof obligations
inside the instruction-lookup equation can be discharged
locally. -/
structure ProgramEmbedsFragment {a b : ℕ}
    (P_big : URMProgram b) (frag : CompiledFragment a)
    (regOffset pcOffset L : ℕ) : Prop where
  hL : L ≤ frag.instrs.size
  hReg : regOffset + frag.numRegs ≤ P_big.numRegs
  hInstr : ∀ (i : ℕ) (hi : i < L),
    P_big.instrs[pcOffset + i]? =
      some (URMInstrRaw.toBounded P_big.numRegs
        (URMInstrRaw.reindexShift regOffset pcOffset
          (toRawOfBounded
            (frag.instrs[i]'(Nat.lt_of_lt_of_le hi hL))))
        (Nat.le_trans
          (regBound_reindexShift_le_offset_add regOffset pcOffset
            frag.numRegs _
            (regBound_toRawOfBounded_le _))
          hReg))

/-- States match under embedding: `s_big`'s PC is the
shifted form of `s_frag`'s PC, and registers in the
embedded block match. Other registers of `s_big` are
unconstrained. -/
def StateEmbedsFrag {a b : ℕ}
    {P_big : URMProgram b} {frag : CompiledFragment a}
    (s_big : URMState P_big) (s_frag : URMState frag.toURMProgram)
    (regOffset pcOffset : ℕ)
    (hReg : regOffset + frag.numRegs ≤ P_big.numRegs) : Prop :=
  s_big.pc = pcOffset + s_frag.pc ∧
  ∀ (j : ℕ) (hj : j < frag.numRegs),
    s_big.regs ⟨regOffset + j,
        Nat.lt_of_lt_of_le (Nat.add_lt_add_left hj _) hReg⟩
      = s_frag.regs ⟨j, hj⟩

/-- Per-step simulation: under the embedding, one step
from a matching state lands on a matching state, provided
`s_frag.pc < L` (the embedded region covers the current
instruction). -/
private theorem stateEmbedsFrag_step {a b : ℕ}
    (P_big : URMProgram b) (frag : CompiledFragment a)
    (regOffset pcOffset L : ℕ)
    (h_emb_prog :
      ProgramEmbedsFragment P_big frag regOffset pcOffset L)
    (s_big : URMState P_big) (s_frag : URMState frag.toURMProgram)
    (h_match :
      StateEmbedsFrag s_big s_frag regOffset pcOffset
        h_emb_prog.hReg)
    (h_pc_in : s_frag.pc < L) :
    StateEmbedsFrag (URMState.step P_big s_big)
        (URMState.step frag.toURMProgram s_frag)
        regOffset pcOffset h_emb_prog.hReg := by
  obtain ⟨hL, hReg, hInstr⟩ := h_emb_prog
  obtain ⟨h_pc, h_regs⟩ := h_match
  have hfrag_lt : s_frag.pc < frag.instrs.size :=
    Nat.lt_of_lt_of_le h_pc_in hL
  -- P_big's instruction at s_big.pc via the embedding.
  have h_big_instr_raw :
      P_big.instrs[s_big.pc]? =
        some (URMInstrRaw.toBounded P_big.numRegs
          (URMInstrRaw.reindexShift regOffset pcOffset
            (toRawOfBounded (frag.instrs[s_frag.pc]'hfrag_lt)))
          (Nat.le_trans
            (regBound_reindexShift_le_offset_add regOffset
              pcOffset frag.numRegs _
              (regBound_toRawOfBounded_le _))
            hReg)) := by
    rw [h_pc]
    exact hInstr s_frag.pc h_pc_in
  -- Pointwise Fin equality / inequality helpers.
  have h_fin_idx : ∀ (j : ℕ) (hj : j < frag.numRegs)
      (i : Fin frag.numRegs), j = i.val →
      (⟨regOffset + j,
        Nat.lt_of_lt_of_le (Nat.add_lt_add_left hj _) hReg⟩ :
        Fin P_big.numRegs) =
      ⟨regOffset + i.val,
        Nat.lt_of_lt_of_le (Nat.add_lt_add_left i.isLt _) hReg⟩ := by
    intro j hj i hji
    apply Fin.ext; change regOffset + j = regOffset + i.val
    omega
  -- Case-split on frag's current instruction.
  match hcase : frag.instrs[s_frag.pc]'hfrag_lt with
  | .assign i c =>
    -- frag step: pc + 1, regs := update s_frag.regs i c
    have h_frag_step :
        URMState.step frag.toURMProgram s_frag =
          { pc := s_frag.pc + 1
            regs := Function.update s_frag.regs i c } := by
      simp only [URMState.step, dif_pos hfrag_lt, hcase]
    have hi_lt : i.val < frag.numRegs := i.isLt
    have h_big_idx_lt : regOffset + i.val < P_big.numRegs :=
      Nat.lt_of_lt_of_le (Nat.add_lt_add_left hi_lt _) hReg
    have h_big_instr :
        P_big.instrs[s_big.pc]? =
          some (.assign ⟨regOffset + i.val, h_big_idx_lt⟩ c) := by
      rw [h_big_instr_raw]
      congr 1
      rw [hcase]
      rfl
    have h_big_step :
        URMState.step P_big s_big =
          { pc := s_big.pc + 1
            regs := Function.update s_big.regs
              ⟨regOffset + i.val, h_big_idx_lt⟩ c } :=
      URMState.step_of_getElem?_assign P_big s_big s_big.pc _ c
        rfl h_big_instr
    refine ⟨?_, ?_⟩
    · rw [h_big_step, h_frag_step, h_pc]
      simp [Nat.add_assoc]
    · intro j hj
      rw [h_big_step, h_frag_step]
      simp only [Function.update_apply]
      by_cases hji : j = i.val
      · have h_big_eq := h_fin_idx j hj i hji
        have h_frag_eq : (⟨j, hj⟩ : Fin frag.numRegs) = i :=
          Fin.ext hji
        simp [h_big_eq, h_frag_eq]
      · have h_big_ne :
            (⟨regOffset + j,
              Nat.lt_of_lt_of_le (Nat.add_lt_add_left hj _)
                hReg⟩ : Fin P_big.numRegs) ≠
            ⟨regOffset + i.val, h_big_idx_lt⟩ := by
          intro he
          apply hji
          have : regOffset + j = regOffset + i.val :=
            congrArg Fin.val he
          omega
        have h_frag_ne : (⟨j, hj⟩ : Fin frag.numRegs) ≠ i := by
          intro he; apply hji; exact congrArg Fin.val he
        simp [h_big_ne, h_frag_ne, h_regs j hj]
  | .inc i =>
    have h_frag_step :
        URMState.step frag.toURMProgram s_frag =
          { pc := s_frag.pc + 1
            regs := Function.update s_frag.regs i
              (s_frag.regs i + 1) } := by
      simp only [URMState.step, dif_pos hfrag_lt, hcase]
    have hi_lt : i.val < frag.numRegs := i.isLt
    have h_big_idx_lt : regOffset + i.val < P_big.numRegs :=
      Nat.lt_of_lt_of_le (Nat.add_lt_add_left hi_lt _) hReg
    have h_big_instr :
        P_big.instrs[s_big.pc]? =
          some (.inc ⟨regOffset + i.val, h_big_idx_lt⟩) := by
      rw [h_big_instr_raw]
      congr 1
      rw [hcase]
      rfl
    have h_regs_at_i :
        s_big.regs ⟨regOffset + i.val, h_big_idx_lt⟩
          = s_frag.regs i := h_regs i.val hi_lt
    have h_big_step :
        URMState.step P_big s_big =
          { pc := s_big.pc + 1
            regs := Function.update s_big.regs
              ⟨regOffset + i.val, h_big_idx_lt⟩
              (s_big.regs ⟨regOffset + i.val, h_big_idx_lt⟩
                + 1) } :=
      URMState.step_of_getElem?_inc P_big s_big s_big.pc _
        rfl h_big_instr
    refine ⟨?_, ?_⟩
    · rw [h_big_step, h_frag_step, h_pc]
      simp [Nat.add_assoc]
    · intro j hj
      rw [h_big_step, h_frag_step]
      simp only [Function.update_apply]
      by_cases hji : j = i.val
      · have h_big_eq := h_fin_idx j hj i hji
        have h_frag_eq : (⟨j, hj⟩ : Fin frag.numRegs) = i :=
          Fin.ext hji
        simp [h_big_eq, h_frag_eq, h_regs_at_i]
      · have h_big_ne :
            (⟨regOffset + j,
              Nat.lt_of_lt_of_le (Nat.add_lt_add_left hj _)
                hReg⟩ : Fin P_big.numRegs) ≠
            ⟨regOffset + i.val, h_big_idx_lt⟩ := by
          intro he
          apply hji
          have : regOffset + j = regOffset + i.val :=
            congrArg Fin.val he
          omega
        have h_frag_ne : (⟨j, hj⟩ : Fin frag.numRegs) ≠ i := by
          intro he; apply hji; exact congrArg Fin.val he
        simp [h_big_ne, h_frag_ne, h_regs j hj]
  | .dec i =>
    have h_frag_step :
        URMState.step frag.toURMProgram s_frag =
          { pc := s_frag.pc + 1
            regs := Function.update s_frag.regs i
              (s_frag.regs i - 1) } := by
      simp only [URMState.step, dif_pos hfrag_lt, hcase]
    have hi_lt : i.val < frag.numRegs := i.isLt
    have h_big_idx_lt : regOffset + i.val < P_big.numRegs :=
      Nat.lt_of_lt_of_le (Nat.add_lt_add_left hi_lt _) hReg
    have h_big_instr :
        P_big.instrs[s_big.pc]? =
          some (.dec ⟨regOffset + i.val, h_big_idx_lt⟩) := by
      rw [h_big_instr_raw]
      congr 1
      rw [hcase]
      rfl
    have h_regs_at_i :
        s_big.regs ⟨regOffset + i.val, h_big_idx_lt⟩
          = s_frag.regs i := h_regs i.val hi_lt
    have h_big_step :
        URMState.step P_big s_big =
          { pc := s_big.pc + 1
            regs := Function.update s_big.regs
              ⟨regOffset + i.val, h_big_idx_lt⟩
              (s_big.regs ⟨regOffset + i.val, h_big_idx_lt⟩
                - 1) } :=
      URMState.step_of_getElem?_dec P_big s_big s_big.pc _
        rfl h_big_instr
    refine ⟨?_, ?_⟩
    · rw [h_big_step, h_frag_step, h_pc]
      simp [Nat.add_assoc]
    · intro j hj
      rw [h_big_step, h_frag_step]
      simp only [Function.update_apply]
      by_cases hji : j = i.val
      · have h_big_eq := h_fin_idx j hj i hji
        have h_frag_eq : (⟨j, hj⟩ : Fin frag.numRegs) = i :=
          Fin.ext hji
        simp [h_big_eq, h_frag_eq, h_regs_at_i]
      · have h_big_ne :
            (⟨regOffset + j,
              Nat.lt_of_lt_of_le (Nat.add_lt_add_left hj _)
                hReg⟩ : Fin P_big.numRegs) ≠
            ⟨regOffset + i.val, h_big_idx_lt⟩ := by
          intro he
          apply hji
          have : regOffset + j = regOffset + i.val :=
            congrArg Fin.val he
          omega
        have h_frag_ne : (⟨j, hj⟩ : Fin frag.numRegs) ≠ i := by
          intro he; apply hji; exact congrArg Fin.val he
        simp [h_big_ne, h_frag_ne, h_regs j hj]
  | .jumpZ i l₁ l₂ =>
    have h_frag_step :
        URMState.step frag.toURMProgram s_frag =
          { pc := if s_frag.regs i = 0 then l₁ else l₂
            regs := s_frag.regs } := by
      simp only [URMState.step, dif_pos hfrag_lt, hcase]
    have hi_lt : i.val < frag.numRegs := i.isLt
    have h_big_idx_lt : regOffset + i.val < P_big.numRegs :=
      Nat.lt_of_lt_of_le (Nat.add_lt_add_left hi_lt _) hReg
    have h_big_instr :
        P_big.instrs[s_big.pc]? =
          some (.jumpZ ⟨regOffset + i.val, h_big_idx_lt⟩
            (pcOffset + l₁) (pcOffset + l₂)) := by
      rw [h_big_instr_raw]
      congr 1
      rw [hcase]
      rfl
    have h_regs_at_i :
        s_big.regs ⟨regOffset + i.val, h_big_idx_lt⟩
          = s_frag.regs i := h_regs i.val hi_lt
    have h_big_step :
        URMState.step P_big s_big =
          { pc := if s_big.regs ⟨regOffset + i.val, h_big_idx_lt⟩ = 0
                  then pcOffset + l₁ else pcOffset + l₂
            regs := s_big.regs } :=
      URMState.step_of_getElem?_jumpZ P_big s_big s_big.pc _
        _ _ rfl h_big_instr
    refine ⟨?_, ?_⟩
    · rw [h_big_step, h_frag_step]
      simp only [h_regs_at_i]
      by_cases hi0 : s_frag.regs i = 0
      · simp [hi0]
      · simp [hi0]
    · intro j hj
      rw [h_big_step, h_frag_step]
      exact h_regs j hj
  | .stop =>
    have h_frag_step :
        URMState.step frag.toURMProgram s_frag = s_frag := by
      simp only [URMState.step, dif_pos hfrag_lt, hcase]
    have h_big_instr : P_big.instrs[s_big.pc]? = some .stop := by
      rw [h_big_instr_raw]
      congr 1
      rw [hcase]
      rfl
    have h_big_step : URMState.step P_big s_big = s_big :=
      URMState.step_of_getElem?_stop P_big s_big s_big.pc
        rfl h_big_instr
    rw [h_big_step, h_frag_step]
    exact ⟨h_pc, h_regs⟩

/-- Multi-step embedding: if `s_frag`'s PC stays `< L`
during the first `T` steps, then `T` steps of `P_big`
mirror `T` steps of `frag` (state matches via the
embedding). -/
theorem stateEmbedsFrag_runFor {a b : ℕ}
    (P_big : URMProgram b) (frag : CompiledFragment a)
    (regOffset pcOffset L : ℕ)
    (h_emb_prog :
      ProgramEmbedsFragment P_big frag regOffset pcOffset L)
    (s_big : URMState P_big) (s_frag : URMState frag.toURMProgram)
    (h_match :
      StateEmbedsFrag s_big s_frag regOffset pcOffset
        h_emb_prog.hReg)
    (T : ℕ)
    (h_in_range : ∀ k, k < T →
      (URMState.runFor frag.toURMProgram s_frag k).pc < L) :
    StateEmbedsFrag (URMState.runFor P_big s_big T)
        (URMState.runFor frag.toURMProgram s_frag T)
        regOffset pcOffset h_emb_prog.hReg := by
  induction T generalizing s_big s_frag with
  | zero => exact h_match
  | succ T ih =>
    have h0 : s_frag.pc < L := by
      have := h_in_range 0 (Nat.succ_pos T)
      simpa [URMState.runFor] using this
    have h_step :=
      stateEmbedsFrag_step P_big frag regOffset pcOffset L
        h_emb_prog s_big s_frag h_match h0
    rw [URMState.runFor_succ, URMState.runFor_succ]
    refine ih (URMState.step P_big s_big)
      (URMState.step frag.toURMProgram s_frag) h_step ?_
    intro k hk
    have hk1 : k + 1 < T + 1 := Nat.succ_lt_succ hk
    have := h_in_range (k + 1) hk1
    simp only [URMState.runFor] at this
    exact this

/-- One step of `P_big` from a state matching `s_frag` at
`s_frag.pc < L` preserves any register outside the embedded
block `[regOffset, regOffset + frag.numRegs)`. -/
private theorem stateEmbedsFrag_step_outside_preserved
    {a b : ℕ}
    (P_big : URMProgram b) (frag : CompiledFragment a)
    (s_big : URMState P_big) (s_frag : URMState frag.toURMProgram)
    (regOffset pcOffset L : ℕ)
    (h_embed : ProgramEmbedsFragment P_big frag regOffset pcOffset L)
    (h_state :
      StateEmbedsFrag s_big s_frag regOffset pcOffset h_embed.hReg)
    (h_pc_lt_L : s_frag.pc < L)
    (r : Fin P_big.numRegs)
    (h_outside :
      r.val < regOffset ∨ regOffset + frag.numRegs ≤ r.val) :
    (URMState.step P_big s_big).regs r = s_big.regs r := by
  obtain ⟨hL, hReg, hInstr⟩ := h_embed
  obtain ⟨h_pc, _h_regs⟩ := h_state
  have hfrag_lt : s_frag.pc < frag.instrs.size :=
    Nat.lt_of_lt_of_le h_pc_lt_L hL
  have h_big_instr_raw :
      P_big.instrs[s_big.pc]? =
        some (URMInstrRaw.toBounded P_big.numRegs
          (URMInstrRaw.reindexShift regOffset pcOffset
            (toRawOfBounded (frag.instrs[s_frag.pc]'hfrag_lt)))
          (Nat.le_trans
            (regBound_reindexShift_le_offset_add regOffset
              pcOffset frag.numRegs _
              (regBound_toRawOfBounded_le _))
            hReg)) := by
    rw [h_pc]
    exact hInstr s_frag.pc h_pc_lt_L
  -- Inside-the-block indices differ from `r` (`r.val` is outside).
  have h_ne_of_inside :
      ∀ (i : Fin frag.numRegs)
        (h_idx_lt : regOffset + i.val < P_big.numRegs),
        (⟨regOffset + i.val, h_idx_lt⟩ : Fin P_big.numRegs) ≠ r := by
    intro i h_idx_lt he
    have hval : regOffset + i.val = r.val := congrArg Fin.val he
    rcases h_outside with hlt | hge
    · have : regOffset + i.val < regOffset := hval ▸ hlt
      omega
    · have hi_lt : i.val < frag.numRegs := i.isLt
      have : regOffset + frag.numRegs ≤ regOffset + i.val :=
        hval ▸ hge
      omega
  match hcase : frag.instrs[s_frag.pc]'hfrag_lt with
  | .assign i c =>
    have hi_lt : i.val < frag.numRegs := i.isLt
    have h_big_idx_lt : regOffset + i.val < P_big.numRegs :=
      Nat.lt_of_lt_of_le (Nat.add_lt_add_left hi_lt _) hReg
    have h_big_instr :
        P_big.instrs[s_big.pc]? =
          some (.assign ⟨regOffset + i.val, h_big_idx_lt⟩ c) := by
      rw [h_big_instr_raw]
      congr 1
      rw [hcase]
      rfl
    have h_big_step :
        URMState.step P_big s_big =
          { pc := s_big.pc + 1
            regs := Function.update s_big.regs
              ⟨regOffset + i.val, h_big_idx_lt⟩ c } :=
      URMState.step_of_getElem?_assign P_big s_big s_big.pc _ c
        rfl h_big_instr
    rw [h_big_step]
    exact Function.update_of_ne (h_ne_of_inside i h_big_idx_lt).symm _ _
  | .inc i =>
    have hi_lt : i.val < frag.numRegs := i.isLt
    have h_big_idx_lt : regOffset + i.val < P_big.numRegs :=
      Nat.lt_of_lt_of_le (Nat.add_lt_add_left hi_lt _) hReg
    have h_big_instr :
        P_big.instrs[s_big.pc]? =
          some (.inc ⟨regOffset + i.val, h_big_idx_lt⟩) := by
      rw [h_big_instr_raw]
      congr 1
      rw [hcase]
      rfl
    have h_big_step :
        URMState.step P_big s_big =
          { pc := s_big.pc + 1
            regs := Function.update s_big.regs
              ⟨regOffset + i.val, h_big_idx_lt⟩
              (s_big.regs ⟨regOffset + i.val, h_big_idx_lt⟩
                + 1) } :=
      URMState.step_of_getElem?_inc P_big s_big s_big.pc _
        rfl h_big_instr
    rw [h_big_step]
    exact Function.update_of_ne (h_ne_of_inside i h_big_idx_lt).symm _ _
  | .dec i =>
    have hi_lt : i.val < frag.numRegs := i.isLt
    have h_big_idx_lt : regOffset + i.val < P_big.numRegs :=
      Nat.lt_of_lt_of_le (Nat.add_lt_add_left hi_lt _) hReg
    have h_big_instr :
        P_big.instrs[s_big.pc]? =
          some (.dec ⟨regOffset + i.val, h_big_idx_lt⟩) := by
      rw [h_big_instr_raw]
      congr 1
      rw [hcase]
      rfl
    have h_big_step :
        URMState.step P_big s_big =
          { pc := s_big.pc + 1
            regs := Function.update s_big.regs
              ⟨regOffset + i.val, h_big_idx_lt⟩
              (s_big.regs ⟨regOffset + i.val, h_big_idx_lt⟩
                - 1) } :=
      URMState.step_of_getElem?_dec P_big s_big s_big.pc _
        rfl h_big_instr
    rw [h_big_step]
    exact Function.update_of_ne (h_ne_of_inside i h_big_idx_lt).symm _ _
  | .jumpZ i l₁ l₂ =>
    have hi_lt : i.val < frag.numRegs := i.isLt
    have h_big_idx_lt : regOffset + i.val < P_big.numRegs :=
      Nat.lt_of_lt_of_le (Nat.add_lt_add_left hi_lt _) hReg
    have h_big_instr :
        P_big.instrs[s_big.pc]? =
          some (.jumpZ ⟨regOffset + i.val, h_big_idx_lt⟩
            (pcOffset + l₁) (pcOffset + l₂)) := by
      rw [h_big_instr_raw]
      congr 1
      rw [hcase]
      rfl
    have h_big_step :
        URMState.step P_big s_big =
          { pc := if s_big.regs ⟨regOffset + i.val, h_big_idx_lt⟩ = 0
                  then pcOffset + l₁ else pcOffset + l₂
            regs := s_big.regs } :=
      URMState.step_of_getElem?_jumpZ P_big s_big s_big.pc _
        _ _ rfl h_big_instr
    rw [h_big_step]
  | .stop =>
    have h_big_instr : P_big.instrs[s_big.pc]? = some .stop := by
      rw [h_big_instr_raw]
      congr 1
      rw [hcase]
      rfl
    have h_big_step : URMState.step P_big s_big = s_big :=
      URMState.step_of_getElem?_stop P_big s_big s_big.pc
        rfl h_big_instr
    rw [h_big_step]

/-- Running `P_big` for `T` steps from a state matching
`s_frag` preserves any register outside the embedded block,
provided `s_frag`'s PC stays `< L` throughout. -/
theorem stateEmbedsFrag_runFor_outside_preserved
    {a b : ℕ}
    (P_big : URMProgram b) (frag : CompiledFragment a)
    (s_big : URMState P_big) (s_frag : URMState frag.toURMProgram)
    (regOffset pcOffset L : ℕ)
    (h_embed : ProgramEmbedsFragment P_big frag regOffset pcOffset L)
    (h_state :
      StateEmbedsFrag s_big s_frag regOffset pcOffset h_embed.hReg)
    (T : ℕ)
    (h_in_range : ∀ k, k < T →
      (URMState.runFor frag.toURMProgram s_frag k).pc < L)
    (r : Fin P_big.numRegs)
    (h_outside :
      r.val < regOffset ∨ regOffset + frag.numRegs ≤ r.val) :
    (URMState.runFor P_big s_big T).regs r = s_big.regs r := by
  induction T generalizing s_big s_frag with
  | zero => rfl
  | succ T ih =>
    have h0 : s_frag.pc < L := by
      have := h_in_range 0 (Nat.succ_pos T)
      simpa [URMState.runFor] using this
    have h_step_state :
        StateEmbedsFrag (URMState.step P_big s_big)
            (URMState.step frag.toURMProgram s_frag)
            regOffset pcOffset h_embed.hReg :=
      stateEmbedsFrag_step P_big frag regOffset pcOffset L
        h_embed s_big s_frag h_state h0
    have h_step_outside :
        (URMState.step P_big s_big).regs r = s_big.regs r :=
      stateEmbedsFrag_step_outside_preserved P_big frag s_big s_frag
        regOffset pcOffset L h_embed h_state h0 r h_outside
    have h_in_range' : ∀ k, k < T →
        (URMState.runFor frag.toURMProgram
          (URMState.step frag.toURMProgram s_frag) k).pc < L := by
      intro k hk
      have hk1 : k + 1 < T + 1 := Nat.succ_lt_succ hk
      have := h_in_range (k + 1) hk1
      simp only [URMState.runFor] at this
      exact this
    rw [URMState.runFor_succ]
    rw [ih (URMState.step P_big s_big)
          (URMState.step frag.toURMProgram s_frag)
          h_step_state h_in_range']
    exact h_step_outside

/-! ### PC-in-range for `compileER` outputs

`stateEmbedsFrag_runFor` requires a `pc < L`
hypothesis. The generic engine driving that hypothesis is
`ZeroTestURM.URMState.runFor_pc_le_size`, which gives a
`pc ≤ instrs.size` bound for any well-bounded program
starting from a PC inside the array-or-halt region.

The wrapper below specialises that generic lemma to
`compileER`-produced URMs starting from
`URMState.init (compileER e) v` (PC = 0). The
well-boundedness obligation
(`(compileER e).WellBounded`, i.e. every `jumpZ` target in
the emitted instructions is at most `instrs.size`) is
carried as an explicit hypothesis: the per-constructor
discharge of that obligation is a separate compositional
proof bundled with the corresponding
`compileER_runFor_*` lemma. -/

/-- For any well-bounded `compileER`-produced URM, running
for any number of steps from its `URMState.init` state
keeps the PC within `[0, instrs.size]`. Used by
`compileER_runFor_{comp,bsum,bprod}` to discharge the
`pc < L` precondition of `stateEmbedsFrag_runFor` after
deriving the strict bound from the per-step layout. -/
private theorem compileER_runFor_pc_le_size {a : ℕ}
    (e : ERMor1 a) (v : Fin a → ℕ) (n : ℕ)
    (h_well : (compileER e).WellBounded) :
    ((URMState.init (compileER e) v).runFor
        (compileER e) n).pc
      ≤ (compileER e).instrs.size := by
  apply URMState.runFor_pc_le_size (compileER e)
    (URMState.init (compileER e) v) h_well
  -- `URMState.init` has `pc = 0`, which is ≤ `instrs.size`.
  change (0 : ℕ) ≤ (compileER e).instrs.size
  exact Nat.zero_le _

/-- For a well-bounded standalone fragment, running it for
any number of steps from a state with PC inside the
array-or-halt region keeps the PC ≤ `instrs.size`. This
is the form consumed inside the inductive step of
`compileER_runFor_comp`'s sub-fragment runs, where the
fragment under analysis is a `compileERFrag` output and
the starting state is its `URMState.init` (PC = 0) or a
mid-execution state produced by a previous embedding
step. -/
private theorem fragment_runFor_pc_le_size {a : ℕ}
    (frag : CompiledFragment a) (s : URMState frag.toURMProgram)
    (h_well : frag.toURMProgram.WellBounded)
    (h_pc : s.pc ≤ frag.instrs.size) (n : ℕ) :
    (URMState.runFor frag.toURMProgram s n).pc
      ≤ frag.instrs.size :=
  URMState.runFor_pc_le_size frag.toURMProgram s h_well h_pc n
/-- For a `URMProgram` whose `inputRegs` maps slot `j` to
register index `2 + j.val`, the registers outside the
input image (specifically register 0, register 1, and
registers `≥ 2 + a`) are 0 in the `init` state.
Used by `compileER_runFor_comp` (and its `bsum`/`bprod`
analogues) to align the outer program's `URMState.init`
with the zero-initialised register block of an embedded
sub-fragment, whose register block lies above
`2 + a`. -/
theorem URMState.init_regs_zero_outside_inputs {a : ℕ}
    (P : URMProgram a) (v : Fin a → ℕ)
    (h_inputs : ∀ j : Fin a, (P.inputRegs j).val = 2 + j.val)
    (r : Fin P.numRegs)
    (h_outside : r.val = 0 ∨ r.val = 1 ∨ r.val ≥ 2 + a) :
    (URMState.init P v).regs r = 0 := by
  change
    (match (List.finRange a).find?
        (fun j => decide (P.inputRegs j = r)) with
      | some j => v j
      | none   => 0) = 0
  have h_none : (List.finRange a).find?
      (fun j => decide (P.inputRegs j = r)) = none := by
    apply List.find?_eq_none.mpr
    intro j _
    simp only [Bool.not_eq_true, decide_eq_false_iff_not]
    intro h
    have hval : (P.inputRegs j).val = r.val := congrArg Fin.val h
    rw [h_inputs j] at hval
    have hjlt : j.val < a := j.isLt
    rcases h_outside with hr | hr | hr <;> omega
  rw [h_none]

/-- Variant of `stateEmbedsFrag_step` for the case where
the embedded region is the tail of the outer program
(i.e., `pcOffset + L = P_big.instrs.size`). With this
condition, even at `s_frag.pc = L` (just past the embedded
region) the outer's `step` is identity (PC past the array
end) and so is the fragment's `step` (PC past its array
end), so the embedding is preserved.

This avoids the strict `s_frag.pc < L` precondition of
`stateEmbedsFrag_step`, accepting `s_frag.pc ≤ L` instead.
Used in `compileER_runFor_comp_k_zero` where the f-body
embedded region is the suffix of the outer program. -/
private theorem stateEmbedsFrag_step_tail {a b : ℕ}
    (P_big : URMProgram b) (frag : CompiledFragment a)
    (regOffset pcOffset L : ℕ)
    (h_emb_prog :
      ProgramEmbedsFragment P_big frag regOffset pcOffset L)
    (h_tail : pcOffset + L = P_big.instrs.size)
    (h_L_eq : L = frag.instrs.size)
    (s_big : URMState P_big) (s_frag : URMState frag.toURMProgram)
    (h_match :
      StateEmbedsFrag s_big s_frag regOffset pcOffset
        h_emb_prog.hReg)
    (h_pc_le : s_frag.pc ≤ L) :
    StateEmbedsFrag (URMState.step P_big s_big)
        (URMState.step frag.toURMProgram s_frag)
        regOffset pcOffset h_emb_prog.hReg := by
  rcases Nat.lt_or_eq_of_le h_pc_le with h_lt | h_eq
  · exact stateEmbedsFrag_step P_big frag regOffset pcOffset L
      h_emb_prog s_big s_frag h_match h_lt
  · -- s_frag.pc = L; both sides' step are identities (PC past end).
    obtain ⟨h_pc, h_regs⟩ := h_match
    have h_frag_step :
        URMState.step frag.toURMProgram s_frag = s_frag := by
      simp only [URMState.step]
      rw [dif_neg]
      rw [h_eq, h_L_eq]
      exact Nat.lt_irrefl _
    have h_big_step : URMState.step P_big s_big = s_big := by
      simp only [URMState.step]
      rw [dif_neg]
      rw [h_pc, h_eq, h_tail]
      exact Nat.lt_irrefl _
    rw [h_big_step, h_frag_step]
    exact ⟨h_pc, h_regs⟩

/-- Multi-step variant of `stateEmbedsFrag_step_tail`,
matching `stateEmbedsFrag_runFor` but with the
weaker `pc_le L` precondition (instead of `pc < L`). -/
theorem stateEmbedsFrag_runFor_tail {a b : ℕ}
    (P_big : URMProgram b) (frag : CompiledFragment a)
    (regOffset pcOffset L : ℕ)
    (h_emb_prog :
      ProgramEmbedsFragment P_big frag regOffset pcOffset L)
    (h_tail : pcOffset + L = P_big.instrs.size)
    (h_L_eq : L = frag.instrs.size)
    (h_well : frag.toURMProgram.WellBounded)
    (s_big : URMState P_big) (s_frag : URMState frag.toURMProgram)
    (h_match :
      StateEmbedsFrag s_big s_frag regOffset pcOffset
        h_emb_prog.hReg)
    (h_pc_le : s_frag.pc ≤ L) (T : ℕ) :
    StateEmbedsFrag (URMState.runFor P_big s_big T)
        (URMState.runFor frag.toURMProgram s_frag T)
        regOffset pcOffset h_emb_prog.hReg := by
  induction T generalizing s_big s_frag with
  | zero => exact h_match
  | succ T ih =>
    have h_step := stateEmbedsFrag_step_tail P_big frag regOffset
      pcOffset L h_emb_prog h_tail h_L_eq s_big s_frag h_match h_pc_le
    rw [URMState.runFor_succ, URMState.runFor_succ]
    refine ih (URMState.step P_big s_big)
      (URMState.step frag.toURMProgram s_frag) h_step ?_
    -- PC stays ≤ L after one step (by well-boundedness applied
    -- to frag.toURMProgram, transporting L = frag.instrs.size).
    rw [h_L_eq]
    exact URMState.step_pc_le_size frag.toURMProgram s_frag h_well
      (h_L_eq ▸ h_pc_le)

/-- Generic bridge from the existential pre-stop form to the
output-only `≤ t'` form. Given the pre-stop witness for a
compiled program `compileER e` reaching its terminal `.stop`
at step `T0`, running for any `t' ≥ compileER_runtime e v`
produces the same output value. Constructor-agnostic: shared
by `compileER_runFor_comp`, and by future `bsum` / `bprod`
analogues, so each connective's wrapper reduces to invoking
its `compileER_pre_stop_correct_*` lemma and applying this
bridge. -/
theorem compileER_pre_stop_to_runFor {a : ℕ}
    (e : ERMor1 a) (v : Fin a → ℕ) (t' : ℕ)
    (ht' : compileER_runtime e v ≤ t')
    (h_pre : ∃ T0 : ℕ,
      T0 ≤ compileER_runtime e v ∧
      (URMState.runFor (compileER e)
            (URMState.init (compileER e) v) T0).pc
          = (compileER e).instrs.size - 1 ∧
      (URMState.runFor (compileER e)
            (URMState.init (compileER e) v) T0).regs
          (compileER e).outputReg
        = e.interp v) :
    (URMState.runFor (compileER e)
        (URMState.init (compileER e) v) t').regs
        (compileER e).outputReg
      = e.interp v := by
  obtain ⟨T0, hT0_bound, h_pc_eq, h_output⟩ := h_pre
  -- Split `t' = T0 + (t' - T0)` using `T0 ≤ runtime ≤ t'`.
  set frag : CompiledFragment a := compileERFrag e
  -- `(compileER e).instrs.size > 0` from `lastInstr_isStop`.
  have h_size_pos : 0 < (compileER e).instrs.size := by
    have hb := frag.lastInstr_isStop
    rcases Nat.eq_zero_or_pos (compileER e).instrs.size with h_eq | h_pos
    · exfalso
      rw [Array.back?] at hb
      have h_none : frag.instrs[frag.instrs.size - 1]? = none := by
        apply Array.getElem?_eq_none
        change (compileER e).instrs.size - 1 ≥ (compileER e).instrs.size
        omega
      rw [h_none] at hb
      cases hb
    · exact h_pos
  -- Set up the post-`T0` state for `runFor_stop`.
  set sT0 : URMState (compileER e) :=
    URMState.runFor (compileER e)
      (URMState.init (compileER e) v) T0
  -- Establish the size-1 form for indexing first, then transport
  -- `pc = size - 1` through both the bound and the value.
  have h_pred_lt : (compileER e).instrs.size - 1 < (compileER e).instrs.size := by
    omega
  have h_stop_last :
      (compileER e).instrs[(compileER e).instrs.size - 1]'h_pred_lt
        = URMInstr.stop := by
    have hb := frag.lastInstr_isStop
    rw [Array.back?] at hb
    obtain ⟨_, h_eq_last⟩ := getElem_of_getElem? hb
    exact h_eq_last
  have h_pc_lt : sT0.pc < (compileER e).instrs.size := h_pc_eq ▸ h_pred_lt
  have h_stop : (compileER e).instrs[sT0.pc]'h_pc_lt = URMInstr.stop := by
    -- `subst h_pc_eq` would fail because `h_pc_eq`'s LHS is the
    -- projection `sT0.pc`, not a local variable; `generalize` plus
    -- `revert`/`intro` re-shapes the goal so `subst` can fire.
    revert h_pc_lt
    generalize sT0.pc = pcVal at h_pc_eq
    intro h_pc_lt
    subst h_pc_eq
    exact h_stop_last
  -- Run `t' = T0 + (t' - T0)` steps; the tail is absorbed by `runFor_stop`.
  have h_t'_eq : t' = T0 + (t' - T0) := by omega
  rw [h_t'_eq, URMState.runFor_add]
  change (URMState.runFor (compileER e) sT0 (t' - T0)).regs
      (compileER e).outputReg
    = e.interp v
  rw [URMState.runFor_stop (compileER e) sT0 (t' - T0) h_pc_lt h_stop]
  exact h_output

end LawvereERKSim
end GebLean
