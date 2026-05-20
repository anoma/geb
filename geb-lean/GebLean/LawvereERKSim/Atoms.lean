import GebLean.LawvereERKSim.Loops

/-!
# LawvereERKSim — atom-constructor correctness

Per-constructor `compileER_runFor_*` and `compileER_pre_stop_correct_atom_*`
lemmas for the four ER atoms (`zero`, `succ`, `proj`, `sub`). Each constructor
appears twice: once in the slack-absorbing `≤ t'` form (the `_runFor_*` lemma)
and once in the existential pre-stop form used by the comp pre-stop assembly
(the `_pre_stop_correct_atom_*` lemma).

## Main statements

- `compileER_runFor_zero`, `_succ`, `_proj`, `_sub`: output-only `≤ t'` form
  for each atom.
- `compileER_pre_stop_correct_atom_zero`, `_succ`, `_proj`, `_sub`:
  existential pre-stop form for each atom (with PC strict bound on earlier
  steps).
- `List.find?_finRange_inputRegs`, `URMState.init_regs_inputRegs`:
  proj-specific helpers for `URMState.init`'s register block on input slots.

## References

- Tourlakis 2018 `PR-complexity-topics.pdf` §0.1.0.37, p. 19 (succ realisation).
- Spec: `docs/superpowers/specs/2026-05-19-lawvere-er-k-sim-file-split-design.md`.
-/

namespace GebLean
namespace LawvereERKSim

open GebLean.ZeroTestURM

/-- Correctness of `compileER` on `.zero`: running for at
least 3 steps from `init` produces output register = 0. -/
private theorem compileER_runFor_zero
    (v : Fin 0 → ℕ) (t' : ℕ)
    (ht' : compileER_runtime (.zero : ERMor1 0) v ≤ t') :
    (URMState.runFor (compileER ERMor1.zero)
        (URMState.init (compileER ERMor1.zero) v) t').regs
        (compileER ERMor1.zero).outputReg
      = ERMor1.zero.interp v := by
  -- runtime = 3; write t' = 3 + (t' - 3).
  have h3 : 3 ≤ t' := ht'
  obtain ⟨sl, rfl⟩ : ∃ sl, t' = 3 + sl :=
    ⟨t' - 3, by omega⟩
  -- Split runFor (3 + sl) = runFor sl after 3 steps.
  rw [URMState.runFor_add]
  -- Compute the state after 3 steps by unfolding step
  -- three times.  All three instruction lookups discharge
  -- by `decide`, since the program is a literal #[…]
  -- array.
  set P : URMProgram 0 := compileER ERMor1.zero
  set s0 : URMState P := URMState.init P v
  -- Step 1: assign ⟨0, _⟩ 0.
  have hs1 : URMState.step P s0 =
      { pc := 1, regs := Function.update s0.regs ⟨0, by decide⟩ 0 } := by
    simp only [URMState.step, s0, URMState.init,
      P, compileER, compileERFrag, compileFrag_zero]
    rfl
  -- Run for sl steps after 3 hops via runFor_stop, since
  -- the third instruction is `.stop`.
  -- Build the state after 3 hops directly.
  set s3 : URMState P :=
    { pc := 2
      regs := Function.update
        (Function.update s0.regs ⟨0, by decide⟩ 0)
        ⟨1, by decide⟩ 0 }
  have h_three :
      URMState.runFor P s0 3 = s3 := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, URMState.runFor_add,
      show (2 : ℕ) = 1 + 1 from rfl, URMState.runFor_add]
    -- Now have runFor P (runFor P (runFor P s0 1) 1) 1
    -- Each individual step computes by `rfl`-like simp.
    simp only [URMState.runFor_succ, URMState.runFor_zero]
    -- Step 1
    rw [show URMState.step P s0 =
        { pc := 1, regs :=
            Function.update s0.regs ⟨0, by decide⟩ 0 } from hs1]
    -- Step 2: assign ⟨1, _⟩ 0.
    have hs2 :
        URMState.step P
          { pc := 1
            regs := Function.update s0.regs ⟨0, by decide⟩ 0 } =
        { pc := 2
          regs := Function.update
            (Function.update s0.regs ⟨0, by decide⟩ 0)
            ⟨1, by decide⟩ 0 } := by
      simp only [URMState.step, P, compileER, compileERFrag,
        compileFrag_zero]
      rfl
    rw [hs2]
    -- Step 3: stop at PC 2.
    change URMState.step P
        { pc := 2
          regs := Function.update
            (Function.update s0.regs ⟨0, by decide⟩ 0)
            ⟨1, by decide⟩ 0 } = s3
    simp only [URMState.step, P, compileER, compileERFrag,
      compileFrag_zero, s3]
    rfl
  rw [h_three]
  -- Slack steps from s3 (PC = 2 = stop instruction) are
  -- absorbed by `runFor_stop`.
  have h_pc : s3.pc < P.instrs.size := by
    change 2 < P.instrs.size
    simp only [P, compileER, compileERFrag, compileFrag_zero]
    decide
  have h_stop : P.instrs[s3.pc]'h_pc = URMInstr.stop := by
    change P.instrs[(2 : ℕ)]'h_pc = URMInstr.stop
    simp only [P, compileER, compileERFrag, compileFrag_zero]
    rfl
  rw [URMState.runFor_stop P s3 sl h_pc h_stop]
  -- Read off register 1 = output reg.
  change s3.regs (compileER ERMor1.zero).outputReg = _
  -- outputReg = ⟨1, _⟩, and regs ⟨1, _⟩ = 0 via the
  -- second Function.update.
  change Function.update (Function.update s0.regs ⟨0, by decide⟩ 0)
      ⟨1, by decide⟩ 0 (compileER ERMor1.zero).outputReg = _
  simp only [P, compileER, compileERFrag, compileFrag_zero]
  rfl

/-- Correctness of `compileER` on `.succ`: running for at
least `12 + 10 * v 0` steps from `init` produces output
register = `(v 0).succ`. Traces the 12-instruction
`compileFrag_succ` program: assignR zeroReg, then 9-step
`preservingTransfer` of input into output, then incR
output, then stopR. -/
private theorem compileER_runFor_succ
    (v : Fin 1 → ℕ) (t' : ℕ)
    (ht' : compileER_runtime (.succ : ERMor1 1) v ≤ t') :
    (URMState.runFor (compileER ERMor1.succ)
        (URMState.init (compileER ERMor1.succ) v) t').regs
        (compileER ERMor1.succ).outputReg
      = ERMor1.succ.interp v := by
  -- Abbreviations for the program and register Fins.
  set P : URMProgram 1 := compileER ERMor1.succ with hP
  set s0 : URMState P := URMState.init P v with hs0
  -- The runtime is 12 + 10 * v 0; the actual trace uses
  -- 9 * v 0 + 5 steps (1 assign + (9 * v 0 + 2) transfer
  -- + 1 inc + 1 stop).  Slack = t' - (9 * v 0 + 5).
  have hrt : compileER_runtime (.succ : ERMor1 1) v = 12 + 10 * v 0 :=
    rfl
  obtain ⟨slack, rfl⟩ : ∃ sl, t' = (9 * v 0 + 5) + sl :=
    ⟨t' - (9 * v 0 + 5), by rw [hrt] at ht'; omega⟩
  -- Five Fins of `P.numRegs = 4`.
  set zReg : Fin P.numRegs := ⟨0, by decide⟩ with hzReg
  set dst  : Fin P.numRegs := ⟨1, by decide⟩ with hdst
  set src  : Fin P.numRegs := ⟨2, by decide⟩ with hsrc
  set tmp  : Fin P.numRegs := ⟨3, by decide⟩ with htmp
  -- Inputs.
  have h_inputReg : P.inputRegs 0 = src := rfl
  -- s0.regs values.
  have hs0_src : s0.regs src = v 0 := by
    -- (List.finRange 1).find? returns some 0 since
    -- inputRegs 0 = src.
    change (URMState.init P v).regs src = v 0
    rfl
  have hs0_zReg : s0.regs zReg = 0 := by
    change (URMState.init P v).regs zReg = 0
    rfl
  have hs0_dst : s0.regs dst = 0 := by
    change (URMState.init P v).regs dst = 0
    rfl
  have hs0_tmp : s0.regs tmp = 0 := by
    change (URMState.init P v).regs tmp = 0
    rfl
  have hs0_pc : s0.pc = 0 := rfl
  -- Disjointness of the four Fins.
  have h_disj_sd : src ≠ dst := by
    intro h; exact absurd (congrArg Fin.val h) (by decide)
  have h_disj_st : src ≠ tmp := by
    intro h; exact absurd (congrArg Fin.val h) (by decide)
  have h_disj_dt : dst ≠ tmp := by
    intro h; exact absurd (congrArg Fin.val h) (by decide)
  have h_disj_zs : zReg ≠ src := by
    intro h; exact absurd (congrArg Fin.val h) (by decide)
  have h_disj_zd : zReg ≠ dst := by
    intro h; exact absurd (congrArg Fin.val h) (by decide)
  have h_disj_zt : zReg ≠ tmp := by
    intro h; exact absurd (congrArg Fin.val h) (by decide)
  -- Instruction-presence hypotheses for preservingTransfer
  -- at PCs 1..9; each one is a literal-array `getElem?`
  -- equality that reduces by `rfl`.
  have H : PreservingTransferInstrs P 1 src dst tmp zReg := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rfl
  -- t' = (9 * v 0 + 5) + slack.
  --   = 1 + (9 * v 0 + 2) + 1 + 1 + slack.
  -- Step 1 (PC 0): assignR 0 0; s0 → s1 with PC = 1 and
  -- regs zReg = 0 (no change).
  have h_split : 9 * v 0 + 5 + slack
      = 1 + ((9 * v 0 + 2) + (1 + (1 + slack))) := by omega
  rw [h_split, URMState.runFor_add]
  -- Compute the first step.
  have h_step0 : URMState.step P s0 =
      { pc := 1
        regs := Function.update s0.regs zReg 0 } := by
    have h_pc : (0 : ℕ) < P.instrs.size := by decide
    have h_eq : P.instrs[(0 : ℕ)]'h_pc = .assign zReg 0 := rfl
    simp only [URMState.step, hs0_pc, dif_pos h_pc, h_eq]
  set s1 : URMState P :=
      { pc := 1
        regs := Function.update s0.regs zReg 0 } with hs1
  have h_first : URMState.runFor P s0 1 = s1 := by
    change URMState.runFor P (URMState.step P s0) 0 = _
    rw [URMState.runFor_zero, h_step0]
  rw [h_first]
  -- s1's register values.
  have hs1_pc : s1.pc = 1 := rfl
  have hs1_zReg : s1.regs zReg = 0 := by
    change Function.update s0.regs zReg 0 zReg = 0
    rw [Function.update_self]
  have hs1_src : s1.regs src = v 0 := by
    change Function.update s0.regs zReg 0 src = v 0
    rw [Function.update_of_ne (Ne.symm h_disj_zs), hs0_src]
  have hs1_dst : s1.regs dst = 0 := by
    change Function.update s0.regs zReg 0 dst = 0
    rw [Function.update_of_ne (Ne.symm h_disj_zd), hs0_dst]
  have hs1_tmp : s1.regs tmp = 0 := by
    change Function.update s0.regs zReg 0 tmp = 0
    rw [Function.update_of_ne (Ne.symm h_disj_zt), hs0_tmp]
  -- Step 2: preservingTransfer block for `9 * v 0 + 2`
  -- steps.
  rw [URMState.runFor_add]
  obtain ⟨pt_pc, pt_dst, pt_src, pt_tmp, pt_z, pt_oth⟩ :=
    preservingTransfer_correct P 1 src dst tmp zReg
      h_disj_sd h_disj_st h_disj_dt h_disj_zs h_disj_zd h_disj_zt
      H s1 hs1_pc hs1_zReg hs1_tmp (v 0) hs1_src
  set s2 : URMState P := URMState.runFor P s1 (9 * v 0 + 2)
    with hs2
  -- s2's values.
  have hs2_pc : s2.pc = 10 := by
    have h10 : (1 : ℕ) + 9 = 10 := by omega
    rw [← h10]; exact pt_pc
  have hs2_dst : s2.regs dst = v 0 := by
    rw [pt_dst, hs1_dst]; omega
  -- Step 3: incR dst at PC 10.
  rw [URMState.runFor_add]
  have h_step2 : URMState.step P s2 =
      { pc := 11
        regs := Function.update s2.regs dst (s2.regs dst + 1) } := by
    have h_pc : (10 : ℕ) < P.instrs.size := by decide
    have h_eq : P.instrs[(10 : ℕ)]'h_pc = .inc dst := rfl
    simp only [URMState.step, hs2_pc, dif_pos h_pc, h_eq]
  set s3 : URMState P :=
      { pc := 11
        regs := Function.update s2.regs dst (s2.regs dst + 1) }
    with hs3
  have h_third : URMState.runFor P s2 1 = s3 := by
    change URMState.runFor P (URMState.step P s2) 0 = _
    rw [URMState.runFor_zero, h_step2]
  rw [h_third]
  have hs3_pc : s3.pc = 11 := rfl
  have hs3_dst : s3.regs dst = v 0 + 1 := by
    change Function.update s2.regs dst (s2.regs dst + 1) dst = v 0 + 1
    rw [Function.update_self, hs2_dst]
  -- Step 4: stopR at PC 11.  The remaining `1 + slack`
  -- steps are absorbed by `runFor_stop`.
  have h_pc11 : s3.pc < P.instrs.size := by
    rw [hs3_pc]; decide
  have h_stop : P.instrs[s3.pc]'h_pc11 = URMInstr.stop := by
    change P.instrs[(11 : ℕ)]'(hs3_pc ▸ h_pc11) = URMInstr.stop
    rfl
  rw [URMState.runFor_stop P s3 (1 + slack) h_pc11 h_stop]
  -- Read off output register.
  change s3.regs dst = _
  rw [hs3_dst, ERMor1.interp_succ]

/-- Auxiliary: `(List.finRange a).find?` over an injective
predicate keyed by `inputRegs` returns the input slot whose
register matches. Phrased over a generic injective `f` to
keep the induction clean. Constructive: built bottom-up from
`List.finRange_succ` and `List.find?_cons`. -/
private theorem List.find?_finRange_inputRegs
    {a : ℕ} {β : Type*} [DecidableEq β]
    (f : Fin a → β) (hf : Function.Injective f) (i : Fin a) :
    (List.finRange a).find? (fun j => decide (f j = f i)) = some i := by
  induction a with
  | zero => exact i.elim0
  | succ a' ih =>
    rw [List.finRange_succ, List.find?_cons]
    by_cases h0 : i = 0
    · subst h0
      simp
    · -- i is some Fin.succ i'.
      have h_dec :
          decide (f 0 = f i) = false := by
        simp only [decide_eq_false_iff_not]
        intro heq; exact h0 (hf heq).symm
      rw [h_dec]
      -- Recurse on `(List.finRange a').map Fin.succ`.
      obtain ⟨i', rfl⟩ : ∃ i', i = Fin.succ i' := ⟨i.pred h0, (i.succ_pred h0).symm⟩
      rw [List.find?_map]
      have h_rec :
          (List.finRange a').find?
              ((fun j => decide (f j = f i'.succ)) ∘ Fin.succ) = some i' := by
        have := ih (f ∘ Fin.succ)
          (fun x y hxy => Fin.succ_injective _ (hf hxy)) i'
        simp only [Function.comp] at this ⊢
        exact this
      rw [h_rec]
      rfl

/-- The `init` register at any input slot's image returns
the corresponding input value. Generalises the single-slot
`rfl` reduction used in `compileER_runFor_succ` to programs
with more than one input. Constructive. -/
theorem URMState.init_regs_inputRegs {a : ℕ}
    (P : URMProgram a) (v : Fin a → ℕ) (i : Fin a) :
    (URMState.init P v).regs (P.inputRegs i) = v i := by
  change
    (match (List.finRange a).find?
        (fun j => decide (P.inputRegs j = P.inputRegs i)) with
      | some j => v j
      | none   => 0) = v i
  rw [List.find?_finRange_inputRegs P.inputRegs P.inputRegs_inj i]

/-- Correctness of `compileER` on `.proj i`: running for at
least `11 + 10 * v i` steps from `init` produces output
register = `v i`. Traces the 11-instruction
`compileFrag_proj i` program: assignR zeroReg, then 9-step
`preservingTransfer` of input slot `i` into output, then
stopR. -/
private theorem compileER_runFor_proj {k : ℕ} (i : Fin k)
    (v : Fin k → ℕ) (t' : ℕ)
    (ht' : compileER_runtime (.proj i : ERMor1 k) v ≤ t') :
    (URMState.runFor (compileER (ERMor1.proj i))
        (URMState.init (compileER (ERMor1.proj i)) v) t').regs
        (compileER (ERMor1.proj i)).outputReg
      = (ERMor1.proj i).interp v := by
  -- Abbreviations for the program and register Fins.
  set P : URMProgram k := compileER (ERMor1.proj i) with hP
  set s0 : URMState P := URMState.init P v with hs0
  -- The runtime is 11 + 10 * v i; the actual trace uses
  -- 9 * v i + 3 steps (1 assign + (9 * v i + 2) transfer
  -- + 1 stop).  Slack = t' - (9 * v i + 3).
  have hrt : compileER_runtime (.proj i : ERMor1 k) v = 11 + 10 * v i :=
    rfl
  obtain ⟨slack, rfl⟩ : ∃ sl, t' = (9 * v i + 3) + sl :=
    ⟨t' - (9 * v i + 3), by rw [hrt] at ht'; omega⟩
  -- Four Fins of `P.numRegs = k + 3`.
  have hi : i.val < k := i.isLt
  set zReg : Fin P.numRegs := ⟨0, by change 0 < k + 3; omega⟩ with hzReg
  set dst  : Fin P.numRegs := ⟨1, by change 1 < k + 3; omega⟩ with hdst
  set src  : Fin P.numRegs := ⟨2 + i.val, by change 2 + i.val < k + 3; omega⟩
    with hsrc
  set tmp  : Fin P.numRegs := ⟨2 + k, by change 2 + k < k + 3; omega⟩ with htmp
  -- Inputs.
  have h_inputReg : P.inputRegs i = src := rfl
  -- s0.regs values.
  have hs0_src : s0.regs src = v i := by
    change (URMState.init P v).regs (P.inputRegs i) = v i
    exact URMState.init_regs_inputRegs P v i
  have hs0_zReg : s0.regs zReg = 0 := by
    change (URMState.init P v).regs zReg = 0
    -- zReg is not in the image of inputRegs; find? returns none.
    change (match (List.finRange k).find?
        (fun j => decide (P.inputRegs j = zReg)) with
      | some j => v j
      | none   => 0) = 0
    have h_none : (List.finRange k).find?
        (fun j => decide (P.inputRegs j = zReg)) = none := by
      apply List.find?_eq_none.mpr
      intro j _
      simp only [Bool.not_eq_true, decide_eq_false_iff_not]
      intro h
      have : (2 + j.val : ℕ) = 0 := congrArg Fin.val h
      omega
    rw [h_none]
  have hs0_dst : s0.regs dst = 0 := by
    change (URMState.init P v).regs dst = 0
    change (match (List.finRange k).find?
        (fun j => decide (P.inputRegs j = dst)) with
      | some j => v j
      | none   => 0) = 0
    have h_none : (List.finRange k).find?
        (fun j => decide (P.inputRegs j = dst)) = none := by
      apply List.find?_eq_none.mpr
      intro j _
      simp only [Bool.not_eq_true, decide_eq_false_iff_not]
      intro h
      have : (2 + j.val : ℕ) = 1 := congrArg Fin.val h
      omega
    rw [h_none]
  have hs0_tmp : s0.regs tmp = 0 := by
    change (URMState.init P v).regs tmp = 0
    change (match (List.finRange k).find?
        (fun j => decide (P.inputRegs j = tmp)) with
      | some j => v j
      | none   => 0) = 0
    have h_none : (List.finRange k).find?
        (fun j => decide (P.inputRegs j = tmp)) = none := by
      apply List.find?_eq_none.mpr
      intro j hj
      simp only [Bool.not_eq_true, decide_eq_false_iff_not]
      intro h
      have : (2 + j.val : ℕ) = 2 + k := congrArg Fin.val h
      have hjlt : j.val < k := j.isLt
      omega
    rw [h_none]
  have hs0_pc : s0.pc = 0 := rfl
  -- Disjointness of the four Fins.
  have h_disj_sd : src ≠ dst := by
    intro h
    have : (2 + i.val : ℕ) = 1 := congrArg Fin.val h
    omega
  have h_disj_st : src ≠ tmp := by
    intro h
    have : (2 + i.val : ℕ) = 2 + k := congrArg Fin.val h
    omega
  have h_disj_dt : dst ≠ tmp := by
    intro h
    have : (1 : ℕ) = 2 + k := congrArg Fin.val h
    omega
  have h_disj_zs : zReg ≠ src := by
    intro h
    have : (0 : ℕ) = 2 + i.val := congrArg Fin.val h
    omega
  have h_disj_zd : zReg ≠ dst := by
    intro h
    have : (0 : ℕ) = 1 := congrArg Fin.val h
    omega
  have h_disj_zt : zReg ≠ tmp := by
    intro h
    have : (0 : ℕ) = 2 + k := congrArg Fin.val h
    omega
  -- Instruction-presence hypotheses for preservingTransfer
  -- at PCs 1..9; each one is a literal-array `getElem?`
  -- equality that reduces by `rfl`.
  have H : PreservingTransferInstrs P 1 src dst tmp zReg := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rfl
  -- t' = (9 * v i + 3) + slack.
  --   = 1 + ((9 * v i + 2) + slack).  The trailing `slack`
  -- includes the final `stop` step at PC 10 and absorbs
  -- via `runFor_stop`.
  have h_split : 9 * v i + 3 + slack
      = 1 + ((9 * v i + 2) + slack) := by omega
  rw [h_split, URMState.runFor_add]
  -- Program size is 11 (independent of i).
  have h_size : P.instrs.size = 11 := rfl
  -- Step 1 (PC 0): assignR 0 0; s0 → s1 with PC = 1 and
  -- regs zReg = 0 (no change).
  have h_step0 : URMState.step P s0 =
      { pc := 1
        regs := Function.update s0.regs zReg 0 } := by
    have h_pc : (0 : ℕ) < P.instrs.size := by rw [h_size]; decide
    have h_eq : P.instrs[(0 : ℕ)]'h_pc = .assign zReg 0 := rfl
    simp only [URMState.step, hs0_pc, dif_pos h_pc, h_eq]
  set s1 : URMState P :=
      { pc := 1
        regs := Function.update s0.regs zReg 0 } with hs1
  have h_first : URMState.runFor P s0 1 = s1 := by
    change URMState.runFor P (URMState.step P s0) 0 = _
    rw [URMState.runFor_zero, h_step0]
  rw [h_first]
  -- s1's register values.
  have hs1_pc : s1.pc = 1 := rfl
  have hs1_zReg : s1.regs zReg = 0 := by
    change Function.update s0.regs zReg 0 zReg = 0
    rw [Function.update_self]
  have hs1_src : s1.regs src = v i := by
    change Function.update s0.regs zReg 0 src = v i
    rw [Function.update_of_ne (Ne.symm h_disj_zs), hs0_src]
  have hs1_dst : s1.regs dst = 0 := by
    change Function.update s0.regs zReg 0 dst = 0
    rw [Function.update_of_ne (Ne.symm h_disj_zd), hs0_dst]
  have hs1_tmp : s1.regs tmp = 0 := by
    change Function.update s0.regs zReg 0 tmp = 0
    rw [Function.update_of_ne (Ne.symm h_disj_zt), hs0_tmp]
  -- Step 2: preservingTransfer block for `9 * v i + 2` steps.
  rw [URMState.runFor_add]
  obtain ⟨pt_pc, pt_dst, _pt_src, _pt_tmp, _pt_z, _pt_oth⟩ :=
    preservingTransfer_correct P 1 src dst tmp zReg
      h_disj_sd h_disj_st h_disj_dt h_disj_zs h_disj_zd h_disj_zt
      H s1 hs1_pc hs1_zReg hs1_tmp (v i) hs1_src
  set s2 : URMState P := URMState.runFor P s1 (9 * v i + 2)
    with hs2
  -- s2's values.
  have hs2_pc : s2.pc = 10 := by
    have h10 : (1 : ℕ) + 9 = 10 := by omega
    rw [← h10]; exact pt_pc
  have hs2_dst : s2.regs dst = v i := by
    rw [pt_dst, hs1_dst]; omega
  -- Step 3: stopR at PC 10.  The remaining `slack` steps
  -- are absorbed by `runFor_stop`.
  have h_pc10 : s2.pc < P.instrs.size := by
    rw [hs2_pc, h_size]; decide
  have h_stop : P.instrs[s2.pc]'h_pc10 = URMInstr.stop := by
    -- `s2.pc = 10`; transport along this to read off the
    -- stop instruction at PC 10.
    revert h_pc10
    rw [hs2_pc]
    intro _; rfl
  rw [URMState.runFor_stop P s2 slack h_pc10 h_stop]
  -- Read off output register.
  change s2.regs dst = _
  rw [hs2_dst, ERMor1.interp_proj]

/-- Correctness of `compileER` on `.sub`: running for at
least `20 + 10 * v 0 + 10 * v 1` steps from `init` produces
output register = `v 0 - v 1` (truncated subtraction).
Traces the 19-instruction `compileFrag_sub` program: assignR
zeroReg, then 9-step `preservingTransfer` of X into output,
then 4-instruction `transferLoop` cloning Y into a scratch,
then inner decrement loop on output by the scratch, then
stopR. -/
private theorem compileER_runFor_sub
    (v : Fin 2 → ℕ) (t' : ℕ)
    (ht' : compileER_runtime (.sub : ERMor1 2) v ≤ t') :
    (URMState.runFor (compileER ERMor1.sub)
        (URMState.init (compileER ERMor1.sub) v) t').regs
        (compileER ERMor1.sub).outputReg
      = ERMor1.sub.interp v := by
  -- Abbreviations for the program and register Fins.
  set P : URMProgram 2 := compileER ERMor1.sub with hP
  set s0 : URMState P := URMState.init P v with hs0
  -- Runtime is `20 + 10 * v 0 + 10 * v 1`; actual prefix
  -- trace uses `9 * v 0 + 8 * v 1 + 5` steps.  Slack ≥ 10.
  have hrt : compileER_runtime (.sub : ERMor1 2) v
      = 20 + 10 * v 0 + 10 * v 1 := rfl
  obtain ⟨slack, rfl⟩ :
      ∃ sl, t' = (9 * v 0 + 8 * v 1 + 5) + sl :=
    ⟨t' - (9 * v 0 + 8 * v 1 + 5),
      by rw [hrt] at ht'; omega⟩
  -- Six Fins of `P.numRegs = 6`.
  set zReg : Fin P.numRegs := ⟨0, by decide⟩ with hzReg
  set dst  : Fin P.numRegs := ⟨1, by decide⟩ with hdst
  set xReg : Fin P.numRegs := ⟨2, by decide⟩ with hxReg
  set yReg : Fin P.numRegs := ⟨3, by decide⟩ with hyReg
  set tmp  : Fin P.numRegs := ⟨4, by decide⟩ with htmp
  set sReg : Fin P.numRegs := ⟨5, by decide⟩ with hsReg
  -- Inputs.
  have h_in0 : P.inputRegs 0 = xReg := rfl
  have h_in1 : P.inputRegs 1 = yReg := rfl
  -- s0.regs values.
  have hs0_xReg : s0.regs xReg = v 0 := by
    change (URMState.init P v).regs xReg = v 0
    rw [show xReg = P.inputRegs 0 from rfl]
    exact URMState.init_regs_inputRegs P v 0
  have hs0_yReg : s0.regs yReg = v 1 := by
    change (URMState.init P v).regs yReg = v 1
    rw [show yReg = P.inputRegs 1 from rfl]
    exact URMState.init_regs_inputRegs P v 1
  have hs0_zReg : s0.regs zReg = 0 := rfl
  have hs0_dst : s0.regs dst = 0 := rfl
  have hs0_tmp : s0.regs tmp = 0 := rfl
  have hs0_sReg : s0.regs sReg = 0 := rfl
  have hs0_pc : s0.pc = 0 := rfl
  -- Disjointness lemmas: each pair distinct by Fin.val.
  have h_disj_zd : zReg ≠ dst := by
    intro h; exact absurd (congrArg Fin.val h) (by decide)
  have h_disj_zx : zReg ≠ xReg := by
    intro h; exact absurd (congrArg Fin.val h) (by decide)
  have h_disj_zy : zReg ≠ yReg := by
    intro h; exact absurd (congrArg Fin.val h) (by decide)
  have h_disj_zt : zReg ≠ tmp := by
    intro h; exact absurd (congrArg Fin.val h) (by decide)
  have h_disj_zs : zReg ≠ sReg := by
    intro h; exact absurd (congrArg Fin.val h) (by decide)
  have h_disj_dx : dst ≠ xReg := by
    intro h; exact absurd (congrArg Fin.val h) (by decide)
  have h_disj_dy : dst ≠ yReg := by
    intro h; exact absurd (congrArg Fin.val h) (by decide)
  have h_disj_dt : dst ≠ tmp := by
    intro h; exact absurd (congrArg Fin.val h) (by decide)
  have h_disj_ds : dst ≠ sReg := by
    intro h; exact absurd (congrArg Fin.val h) (by decide)
  have h_disj_xy : xReg ≠ yReg := by
    intro h; exact absurd (congrArg Fin.val h) (by decide)
  have h_disj_xt : xReg ≠ tmp := by
    intro h; exact absurd (congrArg Fin.val h) (by decide)
  have h_disj_xs : xReg ≠ sReg := by
    intro h; exact absurd (congrArg Fin.val h) (by decide)
  have h_disj_yt : yReg ≠ tmp := by
    intro h; exact absurd (congrArg Fin.val h) (by decide)
  have h_disj_ys : yReg ≠ sReg := by
    intro h; exact absurd (congrArg Fin.val h) (by decide)
  have h_disj_ts : tmp ≠ sReg := by
    intro h; exact absurd (congrArg Fin.val h) (by decide)
  -- Instruction-presence hypotheses.
  have Hpt : PreservingTransferInstrs P 1 xReg dst tmp zReg := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rfl
  have Htl : TransferLoopInstrs P 10 yReg sReg zReg := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> rfl
  have Hsi : SubInnerLoopInstrs P 14 sReg dst zReg := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> rfl
  -- t' = (9 * v 0 + 8 * v 1 + 5) + slack
  --    = 1 + (9 * v 0 + 2) + (4 * v 1 + 1) + (4 * v 1 + 1) + slack.
  have h_split :
      9 * v 0 + 8 * v 1 + 5 + slack
        = 1 + ((9 * v 0 + 2)
          + ((4 * v 1 + 1)
            + ((4 * v 1 + 1) + slack))) := by omega
  rw [h_split, URMState.runFor_add]
  -- Step 1 (PC 0): assignR 0 0.
  have h_step0 : URMState.step P s0 =
      { pc := 1
        regs := Function.update s0.regs zReg 0 } := by
    have h_pc : (0 : ℕ) < P.instrs.size := by decide
    have h_eq : P.instrs[(0 : ℕ)]'h_pc = .assign zReg 0 := rfl
    simp only [URMState.step, hs0_pc, dif_pos h_pc, h_eq]
  set s1 : URMState P :=
      { pc := 1
        regs := Function.update s0.regs zReg 0 } with hs1
  have h_first : URMState.runFor P s0 1 = s1 := by
    change URMState.runFor P (URMState.step P s0) 0 = _
    rw [URMState.runFor_zero, h_step0]
  rw [h_first]
  -- s1's register values.
  have hs1_pc : s1.pc = 1 := rfl
  have hs1_zReg : s1.regs zReg = 0 := by
    change Function.update s0.regs zReg 0 zReg = 0
    rw [Function.update_self]
  have hs1_xReg : s1.regs xReg = v 0 := by
    change Function.update s0.regs zReg 0 xReg = v 0
    rw [Function.update_of_ne (Ne.symm h_disj_zx), hs0_xReg]
  have hs1_yReg : s1.regs yReg = v 1 := by
    change Function.update s0.regs zReg 0 yReg = v 1
    rw [Function.update_of_ne (Ne.symm h_disj_zy), hs0_yReg]
  have hs1_dst : s1.regs dst = 0 := by
    change Function.update s0.regs zReg 0 dst = 0
    rw [Function.update_of_ne (Ne.symm h_disj_zd), hs0_dst]
  have hs1_tmp : s1.regs tmp = 0 := by
    change Function.update s0.regs zReg 0 tmp = 0
    rw [Function.update_of_ne (Ne.symm h_disj_zt), hs0_tmp]
  have hs1_sReg : s1.regs sReg = 0 := by
    change Function.update s0.regs zReg 0 sReg = 0
    rw [Function.update_of_ne (Ne.symm h_disj_zs), hs0_sReg]
  -- Step 2: preservingTransfer block for `9 * v 0 + 2`
  -- steps (PCs 1..9).  Inputs: src = xReg (v 0), dst, tmp.
  rw [URMState.runFor_add]
  obtain ⟨pt_pc, pt_dst, pt_xReg, pt_tmp, pt_z, pt_oth⟩ :=
    preservingTransfer_correct P 1 xReg dst tmp zReg
      h_disj_dx.symm h_disj_xt h_disj_dt h_disj_zx h_disj_zd h_disj_zt
      Hpt s1 hs1_pc hs1_zReg hs1_tmp (v 0) hs1_xReg
  set s2 : URMState P := URMState.runFor P s1 (9 * v 0 + 2)
    with hs2
  -- s2's values.
  have hs2_pc : s2.pc = 10 := by
    have h10 : (1 : ℕ) + 9 = 10 := by omega
    rw [← h10]; exact pt_pc
  have hs2_dst : s2.regs dst = v 0 := by
    rw [pt_dst, hs1_dst]; omega
  have hs2_xReg : s2.regs xReg = v 0 := pt_xReg
  have hs2_zReg : s2.regs zReg = 0 := pt_z
  have hs2_tmp : s2.regs tmp = 0 := pt_tmp
  -- yReg, sReg ≠ dst; use pt_oth.
  have hs2_yReg : s2.regs yReg = v 1 := by
    rw [pt_oth yReg (Ne.symm h_disj_dy), hs1_yReg]
  have hs2_sReg : s2.regs sReg = 0 := by
    rw [pt_oth sReg (Ne.symm h_disj_ds), hs1_sReg]
  -- Step 3: transferLoop block for `4 * v 1 + 1` steps
  -- (PCs 10..13).  src = yReg (v 1), dst = sReg.
  rw [URMState.runFor_add]
  obtain ⟨tl_pc, tl_sReg, tl_yReg, tl_z, tl_oth⟩ :=
    transferLoop_correct P 10 yReg sReg zReg
      h_disj_ys h_disj_zy h_disj_zs
      Htl s2 hs2_pc hs2_zReg (v 1) hs2_yReg
  set s3 : URMState P := URMState.runFor P s2 (4 * v 1 + 1)
    with hs3
  -- s3's values.
  have hs3_pc : s3.pc = 14 := by
    have h14 : (10 : ℕ) + 4 = 14 := by omega
    rw [← h14]; exact tl_pc
  have hs3_sReg : s3.regs sReg = v 1 := by
    rw [tl_sReg, hs2_sReg]; omega
  have hs3_dst : s3.regs dst = v 0 := by
    have h := tl_oth dst h_disj_ds h_disj_dy h_disj_zd.symm
    rw [h, hs2_dst]
  have hs3_zReg : s3.regs zReg = 0 := tl_z
  -- Step 4: subInnerLoop block for `4 * v 1 + 1` steps
  -- (PCs 14..17).  src = sReg, dst = dst (the output).
  rw [URMState.runFor_add]
  obtain ⟨si_pc, si_dst, si_sReg, si_z, _si_oth⟩ :=
    subInnerLoop_correct P 14 sReg dst zReg
      h_disj_ds.symm h_disj_zs h_disj_zd
      Hsi s3 hs3_pc hs3_zReg (v 1) hs3_sReg
  set s4 : URMState P := URMState.runFor P s3 (4 * v 1 + 1)
    with hs4
  -- s4's values.
  have hs4_pc : s4.pc = 18 := by
    have h18 : (14 : ℕ) + 4 = 18 := by omega
    rw [← h18]; exact si_pc
  have hs4_dst : s4.regs dst = v 0 - v 1 := by
    rw [si_dst, hs3_dst]
  -- Step 5: stopR at PC 18.  `slack` steps absorbed.
  have h_pc18 : s4.pc < P.instrs.size := by
    rw [hs4_pc]; decide
  have h_stop : P.instrs[s4.pc]'h_pc18 = URMInstr.stop := by
    revert h_pc18
    rw [hs4_pc]
    intro _; rfl
  rw [URMState.runFor_stop P s4 slack h_pc18 h_stop]
  -- Read off output register.
  change s4.regs dst = _
  rw [hs4_dst, ERMor1.interp_sub]

/-- Pre-stop trace lemma for `compileER ERMor1.zero`. After
`T0 = 2` steps from `init`, the program reaches PC = 2 =
`(compileER ERMor1.zero).instrs.size - 1` (the stop
instruction), the output register holds `0 =
ERMor1.zero.interp v`, and for every earlier step count
`k < 2`, the PC is `0` or `1`, hence strictly less than
`size - 1`. Atom case of `compileER_pre_stop_correct`;
the compositional cases (comp/bsum/bprod) and the
remaining atoms (succ/proj/sub) are deferred. -/
theorem compileER_pre_stop_correct_atom_zero
    (v : Fin 0 → ℕ) :
    ∃ T0 : ℕ,
      T0 ≤ compileER_runtime (.zero : ERMor1 0) v ∧
      ((URMState.init (compileER ERMor1.zero) v).runFor
            (compileER ERMor1.zero) T0).pc
          = (compileER ERMor1.zero).instrs.size - 1 ∧
      ((URMState.init (compileER ERMor1.zero) v).runFor
            (compileER ERMor1.zero) T0).regs
          (compileER ERMor1.zero).outputReg
        = ERMor1.zero.interp v ∧
      (∀ k < T0,
        ((URMState.init (compileER ERMor1.zero) v).runFor
            (compileER ERMor1.zero) k).pc
          < (compileER ERMor1.zero).instrs.size - 1) := by
  -- The atom program has size 3, stop at PC = 2.
  -- T0 = 2: at step 2 the program reaches the stop and the
  -- output register V_1 has been written with 0.
  refine ⟨2, ?_, ?_, ?_, ?_⟩
  · -- 2 ≤ runtime = 3.
    change (2 : ℕ) ≤ 3; decide
  · -- After 2 steps, PC = 2 = size - 1.
    set P : URMProgram 0 := compileER ERMor1.zero with hP
    set s0 : URMState P := URMState.init P v with hs0
    -- Step 0 (PC 0): assign ⟨0, _⟩ 0; PC → 1.
    have h_step0 : URMState.step P s0 =
        { pc := 1
          regs := Function.update s0.regs ⟨0, by decide⟩ 0 } := by
      simp only [URMState.step, s0, URMState.init, P,
        compileER, compileERFrag, compileFrag_zero]
      rfl
    set s1 : URMState P :=
      { pc := 1
        regs := Function.update s0.regs ⟨0, by decide⟩ 0 }
    -- Step 1 (PC 1): assign ⟨1, _⟩ 0; PC → 2.
    have h_step1 : URMState.step P s1 =
        { pc := 2
          regs := Function.update s1.regs ⟨1, by decide⟩ 0 } := by
      simp only [URMState.step, P, compileER, compileERFrag,
        compileFrag_zero]
      rfl
    -- runFor P s0 2 = step (step s0).
    have h_two : URMState.runFor P s0 2 =
        { pc := 2
          regs := Function.update s1.regs ⟨1, by decide⟩ 0 } := by
      change URMState.runFor P (URMState.step P s0) 1 = _
      rw [h_step0]
      change URMState.runFor P (URMState.step P s1) 0 = _
      rw [URMState.runFor_zero, h_step1]
    rw [h_two]
    -- size = 3, size - 1 = 2.
    change (2 : ℕ) = (3 : ℕ) - 1
    rfl
  · -- After 2 steps, output register holds 0 = .zero.interp v.
    set P : URMProgram 0 := compileER ERMor1.zero with hP
    set s0 : URMState P := URMState.init P v with hs0
    have h_step0 : URMState.step P s0 =
        { pc := 1
          regs := Function.update s0.regs ⟨0, by decide⟩ 0 } := by
      simp only [URMState.step, s0, URMState.init, P,
        compileER, compileERFrag, compileFrag_zero]
      rfl
    set s1 : URMState P :=
      { pc := 1
        regs := Function.update s0.regs ⟨0, by decide⟩ 0 }
    have h_step1 : URMState.step P s1 =
        { pc := 2
          regs := Function.update s1.regs ⟨1, by decide⟩ 0 } := by
      simp only [URMState.step, P, compileER, compileERFrag,
        compileFrag_zero]
      rfl
    have h_two : URMState.runFor P s0 2 =
        { pc := 2
          regs := Function.update s1.regs ⟨1, by decide⟩ 0 } := by
      change URMState.runFor P (URMState.step P s0) 1 = _
      rw [h_step0]
      change URMState.runFor P (URMState.step P s1) 0 = _
      rw [URMState.runFor_zero, h_step1]
    rw [h_two]
    -- outputReg = ⟨1, _⟩; the second update writes 0 there.
    change Function.update s1.regs ⟨1, by decide⟩ 0
        (compileER ERMor1.zero).outputReg = _
    simp only [P, compileER, compileERFrag, compileFrag_zero]
    rfl
  · -- For k < 2, the PC after k steps is k itself, < 2.
    intro k hk
    set P : URMProgram 0 := compileER ERMor1.zero with hP
    set s0 : URMState P := URMState.init P v with hs0
    -- Case-split on k = 0 or k = 1.
    match k, hk with
    | 0, _ =>
      -- k = 0: PC = 0 < 2.
      change s0.pc < (compileER ERMor1.zero).instrs.size - 1
      change (0 : ℕ) < 3 - 1
      decide
    | 1, _ =>
      -- k = 1: PC after one step = 1 < 2.
      have h_step0 : URMState.step P s0 =
          { pc := 1
            regs := Function.update s0.regs ⟨0, by decide⟩ 0 } := by
        simp only [URMState.step, s0, URMState.init, P,
          compileER, compileERFrag, compileFrag_zero]
        rfl
      have h_one : URMState.runFor P s0 1 =
          { pc := 1
            regs := Function.update s0.regs ⟨0, by decide⟩ 0 } := by
        change URMState.runFor P (URMState.step P s0) 0 = _
        rw [URMState.runFor_zero, h_step0]
      rw [h_one]
      change (1 : ℕ) < (compileER ERMor1.zero).instrs.size - 1
      change (1 : ℕ) < 3 - 1
      decide

/-- Pre-stop PC and output for the `.succ` atom.  After
`9 * v 0 + 4` steps the program reaches `pc = 11` (the stop
instruction at `size - 1`) with the output register holding
`v 0 + 1 = ERMor1.succ.interp v`; for every earlier step
count the PC is strictly less than `size - 1`. Atom case of
`compileER_pre_stop_correct`. -/
theorem compileER_pre_stop_correct_atom_succ
    (v : Fin 1 → ℕ) :
    ∃ T0 : ℕ,
      T0 ≤ compileER_runtime (.succ : ERMor1 1) v ∧
      (URMState.runFor (compileER ERMor1.succ)
            (URMState.init (compileER ERMor1.succ) v) T0).pc
          = (compileER ERMor1.succ).instrs.size - 1 ∧
      (URMState.runFor (compileER ERMor1.succ)
            (URMState.init (compileER ERMor1.succ) v) T0).regs
          (compileER ERMor1.succ).outputReg
        = ERMor1.succ.interp v ∧
      (∀ k < T0,
        (URMState.runFor (compileER ERMor1.succ)
            (URMState.init (compileER ERMor1.succ) v) k).pc
          < (compileER ERMor1.succ).instrs.size - 1) := by
  -- Mirrors the trace structure of `compileER_runFor_succ`.
  set P : URMProgram 1 := compileER ERMor1.succ with hP
  set s0 : URMState P := URMState.init P v with hs0
  -- Four Fins of `P.numRegs = 4`.
  set zReg : Fin P.numRegs := ⟨0, by decide⟩ with hzReg
  set dst  : Fin P.numRegs := ⟨1, by decide⟩ with hdst
  set src  : Fin P.numRegs := ⟨2, by decide⟩ with hsrc
  set tmp  : Fin P.numRegs := ⟨3, by decide⟩ with htmp
  -- Inputs.
  have hs0_src : s0.regs src = v 0 := by
    change (URMState.init P v).regs src = v 0; rfl
  have hs0_zReg : s0.regs zReg = 0 := by
    change (URMState.init P v).regs zReg = 0; rfl
  have hs0_dst : s0.regs dst = 0 := by
    change (URMState.init P v).regs dst = 0; rfl
  have hs0_tmp : s0.regs tmp = 0 := by
    change (URMState.init P v).regs tmp = 0; rfl
  have hs0_pc : s0.pc = 0 := rfl
  -- Disjointness of the four Fins.
  have h_disj_sd : src ≠ dst := by
    intro h; exact absurd (congrArg Fin.val h) (by decide)
  have h_disj_st : src ≠ tmp := by
    intro h; exact absurd (congrArg Fin.val h) (by decide)
  have h_disj_dt : dst ≠ tmp := by
    intro h; exact absurd (congrArg Fin.val h) (by decide)
  have h_disj_zs : zReg ≠ src := by
    intro h; exact absurd (congrArg Fin.val h) (by decide)
  have h_disj_zd : zReg ≠ dst := by
    intro h; exact absurd (congrArg Fin.val h) (by decide)
  have h_disj_zt : zReg ≠ tmp := by
    intro h; exact absurd (congrArg Fin.val h) (by decide)
  -- Instruction-presence hypotheses for preservingTransfer at PCs 1..9.
  have H : PreservingTransferInstrs P 1 src dst tmp zReg := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rfl
  -- Program size is 12, so size - 1 = 11.
  have h_size : P.instrs.size = 12 := rfl
  -- T0 = 9 * v 0 + 4.
  refine ⟨9 * v 0 + 4, ?_, ?_, ?_, ?_⟩
  · -- 9 * v 0 + 4 ≤ 12 + 10 * v 0.
    change 9 * v 0 + 4 ≤ 12 + 10 * v 0
    omega
  · -- After `9 * v 0 + 4` steps, PC = 11 = size - 1.
    -- Phases: 1 step (assign) + (9 * v 0 + 2) (preservingTransfer)
    -- + 1 step (inc dst).
    have h_split : 9 * v 0 + 4 = 1 + ((9 * v 0 + 2) + 1) := by omega
    rw [h_split, URMState.runFor_add]
    -- Step 1 (PC 0): assignR 0 0.
    have h_step0 : URMState.step P s0 =
        { pc := 1
          regs := Function.update s0.regs zReg 0 } := by
      have h_pc : (0 : ℕ) < P.instrs.size := by decide
      have h_eq : P.instrs[(0 : ℕ)]'h_pc = .assign zReg 0 := rfl
      simp only [URMState.step, hs0_pc, dif_pos h_pc, h_eq]
    set s1 : URMState P :=
        { pc := 1
          regs := Function.update s0.regs zReg 0 } with hs1
    have h_first : URMState.runFor P s0 1 = s1 := by
      change URMState.runFor P (URMState.step P s0) 0 = _
      rw [URMState.runFor_zero, h_step0]
    rw [h_first]
    have hs1_pc : s1.pc = 1 := rfl
    have hs1_zReg : s1.regs zReg = 0 := by
      change Function.update s0.regs zReg 0 zReg = 0
      rw [Function.update_self]
    have hs1_src : s1.regs src = v 0 := by
      change Function.update s0.regs zReg 0 src = v 0
      rw [Function.update_of_ne (Ne.symm h_disj_zs), hs0_src]
    have hs1_dst : s1.regs dst = 0 := by
      change Function.update s0.regs zReg 0 dst = 0
      rw [Function.update_of_ne (Ne.symm h_disj_zd), hs0_dst]
    have hs1_tmp : s1.regs tmp = 0 := by
      change Function.update s0.regs zReg 0 tmp = 0
      rw [Function.update_of_ne (Ne.symm h_disj_zt), hs0_tmp]
    -- preservingTransfer phase.
    rw [URMState.runFor_add]
    obtain ⟨pt_pc, pt_dst, _pt_src, _pt_tmp, _pt_z, _pt_oth⟩ :=
      preservingTransfer_correct P 1 src dst tmp zReg
        h_disj_sd h_disj_st h_disj_dt h_disj_zs h_disj_zd h_disj_zt
        H s1 hs1_pc hs1_zReg hs1_tmp (v 0) hs1_src
    set s2 : URMState P := URMState.runFor P s1 (9 * v 0 + 2)
      with hs2
    have hs2_pc : s2.pc = 10 := by
      have h10 : (1 : ℕ) + 9 = 10 := by omega
      rw [← h10]; exact pt_pc
    have hs2_dst : s2.regs dst = v 0 := by
      rw [pt_dst, hs1_dst]; omega
    -- Inc dst at PC 10.
    have h_step2 : URMState.step P s2 =
        { pc := 11
          regs := Function.update s2.regs dst (s2.regs dst + 1) } := by
      have h_pc : (10 : ℕ) < P.instrs.size := by decide
      have h_eq : P.instrs[(10 : ℕ)]'h_pc = .inc dst := rfl
      simp only [URMState.step, hs2_pc, dif_pos h_pc, h_eq]
    set s3 : URMState P :=
        { pc := 11
          regs := Function.update s2.regs dst (s2.regs dst + 1) }
      with hs3
    have h_third : URMState.runFor P s2 1 = s3 := by
      change URMState.runFor P (URMState.step P s2) 0 = _
      rw [URMState.runFor_zero, h_step2]
    rw [h_third]
    change (11 : ℕ) = (12 : ℕ) - 1
    rfl
  · -- After `9 * v 0 + 4` steps, output register holds v 0 + 1.
    have h_split : 9 * v 0 + 4 = 1 + ((9 * v 0 + 2) + 1) := by omega
    rw [h_split, URMState.runFor_add]
    have h_step0 : URMState.step P s0 =
        { pc := 1
          regs := Function.update s0.regs zReg 0 } := by
      have h_pc : (0 : ℕ) < P.instrs.size := by decide
      have h_eq : P.instrs[(0 : ℕ)]'h_pc = .assign zReg 0 := rfl
      simp only [URMState.step, hs0_pc, dif_pos h_pc, h_eq]
    set s1 : URMState P :=
        { pc := 1
          regs := Function.update s0.regs zReg 0 } with hs1
    have h_first : URMState.runFor P s0 1 = s1 := by
      change URMState.runFor P (URMState.step P s0) 0 = _
      rw [URMState.runFor_zero, h_step0]
    rw [h_first]
    have hs1_pc : s1.pc = 1 := rfl
    have hs1_zReg : s1.regs zReg = 0 := by
      change Function.update s0.regs zReg 0 zReg = 0
      rw [Function.update_self]
    have hs1_src : s1.regs src = v 0 := by
      change Function.update s0.regs zReg 0 src = v 0
      rw [Function.update_of_ne (Ne.symm h_disj_zs), hs0_src]
    have hs1_dst : s1.regs dst = 0 := by
      change Function.update s0.regs zReg 0 dst = 0
      rw [Function.update_of_ne (Ne.symm h_disj_zd), hs0_dst]
    have hs1_tmp : s1.regs tmp = 0 := by
      change Function.update s0.regs zReg 0 tmp = 0
      rw [Function.update_of_ne (Ne.symm h_disj_zt), hs0_tmp]
    rw [URMState.runFor_add]
    obtain ⟨pt_pc, pt_dst, _pt_src, _pt_tmp, _pt_z, _pt_oth⟩ :=
      preservingTransfer_correct P 1 src dst tmp zReg
        h_disj_sd h_disj_st h_disj_dt h_disj_zs h_disj_zd h_disj_zt
        H s1 hs1_pc hs1_zReg hs1_tmp (v 0) hs1_src
    set s2 : URMState P := URMState.runFor P s1 (9 * v 0 + 2)
      with hs2
    have hs2_pc : s2.pc = 10 := by
      have h10 : (1 : ℕ) + 9 = 10 := by omega
      rw [← h10]; exact pt_pc
    have hs2_dst : s2.regs dst = v 0 := by
      rw [pt_dst, hs1_dst]; omega
    have h_step2 : URMState.step P s2 =
        { pc := 11
          regs := Function.update s2.regs dst (s2.regs dst + 1) } := by
      have h_pc : (10 : ℕ) < P.instrs.size := by decide
      have h_eq : P.instrs[(10 : ℕ)]'h_pc = .inc dst := rfl
      simp only [URMState.step, hs2_pc, dif_pos h_pc, h_eq]
    set s3 : URMState P :=
        { pc := 11
          regs := Function.update s2.regs dst (s2.regs dst + 1) }
      with hs3
    have h_third : URMState.runFor P s2 1 = s3 := by
      change URMState.runFor P (URMState.step P s2) 0 = _
      rw [URMState.runFor_zero, h_step2]
    rw [h_third]
    -- Read off output: outputReg = dst.
    change Function.update s2.regs dst (s2.regs dst + 1)
        (compileER ERMor1.succ).outputReg = _
    have h_out : (compileER ERMor1.succ).outputReg = dst := rfl
    rw [h_out, Function.update_self, hs2_dst, ERMor1.interp_succ]
  · -- Per-step PC bound: for k < 9 * v 0 + 4, PC < 11.
    intro k hk
    -- Three phases: k = 0 (initial), 1 ≤ k ≤ 9 * v 0 + 3
    -- (assign + preservingTransfer), k = 9 * v 0 + 3 (after
    -- preservingTransfer, before inc dst).
    by_cases hk0 : k = 0
    · -- k = 0: PC = 0 < 11.
      subst hk0
      rw [URMState.runFor_zero]
      change (0 : ℕ) < (12 : ℕ) - 1
      decide
    · -- k ≥ 1: write k = 1 + k'.
      obtain ⟨k', rfl⟩ : ∃ k', k = 1 + k' :=
        ⟨k - 1, by omega⟩
      rw [URMState.runFor_add]
      -- Compute after first step.
      have h_step0 : URMState.step P s0 =
          { pc := 1
            regs := Function.update s0.regs zReg 0 } := by
        have h_pc : (0 : ℕ) < P.instrs.size := by decide
        have h_eq : P.instrs[(0 : ℕ)]'h_pc = .assign zReg 0 := rfl
        simp only [URMState.step, hs0_pc, dif_pos h_pc, h_eq]
      set s1 : URMState P :=
          { pc := 1
            regs := Function.update s0.regs zReg 0 } with hs1
      have h_first : URMState.runFor P s0 1 = s1 := by
        change URMState.runFor P (URMState.step P s0) 0 = _
        rw [URMState.runFor_zero, h_step0]
      rw [h_first]
      have hs1_pc : s1.pc = 1 := rfl
      have hs1_zReg : s1.regs zReg = 0 := by
        change Function.update s0.regs zReg 0 zReg = 0
        rw [Function.update_self]
      have hs1_src : s1.regs src = v 0 := by
        change Function.update s0.regs zReg 0 src = v 0
        rw [Function.update_of_ne (Ne.symm h_disj_zs), hs0_src]
      have hs1_tmp : s1.regs tmp = 0 := by
        change Function.update s0.regs zReg 0 tmp = 0
        rw [Function.update_of_ne (Ne.symm h_disj_zt), hs0_tmp]
      -- k' < 9 * v 0 + 3.
      have hk' : k' < 9 * v 0 + 3 := by omega
      by_cases hk1 : k' ≤ 9 * v 0 + 2
      · -- k' inside preservingTransfer phase.  PC ≤ 1 + 9 = 10.
        have h_pc_bound :=
          preservingTransfer_correct_pc_bound P 1 src dst tmp zReg
            h_disj_sd h_disj_st h_disj_dt h_disj_zs h_disj_zd
            h_disj_zt H s1 hs1_pc hs1_zReg hs1_tmp (v 0) hs1_src
            k' hk1
        -- size - 1 = 11.
        change (URMState.runFor P s1 k').pc < (12 : ℕ) - 1
        omega
      · -- k' = 9 * v 0 + 3: after preservingTransfer + at PC 10
        -- before inc dst.  But hk1 says ¬(k' ≤ 9*v0+2), so
        -- k' ≥ 9*v0+3.  hk' says k' < 9*v0+3.  Contradiction.
        push_neg at hk1
        omega

/-- Pre-stop PC and output for the `.proj i` atom.  After
`9 * v i + 3` steps the program reaches `pc = 10` (the stop
instruction at `size - 1`) with the output register holding
`v i = (ERMor1.proj i).interp v`; for every earlier step
count the PC is strictly less than `size - 1`. Atom case of
`compileER_pre_stop_correct`. -/
theorem compileER_pre_stop_correct_atom_proj {k : ℕ}
    (i : Fin k) (v : Fin k → ℕ) :
    ∃ T0 : ℕ,
      T0 ≤ compileER_runtime (.proj i : ERMor1 k) v ∧
      (URMState.runFor (compileER (ERMor1.proj i))
            (URMState.init (compileER (ERMor1.proj i)) v) T0).pc
          = (compileER (ERMor1.proj i)).instrs.size - 1 ∧
      (URMState.runFor (compileER (ERMor1.proj i))
            (URMState.init (compileER (ERMor1.proj i)) v) T0).regs
          (compileER (ERMor1.proj i)).outputReg
        = (ERMor1.proj i).interp v ∧
      (∀ k' < T0,
        (URMState.runFor (compileER (ERMor1.proj i))
            (URMState.init (compileER (ERMor1.proj i)) v) k').pc
          < (compileER (ERMor1.proj i)).instrs.size - 1) := by
  set P : URMProgram k := compileER (ERMor1.proj i) with hP
  set s0 : URMState P := URMState.init P v with hs0
  have hi : i.val < k := i.isLt
  set zReg : Fin P.numRegs := ⟨0, by change 0 < k + 3; omega⟩ with hzReg
  set dst  : Fin P.numRegs := ⟨1, by change 1 < k + 3; omega⟩ with hdst
  set src  : Fin P.numRegs := ⟨2 + i.val, by change 2 + i.val < k + 3; omega⟩
    with hsrc
  set tmp  : Fin P.numRegs := ⟨2 + k, by change 2 + k < k + 3; omega⟩ with htmp
  -- s0.regs values.
  have hs0_src : s0.regs src = v i := by
    change (URMState.init P v).regs (P.inputRegs i) = v i
    exact URMState.init_regs_inputRegs P v i
  have hs0_zReg : s0.regs zReg = 0 := by
    change (URMState.init P v).regs zReg = 0
    change (match (List.finRange k).find?
        (fun j => decide (P.inputRegs j = zReg)) with
      | some j => v j
      | none   => 0) = 0
    have h_none : (List.finRange k).find?
        (fun j => decide (P.inputRegs j = zReg)) = none := by
      apply List.find?_eq_none.mpr
      intro j _
      simp only [Bool.not_eq_true, decide_eq_false_iff_not]
      intro h
      have : (2 + j.val : ℕ) = 0 := congrArg Fin.val h
      omega
    rw [h_none]
  have hs0_dst : s0.regs dst = 0 := by
    change (URMState.init P v).regs dst = 0
    change (match (List.finRange k).find?
        (fun j => decide (P.inputRegs j = dst)) with
      | some j => v j
      | none   => 0) = 0
    have h_none : (List.finRange k).find?
        (fun j => decide (P.inputRegs j = dst)) = none := by
      apply List.find?_eq_none.mpr
      intro j _
      simp only [Bool.not_eq_true, decide_eq_false_iff_not]
      intro h
      have : (2 + j.val : ℕ) = 1 := congrArg Fin.val h
      omega
    rw [h_none]
  have hs0_tmp : s0.regs tmp = 0 := by
    change (URMState.init P v).regs tmp = 0
    change (match (List.finRange k).find?
        (fun j => decide (P.inputRegs j = tmp)) with
      | some j => v j
      | none   => 0) = 0
    have h_none : (List.finRange k).find?
        (fun j => decide (P.inputRegs j = tmp)) = none := by
      apply List.find?_eq_none.mpr
      intro j hj
      simp only [Bool.not_eq_true, decide_eq_false_iff_not]
      intro h
      have : (2 + j.val : ℕ) = 2 + k := congrArg Fin.val h
      have hjlt : j.val < k := j.isLt
      omega
    rw [h_none]
  have hs0_pc : s0.pc = 0 := rfl
  -- Disjointness of the four Fins.
  have h_disj_sd : src ≠ dst := by
    intro h
    have : (2 + i.val : ℕ) = 1 := congrArg Fin.val h
    omega
  have h_disj_st : src ≠ tmp := by
    intro h
    have : (2 + i.val : ℕ) = 2 + k := congrArg Fin.val h
    omega
  have h_disj_dt : dst ≠ tmp := by
    intro h
    have : (1 : ℕ) = 2 + k := congrArg Fin.val h
    omega
  have h_disj_zs : zReg ≠ src := by
    intro h
    have : (0 : ℕ) = 2 + i.val := congrArg Fin.val h
    omega
  have h_disj_zd : zReg ≠ dst := by
    intro h
    have : (0 : ℕ) = 1 := congrArg Fin.val h
    omega
  have h_disj_zt : zReg ≠ tmp := by
    intro h
    have : (0 : ℕ) = 2 + k := congrArg Fin.val h
    omega
  have H : PreservingTransferInstrs P 1 src dst tmp zReg := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rfl
  have h_size : P.instrs.size = 11 := rfl
  refine ⟨9 * v i + 3, ?_, ?_, ?_, ?_⟩
  · change 9 * v i + 3 ≤ 11 + 10 * v i
    omega
  · -- After `9 * v i + 3` steps, PC = 10 = size - 1.
    have h_split : 9 * v i + 3 = 1 + (9 * v i + 2) := by omega
    rw [h_split, URMState.runFor_add]
    have h_step0 : URMState.step P s0 =
        { pc := 1
          regs := Function.update s0.regs zReg 0 } := by
      have h_pc : (0 : ℕ) < P.instrs.size := by rw [h_size]; decide
      have h_eq : P.instrs[(0 : ℕ)]'h_pc = .assign zReg 0 := rfl
      simp only [URMState.step, hs0_pc, dif_pos h_pc, h_eq]
    set s1 : URMState P :=
        { pc := 1
          regs := Function.update s0.regs zReg 0 } with hs1
    have h_first : URMState.runFor P s0 1 = s1 := by
      change URMState.runFor P (URMState.step P s0) 0 = _
      rw [URMState.runFor_zero, h_step0]
    rw [h_first]
    have hs1_pc : s1.pc = 1 := rfl
    have hs1_zReg : s1.regs zReg = 0 := by
      change Function.update s0.regs zReg 0 zReg = 0
      rw [Function.update_self]
    have hs1_src : s1.regs src = v i := by
      change Function.update s0.regs zReg 0 src = v i
      rw [Function.update_of_ne (Ne.symm h_disj_zs), hs0_src]
    have hs1_tmp : s1.regs tmp = 0 := by
      change Function.update s0.regs zReg 0 tmp = 0
      rw [Function.update_of_ne (Ne.symm h_disj_zt), hs0_tmp]
    obtain ⟨pt_pc, _pt_dst, _pt_src, _pt_tmp, _pt_z, _pt_oth⟩ :=
      preservingTransfer_correct P 1 src dst tmp zReg
        h_disj_sd h_disj_st h_disj_dt h_disj_zs h_disj_zd h_disj_zt
        H s1 hs1_pc hs1_zReg hs1_tmp (v i) hs1_src
    have h10 : (URMState.runFor P s1 (9 * v i + 2)).pc = 10 := by
      have h10' : (1 : ℕ) + 9 = 10 := by omega
      rw [← h10']; exact pt_pc
    rw [h10]
    change (10 : ℕ) = (11 : ℕ) - 1
    rfl
  · -- After `9 * v i + 3` steps, output register holds v i.
    have h_split : 9 * v i + 3 = 1 + (9 * v i + 2) := by omega
    rw [h_split, URMState.runFor_add]
    have h_step0 : URMState.step P s0 =
        { pc := 1
          regs := Function.update s0.regs zReg 0 } := by
      have h_pc : (0 : ℕ) < P.instrs.size := by rw [h_size]; decide
      have h_eq : P.instrs[(0 : ℕ)]'h_pc = .assign zReg 0 := rfl
      simp only [URMState.step, hs0_pc, dif_pos h_pc, h_eq]
    set s1 : URMState P :=
        { pc := 1
          regs := Function.update s0.regs zReg 0 } with hs1
    have h_first : URMState.runFor P s0 1 = s1 := by
      change URMState.runFor P (URMState.step P s0) 0 = _
      rw [URMState.runFor_zero, h_step0]
    rw [h_first]
    have hs1_pc : s1.pc = 1 := rfl
    have hs1_zReg : s1.regs zReg = 0 := by
      change Function.update s0.regs zReg 0 zReg = 0
      rw [Function.update_self]
    have hs1_src : s1.regs src = v i := by
      change Function.update s0.regs zReg 0 src = v i
      rw [Function.update_of_ne (Ne.symm h_disj_zs), hs0_src]
    have hs1_dst : s1.regs dst = 0 := by
      change Function.update s0.regs zReg 0 dst = 0
      rw [Function.update_of_ne (Ne.symm h_disj_zd), hs0_dst]
    have hs1_tmp : s1.regs tmp = 0 := by
      change Function.update s0.regs zReg 0 tmp = 0
      rw [Function.update_of_ne (Ne.symm h_disj_zt), hs0_tmp]
    obtain ⟨_pt_pc, pt_dst, _pt_src, _pt_tmp, _pt_z, _pt_oth⟩ :=
      preservingTransfer_correct P 1 src dst tmp zReg
        h_disj_sd h_disj_st h_disj_dt h_disj_zs h_disj_zd h_disj_zt
        H s1 hs1_pc hs1_zReg hs1_tmp (v i) hs1_src
    set s2 : URMState P := URMState.runFor P s1 (9 * v i + 2)
    have hs2_dst : s2.regs dst = v i := by
      rw [pt_dst, hs1_dst]; omega
    change s2.regs (compileER (ERMor1.proj i)).outputReg = _
    have h_out : (compileER (ERMor1.proj i)).outputReg = dst := rfl
    rw [h_out, hs2_dst, ERMor1.interp_proj]
  · -- Per-step PC bound: for k' < 9 * v i + 3, PC < 10.
    intro k' hk'
    by_cases hk0 : k' = 0
    · subst hk0
      rw [URMState.runFor_zero]
      change (0 : ℕ) < (11 : ℕ) - 1
      decide
    · obtain ⟨k'', rfl⟩ : ∃ k'', k' = 1 + k'' :=
        ⟨k' - 1, by omega⟩
      rw [URMState.runFor_add]
      have h_step0 : URMState.step P s0 =
          { pc := 1
            regs := Function.update s0.regs zReg 0 } := by
        have h_pc : (0 : ℕ) < P.instrs.size := by rw [h_size]; decide
        have h_eq : P.instrs[(0 : ℕ)]'h_pc = .assign zReg 0 := rfl
        simp only [URMState.step, hs0_pc, dif_pos h_pc, h_eq]
      set s1 : URMState P :=
          { pc := 1
            regs := Function.update s0.regs zReg 0 } with hs1
      have h_first : URMState.runFor P s0 1 = s1 := by
        change URMState.runFor P (URMState.step P s0) 0 = _
        rw [URMState.runFor_zero, h_step0]
      rw [h_first]
      have hs1_pc : s1.pc = 1 := rfl
      have hs1_zReg : s1.regs zReg = 0 := by
        change Function.update s0.regs zReg 0 zReg = 0
        rw [Function.update_self]
      have hs1_src : s1.regs src = v i := by
        change Function.update s0.regs zReg 0 src = v i
        rw [Function.update_of_ne (Ne.symm h_disj_zs), hs0_src]
      have hs1_tmp : s1.regs tmp = 0 := by
        change Function.update s0.regs zReg 0 tmp = 0
        rw [Function.update_of_ne (Ne.symm h_disj_zt), hs0_tmp]
      have hk'' : k'' < 9 * v i + 2 := by omega
      have h_pc_bound :=
        preservingTransfer_correct_pc_strict_bound P 1 src dst tmp zReg
          h_disj_sd h_disj_st h_disj_dt h_disj_zs h_disj_zd
          h_disj_zt H s1 hs1_pc hs1_zReg hs1_tmp (v i) hs1_src
          k'' hk''
      change (URMState.runFor P s1 k'').pc < (11 : ℕ) - 1
      omega

/-- Pre-stop PC and output for the `.sub` atom.  After
`9 * v 0 + 8 * v 1 + 5` steps the program reaches `pc = 18`
(the stop instruction at `size - 1`) with the output register
holding `v 0 - v 1 = ERMor1.sub.interp v`; for every earlier
step count the PC is strictly less than `size - 1`. Atom
case of `compileER_pre_stop_correct`. -/
theorem compileER_pre_stop_correct_atom_sub
    (v : Fin 2 → ℕ) :
    ∃ T0 : ℕ,
      T0 ≤ compileER_runtime (.sub : ERMor1 2) v ∧
      (URMState.runFor (compileER ERMor1.sub)
            (URMState.init (compileER ERMor1.sub) v) T0).pc
          = (compileER ERMor1.sub).instrs.size - 1 ∧
      (URMState.runFor (compileER ERMor1.sub)
            (URMState.init (compileER ERMor1.sub) v) T0).regs
          (compileER ERMor1.sub).outputReg
        = ERMor1.sub.interp v ∧
      (∀ k < T0,
        (URMState.runFor (compileER ERMor1.sub)
            (URMState.init (compileER ERMor1.sub) v) k).pc
          < (compileER ERMor1.sub).instrs.size - 1) := by
  set P : URMProgram 2 := compileER ERMor1.sub with hP
  set s0 : URMState P := URMState.init P v with hs0
  -- Six Fins of `P.numRegs = 6`.
  set zReg : Fin P.numRegs := ⟨0, by decide⟩ with hzReg
  set dst  : Fin P.numRegs := ⟨1, by decide⟩ with hdst
  set xReg : Fin P.numRegs := ⟨2, by decide⟩ with hxReg
  set yReg : Fin P.numRegs := ⟨3, by decide⟩ with hyReg
  set tmp  : Fin P.numRegs := ⟨4, by decide⟩ with htmp
  set sReg : Fin P.numRegs := ⟨5, by decide⟩ with hsReg
  have hs0_xReg : s0.regs xReg = v 0 := by
    change (URMState.init P v).regs xReg = v 0
    rw [show xReg = P.inputRegs 0 from rfl]
    exact URMState.init_regs_inputRegs P v 0
  have hs0_yReg : s0.regs yReg = v 1 := by
    change (URMState.init P v).regs yReg = v 1
    rw [show yReg = P.inputRegs 1 from rfl]
    exact URMState.init_regs_inputRegs P v 1
  have hs0_zReg : s0.regs zReg = 0 := rfl
  have hs0_dst : s0.regs dst = 0 := rfl
  have hs0_tmp : s0.regs tmp = 0 := rfl
  have hs0_sReg : s0.regs sReg = 0 := rfl
  have hs0_pc : s0.pc = 0 := rfl
  -- Disjointness lemmas: each pair distinct by Fin.val.
  have h_disj_zd : zReg ≠ dst := by
    intro h; exact absurd (congrArg Fin.val h) (by decide)
  have h_disj_zx : zReg ≠ xReg := by
    intro h; exact absurd (congrArg Fin.val h) (by decide)
  have h_disj_zy : zReg ≠ yReg := by
    intro h; exact absurd (congrArg Fin.val h) (by decide)
  have h_disj_zt : zReg ≠ tmp := by
    intro h; exact absurd (congrArg Fin.val h) (by decide)
  have h_disj_zs : zReg ≠ sReg := by
    intro h; exact absurd (congrArg Fin.val h) (by decide)
  have h_disj_dx : dst ≠ xReg := by
    intro h; exact absurd (congrArg Fin.val h) (by decide)
  have h_disj_dy : dst ≠ yReg := by
    intro h; exact absurd (congrArg Fin.val h) (by decide)
  have h_disj_dt : dst ≠ tmp := by
    intro h; exact absurd (congrArg Fin.val h) (by decide)
  have h_disj_ds : dst ≠ sReg := by
    intro h; exact absurd (congrArg Fin.val h) (by decide)
  have h_disj_xy : xReg ≠ yReg := by
    intro h; exact absurd (congrArg Fin.val h) (by decide)
  have h_disj_xt : xReg ≠ tmp := by
    intro h; exact absurd (congrArg Fin.val h) (by decide)
  have h_disj_xs : xReg ≠ sReg := by
    intro h; exact absurd (congrArg Fin.val h) (by decide)
  have h_disj_yt : yReg ≠ tmp := by
    intro h; exact absurd (congrArg Fin.val h) (by decide)
  have h_disj_ys : yReg ≠ sReg := by
    intro h; exact absurd (congrArg Fin.val h) (by decide)
  have h_disj_ts : tmp ≠ sReg := by
    intro h; exact absurd (congrArg Fin.val h) (by decide)
  have Hpt : PreservingTransferInstrs P 1 xReg dst tmp zReg := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rfl
  have Htl : TransferLoopInstrs P 10 yReg sReg zReg := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> rfl
  have Hsi : SubInnerLoopInstrs P 14 sReg dst zReg := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> rfl
  have h_size : P.instrs.size = 19 := rfl
  refine ⟨9 * v 0 + 8 * v 1 + 5, ?_, ?_, ?_, ?_⟩
  · change 9 * v 0 + 8 * v 1 + 5 ≤ 20 + 10 * v 0 + 10 * v 1
    omega
  · -- After `9 * v 0 + 8 * v 1 + 5` steps, PC = 18 = size - 1.
    have h_split :
        9 * v 0 + 8 * v 1 + 5
          = 1 + ((9 * v 0 + 2)
            + ((4 * v 1 + 1) + (4 * v 1 + 1))) := by omega
    rw [h_split, URMState.runFor_add]
    have h_step0 : URMState.step P s0 =
        { pc := 1
          regs := Function.update s0.regs zReg 0 } := by
      have h_pc : (0 : ℕ) < P.instrs.size := by decide
      have h_eq : P.instrs[(0 : ℕ)]'h_pc = .assign zReg 0 := rfl
      simp only [URMState.step, hs0_pc, dif_pos h_pc, h_eq]
    set s1 : URMState P :=
        { pc := 1
          regs := Function.update s0.regs zReg 0 } with hs1
    have h_first : URMState.runFor P s0 1 = s1 := by
      change URMState.runFor P (URMState.step P s0) 0 = _
      rw [URMState.runFor_zero, h_step0]
    rw [h_first]
    have hs1_pc : s1.pc = 1 := rfl
    have hs1_zReg : s1.regs zReg = 0 := by
      change Function.update s0.regs zReg 0 zReg = 0
      rw [Function.update_self]
    have hs1_xReg : s1.regs xReg = v 0 := by
      change Function.update s0.regs zReg 0 xReg = v 0
      rw [Function.update_of_ne (Ne.symm h_disj_zx), hs0_xReg]
    have hs1_yReg : s1.regs yReg = v 1 := by
      change Function.update s0.regs zReg 0 yReg = v 1
      rw [Function.update_of_ne (Ne.symm h_disj_zy), hs0_yReg]
    have hs1_dst : s1.regs dst = 0 := by
      change Function.update s0.regs zReg 0 dst = 0
      rw [Function.update_of_ne (Ne.symm h_disj_zd), hs0_dst]
    have hs1_tmp : s1.regs tmp = 0 := by
      change Function.update s0.regs zReg 0 tmp = 0
      rw [Function.update_of_ne (Ne.symm h_disj_zt), hs0_tmp]
    have hs1_sReg : s1.regs sReg = 0 := by
      change Function.update s0.regs zReg 0 sReg = 0
      rw [Function.update_of_ne (Ne.symm h_disj_zs), hs0_sReg]
    rw [URMState.runFor_add]
    obtain ⟨pt_pc, _pt_dst, _pt_xReg, pt_tmp, pt_z, pt_oth⟩ :=
      preservingTransfer_correct P 1 xReg dst tmp zReg
        h_disj_dx.symm h_disj_xt h_disj_dt h_disj_zx h_disj_zd h_disj_zt
        Hpt s1 hs1_pc hs1_zReg hs1_tmp (v 0) hs1_xReg
    set s2 : URMState P := URMState.runFor P s1 (9 * v 0 + 2)
    have hs2_pc : s2.pc = 10 := by
      have h10 : (1 : ℕ) + 9 = 10 := by omega
      rw [← h10]; exact pt_pc
    have hs2_zReg : s2.regs zReg = 0 := pt_z
    have hs2_yReg : s2.regs yReg = v 1 := by
      rw [pt_oth yReg (Ne.symm h_disj_dy), hs1_yReg]
    have hs2_sReg : s2.regs sReg = 0 := by
      rw [pt_oth sReg (Ne.symm h_disj_ds), hs1_sReg]
    rw [URMState.runFor_add]
    obtain ⟨tl_pc, tl_sReg, _tl_yReg, tl_z, _tl_oth⟩ :=
      transferLoop_correct P 10 yReg sReg zReg
        h_disj_ys h_disj_zy h_disj_zs
        Htl s2 hs2_pc hs2_zReg (v 1) hs2_yReg
    set s3 : URMState P := URMState.runFor P s2 (4 * v 1 + 1)
    have hs3_pc : s3.pc = 14 := by
      have h14 : (10 : ℕ) + 4 = 14 := by omega
      rw [← h14]; exact tl_pc
    have hs3_sReg : s3.regs sReg = v 1 := by
      rw [tl_sReg, hs2_sReg]; omega
    have hs3_zReg : s3.regs zReg = 0 := tl_z
    obtain ⟨si_pc, _si_dst, _si_sReg, _si_z, _si_oth⟩ :=
      subInnerLoop_correct P 14 sReg dst zReg
        h_disj_ds.symm h_disj_zs h_disj_zd
        Hsi s3 hs3_pc hs3_zReg (v 1) hs3_sReg
    set s4 : URMState P := URMState.runFor P s3 (4 * v 1 + 1)
    have hs4_pc : s4.pc = 18 := by
      have h18 : (14 : ℕ) + 4 = 18 := by omega
      rw [← h18]; exact si_pc
    rw [hs4_pc]
    change (18 : ℕ) = (19 : ℕ) - 1
    rfl
  · -- After `9 * v 0 + 8 * v 1 + 5` steps, output = v 0 - v 1.
    have h_split :
        9 * v 0 + 8 * v 1 + 5
          = 1 + ((9 * v 0 + 2)
            + ((4 * v 1 + 1) + (4 * v 1 + 1))) := by omega
    rw [h_split, URMState.runFor_add]
    have h_step0 : URMState.step P s0 =
        { pc := 1
          regs := Function.update s0.regs zReg 0 } := by
      have h_pc : (0 : ℕ) < P.instrs.size := by decide
      have h_eq : P.instrs[(0 : ℕ)]'h_pc = .assign zReg 0 := rfl
      simp only [URMState.step, hs0_pc, dif_pos h_pc, h_eq]
    set s1 : URMState P :=
        { pc := 1
          regs := Function.update s0.regs zReg 0 } with hs1
    have h_first : URMState.runFor P s0 1 = s1 := by
      change URMState.runFor P (URMState.step P s0) 0 = _
      rw [URMState.runFor_zero, h_step0]
    rw [h_first]
    have hs1_pc : s1.pc = 1 := rfl
    have hs1_zReg : s1.regs zReg = 0 := by
      change Function.update s0.regs zReg 0 zReg = 0
      rw [Function.update_self]
    have hs1_xReg : s1.regs xReg = v 0 := by
      change Function.update s0.regs zReg 0 xReg = v 0
      rw [Function.update_of_ne (Ne.symm h_disj_zx), hs0_xReg]
    have hs1_yReg : s1.regs yReg = v 1 := by
      change Function.update s0.regs zReg 0 yReg = v 1
      rw [Function.update_of_ne (Ne.symm h_disj_zy), hs0_yReg]
    have hs1_dst : s1.regs dst = 0 := by
      change Function.update s0.regs zReg 0 dst = 0
      rw [Function.update_of_ne (Ne.symm h_disj_zd), hs0_dst]
    have hs1_tmp : s1.regs tmp = 0 := by
      change Function.update s0.regs zReg 0 tmp = 0
      rw [Function.update_of_ne (Ne.symm h_disj_zt), hs0_tmp]
    have hs1_sReg : s1.regs sReg = 0 := by
      change Function.update s0.regs zReg 0 sReg = 0
      rw [Function.update_of_ne (Ne.symm h_disj_zs), hs0_sReg]
    rw [URMState.runFor_add]
    obtain ⟨pt_pc, pt_dst, _pt_xReg, pt_tmp, pt_z, pt_oth⟩ :=
      preservingTransfer_correct P 1 xReg dst tmp zReg
        h_disj_dx.symm h_disj_xt h_disj_dt h_disj_zx h_disj_zd h_disj_zt
        Hpt s1 hs1_pc hs1_zReg hs1_tmp (v 0) hs1_xReg
    set s2 : URMState P := URMState.runFor P s1 (9 * v 0 + 2)
    have hs2_pc : s2.pc = 10 := by
      have h10 : (1 : ℕ) + 9 = 10 := by omega
      rw [← h10]; exact pt_pc
    have hs2_dst : s2.regs dst = v 0 := by
      rw [pt_dst, hs1_dst]; omega
    have hs2_zReg : s2.regs zReg = 0 := pt_z
    have hs2_yReg : s2.regs yReg = v 1 := by
      rw [pt_oth yReg (Ne.symm h_disj_dy), hs1_yReg]
    have hs2_sReg : s2.regs sReg = 0 := by
      rw [pt_oth sReg (Ne.symm h_disj_ds), hs1_sReg]
    rw [URMState.runFor_add]
    obtain ⟨tl_pc, tl_sReg, _tl_yReg, tl_z, tl_oth⟩ :=
      transferLoop_correct P 10 yReg sReg zReg
        h_disj_ys h_disj_zy h_disj_zs
        Htl s2 hs2_pc hs2_zReg (v 1) hs2_yReg
    set s3 : URMState P := URMState.runFor P s2 (4 * v 1 + 1)
    have hs3_pc : s3.pc = 14 := by
      have h14 : (10 : ℕ) + 4 = 14 := by omega
      rw [← h14]; exact tl_pc
    have hs3_sReg : s3.regs sReg = v 1 := by
      rw [tl_sReg, hs2_sReg]; omega
    have hs3_dst : s3.regs dst = v 0 := by
      have h := tl_oth dst h_disj_ds h_disj_dy h_disj_zd.symm
      rw [h, hs2_dst]
    have hs3_zReg : s3.regs zReg = 0 := tl_z
    obtain ⟨_si_pc, si_dst, _si_sReg, _si_z, _si_oth⟩ :=
      subInnerLoop_correct P 14 sReg dst zReg
        h_disj_ds.symm h_disj_zs h_disj_zd
        Hsi s3 hs3_pc hs3_zReg (v 1) hs3_sReg
    set s4 : URMState P := URMState.runFor P s3 (4 * v 1 + 1)
    have hs4_dst : s4.regs dst = v 0 - v 1 := by
      rw [si_dst, hs3_dst]
    change s4.regs (compileER ERMor1.sub).outputReg = _
    have h_out : (compileER ERMor1.sub).outputReg = dst := rfl
    rw [h_out, hs4_dst, ERMor1.interp_sub]
  · -- Per-step PC bound: for k < 9 * v 0 + 8 * v 1 + 5, PC < 18.
    intro k hk
    by_cases hk0 : k = 0
    · subst hk0
      rw [URMState.runFor_zero]
      change (0 : ℕ) < (19 : ℕ) - 1
      decide
    · obtain ⟨k', rfl⟩ : ∃ k', k = 1 + k' :=
        ⟨k - 1, by omega⟩
      rw [URMState.runFor_add]
      have h_step0 : URMState.step P s0 =
          { pc := 1
            regs := Function.update s0.regs zReg 0 } := by
        have h_pc : (0 : ℕ) < P.instrs.size := by decide
        have h_eq : P.instrs[(0 : ℕ)]'h_pc = .assign zReg 0 := rfl
        simp only [URMState.step, hs0_pc, dif_pos h_pc, h_eq]
      set s1 : URMState P :=
          { pc := 1
            regs := Function.update s0.regs zReg 0 } with hs1
      have h_first : URMState.runFor P s0 1 = s1 := by
        change URMState.runFor P (URMState.step P s0) 0 = _
        rw [URMState.runFor_zero, h_step0]
      rw [h_first]
      have hs1_pc : s1.pc = 1 := rfl
      have hs1_zReg : s1.regs zReg = 0 := by
        change Function.update s0.regs zReg 0 zReg = 0
        rw [Function.update_self]
      have hs1_xReg : s1.regs xReg = v 0 := by
        change Function.update s0.regs zReg 0 xReg = v 0
        rw [Function.update_of_ne (Ne.symm h_disj_zx), hs0_xReg]
      have hs1_yReg : s1.regs yReg = v 1 := by
        change Function.update s0.regs zReg 0 yReg = v 1
        rw [Function.update_of_ne (Ne.symm h_disj_zy), hs0_yReg]
      have hs1_dst : s1.regs dst = 0 := by
        change Function.update s0.regs zReg 0 dst = 0
        rw [Function.update_of_ne (Ne.symm h_disj_zd), hs0_dst]
      have hs1_tmp : s1.regs tmp = 0 := by
        change Function.update s0.regs zReg 0 tmp = 0
        rw [Function.update_of_ne (Ne.symm h_disj_zt), hs0_tmp]
      have hs1_sReg : s1.regs sReg = 0 := by
        change Function.update s0.regs zReg 0 sReg = 0
        rw [Function.update_of_ne (Ne.symm h_disj_zs), hs0_sReg]
      -- k' < 9 * v 0 + 8 * v 1 + 4.  Three sub-phases:
      -- preservingTransfer (≤ 9*v0+2), transferLoop
      -- (≤ 4*v1+1), subInnerLoop (≤ 4*v1+1).
      by_cases hkA : k' ≤ 9 * v 0 + 2
      · -- Inside preservingTransfer: PC ≤ 1 + 9 = 10 < 18.
        have h_pc_bound :=
          preservingTransfer_correct_pc_bound P 1 xReg dst tmp zReg
            h_disj_dx.symm h_disj_xt h_disj_dt h_disj_zx h_disj_zd
            h_disj_zt Hpt s1 hs1_pc hs1_zReg hs1_tmp (v 0) hs1_xReg
            k' hkA
        change (URMState.runFor P s1 k').pc < (19 : ℕ) - 1
        omega
      · -- k' beyond preservingTransfer; split off the
        -- preservingTransfer phase.
        push_neg at hkA
        obtain ⟨kA, rfl⟩ : ∃ kA, k' = (9 * v 0 + 2) + kA :=
          ⟨k' - (9 * v 0 + 2), by omega⟩
        rw [URMState.runFor_add]
        obtain ⟨pt_pc, _pt_dst, _pt_xReg, pt_tmp, pt_z, pt_oth⟩ :=
          preservingTransfer_correct P 1 xReg dst tmp zReg
            h_disj_dx.symm h_disj_xt h_disj_dt h_disj_zx h_disj_zd h_disj_zt
            Hpt s1 hs1_pc hs1_zReg hs1_tmp (v 0) hs1_xReg
        set s2 : URMState P := URMState.runFor P s1 (9 * v 0 + 2)
        have hs2_pc : s2.pc = 10 := by
          have h10 : (1 : ℕ) + 9 = 10 := by omega
          rw [← h10]; exact pt_pc
        have hs2_zReg : s2.regs zReg = 0 := pt_z
        have hs2_yReg : s2.regs yReg = v 1 := by
          rw [pt_oth yReg (Ne.symm h_disj_dy), hs1_yReg]
        have hs2_sReg : s2.regs sReg = 0 := by
          rw [pt_oth sReg (Ne.symm h_disj_ds), hs1_sReg]
        -- kA < 8 * v 1 + 3.
        by_cases hkB : kA ≤ 4 * v 1 + 1
        · -- Inside transferLoop: PC ≤ 10 + 4 = 14 < 18.
          have h_pc_bound :=
            transferLoop_correct_pc_bound P 10 yReg sReg zReg
              h_disj_ys h_disj_zy h_disj_zs Htl s2 hs2_pc
              hs2_zReg (v 1) hs2_yReg kA hkB
          change (URMState.runFor P s2 kA).pc < (19 : ℕ) - 1
          omega
        · -- kA beyond transferLoop; split off the transferLoop
          -- phase.  kA = (4*v1+1) + kB with kB ≤ 4*v1 + 1 - 1.
          push_neg at hkB
          obtain ⟨kB, rfl⟩ : ∃ kB, kA = (4 * v 1 + 1) + kB :=
            ⟨kA - (4 * v 1 + 1), by omega⟩
          rw [URMState.runFor_add]
          obtain ⟨tl_pc, tl_sReg, _tl_yReg, tl_z, _tl_oth⟩ :=
            transferLoop_correct P 10 yReg sReg zReg
              h_disj_ys h_disj_zy h_disj_zs
              Htl s2 hs2_pc hs2_zReg (v 1) hs2_yReg
          set s3 : URMState P := URMState.runFor P s2 (4 * v 1 + 1)
          have hs3_pc : s3.pc = 14 := by
            have h14 : (10 : ℕ) + 4 = 14 := by omega
            rw [← h14]; exact tl_pc
          have hs3_sReg : s3.regs sReg = v 1 := by
            rw [tl_sReg, hs2_sReg]; omega
          have hs3_zReg : s3.regs zReg = 0 := tl_z
          -- kB ≤ 4 * v 1 (strict bound from kB < 4 * v 1 + 1).
          have hkB' : kB ≤ 4 * v 1 := by omega
          have h_pc_bound :=
            subInnerLoop_correct_pc_strict_bound P 14 sReg dst zReg
              h_disj_ds.symm h_disj_zs h_disj_zd Hsi s3 hs3_pc
              hs3_zReg (v 1) hs3_sReg kB hkB'
          change (URMState.runFor P s3 kB).pc < (19 : ℕ) - 1
          omega

end LawvereERKSim
end GebLean
