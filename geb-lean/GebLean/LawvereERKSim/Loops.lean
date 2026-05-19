import GebLean.LawvereERKSim.Embedding

/-!
# LawvereERKSim — loop-correctness theorems

Correctness theorems for the three URM loop combinators used by the atom and
comp compilers: `URMRaw.transferLoop` (4n+1 steps), `URMRaw.preservingTransfer`
(9n+2 steps via two inner loops), and the inner loop of `compileFrag_sub`. Each
"correct" theorem comes with per-step and strict per-step PC-bound siblings.

Also includes two `compileFrag_comp`-specific instruction-presence dischargers
(`PreservingTransferInstrs_compileFrag_comp_inputCopies`,
`TransferLoopInstrs_compileFrag_comp_outputTransfer`) that exhibit
`compileFrag_comp_subBlock`'s layout as instances of the loop patterns. The
`preservingTransferInstrs`, `transferLoopInstrs`, and `subInnerLoopInstrs`
structures are exposed beyond file scope because the still-monolithic
atom-correctness and comp pre-stop theorems consume them as hypothesis-bundle
types. Future tasks that complete the Atoms and Comp submodule extractions can
restore `private` where no inter-file consumer remains.

## Main definitions

- `preservingTransferInstrs`, `transferLoopInstrs`, `subInnerLoopInstrs`:
  packaged hypothesis bundles (structures) for each loop pattern.

## Main statements

- `preservingTransfer_correct`, `preservingTransfer_correct_pc_bound`,
  `preservingTransfer_correct_pc_strict_bound`, with inner helpers
  `preservingTransfer_loop1`, `preservingTransfer_loop1_pc_bound`,
  `preservingTransfer_loop2`, `preservingTransfer_loop2_pc_bound`,
  `preservingTransfer_loop2_pc_strict_bound`.
- `transferLoop_correct`, `transferLoop_correct_pc_bound`,
  `transferLoop_correct_pc_strict_bound`.
- `subInnerLoop_correct`, `subInnerLoop_correct_pc_bound`,
  `subInnerLoop_correct_pc_strict_bound`.
- `PreservingTransferInstrs_compileFrag_comp_inputCopies`,
  `TransferLoopInstrs_compileFrag_comp_outputTransfer`: comp-layout dischargers.

## References

- Tourlakis 2018 `PR-complexity-topics.pdf` §0.1.0.37 (URM kernel and
  Tourlakis-style transfer loops).
- Spec: `docs/superpowers/specs/2026-05-19-lawvere-er-k-sim-file-split-design.md`.
-/

namespace GebLean
namespace LawvereERKSim

open GebLean.ZeroTestURM

/-- Hypothesis bundle for `preservingTransfer_correct`:
the nine instruction-lookup equalities at PCs `pcBase..pcBase+8`
matching the raw layout of `URMRaw.preservingTransfer`. The
`zReg` parameter holds the reserved-zero register used by
`URMRaw.goto`; `h_zReg` asserts its value is 0 so the
`goto` jumps fire unconditionally. -/
structure preservingTransferInstrs {a : ℕ}
    (P : URMProgram a) (pcBase : ℕ)
    (src dst tmp zReg : Fin P.numRegs) : Prop where
  h0 : P.instrs[pcBase]? =
    some (.jumpZ src (pcBase + 5) (pcBase + 1))
  h1 : P.instrs[pcBase + 1]? = some (.dec src)
  h2 : P.instrs[pcBase + 2]? = some (.inc dst)
  h3 : P.instrs[pcBase + 3]? = some (.inc tmp)
  h4 : P.instrs[pcBase + 4]? = some (.jumpZ zReg pcBase pcBase)
  h5 : P.instrs[pcBase + 5]? =
    some (.jumpZ tmp (pcBase + 9) (pcBase + 6))
  h6 : P.instrs[pcBase + 6]? = some (.dec tmp)
  h7 : P.instrs[pcBase + 7]? = some (.inc src)
  h8 : P.instrs[pcBase + 8]? =
    some (.jumpZ zReg (pcBase + 5) (pcBase + 5))

/-- For `compileFrag_comp`'s `i`-th sub-block, `j`-th
input-copy preservingTransfer: at PCs
`pcBase_i + 9 * j ..  pcBase_i + 9 * j + 8`, the outer
program's instructions match the nine raw instructions of
`URMRaw.preservingTransfer (pcBase_i + 9 * j.val) (2 + j.val)
(gsBase_i + ((frag_gs i).inputRegs j).val) tmpReg`, after
`URMInstrRaw.toBounded` conversion. The four register
arguments (`src`, `dst`, `tmp`, `zReg`) match those used
inside `compileFrag_comp_subBlock`'s input-copy preamble.
Parallels `ProgramEmbedsFragment_compileFrag_comp_gsBody`
for Phase i.2 (gs body); this lemma covers Phase i.1
(input-copies preamble). -/
theorem PreservingTransferInstrs_compileFrag_comp_inputCopies
    {k a : ℕ}
    (frag_f : CompiledFragment k)
    (frag_gs : Fin k → CompiledFragment a)
    (i : Fin k) (j : Fin a) :
    let outer := (compileFrag_comp frag_f frag_gs).toURMProgram
    let blockLen : Fin k → ℕ := fun i =>
      9 * a + ((frag_gs i).instrs.size - 1) + 4
    let pcBase_i : ℕ :=
      1 + ((List.finRange k).filter
          (fun n => decide (n.val < i.val))).foldr
        (fun n acc => acc + blockLen n) 0
    let gsBase_i : ℕ := 2 + a + gsPrefixSum frag_gs i.val
    let tmpReg : ℕ :=
      2 + a + gsPrefixSum frag_gs k + frag_f.numRegs
    ∃ (h_src : 2 + j.val < outer.numRegs)
      (h_dst : gsBase_i + ((frag_gs i).inputRegs j).val
                 < outer.numRegs)
      (h_tmp : tmpReg < outer.numRegs)
      (h_z : 0 < outer.numRegs),
      preservingTransferInstrs outer (pcBase_i + 9 * j.val)
        ⟨2 + j.val, h_src⟩
        ⟨gsBase_i + ((frag_gs i).inputRegs j).val, h_dst⟩
        ⟨tmpReg, h_tmp⟩
        ⟨0, h_z⟩ := by
  intro outer blockLen pcBase_i gsBase_i tmpReg
  -- Auxiliaries matching the constructor of compileFrag_comp.
  let totalGsRegs : ℕ := gsPrefixSum frag_gs k
  let fBase : ℕ := 2 + a + totalGsRegs
  let nR : ℕ := tmpReg + 1
  let gsBase : Fin k → ℕ :=
    fun j => 2 + a + gsPrefixSum frag_gs j.val
  let pcBase : Fin k → ℕ := fun j =>
    1 + ((List.finRange k).filter
        (fun n => decide (n.val < j.val))).foldr
      (fun n acc => acc + blockLen n) 0
  let subBlocks : List URMInstrRaw :=
    (List.finRange k).flatMap fun n =>
      compileFrag_comp_subBlock frag_f frag_gs
        (gsBase n) fBase tmpReg n (pcBase n)
  let fPcBase : ℕ :=
    1 + (List.finRange k).foldr
      (fun j acc => acc + blockLen j) 0
  let fBody : List URMInstrRaw :=
    frag_f.instrs.toList.map fun ins =>
      URMInstrRaw.reindexShift fBase fPcBase (toRawOfBounded ins)
  let rawList : List URMInstrRaw :=
    (.assignR 0 0) :: (subBlocks ++ fBody)
  -- Bound facts.
  have h_a_le_fBase : a ≤ fBase := by
    change a ≤ 2 + a + totalGsRegs; omega
  have h_jLt : j.val + 1 ≤ a := j.isLt
  have h_src_lt : 2 + j.val < nR := by
    change 2 + j.val < tmpReg + 1
    change 2 + j.val < (fBase + frag_f.numRegs) + 1
    omega
  have h_gsBlock_i : gsBase i + (frag_gs i).numRegs ≤ fBase := by
    have hmono : gsPrefixSum frag_gs (i.val + 1)
        ≤ gsPrefixSum frag_gs k :=
      gsPrefixSum_mono frag_gs i.isLt
    have hsucc :
        gsPrefixSum frag_gs (i.val + 1)
          = gsPrefixSum frag_gs i.val + (frag_gs i).numRegs :=
      gsPrefixSum_succ_eq frag_gs i
    change 2 + a + gsPrefixSum frag_gs i.val
        + (frag_gs i).numRegs ≤ 2 + a + totalGsRegs
    change _ ≤ gsPrefixSum frag_gs k at hmono
    omega
  have h_dst_lt :
      gsBase_i + ((frag_gs i).inputRegs j).val < nR := by
    have hI : ((frag_gs i).inputRegs j).val < (frag_gs i).numRegs :=
      ((frag_gs i).inputRegs j).isLt
    have h_gsBlock_i' :
        2 + a + gsPrefixSum frag_gs i.val + (frag_gs i).numRegs
          ≤ fBase := h_gsBlock_i
    change 2 + a + gsPrefixSum frag_gs i.val
        + ((frag_gs i).inputRegs j).val < tmpReg + 1
    change _ < (fBase + frag_f.numRegs) + 1
    omega
  have h_tmp_lt : tmpReg < nR := by
    change tmpReg < tmpReg + 1; omega
  have h_z_lt : 0 < nR := by
    change 0 < tmpReg + 1; omega
  have h_numRegs_eq : outer.numRegs = nR := rfl
  refine ⟨h_src_lt, h_dst_lt, h_tmp_lt, h_z_lt, ?_⟩
  -- Sub-block at i: split subBlocks via flatMap_finRange_split.
  obtain ⟨pre, suf, h_subBlocks_split, h_pre_len⟩ :=
    flatMap_finRange_split k
      (fun n => compileFrag_comp_subBlock frag_f frag_gs
        (gsBase n) fBase tmpReg n (pcBase n)) i
  have h_pre_len_eq :
      pre.length = pcBase_i - 1 := by
    rw [h_pre_len]
    change _ = (1 + ((List.finRange k).filter
        (fun n => decide (n.val < i.val))).foldr
      (fun n acc => acc + blockLen n) 0) - 1
    have h_each : ∀ n : Fin k,
        (compileFrag_comp_subBlock frag_f frag_gs
          (gsBase n) fBase tmpReg n (pcBase n)).length
          = blockLen n :=
      fun n => compileFrag_comp_subBlock_length
        frag_f frag_gs (gsBase n) fBase tmpReg n (pcBase n)
    have h_foldr_eq :
        ((List.finRange k).filter
            (fun n => decide (n.val < i.val))).foldr
          (fun n acc => acc +
            (compileFrag_comp_subBlock frag_f frag_gs
              (gsBase n) fBase tmpReg n (pcBase n)).length) 0
          = ((List.finRange k).filter
              (fun n => decide (n.val < i.val))).foldr
            (fun n acc => acc + blockLen n) 0 := by
      induction (List.filter (fun n : Fin k =>
          decide (n.val < i.val)) (List.finRange k)) with
      | nil => rfl
      | cons hd tl ih_inner =>
        simp only [List.foldr_cons, ih_inner, h_each hd]
    rw [h_foldr_eq]
    omega
  -- Sub-block i = inputCopies_i ++ body_i ++ transfer_i.
  set sb_i : List URMInstrRaw :=
    compileFrag_comp_subBlock frag_f frag_gs
      (gsBase i) fBase tmpReg i (pcBase i) with h_sb_i
  let bodyBase_i : ℕ := pcBase i + 9 * a
  let body_i : List URMInstrRaw :=
    (frag_gs i).instrs.pop.toList.map fun ins =>
      URMInstrRaw.reindexShift (gsBase i) bodyBase_i
        (toRawOfBounded ins)
  let inputCopies_i : List URMInstrRaw :=
    (List.finRange a).flatMap fun j' =>
      URMRaw.preservingTransfer
        (pcBase i + 9 * j'.val)
        (2 + j'.val)
        (gsBase i + ((frag_gs i).inputRegs j').val)
        tmpReg
  let transfer_i : List URMInstrRaw :=
    URMRaw.transferLoop
      (bodyBase_i + ((frag_gs i).instrs.size - 1))
      (gsBase i + ((frag_gs i).outputReg).val)
      (fBase + (frag_f.inputRegs i).val)
  have h_sb_i_eq : sb_i = inputCopies_i ++ body_i ++ transfer_i := by
    rw [h_sb_i]; rfl
  have h_subBlocks_full :
      subBlocks = pre ++ inputCopies_i ++ body_i
        ++ transfer_i ++ suf := by
    change _ = ((pre ++ inputCopies_i) ++ body_i)
        ++ transfer_i ++ suf
    rw [show ((pre ++ inputCopies_i) ++ body_i) ++ transfer_i
        = pre ++ (inputCopies_i ++ body_i ++ transfer_i) by
      simp [List.append_assoc]]
    rw [← h_sb_i_eq]
    exact h_subBlocks_split
  -- Within inputCopies_i, split at j via flatMap_finRange_split.
  obtain ⟨pre_j, suf_j, h_inputCopies_split, h_pre_j_len⟩ :=
    flatMap_finRange_split a
      (fun j' : Fin a =>
        URMRaw.preservingTransfer
          (pcBase i + 9 * j'.val)
          (2 + j'.val)
          (gsBase i + ((frag_gs i).inputRegs j').val)
          tmpReg) j
  have h_each_pt_len : ∀ j' : Fin a,
      (URMRaw.preservingTransfer
        (pcBase i + 9 * j'.val) (2 + j'.val)
        (gsBase i + ((frag_gs i).inputRegs j').val)
        tmpReg).length = 9 := fun _ => rfl
  have h_pre_j_len_eq : pre_j.length = 9 * j.val := by
    rw [h_pre_j_len]
    have h_foldr_const :
        ((List.finRange a).filter
            (fun n => decide (n.val < j.val))).foldr
          (fun j' acc => acc +
            (URMRaw.preservingTransfer
              (pcBase i + 9 * j'.val) (2 + j'.val)
              (gsBase i + ((frag_gs i).inputRegs j').val)
              tmpReg).length) 0
          = ((List.finRange a).filter
              (fun n => decide (n.val < j.val))).foldr
            (fun _ acc => acc + 9) 0 := by
      induction (List.filter (fun n : Fin a =>
          decide (n.val < j.val)) (List.finRange a)) with
      | nil => rfl
      | cons hd tl ih_inner =>
        simp only [List.foldr_cons, ih_inner, h_each_pt_len hd]
    rw [h_foldr_const]
    -- Filter `(· .val < j.val)` over `List.finRange a` has
    -- length `j.val` (since j.val < a); foldr of constant +9
    -- yields 9 * j.val.  Prove both inline.
    have h_foldr_const_9 : ∀ (l : List (Fin a)),
        l.foldr (fun _ acc => acc + 9) 0 = 9 * l.length := by
      intro l
      induction l with
      | nil => rfl
      | cons _ tl ih_inner =>
        simp only [List.foldr_cons, List.length_cons, ih_inner]
        omega
    have h_filter_len :
        ((List.finRange a).filter
          (fun n => decide (n.val < j.val))).length = j.val := by
      -- Generalise: for any `m ≤ a'`, the filter on `finRange a'`
      -- of the predicate `(· .val < m)` has length `m`.  Induct
      -- on `a'` with `m` generalised; case-split on `m` after
      -- peeling the head of `finRange (a''+1)`.
      suffices h_aux : ∀ (a' m : ℕ) (_ : m ≤ a'),
          ((List.finRange a').filter
            (fun n => decide (n.val < m))).length = m by
        exact h_aux a j.val (Nat.le_of_lt j.isLt)
      intro a' m hm
      induction a' generalizing m with
      | zero =>
        have : m = 0 := Nat.le_zero.mp hm
        subst this
        rfl
      | succ a'' ih_aux =>
        rw [List.finRange_succ, List.filter_cons]
        -- Goal: (if decide ((0 : Fin (a''+1)).val < m) = true
        --   then 0 :: filter ... else filter ...).length = m.
        by_cases hm_pos : 0 < m
        · -- m > 0, write m = m''+1.
          obtain ⟨m'', rfl⟩ := Nat.exists_eq_succ_of_ne_zero
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
            by_cases h : y.val < m''
            · rw [decide_eq_true h, decide_eq_true (Nat.succ_lt_succ h)]
            · rw [decide_eq_false h,
                decide_eq_false (by intro hc; exact h (Nat.lt_of_succ_lt_succ hc))]
          rw [h_pred, List.length_map, ih_aux m'' hm']
        · -- m = 0.
          have hm_zero : m = 0 := Nat.le_zero.mp (Nat.not_lt.mp hm_pos)
          subst hm_zero
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
          -- (filter (fun _ => false) l).length = 0 for any l.
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
  -- Length facts for navigation.
  have h_inputCopies_i_len : inputCopies_i.length = 9 * a := by
    change ((List.finRange a).flatMap _).length = _
    rw [List.length_flatMap]
    rw [List.map_congr_left (fun j' _ => h_each_pt_len j')]
    rw [show (fun _ : Fin a => 9)
        = Function.const (Fin a) 9 from rfl,
      List.map_const, List.sum_replicate_nat,
      List.length_finRange]
    exact Nat.mul_comm a 9
  have h_body_i_len : body_i.length = (frag_gs i).instrs.size - 1 := by
    change ((frag_gs i).instrs.pop.toList.map _).length = _
    rw [List.length_map, Array.length_toList, Array.size_pop]
  have h_pcBase_eq_pcBase_i : pcBase i = pcBase_i := rfl
  -- Concrete preservingTransfer block at position j inside
  -- inputCopies_i.
  let pt_j : List URMInstrRaw :=
    URMRaw.preservingTransfer
      (pcBase i + 9 * j.val) (2 + j.val)
      (gsBase i + ((frag_gs i).inputRegs j).val) tmpReg
  have h_pt_j_len : pt_j.length = 9 := rfl
  have h_inputCopies_full :
      inputCopies_i = pre_j ++ pt_j ++ suf_j := by
    change (List.finRange a).flatMap _ = _
    exact h_inputCopies_split
  -- Outer instrs = toBoundedArray of rawList; bound witness.
  have hBoundOuter : URMInstrRaw.boundedBy nR rawList := by
    intro ins hmem
    have hmem' : ins = (.assignR 0 0 : URMInstrRaw)
        ∨ ins ∈ subBlocks ++ fBody := List.mem_cons.mp hmem
    rcases hmem' with hAssign | hmem
    · rw [hAssign]; simp only [URMInstrRaw.regBound]
      change 0 + 1 ≤ nR
      change 0 + 1 ≤ (fBase + frag_f.numRegs) + 1
      have h_fBase_pos : 0 < fBase := by
        change 0 < 2 + a + totalGsRegs; omega
      omega
    rcases List.mem_append.mp hmem with hSub | hF
    · rcases List.mem_flatMap.mp hSub with ⟨n, _, hn⟩
      have hGsBlock : gsBase n + (frag_gs n).numRegs ≤ fBase := by
        have hmono : gsPrefixSum frag_gs (n.val + 1)
            ≤ gsPrefixSum frag_gs k :=
          gsPrefixSum_mono frag_gs n.isLt
        have hsucc :
            gsPrefixSum frag_gs (n.val + 1)
              = gsPrefixSum frag_gs n.val + (frag_gs n).numRegs :=
          gsPrefixSum_succ_eq frag_gs n
        change 2 + a + gsPrefixSum frag_gs n.val
            + (frag_gs n).numRegs ≤ 2 + a + totalGsRegs
        change _ ≤ gsPrefixSum frag_gs k at hmono
        omega
      have hFBlock : fBase + frag_f.numRegs = tmpReg := rfl
      have hTmp : tmpReg < nR := by change tmpReg < tmpReg + 1; omega
      exact boundedBy_compileFrag_comp_subBlock frag_f frag_gs
        (gsBase n) fBase tmpReg nR n (pcBase n)
        hGsBlock hFBlock hTmp h_a_le_fBase ins hn
    · rcases List.mem_map.mp hF with ⟨ins', _, heq⟩
      rw [← heq]
      have hb : (toRawOfBounded ins').regBound ≤ frag_f.numRegs :=
        regBound_toRawOfBounded_le ins'
      have hr := regBound_reindexShift_le_offset_add fBase
        fPcBase frag_f.numRegs (toRawOfBounded ins') hb
      change _ ≤ (fBase + frag_f.numRegs) + 1
      omega
  have h_outer_instrs :
      outer.instrs = URMInstrRaw.toBoundedArray nR rawList
          hBoundOuter := rfl
  -- rawList length.
  have h_fBody_len : fBody.length = frag_f.instrs.size := by
    change (frag_f.instrs.toList.map _).length = _
    rw [List.length_map, Array.length_toList]
  have h_raw_len : rawList.length
      = 1 + subBlocks.length + fBody.length := by
    change (URMInstrRaw.assignR 0 0 :: (subBlocks ++ fBody)).length
      = 1 + subBlocks.length + fBody.length
    rw [List.length_cons, List.length_append]; omega
  have h_subBlocks_len_eq : subBlocks.length
      = pre.length + sb_i.length + suf.length := by
    change ((List.finRange k).flatMap fun n =>
        compileFrag_comp_subBlock frag_f frag_gs
          (gsBase n) fBase tmpReg n (pcBase n)).length
      = _
    rw [h_subBlocks_split]
    simp [List.length_append, Nat.add_assoc]
  have h_sb_i_len : sb_i.length
      = inputCopies_i.length + body_i.length + transfer_i.length := by
    rw [h_sb_i_eq]
    rw [List.length_append, List.length_append]
  -- Position-in-rawList helper: for d ∈ {0..8}, the rawList
  -- at PC pcBase_i + 9*j.val + d equals pt_j[d].
  have h_pcBase_i_pos : 1 ≤ pcBase_i := by
    change 1 ≤ 1 + _; omega
  have h_pos_lt_subBlocks : ∀ d : ℕ, d < 9 →
      pre.length + (pre_j.length + d) < subBlocks.length := by
    intro d hd
    rw [h_subBlocks_len_eq, h_sb_i_len, h_inputCopies_i_len,
      h_body_i_len, h_pre_j_len_eq]
    have h_jLt' : j.val < a := j.isLt
    omega
  -- The instruction lookup at position pre.length + pre_j.length
  -- + d inside rawList = pt_j[d].
  have h_lookup_pt :
      ∀ (d : ℕ) (hd : d < 9),
      let pos : ℕ := pre.length + (pre_j.length + d)
      have h_pos_in_sub : pos < subBlocks.length :=
        h_pos_lt_subBlocks d hd
      have h_idx_lt : 1 + pos < rawList.length := by
        rw [h_raw_len]; omega
      rawList[1 + pos]'h_idx_lt
        = pt_j[d]'(by rw [h_pt_j_len]; exact hd) := by
    intro d hd pos h_pos_in_sub h_idx_lt
    -- Peel the leading assignR 0 0.
    have h_idx_lt'' : pos < (subBlocks ++ fBody).length := by
      rw [List.length_append]; omega
    have h_idx_lt''' :
        pos + 1 < (URMInstrRaw.assignR 0 0 :: (subBlocks ++ fBody)
            : List URMInstrRaw).length := by
      rw [List.length_cons, List.length_append]; omega
    have h_arith : 1 + pos = pos + 1 := by omega
    have h_step1 :
        rawList[1 + pos]'h_idx_lt
          = (subBlocks ++ fBody)[pos]'h_idx_lt'' := by
      change ((URMInstrRaw.assignR 0 0 ::
          (subBlocks ++ fBody) : List URMInstrRaw))[1 + pos]'_
        = _
      have h_step1a :
          ((URMInstrRaw.assignR 0 0 ::
              (subBlocks ++ fBody) : List URMInstrRaw))[1 + pos]'h_idx_lt
            = ((URMInstrRaw.assignR 0 0 ::
              (subBlocks ++ fBody) : List URMInstrRaw))[pos + 1]'h_idx_lt''' := by
        congr 1
      rw [h_step1a]
      exact List.getElem_cons_succ (URMInstrRaw.assignR 0 0)
        (subBlocks ++ fBody) pos h_idx_lt'''
    rw [h_step1]
    -- Step into subBlocks via getElem_append_left.
    rw [List.getElem_append_left h_pos_in_sub]
    -- Substitute subBlocks via h_subBlocks_full.
    have h_pos_lt_full :
        pos < (pre ++ inputCopies_i ++ body_i ++ transfer_i ++ suf).length := by
      have := h_subBlocks_full
      rw [this] at h_pos_in_sub
      exact h_pos_in_sub
    have h_step2 :
        subBlocks[pos]'h_pos_in_sub
          = (pre ++ inputCopies_i ++ body_i ++ transfer_i ++ suf)[pos]'h_pos_lt_full := by
      congr 1
    rw [h_step2]
    -- Now navigate the append structure.
    have h_jLt' : j.val < a := j.isLt
    have h_pos_lt_4 :
        pos < (pre ++ inputCopies_i ++ body_i ++ transfer_i).length := by
      rw [List.length_append, List.length_append, List.length_append,
        h_body_i_len, h_inputCopies_i_len]
      change pre.length + (pre_j.length + d) < _
      rw [h_pre_j_len_eq]
      omega
    rw [List.getElem_append_left h_pos_lt_4]
    have h_pos_lt_3 :
        pos < (pre ++ inputCopies_i ++ body_i).length := by
      rw [List.length_append, List.length_append,
        h_body_i_len, h_inputCopies_i_len]
      change pre.length + (pre_j.length + d) < _
      rw [h_pre_j_len_eq]
      omega
    rw [List.getElem_append_left h_pos_lt_3]
    have h_pos_lt_2 :
        pos < (pre ++ inputCopies_i).length := by
      rw [List.length_append, h_inputCopies_i_len]
      change pre.length + (pre_j.length + d) < _
      rw [h_pre_j_len_eq]
      omega
    rw [List.getElem_append_left h_pos_lt_2]
    -- (pre ++ inputCopies_i)[pos] with pos ≥ pre.length.
    have h_pos_ge_pre : pre.length ≤ pos := by
      change pre.length ≤ pre.length + (pre_j.length + d); omega
    rw [List.getElem_append_right h_pos_ge_pre]
    -- inputCopies_i[pos - pre.length].
    have h_idx_eq : pos - pre.length = pre_j.length + d := by
      change pre.length + (pre_j.length + d) - pre.length = _
      omega
    have h_pos2_lt :
        pos - pre.length < inputCopies_i.length := by
      rw [h_idx_eq, h_inputCopies_i_len, h_pre_j_len_eq]
      have h_jLt' : j.val < a := j.isLt
      omega
    have h_step3 :
        inputCopies_i[pos - pre.length]'h_pos2_lt
          = inputCopies_i[pre_j.length + d]'(by
              rw [h_inputCopies_i_len, h_pre_j_len_eq]
              have h_jLt' : j.val < a := j.isLt
              omega) := by
      congr 1
    rw [h_step3]
    -- Substitute inputCopies_i via h_inputCopies_full.
    have h_pos2_lt_full :
        pre_j.length + d < (pre_j ++ pt_j ++ suf_j).length := by
      rw [List.length_append, List.length_append, h_pt_j_len]
      omega
    have h_pre_j_plus_d_lt_ic :
        pre_j.length + d < inputCopies_i.length := by
      rw [h_inputCopies_i_len, h_pre_j_len_eq]
      omega
    have h_step4 :
        inputCopies_i[pre_j.length + d]'h_pre_j_plus_d_lt_ic
          = (pre_j ++ pt_j ++ suf_j)[pre_j.length + d]'h_pos2_lt_full := by
      congr 1
    rw [h_step4]
    have h_pos3_lt :
        pre_j.length + d < (pre_j ++ pt_j).length := by
      rw [List.length_append, h_pt_j_len]
      omega
    rw [List.getElem_append_left h_pos3_lt]
    have h_pos3_ge : pre_j.length ≤ pre_j.length + d := by omega
    rw [List.getElem_append_right h_pos3_ge]
    -- pt_j[pre_j.length + d - pre_j.length] = pt_j[d].
    have h_d_eq : pre_j.length + d - pre_j.length = d := by omega
    have h_d_lt : pre_j.length + d - pre_j.length < pt_j.length := by
      rw [h_d_eq, h_pt_j_len]; exact hd
    have h_step5 :
        pt_j[pre_j.length + d - pre_j.length]'h_d_lt
          = pt_j[d]'(by rw [h_pt_j_len]; exact hd) := by
      congr 1
    exact h_step5
  -- General getElem? equality at pcBase_i + 9*j.val + d.
  have h_pcBase_j_eq : pcBase_i + 9 * j.val
      = 1 + (pre.length + pre_j.length) := by
    rw [h_pre_len_eq, h_pre_j_len_eq]
    have : 1 ≤ pcBase_i := h_pcBase_i_pos
    omega
  -- Membership proof for `pt_j[d] ∈ rawList`, used to feed
  -- `hBoundOuter` inside `toBoundedArray_getElem?`.
  have h_pt_d_in_rawList : ∀ (d : ℕ) (hd : d < 9),
      (pt_j[d]'(by rw [h_pt_j_len]; exact hd)) ∈ rawList := by
    intro d hd
    have h_mem_pt :
        pt_j[d]'(by rw [h_pt_j_len]; exact hd) ∈ pt_j :=
      List.getElem_mem _
    have h_mem_ic :
        pt_j[d]'(by rw [h_pt_j_len]; exact hd) ∈ inputCopies_i := by
      rw [h_inputCopies_full]
      exact List.mem_append.mpr
        (Or.inl (List.mem_append.mpr (Or.inr h_mem_pt)))
    have h_mem_sb_i :
        pt_j[d]'(by rw [h_pt_j_len]; exact hd) ∈ sb_i := by
      rw [h_sb_i_eq]
      exact List.mem_append.mpr
        (Or.inl (List.mem_append.mpr (Or.inl h_mem_ic)))
    have h_mem_subBlocks :
        pt_j[d]'(by rw [h_pt_j_len]; exact hd) ∈ subBlocks := by
      change pt_j[d]'_ ∈ (List.finRange k).flatMap _
      exact List.mem_flatMap.mpr
        ⟨i, List.mem_finRange _, h_mem_sb_i⟩
    exact List.mem_cons.mpr
      (Or.inr (List.mem_append.mpr (Or.inl h_mem_subBlocks)))
  have h_outerInstr_lookup :
      ∀ (d : ℕ) (hd : d < 9),
        outer.instrs[pcBase_i + 9 * j.val + d]?
          = some (URMInstrRaw.toBounded nR
              (pt_j[d]'(by rw [h_pt_j_len]; exact hd))
              (hBoundOuter _ (h_pt_d_in_rawList d hd))) := by
    intro d hd
    have h_pos_lt : pre.length + (pre_j.length + d) < subBlocks.length :=
      h_pos_lt_subBlocks d hd
    have h_idx_lt : 1 + (pre.length + (pre_j.length + d)) < rawList.length := by
      rw [h_raw_len]; omega
    -- pcBase_i + 9*j.val + d = 1 + (pre.length + (pre_j.length + d)).
    have h_pcs_eq : pcBase_i + 9 * j.val + d
        = 1 + (pre.length + (pre_j.length + d)) := by
      rw [h_pcBase_j_eq]; omega
    have h_idx_lt_outer :
        pcBase_i + 9 * j.val + d < rawList.length := by
      rw [h_pcs_eq]; exact h_idx_lt
    -- Reduce via toBoundedArray_getElem?.
    change (URMInstrRaw.toBoundedArray nR rawList hBoundOuter)[
        pcBase_i + 9 * j.val + d]? = _
    rw [URMInstrRaw.toBoundedArray_getElem? nR rawList hBoundOuter
        (pcBase_i + 9 * j.val + d) h_idx_lt_outer]
    -- Show the raw equality.
    have h_raw_eq :
        rawList[pcBase_i + 9 * j.val + d]'h_idx_lt_outer
          = pt_j[d]'(by rw [h_pt_j_len]; exact hd) := by
      have h_step :
          rawList[pcBase_i + 9 * j.val + d]'h_idx_lt_outer
            = rawList[1 + (pre.length + (pre_j.length + d))]'h_idx_lt := by
        congr 1
      rw [h_step]
      exact h_lookup_pt d hd
    apply congrArg some
    exact URMInstrRaw.toBounded_congr nR h_raw_eq _ _
  -- Now build the preservingTransferInstrs witness using the
  -- nine concrete entries of pt_j.  Each h_inst_d follows by
  -- specialising h_outerInstr_lookup at d and matching the
  -- raw entry to the toBounded form expected by the structure.
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

/-- Inner loop 1 of `URMRaw.preservingTransfer`: while
`V_src > 0`, body decrements `V_src` and increments
`V_dst`, `V_tmp`. After `5 * m + 1` steps starting from
`pc = pcBase` and `V_src = m`, the state has
`pc = pcBase + 5`, `V_src = 0`, `V_dst += m`, `V_tmp += m`,
and all other registers unchanged. -/
private theorem preservingTransfer_loop1 {a : ℕ}
    (P : URMProgram a) (pcBase : ℕ)
    (src dst tmp zReg : Fin P.numRegs)
    (h_disj_sd : src ≠ dst) (h_disj_st : src ≠ tmp)
    (h_disj_dt : dst ≠ tmp) (h_disj_zs : zReg ≠ src)
    (h_disj_zd : zReg ≠ dst) (h_disj_zt : zReg ≠ tmp)
    (H : preservingTransferInstrs P pcBase src dst tmp zReg)
    (s : URMState P) (h_pc : s.pc = pcBase)
    (h_z : s.regs zReg = 0)
    (m : ℕ) (h_src : s.regs src = m) :
    let s' := URMState.runFor P s (5 * m + 1)
    s'.pc = pcBase + 5 ∧
    s'.regs src = 0 ∧
    s'.regs dst = s.regs dst + m ∧
    s'.regs tmp = s.regs tmp + m ∧
    s'.regs zReg = 0 ∧
    ∀ r, r ≠ src → r ≠ dst → r ≠ tmp → s'.regs r = s.regs r := by
  -- Move the let-binder into the conclusion explicitly.
  simp only []
  induction m generalizing s with
  | zero =>
    -- 1 step: jumpZR src (pcBase+5) (pcBase+1).  V_src = 0,
    -- so PC → pcBase+5.
    have hstep : (5 * 0 + 1 : ℕ) = 0 + 1 := rfl
    rw [hstep, URMState.runFor_succ, URMState.runFor_zero]
    rw [URMState.step_of_getElem?_jumpZ P s pcBase src
      (pcBase + 5) (pcBase + 1) h_pc H.h0]
    have hsrc_eq : s.regs src = 0 := h_src
    simp only [hsrc_eq, ↓reduceIte]
    refine ⟨trivial, trivial, ?_, ?_, h_z, fun _ _ _ _ => trivial⟩
    · show s.regs dst = s.regs dst + 0
      omega
    · show s.regs tmp = s.regs tmp + 0
      omega
  | succ m ih =>
    -- Peel 5 steps: jumpZ (to pcBase+1), dec src, inc dst,
    -- inc tmp, goto pcBase.  Then apply ih on the resulting
    -- state with V_src = m.
    have h5n : 5 * (m + 1) + 1 = 5 + (5 * m + 1) := by omega
    rw [h5n, URMState.runFor_add]
    -- Compute the state after the first 5 steps via a local lemma.
    -- The 5 steps execute: jumpZ src (taken to pcBase+1), dec src,
    -- inc dst, inc tmp, goto pcBase.
    set s5 : URMState P :=
      { pc := pcBase
        regs := Function.update
          (Function.update
            (Function.update s.regs src (s.regs src - 1))
            dst ((Function.update s.regs src (s.regs src - 1)) dst + 1))
          tmp ((Function.update
            (Function.update s.regs src (s.regs src - 1))
            dst ((Function.update s.regs src (s.regs src - 1)) dst + 1))
            tmp + 1) } with hs5_def
    have h_src_ne : s.regs src ≠ 0 := by rw [h_src]; omega
    have h_five : URMState.runFor P s 5 = s5 := by
      -- Peel 5 steps.
      change URMState.runFor P s (4 + 1) = _
      rw [URMState.runFor_succ]
      rw [URMState.step_of_getElem?_jumpZ P s pcBase src
        (pcBase + 5) (pcBase + 1) h_pc H.h0]
      simp only [h_src_ne, ↓reduceIte]
      set s1 : URMState P :=
        { pc := pcBase + 1, regs := s.regs } with hs1_def
      have hs1_pc : s1.pc = pcBase + 1 := rfl
      change URMState.runFor P s1 (3 + 1) = _
      rw [URMState.runFor_succ,
        URMState.step_of_getElem?_dec P s1 (pcBase + 1) src hs1_pc H.h1]
      set s2 : URMState P :=
        { pc := s1.pc + 1
          regs := Function.update s1.regs src (s1.regs src - 1) } with hs2_def
      have hs2_pc : s2.pc = pcBase + 2 := by
        change s1.pc + 1 = pcBase + 2; rw [hs1_pc]
      change URMState.runFor P s2 (2 + 1) = _
      rw [URMState.runFor_succ,
        URMState.step_of_getElem?_inc P s2 (pcBase + 2) dst hs2_pc H.h2]
      set s3 : URMState P :=
        { pc := s2.pc + 1
          regs := Function.update s2.regs dst (s2.regs dst + 1) } with hs3_def
      have hs3_pc : s3.pc = pcBase + 3 := by
        change s2.pc + 1 = pcBase + 3; rw [hs2_pc]
      change URMState.runFor P s3 (1 + 1) = _
      rw [URMState.runFor_succ,
        URMState.step_of_getElem?_inc P s3 (pcBase + 3) tmp hs3_pc H.h3]
      set s4 : URMState P :=
        { pc := s3.pc + 1
          regs := Function.update s3.regs tmp (s3.regs tmp + 1) } with hs4_def
      have hs4_pc : s4.pc = pcBase + 4 := by
        change s3.pc + 1 = pcBase + 4; rw [hs3_pc]
      change URMState.runFor P s4 (0 + 1) = _
      rw [URMState.runFor_succ, URMState.runFor_zero,
        URMState.step_of_getElem?_jumpZ P s4 (pcBase + 4) zReg
          pcBase pcBase hs4_pc H.h4]
      -- Compute s4.regs zReg = 0.
      have hs4_z : s4.regs zReg = 0 := by
        change Function.update s3.regs tmp _ zReg = 0
        rw [Function.update_of_ne h_disj_zt]
        change Function.update s2.regs dst _ zReg = 0
        rw [Function.update_of_ne h_disj_zd]
        change Function.update s1.regs src _ zReg = 0
        rw [Function.update_of_ne h_disj_zs]
        exact h_z
      simp only [hs4_z, ↓reduceIte]
      -- Goal now: { pc := pcBase, regs := s4.regs } = s5
      rfl
    rw [h_five]
    -- Compute s5's register values via Function.update reasoning.
    have hs5_pc : s5.pc = pcBase := rfl
    -- Compute s5.regs values via Function.update reasoning.
    -- For Function.update_of_ne (h : a ≠ a') : update f a' v a = f a.
    -- We rewrite `Function.update _ X _ Y` where Y ≠ X.
    -- Generic helper: register r ≠ src gives `f0 r = s.regs r`.
    set f0 : Fin P.numRegs → ℕ :=
      Function.update s.regs src (s.regs src - 1) with hf0
    set f1 : Fin P.numRegs → ℕ :=
      Function.update f0 dst (f0 dst + 1) with hf1
    -- f0 reasoning.
    have hf0_dst : f0 dst = s.regs dst :=
      Function.update_of_ne h_disj_sd.symm _ s.regs
    have hf0_tmp : f0 tmp = s.regs tmp :=
      Function.update_of_ne h_disj_st.symm _ s.regs
    have hf0_z : f0 zReg = s.regs zReg :=
      Function.update_of_ne h_disj_zs _ s.regs
    have hf0_other : ∀ r, r ≠ src → f0 r = s.regs r := fun r hrs =>
      Function.update_of_ne hrs _ s.regs
    -- f1 reasoning.
    have hf1_dst : f1 dst = s.regs dst + 1 := by
      change Function.update f0 dst (f0 dst + 1) dst = _
      rw [Function.update_self, hf0_dst]
    have hf1_tmp : f1 tmp = s.regs tmp := by
      change Function.update f0 dst (f0 dst + 1) tmp = _
      rw [Function.update_of_ne h_disj_dt.symm, hf0_tmp]
    have hf1_z : f1 zReg = s.regs zReg := by
      change Function.update f0 dst (f0 dst + 1) zReg = _
      rw [Function.update_of_ne h_disj_zd, hf0_z]
    have hf1_src : f1 src = s.regs src - 1 := by
      change Function.update f0 dst (f0 dst + 1) src = _
      rw [Function.update_of_ne h_disj_sd, hf0]
      change Function.update s.regs src (s.regs src - 1) src = _
      rw [Function.update_self]
    have hf1_other : ∀ r, r ≠ src → r ≠ dst → f1 r = s.regs r := by
      intro r hrs hrd
      change Function.update f0 dst (f0 dst + 1) r = _
      rw [Function.update_of_ne hrd]
      exact hf0_other r hrs
    -- s5 reasoning. s5.regs = update f1 tmp (f1 tmp + 1).
    have hs5_z : s5.regs zReg = 0 := by
      change Function.update f1 tmp (f1 tmp + 1) zReg = 0
      rw [Function.update_of_ne h_disj_zt, hf1_z, h_z]
    have hs5_src : s5.regs src = m := by
      change Function.update f1 tmp (f1 tmp + 1) src = m
      rw [Function.update_of_ne h_disj_st, hf1_src]
      omega
    have hs5_dst : s5.regs dst = s.regs dst + 1 := by
      change Function.update f1 tmp (f1 tmp + 1) dst = _
      rw [Function.update_of_ne h_disj_dt]
      exact hf1_dst
    have hs5_tmp : s5.regs tmp = s.regs tmp + 1 := by
      change Function.update f1 tmp (f1 tmp + 1) tmp = _
      rw [Function.update_self, hf1_tmp]
    have hs5_other : ∀ r, r ≠ src → r ≠ dst → r ≠ tmp →
        s5.regs r = s.regs r := by
      intro r hrs hrd hrt
      change Function.update f1 tmp (f1 tmp + 1) r = _
      rw [Function.update_of_ne hrt]
      exact hf1_other r hrs hrd
    obtain ⟨ih_pc, ih_src, ih_dst, ih_tmp, ih_z, ih_oth⟩ :=
      ih s5 hs5_pc hs5_z hs5_src
    refine ⟨ih_pc, ih_src, ?_, ?_, ih_z, ?_⟩
    · rw [ih_dst, hs5_dst]; omega
    · rw [ih_tmp, hs5_tmp]; omega
    · intro r hrs hrd hrt
      rw [ih_oth r hrs hrd hrt, hs5_other r hrs hrd hrt]

/-- Per-step PC bound for `preservingTransfer_loop1`: during
the `5 * m + 1` steps of loop 1, the intermediate PC stays
within `[pcBase, pcBase + 5]`. -/
private theorem preservingTransfer_loop1_pc_bound {a : ℕ}
    (P : URMProgram a) (pcBase : ℕ)
    (src dst tmp zReg : Fin P.numRegs)
    (h_disj_sd : src ≠ dst) (h_disj_st : src ≠ tmp)
    (h_disj_zs : zReg ≠ src)
    (h_disj_zd : zReg ≠ dst) (h_disj_zt : zReg ≠ tmp)
    (H : preservingTransferInstrs P pcBase src dst tmp zReg)
    (s : URMState P) (h_pc : s.pc = pcBase)
    (h_z : s.regs zReg = 0)
    (m : ℕ) (h_src : s.regs src = m)
    (k : ℕ) (h_k : k ≤ 5 * m + 1) :
    (URMState.runFor P s k).pc ≤ pcBase + 5 := by
  induction m generalizing s k with
  | zero =>
    match k, h_k with
    | 0, _ => rw [URMState.runFor_zero, h_pc]; omega
    | 1, _ =>
      rw [show (1 : ℕ) = 0 + 1 from rfl, URMState.runFor_succ,
        URMState.runFor_zero,
        URMState.step_of_getElem?_jumpZ P s pcBase src
          (pcBase + 5) (pcBase + 1) h_pc H.h0]
      have hsrc_eq : s.regs src = 0 := h_src
      simp only [hsrc_eq, ↓reduceIte]
      omega
  | succ m ih =>
    have h_src_ne : s.regs src ≠ 0 := by rw [h_src]; omega
    set s1 : URMState P :=
      { pc := pcBase + 1, regs := s.regs } with hs1_def
    have hs1_pc : s1.pc = pcBase + 1 := rfl
    set s2 : URMState P :=
      { pc := pcBase + 2
        regs := Function.update s1.regs src (s1.regs src - 1) }
      with hs2_def
    have hs2_pc : s2.pc = pcBase + 2 := rfl
    set s3 : URMState P :=
      { pc := pcBase + 3
        regs := Function.update s2.regs dst (s2.regs dst + 1) }
      with hs3_def
    have hs3_pc : s3.pc = pcBase + 3 := rfl
    set s4 : URMState P :=
      { pc := pcBase + 4
        regs := Function.update s3.regs tmp (s3.regs tmp + 1) }
      with hs4_def
    have hs4_pc : s4.pc = pcBase + 4 := rfl
    set s5 : URMState P :=
      { pc := pcBase
        regs := Function.update
          (Function.update
            (Function.update s.regs src (s.regs src - 1))
            dst ((Function.update s.regs src (s.regs src - 1)) dst + 1))
          tmp ((Function.update
            (Function.update s.regs src (s.regs src - 1))
            dst ((Function.update s.regs src (s.regs src - 1)) dst + 1))
            tmp + 1) } with hs5_def
    have h_one : URMState.runFor P s 1 = s1 := by
      rw [show (1 : ℕ) = 0 + 1 from rfl, URMState.runFor_succ,
        URMState.runFor_zero,
        URMState.step_of_getElem?_jumpZ P s pcBase src
          (pcBase + 5) (pcBase + 1) h_pc H.h0]
      simp only [h_src_ne, ↓reduceIte]
      rfl
    have h_two : URMState.runFor P s 2 = s2 := by
      rw [show (2 : ℕ) = 1 + 1 from rfl, URMState.runFor_add, h_one]
      rw [show (1 : ℕ) = 0 + 1 from rfl, URMState.runFor_succ,
        URMState.runFor_zero,
        URMState.step_of_getElem?_dec P s1 (pcBase + 1) src hs1_pc H.h1]
    have h_three : URMState.runFor P s 3 = s3 := by
      rw [show (3 : ℕ) = 2 + 1 from rfl, URMState.runFor_add, h_two]
      rw [show (1 : ℕ) = 0 + 1 from rfl, URMState.runFor_succ,
        URMState.runFor_zero,
        URMState.step_of_getElem?_inc P s2 (pcBase + 2) dst hs2_pc H.h2]
    have h_four : URMState.runFor P s 4 = s4 := by
      rw [show (4 : ℕ) = 3 + 1 from rfl, URMState.runFor_add, h_three]
      rw [show (1 : ℕ) = 0 + 1 from rfl, URMState.runFor_succ,
        URMState.runFor_zero,
        URMState.step_of_getElem?_inc P s3 (pcBase + 3) tmp hs3_pc H.h3]
    have h_five : URMState.runFor P s 5 = s5 := by
      rw [show (5 : ℕ) = 4 + 1 from rfl, URMState.runFor_add, h_four]
      rw [show (1 : ℕ) = 0 + 1 from rfl, URMState.runFor_succ,
        URMState.runFor_zero,
        URMState.step_of_getElem?_jumpZ P s4 (pcBase + 4) zReg
          pcBase pcBase hs4_pc H.h4]
      have hs4_z : s4.regs zReg = 0 := by
        change Function.update s3.regs tmp _ zReg = 0
        rw [Function.update_of_ne h_disj_zt]
        change Function.update s2.regs dst _ zReg = 0
        rw [Function.update_of_ne h_disj_zd]
        change Function.update s1.regs src _ zReg = 0
        rw [Function.update_of_ne h_disj_zs]
        exact h_z
      simp only [hs4_z, ↓reduceIte]
      rfl
    by_cases hk : k ≤ 5
    · match k, hk with
      | 0, _ => rw [URMState.runFor_zero, h_pc]; omega
      | 1, _ => rw [h_one]; change pcBase + 1 ≤ pcBase + 5; omega
      | 2, _ => rw [h_two]; change pcBase + 2 ≤ pcBase + 5; omega
      | 3, _ => rw [h_three]; change pcBase + 3 ≤ pcBase + 5; omega
      | 4, _ => rw [h_four]; change pcBase + 4 ≤ pcBase + 5; omega
      | 5, _ => rw [h_five]; change pcBase ≤ pcBase + 5; omega
    · push_neg at hk
      obtain ⟨k', rfl⟩ : ∃ k', k = 5 + k' := ⟨k - 5, by omega⟩
      have h_k' : k' ≤ 5 * m + 1 := by omega
      rw [URMState.runFor_add, h_five]
      have hs5_pc : s5.pc = pcBase := rfl
      have hs5_z : s5.regs zReg = 0 := by
        change Function.update
          (Function.update
            (Function.update s.regs src (s.regs src - 1))
            dst _) tmp _ zReg = 0
        rw [Function.update_of_ne h_disj_zt]
        rw [Function.update_of_ne h_disj_zd]
        rw [Function.update_of_ne h_disj_zs]
        exact h_z
      have hs5_src : s5.regs src = m := by
        change Function.update
          (Function.update
            (Function.update s.regs src (s.regs src - 1))
            dst _) tmp _ src = m
        rw [Function.update_of_ne h_disj_st]
        rw [Function.update_of_ne h_disj_sd]
        rw [Function.update_self]
        omega
      exact ih s5 hs5_pc hs5_z hs5_src k' h_k'

/-- Inner loop 2 of `URMRaw.preservingTransfer`: while
`V_tmp > 0`, body decrements `V_tmp` and increments
`V_src`. After `4 * m + 1` steps starting from
`pc = pcBase + 5` and `V_tmp = m`, the state has
`pc = pcBase + 9`, `V_tmp = 0`, `V_src += m`, and all
other registers unchanged. -/
private theorem preservingTransfer_loop2 {a : ℕ}
    (P : URMProgram a) (pcBase : ℕ)
    (src dst tmp zReg : Fin P.numRegs)
    (h_disj_st : src ≠ tmp)
    (h_disj_zs : zReg ≠ src) (h_disj_zt : zReg ≠ tmp)
    (H : preservingTransferInstrs P pcBase src dst tmp zReg)
    (s : URMState P) (h_pc : s.pc = pcBase + 5)
    (h_z : s.regs zReg = 0)
    (m : ℕ) (h_tmp : s.regs tmp = m) :
    let s' := URMState.runFor P s (4 * m + 1)
    s'.pc = pcBase + 9 ∧
    s'.regs tmp = 0 ∧
    s'.regs src = s.regs src + m ∧
    s'.regs zReg = 0 ∧
    ∀ r, r ≠ src → r ≠ tmp → s'.regs r = s.regs r := by
  simp only []
  induction m generalizing s with
  | zero =>
    have hstep : (4 * 0 + 1 : ℕ) = 0 + 1 := rfl
    rw [hstep, URMState.runFor_succ, URMState.runFor_zero,
      URMState.step_of_getElem?_jumpZ P s (pcBase + 5) tmp
        (pcBase + 9) (pcBase + 6) h_pc H.h5]
    have htmp_eq : s.regs tmp = 0 := h_tmp
    simp only [htmp_eq, ↓reduceIte]
    -- Goal: True (pc) ∧ True (tmp) ∧ src = src + 0 ∧ True (zReg) ∧ ∀, True.
    refine ⟨trivial, trivial, ?_, h_z, fun _ _ _ => trivial⟩
    show s.regs src = s.regs src + 0
    omega
  | succ m ih =>
    have h4n : 4 * (m + 1) + 1 = 4 + (4 * m + 1) := by omega
    rw [h4n, URMState.runFor_add]
    set s4 : URMState P :=
      { pc := pcBase + 5
        regs := Function.update
          (Function.update s.regs tmp (s.regs tmp - 1))
          src ((Function.update s.regs tmp (s.regs tmp - 1)) src + 1) }
      with hs4_def
    have h_tmp_ne : s.regs tmp ≠ 0 := by rw [h_tmp]; omega
    have h_four : URMState.runFor P s 4 = s4 := by
      change URMState.runFor P s (3 + 1) = _
      rw [URMState.runFor_succ,
        URMState.step_of_getElem?_jumpZ P s (pcBase + 5) tmp
          (pcBase + 9) (pcBase + 6) h_pc H.h5]
      simp only [h_tmp_ne, ↓reduceIte]
      set s1 : URMState P :=
        { pc := pcBase + 6, regs := s.regs } with hs1_def
      have hs1_pc : s1.pc = pcBase + 6 := rfl
      change URMState.runFor P s1 (2 + 1) = _
      rw [URMState.runFor_succ,
        URMState.step_of_getElem?_dec P s1 (pcBase + 6) tmp hs1_pc H.h6]
      set s2 : URMState P :=
        { pc := s1.pc + 1
          regs := Function.update s1.regs tmp (s1.regs tmp - 1) } with hs2_def
      have hs2_pc : s2.pc = pcBase + 7 := by
        change s1.pc + 1 = pcBase + 7; rw [hs1_pc]
      change URMState.runFor P s2 (1 + 1) = _
      rw [URMState.runFor_succ,
        URMState.step_of_getElem?_inc P s2 (pcBase + 7) src hs2_pc H.h7]
      set s3 : URMState P :=
        { pc := s2.pc + 1
          regs := Function.update s2.regs src (s2.regs src + 1) } with hs3_def
      have hs3_pc : s3.pc = pcBase + 8 := by
        change s2.pc + 1 = pcBase + 8; rw [hs2_pc]
      change URMState.runFor P s3 (0 + 1) = _
      rw [URMState.runFor_succ, URMState.runFor_zero,
        URMState.step_of_getElem?_jumpZ P s3 (pcBase + 8) zReg
          (pcBase + 5) (pcBase + 5) hs3_pc H.h8]
      have hs3_z : s3.regs zReg = 0 := by
        change Function.update s2.regs src _ zReg = 0
        rw [Function.update_of_ne h_disj_zs]
        change Function.update s1.regs tmp _ zReg = 0
        rw [Function.update_of_ne h_disj_zt]
        exact h_z
      simp only [hs3_z, ↓reduceIte]
      rfl
    rw [h_four]
    have hs4_pc : s4.pc = pcBase + 5 := rfl
    have hs4_z : s4.regs zReg = 0 := by
      change Function.update (Function.update s.regs tmp
        (s.regs tmp - 1)) src _ zReg = 0
      rw [Function.update_of_ne h_disj_zs]
      rw [Function.update_of_ne h_disj_zt]
      exact h_z
    have hs4_tmp : s4.regs tmp = m := by
      change Function.update (Function.update s.regs tmp
        (s.regs tmp - 1)) src _ tmp = m
      rw [Function.update_of_ne h_disj_st.symm]
      rw [Function.update_self]
      omega
    have hs4_src : s4.regs src = s.regs src + 1 := by
      change Function.update (Function.update s.regs tmp
        (s.regs tmp - 1)) src _ src = _
      rw [Function.update_self]
      rw [Function.update_of_ne h_disj_st]
    have hs4_other : ∀ r, r ≠ src → r ≠ tmp →
        s4.regs r = s.regs r := by
      intro r hrs hrt
      change Function.update (Function.update s.regs tmp
        (s.regs tmp - 1)) src _ r = _
      rw [Function.update_of_ne hrs]
      rw [Function.update_of_ne hrt]
    obtain ⟨ih_pc, ih_tmp', ih_src, ih_z, ih_oth⟩ :=
      ih s4 hs4_pc hs4_z hs4_tmp
    refine ⟨ih_pc, ih_tmp', ?_, ih_z, ?_⟩
    · rw [ih_src, hs4_src]; omega
    · intro r hrs hrt
      rw [ih_oth r hrs hrt, hs4_other r hrs hrt]

/-- Per-step PC bound for `preservingTransfer_loop2`: during
the `4 * m + 1` steps of loop 2, the intermediate PC stays
within `[pcBase + 5, pcBase + 9]`. -/
private theorem preservingTransfer_loop2_pc_bound {a : ℕ}
    (P : URMProgram a) (pcBase : ℕ)
    (src dst tmp zReg : Fin P.numRegs)
    (h_disj_st : src ≠ tmp)
    (h_disj_zs : zReg ≠ src) (h_disj_zt : zReg ≠ tmp)
    (H : preservingTransferInstrs P pcBase src dst tmp zReg)
    (s : URMState P) (h_pc : s.pc = pcBase + 5)
    (h_z : s.regs zReg = 0)
    (m : ℕ) (h_tmp : s.regs tmp = m)
    (k : ℕ) (h_k : k ≤ 4 * m + 1) :
    pcBase + 5 ≤ (URMState.runFor P s k).pc ∧
    (URMState.runFor P s k).pc ≤ pcBase + 9 := by
  induction m generalizing s k with
  | zero =>
    match k, h_k with
    | 0, _ => rw [URMState.runFor_zero, h_pc]; exact ⟨by omega, by omega⟩
    | 1, _ =>
      rw [show (1 : ℕ) = 0 + 1 from rfl, URMState.runFor_succ,
        URMState.runFor_zero,
        URMState.step_of_getElem?_jumpZ P s (pcBase + 5) tmp
          (pcBase + 9) (pcBase + 6) h_pc H.h5]
      have htmp_eq : s.regs tmp = 0 := h_tmp
      simp only [htmp_eq, ↓reduceIte]
      exact ⟨by omega, by omega⟩
  | succ m ih =>
    have h_tmp_ne : s.regs tmp ≠ 0 := by rw [h_tmp]; omega
    set s1 : URMState P :=
      { pc := pcBase + 6, regs := s.regs } with hs1_def
    have hs1_pc : s1.pc = pcBase + 6 := rfl
    set s2 : URMState P :=
      { pc := pcBase + 7
        regs := Function.update s1.regs tmp (s1.regs tmp - 1) }
      with hs2_def
    have hs2_pc : s2.pc = pcBase + 7 := rfl
    set s3 : URMState P :=
      { pc := pcBase + 8
        regs := Function.update s2.regs src (s2.regs src + 1) }
      with hs3_def
    have hs3_pc : s3.pc = pcBase + 8 := rfl
    set s4 : URMState P :=
      { pc := pcBase + 5
        regs := Function.update
          (Function.update s.regs tmp (s.regs tmp - 1))
          src ((Function.update s.regs tmp (s.regs tmp - 1)) src + 1) }
      with hs4_def
    have h_one : URMState.runFor P s 1 = s1 := by
      rw [show (1 : ℕ) = 0 + 1 from rfl, URMState.runFor_succ,
        URMState.runFor_zero,
        URMState.step_of_getElem?_jumpZ P s (pcBase + 5) tmp
          (pcBase + 9) (pcBase + 6) h_pc H.h5]
      simp only [h_tmp_ne, ↓reduceIte]
      rfl
    have h_two : URMState.runFor P s 2 = s2 := by
      rw [show (2 : ℕ) = 1 + 1 from rfl, URMState.runFor_add, h_one]
      rw [show (1 : ℕ) = 0 + 1 from rfl, URMState.runFor_succ,
        URMState.runFor_zero,
        URMState.step_of_getElem?_dec P s1 (pcBase + 6) tmp hs1_pc H.h6]
    have h_three : URMState.runFor P s 3 = s3 := by
      rw [show (3 : ℕ) = 2 + 1 from rfl, URMState.runFor_add, h_two]
      rw [show (1 : ℕ) = 0 + 1 from rfl, URMState.runFor_succ,
        URMState.runFor_zero,
        URMState.step_of_getElem?_inc P s2 (pcBase + 7) src hs2_pc H.h7]
    have h_four : URMState.runFor P s 4 = s4 := by
      rw [show (4 : ℕ) = 3 + 1 from rfl, URMState.runFor_add, h_three]
      rw [show (1 : ℕ) = 0 + 1 from rfl, URMState.runFor_succ,
        URMState.runFor_zero,
        URMState.step_of_getElem?_jumpZ P s3 (pcBase + 8) zReg
          (pcBase + 5) (pcBase + 5) hs3_pc H.h8]
      have hs3_z : s3.regs zReg = 0 := by
        change Function.update s2.regs src _ zReg = 0
        rw [Function.update_of_ne h_disj_zs]
        change Function.update s1.regs tmp _ zReg = 0
        rw [Function.update_of_ne h_disj_zt]
        exact h_z
      simp only [hs3_z, ↓reduceIte]
      rfl
    by_cases hk : k ≤ 4
    · match k, hk with
      | 0, _ =>
        rw [URMState.runFor_zero, h_pc]; exact ⟨by omega, by omega⟩
      | 1, _ =>
        rw [h_one]; change pcBase + 5 ≤ pcBase + 6 ∧ pcBase + 6 ≤ pcBase + 9
        exact ⟨by omega, by omega⟩
      | 2, _ =>
        rw [h_two]; change pcBase + 5 ≤ pcBase + 7 ∧ pcBase + 7 ≤ pcBase + 9
        exact ⟨by omega, by omega⟩
      | 3, _ =>
        rw [h_three]; change pcBase + 5 ≤ pcBase + 8 ∧ pcBase + 8 ≤ pcBase + 9
        exact ⟨by omega, by omega⟩
      | 4, _ =>
        rw [h_four]; change pcBase + 5 ≤ pcBase + 5 ∧ pcBase + 5 ≤ pcBase + 9
        exact ⟨by omega, by omega⟩
    · push_neg at hk
      obtain ⟨k', rfl⟩ : ∃ k', k = 4 + k' := ⟨k - 4, by omega⟩
      have h_k' : k' ≤ 4 * m + 1 := by omega
      rw [URMState.runFor_add, h_four]
      have hs4_pc : s4.pc = pcBase + 5 := rfl
      have hs4_z : s4.regs zReg = 0 := by
        change Function.update (Function.update s.regs tmp
          (s.regs tmp - 1)) src _ zReg = 0
        rw [Function.update_of_ne h_disj_zs]
        rw [Function.update_of_ne h_disj_zt]
        exact h_z
      have hs4_tmp : s4.regs tmp = m := by
        change Function.update (Function.update s.regs tmp
          (s.regs tmp - 1)) src _ tmp = m
        rw [Function.update_of_ne h_disj_st.symm]
        rw [Function.update_self]
        omega
      exact ih s4 hs4_pc hs4_z hs4_tmp k' h_k'

/-- Correctness of the `URMRaw.preservingTransfer` 9-instruction
block. Running for `9 * n + 2` steps from a state with
`pc = pcBase`, `V_src = n`, `V_tmp = 0`, and the reserved-zero
register `V_zReg = 0` yields a state with `pc = pcBase + 9`,
`V_dst += n`, `V_src = n` (preserved), `V_tmp = 0` (restored
after loop 2 consumes the loop-1 deposit), `V_zReg = 0`, and
all other registers unchanged. The instruction-presence
hypothesis bundles the 9 lookup equalities at offsets `0..8`.

The `V_tmp = 0` precondition reflects the spec's
register-allocation discipline: `tmp` is a fragment-local
scratch zeroed before each `preservingTransfer` invocation
(e.g. by `bsum_zeroSweep` in bsum's outer iteration). -/
theorem preservingTransfer_correct {a : ℕ}
    (P : URMProgram a) (pcBase : ℕ)
    (src dst tmp zReg : Fin P.numRegs)
    (h_disj_sd : src ≠ dst) (h_disj_st : src ≠ tmp)
    (h_disj_dt : dst ≠ tmp) (h_disj_zs : zReg ≠ src)
    (h_disj_zd : zReg ≠ dst) (h_disj_zt : zReg ≠ tmp)
    (H : preservingTransferInstrs P pcBase src dst tmp zReg)
    (s : URMState P) (h_pc : s.pc = pcBase)
    (h_z : s.regs zReg = 0) (h_tmp0 : s.regs tmp = 0)
    (n : ℕ) (h_src : s.regs src = n) :
    let s' := URMState.runFor P s (9 * n + 2)
    s'.pc = pcBase + 9 ∧
    s'.regs dst = s.regs dst + n ∧
    s'.regs src = n ∧
    s'.regs tmp = 0 ∧
    s'.regs zReg = 0 ∧
    ∀ r, r ≠ dst → s'.regs r = s.regs r := by
  -- 9n + 2 = (5n + 1) + (4n + 1).
  have hsum : 9 * n + 2 = (5 * n + 1) + (4 * n + 1) := by omega
  rw [hsum, URMState.runFor_add]
  obtain ⟨l1_pc, l1_src, l1_dst, l1_tmp, l1_z, l1_oth⟩ :=
    preservingTransfer_loop1 P pcBase src dst tmp zReg
      h_disj_sd h_disj_st h_disj_dt h_disj_zs h_disj_zd h_disj_zt
      H s h_pc h_z n h_src
  set s1 : URMState P := URMState.runFor P s (5 * n + 1)
  -- s1.regs tmp = s.regs tmp + n = 0 + n = n.
  have h_s1_tmp : s1.regs tmp = n := by rw [l1_tmp, h_tmp0]; omega
  obtain ⟨l2_pc, l2_tmp, l2_src, l2_z, l2_oth⟩ :=
    preservingTransfer_loop2 P pcBase src dst tmp zReg
      h_disj_st h_disj_zs h_disj_zt
      H s1 l1_pc l1_z n h_s1_tmp
  refine ⟨l2_pc, ?_, ?_, l2_tmp, l2_z, ?_⟩
  · -- s'.regs dst = s.regs dst + n.
    -- l2_oth: ∀ r, r ≠ src → r ≠ tmp → final_dst = s1.regs dst
    rw [l2_oth dst h_disj_sd.symm h_disj_dt, l1_dst]
  · -- s'.regs src = n.
    -- l2_src: final_src = s1.regs src + n.  s1.regs src = 0.
    rw [l2_src, l1_src, Nat.zero_add]
  · -- For r ≠ dst, also r ≠ src means we go through l1_oth
    -- (preserving src too).  But here we have only r ≠ dst.
    -- Need to handle r = src and r = tmp separately.
    intro r hrd
    by_cases hrs : r = src
    · subst hrs
      rw [l2_src, l1_src, h_src]; omega
    · by_cases hrt : r = tmp
      · subst hrt
        rw [l2_tmp, h_tmp0]
      · rw [l2_oth r hrs hrt, l1_oth r hrs hrd hrt]

/-- Hypothesis bundle for `transferLoop_correct`: the four
instruction-lookup equalities at PCs `pcBase..pcBase+3`
matching the raw layout of `URMRaw.transferLoop`. The
`zReg` parameter holds the reserved-zero register used by
`URMRaw.goto`; it is required to be the register at index
`0` so the trailing `goto` compiles to a zero-test on
`zReg`. -/
structure transferLoopInstrs {a : ℕ}
    (P : URMProgram a) (pcBase : ℕ)
    (src dst zReg : Fin P.numRegs) : Prop where
  h0 : P.instrs[pcBase]? =
    some (.jumpZ src (pcBase + 4) (pcBase + 1))
  h1 : P.instrs[pcBase + 1]? = some (.dec src)
  h2 : P.instrs[pcBase + 2]? = some (.inc dst)
  h3 : P.instrs[pcBase + 3]? = some (.jumpZ zReg pcBase pcBase)

/-- For `compileFrag_comp`'s `i`-th sub-block, the trailing
output-transfer `transferLoop`: at PCs `transferBase ..
transferBase + 3`, where `transferBase = pcBase_i + 9 * a +
((frag_gs i).instrs.size - 1)`, the outer program's
instructions match the four raw instructions of
`URMRaw.transferLoop transferBase (gsBase_i + ((frag_gs
i).outputReg).val) (fBase + (frag_f.inputRegs i).val)`,
after `URMInstrRaw.toBounded` conversion. The three
register arguments (`src`, `dst`, `zReg`) match those used
inside `compileFrag_comp_subBlock`'s output-transfer
trailing block. Parallels
`PreservingTransferInstrs_compileFrag_comp_inputCopies`
for Phase i.1 (input-copies preamble); this lemma covers
Phase i.3 (output-transfer trailing block). -/
theorem TransferLoopInstrs_compileFrag_comp_outputTransfer
    {k a : ℕ}
    (frag_f : CompiledFragment k)
    (frag_gs : Fin k → CompiledFragment a)
    (i : Fin k) :
    let outer := (compileFrag_comp frag_f frag_gs).toURMProgram
    let blockLen : Fin k → ℕ := fun i =>
      9 * a + ((frag_gs i).instrs.size - 1) + 4
    let pcBase_i : ℕ :=
      1 + ((List.finRange k).filter
          (fun n => decide (n.val < i.val))).foldr
        (fun n acc => acc + blockLen n) 0
    let gsBase_i : ℕ := 2 + a + gsPrefixSum frag_gs i.val
    let fBase : ℕ := 2 + a + gsPrefixSum frag_gs k
    let transferBase : ℕ :=
      pcBase_i + 9 * a + ((frag_gs i).instrs.size - 1)
    ∃ (h_src : gsBase_i + ((frag_gs i).outputReg).val
                 < outer.numRegs)
      (h_dst : fBase + (frag_f.inputRegs i).val
                 < outer.numRegs)
      (h_z : 0 < outer.numRegs),
      transferLoopInstrs outer transferBase
        ⟨gsBase_i + ((frag_gs i).outputReg).val, h_src⟩
        ⟨fBase + (frag_f.inputRegs i).val, h_dst⟩
        ⟨0, h_z⟩ := by
  intro outer blockLen pcBase_i gsBase_i fBase transferBase
  -- Auxiliaries matching the constructor of compileFrag_comp.
  let totalGsRegs : ℕ := gsPrefixSum frag_gs k
  let tmpReg : ℕ := fBase + frag_f.numRegs
  let nR : ℕ := tmpReg + 1
  let gsBase : Fin k → ℕ :=
    fun j => 2 + a + gsPrefixSum frag_gs j.val
  let pcBase : Fin k → ℕ := fun j =>
    1 + ((List.finRange k).filter
        (fun n => decide (n.val < j.val))).foldr
      (fun n acc => acc + blockLen n) 0
  let subBlocks : List URMInstrRaw :=
    (List.finRange k).flatMap fun n =>
      compileFrag_comp_subBlock frag_f frag_gs
        (gsBase n) fBase tmpReg n (pcBase n)
  let fPcBase : ℕ :=
    1 + (List.finRange k).foldr
      (fun j acc => acc + blockLen j) 0
  let fBody : List URMInstrRaw :=
    frag_f.instrs.toList.map fun ins =>
      URMInstrRaw.reindexShift fBase fPcBase (toRawOfBounded ins)
  let rawList : List URMInstrRaw :=
    (.assignR 0 0) :: (subBlocks ++ fBody)
  -- Bound facts.
  have h_a_le_fBase : a ≤ fBase := by
    change a ≤ 2 + a + totalGsRegs; omega
  have h_gsBlock_i : gsBase i + (frag_gs i).numRegs ≤ fBase := by
    have hmono : gsPrefixSum frag_gs (i.val + 1)
        ≤ gsPrefixSum frag_gs k :=
      gsPrefixSum_mono frag_gs i.isLt
    have hsucc :
        gsPrefixSum frag_gs (i.val + 1)
          = gsPrefixSum frag_gs i.val + (frag_gs i).numRegs :=
      gsPrefixSum_succ_eq frag_gs i
    change 2 + a + gsPrefixSum frag_gs i.val
        + (frag_gs i).numRegs ≤ 2 + a + totalGsRegs
    change _ ≤ gsPrefixSum frag_gs k at hmono
    omega
  have h_src_lt :
      gsBase_i + ((frag_gs i).outputReg).val < nR := by
    have hO : ((frag_gs i).outputReg).val < (frag_gs i).numRegs :=
      (frag_gs i).outputReg.isLt
    have h_gsBlock_i' :
        2 + a + gsPrefixSum frag_gs i.val + (frag_gs i).numRegs
          ≤ fBase := h_gsBlock_i
    change 2 + a + gsPrefixSum frag_gs i.val
        + ((frag_gs i).outputReg).val < tmpReg + 1
    change _ < (fBase + frag_f.numRegs) + 1
    omega
  have h_dst_lt :
      fBase + (frag_f.inputRegs i).val < nR := by
    have hI : (frag_f.inputRegs i).val < frag_f.numRegs :=
      (frag_f.inputRegs i).isLt
    change fBase + (frag_f.inputRegs i).val < tmpReg + 1
    change _ < (fBase + frag_f.numRegs) + 1
    omega
  have h_z_lt : 0 < nR := by
    change 0 < tmpReg + 1; omega
  have h_numRegs_eq : outer.numRegs = nR := rfl
  refine ⟨h_src_lt, h_dst_lt, h_z_lt, ?_⟩
  -- Sub-block at i: split subBlocks via flatMap_finRange_split.
  obtain ⟨pre, suf, h_subBlocks_split, h_pre_len⟩ :=
    flatMap_finRange_split k
      (fun n => compileFrag_comp_subBlock frag_f frag_gs
        (gsBase n) fBase tmpReg n (pcBase n)) i
  have h_pre_len_eq :
      pre.length = pcBase_i - 1 := by
    rw [h_pre_len]
    change _ = (1 + ((List.finRange k).filter
        (fun n => decide (n.val < i.val))).foldr
      (fun n acc => acc + blockLen n) 0) - 1
    have h_each : ∀ n : Fin k,
        (compileFrag_comp_subBlock frag_f frag_gs
          (gsBase n) fBase tmpReg n (pcBase n)).length
          = blockLen n :=
      fun n => compileFrag_comp_subBlock_length
        frag_f frag_gs (gsBase n) fBase tmpReg n (pcBase n)
    have h_foldr_eq :
        ((List.finRange k).filter
            (fun n => decide (n.val < i.val))).foldr
          (fun n acc => acc +
            (compileFrag_comp_subBlock frag_f frag_gs
              (gsBase n) fBase tmpReg n (pcBase n)).length) 0
          = ((List.finRange k).filter
              (fun n => decide (n.val < i.val))).foldr
            (fun n acc => acc + blockLen n) 0 := by
      induction (List.filter (fun n : Fin k =>
          decide (n.val < i.val)) (List.finRange k)) with
      | nil => rfl
      | cons hd tl ih_inner =>
        simp only [List.foldr_cons, ih_inner, h_each hd]
    rw [h_foldr_eq]
    omega
  -- Sub-block i = inputCopies_i ++ body_i ++ transfer_i.
  set sb_i : List URMInstrRaw :=
    compileFrag_comp_subBlock frag_f frag_gs
      (gsBase i) fBase tmpReg i (pcBase i) with h_sb_i
  let bodyBase_i : ℕ := pcBase i + 9 * a
  let body_i : List URMInstrRaw :=
    (frag_gs i).instrs.pop.toList.map fun ins =>
      URMInstrRaw.reindexShift (gsBase i) bodyBase_i
        (toRawOfBounded ins)
  let inputCopies_i : List URMInstrRaw :=
    (List.finRange a).flatMap fun j' =>
      URMRaw.preservingTransfer
        (pcBase i + 9 * j'.val)
        (2 + j'.val)
        (gsBase i + ((frag_gs i).inputRegs j').val)
        tmpReg
  let transfer_i : List URMInstrRaw :=
    URMRaw.transferLoop
      (bodyBase_i + ((frag_gs i).instrs.size - 1))
      (gsBase i + ((frag_gs i).outputReg).val)
      (fBase + (frag_f.inputRegs i).val)
  have h_sb_i_eq : sb_i = inputCopies_i ++ body_i ++ transfer_i := by
    rw [h_sb_i]; rfl
  have h_subBlocks_full :
      subBlocks = pre ++ inputCopies_i ++ body_i
        ++ transfer_i ++ suf := by
    change _ = ((pre ++ inputCopies_i) ++ body_i)
        ++ transfer_i ++ suf
    rw [show ((pre ++ inputCopies_i) ++ body_i) ++ transfer_i
        = pre ++ (inputCopies_i ++ body_i ++ transfer_i) by
      simp [List.append_assoc]]
    rw [← h_sb_i_eq]
    exact h_subBlocks_split
  -- Length facts for navigation.
  have h_inputCopies_i_len : inputCopies_i.length = 9 * a := by
    change ((List.finRange a).flatMap _).length = _
    rw [List.length_flatMap]
    have h_each : ∀ j' : Fin a,
        (URMRaw.preservingTransfer (pcBase i + 9 * j'.val)
          (2 + j'.val) (gsBase i + ((frag_gs i).inputRegs j').val)
          tmpReg).length = 9 := fun _ => rfl
    rw [List.map_congr_left (fun j' _ => h_each j')]
    rw [show (fun _ : Fin a => 9)
        = Function.const (Fin a) 9 from rfl,
      List.map_const, List.sum_replicate_nat,
      List.length_finRange]
    exact Nat.mul_comm a 9
  have h_body_i_len : body_i.length = (frag_gs i).instrs.size - 1 := by
    change ((frag_gs i).instrs.pop.toList.map _).length = _
    rw [List.length_map, Array.length_toList, Array.size_pop]
  have h_transfer_i_len : transfer_i.length = 4 := rfl
  have h_pcBase_eq_pcBase_i : pcBase i = pcBase_i := rfl
  -- Position-in-rawList helper: transferBase + d, d ∈ {0..3},
  -- equals 1 + pre.length + (9 * a + body_i.length + d).
  have h_pcBase_i_pos : 1 ≤ pcBase_i := by
    change 1 ≤ 1 + _; omega
  have h_pos_lt_subBlocks : ∀ d : ℕ, d < 4 →
      pre.length + (9 * a + (body_i.length + d)) < subBlocks.length := by
    intro d hd
    -- subBlocks.length = pre.length + sb_i.length + suf.length.
    have h_subBlocks_len_eq : subBlocks.length
        = pre.length + sb_i.length + suf.length := by
      change ((List.finRange k).flatMap fun n =>
          compileFrag_comp_subBlock frag_f frag_gs
            (gsBase n) fBase tmpReg n (pcBase n)).length
        = _
      rw [h_subBlocks_split]
      simp [List.length_append, Nat.add_assoc]
    have h_sb_i_len : sb_i.length
        = inputCopies_i.length + body_i.length + transfer_i.length := by
      rw [h_sb_i_eq]
      rw [List.length_append, List.length_append]
    rw [h_subBlocks_len_eq, h_sb_i_len, h_inputCopies_i_len,
      h_transfer_i_len]
    omega
  -- The instruction lookup at position
  -- pre.length + (9 * a + (body_i.length + d)) inside rawList
  -- = transfer_i[d].
  have h_lookup_tl :
      ∀ (d : ℕ) (hd : d < 4),
      let pos : ℕ := pre.length + (9 * a + (body_i.length + d))
      have h_pos_in_sub : pos < subBlocks.length :=
        h_pos_lt_subBlocks d hd
      have h_raw_len_facts : 1 + pos < rawList.length := by
        change _ < (URMInstrRaw.assignR 0 0
          :: (subBlocks ++ fBody)).length
        rw [List.length_cons, List.length_append]; omega
      rawList[1 + pos]'h_raw_len_facts
        = transfer_i[d]'(by rw [h_transfer_i_len]; exact hd) := by
    intro d hd pos h_pos_in_sub h_raw_len_facts
    -- Peel the leading assignR 0 0.
    have h_idx_lt'' : pos < (subBlocks ++ fBody).length := by
      rw [List.length_append]; omega
    have h_idx_lt''' :
        pos + 1 < (URMInstrRaw.assignR 0 0 :: (subBlocks ++ fBody)
            : List URMInstrRaw).length := by
      rw [List.length_cons, List.length_append]; omega
    have h_step1 :
        rawList[1 + pos]'h_raw_len_facts
          = (subBlocks ++ fBody)[pos]'h_idx_lt'' := by
      change ((URMInstrRaw.assignR 0 0 ::
          (subBlocks ++ fBody) : List URMInstrRaw))[1 + pos]'_
        = _
      have h_step1a :
          ((URMInstrRaw.assignR 0 0 ::
              (subBlocks ++ fBody) : List URMInstrRaw))[1 + pos]'h_raw_len_facts
            = ((URMInstrRaw.assignR 0 0 ::
              (subBlocks ++ fBody) : List URMInstrRaw))[pos + 1]'h_idx_lt''' := by
        congr 1
        omega
      rw [h_step1a]
      exact List.getElem_cons_succ (URMInstrRaw.assignR 0 0)
        (subBlocks ++ fBody) pos h_idx_lt'''
    rw [h_step1]
    -- Step into subBlocks via getElem_append_left.
    rw [List.getElem_append_left h_pos_in_sub]
    -- Substitute subBlocks via h_subBlocks_full.
    have h_pos_lt_full :
        pos < (pre ++ inputCopies_i ++ body_i ++ transfer_i ++ suf).length := by
      have := h_subBlocks_full
      rw [this] at h_pos_in_sub
      exact h_pos_in_sub
    have h_step2 :
        subBlocks[pos]'h_pos_in_sub
          = (pre ++ inputCopies_i ++ body_i ++ transfer_i ++ suf)[pos]'h_pos_lt_full := by
      congr 1
    rw [h_step2]
    -- Navigate the append structure.  pos sits within transfer_i.
    have h_pos_lt_4 :
        pos < (pre ++ inputCopies_i ++ body_i ++ transfer_i).length := by
      rw [List.length_append, List.length_append, List.length_append,
        h_inputCopies_i_len, h_transfer_i_len]
      change pre.length + (9 * a + (body_i.length + d)) < _
      omega
    rw [List.getElem_append_left h_pos_lt_4]
    -- Now (pre ++ inputCopies_i ++ body_i ++ transfer_i)[pos],
    -- pos ≥ pre.length + inputCopies_i.length + body_i.length.
    have h_pos_ge_3 :
        (pre ++ inputCopies_i ++ body_i).length ≤ pos := by
      rw [List.length_append, List.length_append,
        h_inputCopies_i_len]
      change _ ≤ pre.length + (9 * a + (body_i.length + d))
      omega
    rw [List.getElem_append_right h_pos_ge_3]
    -- transfer_i[pos - (pre ++ inputCopies_i ++ body_i).length].
    have h_idx_eq :
        pos - (pre ++ inputCopies_i ++ body_i).length = d := by
      rw [List.length_append, List.length_append,
        h_inputCopies_i_len]
      change pre.length + (9 * a + (body_i.length + d))
          - (pre.length + 9 * a + body_i.length) = d
      omega
    have h_d_lt : pos - (pre ++ inputCopies_i ++ body_i).length
        < transfer_i.length := by
      rw [h_idx_eq, h_transfer_i_len]; exact hd
    have h_step5 :
        transfer_i[pos - (pre ++ inputCopies_i ++ body_i).length]'h_d_lt
          = transfer_i[d]'(by rw [h_transfer_i_len]; exact hd) := by
      congr 1
    exact h_step5
  -- General getElem? equality at transferBase + d.
  have h_transferBase_eq :
      transferBase = 1 + (pre.length + (9 * a + body_i.length)) := by
    rw [h_pre_len_eq, h_body_i_len]
    have : 1 ≤ pcBase_i := h_pcBase_i_pos
    change pcBase_i + 9 * a + ((frag_gs i).instrs.size - 1)
        = 1 + ((pcBase_i - 1) + (9 * a + ((frag_gs i).instrs.size - 1)))
    omega
  -- Outer instrs = toBoundedArray of rawList; bound witness.
  have hBoundOuter : URMInstrRaw.boundedBy nR rawList := by
    intro ins hmem
    have hmem' : ins = (.assignR 0 0 : URMInstrRaw)
        ∨ ins ∈ subBlocks ++ fBody := List.mem_cons.mp hmem
    rcases hmem' with hAssign | hmem
    · rw [hAssign]; simp only [URMInstrRaw.regBound]
      change 0 + 1 ≤ nR
      change 0 + 1 ≤ (fBase + frag_f.numRegs) + 1
      have h_fBase_pos : 0 < fBase := by
        change 0 < 2 + a + totalGsRegs; omega
      omega
    rcases List.mem_append.mp hmem with hSub | hF
    · rcases List.mem_flatMap.mp hSub with ⟨n, _, hn⟩
      have hGsBlock : gsBase n + (frag_gs n).numRegs ≤ fBase := by
        have hmono : gsPrefixSum frag_gs (n.val + 1)
            ≤ gsPrefixSum frag_gs k :=
          gsPrefixSum_mono frag_gs n.isLt
        have hsucc :
            gsPrefixSum frag_gs (n.val + 1)
              = gsPrefixSum frag_gs n.val + (frag_gs n).numRegs :=
          gsPrefixSum_succ_eq frag_gs n
        change 2 + a + gsPrefixSum frag_gs n.val
            + (frag_gs n).numRegs ≤ 2 + a + totalGsRegs
        change _ ≤ gsPrefixSum frag_gs k at hmono
        omega
      have hFBlock : fBase + frag_f.numRegs = tmpReg := rfl
      have hTmp : tmpReg < nR := by change tmpReg < tmpReg + 1; omega
      exact boundedBy_compileFrag_comp_subBlock frag_f frag_gs
        (gsBase n) fBase tmpReg nR n (pcBase n)
        hGsBlock hFBlock hTmp h_a_le_fBase ins hn
    · rcases List.mem_map.mp hF with ⟨ins', _, heq⟩
      rw [← heq]
      have hb : (toRawOfBounded ins').regBound ≤ frag_f.numRegs :=
        regBound_toRawOfBounded_le ins'
      have hr := regBound_reindexShift_le_offset_add fBase
        fPcBase frag_f.numRegs (toRawOfBounded ins') hb
      change _ ≤ (fBase + frag_f.numRegs) + 1
      omega
  have h_outer_instrs :
      outer.instrs = URMInstrRaw.toBoundedArray nR rawList
          hBoundOuter := rfl
  -- Membership proof for `transfer_i[d] ∈ rawList`.
  have h_tl_d_in_rawList : ∀ (d : ℕ) (hd : d < 4),
      (transfer_i[d]'(by rw [h_transfer_i_len]; exact hd)) ∈ rawList := by
    intro d hd
    have h_mem_tl :
        transfer_i[d]'(by rw [h_transfer_i_len]; exact hd) ∈ transfer_i :=
      List.getElem_mem _
    have h_mem_sb_i :
        transfer_i[d]'(by rw [h_transfer_i_len]; exact hd) ∈ sb_i := by
      rw [h_sb_i_eq]
      exact List.mem_append.mpr (Or.inr h_mem_tl)
    have h_mem_subBlocks :
        transfer_i[d]'(by rw [h_transfer_i_len]; exact hd) ∈ subBlocks := by
      change transfer_i[d]'_ ∈ (List.finRange k).flatMap _
      exact List.mem_flatMap.mpr
        ⟨i, List.mem_finRange _, h_mem_sb_i⟩
    exact List.mem_cons.mpr
      (Or.inr (List.mem_append.mpr (Or.inl h_mem_subBlocks)))
  have h_outerInstr_lookup :
      ∀ (d : ℕ) (hd : d < 4),
        outer.instrs[transferBase + d]?
          = some (URMInstrRaw.toBounded nR
              (transfer_i[d]'(by rw [h_transfer_i_len]; exact hd))
              (hBoundOuter _ (h_tl_d_in_rawList d hd))) := by
    intro d hd
    have h_pos_lt : pre.length + (9 * a + (body_i.length + d))
        < subBlocks.length :=
      h_pos_lt_subBlocks d hd
    have h_idx_lt :
        1 + (pre.length + (9 * a + (body_i.length + d)))
          < rawList.length := by
      change _ < (URMInstrRaw.assignR 0 0
        :: (subBlocks ++ fBody)).length
      rw [List.length_cons, List.length_append]; omega
    -- transferBase + d
    --   = 1 + (pre.length + (9 * a + (body_i.length + d))).
    have h_pcs_eq : transferBase + d
        = 1 + (pre.length + (9 * a + (body_i.length + d))) := by
      rw [h_transferBase_eq]; omega
    have h_idx_lt_outer :
        transferBase + d < rawList.length := by
      rw [h_pcs_eq]; exact h_idx_lt
    -- Reduce via toBoundedArray_getElem?.
    change (URMInstrRaw.toBoundedArray nR rawList hBoundOuter)[
        transferBase + d]? = _
    rw [URMInstrRaw.toBoundedArray_getElem? nR rawList hBoundOuter
        (transferBase + d) h_idx_lt_outer]
    -- Show the raw equality.
    have h_raw_eq :
        rawList[transferBase + d]'h_idx_lt_outer
          = transfer_i[d]'(by rw [h_transfer_i_len]; exact hd) := by
      have h_step :
          rawList[transferBase + d]'h_idx_lt_outer
            = rawList[1 + (pre.length
                + (9 * a + (body_i.length + d)))]'h_idx_lt := by
        congr 1
      rw [h_step]
      exact h_lookup_tl d hd
    apply congrArg some
    exact URMInstrRaw.toBounded_congr nR h_raw_eq _ _
  -- Now build the transferLoopInstrs witness using the four
  -- concrete entries of transfer_i.  Each h_inst_d follows by
  -- specialising h_outerInstr_lookup at d.
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals (
    first
      | exact h_outerInstr_lookup 0 (by decide)
      | exact h_outerInstr_lookup 1 (by decide)
      | exact h_outerInstr_lookup 2 (by decide)
      | exact h_outerInstr_lookup 3 (by decide))

/-- Correctness of the `URMRaw.transferLoop` 4-instruction
block. Running for `4 * n + 1` steps from a state with
`pc = pcBase`, `V_src = n`, and the reserved-zero register
`V_zReg = 0` yields a state with `pc = pcBase + 4`,
`V_dst += n`, `V_src = 0` (destructively consumed),
`V_zReg = 0`, and all other registers unchanged. The
instruction-presence hypothesis bundles the four lookup
equalities at offsets `0..3`. -/
theorem transferLoop_correct {a : ℕ}
    (P : URMProgram a) (pcBase : ℕ)
    (src dst zReg : Fin P.numRegs)
    (h_disj_sd : src ≠ dst) (h_disj_zs : zReg ≠ src)
    (h_disj_zd : zReg ≠ dst)
    (H : transferLoopInstrs P pcBase src dst zReg)
    (s : URMState P) (h_pc : s.pc = pcBase)
    (h_z : s.regs zReg = 0)
    (n : ℕ) (h_src : s.regs src = n) :
    let s' := URMState.runFor P s (4 * n + 1)
    s'.pc = pcBase + 4 ∧
    s'.regs dst = s.regs dst + n ∧
    s'.regs src = 0 ∧
    s'.regs zReg = 0 ∧
    ∀ r, r ≠ dst → r ≠ src → r ≠ zReg →
      s'.regs r = s.regs r := by
  simp only []
  induction n generalizing s with
  | zero =>
    -- 1 step: jumpZ src (pcBase+4) (pcBase+1).  V_src = 0,
    -- so PC → pcBase+4.
    have hstep : (4 * 0 + 1 : ℕ) = 0 + 1 := rfl
    rw [hstep, URMState.runFor_succ, URMState.runFor_zero,
      URMState.step_of_getElem?_jumpZ P s pcBase src
        (pcBase + 4) (pcBase + 1) h_pc H.h0]
    have hsrc_eq : s.regs src = 0 := h_src
    simp only [hsrc_eq, ↓reduceIte]
    refine ⟨trivial, ?_, trivial, h_z, fun _ _ _ _ => trivial⟩
    show s.regs dst = s.regs dst + 0
    omega
  | succ n ih =>
    -- Peel 4 steps: jumpZ (to pcBase+1), dec src, inc dst,
    -- goto pcBase.  Then apply ih on the resulting state
    -- with V_src = n.
    have h4n : 4 * (n + 1) + 1 = 4 + (4 * n + 1) := by omega
    rw [h4n, URMState.runFor_add]
    set s4 : URMState P :=
      { pc := pcBase
        regs := Function.update
          (Function.update s.regs src (s.regs src - 1))
          dst ((Function.update s.regs src (s.regs src - 1)) dst + 1) }
      with hs4_def
    have h_src_ne : s.regs src ≠ 0 := by rw [h_src]; omega
    have h_four : URMState.runFor P s 4 = s4 := by
      change URMState.runFor P s (3 + 1) = _
      rw [URMState.runFor_succ,
        URMState.step_of_getElem?_jumpZ P s pcBase src
          (pcBase + 4) (pcBase + 1) h_pc H.h0]
      simp only [h_src_ne, ↓reduceIte]
      set s1 : URMState P :=
        { pc := pcBase + 1, regs := s.regs } with hs1_def
      have hs1_pc : s1.pc = pcBase + 1 := rfl
      change URMState.runFor P s1 (2 + 1) = _
      rw [URMState.runFor_succ,
        URMState.step_of_getElem?_dec P s1 (pcBase + 1) src hs1_pc H.h1]
      set s2 : URMState P :=
        { pc := s1.pc + 1
          regs := Function.update s1.regs src (s1.regs src - 1) } with hs2_def
      have hs2_pc : s2.pc = pcBase + 2 := by
        change s1.pc + 1 = pcBase + 2; rw [hs1_pc]
      change URMState.runFor P s2 (1 + 1) = _
      rw [URMState.runFor_succ,
        URMState.step_of_getElem?_inc P s2 (pcBase + 2) dst hs2_pc H.h2]
      set s3 : URMState P :=
        { pc := s2.pc + 1
          regs := Function.update s2.regs dst (s2.regs dst + 1) } with hs3_def
      have hs3_pc : s3.pc = pcBase + 3 := by
        change s2.pc + 1 = pcBase + 3; rw [hs2_pc]
      change URMState.runFor P s3 (0 + 1) = _
      rw [URMState.runFor_succ, URMState.runFor_zero,
        URMState.step_of_getElem?_jumpZ P s3 (pcBase + 3) zReg
          pcBase pcBase hs3_pc H.h3]
      have hs3_z : s3.regs zReg = 0 := by
        change Function.update s2.regs dst _ zReg = 0
        rw [Function.update_of_ne h_disj_zd]
        change Function.update s1.regs src _ zReg = 0
        rw [Function.update_of_ne h_disj_zs]
        exact h_z
      simp only [hs3_z, ↓reduceIte]
      rfl
    rw [h_four]
    have hs4_pc : s4.pc = pcBase := rfl
    have hs4_z : s4.regs zReg = 0 := by
      change Function.update (Function.update s.regs src
        (s.regs src - 1)) dst _ zReg = 0
      rw [Function.update_of_ne h_disj_zd]
      rw [Function.update_of_ne h_disj_zs]
      exact h_z
    have hs4_src : s4.regs src = n := by
      change Function.update (Function.update s.regs src
        (s.regs src - 1)) dst _ src = n
      rw [Function.update_of_ne h_disj_sd]
      rw [Function.update_self]
      omega
    have hs4_dst : s4.regs dst = s.regs dst + 1 := by
      change Function.update (Function.update s.regs src
        (s.regs src - 1)) dst _ dst = _
      rw [Function.update_self]
      rw [Function.update_of_ne h_disj_sd.symm]
    have hs4_other : ∀ r, r ≠ dst → r ≠ src →
        s4.regs r = s.regs r := by
      intro r hrd hrs
      change Function.update (Function.update s.regs src
        (s.regs src - 1)) dst _ r = _
      rw [Function.update_of_ne hrd]
      rw [Function.update_of_ne hrs]
    obtain ⟨ih_pc, ih_dst, ih_src, ih_z, ih_oth⟩ :=
      ih s4 hs4_pc hs4_z hs4_src
    refine ⟨ih_pc, ?_, ih_src, ih_z, ?_⟩
    · rw [ih_dst, hs4_dst]; omega
    · intro r hrd hrs hrz
      rw [ih_oth r hrd hrs hrz, hs4_other r hrd hrs]

/-- Per-step PC bound for `transferLoop_correct`: during the
`4 * n + 1` steps of the loop, the intermediate PC stays
within `[pcBase, pcBase + 4]`. This complements the
`transferLoop_correct` lemma's final-state characterisation
with a witness for every intermediate step, used downstream
to show that compositional URMs do not prematurely escape
their compiled fragment via the loop block. -/
theorem transferLoop_correct_pc_bound {a : ℕ}
    (P : URMProgram a) (pcBase : ℕ)
    (src dst zReg : Fin P.numRegs)
    (h_disj_sd : src ≠ dst) (h_disj_zs : zReg ≠ src)
    (h_disj_zd : zReg ≠ dst)
    (H : transferLoopInstrs P pcBase src dst zReg)
    (s : URMState P) (h_pc : s.pc = pcBase)
    (h_z : s.regs zReg = 0)
    (n : ℕ) (h_src : s.regs src = n)
    (k : ℕ) (h_k : k ≤ 4 * n + 1) :
    (URMState.runFor P s k).pc ≤ pcBase + 4 := by
  induction n generalizing s k with
  | zero =>
    -- k ≤ 1.  k = 0: pc = pcBase.  k = 1: jumpZ taken to pcBase+4.
    match k, h_k with
    | 0, _ => rw [URMState.runFor_zero, h_pc]; omega
    | 1, _ =>
      rw [show (1 : ℕ) = 0 + 1 from rfl, URMState.runFor_succ,
        URMState.runFor_zero,
        URMState.step_of_getElem?_jumpZ P s pcBase src
          (pcBase + 4) (pcBase + 1) h_pc H.h0]
      have hsrc_eq : s.regs src = 0 := h_src
      simp only [hsrc_eq, ↓reduceIte]
      omega
  | succ n ih =>
    -- For k ≤ 4: peel steps individually.  For k ≥ 4: invoke IH.
    have h_src_ne : s.regs src ≠ 0 := by rw [h_src]; omega
    set s1 : URMState P :=
      { pc := pcBase + 1, regs := s.regs } with hs1_def
    have hs1_pc : s1.pc = pcBase + 1 := rfl
    set s2 : URMState P :=
      { pc := pcBase + 2
        regs := Function.update s1.regs src (s1.regs src - 1) }
      with hs2_def
    have hs2_pc : s2.pc = pcBase + 2 := rfl
    set s3 : URMState P :=
      { pc := pcBase + 3
        regs := Function.update s2.regs dst (s2.regs dst + 1) }
      with hs3_def
    have hs3_pc : s3.pc = pcBase + 3 := rfl
    set s4 : URMState P :=
      { pc := pcBase
        regs := Function.update
          (Function.update s.regs src (s.regs src - 1))
          dst ((Function.update s.regs src (s.regs src - 1)) dst + 1) }
      with hs4_def
    have h_one : URMState.runFor P s 1 = s1 := by
      rw [show (1 : ℕ) = 0 + 1 from rfl, URMState.runFor_succ,
        URMState.runFor_zero,
        URMState.step_of_getElem?_jumpZ P s pcBase src
          (pcBase + 4) (pcBase + 1) h_pc H.h0]
      simp only [h_src_ne, ↓reduceIte]
      rfl
    have h_two : URMState.runFor P s 2 = s2 := by
      rw [show (2 : ℕ) = 1 + 1 from rfl, URMState.runFor_add, h_one]
      rw [show (1 : ℕ) = 0 + 1 from rfl, URMState.runFor_succ,
        URMState.runFor_zero,
        URMState.step_of_getElem?_dec P s1 (pcBase + 1) src hs1_pc H.h1]
    have h_three : URMState.runFor P s 3 = s3 := by
      rw [show (3 : ℕ) = 2 + 1 from rfl, URMState.runFor_add, h_two]
      rw [show (1 : ℕ) = 0 + 1 from rfl, URMState.runFor_succ,
        URMState.runFor_zero,
        URMState.step_of_getElem?_inc P s2 (pcBase + 2) dst hs2_pc H.h2]
    have h_four : URMState.runFor P s 4 = s4 := by
      rw [show (4 : ℕ) = 3 + 1 from rfl, URMState.runFor_add, h_three]
      rw [show (1 : ℕ) = 0 + 1 from rfl, URMState.runFor_succ,
        URMState.runFor_zero,
        URMState.step_of_getElem?_jumpZ P s3 (pcBase + 3) zReg
          pcBase pcBase hs3_pc H.h3]
      have hs3_z : s3.regs zReg = 0 := by
        change Function.update s2.regs dst _ zReg = 0
        rw [Function.update_of_ne h_disj_zd]
        change Function.update s1.regs src _ zReg = 0
        rw [Function.update_of_ne h_disj_zs]
        exact h_z
      simp only [hs3_z, ↓reduceIte]
      rfl
    -- Case-split on k.
    by_cases hk : k ≤ 4
    · -- 0 ≤ k ≤ 4.  Use h_one, h_two, h_three, h_four.
      match k, hk with
      | 0, _ => rw [URMState.runFor_zero, h_pc]; omega
      | 1, _ => rw [h_one]; change pcBase + 1 ≤ pcBase + 4; omega
      | 2, _ => rw [h_two]; change pcBase + 2 ≤ pcBase + 4; omega
      | 3, _ => rw [h_three]; change pcBase + 3 ≤ pcBase + 4; omega
      | 4, _ => rw [h_four]; change pcBase ≤ pcBase + 4; omega
    · -- k > 4.  Write k = 4 + k' with k' ≤ 4n + 1.
      push_neg at hk
      obtain ⟨k', rfl⟩ : ∃ k', k = 4 + k' := ⟨k - 4, by omega⟩
      have h_k' : k' ≤ 4 * n + 1 := by omega
      rw [URMState.runFor_add, h_four]
      have hs4_pc : s4.pc = pcBase := rfl
      have hs4_z : s4.regs zReg = 0 := by
        change Function.update (Function.update s.regs src
          (s.regs src - 1)) dst _ zReg = 0
        rw [Function.update_of_ne h_disj_zd]
        rw [Function.update_of_ne h_disj_zs]
        exact h_z
      have hs4_src : s4.regs src = n := by
        change Function.update (Function.update s.regs src
          (s.regs src - 1)) dst _ src = n
        rw [Function.update_of_ne h_disj_sd]
        rw [Function.update_self]
        omega
      exact ih s4 hs4_pc hs4_z hs4_src k' h_k'

/-- Strict per-step PC bound for `transferLoop_correct`: for
`k ≤ 4 * n` (i.e., strictly before the final exit step), the
intermediate PC is at most `pcBase + 3`. Strict variant of
`transferLoop_correct_pc_bound`. -/
theorem transferLoop_correct_pc_strict_bound {a : ℕ}
    (P : URMProgram a) (pcBase : ℕ)
    (src dst zReg : Fin P.numRegs)
    (h_disj_sd : src ≠ dst) (h_disj_zs : zReg ≠ src)
    (h_disj_zd : zReg ≠ dst)
    (H : transferLoopInstrs P pcBase src dst zReg)
    (s : URMState P) (h_pc : s.pc = pcBase)
    (h_z : s.regs zReg = 0)
    (n : ℕ) (h_src : s.regs src = n)
    (k : ℕ) (h_k : k ≤ 4 * n) :
    (URMState.runFor P s k).pc ≤ pcBase + 3 := by
  induction n generalizing s k with
  | zero =>
    match k, h_k with
    | 0, _ => rw [URMState.runFor_zero, h_pc]; omega
  | succ n ih =>
    have h_src_ne : s.regs src ≠ 0 := by rw [h_src]; omega
    set s1 : URMState P :=
      { pc := pcBase + 1, regs := s.regs } with hs1_def
    have hs1_pc : s1.pc = pcBase + 1 := rfl
    set s2 : URMState P :=
      { pc := pcBase + 2
        regs := Function.update s1.regs src (s1.regs src - 1) }
      with hs2_def
    have hs2_pc : s2.pc = pcBase + 2 := rfl
    set s3 : URMState P :=
      { pc := pcBase + 3
        regs := Function.update s2.regs dst (s2.regs dst + 1) }
      with hs3_def
    have hs3_pc : s3.pc = pcBase + 3 := rfl
    set s4 : URMState P :=
      { pc := pcBase
        regs := Function.update
          (Function.update s.regs src (s.regs src - 1))
          dst ((Function.update s.regs src (s.regs src - 1)) dst + 1) }
      with hs4_def
    have h_one : URMState.runFor P s 1 = s1 := by
      rw [show (1 : ℕ) = 0 + 1 from rfl, URMState.runFor_succ,
        URMState.runFor_zero,
        URMState.step_of_getElem?_jumpZ P s pcBase src
          (pcBase + 4) (pcBase + 1) h_pc H.h0]
      simp only [h_src_ne, ↓reduceIte]
      rfl
    have h_two : URMState.runFor P s 2 = s2 := by
      rw [show (2 : ℕ) = 1 + 1 from rfl, URMState.runFor_add, h_one]
      rw [show (1 : ℕ) = 0 + 1 from rfl, URMState.runFor_succ,
        URMState.runFor_zero,
        URMState.step_of_getElem?_dec P s1 (pcBase + 1) src hs1_pc H.h1]
    have h_three : URMState.runFor P s 3 = s3 := by
      rw [show (3 : ℕ) = 2 + 1 from rfl, URMState.runFor_add, h_two]
      rw [show (1 : ℕ) = 0 + 1 from rfl, URMState.runFor_succ,
        URMState.runFor_zero,
        URMState.step_of_getElem?_inc P s2 (pcBase + 2) dst hs2_pc H.h2]
    have h_four : URMState.runFor P s 4 = s4 := by
      rw [show (4 : ℕ) = 3 + 1 from rfl, URMState.runFor_add, h_three]
      rw [show (1 : ℕ) = 0 + 1 from rfl, URMState.runFor_succ,
        URMState.runFor_zero,
        URMState.step_of_getElem?_jumpZ P s3 (pcBase + 3) zReg
          pcBase pcBase hs3_pc H.h3]
      have hs3_z : s3.regs zReg = 0 := by
        change Function.update s2.regs dst _ zReg = 0
        rw [Function.update_of_ne h_disj_zd]
        change Function.update s1.regs src _ zReg = 0
        rw [Function.update_of_ne h_disj_zs]
        exact h_z
      simp only [hs3_z, ↓reduceIte]
      rfl
    by_cases hk : k ≤ 4
    · match k, hk with
      | 0, _ => rw [URMState.runFor_zero, h_pc]; omega
      | 1, _ => rw [h_one]; change pcBase + 1 ≤ pcBase + 3; omega
      | 2, _ => rw [h_two]; change pcBase + 2 ≤ pcBase + 3; omega
      | 3, _ => rw [h_three]
      | 4, _ => rw [h_four]; change pcBase ≤ pcBase + 3; omega
    · push_neg at hk
      obtain ⟨k', rfl⟩ : ∃ k', k = 4 + k' := ⟨k - 4, by omega⟩
      have h_k' : k' ≤ 4 * n := by omega
      rw [URMState.runFor_add, h_four]
      have hs4_pc : s4.pc = pcBase := rfl
      have hs4_z : s4.regs zReg = 0 := by
        change Function.update (Function.update s.regs src
          (s.regs src - 1)) dst _ zReg = 0
        rw [Function.update_of_ne h_disj_zd]
        rw [Function.update_of_ne h_disj_zs]
        exact h_z
      have hs4_src : s4.regs src = n := by
        change Function.update (Function.update s.regs src
          (s.regs src - 1)) dst _ src = n
        rw [Function.update_of_ne h_disj_sd]
        rw [Function.update_self]
        omega
      exact ih s4 hs4_pc hs4_z hs4_src k' h_k'

/-- Hypothesis bundle for `subInnerLoop_correct`: the four
instruction-lookup equalities at PCs `pcBase..pcBase+3`
matching the inner decrement loop of `compileFrag_sub`.
Test on `src`; the body decrements both `src` and `dst`;
the trailing `goto` returns to the test via `zReg`. -/
structure subInnerLoopInstrs {a : ℕ}
    (P : URMProgram a) (pcBase : ℕ)
    (src dst zReg : Fin P.numRegs) : Prop where
  h0 : P.instrs[pcBase]? =
    some (.jumpZ src (pcBase + 4) (pcBase + 1))
  h1 : P.instrs[pcBase + 1]? = some (.dec src)
  h2 : P.instrs[pcBase + 2]? = some (.dec dst)
  h3 : P.instrs[pcBase + 3]? = some (.jumpZ zReg pcBase pcBase)

/-- Correctness of the inner decrement loop emitted by
`compileFrag_sub`. Running for `4 * n + 1` steps from a state
with `pc = pcBase`, `V_src = n`, and reserved-zero register
`V_zReg = 0` yields a state with `pc = pcBase + 4`,
`V_src = 0` (consumed), `V_dst = V_dst - n` (truncated),
`V_zReg = 0`, and all other registers unchanged. Mirrors
`transferLoop_correct` with `decR dst` substituted for
`incR dst`. -/
theorem subInnerLoop_correct {a : ℕ}
    (P : URMProgram a) (pcBase : ℕ)
    (src dst zReg : Fin P.numRegs)
    (h_disj_sd : src ≠ dst) (h_disj_zs : zReg ≠ src)
    (h_disj_zd : zReg ≠ dst)
    (H : subInnerLoopInstrs P pcBase src dst zReg)
    (s : URMState P) (h_pc : s.pc = pcBase)
    (h_z : s.regs zReg = 0)
    (n : ℕ) (h_src : s.regs src = n) :
    let s' := URMState.runFor P s (4 * n + 1)
    s'.pc = pcBase + 4 ∧
    s'.regs dst = s.regs dst - n ∧
    s'.regs src = 0 ∧
    s'.regs zReg = 0 ∧
    ∀ r, r ≠ dst → r ≠ src → r ≠ zReg →
      s'.regs r = s.regs r := by
  simp only []
  induction n generalizing s with
  | zero =>
    -- 1 step: jumpZ src (pcBase+4) (pcBase+1).  V_src = 0,
    -- so PC → pcBase+4.
    have hstep : (4 * 0 + 1 : ℕ) = 0 + 1 := rfl
    rw [hstep, URMState.runFor_succ, URMState.runFor_zero,
      URMState.step_of_getElem?_jumpZ P s pcBase src
        (pcBase + 4) (pcBase + 1) h_pc H.h0]
    have hsrc_eq : s.regs src = 0 := h_src
    simp only [hsrc_eq, ↓reduceIte]
    refine ⟨trivial, ?_, trivial, h_z, fun _ _ _ _ => trivial⟩
    show s.regs dst = s.regs dst - 0
    omega
  | succ n ih =>
    -- Peel 4 steps: jumpZ (to pcBase+1), dec src, dec dst,
    -- goto pcBase.  Then apply ih on the resulting state
    -- with V_src = n.
    have h4n : 4 * (n + 1) + 1 = 4 + (4 * n + 1) := by omega
    rw [h4n, URMState.runFor_add]
    set s4 : URMState P :=
      { pc := pcBase
        regs := Function.update
          (Function.update s.regs src (s.regs src - 1))
          dst ((Function.update s.regs src (s.regs src - 1)) dst - 1) }
      with hs4_def
    have h_src_ne : s.regs src ≠ 0 := by rw [h_src]; omega
    have h_four : URMState.runFor P s 4 = s4 := by
      change URMState.runFor P s (3 + 1) = _
      rw [URMState.runFor_succ,
        URMState.step_of_getElem?_jumpZ P s pcBase src
          (pcBase + 4) (pcBase + 1) h_pc H.h0]
      simp only [h_src_ne, ↓reduceIte]
      set s1 : URMState P :=
        { pc := pcBase + 1, regs := s.regs } with hs1_def
      have hs1_pc : s1.pc = pcBase + 1 := rfl
      change URMState.runFor P s1 (2 + 1) = _
      rw [URMState.runFor_succ,
        URMState.step_of_getElem?_dec P s1 (pcBase + 1) src hs1_pc H.h1]
      set s2 : URMState P :=
        { pc := s1.pc + 1
          regs := Function.update s1.regs src (s1.regs src - 1) } with hs2_def
      have hs2_pc : s2.pc = pcBase + 2 := by
        change s1.pc + 1 = pcBase + 2; rw [hs1_pc]
      change URMState.runFor P s2 (1 + 1) = _
      rw [URMState.runFor_succ,
        URMState.step_of_getElem?_dec P s2 (pcBase + 2) dst hs2_pc H.h2]
      set s3 : URMState P :=
        { pc := s2.pc + 1
          regs := Function.update s2.regs dst (s2.regs dst - 1) } with hs3_def
      have hs3_pc : s3.pc = pcBase + 3 := by
        change s2.pc + 1 = pcBase + 3; rw [hs2_pc]
      change URMState.runFor P s3 (0 + 1) = _
      rw [URMState.runFor_succ, URMState.runFor_zero,
        URMState.step_of_getElem?_jumpZ P s3 (pcBase + 3) zReg
          pcBase pcBase hs3_pc H.h3]
      have hs3_z : s3.regs zReg = 0 := by
        change Function.update s2.regs dst _ zReg = 0
        rw [Function.update_of_ne h_disj_zd]
        change Function.update s1.regs src _ zReg = 0
        rw [Function.update_of_ne h_disj_zs]
        exact h_z
      simp only [hs3_z, ↓reduceIte]
      rfl
    rw [h_four]
    have hs4_pc : s4.pc = pcBase := rfl
    have hs4_z : s4.regs zReg = 0 := by
      change Function.update (Function.update s.regs src
        (s.regs src - 1)) dst _ zReg = 0
      rw [Function.update_of_ne h_disj_zd]
      rw [Function.update_of_ne h_disj_zs]
      exact h_z
    have hs4_src : s4.regs src = n := by
      change Function.update (Function.update s.regs src
        (s.regs src - 1)) dst _ src = n
      rw [Function.update_of_ne h_disj_sd]
      rw [Function.update_self]
      omega
    have hs4_dst : s4.regs dst = s.regs dst - 1 := by
      change Function.update (Function.update s.regs src
        (s.regs src - 1)) dst _ dst = _
      rw [Function.update_self]
      rw [Function.update_of_ne h_disj_sd.symm]
    have hs4_other : ∀ r, r ≠ dst → r ≠ src →
        s4.regs r = s.regs r := by
      intro r hrd hrs
      change Function.update (Function.update s.regs src
        (s.regs src - 1)) dst _ r = _
      rw [Function.update_of_ne hrd]
      rw [Function.update_of_ne hrs]
    obtain ⟨ih_pc, ih_dst, ih_src, ih_z, ih_oth⟩ :=
      ih s4 hs4_pc hs4_z hs4_src
    refine ⟨ih_pc, ?_, ih_src, ih_z, ?_⟩
    · rw [ih_dst, hs4_dst]; omega
    · intro r hrd hrs hrz
      rw [ih_oth r hrd hrs hrz, hs4_other r hrd hrs]

/-- Per-step PC bound for `subInnerLoop_correct`: during the
`4 * n + 1` steps of the inner decrement loop, the intermediate
PC stays within `[pcBase, pcBase + 4]`. Mirrors
`transferLoop_correct_pc_bound` with `decR dst` substituted for
`incR dst`. -/
private theorem subInnerLoop_correct_pc_bound {a : ℕ}
    (P : URMProgram a) (pcBase : ℕ)
    (src dst zReg : Fin P.numRegs)
    (h_disj_sd : src ≠ dst) (h_disj_zs : zReg ≠ src)
    (h_disj_zd : zReg ≠ dst)
    (H : subInnerLoopInstrs P pcBase src dst zReg)
    (s : URMState P) (h_pc : s.pc = pcBase)
    (h_z : s.regs zReg = 0)
    (n : ℕ) (h_src : s.regs src = n)
    (k : ℕ) (h_k : k ≤ 4 * n + 1) :
    (URMState.runFor P s k).pc ≤ pcBase + 4 := by
  induction n generalizing s k with
  | zero =>
    match k, h_k with
    | 0, _ => rw [URMState.runFor_zero, h_pc]; omega
    | 1, _ =>
      rw [show (1 : ℕ) = 0 + 1 from rfl, URMState.runFor_succ,
        URMState.runFor_zero,
        URMState.step_of_getElem?_jumpZ P s pcBase src
          (pcBase + 4) (pcBase + 1) h_pc H.h0]
      have hsrc_eq : s.regs src = 0 := h_src
      simp only [hsrc_eq, ↓reduceIte]
      omega
  | succ n ih =>
    have h_src_ne : s.regs src ≠ 0 := by rw [h_src]; omega
    set s1 : URMState P :=
      { pc := pcBase + 1, regs := s.regs } with hs1_def
    have hs1_pc : s1.pc = pcBase + 1 := rfl
    set s2 : URMState P :=
      { pc := pcBase + 2
        regs := Function.update s1.regs src (s1.regs src - 1) }
      with hs2_def
    have hs2_pc : s2.pc = pcBase + 2 := rfl
    set s3 : URMState P :=
      { pc := pcBase + 3
        regs := Function.update s2.regs dst (s2.regs dst - 1) }
      with hs3_def
    have hs3_pc : s3.pc = pcBase + 3 := rfl
    set s4 : URMState P :=
      { pc := pcBase
        regs := Function.update
          (Function.update s.regs src (s.regs src - 1))
          dst ((Function.update s.regs src (s.regs src - 1)) dst - 1) }
      with hs4_def
    have h_one : URMState.runFor P s 1 = s1 := by
      rw [show (1 : ℕ) = 0 + 1 from rfl, URMState.runFor_succ,
        URMState.runFor_zero,
        URMState.step_of_getElem?_jumpZ P s pcBase src
          (pcBase + 4) (pcBase + 1) h_pc H.h0]
      simp only [h_src_ne, ↓reduceIte]
      rfl
    have h_two : URMState.runFor P s 2 = s2 := by
      rw [show (2 : ℕ) = 1 + 1 from rfl, URMState.runFor_add, h_one]
      rw [show (1 : ℕ) = 0 + 1 from rfl, URMState.runFor_succ,
        URMState.runFor_zero,
        URMState.step_of_getElem?_dec P s1 (pcBase + 1) src hs1_pc H.h1]
    have h_three : URMState.runFor P s 3 = s3 := by
      rw [show (3 : ℕ) = 2 + 1 from rfl, URMState.runFor_add, h_two]
      rw [show (1 : ℕ) = 0 + 1 from rfl, URMState.runFor_succ,
        URMState.runFor_zero,
        URMState.step_of_getElem?_dec P s2 (pcBase + 2) dst hs2_pc H.h2]
    have h_four : URMState.runFor P s 4 = s4 := by
      rw [show (4 : ℕ) = 3 + 1 from rfl, URMState.runFor_add, h_three]
      rw [show (1 : ℕ) = 0 + 1 from rfl, URMState.runFor_succ,
        URMState.runFor_zero,
        URMState.step_of_getElem?_jumpZ P s3 (pcBase + 3) zReg
          pcBase pcBase hs3_pc H.h3]
      have hs3_z : s3.regs zReg = 0 := by
        change Function.update s2.regs dst _ zReg = 0
        rw [Function.update_of_ne h_disj_zd]
        change Function.update s1.regs src _ zReg = 0
        rw [Function.update_of_ne h_disj_zs]
        exact h_z
      simp only [hs3_z, ↓reduceIte]
      rfl
    by_cases hk : k ≤ 4
    · match k, hk with
      | 0, _ => rw [URMState.runFor_zero, h_pc]; omega
      | 1, _ => rw [h_one]; change pcBase + 1 ≤ pcBase + 4; omega
      | 2, _ => rw [h_two]; change pcBase + 2 ≤ pcBase + 4; omega
      | 3, _ => rw [h_three]; change pcBase + 3 ≤ pcBase + 4; omega
      | 4, _ => rw [h_four]; change pcBase ≤ pcBase + 4; omega
    · push_neg at hk
      obtain ⟨k', rfl⟩ : ∃ k', k = 4 + k' := ⟨k - 4, by omega⟩
      have h_k' : k' ≤ 4 * n + 1 := by omega
      rw [URMState.runFor_add, h_four]
      have hs4_pc : s4.pc = pcBase := rfl
      have hs4_z : s4.regs zReg = 0 := by
        change Function.update (Function.update s.regs src
          (s.regs src - 1)) dst _ zReg = 0
        rw [Function.update_of_ne h_disj_zd]
        rw [Function.update_of_ne h_disj_zs]
        exact h_z
      have hs4_src : s4.regs src = n := by
        change Function.update (Function.update s.regs src
          (s.regs src - 1)) dst _ src = n
        rw [Function.update_of_ne h_disj_sd]
        rw [Function.update_self]
        omega
      exact ih s4 hs4_pc hs4_z hs4_src k' h_k'

/-- Strict per-step PC bound for `preservingTransfer_loop2`:
for `k ≤ 4 * m`, the intermediate PC is at most `pcBase + 8`
(i.e., strictly less than the final-exit PC `pcBase + 9`).
The exit transition from `pcBase + 5` to `pcBase + 9` only
fires at the final step `k = 4 * m + 1`. -/
private theorem preservingTransfer_loop2_pc_strict_bound {a : ℕ}
    (P : URMProgram a) (pcBase : ℕ)
    (src dst tmp zReg : Fin P.numRegs)
    (h_disj_st : src ≠ tmp)
    (h_disj_zs : zReg ≠ src) (h_disj_zt : zReg ≠ tmp)
    (H : preservingTransferInstrs P pcBase src dst tmp zReg)
    (s : URMState P) (h_pc : s.pc = pcBase + 5)
    (h_z : s.regs zReg = 0)
    (m : ℕ) (h_tmp : s.regs tmp = m)
    (k : ℕ) (h_k : k ≤ 4 * m) :
    (URMState.runFor P s k).pc ≤ pcBase + 8 := by
  induction m generalizing s k with
  | zero =>
    match k, h_k with
    | 0, _ => rw [URMState.runFor_zero, h_pc]; omega
  | succ m ih =>
    have h_tmp_ne : s.regs tmp ≠ 0 := by rw [h_tmp]; omega
    set s1 : URMState P :=
      { pc := pcBase + 6, regs := s.regs } with hs1_def
    have hs1_pc : s1.pc = pcBase + 6 := rfl
    set s2 : URMState P :=
      { pc := pcBase + 7
        regs := Function.update s1.regs tmp (s1.regs tmp - 1) }
      with hs2_def
    have hs2_pc : s2.pc = pcBase + 7 := rfl
    set s3 : URMState P :=
      { pc := pcBase + 8
        regs := Function.update s2.regs src (s2.regs src + 1) }
      with hs3_def
    have hs3_pc : s3.pc = pcBase + 8 := rfl
    set s4 : URMState P :=
      { pc := pcBase + 5
        regs := Function.update
          (Function.update s.regs tmp (s.regs tmp - 1))
          src ((Function.update s.regs tmp (s.regs tmp - 1)) src + 1) }
      with hs4_def
    have h_one : URMState.runFor P s 1 = s1 := by
      rw [show (1 : ℕ) = 0 + 1 from rfl, URMState.runFor_succ,
        URMState.runFor_zero,
        URMState.step_of_getElem?_jumpZ P s (pcBase + 5) tmp
          (pcBase + 9) (pcBase + 6) h_pc H.h5]
      simp only [h_tmp_ne, ↓reduceIte]
      rfl
    have h_two : URMState.runFor P s 2 = s2 := by
      rw [show (2 : ℕ) = 1 + 1 from rfl, URMState.runFor_add, h_one]
      rw [show (1 : ℕ) = 0 + 1 from rfl, URMState.runFor_succ,
        URMState.runFor_zero,
        URMState.step_of_getElem?_dec P s1 (pcBase + 6) tmp hs1_pc H.h6]
    have h_three : URMState.runFor P s 3 = s3 := by
      rw [show (3 : ℕ) = 2 + 1 from rfl, URMState.runFor_add, h_two]
      rw [show (1 : ℕ) = 0 + 1 from rfl, URMState.runFor_succ,
        URMState.runFor_zero,
        URMState.step_of_getElem?_inc P s2 (pcBase + 7) src hs2_pc H.h7]
    have h_four : URMState.runFor P s 4 = s4 := by
      rw [show (4 : ℕ) = 3 + 1 from rfl, URMState.runFor_add, h_three]
      rw [show (1 : ℕ) = 0 + 1 from rfl, URMState.runFor_succ,
        URMState.runFor_zero,
        URMState.step_of_getElem?_jumpZ P s3 (pcBase + 8) zReg
          (pcBase + 5) (pcBase + 5) hs3_pc H.h8]
      have hs3_z : s3.regs zReg = 0 := by
        change Function.update s2.regs src _ zReg = 0
        rw [Function.update_of_ne h_disj_zs]
        change Function.update s1.regs tmp _ zReg = 0
        rw [Function.update_of_ne h_disj_zt]
        exact h_z
      simp only [hs3_z, ↓reduceIte]
      rfl
    by_cases hk : k ≤ 4
    · match k, hk with
      | 0, _ => rw [URMState.runFor_zero, h_pc]; omega
      | 1, _ => rw [h_one]; change pcBase + 6 ≤ pcBase + 8; omega
      | 2, _ => rw [h_two]; change pcBase + 7 ≤ pcBase + 8; omega
      | 3, _ => rw [h_three]
      | 4, _ => rw [h_four]; change pcBase + 5 ≤ pcBase + 8; omega
    · push_neg at hk
      obtain ⟨k', rfl⟩ : ∃ k', k = 4 + k' := ⟨k - 4, by omega⟩
      have h_k' : k' ≤ 4 * m := by omega
      rw [URMState.runFor_add, h_four]
      have hs4_pc : s4.pc = pcBase + 5 := rfl
      have hs4_z : s4.regs zReg = 0 := by
        change Function.update (Function.update s.regs tmp
          (s.regs tmp - 1)) src _ zReg = 0
        rw [Function.update_of_ne h_disj_zs]
        rw [Function.update_of_ne h_disj_zt]
        exact h_z
      have hs4_tmp : s4.regs tmp = m := by
        change Function.update (Function.update s.regs tmp
          (s.regs tmp - 1)) src _ tmp = m
        rw [Function.update_of_ne h_disj_st.symm]
        rw [Function.update_self]
        omega
      exact ih s4 hs4_pc hs4_z hs4_tmp k' h_k'

/-- Strict per-step PC bound for `preservingTransfer_correct`:
for `k < 9 * n + 2` (i.e., strictly before the block completes),
the intermediate PC is at most `pcBase + 8` (strictly less than
the final PC `pcBase + 9`). -/
theorem preservingTransfer_correct_pc_strict_bound {a : ℕ}
    (P : URMProgram a) (pcBase : ℕ)
    (src dst tmp zReg : Fin P.numRegs)
    (h_disj_sd : src ≠ dst) (h_disj_st : src ≠ tmp)
    (h_disj_dt : dst ≠ tmp) (h_disj_zs : zReg ≠ src)
    (h_disj_zd : zReg ≠ dst) (h_disj_zt : zReg ≠ tmp)
    (H : preservingTransferInstrs P pcBase src dst tmp zReg)
    (s : URMState P) (h_pc : s.pc = pcBase)
    (h_z : s.regs zReg = 0) (h_tmp0 : s.regs tmp = 0)
    (n : ℕ) (h_src : s.regs src = n)
    (k : ℕ) (h_k : k < 9 * n + 2) :
    (URMState.runFor P s k).pc ≤ pcBase + 8 := by
  -- Split into loop 1 (`5n + 1` steps, PC ≤ pcBase + 5) and
  -- loop 2 (`4n + 1` steps, of which the final step transitions
  -- to pcBase + 9).
  by_cases hk1 : k ≤ 5 * n + 1
  · have h_l1 := preservingTransfer_loop1_pc_bound P pcBase src dst
      tmp zReg h_disj_sd h_disj_st h_disj_zs h_disj_zd h_disj_zt
      H s h_pc h_z n h_src k hk1
    omega
  · push_neg at hk1
    obtain ⟨k', rfl⟩ : ∃ k', k = (5 * n + 1) + k' :=
      ⟨k - (5 * n + 1), by omega⟩
    have h_k' : k' ≤ 4 * n := by omega
    rw [URMState.runFor_add]
    obtain ⟨l1_pc, _l1_src, _l1_dst, l1_tmp, l1_z, _l1_oth⟩ :=
      preservingTransfer_loop1 P pcBase src dst tmp zReg
        h_disj_sd h_disj_st h_disj_dt h_disj_zs h_disj_zd h_disj_zt
        H s h_pc h_z n h_src
    set s1 : URMState P := URMState.runFor P s (5 * n + 1)
    have hs1_pc : s1.pc = pcBase + 5 := l1_pc
    have hs1_z : s1.regs zReg = 0 := l1_z
    have hs1_tmp : s1.regs tmp = n := by rw [l1_tmp, h_tmp0]; omega
    exact preservingTransfer_loop2_pc_strict_bound P pcBase src dst
      tmp zReg h_disj_st h_disj_zs h_disj_zt H s1 hs1_pc hs1_z n
      hs1_tmp k' h_k'

/-- Strict per-step PC bound for `subInnerLoop_correct`: for
`k ≤ 4 * n` (i.e., strictly before the final exit step), the
intermediate PC is at most `pcBase + 3`. -/
theorem subInnerLoop_correct_pc_strict_bound {a : ℕ}
    (P : URMProgram a) (pcBase : ℕ)
    (src dst zReg : Fin P.numRegs)
    (h_disj_sd : src ≠ dst) (h_disj_zs : zReg ≠ src)
    (h_disj_zd : zReg ≠ dst)
    (H : subInnerLoopInstrs P pcBase src dst zReg)
    (s : URMState P) (h_pc : s.pc = pcBase)
    (h_z : s.regs zReg = 0)
    (n : ℕ) (h_src : s.regs src = n)
    (k : ℕ) (h_k : k ≤ 4 * n) :
    (URMState.runFor P s k).pc ≤ pcBase + 3 := by
  induction n generalizing s k with
  | zero =>
    match k, h_k with
    | 0, _ => rw [URMState.runFor_zero, h_pc]; omega
  | succ n ih =>
    have h_src_ne : s.regs src ≠ 0 := by rw [h_src]; omega
    set s1 : URMState P :=
      { pc := pcBase + 1, regs := s.regs } with hs1_def
    have hs1_pc : s1.pc = pcBase + 1 := rfl
    set s2 : URMState P :=
      { pc := pcBase + 2
        regs := Function.update s1.regs src (s1.regs src - 1) }
      with hs2_def
    have hs2_pc : s2.pc = pcBase + 2 := rfl
    set s3 : URMState P :=
      { pc := pcBase + 3
        regs := Function.update s2.regs dst (s2.regs dst - 1) }
      with hs3_def
    have hs3_pc : s3.pc = pcBase + 3 := rfl
    set s4 : URMState P :=
      { pc := pcBase
        regs := Function.update
          (Function.update s.regs src (s.regs src - 1))
          dst ((Function.update s.regs src (s.regs src - 1)) dst - 1) }
      with hs4_def
    have h_one : URMState.runFor P s 1 = s1 := by
      rw [show (1 : ℕ) = 0 + 1 from rfl, URMState.runFor_succ,
        URMState.runFor_zero,
        URMState.step_of_getElem?_jumpZ P s pcBase src
          (pcBase + 4) (pcBase + 1) h_pc H.h0]
      simp only [h_src_ne, ↓reduceIte]
      rfl
    have h_two : URMState.runFor P s 2 = s2 := by
      rw [show (2 : ℕ) = 1 + 1 from rfl, URMState.runFor_add, h_one]
      rw [show (1 : ℕ) = 0 + 1 from rfl, URMState.runFor_succ,
        URMState.runFor_zero,
        URMState.step_of_getElem?_dec P s1 (pcBase + 1) src hs1_pc H.h1]
    have h_three : URMState.runFor P s 3 = s3 := by
      rw [show (3 : ℕ) = 2 + 1 from rfl, URMState.runFor_add, h_two]
      rw [show (1 : ℕ) = 0 + 1 from rfl, URMState.runFor_succ,
        URMState.runFor_zero,
        URMState.step_of_getElem?_dec P s2 (pcBase + 2) dst hs2_pc H.h2]
    have h_four : URMState.runFor P s 4 = s4 := by
      rw [show (4 : ℕ) = 3 + 1 from rfl, URMState.runFor_add, h_three]
      rw [show (1 : ℕ) = 0 + 1 from rfl, URMState.runFor_succ,
        URMState.runFor_zero,
        URMState.step_of_getElem?_jumpZ P s3 (pcBase + 3) zReg
          pcBase pcBase hs3_pc H.h3]
      have hs3_z : s3.regs zReg = 0 := by
        change Function.update s2.regs dst _ zReg = 0
        rw [Function.update_of_ne h_disj_zd]
        change Function.update s1.regs src _ zReg = 0
        rw [Function.update_of_ne h_disj_zs]
        exact h_z
      simp only [hs3_z, ↓reduceIte]
      rfl
    by_cases hk : k ≤ 4
    · match k, hk with
      | 0, _ => rw [URMState.runFor_zero, h_pc]; omega
      | 1, _ => rw [h_one]; change pcBase + 1 ≤ pcBase + 3; omega
      | 2, _ => rw [h_two]; change pcBase + 2 ≤ pcBase + 3; omega
      | 3, _ => rw [h_three]
      | 4, _ => rw [h_four]; change pcBase ≤ pcBase + 3; omega
    · push_neg at hk
      obtain ⟨k', rfl⟩ : ∃ k', k = 4 + k' := ⟨k - 4, by omega⟩
      have h_k' : k' ≤ 4 * n := by omega
      rw [URMState.runFor_add, h_four]
      have hs4_pc : s4.pc = pcBase := rfl
      have hs4_z : s4.regs zReg = 0 := by
        change Function.update (Function.update s.regs src
          (s.regs src - 1)) dst _ zReg = 0
        rw [Function.update_of_ne h_disj_zd]
        rw [Function.update_of_ne h_disj_zs]
        exact h_z
      have hs4_src : s4.regs src = n := by
        change Function.update (Function.update s.regs src
          (s.regs src - 1)) dst _ src = n
        rw [Function.update_of_ne h_disj_sd]
        rw [Function.update_self]
        omega
      exact ih s4 hs4_pc hs4_z hs4_src k' h_k'

/-- Combined per-step PC bound for `preservingTransfer_correct`:
during the `9 * n + 2` steps of the block, the intermediate PC
stays within `[pcBase, pcBase + 9]`. Composed from
`preservingTransfer_loop1_pc_bound` and
`preservingTransfer_loop2_pc_bound`. -/
theorem preservingTransfer_correct_pc_bound {a : ℕ}
    (P : URMProgram a) (pcBase : ℕ)
    (src dst tmp zReg : Fin P.numRegs)
    (h_disj_sd : src ≠ dst) (h_disj_st : src ≠ tmp)
    (h_disj_dt : dst ≠ tmp) (h_disj_zs : zReg ≠ src)
    (h_disj_zd : zReg ≠ dst) (h_disj_zt : zReg ≠ tmp)
    (H : preservingTransferInstrs P pcBase src dst tmp zReg)
    (s : URMState P) (h_pc : s.pc = pcBase)
    (h_z : s.regs zReg = 0) (h_tmp0 : s.regs tmp = 0)
    (n : ℕ) (h_src : s.regs src = n)
    (k : ℕ) (h_k : k ≤ 9 * n + 2) :
    (URMState.runFor P s k).pc ≤ pcBase + 9 := by
  -- Split into loop 1 (`5n + 1` steps) and loop 2 (`4n + 1`
  -- steps).  PCs in loop 1 are ≤ pcBase + 5 ≤ pcBase + 9; PCs
  -- in loop 2 are ≤ pcBase + 9.
  by_cases hk1 : k ≤ 5 * n + 1
  · -- k still inside loop 1.
    have h_l1 := preservingTransfer_loop1_pc_bound P pcBase src dst
      tmp zReg h_disj_sd h_disj_st h_disj_zs h_disj_zd h_disj_zt
      H s h_pc h_z n h_src k hk1
    omega
  · -- k beyond loop 1: split as (5n+1) + k'.
    push_neg at hk1
    obtain ⟨k', rfl⟩ : ∃ k', k = (5 * n + 1) + k' :=
      ⟨k - (5 * n + 1), by omega⟩
    have h_k' : k' ≤ 4 * n + 1 := by omega
    rw [URMState.runFor_add]
    -- After loop 1, state at PC = pcBase + 5, V_tmp = n,
    -- V_zReg = 0.
    obtain ⟨l1_pc, _l1_src, _l1_dst, l1_tmp, l1_z, _l1_oth⟩ :=
      preservingTransfer_loop1 P pcBase src dst tmp zReg
        h_disj_sd h_disj_st h_disj_dt h_disj_zs h_disj_zd h_disj_zt
        H s h_pc h_z n h_src
    set s1 : URMState P := URMState.runFor P s (5 * n + 1)
    have hs1_pc : s1.pc = pcBase + 5 := l1_pc
    have hs1_z : s1.regs zReg = 0 := l1_z
    have hs1_tmp : s1.regs tmp = n := by rw [l1_tmp, h_tmp0]; omega
    have h_l2 := preservingTransfer_loop2_pc_bound P pcBase src dst
      tmp zReg h_disj_st h_disj_zs h_disj_zt H s1 hs1_pc hs1_z n
      hs1_tmp k' h_k'
    exact h_l2.2


end LawvereERKSim
end GebLean
