import GebLean.Utilities.NatERStyle
import GebLean.Utilities.ERArith
import GebLean.Utilities.ERTreeArith

/-!
# Soundness of `Nat.foldBTLOnCodeERStyle` and
# `Nat.boundedRecERStyle` against ER

Proves that the Nat-level ER-style helpers produce the same
output as the corresponding ER combinators' interp on every
input.  These theorems are what makes Option E's bounded NatBT
theory equivalent to `LawvereERCat` on the nose.
-/

namespace GebLean

/-- The Nat-level fold-predicate at index `j` evaluates to
`true` exactly when the corresponding trace condition (the body
of `ERMor1.foldBTLPred_eq_one_iff_trace`) holds. -/
theorem Nat.foldBTLPredAtIndex_eq_true_iff
    (baseLeaf : ℕ → ℕ) (stepNode : ℕ → ℕ → ℕ)
    (cand : ℕ) (j : ℕ) :
    Nat.foldBTLPredAtIndex baseLeaf stepNode cand j = true ↔
      cand.unpair.1 % (1 + (j + 1) * cand.unpair.2) =
        (if j % 2 = 1 then
          stepNode
            (cand.unpair.1 %
              (1 + ((j / 2).unpair.1 + 1) * cand.unpair.2))
            (cand.unpair.1 %
              (1 + ((j / 2).unpair.2 + 1) * cand.unpair.2))
        else baseLeaf (j / 2)) := by
  unfold Nat.foldBTLPredAtIndex
  by_cases hodd : j % 2 = 1
  · simp only [hodd, if_true, decide_eq_true_eq]
  · simp only [hodd, if_false, decide_eq_true_eq]

/-- The Nat-level rec-predicate at index `j` evaluates to
`true` exactly when the corresponding trace condition holds. -/
theorem Nat.boundedRecPredAtIndex_eq_true_iff
    (base : ℕ) (step : ℕ → ℕ → ℕ)
    (cand : ℕ) (j : ℕ) :
    Nat.boundedRecPredAtIndex base step cand j = true ↔
      cand.unpair.1 % (1 + (j + 1) * cand.unpair.2) =
        (if j = 0 then base
        else step (j - 1)
          (cand.unpair.1 % (1 + j * cand.unpair.2))) := by
  unfold Nat.boundedRecPredAtIndex
  by_cases hjz : j = 0
  · simp only [hjz, if_true, decide_eq_true_eq]
  · simp only [hjz, if_false, decide_eq_true_eq]

/-- ER's fold predicate at value `1` matches the Nat-level
`decide (∀ j < code + 1, foldBTLPredAtIndex ... = true) = true`
on the same candidate. -/
theorem ERMor1.foldBTLPred_interp_eq_one_iff_natDecide
    {k : ℕ}
    (baseLeaf : ERMor1 (k + 1)) (stepNode : ERMor1 (k + 2))
    (cand code : ℕ) (ctx_param : Fin k → ℕ) :
    (ERMor1.foldBTLPred baseLeaf stepNode).interp
        (Fin.cons cand (Fin.cons code ctx_param)) = 1 ↔
      (∀ j, j < code + 1 →
        Nat.foldBTLPredAtIndex
          (fun lbl => baseLeaf.interp (Fin.cons lbl ctx_param))
          (fun l r => stepNode.interp
            (Fin.cons l (Fin.cons r ctx_param)))
          cand j = true) := by
  rw [ERMor1.foldBTLPred_eq_one_iff_trace]
  constructor
  · intro h j hj
    rw [Nat.foldBTLPredAtIndex_eq_true_iff]
    exact h j hj
  · intro h j hj
    have := h j hj
    rw [Nat.foldBTLPredAtIndex_eq_true_iff] at this
    exact this

/-- ER's rec predicate at value `1` matches the Nat-level
`decide (∀ j ≤ n, boundedRecPredAtIndex ... = true) = true`
on the same candidate. -/
theorem ERMor1.boundedRecPred_interp_eq_one_iff_natDecide
    {k : ℕ}
    (base : ERMor1 k) (step : ERMor1 (k + 2))
    (cand n : ℕ) (ctx_param : Fin k → ℕ) :
    (ERMor1.boundedRecPred base step).interp
        (Fin.cons cand (Fin.cons n ctx_param)) = 1 ↔
      (∀ j, j ≤ n →
        Nat.boundedRecPredAtIndex
          (base.interp ctx_param)
          (fun i prev => step.interp
            (Fin.cons i (Fin.cons prev ctx_param)))
          cand j = true) := by
  rw [ERMor1.boundedRecPred_eq_one_iff_trace]
  constructor
  · rintro ⟨hbase, hstep⟩ j hj
    rw [Nat.boundedRecPredAtIndex_eq_true_iff]
    by_cases hjz : j = 0
    · subst hjz
      simp only [if_true]
      have hrew : 1 + (0 + 1) * cand.unpair.2 =
          1 + 1 * cand.unpair.2 := by ring
      rw [hrew]
      exact hbase
    · simp only [hjz, if_false]
      have hjpos : 0 < j := Nat.pos_of_ne_zero hjz
      obtain ⟨m, hm⟩ : ∃ m, j = m + 1 :=
        ⟨j - 1, by omega⟩
      subst hm
      have hm_lt : m < n := by omega
      have hm_step := hstep m hm_lt
      have hrew_idx : (m + 1 : ℕ) - 1 = m := by omega
      have hrew_mul : (1 + (m + 1) * cand.unpair.2 : ℕ) =
          1 + (m + 1) * cand.unpair.2 := rfl
      rw [hrew_idx, hrew_mul]
      exact hm_step
  · intro h
    refine ⟨?_, ?_⟩
    · have h0 := h 0 (Nat.zero_le _)
      rw [Nat.boundedRecPredAtIndex_eq_true_iff] at h0
      simp only [if_true] at h0
      have hrew : 1 + 1 * cand.unpair.2 =
          1 + (0 + 1) * cand.unpair.2 := by ring
      rw [hrew]
      exact h0
    · intro j hj
      have hjs_le : j + 1 ≤ n := hj
      have hj1 := h (j + 1) hjs_le
      rw [Nat.boundedRecPredAtIndex_eq_true_iff] at hj1
      have hjs_ne : (j + 1 : ℕ) ≠ 0 := Nat.succ_ne_zero _
      simp only [hjs_ne, if_false] at hj1
      have hrew_idx : (j + 1 : ℕ) - 1 = j := by omega
      rw [hrew_idx] at hj1
      exact hj1

/-- If two predicates agree pointwise (`Bool` vs `0/1`-valued
`ℕ`), the Nat-level bounded search and the ER-level bounded
search return the same value at the same range. -/
theorem Nat.boundedSearchAt_eq_ERboundedSearch
    {k : ℕ}
    (boundN : ℕ) (predBool : ℕ → Bool)
    (boundER : ERMor1 k) (predER : ERMor1 (k + 1))
    (ctx : Fin k → ℕ)
    (hbound : boundER.interp ctx = boundN)
    (hpred_le : ∀ j, predER.interp (Fin.cons j ctx) ≤ 1)
    (hpred_eq : ∀ j,
      predBool j = true ↔
        predER.interp (Fin.cons j ctx) = 1) :
    Nat.boundedSearchAt boundN predBool =
      (ERMor1.boundedSearch boundER predER).interp ctx := by
  rw [ERMor1.interp_boundedSearch _ _ _ hpred_le, hbound]
  unfold Nat.boundedSearchAt
  by_cases hex : ∃ j, j < boundN ∧ predBool j = true
  · have hex' : ∃ j, j < boundN ∧
        predER.interp (Fin.cons j ctx) = 1 := by
      obtain ⟨j, hj, hpj⟩ := hex
      exact ⟨j, hj, (hpred_eq j).mp hpj⟩
    rw [dif_pos hex, dif_pos hex']
    apply Nat.find_eq_iff _ |>.mpr
    refine ⟨?_, ?_⟩
    · obtain ⟨hjlt, hjER⟩ := Nat.find_spec hex'
      refine ⟨hjlt, ?_⟩
      exact (hpred_eq _).mpr hjER
    · intro m hm hmconj
      obtain ⟨hmlt, hmBool⟩ := hmconj
      have hmER : predER.interp (Fin.cons m ctx) = 1 :=
        (hpred_eq m).mp hmBool
      exact Nat.find_min hex' hm ⟨hmlt, hmER⟩
  · have hex' : ¬ ∃ j, j < boundN ∧
        predER.interp (Fin.cons j ctx) = 1 := by
      rintro ⟨j, hj, hjER⟩
      exact hex ⟨j, hj, (hpred_eq j).mpr hjER⟩
    rw [dif_neg hex, dif_neg hex']

/-- Soundness of `Nat.foldBTLOnCodeERStyle`: it produces the
same output as `ERMor1.foldBTLOnCode`'s interp on every input,
including the off-conditions case where the witness search
returns the sentinel `range + 1`. -/
theorem ERMor1.interp_foldBTLOnCode_eq_natFoldBTLOnCodeERStyle
    {k : ℕ}
    (baseLeaf : ERMor1 (k + 1)) (stepNode : ERMor1 (k + 2))
    (bound : ERMor1 (k + 1)) (ctx : Fin (k + 1) → ℕ) :
    (ERMor1.foldBTLOnCode baseLeaf stepNode bound).interp ctx
      = Nat.foldBTLOnCodeERStyle
        (fun lbl => baseLeaf.interp (Fin.cons lbl (Fin.tail ctx)))
        (fun l r => stepNode.interp
          (Fin.cons l (Fin.cons r (Fin.tail ctx))))
        (fun j => bound.interp (Fin.cons j (Fin.tail ctx)))
        (ctx 0) := by
  set code : ℕ := ctx 0 with hcode_def
  set ctx_param : Fin k → ℕ := Fin.tail ctx with hctx_param_def
  have hctx_eq : ctx = Fin.cons code ctx_param :=
    (Fin.cons_self_tail ctx).symm
  set boundN : ℕ := bound.interp (Fin.cons code ctx_param)
    with hboundN_def
  set baseLeafFn : ℕ → ℕ := fun lbl =>
    baseLeaf.interp (Fin.cons lbl ctx_param) with _
  set stepNodeFn : ℕ → ℕ → ℕ := fun l r =>
    stepNode.interp (Fin.cons l (Fin.cons r ctx_param))
    with _
  set boundFn : ℕ → ℕ := fun j =>
    bound.interp (Fin.cons j ctx_param) with _
  rw [hctx_eq]
  unfold Nat.foldBTLOnCodeERStyle
  unfold ERMor1.foldBTLOnCode
  rw [ERMor1.interp_comp, ERMor1.interp_minN]
  set predBool : ℕ → Bool := fun c =>
    decide (∀ j, j < code + 1 →
      Nat.foldBTLPredAtIndex baseLeafFn stepNodeFn c j = true)
    with hpredBool_def
  set rangeN : ℕ := Nat.boundedRecRangeAt (boundFn code) code
    with hrangeN_def
  set predER : ERMor1 (k + 2) :=
    ERMor1.foldBTLPred baseLeaf stepNode with hpredER_def
  set rangeER : ERMor1 (k + 1) :=
    ERMor1.boundedRecRange bound with hrangeER_def
  set search : ERMor1 (k + 1) :=
    ERMor1.boundedSearch rangeER predER with hsearch_def
  have hbound_eq :
      rangeER.interp (Fin.cons code ctx_param) = rangeN := by
    rw [hrangeER_def, ERMor1.interp_boundedRecRange]
    have hc0 :
        (Fin.cons code ctx_param : Fin (k + 1) → ℕ) 0 = code :=
      rfl
    rw [hc0]
    rfl
  have hpred_le :
      ∀ j, predER.interp
        (Fin.cons j (Fin.cons code ctx_param)) ≤ 1 := by
    intro j
    rw [hpredER_def]
    exact ERMor1.foldBTLPred_le_one baseLeaf stepNode _
  have hpred_eq :
      ∀ j, predBool j = true ↔
        predER.interp
          (Fin.cons j (Fin.cons code ctx_param)) = 1 := by
    intro j
    rw [hpredBool_def, hpredER_def]
    rw [ERMor1.foldBTLPred_interp_eq_one_iff_natDecide
      baseLeaf stepNode j code ctx_param]
    simp only [decide_eq_true_eq]
    rfl
  have hsearch_eq :
      Nat.boundedSearchAt rangeN predBool =
        search.interp (Fin.cons code ctx_param) := by
    rw [hsearch_def]
    exact Nat.boundedSearchAt_eq_ERboundedSearch _ _ _ _ _
      hbound_eq hpred_le hpred_eq
  set candN : ℕ := Nat.boundedSearchAt rangeN predBool
    with hcandN_def
  have hbeta_eval :
      (ERMor1.comp ERMor1.beta
        (fun (i : Fin 3) => match i with
          | ⟨0, _⟩ =>
              ERMor1.comp ERMor1.natUnpairFst
                (fun (_ : Fin 1) => search)
          | ⟨1, _⟩ =>
              ERMor1.comp ERMor1.natUnpairSnd
                (fun (_ : Fin 1) => search)
          | ⟨2, _⟩ =>
              ERMor1.proj 0)).interp
        (Fin.cons code ctx_param) =
      candN.unpair.1 % (1 + (code + 1) * candN.unpair.2) := by
    rw [ERMor1.interp_comp]
    have harg :
        (fun (i : Fin 3) =>
          ((match i with
            | ⟨0, _⟩ =>
                ERMor1.comp ERMor1.natUnpairFst
                  (fun (_ : Fin 1) => search)
            | ⟨1, _⟩ =>
                ERMor1.comp ERMor1.natUnpairSnd
                  (fun (_ : Fin 1) => search)
            | ⟨2, _⟩ =>
                ERMor1.proj 0 : ERMor1 (k + 1))).interp
            (Fin.cons code ctx_param)) =
        ![candN.unpair.1, candN.unpair.2, code] := by
      funext i
      match i with
      | ⟨0, _⟩ =>
        change ERMor1.natUnpairFst.interp
            (fun (_ : Fin 1) =>
              search.interp (Fin.cons code ctx_param)) = _
        rw [← hsearch_eq]
        have hfun :
            (fun (_ : Fin 1) => candN) = ![candN] := by
          funext j
          match j with
          | ⟨0, _⟩ => rfl
        rw [hfun, ERMor1.interp_natUnpairFst]
        rfl
      | ⟨1, _⟩ =>
        change ERMor1.natUnpairSnd.interp
            (fun (_ : Fin 1) =>
              search.interp (Fin.cons code ctx_param)) = _
        rw [← hsearch_eq]
        have hfun :
            (fun (_ : Fin 1) => candN) = ![candN] := by
          funext j
          match j with
          | ⟨0, _⟩ => rfl
        rw [hfun, ERMor1.interp_natUnpairSnd]
        rfl
      | ⟨2, _⟩ =>
        change (Fin.cons code ctx_param :
            Fin (k + 1) → ℕ) 0 = _
        rfl
    rw [harg, ERMor1.interp_beta]
  have hbound_RHS :
      bound.interp (Fin.cons code ctx_param) = boundFn code :=
    rfl
  change min
      ((ERMor1.comp ERMor1.beta
        (fun (i : Fin 3) => match i with
          | ⟨0, _⟩ =>
              ERMor1.comp ERMor1.natUnpairFst
                (fun (_ : Fin 1) => search)
          | ⟨1, _⟩ =>
              ERMor1.comp ERMor1.natUnpairSnd
                (fun (_ : Fin 1) => search)
          | ⟨2, _⟩ =>
              ERMor1.proj 0)).interp
        (Fin.cons code ctx_param))
      (bound.interp (Fin.cons code ctx_param)) = _
  rw [hbeta_eval, hbound_RHS]

/-- Soundness of `Nat.boundedRecERStyle`: it produces the same
output as `ERMor1.boundedRec`'s interp on every input,
including the off-conditions case where the witness search
returns the sentinel `range + 1`. -/
theorem ERMor1.interp_boundedRec_eq_natBoundedRecERStyle
    {k : ℕ}
    (base : ERMor1 k) (step : ERMor1 (k + 2))
    (bound : ERMor1 (k + 1))
    (ctx : Fin (k + 1) → ℕ) :
    (ERMor1.boundedRec base step bound).interp ctx
      = Nat.boundedRecERStyle
        (base.interp (Fin.tail ctx))
        (fun j prev => step.interp
          (Fin.cons j (Fin.cons prev (Fin.tail ctx))))
        (fun j => bound.interp (Fin.cons j (Fin.tail ctx)))
        (ctx 0) := by
  set n : ℕ := ctx 0 with hn_def
  set ctx_param : Fin k → ℕ := Fin.tail ctx with hctx_param_def
  have hctx_eq : ctx = Fin.cons n ctx_param :=
    (Fin.cons_self_tail ctx).symm
  set boundN : ℕ := bound.interp (Fin.cons n ctx_param)
    with hboundN_def
  set baseVal : ℕ := base.interp ctx_param with _
  set stepFn : ℕ → ℕ → ℕ := fun j prev => step.interp
    (Fin.cons j (Fin.cons prev ctx_param)) with _
  set boundFn : ℕ → ℕ := fun j =>
    bound.interp (Fin.cons j ctx_param) with _
  rw [hctx_eq]
  unfold Nat.boundedRecERStyle
  unfold ERMor1.boundedRec
  rw [ERMor1.interp_comp, ERMor1.interp_minN]
  set predBool : ℕ → Bool := fun c =>
    decide (∀ j, j ≤ n →
      Nat.boundedRecPredAtIndex baseVal stepFn c j = true)
    with hpredBool_def
  set rangeN : ℕ := Nat.boundedRecRangeAt (boundFn n) n
    with _
  set predER : ERMor1 (k + 2) :=
    ERMor1.boundedRecPred base step with hpredER_def
  set rangeER : ERMor1 (k + 1) :=
    ERMor1.boundedRecRange bound with hrangeER_def
  set search : ERMor1 (k + 1) :=
    ERMor1.boundedSearch rangeER predER with hsearch_def
  have hbound_eq :
      rangeER.interp (Fin.cons n ctx_param) = rangeN := by
    rw [hrangeER_def, ERMor1.interp_boundedRecRange]
    have hc0 :
        (Fin.cons n ctx_param : Fin (k + 1) → ℕ) 0 = n :=
      rfl
    rw [hc0]
    rfl
  have hpred_le :
      ∀ j, predER.interp
        (Fin.cons j (Fin.cons n ctx_param)) ≤ 1 := by
    intro j
    rw [hpredER_def]
    exact ERMor1.boundedRecPred_le_one base step _
  have hpred_eq :
      ∀ j, predBool j = true ↔
        predER.interp
          (Fin.cons j (Fin.cons n ctx_param)) = 1 := by
    intro j
    rw [hpredBool_def, hpredER_def]
    rw [ERMor1.boundedRecPred_interp_eq_one_iff_natDecide
      base step j n ctx_param]
    simp only [decide_eq_true_eq]
    rfl
  have hsearch_eq :
      Nat.boundedSearchAt rangeN predBool =
        search.interp (Fin.cons n ctx_param) := by
    rw [hsearch_def]
    exact Nat.boundedSearchAt_eq_ERboundedSearch _ _ _ _ _
      hbound_eq hpred_le hpred_eq
  set candN : ℕ := Nat.boundedSearchAt rangeN predBool with _
  have hbeta_eval :
      (ERMor1.comp ERMor1.beta
        (fun (i : Fin 3) => match i with
          | ⟨0, _⟩ =>
              ERMor1.comp ERMor1.natUnpairFst
                (fun (_ : Fin 1) => search)
          | ⟨1, _⟩ =>
              ERMor1.comp ERMor1.natUnpairSnd
                (fun (_ : Fin 1) => search)
          | ⟨2, _⟩ =>
              ERMor1.proj 0)).interp
        (Fin.cons n ctx_param) =
      candN.unpair.1 % (1 + (n + 1) * candN.unpair.2) := by
    rw [ERMor1.interp_comp]
    have harg :
        (fun (i : Fin 3) =>
          ((match i with
            | ⟨0, _⟩ =>
                ERMor1.comp ERMor1.natUnpairFst
                  (fun (_ : Fin 1) => search)
            | ⟨1, _⟩ =>
                ERMor1.comp ERMor1.natUnpairSnd
                  (fun (_ : Fin 1) => search)
            | ⟨2, _⟩ =>
                ERMor1.proj 0 : ERMor1 (k + 1))).interp
            (Fin.cons n ctx_param)) =
        ![candN.unpair.1, candN.unpair.2, n] := by
      funext i
      match i with
      | ⟨0, _⟩ =>
        change ERMor1.natUnpairFst.interp
            (fun (_ : Fin 1) =>
              search.interp (Fin.cons n ctx_param)) = _
        rw [← hsearch_eq]
        have hfun :
            (fun (_ : Fin 1) => candN) = ![candN] := by
          funext j
          match j with
          | ⟨0, _⟩ => rfl
        rw [hfun, ERMor1.interp_natUnpairFst]
        rfl
      | ⟨1, _⟩ =>
        change ERMor1.natUnpairSnd.interp
            (fun (_ : Fin 1) =>
              search.interp (Fin.cons n ctx_param)) = _
        rw [← hsearch_eq]
        have hfun :
            (fun (_ : Fin 1) => candN) = ![candN] := by
          funext j
          match j with
          | ⟨0, _⟩ => rfl
        rw [hfun, ERMor1.interp_natUnpairSnd]
        rfl
      | ⟨2, _⟩ =>
        change (Fin.cons n ctx_param :
            Fin (k + 1) → ℕ) 0 = _
        rfl
    rw [harg, ERMor1.interp_beta]
  have hbound_RHS :
      bound.interp (Fin.cons n ctx_param) = boundFn n :=
    rfl
  change min
      ((ERMor1.comp ERMor1.beta
        (fun (i : Fin 3) => match i with
          | ⟨0, _⟩ =>
              ERMor1.comp ERMor1.natUnpairFst
                (fun (_ : Fin 1) => search)
          | ⟨1, _⟩ =>
              ERMor1.comp ERMor1.natUnpairSnd
                (fun (_ : Fin 1) => search)
          | ⟨2, _⟩ =>
              ERMor1.proj 0)).interp
        (Fin.cons n ctx_param))
      (bound.interp (Fin.cons n ctx_param)) = _
  rw [hbeta_eval, hbound_RHS]

end GebLean

