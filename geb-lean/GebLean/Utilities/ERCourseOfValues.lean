import GebLean.Utilities.ERTreeArith

/-!
# ER Course-of-Values Table Search

`ERMor1.cvRec` realizes a generic one-dimensional course-of-values recursion
as a single elementary-recursive bounded search: a Gödel β-encoded value
table is sought below the `ERMor1.boundedRecRange` envelope, a candidate is
accepted when its β-read at every position `j ≤ code` matches a
client-supplied node morphism evaluated at that position, and the accepted
table's value at the input position is extracted, clamped by the client's
value bound.

`ERMor1.cvRecGated` is the gated variant: the checked range is
`[0, idxBound]` for a client index bound, each position's check is enabled
by a client gate morphism `sane` (ungated positions contribute `1` to the
bounded product), and extraction β-reads at a client extraction position
`extractAt`, clamped by the value bound.

## Main definitions

- `ERMor1.cvRecBody`: per-position check comparing the β-read `β(cand, j)`
  against the node value at `j`.
- `ERMor1.cvRecPred`: the search predicate, a bounded product of body checks
  over positions `j < code + 1`.
- `ERMor1.cvRec`: the combinator — bounded search for a β-witness, β-extraction
  at the input position, `min`-clamp by the value bound.
- `ERMor1.cvRecGatedBody`: per-position check of the gated variant — the
  `cvRecBody` check where the gate reads `1`, the constant `1` elsewhere.
- `ERMor1.cvRecGatedPred`: the gated search predicate, a bounded product of
  gated body checks over positions `j < idxBound + 1`.
- `ERMor1.cvRecGatedRange`: the gated search envelope — `boundedRecRange`
  evaluated with the index bound in the counter slot.
- `ERMor1.cvRecGated`: the gated combinator — bounded search for a β-witness,
  β-extraction at the extraction position, `min`-clamp by the value bound.

## Main statements

- `ERMor1.interp_cvRec_le_bound`: the output is unconditionally dominated by
  the value bound.
- `ERMor1.cvRecPred_trace_match`: determinacy — under the node-faithfulness
  hypothesis, any accepted candidate β-reads the reference table at every
  position `j ≤ code`.
- `ERMor1.interp_cvRec_of_bounded`: conditional correctness — when the value
  bound dominates the reference table, is monotone into the input position,
  and the node is faithful to the table, the combinator computes the table
  value at the input position.
- `ERMor1.interp_cvRecGated_le_bound`: the gated output is unconditionally
  dominated by the value bound.
- `ERMor1.interp_cvRecGated_eq`: conditional correctness of the gated
  variant — under gate boundedness, table boundedness, gated
  node-faithfulness, and a client-supplied determinacy hypothesis, the
  combinator computes the table value at the extraction position.

## Implementation notes

The node morphism has arity `k + 3` at slots `(i, cand, code, params…)`: it
computes the recursion equation's right-hand side at table index `i`,
performing its own β-reads
`β(cand, p) = cand.unpair.1 % (1 + (p + 1) * cand.unpair.2)` from the
candidate at whatever child positions it computes from `i` (via
`ERMor1.beta`).  The combinator therefore fixes no recursion shape; the
per-client correctness input is the node-faithfulness hypothesis of
`ERMor1.interp_cvRec_of_bounded`: any candidate whose β-reads agree with the
reference table at all positions `p < i` makes the node compute the table
value at `i`.  Its `p < i` form yields both existence (the β-witness of
`Nat.bounded_beta_exists` agrees with the table everywhere, hence at all
`p < i`) and determinacy (strong induction on the position); it is
dischargeable exactly when every position the node reads is strictly below
its index.  `ERMor1.foldBTLOnCode` (`GebLean.Utilities.ERTreeArith`) is the
fixed-shape precedent this combinator generalizes: there the node is a fixed
even/odd dispatch reading the two β-positions `(j / 2).unpair`.

The gated variant serves recursions whose descent order is not the numeric
index order (for example two-dimensional tables keyed by `Nat.pair d m`,
where a descent may increase the index): agreement then cannot be propagated
by strong induction on the position, so `ERMor1.interp_cvRecGated_eq` takes
determinacy as the explicit client hypothesis `h_det`, discharged per
instance (typically by strong induction on a component the recursion does
decrease).  The gate `sane` (with values in `{0, 1}` on the checked range)
confines the imposed equations to positions whose reads stay inside the
checked range; its node-faithfulness hypothesis assumes agreement with the
reference table on all of `[0, idxBound]`, matching the β-witness produced
by `Nat.bounded_beta_exists` over the whole table.

## References

D. Leivant, "Ramified recurrence and computational complexity III: Higher
type recurrence and elementary complexity", Annals of Pure and Applied Logic
96 (1999) 209-229, DOI `10.1016/S0168-0072(98)00040-2`.  Footnote 10
(p. 226) delegates the arithmetization of machine models to the standard
literature; this combinator is part of the layer paying that absorption
formally.
-/

namespace GebLean

/-- Per-position body of the course-of-values predicate: an arity-`k + 3`
term at context `(j, cand, code, ctx)` evaluating to `1` iff the β-read
`β(cand, j)` equals `node.interp (j, cand, code, ctx)`. -/
def ERMor1.cvRecBody {k : ℕ} (node : ERMor1 (k + 3)) :
    ERMor1 (k + 3) :=
  ERMor1.boolEqAt (ERMor1.betaOnCandFold (ERMor1.proj 0)) node

/-- Full predicate for the course-of-values β-witness search.  At context
`Fin.cons cand (Fin.cons code ctx)`, evaluates to `1` iff every position
`j < code + 1` satisfies the body check. -/
def ERMor1.cvRecPred {k : ℕ} (node : ERMor1 (k + 3)) :
    ERMor1 (k + 2) :=
  ERMor1.comp (ERMor1.bprod (ERMor1.cvRecBody node))
    (fun (i : Fin (k + 3)) => match i with
      | ⟨0, _⟩ =>
          ERMor1.comp ERMor1.succ
            (fun (_ : Fin 1) => ERMor1.proj 1)
      | ⟨1, _⟩ => ERMor1.proj 0
      | ⟨2, _⟩ => ERMor1.proj 1
      | ⟨p + 3, h⟩ =>
          ERMor1.proj ⟨p + 2, by omega⟩)

/-- The course-of-values body evaluates in `{0, 1}`. -/
theorem ERMor1.cvRecBody_le_one {k : ℕ} (node : ERMor1 (k + 3))
    (ctx : Fin (k + 3) → ℕ) :
    (ERMor1.cvRecBody node).interp ctx ≤ 1 :=
  ERMor1.boolEqAt_le_one _ _ _

/-- The course-of-values body evaluates to `1` iff the β-read at position
`j` matches the node value at `j`. -/
theorem ERMor1.cvRecBody_eq_one_iff {k : ℕ}
    (node : ERMor1 (k + 3)) (j cand code : ℕ) (ctx : Fin k → ℕ) :
    (ERMor1.cvRecBody node).interp
        (Fin.cons j (Fin.cons cand (Fin.cons code ctx))) = 1 ↔
      cand.unpair.1 % (1 + (j + 1) * cand.unpair.2) =
        node.interp
          (Fin.cons j (Fin.cons cand (Fin.cons code ctx))) := by
  unfold ERMor1.cvRecBody
  rw [ERMor1.boolEqAt_eq_one_iff, ERMor1.interp_betaOnCandFold]
  have hproj :
      (ERMor1.proj (0 : Fin (k + 3))).interp
        (Fin.cons j (Fin.cons cand (Fin.cons code ctx))) = j := rfl
  rw [hproj]

/-- The course-of-values predicate evaluates in `{0, 1}`. -/
theorem ERMor1.cvRecPred_le_one {k : ℕ} (node : ERMor1 (k + 3))
    (ctx : Fin (k + 2) → ℕ) :
    (ERMor1.cvRecPred node).interp ctx ≤ 1 := by
  unfold ERMor1.cvRecPred
  rw [ERMor1.interp_comp, ERMor1.interp_bprod]
  exact natBProd_le_one_of_body_le_one _ _ (fun _ =>
    ERMor1.cvRecBody_le_one node _)

/-- The course-of-values predicate as a bounded product of body values over
positions `j ∈ [0, code + 1)`. -/
theorem ERMor1.interp_cvRecPred_as_bprod {k : ℕ}
    (node : ERMor1 (k + 3)) (cand code : ℕ) (ctx : Fin k → ℕ) :
    (ERMor1.cvRecPred node).interp
        (Fin.cons cand (Fin.cons code ctx)) =
      natBProd (code + 1) (fun j =>
        (ERMor1.cvRecBody node).interp
          (Fin.cons j (Fin.cons cand (Fin.cons code ctx)))) := by
  unfold ERMor1.cvRecPred
  rw [ERMor1.interp_comp]
  set argFn : Fin (k + 3) → ℕ := fun i =>
    ((fun i : Fin (k + 3) => match i with
      | ⟨0, _⟩ =>
          ERMor1.comp ERMor1.succ
            (fun (_ : Fin 1) => ERMor1.proj (k := k + 2) 1)
      | ⟨1, _⟩ => ERMor1.proj 0
      | ⟨2, _⟩ => ERMor1.proj 1
      | ⟨p + 3, h⟩ =>
          ERMor1.proj
            (⟨p + 2, by omega⟩ : Fin (k + 2))) i).interp
      (Fin.cons cand (Fin.cons code ctx))
  rw [ERMor1.interp_bprod]
  have h0 : argFn 0 = code + 1 := by
    change ((ERMor1.comp ERMor1.succ
          (fun (_ : Fin 1) =>
            ERMor1.proj (k := k + 2) 1)).interp
          (Fin.cons cand (Fin.cons code ctx))) = _
    rw [ERMor1.interp_comp, ERMor1.interp_succ]
    rfl
  have htail :
      Fin.tail argFn =
        Fin.cons cand (Fin.cons code ctx) := by
    funext ⟨p, hp⟩
    change argFn ⟨p + 1, by omega⟩ = _
    match p with
    | 0 => rfl
    | 1 => rfl
    | q + 2 => rfl
  rw [h0, htail]

/-- The course-of-values predicate equals `1` iff the β-reads match the node
values at every position `j ≤ code`. -/
theorem ERMor1.cvRecPred_eq_one_iff_trace {k : ℕ}
    (node : ERMor1 (k + 3)) (cand code : ℕ) (ctx : Fin k → ℕ) :
    (ERMor1.cvRecPred node).interp
        (Fin.cons cand (Fin.cons code ctx)) = 1 ↔
      ∀ j, j < code + 1 →
        cand.unpair.1 % (1 + (j + 1) * cand.unpair.2) =
          node.interp
            (Fin.cons j (Fin.cons cand (Fin.cons code ctx))) := by
  rw [ERMor1.interp_cvRecPred_as_bprod,
    natBProd_eq_one_iff_all_one]
  constructor
  · intro h j hj
    exact (ERMor1.cvRecBody_eq_one_iff node
      j cand code ctx).mp (h j hj)
  · intro h j hj
    exact (ERMor1.cvRecBody_eq_one_iff node
      j cand code ctx).mpr (h j hj)

/-- Generic ER course-of-values table search.  At outer arity `k + 1` with
slot `0` the code and slots `1..k` the parameter context, returns
`min (β(a, b, code)) valBound`, where `(a, b) = Nat.unpair` of the least
`cand` satisfying `cvRecPred node = 1` below
`boundedRecRange valBound`.  The outer `minN` makes the output
unconditionally bounded by `valBound`.  Correctness against a reference
table holds under the node-faithfulness hypothesis of
`ERMor1.interp_cvRec_of_bounded`. -/
def ERMor1.cvRec {k : ℕ} (node : ERMor1 (k + 3))
    (valBound : ERMor1 (k + 1)) : ERMor1 (k + 1) :=
  let search : ERMor1 (k + 1) :=
    ERMor1.boundedSearch (ERMor1.boundedRecRange valBound)
      (ERMor1.cvRecPred node)
  let betaAtCode : ERMor1 (k + 1) :=
    ERMor1.comp ERMor1.beta (fun i => match i with
      | ⟨0, _⟩ =>
          ERMor1.comp ERMor1.natUnpairFst
            (fun (_ : Fin 1) => search)
      | ⟨1, _⟩ =>
          ERMor1.comp ERMor1.natUnpairSnd
            (fun (_ : Fin 1) => search)
      | ⟨2, _⟩ => ERMor1.proj 0)
  ERMor1.comp ERMor1.minN (fun i => match i with
    | ⟨0, _⟩ => betaAtCode
    | ⟨1, _⟩ => valBound)

/-- Unconditional upper bound for `cvRec`: its interpretation is dominated
by `valBound.interp ctx` for every code and parameter context. -/
theorem ERMor1.interp_cvRec_le_bound {k : ℕ} (node : ERMor1 (k + 3))
    (valBound : ERMor1 (k + 1)) (ctx : Fin (k + 1) → ℕ) :
    (ERMor1.cvRec node valBound).interp ctx ≤ valBound.interp ctx := by
  unfold ERMor1.cvRec
  rw [ERMor1.interp_comp, ERMor1.interp_minN]
  exact Nat.min_le_right _ _

/-- Determinacy helper for `cvRec`: under the node-faithfulness hypothesis,
any candidate satisfying the per-position clauses of `cvRecPred` for every
`j < code + 1` β-reads the reference table `f` at every position
`j ≤ code`.  Strong induction on the position: agreement propagates upward
because the node hypothesis needs agreement only strictly below its
index. -/
theorem ERMor1.cvRecPred_trace_match {k : ℕ}
    (node : ERMor1 (k + 3)) (cand : ℕ) (ctx : Fin k → ℕ)
    (code : ℕ) (f : ℕ → ℕ)
    (h_node : ∀ i, i ≤ code → ∀ c,
      (∀ p, p < i →
        c.unpair.1 % (1 + (p + 1) * c.unpair.2) = f p) →
      node.interp
        (Fin.cons i (Fin.cons c (Fin.cons code ctx))) = f i)
    (htrace : ∀ j, j < code + 1 →
      cand.unpair.1 % (1 + (j + 1) * cand.unpair.2) =
        node.interp
          (Fin.cons j (Fin.cons cand (Fin.cons code ctx)))) :
    ∀ j, j ≤ code →
      cand.unpair.1 % (1 + (j + 1) * cand.unpair.2) = f j := by
  intro j hj
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    have hreads : ∀ p, p < j →
        cand.unpair.1 % (1 + (p + 1) * cand.unpair.2) = f p :=
      fun p hp => ih p hp (le_trans (Nat.le_of_lt hp) hj)
    have hnode_j := h_node j hj cand hreads
    have hbody := htrace j (Nat.lt_succ_of_le hj)
    rw [hbody, hnode_j]

set_option maxHeartbeats 800000 in
-- The bprod-based β-witness search exceeds the default heartbeat limit.
/-- Conditional correctness of `cvRec`: when the value bound dominates the
reference table `f` on `[0, code]` and is monotone into the input position,
and the node is faithful to `f` (any candidate whose β-reads agree with `f`
at all positions `p < i` makes the node compute `f i`), the combinator
computes `f code`. -/
theorem ERMor1.interp_cvRec_of_bounded {k : ℕ}
    (node : ERMor1 (k + 3)) (valBound : ERMor1 (k + 1))
    (code : ℕ) (ctx : Fin k → ℕ) (f : ℕ → ℕ)
    (hval : ∀ j, j ≤ code → f j ≤ valBound.interp (Fin.cons j ctx))
    (h_mono : ∀ j, j ≤ code →
      valBound.interp (Fin.cons j ctx) ≤
        valBound.interp (Fin.cons code ctx))
    (h_node : ∀ i, i ≤ code → ∀ cand,
      (∀ p, p < i →
        cand.unpair.1 % (1 + (p + 1) * cand.unpair.2) = f p) →
      node.interp
        (Fin.cons i (Fin.cons cand (Fin.cons code ctx))) = f i) :
    (ERMor1.cvRec node valBound).interp (Fin.cons code ctx) = f code := by
  set B : ℕ := valBound.interp (Fin.cons code ctx) with _
  let s : Fin (code + 1) → ℕ := fun j => f j.val
  have hs_le_B : ∀ j : Fin (code + 1), s j ≤ B := by
    intro j
    have hj_le : j.val ≤ code := Nat.le_of_lt_succ j.isLt
    exact le_trans (hval j.val hj_le) (h_mono j.val hj_le)
  obtain ⟨a, b, hb_eq, ha_lt, hbeta⟩ :=
    Nat.bounded_beta_exists s B hs_le_B
  set cand : ℕ := Nat.pair a b with hcand_def
  have hcand_unpair_fst : cand.unpair.1 = a := by
    rw [hcand_def, Nat.unpair_pair]
  have hcand_unpair_snd : cand.unpair.2 = b := by
    rw [hcand_def, Nat.unpair_pair]
  have hrange :
      (ERMor1.boundedRecRange valBound).interp
        (Fin.cons code ctx) =
      ((code + B + 3).factorial) ^
        ((code + B + 3).factorial) + 1 := by
    rw [ERMor1.interp_boundedRecRange]
    have hc0 :
        (Fin.cons code ctx : Fin (k + 1) → ℕ) 0 = code := by
      rfl
    rw [hc0]
  have hcand_lt_range :
      cand <
        (ERMor1.boundedRecRange valBound).interp
          (Fin.cons code ctx) := by
    rw [hrange]
    exact Nat.pair_lt_boundedRecRange code B a b hb_eq ha_lt
  have hpred_hold :
      (ERMor1.cvRecPred node).interp
          (Fin.cons cand (Fin.cons code ctx)) = 1 := by
    rw [ERMor1.cvRecPred_eq_one_iff_trace]
    intro j hj
    have hj_le : j ≤ code := Nat.le_of_lt_succ hj
    have hreads : ∀ p, p < j →
        cand.unpair.1 % (1 + (p + 1) * cand.unpair.2) = f p := by
      intro p hp
      have hp_lt : p < code + 1 := by omega
      have hbeta_p := hbeta ⟨p, hp_lt⟩
      change a % (1 + (p + 1) * b) = f p at hbeta_p
      rw [hcand_unpair_fst, hcand_unpair_snd]
      exact hbeta_p
    have hnode_j := h_node j hj_le cand hreads
    rw [hnode_j, hcand_unpair_fst, hcand_unpair_snd]
    have hbeta_j := hbeta ⟨j, hj⟩
    change a % (1 + (j + 1) * b) = f j at hbeta_j
    exact hbeta_j
  have hpred_bound :
      ∀ j, (ERMor1.cvRecPred node).interp
        (Fin.cons j (Fin.cons code ctx)) ≤ 1 := by
    intro j
    exact ERMor1.cvRecPred_le_one node _
  set search : ERMor1 (k + 1) :=
    ERMor1.boundedSearch (ERMor1.boundedRecRange valBound)
      (ERMor1.cvRecPred node) with hsearch_def
  have hex : ∃ j, j <
      (ERMor1.boundedRecRange valBound).interp
        (Fin.cons code ctx) ∧
      (ERMor1.cvRecPred node).interp
        (Fin.cons j (Fin.cons code ctx)) = 1 :=
    ⟨cand, hcand_lt_range, hpred_hold⟩
  have hsearch_eval :
      search.interp (Fin.cons code ctx) = Nat.find hex := by
    rw [hsearch_def,
      ERMor1.interp_boundedSearch _ _ _ hpred_bound,
      dif_pos hex]
  set found : ℕ := Nat.find hex with hfound_def
  have hfound_pred :
      (ERMor1.cvRecPred node).interp
        (Fin.cons found (Fin.cons code ctx)) = 1 :=
    (Nat.find_spec hex).2
  have hfound_htrace :=
    (ERMor1.cvRecPred_eq_one_iff_trace node
      found code ctx).mp hfound_pred
  have hfound_trace :
      ∀ j, j ≤ code →
        found.unpair.1 % (1 + (j + 1) * found.unpair.2) = f j :=
    ERMor1.cvRecPred_trace_match node found ctx code f
      h_node hfound_htrace
  unfold ERMor1.cvRec
  rw [ERMor1.interp_comp, ERMor1.interp_minN]
  change min
      ((ERMor1.comp ERMor1.beta _).interp (Fin.cons code ctx))
      (valBound.interp (Fin.cons code ctx)) = f code
  have hbetaCode_eval :
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
        (Fin.cons code ctx) =
      found.unpair.1 %
        (1 + (code + 1) * found.unpair.2) := by
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
            (Fin.cons code ctx)) =
        ![found.unpair.1, found.unpair.2, code] := by
      funext i
      match i with
      | ⟨0, _⟩ =>
        change ERMor1.natUnpairFst.interp
            (fun (_ : Fin 1) =>
              search.interp (Fin.cons code ctx)) = _
        rw [hsearch_eval]
        have hfun :
            (fun (_ : Fin 1) => (found : ℕ)) = ![found] := by
          funext j
          match j with
          | ⟨0, _⟩ => rfl
        rw [hfun, ERMor1.interp_natUnpairFst]
        rfl
      | ⟨1, _⟩ =>
        change ERMor1.natUnpairSnd.interp
            (fun (_ : Fin 1) =>
              search.interp (Fin.cons code ctx)) = _
        rw [hsearch_eval]
        have hfun :
            (fun (_ : Fin 1) => (found : ℕ)) = ![found] := by
          funext j
          match j with
          | ⟨0, _⟩ => rfl
        rw [hfun, ERMor1.interp_natUnpairSnd]
        rfl
      | ⟨2, _⟩ =>
        change (Fin.cons code ctx :
            Fin (k + 1) → ℕ) 0 = _
        rfl
    rw [harg, ERMor1.interp_beta]
  rw [hbetaCode_eval]
  have htrace_code := hfound_trace code (le_refl code)
  rw [htrace_code]
  have htrace_le : f code ≤ B :=
    le_trans (hval code (le_refl code)) (h_mono code (le_refl code))
  exact min_eq_left htrace_le

/-! ### Gated two-dimensional variant -/

/-- Variant of `natBProd_le_one_of_body_le_one` requiring the factor bound
only on the interval of multiplication. -/
theorem natBProd_le_one_of_body_le_one_of_lt (b : ℕ) (f : ℕ → ℕ)
    (hf : ∀ i, i < b → f i ≤ 1) : natBProd b f ≤ 1 := by
  induction b with
  | zero => exact le_refl _
  | succ n ih =>
    have h1 : natBProd n f ≤ 1 :=
      ih (fun i hi => hf i (Nat.lt_succ_of_lt hi))
    have h2 : f n ≤ 1 := hf n (Nat.lt_succ_self _)
    change natBProd n f * f n ≤ 1
    calc natBProd n f * f n
        _ ≤ 1 * f n := Nat.mul_le_mul_right _ h1
        _ ≤ 1 * 1 := Nat.mul_le_mul_left _ h2
        _ = 1 := Nat.one_mul _

/-- Per-position body of the gated course-of-values predicate: an arity-`k + 3`
term at context `(j, cand, code, ctx)` selecting the `ERMor1.cvRecBody` check
when the gate `sane` (an arity-`k + 2` term at context `(j, code, ctx)`) reads
`1`, and the constant `1` when it reads `0`. -/
def ERMor1.cvRecGatedBody {k : ℕ} (node : ERMor1 (k + 3))
    (sane : ERMor1 (k + 2)) : ERMor1 (k + 3) :=
  ERMor1.comp ERMor1.condN (fun i => match i with
    | ⟨0, _⟩ =>
        ERMor1.comp sane (fun j => match j with
          | ⟨0, _⟩ => ERMor1.proj 0
          | ⟨p + 1, h⟩ =>
              ERMor1.proj (⟨p + 2, by omega⟩ : Fin (k + 3)))
    | ⟨1, _⟩ => ERMor1.cvRecBody node
    | ⟨2, _⟩ => ERMor1.natN (k + 3) 1)

/-- Arithmetic unfolding of the gated body as the `ERMor1.condN` expression
over the gate value and the ungated body check. -/
theorem ERMor1.interp_cvRecGatedBody {k : ℕ}
    (node : ERMor1 (k + 3)) (sane : ERMor1 (k + 2))
    (j cand code : ℕ) (ctx : Fin k → ℕ) :
    (ERMor1.cvRecGatedBody node sane).interp
        (Fin.cons j (Fin.cons cand (Fin.cons code ctx))) =
      sane.interp (Fin.cons j (Fin.cons code ctx)) *
          (ERMor1.cvRecBody node).interp
            (Fin.cons j (Fin.cons cand (Fin.cons code ctx))) +
        (1 - sane.interp (Fin.cons j (Fin.cons code ctx))) * 1 := by
  have hunf :
      (ERMor1.cvRecGatedBody node sane).interp
          (Fin.cons j (Fin.cons cand (Fin.cons code ctx))) =
        ERMor1.condN.interp
          ![sane.interp (Fin.cons j (Fin.cons code ctx)),
            (ERMor1.cvRecBody node).interp
              (Fin.cons j (Fin.cons cand (Fin.cons code ctx))), 1] := by
    change ERMor1.condN.interp _ = ERMor1.condN.interp _
    congr 1
    funext i
    match i with
    | ⟨0, _⟩ =>
      change sane.interp _ = _
      congr 1
      funext p
      match p with
      | ⟨0, _⟩ => rfl
      | ⟨1, _⟩ => rfl
      | ⟨q + 2, _⟩ => rfl
    | ⟨1, _⟩ => rfl
    | ⟨2, _⟩ => exact ERMor1.interp_natN _ _ _
  rw [hunf, ERMor1.interp_condN]
  rfl

/-- The gated body evaluates in `{0, 1}` whenever the gate does. -/
theorem ERMor1.cvRecGatedBody_le_one {k : ℕ}
    (node : ERMor1 (k + 3)) (sane : ERMor1 (k + 2))
    (j cand code : ℕ) (ctx : Fin k → ℕ)
    (hS : sane.interp (Fin.cons j (Fin.cons code ctx)) ≤ 1) :
    (ERMor1.cvRecGatedBody node sane).interp
      (Fin.cons j (Fin.cons cand (Fin.cons code ctx))) ≤ 1 := by
  rw [ERMor1.interp_cvRecGatedBody]
  have hb := ERMor1.cvRecBody_le_one node
    (Fin.cons j (Fin.cons cand (Fin.cons code ctx)))
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hS with h0 | h1
  · rw [h0]
    omega
  · rw [h1]
    omega

/-- The gated body equals `1` iff a gate reading of `1` forces the β-read at
position `j` to match the node value at `j`.  Requires the gate to evaluate
in `{0, 1}`. -/
theorem ERMor1.cvRecGatedBody_eq_one_iff {k : ℕ}
    (node : ERMor1 (k + 3)) (sane : ERMor1 (k + 2))
    (j cand code : ℕ) (ctx : Fin k → ℕ)
    (hS : sane.interp (Fin.cons j (Fin.cons code ctx)) ≤ 1) :
    (ERMor1.cvRecGatedBody node sane).interp
        (Fin.cons j (Fin.cons cand (Fin.cons code ctx))) = 1 ↔
      (sane.interp (Fin.cons j (Fin.cons code ctx)) = 1 →
        cand.unpair.1 % (1 + (j + 1) * cand.unpair.2) =
          node.interp
            (Fin.cons j (Fin.cons cand (Fin.cons code ctx)))) := by
  rw [ERMor1.interp_cvRecGatedBody]
  have hb1 := ERMor1.cvRecBody_eq_one_iff node j cand code ctx
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hS with h0 | h1
  · rw [h0]
    constructor
    · intro _ habs
      exact (Nat.zero_ne_one habs).elim
    · intro _
      omega
  · rw [h1]
    constructor
    · intro h _
      apply hb1.mp
      omega
    · intro h
      have hb := hb1.mpr (h rfl)
      omega

/-- Full predicate for the gated course-of-values β-witness search.  At
context `Fin.cons cand (Fin.cons code ctx)`, evaluates to `1` iff every
position `j < idxBound + 1` satisfies the gated body check. -/
def ERMor1.cvRecGatedPred {k : ℕ} (node : ERMor1 (k + 3))
    (sane : ERMor1 (k + 2)) (idxBound : ERMor1 (k + 1)) :
    ERMor1 (k + 2) :=
  ERMor1.comp (ERMor1.bprod (ERMor1.cvRecGatedBody node sane))
    (fun (i : Fin (k + 3)) => match i with
      | ⟨0, _⟩ =>
          ERMor1.comp ERMor1.succ (fun (_ : Fin 1) =>
            ERMor1.comp idxBound
              (fun j => ERMor1.proj (k := k + 2) j.succ))
      | ⟨1, _⟩ => ERMor1.proj 0
      | ⟨2, _⟩ => ERMor1.proj 1
      | ⟨p + 3, h⟩ =>
          ERMor1.proj ⟨p + 2, by omega⟩)

/-- The gated predicate as a bounded product of gated body values over
positions `j ∈ [0, idxBound + 1)`. -/
theorem ERMor1.interp_cvRecGatedPred_as_bprod {k : ℕ}
    (node : ERMor1 (k + 3)) (sane : ERMor1 (k + 2))
    (idxBound : ERMor1 (k + 1)) (cand code : ℕ) (ctx : Fin k → ℕ) :
    (ERMor1.cvRecGatedPred node sane idxBound).interp
        (Fin.cons cand (Fin.cons code ctx)) =
      natBProd (idxBound.interp (Fin.cons code ctx) + 1) (fun j =>
        (ERMor1.cvRecGatedBody node sane).interp
          (Fin.cons j (Fin.cons cand (Fin.cons code ctx)))) := by
  unfold ERMor1.cvRecGatedPred
  rw [ERMor1.interp_comp]
  set argFn : Fin (k + 3) → ℕ := fun i =>
    ((fun i : Fin (k + 3) => match i with
      | ⟨0, _⟩ =>
          ERMor1.comp ERMor1.succ (fun (_ : Fin 1) =>
            ERMor1.comp idxBound
              (fun j => ERMor1.proj (k := k + 2) j.succ))
      | ⟨1, _⟩ => ERMor1.proj 0
      | ⟨2, _⟩ => ERMor1.proj 1
      | ⟨p + 3, h⟩ =>
          ERMor1.proj
            (⟨p + 2, by omega⟩ : Fin (k + 2))) i).interp
      (Fin.cons cand (Fin.cons code ctx))
  rw [ERMor1.interp_bprod]
  have h0 : argFn 0 = idxBound.interp (Fin.cons code ctx) + 1 := by
    change ((ERMor1.comp ERMor1.succ (fun (_ : Fin 1) =>
        ERMor1.comp idxBound
          (fun j => ERMor1.proj (k := k + 2) j.succ))).interp
        (Fin.cons cand (Fin.cons code ctx))) = _
    rw [ERMor1.interp_comp, ERMor1.interp_succ]
    rw [ERMor1.interp_comp]
    have hargs :
        (fun j : Fin (k + 1) =>
          (ERMor1.proj (k := k + 2) j.succ).interp
            (Fin.cons cand (Fin.cons code ctx))) =
          Fin.cons code ctx := by
      funext p
      rfl
    rw [hargs]
  have htail :
      Fin.tail argFn =
        Fin.cons cand (Fin.cons code ctx) := by
    funext ⟨p, hp⟩
    change argFn ⟨p + 1, by omega⟩ = _
    match p with
    | 0 => rfl
    | 1 => rfl
    | q + 2 => rfl
  rw [h0, htail]

/-- The gated predicate evaluates in `{0, 1}` whenever the gate does on the
checked range. -/
theorem ERMor1.cvRecGatedPred_le_one {k : ℕ}
    (node : ERMor1 (k + 3)) (sane : ERMor1 (k + 2))
    (idxBound : ERMor1 (k + 1)) (cand code : ℕ) (ctx : Fin k → ℕ)
    (h_sane : ∀ i, i ≤ idxBound.interp (Fin.cons code ctx) →
      sane.interp (Fin.cons i (Fin.cons code ctx)) ≤ 1) :
    (ERMor1.cvRecGatedPred node sane idxBound).interp
      (Fin.cons cand (Fin.cons code ctx)) ≤ 1 := by
  rw [ERMor1.interp_cvRecGatedPred_as_bprod]
  exact natBProd_le_one_of_body_le_one_of_lt _ _ (fun i hi =>
    ERMor1.cvRecGatedBody_le_one node sane i cand code ctx
      (h_sane i (Nat.le_of_lt_succ hi)))

/-- The gated predicate equals `1` iff, at every position `j ≤ idxBound`
where the gate reads `1`, the β-read matches the node value.  Requires the
gate to evaluate in `{0, 1}` on the checked range. -/
theorem ERMor1.cvRecGatedPred_eq_one_iff_trace {k : ℕ}
    (node : ERMor1 (k + 3)) (sane : ERMor1 (k + 2))
    (idxBound : ERMor1 (k + 1)) (cand code : ℕ) (ctx : Fin k → ℕ)
    (h_sane : ∀ i, i ≤ idxBound.interp (Fin.cons code ctx) →
      sane.interp (Fin.cons i (Fin.cons code ctx)) ≤ 1) :
    (ERMor1.cvRecGatedPred node sane idxBound).interp
        (Fin.cons cand (Fin.cons code ctx)) = 1 ↔
      ∀ j, j < idxBound.interp (Fin.cons code ctx) + 1 →
        sane.interp (Fin.cons j (Fin.cons code ctx)) = 1 →
        cand.unpair.1 % (1 + (j + 1) * cand.unpair.2) =
          node.interp
            (Fin.cons j (Fin.cons cand (Fin.cons code ctx))) := by
  rw [ERMor1.interp_cvRecGatedPred_as_bprod,
    natBProd_eq_one_iff_all_one]
  constructor
  · intro h j hj
    exact (ERMor1.cvRecGatedBody_eq_one_iff node sane
      j cand code ctx (h_sane j (Nat.le_of_lt_succ hj))).mp (h j hj)
  · intro h j hj
    exact (ERMor1.cvRecGatedBody_eq_one_iff node sane
      j cand code ctx (h_sane j (Nat.le_of_lt_succ hj))).mpr (h j hj)

/-- Search range for the gated combinator: `ERMor1.boundedRecRange` with the
index bound in the counter slot and the value bound as its bound argument,
evaluating to `((N + B + 3)!) ^ ((N + B + 3)!) + 1` with `N` the index bound
and `B` the value bound at `(code, ctx)`.  This dominates every
Szudzik-paired β-witness produced by `Nat.bounded_beta_exists` on a table of
length `N + 1` whose values are bounded by `B`. -/
def ERMor1.cvRecGatedRange {k : ℕ}
    (idxBound valBound : ERMor1 (k + 1)) : ERMor1 (k + 1) :=
  ERMor1.comp
    (ERMor1.boundedRecRange (k := k + 1)
      (ERMor1.comp valBound (fun i => ERMor1.proj i.succ)))
    (fun i => match i with
      | ⟨0, _⟩ => idxBound
      | ⟨p + 1, h⟩ =>
          ERMor1.proj (⟨p, by omega⟩ : Fin (k + 1)))

/-- Interpretation of `cvRecGatedRange`. -/
@[simp] theorem ERMor1.interp_cvRecGatedRange {k : ℕ}
    (idxBound valBound : ERMor1 (k + 1)) (ctx : Fin (k + 1) → ℕ) :
    (ERMor1.cvRecGatedRange idxBound valBound).interp ctx =
      ((idxBound.interp ctx + valBound.interp ctx + 3).factorial) ^
        ((idxBound.interp ctx + valBound.interp ctx + 3).factorial) + 1 := by
  have hbrr :
      (ERMor1.boundedRecRange (k := k + 1)
          (ERMor1.comp valBound (fun i => ERMor1.proj i.succ))).interp
        (Fin.cons (idxBound.interp ctx) ctx) =
      ((idxBound.interp ctx + valBound.interp ctx + 3).factorial) ^
        ((idxBound.interp ctx + valBound.interp ctx + 3).factorial) + 1 := by
    rw [ERMor1.interp_boundedRecRange]
    have h0 : (Fin.cons (idxBound.interp ctx) ctx :
        Fin (k + 2) → ℕ) 0 = idxBound.interp ctx := rfl
    have hvb :
        (ERMor1.comp valBound (fun i => ERMor1.proj i.succ)).interp
            (Fin.cons (idxBound.interp ctx) ctx) =
          valBound.interp ctx := by
      rw [ERMor1.interp_comp]
      congr 1
    rw [h0, hvb]
  unfold ERMor1.cvRecGatedRange
  rw [ERMor1.interp_comp]
  refine Eq.trans ?_ hbrr
  congr 1
  funext ⟨p, hp⟩
  match p with
  | 0 => rfl
  | q + 1 => rfl

/-- Gated ER course-of-values table search.  At outer arity `k + 1` with
slot `0` the code and slots `1..k` the parameter context, returns
`min (β(a, b, extractAt)) valBound`, where `(a, b) = Nat.unpair` of the
least `cand` satisfying `cvRecGatedPred node sane idxBound = 1` below
`cvRecGatedRange idxBound valBound`.  The outer `minN` makes the output
unconditionally bounded by `valBound`.  Correctness against a reference
table holds under the hypotheses of `ERMor1.interp_cvRecGated_eq`. -/
def ERMor1.cvRecGated {k : ℕ} (node : ERMor1 (k + 3))
    (sane : ERMor1 (k + 2))
    (idxBound extractAt valBound : ERMor1 (k + 1)) : ERMor1 (k + 1) :=
  let search : ERMor1 (k + 1) :=
    ERMor1.boundedSearch (ERMor1.cvRecGatedRange idxBound valBound)
      (ERMor1.cvRecGatedPred node sane idxBound)
  let betaAtExtract : ERMor1 (k + 1) :=
    ERMor1.comp ERMor1.beta (fun i => match i with
      | ⟨0, _⟩ =>
          ERMor1.comp ERMor1.natUnpairFst
            (fun (_ : Fin 1) => search)
      | ⟨1, _⟩ =>
          ERMor1.comp ERMor1.natUnpairSnd
            (fun (_ : Fin 1) => search)
      | ⟨2, _⟩ => extractAt)
  ERMor1.comp ERMor1.minN (fun i => match i with
    | ⟨0, _⟩ => betaAtExtract
    | ⟨1, _⟩ => valBound)

/-- Unconditional upper bound for `cvRecGated`: its interpretation is
dominated by `valBound.interp ctx` for every code and parameter context. -/
theorem ERMor1.interp_cvRecGated_le_bound {k : ℕ}
    (node : ERMor1 (k + 3)) (sane : ERMor1 (k + 2))
    (idxBound extractAt valBound : ERMor1 (k + 1))
    (ctx : Fin (k + 1) → ℕ) :
    (ERMor1.cvRecGated node sane idxBound extractAt valBound).interp ctx ≤
      valBound.interp ctx := by
  unfold ERMor1.cvRecGated
  rw [ERMor1.interp_comp, ERMor1.interp_minN]
  exact Nat.min_le_right _ _

set_option maxHeartbeats 800000 in
-- The bprod-based β-witness search exceeds the default heartbeat limit.
/-- Conditional correctness of `cvRecGated`.  With `N`, `B`, `X` the
interpretations of `idxBound`, `valBound`, `extractAt` at `(code, ctx)`:
when the gate evaluates in `{0, 1}` on `[0, N]` (`h_sane`), the value bound
dominates the reference table `f` on `[0, N]` (`hval`), the node is faithful
to `f` at gated positions against candidates agreeing with `f` on all of
`[0, N]` (`h_node`), any candidate satisfying every gated equation β-reads
`f X` at the extraction position (`h_det`, the client-supplied determinacy
input), and `X ≤ N` (`h_ext`), the combinator computes `f X`.  The
extraction-value bound `f X ≤ B` deactivating the clamp follows from `hval`
at `h_ext`. -/
theorem ERMor1.interp_cvRecGated_eq {k : ℕ}
    (node : ERMor1 (k + 3)) (sane : ERMor1 (k + 2))
    (idxBound extractAt valBound : ERMor1 (k + 1))
    (code : ℕ) (ctx : Fin k → ℕ) (f : ℕ → ℕ)
    (h_sane : ∀ i, i ≤ idxBound.interp (Fin.cons code ctx) →
      sane.interp (Fin.cons i (Fin.cons code ctx)) ≤ 1)
    (hval : ∀ i, i ≤ idxBound.interp (Fin.cons code ctx) →
      f i ≤ valBound.interp (Fin.cons code ctx))
    (h_node : ∀ i, i ≤ idxBound.interp (Fin.cons code ctx) →
      sane.interp (Fin.cons i (Fin.cons code ctx)) = 1 → ∀ cand,
      (∀ p, p ≤ idxBound.interp (Fin.cons code ctx) →
        cand.unpair.1 % (1 + (p + 1) * cand.unpair.2) = f p) →
      node.interp
        (Fin.cons i (Fin.cons cand (Fin.cons code ctx))) = f i)
    (h_det : ∀ cand,
      (∀ i, i ≤ idxBound.interp (Fin.cons code ctx) →
        sane.interp (Fin.cons i (Fin.cons code ctx)) = 1 →
        cand.unpair.1 % (1 + (i + 1) * cand.unpair.2) =
          node.interp
            (Fin.cons i (Fin.cons cand (Fin.cons code ctx)))) →
      cand.unpair.1 %
          (1 + (extractAt.interp (Fin.cons code ctx) + 1) *
            cand.unpair.2) =
        f (extractAt.interp (Fin.cons code ctx)))
    (h_ext : extractAt.interp (Fin.cons code ctx) ≤
      idxBound.interp (Fin.cons code ctx)) :
    (ERMor1.cvRecGated node sane idxBound extractAt valBound).interp
        (Fin.cons code ctx) =
      f (extractAt.interp (Fin.cons code ctx)) := by
  set N : ℕ := idxBound.interp (Fin.cons code ctx) with hN_def
  set B : ℕ := valBound.interp (Fin.cons code ctx) with hB_def
  set X : ℕ := extractAt.interp (Fin.cons code ctx) with hX_def
  let s : Fin (N + 1) → ℕ := fun j => f j.val
  have hs_le_B : ∀ j : Fin (N + 1), s j ≤ B := fun j =>
    hval j.val (Nat.le_of_lt_succ j.isLt)
  obtain ⟨a, b, hb_eq, ha_lt, hbeta⟩ :=
    Nat.bounded_beta_exists s B hs_le_B
  set cand : ℕ := Nat.pair a b with hcand_def
  have hcand_unpair_fst : cand.unpair.1 = a := by
    rw [hcand_def, Nat.unpair_pair]
  have hcand_unpair_snd : cand.unpair.2 = b := by
    rw [hcand_def, Nat.unpair_pair]
  have hreads : ∀ p, p ≤ N →
      cand.unpair.1 % (1 + (p + 1) * cand.unpair.2) = f p := by
    intro p hp
    have hbeta_p := hbeta ⟨p, Nat.lt_succ_of_le hp⟩
    change a % (1 + (p + 1) * b) = f p at hbeta_p
    rw [hcand_unpair_fst, hcand_unpair_snd]
    exact hbeta_p
  have hrange :
      (ERMor1.cvRecGatedRange idxBound valBound).interp
          (Fin.cons code ctx) =
        ((N + B + 3).factorial) ^ ((N + B + 3).factorial) + 1 := by
    rw [ERMor1.interp_cvRecGatedRange]
  have hcand_lt_range :
      cand <
        (ERMor1.cvRecGatedRange idxBound valBound).interp
          (Fin.cons code ctx) := by
    rw [hrange]
    exact Nat.pair_lt_boundedRecRange N B a b hb_eq ha_lt
  have hpred_hold :
      (ERMor1.cvRecGatedPred node sane idxBound).interp
          (Fin.cons cand (Fin.cons code ctx)) = 1 := by
    rw [ERMor1.cvRecGatedPred_eq_one_iff_trace node sane idxBound
      cand code ctx h_sane]
    intro j hj hSj
    have hj_le : j ≤ N := Nat.le_of_lt_succ hj
    have hnode_j := h_node j hj_le hSj cand hreads
    rw [hnode_j]
    exact hreads j hj_le
  have hpred_bound :
      ∀ j, (ERMor1.cvRecGatedPred node sane idxBound).interp
        (Fin.cons j (Fin.cons code ctx)) ≤ 1 :=
    fun j => ERMor1.cvRecGatedPred_le_one node sane idxBound
      j code ctx h_sane
  set search : ERMor1 (k + 1) :=
    ERMor1.boundedSearch (ERMor1.cvRecGatedRange idxBound valBound)
      (ERMor1.cvRecGatedPred node sane idxBound) with hsearch_def
  have hex : ∃ j, j <
      (ERMor1.cvRecGatedRange idxBound valBound).interp
        (Fin.cons code ctx) ∧
      (ERMor1.cvRecGatedPred node sane idxBound).interp
        (Fin.cons j (Fin.cons code ctx)) = 1 :=
    ⟨cand, hcand_lt_range, hpred_hold⟩
  have hsearch_eval :
      search.interp (Fin.cons code ctx) = Nat.find hex := by
    rw [hsearch_def,
      ERMor1.interp_boundedSearch _ _ _ hpred_bound,
      dif_pos hex]
  set found : ℕ := Nat.find hex with hfound_def
  have hfound_pred :
      (ERMor1.cvRecGatedPred node sane idxBound).interp
        (Fin.cons found (Fin.cons code ctx)) = 1 :=
    (Nat.find_spec hex).2
  have hfound_trace :=
    (ERMor1.cvRecGatedPred_eq_one_iff_trace node sane idxBound
      found code ctx h_sane).mp hfound_pred
  have hdet_found :
      found.unpair.1 % (1 + (X + 1) * found.unpair.2) = f X :=
    h_det found (fun i hi hSi =>
      hfound_trace i (Nat.lt_succ_of_le hi) hSi)
  unfold ERMor1.cvRecGated
  rw [ERMor1.interp_comp, ERMor1.interp_minN]
  change min
      ((ERMor1.comp ERMor1.beta _).interp (Fin.cons code ctx))
      (valBound.interp (Fin.cons code ctx)) = f X
  have hbetaExtract_eval :
      (ERMor1.comp ERMor1.beta
        (fun (i : Fin 3) => match i with
          | ⟨0, _⟩ =>
              ERMor1.comp ERMor1.natUnpairFst
                (fun (_ : Fin 1) => search)
          | ⟨1, _⟩ =>
              ERMor1.comp ERMor1.natUnpairSnd
                (fun (_ : Fin 1) => search)
          | ⟨2, _⟩ => extractAt)).interp
        (Fin.cons code ctx) =
      found.unpair.1 %
        (1 + (X + 1) * found.unpair.2) := by
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
            | ⟨2, _⟩ => extractAt : ERMor1 (k + 1))).interp
            (Fin.cons code ctx)) =
        ![found.unpair.1, found.unpair.2, X] := by
      funext i
      match i with
      | ⟨0, _⟩ =>
        change ERMor1.natUnpairFst.interp
            (fun (_ : Fin 1) =>
              search.interp (Fin.cons code ctx)) = _
        rw [hsearch_eval]
        have hfun :
            (fun (_ : Fin 1) => (found : ℕ)) = ![found] := by
          funext j
          match j with
          | ⟨0, _⟩ => rfl
        rw [hfun, ERMor1.interp_natUnpairFst]
        rfl
      | ⟨1, _⟩ =>
        change ERMor1.natUnpairSnd.interp
            (fun (_ : Fin 1) =>
              search.interp (Fin.cons code ctx)) = _
        rw [hsearch_eval]
        have hfun :
            (fun (_ : Fin 1) => (found : ℕ)) = ![found] := by
          funext j
          match j with
          | ⟨0, _⟩ => rfl
        rw [hfun, ERMor1.interp_natUnpairSnd]
        rfl
      | ⟨2, _⟩ =>
        change extractAt.interp (Fin.cons code ctx) = _
        rfl
    rw [harg, ERMor1.interp_beta]
  rw [hbetaExtract_eval, hdet_found]
  exact min_eq_left (hval X h_ext)

end GebLean
