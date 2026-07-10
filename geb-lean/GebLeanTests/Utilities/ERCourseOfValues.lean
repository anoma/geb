import GebLean.Utilities.ERCourseOfValues

/-!
# Tests for `GebLean.Utilities.ERCourseOfValues`.
-/

open GebLean

/-- `cvRec` at `k = 0` with the node `proj 0` (which reads no β-positions,
so the reference table is the identity `f = id`) and value bound `proj 0`
extracts the input code itself, by `interp_cvRec_of_bounded`. -/
example (c : ℕ) :
    (ERMor1.cvRec (k := 0) (ERMor1.proj 0)
        (ERMor1.proj 0)).interp ![c] = c :=
  ERMor1.interp_cvRec_of_bounded
    (ERMor1.proj 0) (ERMor1.proj 0) c ![] id
    (fun j _ => le_refl j)
    (fun _ hj => hj)
    (fun _ _ _ _ => rfl)

/-- The `cvRec` output at the identity instantiation is dominated by its
value bound, by `interp_cvRec_le_bound`. -/
example (c : ℕ) :
    (ERMor1.cvRec (k := 0) (ERMor1.proj 0)
        (ERMor1.proj 0)).interp ![c] ≤ c :=
  ERMor1.interp_cvRec_le_bound
    (ERMor1.proj 0) (ERMor1.proj 0) ![c]

namespace GebLean.CvRecGatedSmoke

/-- Gate for the `cvRecGated` smoke test: at context `(i, code)`, evaluates
to `1` iff `i ≤ code / 2`. -/
def gateHalf : ERMor1 2 :=
  ERMor1.comp ERMor1.leN (fun j => match j with
    | ⟨0, _⟩ => ERMor1.proj 0
    | ⟨1, _⟩ =>
        ERMor1.comp ERMor1.div (fun l => match l with
          | ⟨0, _⟩ => ERMor1.proj 1
          | ⟨1, _⟩ => ERMor1.natN 2 2))

/-- Interpretation of `gateHalf`: the `0/1` indicator of `ctx 0 ≤ ctx 1 / 2`. -/
theorem interp_gateHalf (ctx : Fin 2 → ℕ) :
    gateHalf.interp ctx = if ctx 0 ≤ ctx 1 / 2 then 1 else 0 := by
  have hunf : gateHalf.interp ctx =
      ERMor1.leN.interp ![ctx 0, ctx 1 / 2] := by
    change ERMor1.leN.interp _ = ERMor1.leN.interp _
    congr 1
    funext j
    match j with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ =>
      change ERMor1.div.interp _ = _
      have harg :
          (fun l : Fin 2 =>
            ((match l with
              | ⟨0, _⟩ => ERMor1.proj 1
              | ⟨1, _⟩ => ERMor1.natN 2 2 : ERMor1 2)).interp ctx) =
          ![ctx 1, 2] := by
        funext l
        match l with
        | ⟨0, _⟩ => rfl
        | ⟨1, _⟩ => exact ERMor1.interp_natN 2 2 ctx
      rw [harg, ERMor1.interp_div]
      rfl
  rw [hunf, ERMor1.interp_leN]
  rfl

/-- Halving morphism for the `cvRecGated` smoke test: `ctx 0 / 2`. -/
def halfN : ERMor1 1 :=
  ERMor1.comp ERMor1.div (fun l => match l with
    | ⟨0, _⟩ => ERMor1.proj 0
    | ⟨1, _⟩ => ERMor1.natN 1 2)

/-- Interpretation of `halfN`. -/
theorem interp_halfN (ctx : Fin 1 → ℕ) :
    halfN.interp ctx = ctx 0 / 2 := by
  have hunf : halfN.interp ctx = ERMor1.div.interp ![ctx 0, 2] := by
    change ERMor1.div.interp _ = ERMor1.div.interp _
    congr 1
    funext l
    match l with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => exact ERMor1.interp_natN 1 2 ctx
  rw [hunf, ERMor1.interp_div]

/-- `cvRecGated` at `k = 0` with gate `i ≤ code / 2` (so the checked range
`[0, code]` includes off-gate positions, exercising the ungated
constant-`1` path of the predicate), node `proj 0`, reference table
`f i = if i ≤ code / 2 then i else 0`, and extraction at the gated position
`code / 2`: computes `code / 2`, by `interp_cvRecGated_eq` with a
hand-proved determinacy hypothesis. -/
example (c : ℕ) :
    (ERMor1.cvRecGated (k := 0) (ERMor1.proj 0) gateHalf (ERMor1.proj 0)
        halfN (ERMor1.proj 0)).interp ![c] = c / 2 := by
  have hgate_le_one : ∀ i : ℕ,
      gateHalf.interp (Fin.cons i (Fin.cons c ![])) ≤ 1 := by
    intro i
    rw [interp_gateHalf]
    split
    · exact le_refl 1
    · exact Nat.zero_le 1
  have hgate_of_eq_one : ∀ i : ℕ,
      gateHalf.interp (Fin.cons i (Fin.cons c ![])) = 1 → i ≤ c / 2 := by
    intro i h
    rw [interp_gateHalf] at h
    change (if i ≤ c / 2 then 1 else 0) = 1 at h
    by_contra hnot
    rw [if_neg hnot] at h
    omega
  have h_sane : ∀ i : ℕ, i ≤ c →
      gateHalf.interp (Fin.cons i (Fin.cons c ![])) ≤ 1 :=
    fun i _ => hgate_le_one i
  have hval : ∀ i : ℕ, i ≤ c → (if i ≤ c / 2 then i else 0) ≤ c := by
    intro i hi
    split
    · exact hi
    · exact Nat.zero_le c
  have h_node : ∀ i : ℕ, i ≤ c →
      gateHalf.interp (Fin.cons i (Fin.cons c ![])) = 1 → ∀ cand : ℕ,
      (∀ p : ℕ, p ≤ c →
        cand.unpair.1 % (1 + (p + 1) * cand.unpair.2) =
          (if p ≤ c / 2 then p else 0)) →
      (ERMor1.proj (0 : Fin 3)).interp
          (Fin.cons i (Fin.cons cand (Fin.cons c ![]))) =
        (if i ≤ c / 2 then i else 0) := by
    intro i _ hS cand _
    rw [if_pos (hgate_of_eq_one i hS)]
    rfl
  have h_det : ∀ cand : ℕ,
      (∀ i : ℕ, i ≤ c →
        gateHalf.interp (Fin.cons i (Fin.cons c ![])) = 1 →
        cand.unpair.1 % (1 + (i + 1) * cand.unpair.2) =
          (ERMor1.proj (0 : Fin 3)).interp
            (Fin.cons i (Fin.cons cand (Fin.cons c ![])))) →
      cand.unpair.1 %
          (1 + (halfN.interp (Fin.cons c ![]) + 1) * cand.unpair.2) =
        (if halfN.interp (Fin.cons c ![]) ≤ c / 2 then
          halfN.interp (Fin.cons c ![]) else 0) := by
    intro cand h
    have hXval : halfN.interp (Fin.cons c ![]) = c / 2 :=
      interp_halfN (Fin.cons c ![])
    rw [hXval]
    have hgate : gateHalf.interp
        (Fin.cons (c / 2) (Fin.cons c ![])) = 1 := by
      rw [interp_gateHalf]
      change (if c / 2 ≤ c / 2 then 1 else 0) = 1
      rw [if_pos (le_refl (c / 2))]
    have hread := h (c / 2) (Nat.div_le_self c 2) hgate
    rw [if_pos (le_refl (c / 2))]
    exact hread
  have h_ext : halfN.interp (Fin.cons c ![]) ≤
      (ERMor1.proj (0 : Fin 1)).interp (Fin.cons c ![]) := by
    rw [interp_halfN]
    exact Nat.div_le_self c 2
  have key := ERMor1.interp_cvRecGated_eq (ERMor1.proj 0) gateHalf
    (ERMor1.proj 0) halfN (ERMor1.proj 0) c ![]
    (fun i => if i ≤ c / 2 then i else 0)
    h_sane hval h_node h_det h_ext
  rw [interp_halfN] at key
  exact key.trans (if_pos (le_refl (c / 2)))

/-- The `cvRecGated` output at the smoke instantiation is dominated by its
value bound, by `interp_cvRecGated_le_bound`. -/
example (c : ℕ) :
    (ERMor1.cvRecGated (k := 0) (ERMor1.proj 0) gateHalf (ERMor1.proj 0)
        halfN (ERMor1.proj 0)).interp ![c] ≤ c :=
  ERMor1.interp_cvRecGated_le_bound (ERMor1.proj 0) gateHalf
    (ERMor1.proj 0) halfN (ERMor1.proj 0) ![c]

end GebLean.CvRecGatedSmoke
