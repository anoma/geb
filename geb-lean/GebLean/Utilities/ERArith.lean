import GebLean.LawvereER
import GebLean.LawvereERArith
import GebLean.LawvereERBool
import GebLean.Utilities.SzudzikSeq
import Mathlib.Data.Nat.Pairing
import Mathlib.Logic.Godel.GodelBetaFunction
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# ER-Derived Arithmetic and Gödel β

`ERMor1`-level versions of mathlib's `Nat.pair`/`Nat.unpair`/
`Nat.sqrt` plus derived `div`/`mod`, the Gödel β-function, a
bounded search combinator, and the primitive-recursion
combinator `ERMor1.natRec`.  Each primitive carries an
`@[simp]`-marked correctness theorem linking its
interpretation to its mathematical counterpart.

Every primitive is a closed-form `ERMor1` term built by
composition of the 7 Wikipedia generators (`zero`, `succ`,
`proj`, `sub`, `comp`, `bsum`, `bprod`).  The `ERMor1`
inductive is not extended.

Part of the ER-Primrec mini-phase; see
`docs/superpowers/specs/2026-04-17-er-primrec-design.md`.
-/

namespace GebLean

/-- Multiplication as an `ERMor1 2` term: interpretation at
`![a, b]` equals `a * b`.  Coincides with `boolAnd`. -/
def ERMor1.mulN : ERMor1 2 := ERMor1.boolAnd

/-- Interpretation of `mulN`. -/
@[simp] theorem ERMor1.interp_mulN (ctx : Fin 2 → ℕ) :
    ERMor1.mulN.interp ctx = ctx 0 * ctx 1 :=
  ERMor1.interp_boolAnd ctx

/-- Addition as an `ERMor1 2` term.  Implemented via the
identity `a + b = (a + 1) * (b + 1) - a * b - 1`, which is
non-truncating on ℕ since `(a+1)*(b+1) = a*b + a + b + 1`. -/
def ERMor1.addN : ERMor1 2 :=
  ERMor1.comp ERMor1.sub fun i => match i with
    | ⟨0, _⟩ =>
        ERMor1.comp ERMor1.sub fun j => match j with
          | ⟨0, _⟩ =>
              ERMor1.comp ERMor1.mulN fun k => match k with
                | ⟨0, _⟩ =>
                    ERMor1.comp ERMor1.succ
                      fun (_ : Fin 1) => ERMor1.proj 0
                | ⟨1, _⟩ =>
                    ERMor1.comp ERMor1.succ
                      fun (_ : Fin 1) => ERMor1.proj 1
          | ⟨1, _⟩ => ERMor1.mulN
    | ⟨1, _⟩ => ERMor1.oneN 2

/-- Interpretation of `addN`: `ctx 0 + ctx 1`. -/
@[simp] theorem ERMor1.interp_addN (ctx : Fin 2 → ℕ) :
    ERMor1.addN.interp ctx = ctx 0 + ctx 1 := by
  have heq : ERMor1.addN.interp ctx =
      (ctx 0 + 1) * (ctx 1 + 1) - ctx 0 * ctx 1 - 1 := by
    unfold ERMor1.addN
    simp only [ERMor1.interp_comp, ERMor1.interp_sub,
      ERMor1.interp_mulN, ERMor1.interp_succ,
      ERMor1.interp_proj, ERMor1.interp_oneN]
  rw [heq]
  have h : (ctx 0 + 1) * (ctx 1 + 1) =
      ctx 0 * ctx 1 + (ctx 0 + ctx 1 + 1) := by ring
  rw [h, Nat.add_sub_cancel_left]
  omega

/-- Sign function indicator: `signN.interp ![x] = 1` if `x ≥ 1`
and `0` if `x = 0`.  Implemented as `1 - (1 - x)`. -/
def ERMor1.signN : ERMor1 1 :=
  ERMor1.comp ERMor1.subSwap fun i => match i with
    | ⟨0, _⟩ => ERMor1.boolNot
    | ⟨1, _⟩ => ERMor1.oneN 1

/-- Interpretation of `signN`: `1 - (1 - ctx 0)`. -/
@[simp] theorem ERMor1.interp_signN (ctx : Fin 1 → ℕ) :
    ERMor1.signN.interp ctx = 1 - (1 - ctx 0) := by
  have heq : ERMor1.signN.interp ctx =
      1 - (1 - ctx 0) := by
    unfold ERMor1.signN
    simp only [ERMor1.interp_comp, ERMor1.interp_subSwap,
      ERMor1.interp_boolNot, ERMor1.interp_oneN]
  exact heq

/-- Strict less-than indicator: `ltN.interp ![a, b] = 1` if
`a < b`, else `0`.  Implemented as `signN (b - a)`. -/
def ERMor1.ltN : ERMor1 2 :=
  ERMor1.comp ERMor1.signN fun (_ : Fin 1) => ERMor1.subSwap

/-- Interpretation of `ltN`: indicator of `ctx 0 < ctx 1`. -/
@[simp] theorem ERMor1.interp_ltN (ctx : Fin 2 → ℕ) :
    ERMor1.ltN.interp ctx =
      if ctx 0 < ctx 1 then 1 else 0 := by
  have heq : ERMor1.ltN.interp ctx =
      1 - (1 - (ctx 1 - ctx 0)) := by
    unfold ERMor1.ltN
    simp only [ERMor1.interp_comp, ERMor1.interp_signN,
      ERMor1.interp_subSwap]
  rw [heq]
  split_ifs with h
  · have h1 : 1 ≤ ctx 1 - ctx 0 := Nat.sub_pos_of_lt h
    omega
  · have h1 : ctx 1 ≤ ctx 0 := Nat.not_lt.mp h
    have h2 : ctx 1 - ctx 0 = 0 := Nat.sub_eq_zero_of_le h1
    rw [h2]

/-- Conditional selector with Boolean switch in slot 0,
`then`-branch in slot 1, `else`-branch in slot 2.  When the
switch is `1`, returns slot 1; when it is `0`, returns slot 2;
otherwise returns a well-defined but unspecified value. -/
def ERMor1.condN : ERMor1 3 :=
  ERMor1.comp ERMor1.addN fun i => match i with
    | ⟨0, _⟩ =>
        ERMor1.comp ERMor1.mulN fun j => match j with
          | ⟨0, _⟩ => ERMor1.proj 0
          | ⟨1, _⟩ => ERMor1.proj 1
    | ⟨1, _⟩ =>
        ERMor1.comp ERMor1.mulN fun j => match j with
          | ⟨0, _⟩ =>
              ERMor1.comp ERMor1.boolNot
                fun (_ : Fin 1) => ERMor1.proj 0
          | ⟨1, _⟩ => ERMor1.proj 2

/-- Interpretation of `condN` as the arithmetic expression
`b * t + (1 - b) * f`. -/
@[simp] theorem ERMor1.interp_condN (ctx : Fin 3 → ℕ) :
    ERMor1.condN.interp ctx =
      ctx 0 * ctx 1 + (1 - ctx 0) * ctx 2 := by
  have heq : ERMor1.condN.interp ctx =
      ctx 0 * ctx 1 + (1 - ctx 0) * ctx 2 := by
    unfold ERMor1.condN
    simp only [ERMor1.interp_comp, ERMor1.interp_addN,
      ERMor1.interp_mulN, ERMor1.interp_boolNot,
      ERMor1.interp_proj]
  exact heq

/-- Under the assumption that `ctx 0 ∈ {0, 1}`, `condN`
computes the Boolean conditional. -/
theorem ERMor1.condN_boolean (ctx : Fin 3 → ℕ)
    (hb : ctx 0 ≤ 1) :
    ERMor1.condN.interp ctx =
      if ctx 0 = 1 then ctx 1 else ctx 2 := by
  rw [ERMor1.interp_condN]
  rcases Nat.lt_or_ge (ctx 0) 1 with h0 | h1
  · have hz : ctx 0 = 0 := Nat.lt_one_iff.mp h0
    rw [hz]
    simp
  · have h_eq : ctx 0 = 1 := Nat.le_antisymm hb h1
    rw [h_eq]
    simp

/-- ER-derived Szudzik pairing.  Interpretation at
`![x, y]` equals `Nat.pair x y`. -/
def ERMor1.natPair : ERMor1 2 :=
  ERMor1.comp ERMor1.condN fun i => match i with
    | ⟨0, _⟩ => ERMor1.ltN
    | ⟨1, _⟩ =>
        ERMor1.comp ERMor1.addN fun j => match j with
          | ⟨0, _⟩ =>
              ERMor1.comp ERMor1.mulN fun k => match k with
                | ⟨0, _⟩ => ERMor1.proj 1
                | ⟨1, _⟩ => ERMor1.proj 1
          | ⟨1, _⟩ => ERMor1.proj 0
    | ⟨2, _⟩ =>
        ERMor1.comp ERMor1.addN fun j => match j with
          | ⟨0, _⟩ =>
              ERMor1.comp ERMor1.addN fun k => match k with
                | ⟨0, _⟩ =>
                    ERMor1.comp ERMor1.mulN fun l =>
                      match l with
                      | ⟨0, _⟩ => ERMor1.proj 0
                      | ⟨1, _⟩ => ERMor1.proj 0
                | ⟨1, _⟩ => ERMor1.proj 0
          | ⟨1, _⟩ => ERMor1.proj 1

/-- Interpretation of `natPair` agrees with mathlib's
`Nat.pair`. -/
@[simp] theorem ERMor1.interp_natPair (x y : ℕ) :
    ERMor1.natPair.interp ![x, y] = Nat.pair x y := by
  have hlt :
      ERMor1.ltN.interp ![x, y] =
        if x < y then 1 else 0 := by
    rw [ERMor1.interp_ltN]
    simp
  have hb : ERMor1.ltN.interp ![x, y] ≤ 1 := by
    rw [hlt]; split_ifs <;> simp
  have hunf : ERMor1.natPair.interp ![x, y] =
      ERMor1.condN.interp
        ![ERMor1.ltN.interp ![x, y],
          y * y + x, x * x + x + y] := by
    change ERMor1.condN.interp _ = ERMor1.condN.interp _
    congr 1
    funext i
    match i with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ =>
      change ERMor1.addN.interp _ = _
      rw [ERMor1.interp_addN]
      change ERMor1.mulN.interp _ + _ = _
      rw [ERMor1.interp_mulN]
      rfl
    | ⟨2, _⟩ =>
      change ERMor1.addN.interp _ = _
      rw [ERMor1.interp_addN]
      change ERMor1.addN.interp _ + _ = _
      rw [ERMor1.interp_addN]
      change ERMor1.mulN.interp _ + _ + _ = _
      rw [ERMor1.interp_mulN]
      rfl
  rw [hunf, ERMor1.condN_boolean _ hb]
  change (if (![ERMor1.ltN.interp ![x, y],
              y * y + x, x * x + x + y] : Fin 3 → ℕ) 0 = 1
          then (![ERMor1.ltN.interp ![x, y],
              y * y + x, x * x + x + y] : Fin 3 → ℕ) 1
          else (![ERMor1.ltN.interp ![x, y],
              y * y + x, x * x + x + y] : Fin 3 → ℕ) 2) =
        Nat.pair x y
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
    hlt]
  unfold Nat.pair
  by_cases hxy : x < y
  · simp [hxy]
  · simp [hxy]

/-- Non-strict less-than-or-equal indicator:
`leN.interp ![a, b] = 1` iff `a ≤ b`, else `0`.  Implemented
as `boolNot (ltN b a)`. -/
def ERMor1.leN : ERMor1 2 :=
  ERMor1.comp ERMor1.boolNot fun (_ : Fin 1) =>
    ERMor1.comp ERMor1.ltN fun i => match i with
      | ⟨0, _⟩ => ERMor1.proj 1
      | ⟨1, _⟩ => ERMor1.proj 0

/-- Interpretation of `leN`: 0/1 indicator for `ctx 0 ≤ ctx 1`. -/
@[simp] theorem ERMor1.interp_leN (ctx : Fin 2 → ℕ) :
    ERMor1.leN.interp ctx =
      if ctx 0 ≤ ctx 1 then 1 else 0 := by
  have heq : ERMor1.leN.interp ctx =
      1 - ERMor1.ltN.interp ![ctx 1, ctx 0] := by
    change 1 - ERMor1.ltN.interp _ = _
    congr 1
  rw [heq, ERMor1.interp_ltN]
  by_cases h : ctx 0 ≤ ctx 1
  · have : ¬ ctx 1 < ctx 0 := Nat.not_lt.mpr h
    simp [this, h]
  · push_neg at h
    simp [h, Nat.not_le.mpr h]

/-- Counting body for `natSqrt`: at context `![k, n]`,
returns `1` if `(k + 1) * (k + 1) ≤ n`, else `0`. -/
def ERMor1.sqrtBody : ERMor1 2 :=
  ERMor1.comp ERMor1.leN fun i => match i with
    | ⟨0, _⟩ =>
        ERMor1.comp ERMor1.mulN fun j => match j with
          | ⟨0, _⟩ =>
              ERMor1.comp ERMor1.succ
                fun (_ : Fin 1) => ERMor1.proj 0
          | ⟨1, _⟩ =>
              ERMor1.comp ERMor1.succ
                fun (_ : Fin 1) => ERMor1.proj 0
    | ⟨1, _⟩ => ERMor1.proj 1

/-- Interpretation of `sqrtBody`. -/
@[simp] theorem ERMor1.interp_sqrtBody (ctx : Fin 2 → ℕ) :
    ERMor1.sqrtBody.interp ctx =
      if (ctx 0 + 1) * (ctx 0 + 1) ≤ ctx 1 then 1 else 0 := by
  have heq : ERMor1.sqrtBody.interp ctx =
      ERMor1.leN.interp ![(ctx 0 + 1) * (ctx 0 + 1), ctx 1] := by
    change ERMor1.leN.interp _ = ERMor1.leN.interp _
    congr 1
    funext i
    match i with
    | ⟨0, _⟩ =>
      rw [ERMor1.interp_comp, ERMor1.interp_mulN]
      rfl
    | ⟨1, _⟩ => rfl
  rw [heq, ERMor1.interp_leN]
  congr 1

/-- Integer square root as an ER term: bounded search over
`k < n` counting predicates `(k + 1) * (k + 1) ≤ n`. -/
def ERMor1.natSqrt : ERMor1 1 :=
  ERMor1.comp (ERMor1.bsum ERMor1.sqrtBody) fun i =>
    match i with
      | ⟨0, _⟩ => ERMor1.proj 0
      | ⟨1, _⟩ => ERMor1.proj 0

/-- Auxiliary: the `bsum` body summed over `[0, n)` equals
`Nat.sqrt n`.  Proof uses `Nat.sqrt_le_self` to bound the
count. -/
theorem natBSum_sqrtBody_eq (n : ℕ) :
    natBSum n (fun k =>
      if (k + 1) * (k + 1) ≤ n then 1 else 0) = Nat.sqrt n := by
  induction n with
  | zero => rfl
  | succ m ih =>
    -- The sum up to bound (m+1) counts how many k in [0, m+1) have
    -- (k+1)² ≤ m+1.  This equals Nat.sqrt (m+1).
    -- Use the characterization: Nat.sqrt n is the greatest k with
    -- k² ≤ n.
    set N := m + 1
    clear ih
    have hle : ∀ k, (k + 1) * (k + 1) ≤ N ↔ k + 1 ≤ Nat.sqrt N := by
      intro k
      rw [Nat.le_sqrt]
    have hsqrt_le : Nat.sqrt N ≤ N := Nat.sqrt_le_self N
    have hmain : ∀ B : ℕ, B ≤ N →
        natBSum B (fun k =>
          if (k + 1) * (k + 1) ≤ N then 1 else 0) =
        min B (Nat.sqrt N) := by
      intro B hB
      induction B with
      | zero => rfl
      | succ b ihb =>
        have hb' : b ≤ N := Nat.le_of_succ_le hB
        change natBSum b _ + _ = _
        rw [ihb hb']
        by_cases hcond : (b + 1) * (b + 1) ≤ N
        · simp only [hcond, if_true]
          have hkle : b + 1 ≤ Nat.sqrt N := (hle b).mp hcond
          have : min b (Nat.sqrt N) = b := by
            exact Nat.min_eq_left (Nat.le_of_succ_le hkle)
          rw [this]
          exact (Nat.min_eq_left hkle).symm
        · simp only [hcond, if_false]
          rw [Nat.add_zero]
          have hnlt : ¬ (b + 1 ≤ Nat.sqrt N) := fun h =>
            hcond ((hle b).mpr h)
          have hge : Nat.sqrt N ≤ b := Nat.lt_succ_iff.mp
            (Nat.lt_of_not_le hnlt)
          rw [Nat.min_eq_right hge, Nat.min_eq_right
            (Nat.le_succ_of_le hge)]
    have := hmain N (Nat.le_refl N)
    rw [this, Nat.min_eq_right hsqrt_le]

/-- Interpretation of `natSqrt`. -/
@[simp] theorem ERMor1.interp_natSqrt (ctx : Fin 1 → ℕ) :
    ERMor1.natSqrt.interp ctx = Nat.sqrt (ctx 0) := by
  have hstep : ERMor1.natSqrt.interp ctx =
      natBSum (ctx 0) (fun k =>
        if (k + 1) * (k + 1) ≤ ctx 0 then 1 else 0) := by
    change (ERMor1.bsum ERMor1.sqrtBody).interp _ = _
    rw [ERMor1.interp_bsum]
    congr 1
    funext k
    rw [ERMor1.interp_sqrtBody]
    rfl
  rw [hstep, natBSum_sqrtBody_eq]

/-- ER term computing the first component of `Nat.unpair n`. -/
def ERMor1.natUnpairFst : ERMor1 1 :=
  ERMor1.comp ERMor1.condN fun i => match i with
    | ⟨0, _⟩ =>
        ERMor1.comp ERMor1.ltN fun j => match j with
          | ⟨0, _⟩ =>
              ERMor1.comp ERMor1.sub fun k => match k with
                | ⟨0, _⟩ => ERMor1.proj 0
                | ⟨1, _⟩ =>
                    ERMor1.comp ERMor1.mulN fun l => match l with
                      | ⟨0, _⟩ => ERMor1.natSqrt
                      | ⟨1, _⟩ => ERMor1.natSqrt
          | ⟨1, _⟩ => ERMor1.natSqrt
    | ⟨1, _⟩ =>
        ERMor1.comp ERMor1.sub fun k => match k with
          | ⟨0, _⟩ => ERMor1.proj 0
          | ⟨1, _⟩ =>
              ERMor1.comp ERMor1.mulN fun l => match l with
                | ⟨0, _⟩ => ERMor1.natSqrt
                | ⟨1, _⟩ => ERMor1.natSqrt
    | ⟨2, _⟩ => ERMor1.natSqrt

/-- ER term computing the second component of `Nat.unpair n`. -/
def ERMor1.natUnpairSnd : ERMor1 1 :=
  ERMor1.comp ERMor1.condN fun i => match i with
    | ⟨0, _⟩ =>
        ERMor1.comp ERMor1.ltN fun j => match j with
          | ⟨0, _⟩ =>
              ERMor1.comp ERMor1.sub fun k => match k with
                | ⟨0, _⟩ => ERMor1.proj 0
                | ⟨1, _⟩ =>
                    ERMor1.comp ERMor1.mulN fun l => match l with
                      | ⟨0, _⟩ => ERMor1.natSqrt
                      | ⟨1, _⟩ => ERMor1.natSqrt
          | ⟨1, _⟩ => ERMor1.natSqrt
    | ⟨1, _⟩ => ERMor1.natSqrt
    | ⟨2, _⟩ =>
        ERMor1.comp ERMor1.sub fun k => match k with
          | ⟨0, _⟩ =>
              ERMor1.comp ERMor1.sub fun l => match l with
                | ⟨0, _⟩ => ERMor1.proj 0
                | ⟨1, _⟩ =>
                    ERMor1.comp ERMor1.mulN fun m => match m with
                      | ⟨0, _⟩ => ERMor1.natSqrt
                      | ⟨1, _⟩ => ERMor1.natSqrt
          | ⟨1, _⟩ => ERMor1.natSqrt

/-- Interpretation of `natUnpairFst` agrees with the first
component of `Nat.unpair`. -/
@[simp] theorem ERMor1.interp_natUnpairFst (n : ℕ) :
    ERMor1.natUnpairFst.interp ![n] = (Nat.unpair n).1 := by
  set s := Nat.sqrt n
  have hs : ERMor1.natSqrt.interp ![n] = s := by
    rw [ERMor1.interp_natSqrt]
    rfl
  have hlt :
      ERMor1.ltN.interp ![n - s * s, s] =
        if n - s * s < s then 1 else 0 := by
    rw [ERMor1.interp_ltN]
    rfl
  have hb :
      ERMor1.ltN.interp ![n - s * s, s] ≤ 1 := by
    rw [hlt]; split_ifs <;> simp
  have hunf : ERMor1.natUnpairFst.interp ![n] =
      ERMor1.condN.interp
        ![ERMor1.ltN.interp ![n - s * s, s],
          n - s * s, s] := by
    change ERMor1.condN.interp _ = ERMor1.condN.interp _
    congr 1
    funext i
    match i with
    | ⟨0, _⟩ =>
      rw [ERMor1.interp_comp]
      change ERMor1.ltN.interp _ = _
      congr 1
      funext j
      match j with
      | ⟨0, _⟩ =>
        rw [ERMor1.interp_comp, ERMor1.interp_sub]
        change n - ERMor1.mulN.interp _ = _
        rw [ERMor1.interp_mulN]
        rw [show ERMor1.natSqrt.interp ![n] = s from hs]
        rfl
      | ⟨1, _⟩ => exact hs
    | ⟨1, _⟩ =>
      rw [ERMor1.interp_comp, ERMor1.interp_sub]
      change n - ERMor1.mulN.interp _ = _
      rw [ERMor1.interp_mulN]
      rw [show ERMor1.natSqrt.interp ![n] = s from hs]
      rfl
    | ⟨2, _⟩ => exact hs
  rw [hunf, ERMor1.condN_boolean _ hb]
  change (if (![ERMor1.ltN.interp ![n - s * s, s],
              n - s * s, s] : Fin 3 → ℕ) 0 = 1
          then (![ERMor1.ltN.interp ![n - s * s, s],
              n - s * s, s] : Fin 3 → ℕ) 1
          else (![ERMor1.ltN.interp ![n - s * s, s],
              n - s * s, s] : Fin 3 → ℕ) 2) =
        (Nat.unpair n).1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
    hlt]
  unfold Nat.unpair
  change (if (if n - s * s < s then 1 else 0 : ℕ) = 1
          then n - s * s else s) =
        (if n - s * s < s then (n - s * s, s)
          else (s, n - s * s - s)).1
  by_cases h : n - s * s < s
  · rw [if_pos h, if_pos h]
    simp
  · rw [if_neg h, if_neg h]
    simp

/-- Interpretation of `natUnpairSnd` agrees with the second
component of `Nat.unpair`. -/
@[simp] theorem ERMor1.interp_natUnpairSnd (n : ℕ) :
    ERMor1.natUnpairSnd.interp ![n] = (Nat.unpair n).2 := by
  set s := Nat.sqrt n
  have hs : ERMor1.natSqrt.interp ![n] = s := by
    rw [ERMor1.interp_natSqrt]
    rfl
  have hlt :
      ERMor1.ltN.interp ![n - s * s, s] =
        if n - s * s < s then 1 else 0 := by
    rw [ERMor1.interp_ltN]
    rfl
  have hb :
      ERMor1.ltN.interp ![n - s * s, s] ≤ 1 := by
    rw [hlt]; split_ifs <;> simp
  have hunf : ERMor1.natUnpairSnd.interp ![n] =
      ERMor1.condN.interp
        ![ERMor1.ltN.interp ![n - s * s, s],
          s, n - s * s - s] := by
    change ERMor1.condN.interp _ = ERMor1.condN.interp _
    congr 1
    funext i
    match i with
    | ⟨0, _⟩ =>
      rw [ERMor1.interp_comp]
      change ERMor1.ltN.interp _ = _
      congr 1
      funext j
      match j with
      | ⟨0, _⟩ =>
        rw [ERMor1.interp_comp, ERMor1.interp_sub]
        change n - ERMor1.mulN.interp _ = _
        rw [ERMor1.interp_mulN]
        rw [show ERMor1.natSqrt.interp ![n] = s from hs]
        rfl
      | ⟨1, _⟩ => exact hs
    | ⟨1, _⟩ => exact hs
    | ⟨2, _⟩ =>
      rw [ERMor1.interp_comp, ERMor1.interp_sub]
      rw [show
          ERMor1.natSqrt.interp ![n] = s from hs]
      change n - ERMor1.mulN.interp _ - s = _
      rw [ERMor1.interp_mulN, hs]
      rfl
  rw [hunf, ERMor1.condN_boolean _ hb]
  change (if (![ERMor1.ltN.interp ![n - s * s, s],
              s, n - s * s - s] : Fin 3 → ℕ) 0 = 1
          then (![ERMor1.ltN.interp ![n - s * s, s],
              s, n - s * s - s] : Fin 3 → ℕ) 1
          else (![ERMor1.ltN.interp ![n - s * s, s],
              s, n - s * s - s] : Fin 3 → ℕ) 2) =
        (Nat.unpair n).2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
    hlt]
  unfold Nat.unpair
  change (if (if n - s * s < s then 1 else 0 : ℕ) = 1
          then s else n - s * s - s) =
        (if n - s * s < s then (n - s * s, s)
          else (s, n - s * s - s)).2
  by_cases h : n - s * s < s
  · rw [if_pos h, if_pos h]
    simp
  · rw [if_neg h, if_neg h]
    simp

/-- Round-trip: unpacking the first component of
`natPair x y` recovers `x`. -/
@[simp] theorem ERMor1.natUnpairFst_pair (x y : ℕ) :
    ERMor1.natUnpairFst.interp
        ![ERMor1.natPair.interp ![x, y]] = x := by
  rw [ERMor1.interp_natPair, ERMor1.interp_natUnpairFst,
    Nat.unpair_pair]

/-- Round-trip: unpacking the second component of
`natPair x y` recovers `y`. -/
@[simp] theorem ERMor1.natUnpairSnd_pair (x y : ℕ) :
    ERMor1.natUnpairSnd.interp
        ![ERMor1.natPair.interp ![x, y]] = y := by
  rw [ERMor1.interp_natPair, ERMor1.interp_natUnpairSnd,
    Nat.unpair_pair]

/-- Body of the `bsum` used to define `div`.  At context
`![k, a, b]` returns `1` if `(k + 1) * b ≤ a`, else `0`. -/
def ERMor1.divBody : ERMor1 3 :=
  ERMor1.comp ERMor1.leN fun i => match i with
    | ⟨0, _⟩ =>
        ERMor1.comp ERMor1.mulN fun j => match j with
          | ⟨0, _⟩ =>
              ERMor1.comp ERMor1.succ
                fun (_ : Fin 1) => ERMor1.proj 0
          | ⟨1, _⟩ => ERMor1.proj 2
    | ⟨1, _⟩ => ERMor1.proj 1

/-- Interpretation of `divBody`. -/
@[simp] theorem ERMor1.interp_divBody (ctx : Fin 3 → ℕ) :
    ERMor1.divBody.interp ctx =
      if (ctx 0 + 1) * ctx 2 ≤ ctx 1 then 1 else 0 := by
  have heq : ERMor1.divBody.interp ctx =
      ERMor1.leN.interp ![(ctx 0 + 1) * ctx 2, ctx 1] := by
    change ERMor1.leN.interp _ = ERMor1.leN.interp _
    congr 1
    funext i
    match i with
    | ⟨0, _⟩ =>
      rw [ERMor1.interp_comp, ERMor1.interp_mulN]
      rfl
    | ⟨1, _⟩ => rfl
  rw [heq, ERMor1.interp_leN]
  congr 1

/-- Auxiliary: when `b ≥ 1`, counting `k < B` with
`(k + 1) * b ≤ a` yields `min B (a / b)`.  Proof by
induction on `B`. -/
theorem natBSum_divBody_eq_min (a b B : ℕ) (hb : 1 ≤ b) :
    natBSum B (fun k =>
      if (k + 1) * b ≤ a then 1 else 0) =
    min B (a / b) := by
  induction B with
  | zero => rfl
  | succ m ih =>
    change natBSum m _ + _ = _
    rw [ih]
    have hle : ∀ k, (k + 1) * b ≤ a ↔ k + 1 ≤ a / b := by
      intro k
      exact (Nat.le_div_iff_mul_le hb).symm
    by_cases hcond : (m + 1) * b ≤ a
    · simp only [hcond, if_true]
      have hkle : m + 1 ≤ a / b := (hle m).mp hcond
      rw [Nat.min_eq_left (Nat.le_of_succ_le hkle),
        Nat.min_eq_left hkle]
    · simp only [hcond, if_false]
      rw [Nat.add_zero]
      have hnlt : ¬ (m + 1 ≤ a / b) := fun h =>
        hcond ((hle m).mpr h)
      have hge : a / b ≤ m := Nat.lt_succ_iff.mp
        (Nat.lt_of_not_le hnlt)
      rw [Nat.min_eq_right hge, Nat.min_eq_right
        (Nat.le_succ_of_le hge)]

/-- ER-derived integer division `a / b`, matching `Nat.div`
(in particular `a / 0 = 0`).  Counts `k < a` with
`(k + 1) * b ≤ a`, then multiplies by the sign of `b` so that
`b = 0` returns `0`. -/
def ERMor1.div : ERMor1 2 :=
  ERMor1.comp ERMor1.mulN fun i => match i with
    | ⟨0, _⟩ =>
        ERMor1.comp ERMor1.signN
          fun (_ : Fin 1) => ERMor1.proj 1
    | ⟨1, _⟩ =>
        ERMor1.comp (ERMor1.bsum ERMor1.divBody)
          fun j => match j with
            | ⟨0, _⟩ => ERMor1.proj 0
            | ⟨1, _⟩ => ERMor1.proj 0
            | ⟨2, _⟩ => ERMor1.proj 1

/-- Interpretation of `div`: agrees with `Nat.div`. -/
@[simp] theorem ERMor1.interp_div (a b : ℕ) :
    ERMor1.div.interp ![a, b] = a / b := by
  have hsign : ERMor1.signN.interp ![b] = 1 - (1 - b) := by
    rw [ERMor1.interp_signN]
    rfl
  have hbsum : (ERMor1.bsum ERMor1.divBody).interp
      ![a, a, b] =
      natBSum a (fun k =>
        if (k + 1) * b ≤ a then 1 else 0) := by
    rw [ERMor1.interp_bsum]
    congr 1
    funext k
    rw [ERMor1.interp_divBody]
    rfl
  have hunf : ERMor1.div.interp ![a, b] =
      ERMor1.signN.interp ![b] *
        (ERMor1.bsum ERMor1.divBody).interp ![a, a, b] := by
    change ERMor1.mulN.interp _ = _
    rw [ERMor1.interp_mulN]
    rfl
  rw [hunf, hsign, hbsum]
  rcases Nat.eq_zero_or_pos b with hb0 | hbpos
  · subst hb0
    simp
  · have hb : 1 ≤ b := hbpos
    rw [natBSum_divBody_eq_min a b a hb]
    have hle : a / b ≤ a := Nat.div_le_self a b
    rw [Nat.min_eq_right hle]
    have h1 : 1 - (1 - b) = 1 := by omega
    rw [h1, Nat.one_mul]

/-- ER-derived integer modulo `a % b`, defined as
`a - (a / b) * b`.  Matches `Nat.mod` in particular for
`b = 0`, where `a % 0 = a`. -/
def ERMor1.mod : ERMor1 2 :=
  ERMor1.comp ERMor1.sub fun i => match i with
    | ⟨0, _⟩ => ERMor1.proj 0
    | ⟨1, _⟩ =>
        ERMor1.comp ERMor1.mulN fun j => match j with
          | ⟨0, _⟩ => ERMor1.div
          | ⟨1, _⟩ => ERMor1.proj 1

/-- Interpretation of `mod`: agrees with `Nat.mod`. -/
@[simp] theorem ERMor1.interp_mod (a b : ℕ) :
    ERMor1.mod.interp ![a, b] = a % b := by
  have hdiv : ERMor1.div.interp ![a, b] = a / b :=
    ERMor1.interp_div a b
  have hunf : ERMor1.mod.interp ![a, b] =
      a - (a / b) * b := by
    unfold ERMor1.mod
    rw [ERMor1.interp_comp, ERMor1.interp_sub]
    change (![a, b] : Fin 2 → ℕ) 0 -
        ERMor1.mulN.interp _ = _
    rw [ERMor1.interp_mulN]
    change a - ERMor1.div.interp _ * _ = _
    rw [hdiv]
    rfl
  rw [hunf]
  have hadd : a / b * b + a % b = a := Nat.div_add_mod' a b
  omega

/-- Gödel's β-function as an `ERMor1 3` term:
`β(a, b, i) = a mod (1 + (i + 1) * b)`.  Constant-depth
arithmetic; no iteration.  Used by `natRec` (Task 12e) to
extract values from a Gödel-encoded trace of a
primitive-recursion computation. -/
def ERMor1.beta : ERMor1 3 :=
  ERMor1.comp ERMor1.mod fun i => match i with
    | ⟨0, _⟩ => ERMor1.proj 0
    | ⟨1, _⟩ =>
        ERMor1.comp ERMor1.succ fun (_ : Fin 1) =>
          ERMor1.comp ERMor1.mulN fun j => match j with
            | ⟨0, _⟩ =>
                ERMor1.comp ERMor1.succ fun (_ : Fin 1) =>
                  ERMor1.proj 2
            | ⟨1, _⟩ => ERMor1.proj 1

/-- Interpretation of `beta`: agrees with
`a mod (1 + (i + 1) * b)`. -/
@[simp] theorem ERMor1.interp_beta (a b i : ℕ) :
    (ERMor1.beta).interp ![a, b, i] =
      a % (1 + (i + 1) * b) := by
  have hunf : (ERMor1.beta).interp ![a, b, i] =
      ERMor1.mod.interp ![a, 1 + (i + 1) * b] := by
    change ERMor1.mod.interp _ = ERMor1.mod.interp _
    congr 1
    funext k
    match k with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ =>
      simp
      omega
  rw [hunf, ERMor1.interp_mod]

/-- Meta-level Gödel β-existence: for any finite
ℕ-sequence there exist parameters `(a, b)` such that
`a mod (1 + (i + 1) * b) = s i` for every `i < N`.  Derived
from mathlib's `Nat.beta_unbeta_coe`. -/
theorem Nat.beta_exists {N : ℕ} (s : Fin N → ℕ) :
    ∃ a b : ℕ, ∀ i : Fin N,
      a % (1 + (i.val + 1) * b) = s i := by
  let l : List ℕ := List.ofFn s
  have hlen : l.length = N := List.length_ofFn
  let n : ℕ := Nat.unbeta l
  refine ⟨n.unpair.1, n.unpair.2, ?_⟩
  intro i
  have hi : i.val < l.length := by
    rw [hlen]; exact i.isLt
  let j : Fin l.length := ⟨i.val, hi⟩
  have hb : Nat.beta n ↑j = l[j] :=
    Nat.beta_unbeta_coe l j
  have hj : (↑j : ℕ) = i.val := rfl
  have hget : l[j] = s i := by
    change (List.ofFn s)[i.val]'(by
      rw [List.length_ofFn]; exact i.isLt) = s i
    rw [List.getElem_ofFn]
  have hbeta_def : Nat.beta n ↑j =
      n.unpair.1 % ((↑j + 1) * n.unpair.2 + 1) := rfl
  have hcomm : 1 + (i.val + 1) * n.unpair.2 =
      (i.val + 1) * n.unpair.2 + 1 := by omega
  rw [hcomm, ← hj, ← hbeta_def, hb, hget]

/-- Meta-level Gödel β-existence with an explicit elementary
bound on the witness pair.  Given a sequence `s : Fin N → ℕ`
and any `M` with `s i ≤ M` for all `i`, set
`K := max N M + 1`, `b := K !`, and
`P := (N * b + 1) ^ N`.  Then there exist `a < P`, `b = K !`
such that `a % (1 + (i.val + 1) * b) = s i` for all `i`.
The bound uses only `Nat.factorial`, multiplication, addition,
and exponentiation, hence is ER-derivable.  Downstream
bounded-search combinators use `P` and `b` as search
ranges when recovering β-witnesses. -/
theorem Nat.bounded_beta_exists {N : ℕ} (s : Fin N → ℕ)
    (M : ℕ) (hM : ∀ i : Fin N, s i ≤ M) :
    ∃ a b : ℕ,
      b = (max N M + 1).factorial ∧
      a < (N * b + 1) ^ N ∧
      ∀ i : Fin N,
        a % (1 + (i.val + 1) * b) = s i := by
  set K : ℕ := max N M + 1 with hK_def
  set b : ℕ := K.factorial with hb_def
  have hb_pos : 0 < b := Nat.factorial_pos K
  let c : Fin N → ℕ := fun i => (i.val + 1) * b + 1
  have hc_ne : ∀ i ∈ (Finset.univ : Finset (Fin N)),
      c i ≠ 0 := by
    intro i _
    have : 0 < c i := Nat.succ_pos _
    exact Nat.pos_iff_ne_zero.mp this
  have hK_upper : ∀ i : Fin N, i.val < K := by
    intro i
    have hiN : i.val < N := i.isLt
    have : i.val < max N M + 1 := by
      have : i.val ≤ max N M :=
        le_trans (Nat.le_of_lt hiN) (le_max_left _ _)
      exact Nat.lt_succ_of_le this
    simpa [hK_def] using this
  have hsub_dvd_b : ∀ i j : Fin N, i.val < j.val →
      (j.val + 1) - (i.val + 1) ∣ b := by
    intro i j hij
    have hjK : j.val + 1 ≤ K := hK_upper j
    have hjK' : j.val + 1 - (i.val + 1) ≤ K :=
      le_trans (Nat.sub_le _ _) hjK
    have hpos : 0 < j.val + 1 - (i.val + 1) := by
      have : i.val + 1 < j.val + 1 := Nat.succ_lt_succ hij
      exact Nat.sub_pos_of_lt this
    exact Nat.dvd_factorial hpos hjK'
  have hpairwise :
      Set.Pairwise
        ((Finset.univ : Finset (Fin N)) : Set (Fin N))
        (fun i j => Nat.Coprime (c i) (c j)) := by
    intro i _ j _ hij
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · have hlt' : i.val < j.val := Fin.val_fin_lt.mpr hlt
      have hd : (j.val + 1) - (i.val + 1) ∣ b :=
        hsub_dvd_b i j hlt'
      exact Nat.coprime_mul_succ hd
    · have hlt' : j.val < i.val := Fin.val_fin_lt.mpr hgt
      have hd : (i.val + 1) - (j.val + 1) ∣ b :=
        hsub_dvd_b j i hlt'
      exact (Nat.coprime_mul_succ hd).symm
  let cr := Nat.chineseRemainderOfFinset
      (fun i : Fin N => s i) c Finset.univ hc_ne hpairwise
  set a : ℕ := (cr : ℕ) with ha_def
  have hcr_lt : a < ∏ i ∈ Finset.univ, c i := by
    simpa [ha_def] using
      Nat.chineseRemainderOfFinset_lt_prod
        (fun i : Fin N => s i) c hc_ne hpairwise
  have hc_le : ∀ i ∈ (Finset.univ : Finset (Fin N)),
      c i ≤ N * b + 1 := by
    intro i _
    have hiN : i.val + 1 ≤ N := i.isLt
    have : (i.val + 1) * b ≤ N * b :=
      Nat.mul_le_mul_right b hiN
    exact Nat.add_le_add_right this 1
  have hprod_le :
      ∏ i ∈ (Finset.univ : Finset (Fin N)), c i ≤
        (N * b + 1) ^ N := by
    have hstep :
        ∏ i ∈ (Finset.univ : Finset (Fin N)), c i ≤
          ∏ _i ∈ (Finset.univ : Finset (Fin N)),
              (N * b + 1) :=
      Finset.prod_le_prod' hc_le
    have hconst :
        ∏ _i ∈ (Finset.univ : Finset (Fin N)),
            (N * b + 1) = (N * b + 1) ^ N := by
      rw [Finset.prod_const, Finset.card_univ,
        Fintype.card_fin]
    exact le_of_le_of_eq hstep hconst
  have ha_lt : a < (N * b + 1) ^ N :=
    lt_of_lt_of_le hcr_lt hprod_le
  refine ⟨a, b, rfl, ha_lt, ?_⟩
  intro i
  have hmem : i ∈ (Finset.univ : Finset (Fin N)) :=
    Finset.mem_univ i
  have hmod : a ≡ s i [MOD c i] := cr.prop i hmem
  have hsi_lt_K : s i < K := by
    have : s i ≤ max N M :=
      le_trans (hM i) (le_max_right _ _)
    exact Nat.lt_succ_of_le this
  have hsi_lt_b : s i < b := by
    have hKfact : K ≤ b := by
      simpa [hb_def] using Nat.self_le_factorial K
    exact lt_of_lt_of_le hsi_lt_K hKfact
  have hsi_lt_c : s i < c i := by
    have hbmul : b ≤ (i.val + 1) * b :=
      Nat.le_mul_of_pos_left b (Nat.succ_pos _)
    have : s i < (i.val + 1) * b :=
      lt_of_lt_of_le hsi_lt_b hbmul
    exact lt_trans this (Nat.lt_succ_self _)
  have hmod_eq : a % c i = s i :=
    Nat.mod_eq_of_modEq hmod hsi_lt_c
  have hcomm : 1 + (i.val + 1) * b = c i := by
    change 1 + (i.val + 1) * b = (i.val + 1) * b + 1
    omega
  rw [hcomm, hmod_eq]

/-- `consBound bound i` is the term substituted into slot `i`
when wrapping a `(k + 1)`-ary body into a `k`-ary term: slot
`0` is replaced by `bound`, slot `i + 1` by the projection
`proj i`. -/
def ERMor1.consBound {k : ℕ} (bound : ERMor1 k)
    (i : Fin (k + 1)) : ERMor1 k :=
  Fin.cases bound (fun j => ERMor1.proj j) i

/-- Interpretation of `consBound bound` at outer context `ctx`
equals `Fin.cons (bound.interp ctx) ctx`. -/
@[simp] theorem ERMor1.interp_consBound {k : ℕ}
    (bound : ERMor1 k) (ctx : Fin k → ℕ) :
    (fun i => (ERMor1.consBound bound i).interp ctx) =
      Fin.cons (bound.interp ctx) ctx := by
  funext i
  refine Fin.cases ?_ ?_ i
  · rfl
  · intro j
    rfl

/-- Body of the outer `bsum` used by `boundedSearch`: at
context `Fin.cons j outer_ctx`, evaluates to
`(1 - Σ_{m<j} pred m) * pred j * (j + 1)`.  Under the
assumption that `pred` is `0/1`-valued, this contributes
`j + 1` exactly at the least `j` with `pred j = 1` and `0`
everywhere else. -/
def ERMor1.searchBody {k : ℕ} (pred : ERMor1 (k + 1)) :
    ERMor1 (k + 1) :=
  ERMor1.comp ERMor1.mulN (fun i => match i with
    | ⟨0, _⟩ =>
      ERMor1.comp ERMor1.mulN (fun j => match j with
        | ⟨0, _⟩ =>
          ERMor1.comp ERMor1.boolNot (fun _ =>
            ERMor1.bsum pred)
        | ⟨1, _⟩ => pred)
    | ⟨1, _⟩ =>
      ERMor1.comp ERMor1.succ (fun _ => ERMor1.proj 0))

/-- Interpretation of `searchBody` at `Fin.cons j ctx`. -/
@[simp] theorem ERMor1.interp_searchBody {k : ℕ}
    (pred : ERMor1 (k + 1)) (j : ℕ) (ctx : Fin k → ℕ) :
    (ERMor1.searchBody pred).interp (Fin.cons j ctx) =
      (1 - natBSum j (fun m =>
          pred.interp (Fin.cons m ctx)))
        * pred.interp (Fin.cons j ctx) * (j + 1) := by
  have hcum :
      (ERMor1.bsum pred).interp (Fin.cons j ctx) =
        natBSum j (fun m => pred.interp (Fin.cons m ctx)) := by
    rw [ERMor1.interp_bsum]
    rfl
  unfold ERMor1.searchBody
  rw [ERMor1.interp_comp, ERMor1.interp_mulN]
  change ERMor1.mulN.interp _ * _ = _
  rw [ERMor1.interp_mulN]
  change (1 - (ERMor1.bsum pred).interp _) *
      pred.interp _ *
      ((Fin.cons j ctx : Fin (k + 1) → ℕ) 0 + 1) = _
  rw [hcum]
  rfl

/-- Bounded search: given a bound `bound : ERMor1 k` and a
predicate `pred : ERMor1 (k + 1)` that is `0/1`-valued, returns
the least `j < bound.interp ctx` with
`pred.interp (Fin.cons j ctx) = 1`, or `bound.interp ctx + 1`
if no such `j` exists. -/
def ERMor1.boundedSearch {k : ℕ}
    (bound : ERMor1 k) (pred : ERMor1 (k + 1)) :
    ERMor1 k :=
  ERMor1.comp ERMor1.addN (fun i => match i with
    | ⟨0, _⟩ =>
      ERMor1.comp ERMor1.sub (fun j => match j with
        | ⟨0, _⟩ =>
          ERMor1.comp (ERMor1.bsum (ERMor1.searchBody pred))
            (ERMor1.consBound bound)
        | ⟨1, _⟩ =>
          ERMor1.comp ERMor1.signN (fun _ =>
            ERMor1.comp (ERMor1.bsum pred)
              (ERMor1.consBound bound)))
    | ⟨1, _⟩ =>
      ERMor1.comp ERMor1.mulN (fun j => match j with
        | ⟨0, _⟩ =>
          ERMor1.comp ERMor1.boolNot (fun _ =>
            ERMor1.comp ERMor1.signN (fun _ =>
              ERMor1.comp (ERMor1.bsum pred)
                (ERMor1.consBound bound)))
        | ⟨1, _⟩ =>
          ERMor1.comp ERMor1.succ (fun _ => bound)))

/-- Arithmetic unfolding of `boundedSearch`: interprets to
`(S1 - hasWit) + noWit * (B + 1)`, where `S1` is the
first-witness-plus-one `bsum`, `hasWit` the sign of the total
predicate count, and `noWit = 1 - hasWit`. -/
theorem ERMor1.interp_boundedSearch_raw {k : ℕ}
    (bound : ERMor1 k) (pred : ERMor1 (k + 1))
    (ctx : Fin k → ℕ) :
    (ERMor1.boundedSearch bound pred).interp ctx =
      (natBSum (bound.interp ctx) (fun j =>
          (1 - natBSum j (fun m =>
              pred.interp (Fin.cons m ctx)))
            * pred.interp (Fin.cons j ctx) * (j + 1))
        - (1 - (1 - natBSum (bound.interp ctx)
            (fun m => pred.interp (Fin.cons m ctx)))))
      + (1 - (1 - (1 - natBSum (bound.interp ctx)
          (fun m => pred.interp (Fin.cons m ctx)))))
        * (bound.interp ctx + 1) := by
  set B := bound.interp ctx
  have hbsum_at_B :
      (ERMor1.bsum pred).interp
          (fun i => (ERMor1.consBound bound i).interp ctx) =
        natBSum B (fun m => pred.interp (Fin.cons m ctx)) := by
    rw [ERMor1.interp_consBound]
    rw [ERMor1.interp_bsum]
    rfl
  have hsearch_at_B :
      (ERMor1.bsum (ERMor1.searchBody pred)).interp
          (fun i => (ERMor1.consBound bound i).interp ctx) =
        natBSum B (fun j =>
          (1 - natBSum j (fun m =>
              pred.interp (Fin.cons m ctx)))
            * pred.interp (Fin.cons j ctx) * (j + 1)) := by
    rw [ERMor1.interp_consBound]
    rw [ERMor1.interp_bsum]
    have h0 : (Fin.cons B ctx : Fin (k + 1) → ℕ) 0 = B := rfl
    rw [h0]
    congr 1
    funext j
    have htail :
        Fin.tail (Fin.cons B ctx : Fin (k + 1) → ℕ) = ctx := by
      funext i
      simp [Fin.tail, Fin.cons_succ]
    rw [htail, ERMor1.interp_searchBody]
  have hunf :
      (ERMor1.boundedSearch bound pred).interp ctx =
        ((ERMor1.bsum (ERMor1.searchBody pred)).interp
            (fun i => (ERMor1.consBound bound i).interp ctx)
          - (1 - (1 - (ERMor1.bsum pred).interp
              (fun i => (ERMor1.consBound bound i).interp
                ctx)))) +
        (1 - (1 - (1 - (ERMor1.bsum pred).interp
            (fun i => (ERMor1.consBound bound i).interp
              ctx)))) *
          ((bound.interp ctx : ℕ).succ) := by
    unfold ERMor1.boundedSearch
    simp only [ERMor1.interp_comp, ERMor1.interp_addN,
      ERMor1.interp_sub, ERMor1.interp_mulN,
      ERMor1.interp_signN, ERMor1.interp_boolNot,
      ERMor1.interp_succ]
  rw [hunf, hbsum_at_B, hsearch_at_B]

/-- If `P` is `0/1`-valued, the total `natBSum` over `[0, B)`
reports whether at least one witness exists: nonzero iff
`∃ j < B, P j = 1`. -/
theorem natBSum_pos_iff_exists (P : ℕ → ℕ) (B : ℕ)
    (hP : ∀ j, P j ≤ 1) :
    0 < natBSum B P ↔ ∃ j, j < B ∧ P j = 1 := by
  induction B with
  | zero =>
    refine ⟨fun h => ?_, fun ⟨j, hj, _⟩ => ?_⟩
    · exact (Nat.lt_irrefl 0 h).elim
    · exact (Nat.not_lt_zero _ hj).elim
  | succ b ih =>
    change 0 < natBSum b P + P b ↔ _
    refine ⟨fun h => ?_, fun ⟨j, hj, hpj⟩ => ?_⟩
    · rcases Nat.eq_zero_or_pos (natBSum b P) with h1 | h1
      · rw [h1, Nat.zero_add] at h
        have hpb : P b = 1 :=
          Nat.le_antisymm (hP b) h
        exact ⟨b, Nat.lt_succ_self b, hpb⟩
      · rcases (ih.mp h1) with ⟨j, hj, hpj⟩
        exact ⟨j, Nat.lt_succ_of_lt hj, hpj⟩
    · rcases Nat.lt_or_ge j b with hjlt | hjge
      · have hex : ∃ j, j < b ∧ P j = 1 := ⟨j, hjlt, hpj⟩
        have : 0 < natBSum b P := ih.mpr hex
        omega
      · have : j = b := Nat.le_antisymm
          (Nat.lt_succ_iff.mp hj) hjge
        subst this
        rw [hpj]
        omega

/-- Arithmetic core lemma: when `P` is `0/1`-valued, the
"first-witness-plus-one" bsum equals `(Nat.find h) + 1` when a
witness exists, else `0`. -/
theorem natBSum_firstWitness (P : ℕ → ℕ) (B : ℕ)
    (hP : ∀ j, P j ≤ 1) :
    natBSum B (fun j =>
        (1 - natBSum j P) * P j * (j + 1)) =
      if h : ∃ j, j < B ∧ P j = 1
        then Nat.find h + 1
        else 0 := by
  induction B with
  | zero =>
    have hno : ¬ ∃ j, j < 0 ∧ P j = 1 := by
      rintro ⟨j, hj, _⟩
      exact (Nat.not_lt_zero _ hj).elim
    rw [dif_neg hno]
    rfl
  | succ b ih =>
    change natBSum b (fun j =>
        (1 - natBSum j P) * P j * (j + 1))
      + ((1 - natBSum b P) * P b * (b + 1)) = _
    rw [ih]
    by_cases hex_old : ∃ j, j < b ∧ P j = 1
    · have hex_new : ∃ j, j < b + 1 ∧ P j = 1 := by
        rcases hex_old with ⟨j, hj, hpj⟩
        exact ⟨j, Nat.lt_succ_of_lt hj, hpj⟩
      rw [dif_pos hex_old, dif_pos hex_new]
      have hfind_eq : Nat.find hex_new = Nat.find hex_old := by
        rw [Nat.find_eq_iff]
        obtain ⟨hlt, hP1⟩ := Nat.find_spec hex_old
        refine ⟨⟨Nat.lt_succ_of_lt hlt, hP1⟩, ?_⟩
        intro m hm ⟨_, hmP⟩
        have hmltb : m < b := by
          have : Nat.find hex_old < b := hlt
          omega
        exact Nat.find_min hex_old hm ⟨hmltb, hmP⟩
      rw [hfind_eq]
      have hsum_pos : 0 < natBSum b P :=
        (natBSum_pos_iff_exists P b hP).mpr hex_old
      have hcumb : 1 - natBSum b P = 0 := by omega
      rw [hcumb]
      ring
    · by_cases hpb : P b = 1
      · have hex_new : ∃ j, j < b + 1 ∧ P j = 1 :=
          ⟨b, Nat.lt_succ_self b, hpb⟩
        rw [dif_neg hex_old, dif_pos hex_new]
        have hfind_b : Nat.find hex_new = b := by
          rw [Nat.find_eq_iff]
          refine ⟨⟨Nat.lt_succ_self b, hpb⟩, ?_⟩
          intro m hm ⟨hmlt, hmP⟩
          exact hex_old ⟨m, hm, hmP⟩
        rw [hfind_b]
        have hsum_zero : natBSum b P = 0 := by
          rcases Nat.eq_zero_or_pos (natBSum b P) with h0 | h0
          · exact h0
          · exact absurd
              ((natBSum_pos_iff_exists P b hP).mp h0)
              hex_old
        rw [hsum_zero, hpb]
        ring
      · have hex_new_not : ¬ ∃ j, j < b + 1 ∧ P j = 1 := by
          rintro ⟨j, hj, hpj⟩
          rcases Nat.lt_or_ge j b with hjlt | hjge
          · exact hex_old ⟨j, hjlt, hpj⟩
          · have hjb : j = b :=
              Nat.le_antisymm (Nat.lt_succ_iff.mp hj) hjge
            subst hjb
            exact hpb hpj
        rw [dif_neg hex_old, dif_neg hex_new_not]
        have hpb0 : P b = 0 := by
          rcases Nat.lt_or_ge (P b) 1 with h | h
          · exact Nat.lt_one_iff.mp h
          · exact absurd (Nat.le_antisymm (hP b) h) hpb
        rw [hpb0]
        ring

/-- Correctness of `boundedSearch`: when `pred` is `0/1`-valued
on the relevant fibre, the search returns the least witness
below `bound` or `bound + 1` if none exists. -/
theorem ERMor1.interp_boundedSearch {k : ℕ}
    (bound : ERMor1 k) (pred : ERMor1 (k + 1))
    (ctx : Fin k → ℕ)
    (hpred : ∀ j, pred.interp (Fin.cons j ctx) ≤ 1) :
    (ERMor1.boundedSearch bound pred).interp ctx =
      if h : ∃ j, j < bound.interp ctx ∧
          (pred.interp (Fin.cons j ctx) = 1)
        then Nat.find h
        else bound.interp ctx + 1 := by
  set B := bound.interp ctx with hBdef
  set P : ℕ → ℕ := fun j => pred.interp (Fin.cons j ctx)
    with hPdef
  have hP_le : ∀ j, P j ≤ 1 := hpred
  rw [ERMor1.interp_boundedSearch_raw]
  change (natBSum B (fun j =>
            (1 - natBSum j P) * P j * (j + 1))
          - (1 - (1 - natBSum B P)))
        + (1 - (1 - (1 - natBSum B P))) * (B + 1) = _
  rw [natBSum_firstWitness P B hP_le]
  by_cases hex : ∃ j, j < B ∧ P j = 1
  · rw [dif_pos hex, dif_pos hex]
    have hsum_pos : 0 < natBSum B P :=
      (natBSum_pos_iff_exists P B hP_le).mpr hex
    have hrw_inner :
        (1 : ℕ) - (1 - (1 - natBSum B P)) = 0 := by omega
    rw [hrw_inner]
    rw [Nat.zero_mul, Nat.add_zero]
    have hrw_outer :
        (1 : ℕ) - (1 - natBSum B P) = 1 := by omega
    rw [hrw_outer]
    omega
  · rw [dif_neg hex, dif_neg hex]
    have hsum_zero : natBSum B P = 0 := by
      rcases Nat.eq_zero_or_pos (natBSum B P) with h0 | h0
      · exact h0
      · exact absurd
          ((natBSum_pos_iff_exists P B hP_le).mp h0) hex
    rw [hsum_zero]
    change 0 - (1 - (1 - 0)) + (1 - (1 - (1 - 0))) * (B + 1) =
      B + 1
    omega

/-- If `pred` holds uniquely at `j < bound`, `boundedSearch`
returns that `j`.  Used by `natRec` at Task 12e. -/
theorem ERMor1.boundedSearch_eq_unique {k : ℕ}
    (bound : ERMor1 k) (pred : ERMor1 (k + 1))
    (ctx : Fin k → ℕ) (j : ℕ)
    (hpred : ∀ m, pred.interp (Fin.cons m ctx) ≤ 1)
    (hj_lt : j < bound.interp ctx)
    (hj_pred : pred.interp (Fin.cons j ctx) = 1)
    (hj_unique : ∀ j', j' < bound.interp ctx →
      (pred.interp (Fin.cons j' ctx) = 1) →
      j' = j) :
    (ERMor1.boundedSearch bound pred).interp ctx = j := by
  have hex : ∃ m, m < bound.interp ctx ∧
      (pred.interp (Fin.cons m ctx) = 1) :=
    ⟨j, hj_lt, hj_pred⟩
  rw [ERMor1.interp_boundedSearch bound pred ctx hpred,
    dif_pos hex]
  apply Nat.find_eq_iff _ |>.mpr
  refine ⟨⟨hj_lt, hj_pred⟩, ?_⟩
  intro m hm ⟨hmlt, hmP⟩
  have hm_eq : m = j := hj_unique m hmlt hmP
  omega

/-- ER-derived minimum of two naturals:
`min.interp ![a, b] = min a b`.  Implemented as
`a - (a - b)` which equals `min a b` in ℕ. -/
def ERMor1.minN : ERMor1 2 :=
  ERMor1.comp ERMor1.sub fun i => match i with
    | ⟨0, _⟩ => ERMor1.proj 0
    | ⟨1, _⟩ =>
        ERMor1.comp ERMor1.sub fun j => match j with
          | ⟨0, _⟩ => ERMor1.proj 0
          | ⟨1, _⟩ => ERMor1.proj 1

/-- Interpretation of `minN`: `min (ctx 0) (ctx 1)`. -/
@[simp] theorem ERMor1.interp_minN (ctx : Fin 2 → ℕ) :
    ERMor1.minN.interp ctx = min (ctx 0) (ctx 1) := by
  have heq : ERMor1.minN.interp ctx =
      ctx 0 - (ctx 0 - ctx 1) := by
    unfold ERMor1.minN
    simp only [ERMor1.interp_comp, ERMor1.interp_sub,
      ERMor1.interp_proj]
  rw [heq]
  omega

/-- `natBProd n (fun i => i + 1) = n.factorial`. -/
theorem natBProd_succ_eq_factorial (n : ℕ) :
    natBProd n (fun i => i + 1) = n.factorial := by
  induction n with
  | zero => rfl
  | succ b ih =>
    change natBProd b (fun i => i + 1) * (b + 1) =
        (b + 1).factorial
    rw [ih, Nat.factorial_succ, Nat.mul_comm]

/-- Factorial as an elementary recursive term:
`factN` interprets at context `[n]` as `n.factorial`,
built via bounded product of `succ (proj 0)`. -/
def ERMor1.factN : ERMor1 1 :=
  ERMor1.bprod
    (ERMor1.comp ERMor1.succ
      (fun (_ : Fin 1) => ERMor1.proj 0))

/-- Interpretation of `factN`:
`factN.interp ![n] = n.factorial`. -/
@[simp] theorem ERMor1.interp_factN
    (ctx : Fin 1 → ℕ) :
    ERMor1.factN.interp ctx = (ctx 0).factorial := by
  change natBProd (ctx 0)
    (fun i =>
      (ERMor1.comp ERMor1.succ
        (fun (_ : Fin 1) => ERMor1.proj (k := 1) 0)).interp
          (Fin.cons i (Fin.tail ctx))) =
    (ctx 0).factorial
  have hbody : (fun i : ℕ =>
      (ERMor1.comp ERMor1.succ
        (fun (_ : Fin 1) => ERMor1.proj (k := 1) 0)).interp
          (Fin.cons i (Fin.tail ctx))) =
      (fun i => i + 1) := by
    funext i
    simp only [ERMor1.interp_comp, ERMor1.interp_succ,
      ERMor1.interp_proj, Fin.cons_zero]
  rw [hbody, natBProd_succ_eq_factorial]

/-- Power as an elementary recursive term:
`powN` interprets at context `[base, exp]` as
`base ^ exp`, built as `expER` with swapped arguments. -/
def ERMor1.powN : ERMor1 2 :=
  ERMor1.comp ERMor1.expER
    (fun i => match i with
      | ⟨0, _⟩ => ERMor1.proj 1
      | ⟨1, _⟩ => ERMor1.proj 0)

/-- Interpretation of `powN`:
`powN.interp ![base, exp] = base ^ exp`. -/
@[simp] theorem ERMor1.interp_powN
    (ctx : Fin 2 → ℕ) :
    ERMor1.powN.interp ctx = (ctx 0) ^ (ctx 1) := by
  unfold ERMor1.powN
  simp only [ERMor1.interp_comp, ERMor1.interp_expER,
    ERMor1.interp_proj]

/-! ### Bounded primitive recursion -/

/-- A bounded product equals `1` exactly when each factor
equals `1` on the interval of summation. -/
theorem natBProd_eq_one_iff_all_one (b : ℕ) (f : ℕ → ℕ) :
    natBProd b f = 1 ↔ ∀ i, i < b → f i = 1 := by
  induction b with
  | zero =>
    refine ⟨fun _ i hi => (Nat.not_lt_zero _ hi).elim,
      fun _ => rfl⟩
  | succ n ih =>
    change natBProd n f * f n = 1 ↔ _
    constructor
    · intro hmul
      have hn_one : f n = 1 :=
        (Nat.eq_one_of_mul_eq_one_left hmul)
      have hp_one : natBProd n f = 1 :=
        (Nat.eq_one_of_mul_eq_one_right hmul)
      intro i hi
      rcases Nat.lt_or_ge i n with hilt | hige
      · exact (ih.mp hp_one) i hilt
      · have hieq : i = n :=
          Nat.le_antisymm (Nat.lt_succ_iff.mp hi) hige
        rw [hieq]; exact hn_one
    · intro hall
      have hn_one : f n = 1 := hall n (Nat.lt_succ_self _)
      have hp_one : natBProd n f = 1 :=
        (ih.mpr fun i hi => hall i (Nat.lt_succ_of_lt hi))
      rw [hp_one, hn_one]

/-- Every factor in a `natBProd` of `0/1`-valued terms is
itself bounded by `1`, so the product is bounded by `1`. -/
theorem natBProd_le_one_of_body_le_one (b : ℕ) (f : ℕ → ℕ)
    (hf : ∀ i, f i ≤ 1) : natBProd b f ≤ 1 := by
  induction b with
  | zero => exact le_refl _
  | succ n ih =>
    change natBProd n f * f n ≤ 1
    calc natBProd n f * f n
        _ ≤ 1 * f n := Nat.mul_le_mul_right _ ih
        _ ≤ 1 * 1 := Nat.mul_le_mul_left _ (hf n)
        _ = 1 := Nat.one_mul _

/-- Search range for `boundedRec`: at `Fin.cons n ctx`,
evaluates to `((n + B + 3)!)^((n + B + 3)!) + 1`, where
`B := bound.interp (Fin.cons n ctx)`.  This dominates every
Szudzik-paired β-witness `(a, b)` produced by
`Nat.bounded_beta_exists` on a trace of length `n + 1` whose
values are bounded by `B`. -/
def ERMor1.boundedRecRange {k : ℕ}
    (bound : ERMor1 (k + 1)) : ERMor1 (k + 1) :=
  let K : ERMor1 (k + 1) :=
    ERMor1.comp ERMor1.succ (fun (_ : Fin 1) =>
      ERMor1.comp ERMor1.succ (fun (_ : Fin 1) =>
        ERMor1.comp ERMor1.succ (fun (_ : Fin 1) =>
          ERMor1.comp ERMor1.addN (fun i => match i with
            | ⟨0, _⟩ => ERMor1.proj 0
            | ⟨1, _⟩ => bound))))
  let Kfact : ERMor1 (k + 1) :=
    ERMor1.comp ERMor1.factN (fun (_ : Fin 1) => K)
  ERMor1.comp ERMor1.succ (fun (_ : Fin 1) =>
    ERMor1.comp ERMor1.powN (fun i => match i with
      | ⟨0, _⟩ => Kfact
      | ⟨1, _⟩ => Kfact))

/-- Interpretation of `boundedRecRange`. -/
@[simp] theorem ERMor1.interp_boundedRecRange {k : ℕ}
    (bound : ERMor1 (k + 1)) (ctx : Fin (k + 1) → ℕ) :
    (ERMor1.boundedRecRange bound).interp ctx =
      ((ctx 0 + bound.interp ctx + 3).factorial) ^
        ((ctx 0 + bound.interp ctx + 3).factorial) + 1 := by
  unfold ERMor1.boundedRecRange
  simp only [ERMor1.interp_comp, ERMor1.interp_succ,
    ERMor1.interp_powN, ERMor1.interp_factN,
    ERMor1.interp_addN, ERMor1.interp_proj]

/-- β(cand, i) evaluated as an `ERMor1 (k + 2)` term with slot
0 the candidate `cand = Nat.pair a b`, slot 1 the trace length
`n`, and slots 2..k+1 the parameter context.  The inner
argument `iTerm` supplies the third β argument. -/
def ERMor1.betaOnCand {k : ℕ}
    (iTerm : ERMor1 (k + 2)) : ERMor1 (k + 2) :=
  ERMor1.comp ERMor1.beta (fun j => match j with
    | ⟨0, _⟩ =>
        ERMor1.comp ERMor1.natUnpairFst
          (fun (_ : Fin 1) => ERMor1.proj 0)
    | ⟨1, _⟩ =>
        ERMor1.comp ERMor1.natUnpairSnd
          (fun (_ : Fin 1) => ERMor1.proj 0)
    | ⟨2, _⟩ => iTerm)

/-- `base` applied to the parameter context at slots 2..k+1
of a `k + 2`-ary context. -/
def ERMor1.baseOnCand {k : ℕ} (base : ERMor1 k) :
    ERMor1 (k + 2) :=
  ERMor1.comp base
    (fun i => ERMor1.proj ⟨i.val + 2, by omega⟩)

/-- Base-case check for the β-witness predicate.  At context
`Fin.cons cand (Fin.cons n ctx)` (with `cand = Nat.pair a b`),
evaluates to `1` iff `β(a, b, 0) = base.interp ctx`. -/
def ERMor1.boundedRecBaseCheck {k : ℕ}
    (base : ERMor1 k) : ERMor1 (k + 2) :=
  ERMor1.boolEqAt
    (ERMor1.betaOnCand (ERMor1.zeroN (k + 2)))
    (ERMor1.baseOnCand base)

/-- β at the iteration index `iTerm` for a `k+3`-ary context
`(j, cand, n, ctx)` with `cand` in slot 1. -/
def ERMor1.betaOnCandStep {k : ℕ}
    (iTerm : ERMor1 (k + 3)) : ERMor1 (k + 3) :=
  ERMor1.comp ERMor1.beta (fun j => match j with
    | ⟨0, _⟩ =>
        ERMor1.comp ERMor1.natUnpairFst
          (fun (_ : Fin 1) => ERMor1.proj 1)
    | ⟨1, _⟩ =>
        ERMor1.comp ERMor1.natUnpairSnd
          (fun (_ : Fin 1) => ERMor1.proj 1)
    | ⟨2, _⟩ => iTerm)

/-- Apply `step` at a `k+3`-ary context `(j, cand, n, ctx)`
with `cand` at slot 1: slot 0 of `step` is `j`, slot 1 is
`β(a, b, j)` (the recursion accumulator), slots 2..k+1 are
the parameter context. -/
def ERMor1.stepOnCandStep {k : ℕ}
    (step : ERMor1 (k + 2)) : ERMor1 (k + 3) :=
  ERMor1.comp step (fun i => match i with
    | ⟨0, _⟩ => ERMor1.proj 0
    | ⟨1, _⟩ =>
        ERMor1.betaOnCandStep (ERMor1.proj 0)
    | ⟨j + 2, h⟩ =>
        ERMor1.proj ⟨j + 3, by omega⟩)

/-- Step-case check body: an arity-`k+3` term with slot 0 the
bprod counter `j`, slot 1 the candidate, slot 2 the trace
length `n`, slots 3..k+2 the parameter context.  Evaluates to
`1` iff `β(a, b, j + 1) = step.interp (Fin.cons j
  (Fin.cons (β(a, b, j)) ctx))`. -/
def ERMor1.boundedRecStepBody {k : ℕ}
    (step : ERMor1 (k + 2)) : ERMor1 (k + 3) :=
  ERMor1.boolEqAt
    (ERMor1.betaOnCandStep
      (ERMor1.comp ERMor1.succ
        (fun (_ : Fin 1) => ERMor1.proj 0)))
    (ERMor1.stepOnCandStep step)

/-- Step-case check: an arity-`k+2` term with slot 0 the
candidate, slot 1 the trace length `n`, slots 2..k+1 the
parameter context.  Evaluates to `1` iff the β-sequence
transitions by `step` at every index `j < n`. -/
def ERMor1.boundedRecStepCheck {k : ℕ}
    (step : ERMor1 (k + 2)) : ERMor1 (k + 2) :=
  ERMor1.comp (ERMor1.bprod (ERMor1.boundedRecStepBody step))
    (fun (i : Fin (k + 3)) => match i with
      | ⟨0, _⟩ => ERMor1.proj 1
      | ⟨1, _⟩ => ERMor1.proj 0
      | ⟨2, _⟩ => ERMor1.proj 1
      | ⟨j + 3, h⟩ =>
          ERMor1.proj ⟨j + 2, by omega⟩)

/-- Full predicate for the β-witness search: `boolAnd` of the
base-case check and the step-case check. -/
def ERMor1.boundedRecPred {k : ℕ}
    (base : ERMor1 k) (step : ERMor1 (k + 2)) :
    ERMor1 (k + 2) :=
  ERMor1.comp ERMor1.boolAnd (fun i => match i with
    | ⟨0, _⟩ => ERMor1.boundedRecBaseCheck base
    | ⟨1, _⟩ => ERMor1.boundedRecStepCheck step)

/-- The base-case check evaluates in `{0, 1}`. -/
theorem ERMor1.boundedRecBaseCheck_le_one {k : ℕ}
    (base : ERMor1 k) (ctx : Fin (k + 2) → ℕ) :
    (ERMor1.boundedRecBaseCheck base).interp ctx ≤ 1 :=
  ERMor1.boolEqAt_le_one _ _ _

/-- Interpretation of `baseOnCand` at `Fin.cons cand
(Fin.cons n ctx)` reduces to `base.interp ctx`. -/
theorem ERMor1.interp_baseOnCand {k : ℕ} (base : ERMor1 k)
    (cand n : ℕ) (ctx : Fin k → ℕ) :
    (ERMor1.baseOnCand base).interp
        (Fin.cons cand (Fin.cons n ctx)) = base.interp ctx := by
  unfold ERMor1.baseOnCand
  rw [ERMor1.interp_comp]
  congr 1

/-- Interpretation of `betaOnCand iTerm` at `Fin.cons cand
(Fin.cons n ctx)` equals `β(cand.unpair.1, cand.unpair.2,
iTerm.interp (cons cand (cons n ctx)))`. -/
theorem ERMor1.interp_betaOnCand {k : ℕ}
    (iTerm : ERMor1 (k + 2)) (cand n : ℕ)
    (ctx : Fin k → ℕ) :
    (ERMor1.betaOnCand iTerm).interp
        (Fin.cons cand (Fin.cons n ctx)) =
      cand.unpair.1 %
        (1 + (iTerm.interp
          (Fin.cons cand (Fin.cons n ctx)) + 1) *
            cand.unpair.2) := by
  have hconv : (fun (_ : Fin 1) => cand) = ![cand] := by
    funext i
    match i with
    | ⟨0, _⟩ => rfl
  set iVal :=
    iTerm.interp (Fin.cons cand (Fin.cons n ctx)) with hiDef
  have hrew :
      (ERMor1.betaOnCand iTerm).interp
          (Fin.cons cand (Fin.cons n ctx)) =
        ERMor1.beta.interp
          ![cand.unpair.1, cand.unpair.2, iVal] := by
    unfold ERMor1.betaOnCand
    change ERMor1.beta.interp _ = ERMor1.beta.interp _
    congr 1
    funext j
    match j with
    | ⟨0, _⟩ =>
      change ERMor1.natUnpairFst.interp
          (fun (_ : Fin 1) =>
            (Fin.cons cand (Fin.cons n ctx) :
              Fin (k + 2) → ℕ) 0) = _
      have hcand :
          (Fin.cons cand (Fin.cons n ctx) :
            Fin (k + 2) → ℕ) 0 = cand := rfl
      rw [hcand, hconv, ERMor1.interp_natUnpairFst]
      rfl
    | ⟨1, _⟩ =>
      change ERMor1.natUnpairSnd.interp
          (fun (_ : Fin 1) =>
            (Fin.cons cand (Fin.cons n ctx) :
              Fin (k + 2) → ℕ) 0) = _
      have hcand :
          (Fin.cons cand (Fin.cons n ctx) :
            Fin (k + 2) → ℕ) 0 = cand := rfl
      rw [hcand, hconv, ERMor1.interp_natUnpairSnd]
      rfl
    | ⟨2, _⟩ => rfl
  rw [hrew, ERMor1.interp_beta]

/-- Base-check evaluates to `1` iff `β(a, b, 0) = base(ctx)`. -/
theorem ERMor1.boundedRecBaseCheck_eq_one_iff {k : ℕ}
    (base : ERMor1 k) (cand n : ℕ) (ctx : Fin k → ℕ) :
    (ERMor1.boundedRecBaseCheck base).interp
        (Fin.cons cand (Fin.cons n ctx)) = 1 ↔
      cand.unpair.1 % (1 + 1 * cand.unpair.2) =
        base.interp ctx := by
  unfold ERMor1.boundedRecBaseCheck
  rw [ERMor1.boolEqAt_eq_one_iff,
    ERMor1.interp_betaOnCand, ERMor1.interp_baseOnCand]
  have hzero :
      (ERMor1.zeroN (k + 2)).interp
        (Fin.cons cand (Fin.cons n ctx)) = 0 := rfl
  rw [hzero]

/-- The step-body check evaluates in `{0, 1}`. -/
theorem ERMor1.boundedRecStepBody_le_one {k : ℕ}
    (step : ERMor1 (k + 2)) (ctx : Fin (k + 3) → ℕ) :
    (ERMor1.boundedRecStepBody step).interp ctx ≤ 1 :=
  ERMor1.boolEqAt_le_one _ _ _

/-- Interpretation of `betaOnCandStep iTerm` at
`Fin.cons j (Fin.cons cand (Fin.cons n ctx))` equals
`β(cand.unpair.1, cand.unpair.2, iTerm.interp(…))`. -/
theorem ERMor1.interp_betaOnCandStep {k : ℕ}
    (iTerm : ERMor1 (k + 3)) (j cand n : ℕ)
    (ctx : Fin k → ℕ) :
    (ERMor1.betaOnCandStep iTerm).interp
        (Fin.cons j (Fin.cons cand (Fin.cons n ctx))) =
      cand.unpair.1 %
        (1 + (iTerm.interp
          (Fin.cons j
            (Fin.cons cand (Fin.cons n ctx))) + 1) *
            cand.unpair.2) := by
  have hconv : (fun (_ : Fin 1) => cand) = ![cand] := by
    funext i
    match i with
    | ⟨0, _⟩ => rfl
  set iVal :=
    iTerm.interp
      (Fin.cons j (Fin.cons cand (Fin.cons n ctx))) with hiDef
  have hrew :
      (ERMor1.betaOnCandStep iTerm).interp
          (Fin.cons j
            (Fin.cons cand (Fin.cons n ctx))) =
        ERMor1.beta.interp
          ![cand.unpair.1, cand.unpair.2, iVal] := by
    unfold ERMor1.betaOnCandStep
    change ERMor1.beta.interp _ = ERMor1.beta.interp _
    congr 1
    funext p
    match p with
    | ⟨0, _⟩ =>
      change ERMor1.natUnpairFst.interp
          (fun (_ : Fin 1) =>
            (Fin.cons j (Fin.cons cand
              (Fin.cons n ctx)) :
                Fin (k + 3) → ℕ) 1) = _
      have hcand :
          (Fin.cons j (Fin.cons cand (Fin.cons n ctx)) :
            Fin (k + 3) → ℕ) 1 = cand := rfl
      rw [hcand, hconv, ERMor1.interp_natUnpairFst]
      rfl
    | ⟨1, _⟩ =>
      change ERMor1.natUnpairSnd.interp
          (fun (_ : Fin 1) =>
            (Fin.cons j (Fin.cons cand
              (Fin.cons n ctx)) :
                Fin (k + 3) → ℕ) 1) = _
      have hcand :
          (Fin.cons j (Fin.cons cand (Fin.cons n ctx)) :
            Fin (k + 3) → ℕ) 1 = cand := rfl
      rw [hcand, hconv, ERMor1.interp_natUnpairSnd]
      rfl
    | ⟨2, _⟩ => rfl
  rw [hrew, ERMor1.interp_beta]

/-- Interpretation of `stepOnCandStep step` at
`Fin.cons j (Fin.cons cand (Fin.cons n ctx))` equals
`step.interp (Fin.cons j (Fin.cons (β(a, b, j)) ctx))`. -/
theorem ERMor1.interp_stepOnCandStep {k : ℕ}
    (step : ERMor1 (k + 2)) (j cand n : ℕ)
    (ctx : Fin k → ℕ) :
    (ERMor1.stepOnCandStep step).interp
        (Fin.cons j (Fin.cons cand (Fin.cons n ctx))) =
      step.interp
        (Fin.cons j (Fin.cons
          (cand.unpair.1 % (1 + (j + 1) * cand.unpair.2))
          ctx)) := by
  unfold ERMor1.stepOnCandStep
  rw [ERMor1.interp_comp]
  congr 1
  funext i
  match i with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ =>
    change (ERMor1.betaOnCandStep (ERMor1.proj 0)).interp
        (Fin.cons j (Fin.cons cand (Fin.cons n ctx))) = _
    rw [ERMor1.interp_betaOnCandStep]
    have hproj :
        (ERMor1.proj (0 : Fin (k + 3))).interp
          (Fin.cons j
            (Fin.cons cand (Fin.cons n ctx))) = j := rfl
    rw [hproj]
    rfl
  | ⟨p + 2, h⟩ =>
    change (Fin.cons j (Fin.cons cand (Fin.cons n ctx)) :
        Fin (k + 3) → ℕ) ⟨p + 3, by omega⟩ = _
    rfl

/-- Step-body evaluates to `1` iff the trace recurrence holds
at index `j`. -/
theorem ERMor1.boundedRecStepBody_eq_one_iff {k : ℕ}
    (step : ERMor1 (k + 2)) (j cand n : ℕ)
    (ctx : Fin k → ℕ) :
    (ERMor1.boundedRecStepBody step).interp
        (Fin.cons j (Fin.cons cand (Fin.cons n ctx))) = 1 ↔
      cand.unpair.1 %
        (1 + (j + 1 + 1) * cand.unpair.2) =
        step.interp (Fin.cons j
          (Fin.cons
            (cand.unpair.1 %
              (1 + (j + 1) * cand.unpair.2))
            ctx)) := by
  unfold ERMor1.boundedRecStepBody
  rw [ERMor1.boolEqAt_eq_one_iff,
    ERMor1.interp_betaOnCandStep,
    ERMor1.interp_stepOnCandStep]
  have hsucc :
      (ERMor1.comp ERMor1.succ
        (fun (_ : Fin 1) =>
          (ERMor1.proj (0 : Fin (k + 3))))).interp
        (Fin.cons j
          (Fin.cons cand (Fin.cons n ctx))) = j + 1 := by
    rfl
  rw [hsucc]

/-- The step-check evaluates in `{0, 1}`. -/
theorem ERMor1.boundedRecStepCheck_le_one {k : ℕ}
    (step : ERMor1 (k + 2)) (ctx : Fin (k + 2) → ℕ) :
    (ERMor1.boundedRecStepCheck step).interp ctx ≤ 1 := by
  unfold ERMor1.boundedRecStepCheck
  rw [ERMor1.interp_comp, ERMor1.interp_bprod]
  exact natBProd_le_one_of_body_le_one _ _ (fun _ =>
    ERMor1.boundedRecStepBody_le_one step _)

/-- Interpretation of `boundedRecStepCheck` at
`Fin.cons cand (Fin.cons n ctx)` equals the bounded product
of `boundedRecStepBody` values over `j ∈ [0, n)`. -/
theorem ERMor1.interp_boundedRecStepCheck_as_bprod {k : ℕ}
    (step : ERMor1 (k + 2)) (cand n : ℕ)
    (ctx : Fin k → ℕ) :
    (ERMor1.boundedRecStepCheck step).interp
        (Fin.cons cand (Fin.cons n ctx)) =
      natBProd n (fun j =>
        (ERMor1.boundedRecStepBody step).interp
          (Fin.cons j
            (Fin.cons cand (Fin.cons n ctx)))) := by
  unfold ERMor1.boundedRecStepCheck
  rw [ERMor1.interp_comp]
  set argFn : Fin (k + 3) → ℕ := fun i =>
    ((fun i : Fin (k + 3) => match i with
      | ⟨0, _⟩ => ERMor1.proj 1
      | ⟨1, _⟩ => ERMor1.proj 0
      | ⟨2, _⟩ => ERMor1.proj 1
      | ⟨j + 3, h⟩ =>
          ERMor1.proj (⟨j + 2, by omega⟩ : Fin (k + 2))) i).interp
      (Fin.cons cand (Fin.cons n ctx))
  rw [ERMor1.interp_bprod]
  have h0 : argFn 0 = n := rfl
  have htail :
      Fin.tail argFn = Fin.cons cand (Fin.cons n ctx) := by
    funext ⟨p, hp⟩
    change argFn ⟨p + 1, by omega⟩ = _
    match p with
    | 0 => rfl
    | 1 => rfl
    | q + 2 => rfl
  rw [h0, htail]

/-- Step-check evaluates to `1` iff the trace recurrence holds
at every index `j < n`. -/
theorem ERMor1.boundedRecStepCheck_eq_one_iff {k : ℕ}
    (step : ERMor1 (k + 2)) (cand n : ℕ)
    (ctx : Fin k → ℕ) :
    (ERMor1.boundedRecStepCheck step).interp
        (Fin.cons cand (Fin.cons n ctx)) = 1 ↔
      ∀ j, j < n →
        cand.unpair.1 %
          (1 + (j + 1 + 1) * cand.unpair.2) =
          step.interp (Fin.cons j
            (Fin.cons
              (cand.unpair.1 %
                (1 + (j + 1) * cand.unpair.2))
              ctx)) := by
  rw [ERMor1.interp_boundedRecStepCheck_as_bprod,
    natBProd_eq_one_iff_all_one]
  constructor
  · intro h j hj
    exact (ERMor1.boundedRecStepBody_eq_one_iff step j cand
      n ctx).mp (h j hj)
  · intro h j hj
    exact (ERMor1.boundedRecStepBody_eq_one_iff step j cand
      n ctx).mpr (h j hj)

/-- The full predicate evaluates in `{0, 1}`. -/
theorem ERMor1.boundedRecPred_le_one {k : ℕ}
    (base : ERMor1 k) (step : ERMor1 (k + 2))
    (ctx : Fin (k + 2) → ℕ) :
    (ERMor1.boundedRecPred base step).interp ctx ≤ 1 := by
  unfold ERMor1.boundedRecPred
  rw [ERMor1.interp_comp, ERMor1.interp_boolAnd]
  calc _ ≤ 1 * _ := Nat.mul_le_mul_right _
            (ERMor1.boundedRecBaseCheck_le_one _ _)
    _ ≤ 1 * 1 := Nat.mul_le_mul_left _
            (ERMor1.boundedRecStepCheck_le_one _ _)
    _ = 1 := Nat.one_mul _

/-- Auxiliary: product of two naturals equals `1` iff both
are `1`. -/
theorem Nat.mul_eq_one_iff_both
    {x y : ℕ} : x * y = 1 ↔ x = 1 ∧ y = 1 := by
  constructor
  · intro h
    refine ⟨Nat.eq_one_of_mul_eq_one_right h,
      Nat.eq_one_of_mul_eq_one_left h⟩
  · rintro ⟨hx1, hy1⟩
    rw [hx1, hy1]

/-- Predicate evaluates to `1` iff both the base and step
traces match at every index up to `n - 1`. -/
theorem ERMor1.boundedRecPred_eq_one_iff_trace {k : ℕ}
    (base : ERMor1 k) (step : ERMor1 (k + 2))
    (cand n : ℕ) (ctx : Fin k → ℕ) :
    (ERMor1.boundedRecPred base step).interp
        (Fin.cons cand (Fin.cons n ctx)) = 1 ↔
      (cand.unpair.1 % (1 + 1 * cand.unpair.2) =
        base.interp ctx) ∧
      (∀ j, j < n →
        cand.unpair.1 %
          (1 + (j + 1 + 1) * cand.unpair.2) =
          step.interp (Fin.cons j
            (Fin.cons
              (cand.unpair.1 %
                (1 + (j + 1) * cand.unpair.2))
              ctx))) := by
  unfold ERMor1.boundedRecPred
  rw [ERMor1.interp_comp, ERMor1.interp_boolAnd,
    Nat.mul_eq_one_iff_both,
    ERMor1.boundedRecBaseCheck_eq_one_iff,
    ERMor1.boundedRecStepCheck_eq_one_iff]

/-- ER-derived bounded primitive recursion.  At outer arity
`k + 1` with slot `0` the iteration counter `n` and slots
`1..k` the parameter context `ctx`, returns
`min (β(a, b, n)) (bound.interp (Fin.cons n ctx))`, where
`(a, b) = Nat.unpair` of the least `cand < boundedRecRange`
with `boundedRecPred = 1`.  Composing with `minN` against
`bound` makes the output unconditionally bounded by
`bound.interp (Fin.cons n ctx)`.  Correctness against
`Nat.rec` holds when `bound` pointwise dominates the trace. -/
def ERMor1.boundedRec {k : ℕ}
    (base : ERMor1 k) (step : ERMor1 (k + 2))
    (bound : ERMor1 (k + 1)) : ERMor1 (k + 1) :=
  let search : ERMor1 (k + 1) :=
    ERMor1.boundedSearch (ERMor1.boundedRecRange bound)
      (ERMor1.boundedRecPred base step)
  let betaAtN : ERMor1 (k + 1) :=
    ERMor1.comp ERMor1.beta (fun i => match i with
      | ⟨0, _⟩ =>
          ERMor1.comp ERMor1.natUnpairFst
            (fun (_ : Fin 1) => search)
      | ⟨1, _⟩ =>
          ERMor1.comp ERMor1.natUnpairSnd
            (fun (_ : Fin 1) => search)
      | ⟨2, _⟩ => ERMor1.proj 0)
  ERMor1.comp ERMor1.minN (fun i => match i with
    | ⟨0, _⟩ => betaAtN
    | ⟨1, _⟩ => bound)

/-- Unconditional upper bound for `boundedRec`: its
interpretation is dominated by `bound.interp (Fin.cons n ctx)`
for every counter `n` and every parameter context `ctx`. -/
theorem ERMor1.interp_boundedRec_le_bound {k : ℕ}
    (base : ERMor1 k) (step : ERMor1 (k + 2))
    (bound : ERMor1 (k + 1)) (ctx : Fin (k + 1) → ℕ) :
    (ERMor1.boundedRec base step bound).interp ctx ≤
      bound.interp ctx := by
  unfold ERMor1.boundedRec
  rw [ERMor1.interp_comp, ERMor1.interp_minN]
  exact Nat.min_le_right _ _

/-- Arithmetic envelope lemma for the bounded-recursion
search range.  With `N = n + 1`, `b = (max N B + 1)!`, and
`R = (n + B + 3)!`, any `a` bounded by `(N * b + 1) ^ N`
Szudzik-pairs with `b` below `R ^ R + 1`. -/
theorem Nat.pair_lt_boundedRecRange (n B a b : ℕ)
    (hb_eq : b = (max (n + 1) B + 1).factorial)
    (ha_lt : a < ((n + 1) * b + 1) ^ (n + 1)) :
    Nat.pair a b <
      ((n + B + 3).factorial) ^ ((n + B + 3).factorial) + 1 := by
  set R : ℕ := (n + B + 3).factorial with hRdef
  have hR_pos : 0 < R := Nat.factorial_pos _
  have hR_ge_one : 1 ≤ R := hR_pos
  have hb_le_R : b ≤ R := by
    rw [hb_eq, hRdef]
    apply Nat.factorial_le
    have hmax : max (n + 1) B ≤ n + B + 2 :=
      max_le (by omega) (by omega)
    omega
  have hb_lt_R : b < R := by
    rw [hb_eq, hRdef]
    have hmax_le : max (n + 1) B + 1 ≤ n + B + 2 := by
      have hmax : max (n + 1) B ≤ n + B + 1 :=
        max_le (by omega) (by omega)
      omega
    have h1 : (max (n + 1) B + 1).factorial ≤
        (n + B + 2).factorial :=
      Nat.factorial_le hmax_le
    have h2 : (n + B + 2).factorial < (n + B + 3).factorial :=
      Nat.factorial_lt_of_lt (by omega) (by omega)
    omega
  have hn1_le_R : n + 1 ≤ R := by
    rw [hRdef]
    have h1 : n + 1 ≤ n + B + 3 := by omega
    exact le_trans h1 (Nat.self_le_factorial _)
  have hNb_le_R : (n + 1) * b + 1 ≤ R := by
    have hmax_le : max (n + 1) B + 1 ≤ n + B + 2 := by
      have hmax : max (n + 1) B ≤ n + B + 1 :=
        max_le (by omega) (by omega)
      omega
    have hb_le : b ≤ (n + B + 2).factorial := by
      rw [hb_eq]
      exact Nat.factorial_le hmax_le
    have h1 : (n + 1) * b ≤ (n + B + 2) * b :=
      Nat.mul_le_mul_right _ (by omega)
    have h2 : (n + B + 2) * b ≤
        (n + B + 2) * (n + B + 2).factorial :=
      Nat.mul_le_mul_left _ hb_le
    have hfs : (n + B + 3).factorial =
        (n + B + 3) * (n + B + 2).factorial :=
      Nat.factorial_succ (n + B + 2)
    have h3 : (n + B + 2) * (n + B + 2).factorial +
        (n + B + 2).factorial ≤
        (n + B + 3) * (n + B + 2).factorial := by
      have heq :
          (n + B + 3) * (n + B + 2).factorial =
          (n + B + 2) * (n + B + 2).factorial +
            (n + B + 2).factorial := by ring
      omega
    have hR_pos' : 1 ≤ (n + B + 2).factorial :=
      Nat.factorial_pos _
    rw [hRdef, hfs]
    omega
  have ha_lt_RN : a < R ^ (n + 1) := by
    have hbase : (n + 1) * b + 1 ≤ R := hNb_le_R
    have hpow :
        ((n + 1) * b + 1) ^ (n + 1) ≤ R ^ (n + 1) :=
      Nat.pow_le_pow_left hbase _
    exact lt_of_lt_of_le ha_lt hpow
  have hb_le_RN : b ≤ R ^ (n + 1) := by
    have h1 : R ≤ R ^ (n + 1) := by
      have := Nat.le_self_pow (n := n + 1) (by omega) R
      simpa using this
    exact le_trans hb_le_R h1
  have hb_lt_RN : b < R ^ (n + 1) :=
    lt_of_lt_of_le hb_lt_R (by
      have := Nat.le_self_pow (n := n + 1) (by omega) R
      simpa using this)
  have hpair_lt :
      Nat.pair a b < (max a b + 1) ^ 2 :=
    Nat.pair_lt_max_add_one_sq a b
  have hmax1_le : max a b + 1 ≤ R ^ (n + 1) := by
    have h1 : a + 1 ≤ R ^ (n + 1) := ha_lt_RN
    have h2 : b + 1 ≤ R ^ (n + 1) := hb_lt_RN
    have : max a b + 1 = max (a + 1) (b + 1) := by
      rcases le_total a b with h | h
      · rw [max_eq_right h,
          max_eq_right (by omega : a + 1 ≤ b + 1)]
      · rw [max_eq_left h,
          max_eq_left (by omega : b + 1 ≤ a + 1)]
    rw [this]
    exact max_le h1 h2
  have hpow2_le :
      (max a b + 1) ^ 2 ≤ (R ^ (n + 1)) ^ 2 :=
    Nat.pow_le_pow_left hmax1_le 2
  have hpow_combine :
      (R ^ (n + 1)) ^ 2 = R ^ (2 * (n + 1)) := by
    rw [← pow_mul]; ring_nf
  have h2n_le_R : 2 * (n + 1) ≤ R := by
    rw [hRdef]
    have hfact_ge : (n + 3).factorial ≤ (n + B + 3).factorial :=
      Nat.factorial_le (by omega)
    have hnfact : 2 * (n + 1) ≤ (n + 3).factorial := by
      have hfact_split : (n + 3).factorial =
          (n + 3) * ((n + 2) * (n + 1).factorial) := by
        rw [show (n + 3) = (n + 2) + 1 from rfl,
          Nat.factorial_succ,
          show (n + 2) = (n + 1) + 1 from rfl,
          Nat.factorial_succ]
      have hfact_pos : 1 ≤ (n + 1).factorial :=
        Nat.factorial_pos _
      have h23 : 2 * (n + 1) ≤ (n + 3) * (n + 2) := by
        have : (n + 3) * (n + 2) = n * n + 5 * n + 6 := by
          ring
        omega
      have : 2 * (n + 1) ≤ (n + 3) * (n + 2) *
          (n + 1).factorial := by
        have hmul :
            (n + 3) * (n + 2) ≤
              (n + 3) * (n + 2) * (n + 1).factorial := by
          exact Nat.le_mul_of_pos_right _ hfact_pos
        omega
      rw [hfact_split]
      calc 2 * (n + 1) ≤ (n + 3) * (n + 2) *
            (n + 1).factorial := this
        _ = (n + 3) * ((n + 2) * (n + 1).factorial) := by ring
    exact le_trans hnfact hfact_ge
  have hpow_le_RR :
      R ^ (2 * (n + 1)) ≤ R ^ R :=
    Nat.pow_le_pow_right hR_pos h2n_le_R
  have : Nat.pair a b < R ^ R + 1 := by
    have hchain : Nat.pair a b < R ^ R := by
      calc Nat.pair a b
          < (max a b + 1) ^ 2 := hpair_lt
        _ ≤ (R ^ (n + 1)) ^ 2 := hpow2_le
        _ = R ^ (2 * (n + 1)) := hpow_combine
        _ ≤ R ^ R := hpow_le_RR
    omega
  exact this

/-- Helper for the conditional correctness of `boundedRec`:
if a candidate satisfies the base and step clauses of
`boundedRecPred`, then its β-extraction at each index
`j ≤ n` equals the `Nat.rec` trace at `j`. -/
theorem ERMor1.boundedRecPred_trace_match {k : ℕ}
    (base : ERMor1 k) (step : ERMor1 (k + 2))
    (cand : ℕ) (ctx : Fin k → ℕ)
    (hbase : cand.unpair.1 % (1 + 1 * cand.unpair.2) =
      base.interp ctx) (n : ℕ)
    (hstep : ∀ j, j < n →
      cand.unpair.1 %
        (1 + (j + 1 + 1) * cand.unpair.2) =
        step.interp (Fin.cons j
          (Fin.cons
            (cand.unpair.1 %
              (1 + (j + 1) * cand.unpair.2))
            ctx))) :
    ∀ j, j ≤ n →
      cand.unpair.1 % (1 + (j + 1) * cand.unpair.2) =
        Nat.rec (base.interp ctx)
          (fun i prev =>
            step.interp (Fin.cons i
              (Fin.cons prev ctx))) j := by
  intro j hj
  induction j with
  | zero =>
    have hrew :
        1 + (0 + 1) * cand.unpair.2 =
          1 + 1 * cand.unpair.2 := by ring
    rw [hrew, hbase]
    rfl
  | succ m ih =>
    have hm_le : m ≤ n := Nat.le_of_succ_le hj
    have ih' := ih hm_le
    have hm_lt : m < n := Nat.lt_of_succ_le hj
    have hsm := hstep m hm_lt
    rw [ih'] at hsm
    exact hsm

set_option maxHeartbeats 800000 in
-- The multi-stage β-witness extraction in this proof
-- exceeds the default heartbeat limit.
/-- Conditional equality with `Nat.rec`: when the client's
bound is monotone in the counter slot and pointwise dominates
the trace, the combinator agrees with `Nat.rec`. -/
theorem ERMor1.interp_boundedRec_of_bounded {k : ℕ}
    (base : ERMor1 k) (step : ERMor1 (k + 2))
    (bound : ERMor1 (k + 1))
    (n : ℕ) (ctx : Fin k → ℕ)
    (h : ∀ j, j ≤ n →
      Nat.rec (base.interp ctx)
        (fun i prev =>
          step.interp (Fin.cons i (Fin.cons prev ctx)))
        j ≤
        bound.interp (Fin.cons j ctx))
    (h_mono : ∀ j, j ≤ n →
      bound.interp (Fin.cons j ctx) ≤
        bound.interp (Fin.cons n ctx)) :
    (ERMor1.boundedRec base step bound).interp
        (Fin.cons n ctx) =
      Nat.rec (base.interp ctx)
        (fun j prev =>
          step.interp (Fin.cons j (Fin.cons prev ctx)))
        n := by
  set B : ℕ := bound.interp (Fin.cons n ctx) with hBdef
  let trace : ℕ → ℕ := fun j =>
    Nat.rec (base.interp ctx)
      (fun i prev =>
        step.interp (Fin.cons i (Fin.cons prev ctx)))
      j
  let s : Fin (n + 1) → ℕ := fun j => trace j.val
  have hs_le_B : ∀ j : Fin (n + 1), s j ≤ B := by
    intro j
    have hj_le : j.val ≤ n := Nat.le_of_lt_succ j.isLt
    have h1 : s j ≤ bound.interp (Fin.cons j.val ctx) :=
      h j.val hj_le
    have h2 :
        bound.interp (Fin.cons j.val ctx) ≤ B :=
      h_mono j.val hj_le
    exact le_trans h1 h2
  obtain ⟨a, b, hb_eq, ha_lt, hbeta⟩ :=
    Nat.bounded_beta_exists s B hs_le_B
  set cand : ℕ := Nat.pair a b with hcand_def
  have hcand_unpair_fst : cand.unpair.1 = a := by
    rw [hcand_def, Nat.unpair_pair]
  have hcand_unpair_snd : cand.unpair.2 = b := by
    rw [hcand_def, Nat.unpair_pair]
  have hrange :
      (ERMor1.boundedRecRange bound).interp
        (Fin.cons n ctx) =
      ((n + B + 3).factorial) ^ ((n + B + 3).factorial) + 1 := by
    rw [ERMor1.interp_boundedRecRange]
    have hc0 : (Fin.cons n ctx : Fin (k + 1) → ℕ) 0 = n := by
      rfl
    rw [hc0]
  have hcand_lt_range :
      cand <
        (ERMor1.boundedRecRange bound).interp
          (Fin.cons n ctx) := by
    rw [hrange]
    exact Nat.pair_lt_boundedRecRange n B a b hb_eq ha_lt
  have hpred_hold :
      (ERMor1.boundedRecPred base step).interp
          (Fin.cons cand (Fin.cons n ctx)) = 1 := by
    rw [ERMor1.boundedRecPred_eq_one_iff_trace]
    refine ⟨?_, ?_⟩
    · rw [hcand_unpair_fst, hcand_unpair_snd]
      have hzero_lt : 0 < n + 1 := Nat.succ_pos _
      have h0 := hbeta ⟨0, hzero_lt⟩
      have hs0 : s ⟨0, hzero_lt⟩ = base.interp ctx := rfl
      rw [hs0] at h0
      have hrew :
          1 + 1 * b = 1 + (0 + 1) * b := by ring
      rw [hrew]; exact h0
    · intro j hj
      rw [hcand_unpair_fst, hcand_unpair_snd]
      have hj_lt : j < n + 1 := Nat.lt_succ_of_lt hj
      have hjsucc_lt : j + 1 < n + 1 :=
        Nat.succ_lt_succ hj
      have hbeta_j := hbeta ⟨j, hj_lt⟩
      have hbeta_js := hbeta ⟨j + 1, hjsucc_lt⟩
      change a % (1 + (j + 1) * b) = trace j at hbeta_j
      change a % (1 + (j + 1 + 1) * b) = trace (j + 1) at hbeta_js
      have hstep_trace :
          trace (j + 1) = step.interp
            (Fin.cons j (Fin.cons (trace j) ctx)) := rfl
      rw [hstep_trace] at hbeta_js
      rw [← hbeta_j] at hbeta_js
      exact hbeta_js
  have hpred_bound :
      ∀ j, (ERMor1.boundedRecPred base step).interp
        (Fin.cons j (Fin.cons n ctx)) ≤ 1 := by
    intro j
    exact ERMor1.boundedRecPred_le_one base step _
  set search : ERMor1 (k + 1) :=
    ERMor1.boundedSearch (ERMor1.boundedRecRange bound)
      (ERMor1.boundedRecPred base step) with hsearch_def
  have hex : ∃ j, j <
      (ERMor1.boundedRecRange bound).interp
        (Fin.cons n ctx) ∧
      (ERMor1.boundedRecPred base step).interp
        (Fin.cons j (Fin.cons n ctx)) = 1 :=
    ⟨cand, hcand_lt_range, hpred_hold⟩
  have hsearch_eval :
      search.interp (Fin.cons n ctx) = Nat.find hex := by
    rw [hsearch_def,
      ERMor1.interp_boundedSearch _ _ _ hpred_bound,
      dif_pos hex]
  set found : ℕ := Nat.find hex with hfound_def
  have hfound_lt :
      found < (ERMor1.boundedRecRange bound).interp
        (Fin.cons n ctx) :=
    (Nat.find_spec hex).1
  have hfound_pred :
      (ERMor1.boundedRecPred base step).interp
        (Fin.cons found (Fin.cons n ctx)) = 1 :=
    (Nat.find_spec hex).2
  obtain ⟨hfound_base, hfound_step⟩ :=
    (ERMor1.boundedRecPred_eq_one_iff_trace base step
      found n ctx).mp hfound_pred
  have hfound_trace :
      ∀ j, j ≤ n →
        found.unpair.1 % (1 + (j + 1) * found.unpair.2) =
          trace j :=
    ERMor1.boundedRecPred_trace_match base step found ctx
      hfound_base n hfound_step
  unfold ERMor1.boundedRec
  rw [ERMor1.interp_comp, ERMor1.interp_minN]
  change min
      ((ERMor1.comp ERMor1.beta _).interp (Fin.cons n ctx))
      (bound.interp (Fin.cons n ctx)) = trace n
  have hbetaN_eval :
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
        (Fin.cons n ctx) =
      found.unpair.1 % (1 + (n + 1) * found.unpair.2) := by
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
            (Fin.cons n ctx)) =
        ![found.unpair.1, found.unpair.2, n] := by
      funext i
      match i with
      | ⟨0, _⟩ =>
        change ERMor1.natUnpairFst.interp
            (fun (_ : Fin 1) =>
              search.interp (Fin.cons n ctx)) = _
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
              search.interp (Fin.cons n ctx)) = _
        rw [hsearch_eval]
        have hfun :
            (fun (_ : Fin 1) => (found : ℕ)) = ![found] := by
          funext j
          match j with
          | ⟨0, _⟩ => rfl
        rw [hfun, ERMor1.interp_natUnpairSnd]
        rfl
      | ⟨2, _⟩ =>
        change (Fin.cons n ctx : Fin (k + 1) → ℕ) 0 = _
        rfl
    rw [harg, ERMor1.interp_beta]
  rw [hbetaN_eval]
  have htrace_n := hfound_trace n (le_refl n)
  rw [htrace_n]
  have htrace_le : trace n ≤ B := by
    have := h n (le_refl n)
    have hmono := h_mono n (le_refl n)
    exact le_trans this hmono
  exact min_eq_left htrace_le

/-- Convenience alias for `interp_boundedRec_of_bounded`.
When the client supplies pointwise bound-adequacy and
counter-monotonicity hypotheses, `boundedRec` computes the
exact `Nat.rec` trace value at position `n`. -/
theorem ERMor1.boundedRec_eq_natRec_of_bounded {k : ℕ}
    (base : ERMor1 k) (step : ERMor1 (k + 2))
    (bound : ERMor1 (k + 1))
    (n : ℕ) (ctx : Fin k → ℕ)
    (h : ∀ j, j ≤ n →
      Nat.rec (base.interp ctx)
        (fun i prev =>
          step.interp (Fin.cons i (Fin.cons prev ctx)))
        j ≤
        bound.interp (Fin.cons j ctx))
    (h_mono : ∀ j, j ≤ n →
      bound.interp (Fin.cons j ctx) ≤
        bound.interp (Fin.cons n ctx)) :
    (ERMor1.boundedRec base step bound).interp
        (Fin.cons n ctx) =
      Nat.rec (base.interp ctx)
        (fun j prev =>
          step.interp (Fin.cons j (Fin.cons prev ctx)))
        n :=
  ERMor1.interp_boundedRec_of_bounded base step bound n ctx
    h h_mono

/-! ### Showcase primitives: `natAdd`, `natMul`, `factorial` -/

/-- Addition via bounded recursion: slot 0 is the iteration
counter `x`, slot 1 is the addend `y`.  The trace satisfies
`Nat.rec y (fun _ p => p + 1) x = y + x`. -/
def ERMor1.natAdd : ERMor1 2 :=
  ERMor1.boundedRec
    (ERMor1.proj (k := 1) 0)
    (ERMor1.comp ERMor1.succ
      (fun (_ : Fin 1) => ERMor1.proj (k := 3) 1))
    (ERMor1.comp ERMor1.succ
      (fun (_ : Fin 1) =>
        ERMor1.comp ERMor1.addN
          (fun i => match i with
            | ⟨0, _⟩ => ERMor1.proj (k := 2) 0
            | ⟨1, _⟩ => ERMor1.proj (k := 2) 1)))

/-- The `natAdd` step term evaluates to `prev + 1`. -/
private theorem ERMor1.natAdd_step_eval
    (y j prev : ℕ) :
    (ERMor1.comp ERMor1.succ
      (fun (_ : Fin 1) => ERMor1.proj (k := 3) 1)).interp
      (Fin.cons j (Fin.cons prev (Fin.cons y Fin.elim0))) =
      prev + 1 := by
  simp only [ERMor1.interp_comp, ERMor1.interp_succ,
    ERMor1.interp_proj]
  rfl

/-- The `natAdd` bound term evaluates to `j + y + 1`. -/
private theorem ERMor1.natAdd_bound_eval (y j : ℕ) :
    (ERMor1.comp ERMor1.succ
      (fun (_ : Fin 1) =>
        ERMor1.comp ERMor1.addN
          (fun i => match i with
            | ⟨0, _⟩ => ERMor1.proj (k := 2) 0
            | ⟨1, _⟩ => ERMor1.proj (k := 2) 1))).interp
      (Fin.cons j (Fin.cons y Fin.elim0)) = j + y + 1 := by
  simp only [ERMor1.interp_comp, ERMor1.interp_succ,
    ERMor1.interp_addN, ERMor1.interp_proj, Fin.cons_zero]
  rfl

/-- The `natAdd` raw Nat.rec trace with unevaluated step equals
the one with simplified arithmetic step. -/
private theorem ERMor1.natAdd_rec_simp (y n : ℕ) :
    (Nat.rec y
      (fun i prev =>
        (ERMor1.comp ERMor1.succ
          (fun (_ : Fin 1) =>
            ERMor1.proj (k := 3) 1)).interp
          (Fin.cons i (Fin.cons prev
            (Fin.cons y Fin.elim0)))) n : ℕ) =
    Nat.rec y (fun (_ : ℕ) (p : ℕ) => p + 1) n := by
  induction n with
  | zero => rfl
  | succ m ih =>
    change (ERMor1.comp ERMor1.succ
        (fun (_ : Fin 1) => ERMor1.proj (k := 3) 1)).interp
        (Fin.cons m (Fin.cons
          (Nat.rec y (fun (_ : ℕ) (p : ℕ) => p + 1) m)
          (Fin.cons y Fin.elim0))) =
        Nat.rec y (fun (_ : ℕ) (p : ℕ) => p + 1) m + 1
    rw [← ih, ERMor1.natAdd_step_eval]

/-- Sub-lemma: `natAdd` simplified trace at step `j` equals
`y + j`. -/
private theorem ERMor1.natAdd_trace_eq (y j : ℕ) :
    Nat.rec y (fun (_ : ℕ) (p : ℕ) => p + 1) j = y + j := by
  induction j with
  | zero => rfl
  | succ m ih =>
    change Nat.rec y (fun _ p => p + 1) m + 1 = y + (m + 1)
    omega

set_option maxHeartbeats 400000 in
-- `boundedRec_eq_natRec_of_bounded` unification is heavy
/-- Interpretation of `natAdd`:
`natAdd.interp ![x, y] = x + y`. -/
@[simp] theorem ERMor1.interp_natAdd (x y : ℕ) :
    ERMor1.natAdd.interp ![x, y] = x + y := by
  change ERMor1.natAdd.interp
      (Fin.cons x (Fin.cons y Fin.elim0)) = x + y
  unfold ERMor1.natAdd
  refine ERMor1.boundedRec_eq_natRec_of_bounded _ _ _ _ _
      ?_ ?_ |>.trans ?_
  · intro j _hj
    simp only [ERMor1.interp_proj, Fin.cons_zero]
    rw [ERMor1.natAdd_rec_simp, ERMor1.natAdd_bound_eval,
      ERMor1.natAdd_trace_eq]
    omega
  · intro j hj
    rw [ERMor1.natAdd_bound_eval, ERMor1.natAdd_bound_eval]
    omega
  · simp only [ERMor1.interp_proj, Fin.cons_zero]
    rw [ERMor1.natAdd_rec_simp, ERMor1.natAdd_trace_eq]
    omega

/-- Multiplication via bounded recursion: slot 0 is the
iteration counter `x`, slot 1 is the multiplicand `y`.
The trace satisfies `Nat.rec 0 (fun _ p => p + y) x = x * y`.
-/
def ERMor1.natMul : ERMor1 2 :=
  ERMor1.boundedRec
    (ERMor1.zeroN 1)
    (ERMor1.comp ERMor1.addN
      (fun i => match i with
        | ⟨0, _⟩ => ERMor1.proj (k := 3) 1
        | ⟨1, _⟩ => ERMor1.proj (k := 3) 2))
    (ERMor1.comp ERMor1.succ
      (fun (_ : Fin 1) =>
        ERMor1.comp ERMor1.mulN
          (fun i => match i with
            | ⟨0, _⟩ =>
                ERMor1.comp ERMor1.succ
                  (fun (_ : Fin 1) => ERMor1.proj (k := 2) 0)
            | ⟨1, _⟩ => ERMor1.proj (k := 2) 1)))

/-- The `natMul` step term evaluates to `prev + y`. -/
private theorem ERMor1.natMul_step_eval
    (y j prev : ℕ) :
    (ERMor1.comp ERMor1.addN
      (fun i => match i with
        | ⟨0, _⟩ => ERMor1.proj (k := 3) 1
        | ⟨1, _⟩ => ERMor1.proj (k := 3) 2)).interp
      (Fin.cons j (Fin.cons prev (Fin.cons y Fin.elim0))) =
      prev + y := by
  simp only [ERMor1.interp_comp, ERMor1.interp_addN,
    ERMor1.interp_proj]
  rfl

/-- The `natMul` bound term evaluates to `(j + 1) * y + 1`. -/
private theorem ERMor1.natMul_bound_eval (y j : ℕ) :
    (ERMor1.comp ERMor1.succ
      (fun (_ : Fin 1) =>
        ERMor1.comp ERMor1.mulN
          (fun i => match i with
            | ⟨0, _⟩ =>
                ERMor1.comp ERMor1.succ
                  (fun (_ : Fin 1) =>
                    ERMor1.proj (k := 2) 0)
            | ⟨1, _⟩ => ERMor1.proj (k := 2) 1))).interp
      (Fin.cons j (Fin.cons y Fin.elim0)) =
    (j + 1) * y + 1 := by
  simp only [ERMor1.interp_comp, ERMor1.interp_succ,
    ERMor1.interp_mulN, ERMor1.interp_proj, Fin.cons_zero]
  change ((j + 1) *
      (Fin.cons j (Fin.cons y Fin.elim0) : Fin 2 → ℕ) 1)
      + 1 = (j + 1) * y + 1
  rfl

/-- Direct trace evaluation for `natMul`: the raw `Nat.rec`
over the ER step term at counter `n` equals `n * y`. -/
private theorem ERMor1.natMul_trace_direct (y n : ℕ) :
    (Nat.rec 0
      (fun i prev =>
        (ERMor1.comp ERMor1.addN
          (fun k => match k with
            | ⟨0, _⟩ => ERMor1.proj (k := 3) 1
            | ⟨1, _⟩ => ERMor1.proj (k := 3) 2)).interp
          (Fin.cons i (Fin.cons prev
            (Fin.cons y Fin.elim0)))) n : ℕ) = n * y := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Nat.succ_mul, ← ih]
    exact ERMor1.natMul_step_eval y m _

set_option maxHeartbeats 400000 in
-- `boundedRec_eq_natRec_of_bounded` unification is heavy
/-- Interpretation of `natMul`:
`natMul.interp ![x, y] = x * y`. -/
@[simp] theorem ERMor1.interp_natMul (x y : ℕ) :
    ERMor1.natMul.interp ![x, y] = x * y := by
  change ERMor1.natMul.interp
      (Fin.cons x (Fin.cons y Fin.elim0)) = x * y
  unfold ERMor1.natMul
  refine ERMor1.boundedRec_eq_natRec_of_bounded _ _ _ _ _
      ?_ ?_ |>.trans ?_
  · intro j _hj
    simp only [ERMor1.interp_zeroN]
    rw [ERMor1.natMul_trace_direct, ERMor1.natMul_bound_eval]
    have : j * y ≤ (j + 1) * y + 1 := by
      rw [Nat.succ_mul]; omega
    exact this
  · intro j hj
    rw [ERMor1.natMul_bound_eval, ERMor1.natMul_bound_eval]
    have : (j + 1) * y ≤ (x + 1) * y :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  · simp only [ERMor1.interp_zeroN]
    rw [ERMor1.natMul_trace_direct]

/-- Factorial via bounded recursion: slot 0 is the iteration
counter `n`.  The bound is `factN` itself, reflecting that
`j! ≤ n!` for `j ≤ n`.  The trace satisfies
`Nat.rec 1 (fun i p => (i + 1) * p) n = n!`. -/
def ERMor1.factorial : ERMor1 1 :=
  ERMor1.boundedRec
    (ERMor1.oneN 0)
    (ERMor1.comp ERMor1.mulN
      (fun i => match i with
        | ⟨0, _⟩ =>
            ERMor1.comp ERMor1.succ
              (fun (_ : Fin 1) => ERMor1.proj (k := 2) 0)
        | ⟨1, _⟩ => ERMor1.proj (k := 2) 1))
    ERMor1.factN

/-- The `factorial` step term evaluates to `(j + 1) * prev`. -/
private theorem ERMor1.factorial_step_eval
    (j prev : ℕ) :
    (ERMor1.comp ERMor1.mulN
      (fun i => match i with
        | ⟨0, _⟩ =>
            ERMor1.comp ERMor1.succ
              (fun (_ : Fin 1) => ERMor1.proj (k := 2) 0)
        | ⟨1, _⟩ => ERMor1.proj (k := 2) 1)).interp
      (Fin.cons j (Fin.cons prev Fin.elim0)) =
      (j + 1) * prev := by
  simp only [ERMor1.interp_comp, ERMor1.interp_mulN,
    ERMor1.interp_succ, ERMor1.interp_proj, Fin.cons_zero]
  change (j + 1) *
      (Fin.cons j (Fin.cons prev Fin.elim0) : Fin 2 → ℕ) 1 =
      (j + 1) * prev
  rfl

/-- Direct trace evaluation for `factorial`: the raw `Nat.rec`
over the ER step term at counter `n` equals `n!`. -/
private theorem ERMor1.factorial_trace_direct (n : ℕ) :
    (Nat.rec 1
      (fun i prev =>
        (ERMor1.comp ERMor1.mulN
          (fun k => match k with
            | ⟨0, _⟩ =>
                ERMor1.comp ERMor1.succ
                  (fun (_ : Fin 1) =>
                    ERMor1.proj (k := 2) 0)
            | ⟨1, _⟩ => ERMor1.proj (k := 2) 1)).interp
          (Fin.cons i (Fin.cons prev Fin.elim0))) n : ℕ) =
    n.factorial := by
  induction n with
  | zero => rfl
  | succ m ih =>
    rw [Nat.factorial_succ, ← ih]
    exact ERMor1.factorial_step_eval m _

set_option maxHeartbeats 400000 in
-- `boundedRec_eq_natRec_of_bounded` unification is heavy
/-- Interpretation of `factorial`:
`factorial.interp ![n] = n.factorial`. -/
@[simp] theorem ERMor1.interp_factorial (n : ℕ) :
    ERMor1.factorial.interp ![n] = n.factorial := by
  change ERMor1.factorial.interp (Fin.cons n Fin.elim0) =
      n.factorial
  unfold ERMor1.factorial
  refine ERMor1.boundedRec_eq_natRec_of_bounded _ _ _ _ _
      ?_ ?_ |>.trans ?_
  · intro j hj
    simp only [ERMor1.interp_oneN]
    rw [ERMor1.factorial_trace_direct, ERMor1.interp_factN,
      Fin.cons_zero]
  · intro j hj
    simp only [ERMor1.interp_factN, Fin.cons_zero]
    exact Nat.factorial_le hj
  · simp only [ERMor1.interp_oneN]
    rw [ERMor1.factorial_trace_direct]

end GebLean
