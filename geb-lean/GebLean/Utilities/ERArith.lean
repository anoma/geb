import GebLean.LawvereER
import GebLean.LawvereERArith
import GebLean.LawvereERBool
import GebLean.Utilities.SzudzikSeq
import Mathlib.Data.Nat.Pairing
import Mathlib.Logic.Godel.GodelBetaFunction

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

end GebLean
