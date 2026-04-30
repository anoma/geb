import GebLean.LawvereER
import GebLean.LawvereERBound
import GebLean.LawvereERBoundComputable
import GebLean.Utilities.ComputationalComplexity

/-!
# ER polynomial bounds and structural towerHeight lemma

ER-side polynomial-value-bound infrastructure used in
the K^sim → ER forward translation's interp-preservation
theorem.

The principal results are:

- `ERMor1.PolyBound` — data-bearing structure carrying
  polynomial degree, leading coefficient, and additive
  constant fields, together with a value-bound proof in
  the shape `c · (sup ctx + 1)^d + k`.

References `ERMor1` but not `KMor1`.

See `docs/plans/2026-04-30-er-polynomial-bound-design.md`
(Module B) and
`docs/research/2026-04-30-ksim-polynomial-bound-references.md`
(Claim 7 / FOLKLORE 4).
-/

namespace GebLean

/-- Data-bearing polynomial-value-bound for an ER term,
in the standard `c · (sup ctx + 1)^d + k` shape per
Tourlakis 2018 §0.1.0.27 (3) ("Bounding Lemma" clause 3
for E^2: there are C, n, k such that
`f(x⃗) ≤ C max(x⃗)^n + k`).
The fields are:

- `degree`: polynomial degree (the `n` in Tourlakis).
- `coefficient`: leading coefficient (the `C`).
- `constant`: additive constant (the `k`).
- `bounds`: the value-bound proof. -/
structure ERMor1.PolyBound {n : ℕ} (f : ERMor1 n) where
  degree : ℕ
  coefficient : ℕ
  constant : ℕ
  bounds : ∀ ctx : Fin n → ℕ,
    f.interp ctx ≤
      coefficient *
        ((Finset.univ : Finset (Fin n)).sup ctx + 1) ^ degree
      + constant

namespace ERMor1.PolyBound

/-- Auxiliary: a single `(g i).interp ctx` is dominated by
the family-wide constants `(c_g, d_g, k_g)`. -/
private theorem comp_inner_bound_pointwise
    {k n : ℕ} (g : Fin k → ERMor1 n)
    (pb_g : (i : Fin k) → PolyBound (g i))
    (ctx : Fin n → ℕ) (i : Fin k) :
    (g i).interp ctx ≤
      ((Finset.univ : Finset (Fin k)).sup
          (fun j => (pb_g j).coefficient))
        * (maxCtx ctx + 1) ^
          ((Finset.univ : Finset (Fin k)).sup
            (fun j => (pb_g j).degree))
      + ((Finset.univ : Finset (Fin k)).sup
          (fun j => (pb_g j).constant)) := by
  have h_one_le_S : 1 ≤ maxCtx ctx + 1 := by omega
  have h_applied := (pb_g i).bounds ctx
  change (g i).interp ctx ≤
    (pb_g i).coefficient *
        (maxCtx ctx + 1) ^ (pb_g i).degree
      + (pb_g i).constant at h_applied
  have h_coeff_le :
      (pb_g i).coefficient ≤
        (Finset.univ : Finset (Fin k)).sup
          (fun j => (pb_g j).coefficient) :=
    Finset.le_sup (f := fun j => (pb_g j).coefficient)
      (Finset.mem_univ i)
  have h_deg_le :
      (pb_g i).degree ≤
        (Finset.univ : Finset (Fin k)).sup
          (fun j => (pb_g j).degree) :=
    Finset.le_sup (f := fun j => (pb_g j).degree)
      (Finset.mem_univ i)
  have h_const_le :
      (pb_g i).constant ≤
        (Finset.univ : Finset (Fin k)).sup
          (fun j => (pb_g j).constant) :=
    Finset.le_sup (f := fun j => (pb_g j).constant)
      (Finset.mem_univ i)
  have h_pow_le :
      (maxCtx ctx + 1) ^ (pb_g i).degree ≤
        (maxCtx ctx + 1) ^
          ((Finset.univ : Finset (Fin k)).sup
            (fun j => (pb_g j).degree)) :=
    Nat.pow_le_pow_right h_one_le_S h_deg_le
  have h_term_le :
      (pb_g i).coefficient *
          (maxCtx ctx + 1) ^ (pb_g i).degree
        ≤ ((Finset.univ : Finset (Fin k)).sup
              (fun j => (pb_g j).coefficient))
          * (maxCtx ctx + 1) ^
            ((Finset.univ : Finset (Fin k)).sup
              (fun j => (pb_g j).degree)) :=
    Nat.mul_le_mul h_coeff_le h_pow_le
  omega

/-- Auxiliary: `maxCtx` of the composition's inner context
is dominated by the family-wide bound. -/
private theorem comp_maxCtx_inner_le
    {k n : ℕ} (g : Fin k → ERMor1 n)
    (pb_g : (i : Fin k) → PolyBound (g i))
    (ctx : Fin n → ℕ) :
    maxCtx (fun i => (g i).interp ctx) ≤
      ((Finset.univ : Finset (Fin k)).sup
          (fun j => (pb_g j).coefficient))
        * (maxCtx ctx + 1) ^
          ((Finset.univ : Finset (Fin k)).sup
            (fun j => (pb_g j).degree))
      + ((Finset.univ : Finset (Fin k)).sup
          (fun j => (pb_g j).constant)) := by
  apply Finset.sup_le
  intro i _
  exact comp_inner_bound_pointwise g pb_g ctx i

/-- Polynomial bound for `zero` (constant `0`). -/
def ofZero : PolyBound ERMor1.zero where
  degree := 0
  coefficient := 0
  constant := 0
  bounds := fun _ => by
    simp [ERMor1.interp_zero]

/-- Polynomial bound for `succ` (linear, `c=1`, `d=1`,
`k=1`). -/
def ofSucc : PolyBound ERMor1.succ where
  degree := 1
  coefficient := 1
  constant := 1
  bounds := fun ctx => by
    simp only [ERMor1.interp_succ, pow_one, one_mul]
    have h : ctx 0 ≤
        (Finset.univ : Finset (Fin 1)).sup ctx :=
      Finset.le_sup (Finset.mem_univ _)
    omega

/-- Polynomial bound for `proj i` (linear, `c=1`, `d=1`,
`k=0`). -/
def ofProj {k : ℕ} (i : Fin k) :
    PolyBound (ERMor1.proj i) where
  degree := 1
  coefficient := 1
  constant := 0
  bounds := fun ctx => by
    simp only [ERMor1.interp_proj, pow_one, one_mul]
    have h : ctx i ≤
        (Finset.univ : Finset (Fin k)).sup ctx :=
      Finset.le_sup (Finset.mem_univ _)
    omega

/-- Polynomial bound for `sub` (linear, `c=1`, `d=1`,
`k=0`). -/
def ofSub : PolyBound ERMor1.sub where
  degree := 1
  coefficient := 1
  constant := 0
  bounds := fun ctx => by
    simp only [ERMor1.interp_sub, pow_one, one_mul]
    have h0 : ctx 0 ≤
        (Finset.univ : Finset (Fin 2)).sup ctx :=
      Finset.le_sup (Finset.mem_univ _)
    omega

/-- Polynomial bound for composition.  If `f` has bound
`c_f * y^d_f + k_f` and the family `g` has uniform bound
`c_g * x^d_g + k_g` (taking sups over the family), then
`comp f g` has bound
`c_f * (c_g + k_g + 1)^d_f * x^(d_f * d_g) + k_f`. -/
def ofComp {k n : ℕ} {f : ERMor1 k} {g : Fin k → ERMor1 n}
    (pb_f : PolyBound f)
    (pb_g : (i : Fin k) → PolyBound (g i)) :
    PolyBound (ERMor1.comp f g) :=
  let c_g := (Finset.univ : Finset (Fin k)).sup
    (fun i => (pb_g i).coefficient)
  let d_g := (Finset.univ : Finset (Fin k)).sup
    (fun i => (pb_g i).degree)
  let k_g := (Finset.univ : Finset (Fin k)).sup
    (fun i => (pb_g i).constant)
  { degree := pb_f.degree * d_g
    coefficient :=
      pb_f.coefficient * (c_g + k_g + 1) ^ pb_f.degree
    constant := pb_f.constant
    bounds := fun ctx => by
      simp only [ERMor1.interp_comp]
      set S : ℕ := maxCtx ctx + 1 with hS
      have h_S_pos : 1 ≤ S := by
        simp only [hS, maxCtx]; omega
      have h_inner_max :
          maxCtx (fun i => (g i).interp ctx) ≤
            c_g * S ^ d_g + k_g := by
        change maxCtx (fun i => (g i).interp ctx) ≤
          c_g * (maxCtx ctx + 1) ^ d_g + k_g
        exact comp_maxCtx_inner_le g pb_g ctx
      have h_f_applied :=
        pb_f.bounds (fun i => (g i).interp ctx)
      change f.interp (fun i => (g i).interp ctx) ≤
        pb_f.coefficient *
            (maxCtx (fun i => (g i).interp ctx) + 1)
              ^ pb_f.degree
          + pb_f.constant at h_f_applied
      have h_inner_plus_one :
          maxCtx (fun i => (g i).interp ctx) + 1 ≤
            (c_g + k_g + 1) * S ^ d_g := by
        have h_pow_pos : 1 ≤ S ^ d_g :=
          Nat.one_le_pow _ _ h_S_pos
        have h_kg_bound : k_g ≤ k_g * S ^ d_g :=
          Nat.le_mul_of_pos_right _ h_pow_pos
        have h_one_bound : 1 ≤ S ^ d_g := h_pow_pos
        have h_step :
            c_g * S ^ d_g + k_g + 1 ≤
              c_g * S ^ d_g + k_g * S ^ d_g + S ^ d_g := by
          omega
        have h_factor :
            c_g * S ^ d_g + k_g * S ^ d_g + S ^ d_g
              = (c_g + k_g + 1) * S ^ d_g := by ring
        omega
      have h_pow_inner :
          (maxCtx (fun i => (g i).interp ctx) + 1)
              ^ pb_f.degree ≤
            ((c_g + k_g + 1) * S ^ d_g) ^ pb_f.degree :=
        Nat.pow_le_pow_left h_inner_plus_one _
      have h_pow_split :
          ((c_g + k_g + 1) * S ^ d_g) ^ pb_f.degree =
            (c_g + k_g + 1) ^ pb_f.degree *
              S ^ (pb_f.degree * d_g) := by
        rw [Nat.mul_pow, ← Nat.pow_mul]
        ring
      have h_coeff_step :
          pb_f.coefficient *
              (maxCtx (fun i => (g i).interp ctx) + 1)
                ^ pb_f.degree
            ≤ pb_f.coefficient *
                ((c_g + k_g + 1) ^ pb_f.degree *
                  S ^ (pb_f.degree * d_g)) := by
        have h := Nat.mul_le_mul_left pb_f.coefficient
          h_pow_inner
        rw [h_pow_split] at h
        exact h
      have h_assoc :
          pb_f.coefficient *
              ((c_g + k_g + 1) ^ pb_f.degree *
                S ^ (pb_f.degree * d_g))
            = pb_f.coefficient *
                (c_g + k_g + 1) ^ pb_f.degree *
                S ^ (pb_f.degree * d_g) := by ring
      have h_combined :
          f.interp (fun i => (g i).interp ctx) ≤
            pb_f.coefficient *
                (c_g + k_g + 1) ^ pb_f.degree *
                S ^ (pb_f.degree * d_g) +
              pb_f.constant := by
        have := le_trans h_f_applied
          (Nat.add_le_add_right h_coeff_step _)
        rw [h_assoc] at this
        exact this
      exact h_combined }

/-- Polynomial bound for `bsum f`: bounded summation
adds 1 to the inner degree (sums up-to-`(ctx 0)`-many
copies, each itself polynomial-bounded).  The constant
field is absorbed into the leading coefficient since the
linear-in-`(sup + 1)` constant term is dominated by a
larger leading polynomial term. -/
def ofBsum {k : ℕ} {f : ERMor1 (k + 1)}
    (pb_f : PolyBound f) :
    PolyBound (ERMor1.bsum f) where
  degree := pb_f.degree + 1
  coefficient := pb_f.coefficient + pb_f.constant
  constant := 0
  bounds := fun ctx => by
    simp only [ERMor1.interp_bsum, Nat.add_zero]
    set S : ℕ := maxCtx ctx + 1 with hS
    have h_S_pos : 1 ≤ S := by
      simp only [hS, maxCtx]; omega
    have h_inner : ∀ i < ctx 0,
        f.interp (Fin.cons i (Fin.tail ctx))
          ≤ pb_f.coefficient * S ^ pb_f.degree
            + pb_f.constant := by
      intro i hi
      have hi_le : i ≤ maxCtx ctx :=
        le_trans (Nat.le_of_lt hi) (le_maxCtx ctx 0)
      have h_max_le :
          maxCtx (Fin.cons i (Fin.tail ctx)) ≤ maxCtx ctx :=
        maxCtx_cons_le i ctx hi_le
      have h_applied :=
        pb_f.bounds (Fin.cons i (Fin.tail ctx))
      change f.interp (Fin.cons i (Fin.tail ctx)) ≤
        pb_f.coefficient *
            (maxCtx (Fin.cons i (Fin.tail ctx)) + 1)
              ^ pb_f.degree
          + pb_f.constant at h_applied
      have h_S_mono :
          (maxCtx (Fin.cons i (Fin.tail ctx)) + 1)
              ^ pb_f.degree ≤ S ^ pb_f.degree :=
        Nat.pow_le_pow_left (by simp only [hS]; omega) _
      have h_coeff_mono :
          pb_f.coefficient *
              (maxCtx (Fin.cons i (Fin.tail ctx)) + 1)
                ^ pb_f.degree
            ≤ pb_f.coefficient * S ^ pb_f.degree :=
        Nat.mul_le_mul_left _ h_S_mono
      exact le_trans h_applied (by omega)
    have h_sum :=
      natBSum_le_mul_max (ctx 0)
        (fun i => f.interp (Fin.cons i (Fin.tail ctx)))
        (pb_f.coefficient * S ^ pb_f.degree
          + pb_f.constant) h_inner
    have h_ctx0_le_S : ctx 0 ≤ S := by
      have := le_maxCtx ctx 0
      simp only [hS]; omega
    have h_mul_le :
        ctx 0 *
            (pb_f.coefficient * S ^ pb_f.degree
              + pb_f.constant)
          ≤ S *
            (pb_f.coefficient * S ^ pb_f.degree
              + pb_f.constant) :=
      Nat.mul_le_mul_right _ h_ctx0_le_S
    have h_S_pow_succ :
        S * S ^ pb_f.degree = S ^ (pb_f.degree + 1) := by
      rw [pow_succ]; ring
    have h_distrib :
        S * (pb_f.coefficient * S ^ pb_f.degree
              + pb_f.constant)
          = pb_f.coefficient * S ^ (pb_f.degree + 1)
            + pb_f.constant * S := by
      rw [Nat.mul_add, ← h_S_pow_succ]; ring
    have h_pow_le :
        S ≤ S ^ (pb_f.degree + 1) := by
      calc S = S ^ 1 := (pow_one S).symm
        _ ≤ S ^ (pb_f.degree + 1) :=
            Nat.pow_le_pow_right h_S_pos (by omega)
    have h_const_absorb :
        pb_f.constant * S ≤
          pb_f.constant * S ^ (pb_f.degree + 1) :=
      Nat.mul_le_mul_left _ h_pow_le
    have h_eq_combine :
        pb_f.coefficient * S ^ (pb_f.degree + 1)
            + pb_f.constant * S ^ (pb_f.degree + 1)
          = (pb_f.coefficient + pb_f.constant)
            * S ^ (pb_f.degree + 1) := by ring
    have h_combine :
        ctx 0 *
            (pb_f.coefficient * S ^ pb_f.degree
              + pb_f.constant)
          ≤ (pb_f.coefficient + pb_f.constant)
              * S ^ (pb_f.degree + 1) := by
      have h_step1 :=
        le_trans h_mul_le (le_of_eq h_distrib)
      have h_step2 :
          pb_f.coefficient * S ^ (pb_f.degree + 1)
              + pb_f.constant * S
            ≤ pb_f.coefficient * S ^ (pb_f.degree + 1)
              + pb_f.constant * S ^ (pb_f.degree + 1) :=
        Nat.add_le_add_left h_const_absorb _
      exact le_trans h_step1
        (le_trans h_step2 (le_of_eq h_eq_combine))
    exact le_trans h_sum h_combine

/-!
## On the structural `towerHeight` lemma

A general structural lemma of the form
`Nat.log 2 pb.degree ≤ f.towerHeight`, parameterized over
arbitrary `pb : PolyBound f`, does not hold.  The
`PolyBound` structure does not constrain `degree` from
above when the value bound is satisfied vacuously: for
example, on `ERMor1.zero`, every `pb.bounds` proof reduces
to `0 ≤ ...`, which holds for any choice of `degree`,
`coefficient`, and `constant`.  A user-supplied `pb` with
`degree := 100` is then a valid `PolyBound ERMor1.zero`,
yet `Nat.log 2 100 = 6 > 0 = ERMor1.zero.towerHeight`.

The structural relationship between polynomial degree and
`towerHeight` therefore depends on `pb` being built from
the per-constructor builders `ofZero`, `ofSucc`, `ofProj`,
`ofSub`, `ofComp`, `ofBsum` (the bprod-free fragment;
`bprod`'s value bound is not polynomial in the inputs).
The relationship is established at the call site in Module
C (`LawvereKSimPolynomialBound.lean`) for the specific
`PolyBound`s built for `kSimPackedStep` and
`kSimPackedBase`, where the structural form of the
underlying ER term is known.
-/

end ERMor1.PolyBound

end GebLean
