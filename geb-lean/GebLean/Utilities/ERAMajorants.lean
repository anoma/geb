import GebLean.LawvereER
import GebLean.Utilities.ERArith
import GebLean.LawvereERBoundComputable
import GebLean.LawvereERPolynomialBound
import GebLean.Utilities.Tower

/-!
# Tourlakis A_n^r majorant family in ER

Lean-side realization of Tourlakis 2018 page 22 (proof of
§0.1.0.44 ⊆ direction) majorant family for K^sim level 2:

- `ERMor1.A_one : ERMor1 1` (interp `λx. 2x + 2`).
- `ERMor1.A_one_iter : ℕ → ERMor1 1`
  (interp `λx. 2^r * x + (2^{r+1} - 2)`).
- `ERMor1.A_two_iter : ℕ → ERMor1 1` (alias of
  `ERMor1.towerER`, interp `λx. tower r x`).

`A_one` and `A_one_iter` carry `PolyBound` builders
(linear in the input).  `A_two_iter` does not: `tower r x`
for `r ≥ 1` is not polynomially bounded in `x`, and
`ERMor1.PolyBound` is the bprod-free polynomial fragment
per `LawvereERPolynomialBound.lean`'s structural-towerHeight
section.  Downstream consumers (step 4 majorization,
step 5 `kToER` simrec at level 2) reason about
`A_two_iter`'s growth via `interp_A_two_iter` plus
`Utilities/Tower.lean`'s monotonicity lemmas (`tower_mono_right`,
`tower_mono_left`, `self_le_tower`,
`mul_tower_le_tower_add_two`,
`tower_pow_le_tower_add_three`), and feed the resulting
Nat-level dominance hypothesis into
`simultaneousBoundedRec_interp_correct` directly — no
`PolyBound` builder is invoked at level 2.

See
`docs/superpowers/specs/2026-05-03-step-3-er-tourlakis-A-majorants-design.md`
and master design §3.3 in
`docs/research/2026-05-02-er-ksim2-equiv-via-urm-master-design.md`.
Cross-reference network:
`docs/research/2026-04-30-ksim-polynomial-bound-references.md`
for the polynomial-bound infrastructure context.
-/

namespace GebLean

namespace ERMor1

/-- Tourlakis 2018 page 22 majorant `A_1 = λx. 2x + 2`,
realized as an ER named composite.  Master design §3.3.

Construction: `addN(succ(proj 0), succ(proj 0))`, i.e.
`(x + 1) + (x + 1) = 2x + 2`. -/
def A_one : ERMor1 1 :=
  ERMor1.comp ERMor1.addN fun i => match i with
    | ⟨0, _⟩ => ERMor1.comp ERMor1.succ
                  (fun _ : Fin 1 =>
                    ERMor1.proj (0 : Fin 1))
    | ⟨1, _⟩ => ERMor1.comp ERMor1.succ
                  (fun _ : Fin 1 =>
                    ERMor1.proj (0 : Fin 1))

/-- Closed-form interpretation of `A_one`:
`A_one.interp ![x] = 2 * x + 2` (Tourlakis 2018 page 22,
`A_1`).  Master design §3.3. -/
@[simp] theorem interp_A_one (ctx : Fin 1 → ℕ) :
    A_one.interp ctx = 2 * (ctx 0) + 2 := by
  unfold A_one
  simp only [ERMor1.interp_comp, ERMor1.interp_addN,
    ERMor1.interp_succ, ERMor1.interp_proj]
  omega

/-- Tourlakis 2018 page 22 iterated majorant
`A_1^r = λx. 2^r * x + (2^{r+1} − 2)`, realized as r-fold
composition of `A_one` with itself.  Master design §3.3.

Recursion direction: `A_1 ∘ A_1^r` (apply r-fold first,
then one more `A_one`).  At `r = 0` returns the
identity-on-1, realized as `proj 0`. -/
def A_one_iter : ℕ → ERMor1 1
  | 0     => ERMor1.proj (0 : Fin 1)
  | r + 1 => ERMor1.comp A_one
              (fun _ : Fin 1 => A_one_iter r)

/-- Closed-form interpretation of `A_one_iter`:
`(A_one_iter r).interp ![x] = 2^r * x + (2^{r+1} − 2)`
(Tourlakis 2018 page 22, `A_1^r` r-fold composition closed
form).  Master design §3.3.

Proof outline: induction on `r`.  Base case unfolds
`A_one_iter 0 = proj 0` and reduces by `omega`.  Successor
case unfolds one layer of `A_one_iter (r + 1)`, applies the
`@[simp] interp_A_one` rewrite to collapse the outer
`A_one`, rewrites by the IH, and closes via `omega` after
introducing explicit `pow_succ`-derived equalities for
`2^(r+1)` and `2^(r+2)`, a positivity hypothesis
`Nat.one_le_pow _ _` for the `Nat`-subtraction guard, and
a multiplicative bridge
`2^(r+1) * ctx 0 = 2 * (2^r * ctx 0)` (without which omega
treats the two `* ctx 0` products as independent atoms;
see spec §9.6). -/
@[simp] theorem interp_A_one_iter (r : ℕ)
    (ctx : Fin 1 → ℕ) :
    (A_one_iter r).interp ctx
      = 2 ^ r * (ctx 0) + (2 ^ (r + 1) - 2) := by
  induction r with
  | zero =>
      unfold A_one_iter
      simp only [ERMor1.interp_proj, pow_zero, one_mul]
      omega
  | succ r ih =>
      unfold A_one_iter
      simp only [ERMor1.interp_comp, interp_A_one]
      rw [ih]
      have h_succ1 : 2 ^ (r + 1) = 2 * 2 ^ r := by
        rw [pow_succ]; ring
      have h_succ2 : 2 ^ (r + 2) = 2 * 2 ^ (r + 1) := by
        rw [pow_succ]; ring
      have h_pow_ge_two : 2 ≤ 2 ^ (r + 1) := by
        rw [h_succ1]
        have h_pow_pos_r : 1 ≤ 2 ^ r :=
          Nat.one_le_pow _ _ (by omega)
        omega
      have h_mul_bridge :
          2 ^ (r + 1) * ctx 0 = 2 * (2 ^ r * ctx 0) := by
        rw [h_succ1]; ring
      omega

/-- Tourlakis 2018 page 22 iterated majorant
`A_2^r = λx. tower r x`, realized as the existing named
composite `def ERMor1.towerER` in
`LawvereERBoundComputable.lean`.  Underlying construction
iterates `expER` with base `2`, citing Tourlakis 2018
§0.1.0.17 (c) `λx. 2^x ∈ ER`.  Master design §3.3.

No `PolyBound` builder is provided: `tower r x` for
`r ≥ 1` is not polynomially bounded in `x`, and
`ERMor1.PolyBound` is the bprod-free polynomial fragment
per `LawvereERPolynomialBound.lean`'s structural-towerHeight
section.  See the module docstring for how downstream
consumers handle this. -/
def A_two_iter (r : ℕ) : ERMor1 1 := ERMor1.towerER r

/-- Closed-form interpretation of `A_two_iter`:
`(A_two_iter r).interp ![x] = tower r x` (Tourlakis 2018
page 22, `A_2^r = tower r x`).  Routes through the existing
`interp_towerER` simp lemma.  Master design §3.3. -/
@[simp] theorem interp_A_two_iter (r : ℕ)
    (ctx : Fin 1 → ℕ) :
    (A_two_iter r).interp ctx
      = tower r (ctx 0) := by
  unfold A_two_iter
  exact ERMor1.interp_towerER r ctx

namespace PolyBound

/-- Polynomial bound for `A_one`: linear with leading
coefficient `2` and zero constant.

The bound shape `2 * (sup ctx + 1)^1 + 0` evaluates to
`2 * (sup + 1) = 2 * sup + 2 ≥ 2 * (ctx 0) + 2`, since
`ctx 0 ≤ sup ctx`.  Master design §3.3 amended
polynomial-bound certification subsection. -/
def ofA_one : PolyBound A_one where
  degree      := 1
  coefficient := 2
  constant    := 0
  bounds      := fun ctx => by
    rw [interp_A_one]
    simp only [pow_one, Nat.add_zero]
    have h_ctx0_le_sup :
        ctx 0
          ≤ (Finset.univ : Finset (Fin 1)).sup ctx :=
      Finset.le_sup
        (s := (Finset.univ : Finset (Fin 1)))
        (f := ctx) (b := (0 : Fin 1))
        (Finset.mem_univ _)
    omega

end PolyBound

namespace PolyBound

/-- Polynomial bound for `A_one_iter r`: linear with
leading coefficient `2^r` and constant `2^{r+1} − 2`.

The chosen `(degree, coefficient, constant)` triple
matches the closed-form `interp_A_one_iter` literally:
the closed form `2^r * (ctx 0) + (2^{r+1} − 2)` is
dominated by `2^r * (sup ctx + 1) + (2^{r+1} − 2)`
because `ctx 0 ≤ sup ctx ≤ sup ctx + 1`, so the bounds
proof reduces to a `Nat.mul_le_mul_left` step on the
leading-coefficient slot.  The constant slot is matched
exactly.

Master design §3.3 amended polynomial-bound
certification subsection. -/
def ofA_one_iter (r : ℕ) : PolyBound (A_one_iter r) where
  degree      := 1
  coefficient := 2 ^ r
  constant    := 2 ^ (r + 1) - 2
  bounds      := fun ctx => by
    rw [interp_A_one_iter]
    simp only [pow_one]
    have h_ctx0_le_sup :
        ctx 0
          ≤ (Finset.univ : Finset (Fin 1)).sup ctx :=
      Finset.le_sup
        (s := (Finset.univ : Finset (Fin 1)))
        (f := ctx) (b := (0 : Fin 1))
        (Finset.mem_univ _)
    have h_ctx0_le_succ :
        ctx 0
          ≤ (Finset.univ : Finset (Fin 1)).sup ctx + 1 := by
      omega
    have h_mul :
        2 ^ r * ctx 0
          ≤ 2 ^ r *
              ((Finset.univ : Finset (Fin 1)).sup ctx + 1) :=
      Nat.mul_le_mul_left _ h_ctx0_le_succ
    omega

end PolyBound

end ERMor1

end GebLean
