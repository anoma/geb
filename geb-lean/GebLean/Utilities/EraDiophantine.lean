import GebLean.Era
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Fin

/-!
# The term-to-Diophantine reduction: the monotone `ETm` majorant

The bounded-sum/bounded-product engine packs the values `f 0, …, f (y-1)`
of a summand `f i = Tm.eval eraInterp t (Fin.cons i …)` into the
base-`2^w` digits of a single natural number. A correct packing requires
a uniform width `w` valid across the whole loop range, which in turn
requires an arithmetic-term majorant `A` with `f i < A` for every `i`
in range. This file builds that majorant, `eraMajorant`, the first
dependency-critical sub-task of the engine: it fixes the packing width
(Phase 5) and the witness bounds of the Diophantine encoding (Phase 4),
so it precedes both.

## Main definitions

* `eraMajorant` — a strictly dominating, monotone `ETm` majorant of a
  term, obtained by structural recursion.
* `SimpleMonomial` — Expression (6) of arXiv:2407.12928: a simple
  exponential monomial over `m` variables, with `SimpleMonomial.eval` its
  natural-number denotation.
* `SimpleSum`, `SosTerm`, `SosSystem` — the sum-of-squares atom algebra:
  non-negative sums of monomials, squared-difference / product atoms, and
  systems of atoms, with their `eval` denotations.

## Main statements

* `eraMajorant_spec` — strict domination:
  `Tm.eval eraInterp t ctx < Tm.eval eraInterp (eraMajorant t) ctx`.
* `eraMajorant_pos` — positivity: the majorant evaluates to at least `1`.
* `eraMajorant_mono` — monotonicity: the majorant's denotation is
  monotone in every variable. Combined with `eraMajorant_spec`, this
  bounds `f i` for every `i` below a range bound `y` by the single value
  obtained by substituting `y` for the loop index.
* `SosSystem.eval_eq_zero_iff`, `SosTerm.sqDist_eval_eq_zero_iff`,
  `SosTerm.prod_eval_eq_zero_iff` — the zero-set characterisation of the
  atom algebra.

## Implementation notes

Step-1 reuse assessment (decision note § 7, plan Phase 3.5 Step 1):
`GebLean/Utilities/ERAMajorants.lean` provides the Tourlakis `A`-family
(`A_one`, `A_one_iter`, `A_two_iter`/`towerER`), but typed for `ERMor1`,
not `ETm`; it therefore yields no `ETm`-summand majorant directly and is
not reused here. Its `PolyBound`/`towerER` magnitude bounds concern the
level-2 `K`-simulation argument, a different consumer, and do not feed
this width estimate. The `ETm` majorant is built fresh.

Step-2 construction choice (plan Phase 3.5 Step 2): route (A), structural
recursion on `ETm`. A raw `ETm` is not monotone under `Tm.eval`, because
truncated subtraction (`a - b`), division (`a / b`), and remainder
(`a % b`) all decrease in their second argument. Each of those three is
nonetheless bounded above by its first argument (`a - b ≤ a`,
`a / b ≤ a`, `a % b ≤ a`), so `eraMajorant` over-approximates each by the
majorant of its first argument alone, discarding the non-monotone second
argument. The remaining operations (`add`, `mul`, `pow`, `pow2`, `succ`)
are monotone and are kept; the `pow` case carries an extra `succ` to
force strictness when the base reduces to `1`. This realises the spirit
of the recurrence paper's Claim-2 recipe (route B, "replace `tsub` by an
additive over-approximation") as a single structural recursion. Strict
domination and monotonicity are proved as two separate inductions: the
former needs only itself, the latter needs the former solely for the
`base ≥ 1` side condition of the `pow` case.

Carrier-design choice (plan Phase 4, Task 4.1 Step 1): the Diophantine
predicate is carried as typed `SosSystem` atoms (`sqDist` / `prod` over
`SimpleSum`/`SimpleMonomial`), not as a raw `ETm` paired with a
`Simple : ETm → Prop` predicate. The typed algebra makes non-negativity
and the squared-distance / product zero-set structural, and is preferred
over the raw-`ETm`-plus-`Simple`-predicate fallback.

## References

* Prunescu, Sauras-Altuzarra, Shunia, arXiv:2505.23787 (the basis).
* Istrate, Prunescu, Shunia, arXiv:2606.09336 (the recurrence-to-term
  metatheorem; the majorant supplies its witness bounds).
* Prunescu, arXiv:2407.12928 (Expression (6): the simple exponential
  monomial form of `SimpleMonomial`).

## Tags

elementary recursive, majorant, monotone, Diophantine
-/

namespace GebLean

open Era

/-- A monotone arithmetic-term majorant of `t`. Built by structural
recursion: the monotone operations (`add`, `mul`, `pow`, `pow2`, `succ`)
are preserved, while truncated subtraction, division, and remainder —
each non-monotone in its second argument but bounded above by its first
(`a - b ≤ a`, `a / b ≤ a`, `a % b ≤ a`) — are over-approximated by the
majorant of their first argument. The result strictly dominates `t`
(`eraMajorant_spec`) and is monotone (`eraMajorant_mono`). -/
def eraMajorant {n : Nat} (t : ETm n) : ETm n :=
  match t with
  | .var i  => .succ (.var i)
  | .zero   => one
  | .succ s => .succ (eraMajorant s)
  | .app b ts =>
    match b with
    | .add  => eraMajorant (ts ⟨0, by decide⟩) +ᵉ eraMajorant (ts ⟨1, by decide⟩)
    | .mul  => eraMajorant (ts ⟨0, by decide⟩) *ᵉ eraMajorant (ts ⟨1, by decide⟩)
    | .pow  => .succ (eraMajorant (ts ⟨0, by decide⟩) ^ᵉ eraMajorant (ts ⟨1, by decide⟩))
    | .pow2 => epow2 (eraMajorant (ts ⟨0, by decide⟩))
    | .tsub => eraMajorant (ts ⟨0, by decide⟩)
    | .div  => eraMajorant (ts ⟨0, by decide⟩)
    | .mod  => eraMajorant (ts ⟨0, by decide⟩)

/-- Strict domination: the majorant's denotation strictly exceeds the
term's, at every context. -/
theorem eraMajorant_spec {n : Nat} (t : ETm n) (ctx : Fin n → Nat) :
    Tm.eval eraInterp t ctx < Tm.eval eraInterp (eraMajorant t) ctx := by
  induction t with
  | var i => simp only [eraMajorant, Tm.eval]; omega
  | zero => simp only [eraMajorant, one, Tm.eval]; omega
  | succ s ih => simp only [eraMajorant, Tm.eval]; omega
  | app b ts ih =>
    cases b
    · simp only [eraMajorant, Tm.eval, eraInterp, eadd_eval, fcons]
      have h0 := ih ⟨0, by decide⟩
      have h1 := ih ⟨1, by decide⟩
      omega
    · simp only [eraMajorant, Tm.eval, eraInterp]
      exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) (ih ⟨0, by decide⟩)
    · simp only [eraMajorant, Tm.eval, eraInterp, epow2_eval, fcons]
      exact Nat.pow_lt_pow_right Nat.one_lt_two (ih ⟨0, by decide⟩)
    · simp only [eraMajorant, Tm.eval, eraInterp]
      exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) (ih ⟨0, by decide⟩)
    · simp only [eraMajorant, Tm.eval, eraInterp, emul_eval, fcons]
      exact Nat.mul_lt_mul'' (ih ⟨0, by decide⟩) (ih ⟨1, by decide⟩)
    · simp only [eraMajorant, Tm.eval, eraInterp]
      exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (ih ⟨0, by decide⟩)
    · simp only [eraMajorant, Tm.eval, eraInterp, epow_eval, fcons]
      have h := Nat.le_trans (Nat.pow_le_pow_left (Nat.le_of_lt (ih ⟨0, by decide⟩)) _)
        (Nat.pow_le_pow_right (Nat.lt_of_le_of_lt (Nat.zero_le _) (ih ⟨0, by decide⟩))
          (Nat.le_of_lt (ih ⟨1, by decide⟩)))
      omega

/-- Positivity: the majorant evaluates to at least `1`, since it strictly
exceeds a natural number. -/
theorem eraMajorant_pos {n : Nat} (t : ETm n) (ctx : Fin n → Nat) :
    0 < Tm.eval eraInterp (eraMajorant t) ctx :=
  Nat.lt_of_le_of_lt (Nat.zero_le _) (eraMajorant_spec t ctx)

/-- Monotonicity: the majorant's denotation is monotone in every variable.
With `eraMajorant_spec`, this bounds `f i` for every `i` below a range
bound `y` by the single value at the range bound, supplying the uniform
packing width the engine requires. -/
theorem eraMajorant_mono {n : Nat} (t : ETm n) {ctx ctx' : Fin n → Nat}
    (h : ∀ i, ctx i ≤ ctx' i) :
    Tm.eval eraInterp (eraMajorant t) ctx ≤ Tm.eval eraInterp (eraMajorant t) ctx' := by
  induction t with
  | var i => simp only [eraMajorant, Tm.eval]; exact Nat.add_le_add_right (h i) 1
  | zero => exact Nat.le_refl _
  | succ s ih => simp only [eraMajorant, Tm.eval]; exact Nat.add_le_add_right ih 1
  | app b ts ih =>
    cases b
    · simp only [eraMajorant, eraInterp, eadd_eval, fcons]
      exact Nat.add_le_add (ih ⟨0, by decide⟩) (ih ⟨1, by decide⟩)
    · simp only [eraMajorant]; exact ih ⟨0, by decide⟩
    · simp only [eraMajorant, eraInterp, epow2_eval, fcons]
      exact Nat.pow_le_pow_right (by decide) (ih ⟨0, by decide⟩)
    · simp only [eraMajorant]; exact ih ⟨0, by decide⟩
    · simp only [eraMajorant, eraInterp, emul_eval, fcons]
      exact Nat.mul_le_mul (ih ⟨0, by decide⟩) (ih ⟨1, by decide⟩)
    · simp only [eraMajorant]; exact ih ⟨0, by decide⟩
    · simp only [eraMajorant, Tm.eval, eraInterp, epow_eval, fcons]
      have h := Nat.le_trans (Nat.pow_le_pow_left (ih ⟨0, by decide⟩) _)
        (Nat.pow_le_pow_right (eraMajorant_pos (ts ⟨0, by decide⟩) ctx')
          (ih ⟨1, by decide⟩))
      omega

/-- A simple exponential monomial over `m` variables (arXiv:2407.12928,
Expression (6)):
`coeff · ∏ᵢ (expBase i) ^ ((expCoeff i) · xᵢ) · ∏ᵢ xᵢ ^ (polyExp i)`.
The coefficient and the per-variable exponential bases and coefficients are
`ETm m`-valued, so monomials compose with the Era term language; the
per-variable polynomial exponents are constant naturals, and the value of a
monomial is a natural number. -/
structure SimpleMonomial (m : ℕ) where
  /-- The leading coefficient. -/
  coeff : ETm m
  /-- The per-variable exponential base. -/
  expBase : Fin m → ETm m
  /-- The per-variable exponential coefficient, multiplying the variable in
  the exponent. -/
  expCoeff : Fin m → ETm m
  /-- The per-variable constant polynomial exponent. -/
  polyExp : Fin m → ℕ

/-- The natural-number denotation of a simple monomial at a context `ρ`:
`coeff · ∏ᵢ (expBase i) ^ ((expCoeff i) · ρ i) · ∏ᵢ (ρ i) ^ (polyExp i)`,
with the `ETm`-valued fields evaluated by `Tm.eval eraInterp`. -/
def SimpleMonomial.eval {m : ℕ} (mon : SimpleMonomial m) (ρ : Fin m → ℕ) : ℕ :=
  Tm.eval eraInterp mon.coeff ρ
    * (∏ i, Tm.eval eraInterp (mon.expBase i) ρ
        ^ (Tm.eval eraInterp (mon.expCoeff i) ρ * ρ i))
    * (∏ i, ρ i ^ mon.polyExp i)

/-- A non-negative sum of simple monomials. -/
abbrev SimpleSum (m : ℕ) := List (SimpleMonomial m)

/-- The denotation of a simple sum: the sum of its monomials' values. -/
def SimpleSum.eval {m : ℕ} (p : SimpleSum m) (ρ : Fin m → ℕ) : ℕ :=
  (p.map (fun mon => mon.eval ρ)).sum

/-- A sum-of-squares atom over `m` variables: either a symmetric truncated
squared distance `(P − Q)² + (Q − P)²` between two simple sums (zero iff
`P = Q`), or a product of two sub-systems (zero iff one sub-system is zero). -/
inductive SosTerm (m : ℕ) where
  /-- The symmetric truncated squared distance `(P − Q)² + (Q − P)²`. -/
  | sqDist : SimpleSum m → SimpleSum m → SosTerm m
  /-- The product of two sub-systems' denotations. -/
  | prod : List (SosTerm m) → List (SosTerm m) → SosTerm m

/-- A sum-of-squares system over `m` variables; its denotation is the sum
over its atoms. -/
abbrev SosSystem (m : ℕ) := List (SosTerm m)

mutual
/-- The denotation of a sum-of-squares atom at a context `ρ`. A `sqDist P Q`
atom denotes the symmetric truncated squared distance
`(P.eval ρ − Q.eval ρ)² + (Q.eval ρ − P.eval ρ)²` (the two terms make it zero
exactly on equality, working around truncated subtraction); a `prod s t` atom
denotes the product `SosSystem.eval s ρ · SosSystem.eval t ρ`. -/
def SosTerm.eval {m : ℕ} (a : SosTerm m) (ρ : Fin m → ℕ) : ℕ :=
  match a with
  | .sqDist P Q =>
    (P.eval ρ - Q.eval ρ) ^ 2 + (Q.eval ρ - P.eval ρ) ^ 2
  | .prod s t => SosSystem.eval s ρ * SosSystem.eval t ρ
--
/-- The denotation of a sum-of-squares system at a context `ρ`: the sum of
its atoms' denotations. -/
def SosSystem.eval {m : ℕ} (s : SosSystem m) (ρ : Fin m → ℕ) : ℕ :=
  match s with
  | [] => 0
  | a :: rest => SosTerm.eval a ρ + SosSystem.eval rest ρ
end

/-- A sum-of-squares system is zero exactly when each of its atoms is. -/
theorem SosSystem.eval_eq_zero_iff {m : ℕ} (s : SosSystem m) (ρ : Fin m → ℕ) :
    SosSystem.eval s ρ = 0 ↔ ∀ a ∈ s, SosTerm.eval a ρ = 0 := by
  induction s with
  | nil => simp [SosSystem.eval]
  | cons a rest ih =>
    rw [SosSystem.eval, Nat.add_eq_zero_iff, List.forall_mem_cons, ih]

/-- A squared-distance atom is zero iff its two simple sums are equal. -/
theorem SosTerm.sqDist_eval_eq_zero_iff {m : ℕ} (P Q : SimpleSum m) (ρ : Fin m → ℕ) :
    SosTerm.eval (.sqDist P Q) ρ = 0 ↔ P.eval ρ = Q.eval ρ := by
  simp only [SosTerm.eval, Nat.add_eq_zero_iff, Nat.pow_eq_zero,
    Nat.sub_eq_zero_iff_le]
  omega

/-- A product atom is zero iff one of its two sub-systems is zero. -/
theorem SosTerm.prod_eval_eq_zero_iff {m : ℕ} (s t : List (SosTerm m)) (ρ : Fin m → ℕ) :
    SosTerm.eval (.prod s t) ρ = 0 ↔ SosSystem.eval s ρ = 0 ∨ SosSystem.eval t ρ = 0 := by
  rw [SosTerm.eval, Nat.mul_eq_zero]

/-- A bounded, unique-witness, sum-of-squares Diophantine encoding of an
`ETm n` term's graph `t.eval ρ = y` (arXiv:2606.09336, Lemma 2). System
variables: the `n` inputs, then the output `y` at index `n`, then
`witArity` witnesses. "Sum of squares" and "simple" are structural
(`SosSystem`). -/
structure DiophEnc (n : ℕ) where
  /-- The number of witness variables, beyond the `n` inputs and output. -/
  witArity : ℕ
  /-- The sum-of-squares system over the `n` inputs, the output, and the
  witnesses, whose zero set is the term's graph. -/
  sys : SosSystem (n + 1 + witArity)
  /-- The per-witness bound: an `ETm (n + 1)` over the inputs and output that
  strictly dominates the witness, making the witness unique. -/
  bound : Fin witArity → ETm (n + 1)

/-- Assemble inputs `ρ`, output `y`, and witnesses `w` into the system's
context `Fin (n + 1 + e.witArity) → ℕ`. -/
def DiophEnc.ctx {n : ℕ} (e : DiophEnc n) (ρ : Fin n → ℕ) (y : ℕ)
    (w : Fin e.witArity → ℕ) : Fin (n + 1 + e.witArity) → ℕ :=
  Fin.append (Fin.snoc ρ y) w

end GebLean
