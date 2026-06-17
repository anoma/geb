import GebLean.Era
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Nat.ModEq

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
* `Era.Tm.weaken`, `SimpleMonomial.weaken`, `SimpleSum.weaken`,
  `SosTerm.weaken`, `SosSystem.weaken` — re-indexing of the atom algebra
  along a variable map `f : Fin m → Fin m'`, lifting an `m`-variable
  object to an `m'`-variable context.
* `spliceEmb`, `SosSystem.spliceWeaken` — the variable embedding splicing a
  sub-encoding over `Fin (n + 1 + wSub)` into a compound layout over
  `Fin (n + 1 + wComp)` (inputs fixed, sub-output to a witness slot,
  sub-witnesses to a witness block), and the system re-indexing along it.
* `DiophEnc.Encodes` — the correctness contract of a `DiophEnc n` for a
  unary-output function: soundness, unique-witness completeness, input-only
  witness boundedness, and value majorisation.
* `diophVar`, `diophZero`, `diophSucc` — the projection, constant-zero, and
  successor combinators on `DiophEnc`s, each proved to satisfy `Encodes`
  (`diophVar_encodes`, `diophZero_encodes`, `diophSucc_encodes`).
* `binAssemble`, `binBound`, `binSplicedSys` — the binary-combine layout: the
  four-block assembly of compound data, the per-witness bound map, and the
  two-sub spliced system over the layout `Fin (w1 + 1 + w2 + 1)`, with slot
  embeddings `binWitEmb1`/`binOutSlot1`/`binWitEmb2`/`binOutSlot2` and the case
  recursor `binLayoutCases`.
* `diophAdd`, `diophMul`, `diophPow2` — the addition, multiplication, and
  base-`2` power combinators on `DiophEnc`s (arXiv:2606.09336, Lemma 2 Cases 2
  and 1, and the multiplication gadget), each proved to satisfy `Encodes`
  (`diophAdd_encodes`, `diophMul_encodes`, `diophPow2_encodes`).
* `binExtEmb`, `binExtSplicedSys`, `binExtAssemble`, `binExtBound`,
  `binExtLayoutCases` — the binary-combine layer extended by `k` local witnesses:
  the layout `Fin (w1 + 1 + w2 + 1 + k)` = `[sub1 wit, y₁, sub2 wit, y₂, locals]`,
  with the binary block weakened along `binExtEmb`, the local-aware data assembly,
  per-witness bound map, and five-way slot recursor (slot embeddings
  `binExtWitEmb1`/`binExtOutSlot1`/`binExtWitEmb2`/`binExtOutSlot2`/`binExtLocalSlot`).
* `diophMod`, `diophTsub`, `diophDiv` — the remainder, truncated-subtraction, and
  division combinators on `DiophEnc`s (arXiv:2606.09336, Lemma 2 Case 3, the monus
  gadget, and the division gadget), each proved to satisfy `Encodes`
  (`diophMod_encodes`, `diophTsub_encodes`, `diophDiv_encodes`).
* `diophOne`, `diophPow` — the constant-`1` and general-power combinators on
  `DiophEnc`s, the latter a composition of existing combinators along Marchenkov's
  identity `pow_eq_two_pow_mod`, proved to satisfy `Encodes` (`diophPow_encodes`).
* `diophOf` — the term-to-Diophantine reduction: a `DiophEnc n` for every `ETm n`,
  obtained by structural recursion dispatching each constructor to its combinator.

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
* `Era.Tm.eval_weaken`, `SimpleMonomial.eval_weaken`,
  `SimpleSum.eval_weaken`, `SosTerm.eval_weaken`, `SosSystem.eval_weaken` —
  re-indexing compatibility: evaluating a weakened object at `ρ'` equals
  evaluating the original at `ρ' ∘ f` (the monomial, sum, term, and system
  cases assume `Function.Injective f`, so each weakened variable has a
  unique source).
* `spliceEmb_injective`, `SosSystem.eval_spliceWeaken` — injectivity of the
  splicing embedding (under a witness-block injectivity and slot-disjointness
  hypothesis) and the resulting re-indexing compatibility.
* `diophVar_encodes`, `diophZero_encodes`, `diophSucc_encodes` — the
  `Encodes` correctness of the projection, constant-zero, and successor
  combinators (the last preserving `Encodes` from a sub-encoding).
* `append_snoc_comp_spliceEmb`, `binSplicedSys_eval` — the generic
  context-recovery identity for a single splice and the additive evaluation of
  the binary spliced system into its two sub-systems.
* `diophAdd_encodes`, `diophMul_encodes`, `diophPow2_encodes` — the `Encodes`
  correctness of the addition, multiplication, and base-`2` power combinators,
  each preserving `Encodes` from its sub-encodings.
* `binExtSplicedSys_eval` — the additive evaluation of the extended binary spliced
  system into its two sub-systems.
* `diophMod_encodes`, `diophTsub_encodes`, `diophDiv_encodes` — the `Encodes`
  correctness of the remainder, truncated-subtraction, and division combinators,
  each preserving `Encodes` from its two sub-encodings.
* `diophPow_encodes` — the `Encodes` correctness of the general-power combinator,
  obtained by chaining the `Encodes` lemmas of its constituent combinators along
  `pow_eq_two_pow_mod`.
* `diophOf_encodes` — the `Encodes` correctness of `diophOf`, by induction over the
  term, each constructor case transporting the matching combinator's `Encodes`
  lemma along `DiophEnc.Encodes_congr`.
* `diophOf_graph_iff`, `diophOf_unique`, `diophOf_bound` — the reduction's graph
  characterisation, witness uniqueness, and input-only witness boundedness,
  unpacked from `diophOf_encodes`.

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

Re-indexing computability (plan Phase 4, Task 4.4): `weaken` along a
general `f : Fin m → Fin m'` is a `def`, so its body must execute without
`Classical.choice`. The `ETm`-valued fields are renamed by
`Era.Tm.weaken f` (substitution of `fun i => .var (f i)`). The
per-target-index data of a weakened monomial reads off the source index
`i` with `f i = j` via the computable finite search `preimage` (a
`List.find?` over `List.finRange`), defaulting off the image of `f` to
`.zero` / `0`; those off-image factors contribute `_ ^ 0 = 1` and so do
not affect the value. The eval-compatibility proofs assume
`Function.Injective f`, under which `preimage` recovers the unique source
(`preimage_apply`), and re-index the `Finset.prod` over `Fin m'` to the
product over `Fin m` by `Finset.prod_of_injOn`.

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

/-- The base-`2` envelope bound underlying Marchenkov's identity:
`a ^ b + a < 2 ^ (a * b + a + 1)`. It supplies both `a < 2 ^ (a * b + a + 1)`
(so the modulus `2 ^ (a * b + a + 1) - a` is positive) and the strict bound
`a ^ b < 2 ^ (a * b + a + 1) - a` that makes the residue exact. The proof
chains `a ^ b ≤ 2 ^ (a * b)` (from `a < 2 ^ a`) with `2 ^ (a * b + a + 1) =
2 ^ (a * b + a) + 2 ^ (a * b + a)`. -/
private lemma pow_add_lt_two_pow (a b : ℕ) : a ^ b + a < 2 ^ (a * b + a + 1) := by
  have h1 : a ^ b ≤ 2 ^ (a * b) := by
    calc a ^ b ≤ (2 ^ a) ^ b := Nat.pow_le_pow_left (Nat.le_of_lt Nat.lt_two_pow_self) b
      _ = 2 ^ (a * b) := by rw [← Nat.pow_mul]
  have h2 : a < 2 ^ a := Nat.lt_two_pow_self
  have h3 : 2 ^ (a * b) ≤ 2 ^ (a * b + a) :=
    Nat.pow_le_pow_right (by decide) (Nat.le_add_right _ _)
  have h4 : 2 ^ a ≤ 2 ^ (a * b + a) :=
    Nat.pow_le_pow_right (by decide) (Nat.le_add_left _ _)
  have h5 : 2 ^ (a * b + a + 1) = 2 ^ (a * b + a) + 2 ^ (a * b + a) := by
    rw [Nat.pow_succ, Nat.mul_two]
  omega

/-- Marchenkov's identity (arXiv:2407.12928, eq. (4); arXiv:2606.09336
§ 3): a variable-base, variable-exponent power as a base-2 power modulo a
term. Valid for all `a b : ℕ`, including `0 ^ 0 = 1`. -/
theorem pow_eq_two_pow_mod (a b : ℕ) :
    a ^ b = 2 ^ ((a * b + a + 1) * b) % (2 ^ (a * b + a + 1) - a) := by
  have hcrux : a ^ b + a < 2 ^ (a * b + a + 1) := pow_add_lt_two_pow a b
  set M := a * b + a + 1 with hM
  have haM : a < 2 ^ M := by omega
  rcases Nat.eq_zero_or_pos b with hb | hb
  · subst hb
    have hM0 : M = a + 1 := by omega
    rw [hM0]
    simp only [Nat.mul_zero, Nat.pow_zero]
    have hp : 2 ^ a + 2 ^ a = 2 ^ (a + 1) := by rw [Nat.pow_succ, Nat.mul_two]
    have h2a : a < 2 ^ a := Nat.lt_two_pow_self
    rw [Nat.mod_eq_of_lt]
    omega
  · have hbase : 2 ^ M ≡ a [MOD 2 ^ M - a] := by
      have hsac : (2 ^ M - a) + a = 2 ^ M := Nat.sub_add_cancel (Nat.le_of_lt haM)
      calc 2 ^ M = (2 ^ M - a) + a := hsac.symm
        _ ≡ 0 + a [MOD 2 ^ M - a] :=
          Nat.ModEq.add_right a (Nat.modEq_zero_iff_dvd.mpr (dvd_refl _))
        _ = a := by rw [Nat.zero_add]
    have key : 2 ^ (M * b) ≡ a ^ b [MOD 2 ^ M - a] := by
      calc 2 ^ (M * b) = (2 ^ M) ^ b := by rw [Nat.pow_mul]
        _ ≡ a ^ b [MOD 2 ^ M - a] := hbase.pow b
    have hlt : a ^ b < 2 ^ M - a := by omega
    rw [key, Nat.mod_eq_of_lt hlt]

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

/-- The denotation of a concatenated system is the sum of the parts'
denotations. -/
theorem SosSystem.eval_append {m : ℕ} (s t : SosSystem m) (ρ : Fin m → ℕ) :
    SosSystem.eval (s ++ t) ρ = SosSystem.eval s ρ + SosSystem.eval t ρ := by
  induction s with
  | nil => simp only [List.nil_append, SosSystem.eval, Nat.zero_add]
  | cons a rest ih =>
    rw [List.cons_append, SosSystem.eval, SosSystem.eval, ih, Nat.add_assoc]

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

/-- The computable preimage search for re-indexing: the first source index
`i` of `Fin m` with `f i = j`, or `none` when `j` is outside the image of
`f`. Implemented by `List.find?` over `List.finRange`, so it executes
without `Classical.choice`. -/
def preimage {m m' : ℕ} (f : Fin m → Fin m') (j : Fin m') : Option (Fin m) :=
  (List.finRange m).find? (fun i => decide (f i = j))

/-- For an injective `f`, the preimage of `f i` is the unique source `i`. -/
theorem preimage_apply {m m' : ℕ} {f : Fin m → Fin m'} (hf : Function.Injective f)
    (i : Fin m) : preimage f (f i) = some i := by
  unfold preimage
  rw [List.find?_eq_some_iff_getElem]
  refine ⟨by simp, i.val, ?_, ?_, ?_⟩
  · rw [List.length_finRange]; exact i.isLt
  · rw [List.getElem_finRange]; rfl
  · intro j hj
    rw [List.getElem_finRange]
    simp only [Bool.not_eq_true', decide_eq_false_iff_not]
    intro h
    have heq := hf h
    rw [Fin.ext_iff] at heq
    simp only [Fin.val_cast] at heq
    omega

/-- The preimage is `none` for a target index outside the image of `f`. -/
theorem preimage_eq_none {m m' : ℕ} {f : Fin m → Fin m'} {j : Fin m'}
    (h : ∀ i, f i ≠ j) : preimage f j = none := by
  unfold preimage
  rw [List.find?_eq_none]
  intro i _
  simp only [decide_eq_true_eq]
  exact h i

/-- Re-index a simple monomial along a variable map `f : Fin m → Fin m'`.
The coefficient and per-variable exponential bases and coefficients are
renamed by `Era.Tm.weaken f`; each target index `j` reads the source data
of the unique `i` with `f i = j` (`preimage`), defaulting off the image of
`f` to `.zero` / `0`, whose factors then contribute `_ ^ 0 = 1`. -/
def SimpleMonomial.weaken {m m' : ℕ} (mon : SimpleMonomial m) (f : Fin m → Fin m') :
    SimpleMonomial m' where
  coeff := mon.coeff.weaken f
  expBase := fun j =>
    match preimage f j with
    | some i => (mon.expBase i).weaken f
    | none => .zero
  expCoeff := fun j =>
    match preimage f j with
    | some i => (mon.expCoeff i).weaken f
    | none => .zero
  polyExp := fun j =>
    match preimage f j with
    | some i => mon.polyExp i
    | none => 0

/-- Re-indexing compatibility for monomials: for injective `f`, evaluating
`mon.weaken f` at `ρ'` equals evaluating `mon` at `ρ' ∘ f`. The off-image
factors are `1`, and `Finset.prod_of_injOn` re-indexes the products over
`Fin m'` to the products over `Fin m`. -/
theorem SimpleMonomial.eval_weaken {m m' : ℕ} (mon : SimpleMonomial m)
    (f : Fin m → Fin m') (hf : Function.Injective f) (ρ' : Fin m' → ℕ) :
    (mon.weaken f).eval ρ' = mon.eval (ρ' ∘ f) := by
  unfold SimpleMonomial.eval SimpleMonomial.weaken
  congr 1
  · congr 1
    · exact Tm.eval_weaken eraInterp f mon.coeff ρ'
    · refine (Finset.prod_of_injOn f (fun a _ b _ h => hf h) (fun _ _ => Finset.mem_univ _)
        ?_ ?_).symm
      · intro j _ hj
        have hnone : preimage f j = none := by
          apply preimage_eq_none
          intro i hi
          exact hj ⟨i, Finset.mem_univ i, hi⟩
        simp only [hnone]
        simp only [Tm.eval]
        rw [Nat.zero_mul, Nat.pow_zero]
      · intro i _
        simp only [preimage_apply hf]
        rw [Tm.eval_weaken, Tm.eval_weaken]
        rfl
  · refine (Finset.prod_of_injOn f (fun a _ b _ h => hf h) (fun _ _ => Finset.mem_univ _)
      ?_ ?_).symm
    · intro j _ hj
      have hnone : preimage f j = none := by
        apply preimage_eq_none
        intro i hi
        exact hj ⟨i, Finset.mem_univ i, hi⟩
      simp only [hnone]
      rw [Nat.pow_zero]
    · intro i _
      simp only [preimage_apply hf]
      rfl

/-- Re-index a simple sum along `f`, by re-indexing each monomial. -/
def SimpleSum.weaken {m m' : ℕ} (p : SimpleSum m) (f : Fin m → Fin m') : SimpleSum m' :=
  p.map (fun mon => mon.weaken f)

/-- Re-indexing compatibility for sums: for injective `f`, evaluating
`p.weaken f` at `ρ'` equals evaluating `p` at `ρ' ∘ f`. -/
theorem SimpleSum.eval_weaken {m m' : ℕ} (p : SimpleSum m) (f : Fin m → Fin m')
    (hf : Function.Injective f) (ρ' : Fin m' → ℕ) :
    (p.weaken f).eval ρ' = p.eval (ρ' ∘ f) := by
  unfold SimpleSum.eval SimpleSum.weaken
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro mon _
  exact mon.eval_weaken f hf ρ'

mutual
/-- Re-index a sum-of-squares atom along `f`, recursing into its simple
sums (for `sqDist`) or sub-systems (for `prod`). -/
def SosTerm.weaken {m m' : ℕ} (a : SosTerm m) (f : Fin m → Fin m') : SosTerm m' :=
  match a with
  | .sqDist P Q => .sqDist (P.weaken f) (Q.weaken f)
  | .prod s t => .prod (SosSystem.weaken s f) (SosSystem.weaken t f)
--
/-- Re-index a sum-of-squares system along `f`, by re-indexing each atom. -/
def SosSystem.weaken {m m' : ℕ} (s : SosSystem m) (f : Fin m → Fin m') : SosSystem m' :=
  match s with
  | [] => []
  | a :: rest => a.weaken f :: SosSystem.weaken rest f
end

mutual
/-- Re-indexing compatibility for atoms: for injective `f`, evaluating
`a.weaken f` at `ρ'` equals evaluating `a` at `ρ' ∘ f`. -/
theorem SosTerm.eval_weaken {m m' : ℕ} (a : SosTerm m) (f : Fin m → Fin m')
    (hf : Function.Injective f) (ρ' : Fin m' → ℕ) :
    (a.weaken f).eval ρ' = a.eval (ρ' ∘ f) := by
  match a with
  | .sqDist P Q =>
    simp only [SosTerm.weaken, SosTerm.eval, P.eval_weaken f hf ρ', Q.eval_weaken f hf ρ']
  | .prod s t =>
    simp only [SosTerm.weaken, SosTerm.eval, SosSystem.eval_weaken s f hf ρ',
      SosSystem.eval_weaken t f hf ρ']
--
/-- Re-indexing compatibility for systems: for injective `f`, evaluating
`s.weaken f` at `ρ'` equals evaluating `s` at `ρ' ∘ f`. -/
theorem SosSystem.eval_weaken {m m' : ℕ} (s : SosSystem m) (f : Fin m → Fin m')
    (hf : Function.Injective f) (ρ' : Fin m' → ℕ) :
    (s.weaken f).eval ρ' = s.eval (ρ' ∘ f) := by
  match s with
  | [] => simp only [SosSystem.weaken, SosSystem.eval]
  | a :: rest =>
    simp only [SosSystem.weaken, SosSystem.eval, a.eval_weaken f hf ρ',
      SosSystem.eval_weaken rest f hf ρ']
end

/-- The variable embedding splicing a sub-encoding's layout
`Fin (n + 1 + wSub)` into a compound layout `Fin (n + 1 + wComp)`: the `n`
inputs are fixed, the sub-output index `n` is sent to the compound witness
slot `outSlot`, and the sub-witnesses are sent through `witEmb` into the
compound witness block. Built from `Fin.addCases` / `Fin.lastCases`, so it
executes. -/
def spliceEmb {n wSub wComp : ℕ} (outSlot : Fin wComp) (witEmb : Fin wSub → Fin wComp) :
    Fin (n + 1 + wSub) → Fin (n + 1 + wComp) :=
  Fin.addCases
    (Fin.lastCases (Fin.natAdd (n + 1) outSlot)
      (fun i => Fin.castAdd wComp i.castSucc))
    (fun k => Fin.natAdd (n + 1) (witEmb k))

/-- Injectivity of `spliceEmb`: the inputs land in the input block and the
sub-output and sub-witnesses land in the witness block, so the two never
collide; within the witness block, injectivity follows from `witEmb` being
injective and missing `outSlot`. -/
theorem spliceEmb_injective {n wSub wComp : ℕ} (outSlot : Fin wComp)
    (witEmb : Fin wSub → Fin wComp) (hwit : Function.Injective witEmb)
    (hout : ∀ k, witEmb k ≠ outSlot) :
    Function.Injective (spliceEmb (n := n) outSlot witEmb) := by
  intro a b hab
  unfold spliceEmb at hab
  induction a using Fin.addCases with
  | left ia =>
    induction b using Fin.addCases with
    | left ib =>
      simp only [Fin.addCases_left] at hab
      induction ia using Fin.lastCases with
      | last =>
        induction ib using Fin.lastCases with
        | last => rfl
        | cast jb =>
          simp only [Fin.lastCases_last, Fin.lastCases_castSucc] at hab
          rw [Fin.ext_iff] at hab
          simp only [Fin.val_natAdd, Fin.val_castAdd, Fin.val_castSucc] at hab
          omega
      | cast ja =>
        induction ib using Fin.lastCases with
        | last =>
          simp only [Fin.lastCases_last, Fin.lastCases_castSucc] at hab
          rw [Fin.ext_iff] at hab
          simp only [Fin.val_natAdd, Fin.val_castAdd, Fin.val_castSucc] at hab
          omega
        | cast jb =>
          simp only [Fin.lastCases_castSucc] at hab
          have := Fin.castAdd_injective _ _ hab
          rw [Fin.castSucc_inj] at this
          rw [this]
    | right kb =>
      simp only [Fin.addCases_left, Fin.addCases_right] at hab
      induction ia using Fin.lastCases with
      | last =>
        simp only [Fin.lastCases_last] at hab
        have := Fin.natAdd_injective _ _ hab
        exact absurd this.symm (hout kb)
      | cast ja =>
        simp only [Fin.lastCases_castSucc] at hab
        rw [Fin.ext_iff] at hab
        simp only [Fin.val_castAdd, Fin.val_castSucc, Fin.val_natAdd] at hab
        omega
  | right ka =>
    induction b using Fin.addCases with
    | left ib =>
      simp only [Fin.addCases_left, Fin.addCases_right] at hab
      induction ib using Fin.lastCases with
      | last =>
        simp only [Fin.lastCases_last] at hab
        have := Fin.natAdd_injective _ _ hab
        exact absurd this (hout ka)
      | cast jb =>
        simp only [Fin.lastCases_castSucc] at hab
        rw [Fin.ext_iff] at hab
        simp only [Fin.val_castAdd, Fin.val_castSucc, Fin.val_natAdd] at hab
        omega
    | right kb =>
      simp only [Fin.addCases_right] at hab
      have := Fin.natAdd_injective _ _ hab
      rw [hwit this]

/-- Splice a sub-encoding's system over `Fin (n + 1 + wSub)` into the
compound layout `Fin (n + 1 + wComp)`, by re-indexing along `spliceEmb`. -/
def SosSystem.spliceWeaken {n wSub wComp : ℕ} (s : SosSystem (n + 1 + wSub))
    (outSlot : Fin wComp) (witEmb : Fin wSub → Fin wComp) : SosSystem (n + 1 + wComp) :=
  s.weaken (spliceEmb outSlot witEmb)

/-- Re-indexing compatibility for the splice: under the embedding's
injectivity hypotheses, evaluating the spliced system at `ρ'` equals
evaluating the sub-system at `ρ' ∘ spliceEmb …`. An instance of
`SosSystem.eval_weaken`. -/
theorem SosSystem.eval_spliceWeaken {n wSub wComp : ℕ} (s : SosSystem (n + 1 + wSub))
    (outSlot : Fin wComp) (witEmb : Fin wSub → Fin wComp) (hwit : Function.Injective witEmb)
    (hout : ∀ k, witEmb k ≠ outSlot) (ρ' : Fin (n + 1 + wComp) → ℕ) :
    (s.spliceWeaken outSlot witEmb).eval ρ' = s.eval (ρ' ∘ spliceEmb outSlot witEmb) :=
  s.eval_weaken (spliceEmb outSlot witEmb) (spliceEmb_injective outSlot witEmb hwit hout) ρ'

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
  /-- The per-witness bound: an input-only `ETm n` over the `n` inputs that
  strictly dominates the witness, making the witness unique. -/
  bound : Fin witArity → ETm n
  /-- An input-only `ETm n` over the `n` inputs that strictly dominates the
  encoded value `g ρ`. -/
  valBound : ETm n

/-- Assemble inputs `ρ`, output `y`, and witnesses `w` into the system's
context `Fin (n + 1 + e.witArity) → ℕ`. -/
def DiophEnc.ctx {n : ℕ} (e : DiophEnc n) (ρ : Fin n → ℕ) (y : ℕ)
    (w : Fin e.witArity → ℕ) : Fin (n + 1 + e.witArity) → ℕ :=
  Fin.append (Fin.snoc ρ y) w

/-- The simple monomial over `Fin m` whose value at `ρ` is exactly `ρ j`: the
coefficient is the variable `j`, every exponential coefficient and every
polynomial exponent is zero, so all product factors are `1`. -/
def SimpleMonomial.var {m : ℕ} (j : Fin m) : SimpleMonomial m where
  coeff := .var j
  expBase := fun _ => .zero
  expCoeff := fun _ => .zero
  polyExp := fun _ => 0

/-- The variable monomial evaluates to the value of its variable. -/
@[simp]
theorem SimpleMonomial.var_eval {m : ℕ} (j : Fin m) (ρ : Fin m → ℕ) :
    (SimpleMonomial.var j).eval ρ = ρ j := by
  simp only [SimpleMonomial.eval, SimpleMonomial.var, Tm.eval, Nat.zero_mul, Nat.pow_zero,
    Finset.prod_const_one, Nat.mul_one]

/-- The constant simple monomial over `Fin m` whose value at every `ρ` is `1`:
the coefficient is `1` and all product factors are `1`. -/
def SimpleMonomial.one {m : ℕ} : SimpleMonomial m where
  coeff := Era.one
  expBase := fun _ => .zero
  expCoeff := fun _ => .zero
  polyExp := fun _ => 0

/-- The constant monomial evaluates to `1`. -/
@[simp]
theorem SimpleMonomial.one_eval {m : ℕ} (ρ : Fin m → ℕ) :
    (SimpleMonomial.one (m := m)).eval ρ = 1 := by
  simp only [SimpleMonomial.eval, SimpleMonomial.one, Era.one, Tm.eval, Nat.zero_mul,
    Nat.pow_zero, Finset.prod_const_one, Nat.mul_one, Nat.zero_add]

/-- The simple monomial over `Fin m` whose value at `ρ` is the product
`ρ j * ρ k`: the coefficient is the term `var j * var k`, and every exponential
coefficient and polynomial exponent is zero, so all product factors are `1`. -/
def SimpleMonomial.mulVars {m : ℕ} (j k : Fin m) : SimpleMonomial m where
  coeff := .var j *ᵉ .var k
  expBase := fun _ => .zero
  expCoeff := fun _ => .zero
  polyExp := fun _ => 0

/-- The product monomial evaluates to the product of its two variables. -/
@[simp]
theorem SimpleMonomial.mulVars_eval {m : ℕ} (j k : Fin m) (ρ : Fin m → ℕ) :
    (SimpleMonomial.mulVars j k).eval ρ = ρ j * ρ k := by
  simp only [SimpleMonomial.eval, SimpleMonomial.mulVars, emul_eval, eraInterp, fcons, Tm.eval,
    Nat.zero_mul, Nat.pow_zero, Finset.prod_const_one, Nat.mul_one]

/-- The simple monomial over `Fin m` whose value at `ρ` is `2 ^ ρ j`: a single
exponential factor with constant base `2` and exponential coefficient `1` at slot
`j` (Expression (6) of arXiv:2407.12928), all other data trivial. -/
def SimpleMonomial.pow2Var {m : ℕ} (j : Fin m) : SimpleMonomial m where
  coeff := Era.one
  expBase := fun i => if i = j then .succ Era.one else .zero
  expCoeff := fun i => if i = j then Era.one else .zero
  polyExp := fun _ => 0

/-- The base-`2` power monomial evaluates to `2 ^ ρ j`. -/
@[simp]
theorem SimpleMonomial.pow2Var_eval {m : ℕ} (j : Fin m) (ρ : Fin m → ℕ) :
    (SimpleMonomial.pow2Var j).eval ρ = 2 ^ ρ j := by
  rw [SimpleMonomial.eval]
  have hprod : (∏ i, Tm.eval eraInterp ((SimpleMonomial.pow2Var j).expBase i) ρ
      ^ (Tm.eval eraInterp ((SimpleMonomial.pow2Var j).expCoeff i) ρ * ρ i)) = 2 ^ ρ j := by
    rw [Finset.prod_eq_single j]
    · simp only [SimpleMonomial.pow2Var, if_true, Era.one, Tm.eval, Nat.zero_add, Nat.one_mul]
    · intro i _ hi
      simp only [SimpleMonomial.pow2Var, if_neg hi, Tm.eval, Nat.zero_mul, Nat.pow_zero]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  rw [hprod]
  simp only [SimpleMonomial.pow2Var, Era.one, Tm.eval, Nat.pow_zero, Finset.prod_const_one,
    Nat.mul_one, Nat.zero_add, Nat.one_mul]

/-- The compound context, precomposed with `spliceEmb outSlot witEmb`, recovers
the sub-encoding's context: the `n` inputs are unchanged, the sub-output reads
the compound witness slot `outSlot`, and the sub-witnesses read their slots
through `witEmb`. This is the generic re-indexing identity behind every splice
combinator. -/
theorem append_snoc_comp_spliceEmb {n wSub wComp : ℕ} (ρ : Fin n → ℕ) (y : ℕ)
    (w : Fin wComp → ℕ) (outSlot : Fin wComp) (witEmb : Fin wSub → Fin wComp) :
    (Fin.append (Fin.snoc ρ y) w) ∘ spliceEmb outSlot witEmb =
      Fin.append (Fin.snoc ρ (w outSlot)) (fun k => w (witEmb k)) := by
  refine funext (fun a => ?_)
  simp only [Function.comp_apply, spliceEmb]
  refine Fin.addCases ?_ ?_ a
  · intro io
    refine Fin.lastCases ?_ ?_ io
    · simp only [Fin.addCases_left, Fin.lastCases_last, Fin.append_right, Fin.append_left,
        Fin.snoc_last]
    · intro j
      simp only [Fin.addCases_left, Fin.lastCases_castSucc, Fin.append_left, Fin.snoc_castSucc]
  · intro k
    simp only [Fin.addCases_right, Fin.append_right]

/-- `e` correctly encodes the unary-output function `g` on `n` inputs: the
system vanishes only at the right output, has a unique witness there, its
witnesses respect the input-only bounds, and its value is dominated by the
input-only majorant. The four conjuncts are soundness (a vanishing assignment
forces `y = g ρ`), completeness with uniqueness (at the correct output there is
exactly one witness tuple), boundedness (every vanishing witness lies below its
input-only bound), and value majorisation (`g ρ` lies below `valBound`). -/
def DiophEnc.Encodes {n : ℕ} (e : DiophEnc n) (g : (Fin n → ℕ) → ℕ) : Prop :=
  (∀ ρ y w, SosSystem.eval e.sys (e.ctx ρ y w) = 0 → y = g ρ) ∧
  (∀ ρ, ∃! w, SosSystem.eval e.sys (e.ctx ρ (g ρ) w) = 0) ∧
  (∀ ρ y w, SosSystem.eval e.sys (e.ctx ρ y w) = 0 →
    ∀ i, w i < Tm.eval eraInterp (e.bound i) ρ) ∧
  (∀ ρ, g ρ < Tm.eval eraInterp e.valBound ρ)

/-- The encoding of the `i`-th projection `fun ρ => ρ i`: no witnesses, and a
single squared-distance atom equating the input slot `i` to the output slot. -/
def diophVar {n : ℕ} (i : Fin n) : DiophEnc n where
  witArity := 0
  sys := [.sqDist [SimpleMonomial.var (Fin.castAdd 0 i.castSucc)]
    [SimpleMonomial.var (Fin.castAdd 0 (Fin.last n))]]
  bound := Fin.elim0
  valBound := Tm.succ (Tm.var i)

/-- `diophVar i` encodes the `i`-th projection. -/
theorem diophVar_encodes {n : ℕ} (i : Fin n) :
    (diophVar i).Encodes (fun ρ => ρ i) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ρ y w hzero
    rw [DiophEnc.ctx] at hzero
    simp only [diophVar, SosSystem.eval, SosTerm.sqDist_eval_eq_zero_iff, SimpleSum.eval,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero,
      SimpleMonomial.var_eval, Fin.append_left, Fin.snoc_castSucc, Fin.snoc_last] at hzero
    exact hzero.symm
  · intro ρ
    refine ⟨Fin.elim0, ?_, ?_⟩
    · simp only [diophVar, DiophEnc.ctx, SosSystem.eval, SosTerm.sqDist_eval_eq_zero_iff,
        SimpleSum.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero,
        SimpleMonomial.var_eval, Fin.append_left, Fin.snoc_castSucc, Fin.snoc_last]
    · intro w _
      exact funext (fun j => j.elim0)
  · intro ρ y w _ j
    exact j.elim0
  · intro ρ
    simp only [diophVar, Tm.eval]
    omega

/-- The encoding of the constant-zero function `fun _ => 0`: no witnesses, and
a single squared-distance atom equating the empty sum to the output slot, which
vanishes exactly when the output is `0`. -/
def diophZero {n : ℕ} : DiophEnc n where
  witArity := 0
  sys := [.sqDist [] [SimpleMonomial.var (Fin.castAdd 0 (Fin.last n))]]
  bound := Fin.elim0
  valBound := one

/-- `diophZero` encodes the constant-zero function. -/
theorem diophZero_encodes {n : ℕ} : (diophZero (n := n)).Encodes (fun _ => 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ρ y w hzero
    simp only [diophZero, DiophEnc.ctx, SosSystem.eval, SosTerm.sqDist_eval_eq_zero_iff,
      SimpleSum.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero,
      SimpleMonomial.var_eval, Fin.append_left, Fin.snoc_last] at hzero
    exact hzero.symm
  · intro ρ
    refine ⟨Fin.elim0, ?_, ?_⟩
    · simp only [diophZero, DiophEnc.ctx, SosSystem.eval, SosTerm.sqDist_eval_eq_zero_iff,
        SimpleSum.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero,
        SimpleMonomial.var_eval, Fin.append_left, Fin.snoc_last]
    · intro w _
      exact funext (fun j => j.elim0)
  · intro ρ y w _ j
    exact j.elim0
  · intro ρ
    simp only [diophZero, one, Tm.eval]
    omega

/-- The witness embedding of `diophSucc`: send a sub-witness `k` to the same
slot `k.castSucc` in the compound witness block, leaving the last slot for the
new witness `y₁`. -/
def succWitEmb {w : ℕ} : Fin w → Fin (w + 1) := Fin.castSucc

/-- `succWitEmb` is injective. -/
theorem succWitEmb_injective {w : ℕ} : Function.Injective (succWitEmb (w := w)) :=
  Fin.castSucc_injective w

/-- No sub-witness slot collides with the new `y₁` slot `Fin.last w`. -/
theorem succWitEmb_ne_last {w : ℕ} (k : Fin w) : succWitEmb k ≠ Fin.last w :=
  Fin.castSucc_lt_last k |>.ne

/-- The encoding of `fun ρ => g ρ + 1` from an encoding `sub` of `g`. A new
witness `y₁` holds the sub-output: `sub.sys` is spliced so its output becomes
the `y₁` slot (the last witness) and its witnesses occupy the first
`sub.witArity` slots; an added squared-distance atom forces `y₁ + 1 = y`. The
new witness `y₁` is bounded by `sub.valBound`; each sub-witness keeps its
input-only sub-bound `sub.bound k`, which transfers unchanged since the
sub-encoding shares the same inputs. The value majorant is `sub.valBound + 1`. -/
def diophSucc {n : ℕ} (sub : DiophEnc n) : DiophEnc n where
  witArity := sub.witArity + 1
  sys :=
    sub.sys.spliceWeaken (Fin.last sub.witArity) succWitEmb ++
      [.sqDist
        [SimpleMonomial.var (Fin.natAdd (n + 1) (Fin.last sub.witArity)),
          SimpleMonomial.one]
        [SimpleMonomial.var (Fin.castAdd (sub.witArity + 1) (Fin.last n))]]
  bound := Fin.snoc sub.bound sub.valBound
  valBound := Tm.succ sub.valBound

/-- The compound context, precomposed with `diophSucc`'s splice embedding,
recovers the sub-encoding's context: the inputs are unchanged, the sub-output
reads the new `y₁` witness, and the sub-witnesses read the first witness block. -/
theorem ctx_comp_succSpliceEmb {n : ℕ} (sub : DiophEnc n) (ρ : Fin n → ℕ) (y : ℕ)
    (w : Fin (sub.witArity + 1) → ℕ) :
    (DiophEnc.ctx (diophSucc sub) ρ y w) ∘ spliceEmb (Fin.last sub.witArity) succWitEmb =
      sub.ctx ρ (w (Fin.last sub.witArity)) (fun k => w k.castSucc) := by
  refine funext (fun a => ?_)
  simp only [Function.comp_apply, DiophEnc.ctx, spliceEmb]
  refine Fin.addCases ?_ ?_ a
  · intro io
    refine Fin.lastCases ?_ ?_ io
    · simp only [Fin.addCases_left, Fin.lastCases_last, Fin.append_right, Fin.append_left,
        Fin.snoc_last]
    · intro j
      simp only [Fin.addCases_left, Fin.lastCases_castSucc, Fin.append_left, Fin.snoc_castSucc]
  · intro k
    simp only [Fin.addCases_right, Fin.append_right, succWitEmb]

/-- The `diophSucc sub` system vanishes at `ctx ρ y w` exactly when the
sub-system vanishes at its recovered context and the new witness satisfies
`y₁ + 1 = y`. -/
theorem diophSucc_eval_eq_zero_iff {n : ℕ} (sub : DiophEnc n) (ρ : Fin n → ℕ) (y : ℕ)
    (w : Fin (sub.witArity + 1) → ℕ) :
    SosSystem.eval (diophSucc sub).sys ((diophSucc sub).ctx ρ y w) = 0 ↔
      SosSystem.eval sub.sys (sub.ctx ρ (w (Fin.last sub.witArity))
          (fun k => w k.castSucc)) = 0 ∧
        w (Fin.last sub.witArity) + 1 = y := by
  have hsplice :
      SosSystem.eval ((diophSucc sub).sys) ((diophSucc sub).ctx ρ y w) =
        SosSystem.eval sub.sys (sub.ctx ρ (w (Fin.last sub.witArity))
            (fun k => w k.castSucc)) +
          SosTerm.eval (.sqDist
            [SimpleMonomial.var (Fin.natAdd (n + 1) (Fin.last sub.witArity)),
              SimpleMonomial.one]
            [SimpleMonomial.var (Fin.castAdd (sub.witArity + 1) (Fin.last n))])
            ((diophSucc sub).ctx ρ y w) := by
    change SosSystem.eval
        (sub.sys.spliceWeaken (Fin.last sub.witArity) succWitEmb ++
          [SosTerm.sqDist
            [SimpleMonomial.var (Fin.natAdd (n + 1) (Fin.last sub.witArity)),
              SimpleMonomial.one]
            [SimpleMonomial.var (Fin.castAdd (sub.witArity + 1) (Fin.last n))]])
        ((diophSucc sub).ctx ρ y w) = _
    rw [SosSystem.eval_append, SosSystem.eval, SosSystem.eval,
      SosSystem.eval_spliceWeaken sub.sys (Fin.last sub.witArity) succWitEmb
        succWitEmb_injective succWitEmb_ne_last]
    refine congrArg₂ (· + ·) ?_ (Nat.add_zero _)
    exact congrArg (SosSystem.eval sub.sys) (ctx_comp_succSpliceEmb sub ρ y w)
  rw [hsplice, Nat.add_eq_zero_iff, SosTerm.sqDist_eval_eq_zero_iff]
  simp only [SimpleSum.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Nat.add_zero, SimpleMonomial.var_eval, SimpleMonomial.one_eval, DiophEnc.ctx]
  erw [Fin.append_right, Fin.append_left, Fin.snoc_last]

/-- The `diophSucc` bound at the new `y₁` slot is the sub-encoding's value
majorant. -/
theorem diophSucc_bound_last {n : ℕ} (sub : DiophEnc n) :
    (diophSucc sub).bound (Fin.last sub.witArity) = sub.valBound := by
  change (Fin.snoc sub.bound sub.valBound :
      Fin (sub.witArity + 1) → ETm n) (Fin.last sub.witArity) = sub.valBound
  rw [Fin.snoc_last]

/-- The `diophSucc` bound at a sub-witness slot is the sub-encoding's bound. -/
theorem diophSucc_bound_castSucc {n : ℕ} (sub : DiophEnc n) (k : Fin sub.witArity) :
    (diophSucc sub).bound (Fin.castSucc k) = sub.bound k := by
  change (Fin.snoc sub.bound sub.valBound :
      Fin (sub.witArity + 1) → ETm n) (Fin.castSucc k) = sub.bound k
  rw [Fin.snoc_castSucc]

/-- `diophSucc sub` encodes `fun ρ => g ρ + 1` whenever `sub` encodes `g`. -/
theorem diophSucc_encodes {n : ℕ} {sub : DiophEnc n} {g : (Fin n → ℕ) → ℕ}
    (h : sub.Encodes g) : (diophSucc sub).Encodes (fun ρ => g ρ + 1) := by
  obtain ⟨hsound, huniq, hbound, hval⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ρ y w hzero
    rw [diophSucc_eval_eq_zero_iff] at hzero
    obtain ⟨hsub, hy⟩ := hzero
    rw [hsound ρ (w (Fin.last sub.witArity)) (fun k => w k.castSucc) hsub] at hy
    exact hy.symm
  · intro ρ
    obtain ⟨wsub, hwsub, hwsubuniq⟩ := huniq ρ
    refine ⟨Fin.snoc wsub (g ρ), ?_, ?_⟩
    · change (diophSucc sub).sys.eval ((diophSucc sub).ctx ρ (g ρ + 1) (Fin.snoc wsub (g ρ))) = 0
      rw [diophSucc_eval_eq_zero_iff, Fin.snoc_last]
      refine ⟨?_, rfl⟩
      simp only [Fin.snoc_castSucc]
      exact hwsub
    · intro w' hw'
      have hw'' : (diophSucc sub).sys.eval ((diophSucc sub).ctx ρ (g ρ + 1) w') = 0 := hw'
      rw [diophSucc_eval_eq_zero_iff] at hw''
      obtain ⟨hsub', hlast'⟩ := hw''
      have hlast : w' (Fin.last sub.witArity) = g ρ := by omega
      rw [hlast] at hsub'
      have hinit : (fun k => w' k.castSucc) = wsub := hwsubuniq (fun k => w' k.castSucc) hsub'
      refine funext (fun j => ?_)
      refine Fin.lastCases ?_ ?_ j
      · rw [Fin.snoc_last, hlast]
      · intro k
        rw [Fin.snoc_castSucc]
        exact congrFun hinit k
  · intro ρ y w hzero i
    rw [diophSucc_eval_eq_zero_iff] at hzero
    obtain ⟨hsub, hy⟩ := hzero
    have hg : w (Fin.last sub.witArity) = g ρ :=
      hsound ρ (w (Fin.last sub.witArity)) (fun k => w k.castSucc) hsub
    refine Fin.lastCases ?_ ?_ i
    · rw [diophSucc_bound_last, hg]
      exact hval ρ
    · intro k
      rw [diophSucc_bound_castSucc]
      exact hbound ρ (g ρ) (fun k => w k.castSucc) (by rw [← hg]; exact hsub) k
  · intro ρ
    simp only [diophSucc, Tm.eval]
    exact Nat.succ_lt_succ (hval ρ)

/-- The first output slot `y₁` of a binary combine over witness arities `w1`,
`w2`: the slot at index `w1` in the compound block `Fin (w1 + 1 + w2 + 1)`,
holding the first sub-encoding's output. -/
def binOutSlot1 {w1 w2 : ℕ} : Fin (w1 + 1 + w2 + 1) :=
  Fin.castSucc (Fin.castAdd w2 (Fin.last w1))

/-- The second output slot `y₂` of a binary combine: the last slot at index
`w1 + 1 + w2` in the compound block, holding the second sub-encoding's output. -/
def binOutSlot2 {w1 w2 : ℕ} : Fin (w1 + 1 + w2 + 1) :=
  Fin.last (w1 + 1 + w2)

/-- The first sub-encoding's witness embedding for a binary combine: a
sub-witness `k` of `sub1` lands at index `k` (slots `0 .. w1 - 1`), below the
`y₁` slot. -/
def binWitEmb1 {w1 w2 : ℕ} (k : Fin w1) : Fin (w1 + 1 + w2 + 1) :=
  Fin.castSucc (Fin.castAdd w2 k.castSucc)

/-- The second sub-encoding's witness embedding for a binary combine: a
sub-witness `k` of `sub2` lands at index `w1 + 1 + k` (slots `w1 + 1 .. w1 + w2`),
between the `y₁` and `y₂` slots. -/
def binWitEmb2 {w1 w2 : ℕ} (k : Fin w2) : Fin (w1 + 1 + w2 + 1) :=
  Fin.castSucc (Fin.natAdd (w1 + 1) k)

/-- `binWitEmb1` is injective: it composes the injective casts
`Fin.castSucc`, `Fin.castAdd`, `Fin.castSucc`. -/
theorem binWitEmb1_injective {w1 w2 : ℕ} :
    Function.Injective (binWitEmb1 (w1 := w1) (w2 := w2)) := by
  intro a b hab
  rw [binWitEmb1, binWitEmb1, Fin.ext_iff] at hab
  simp only [Fin.val_castSucc, Fin.val_castAdd] at hab
  exact Fin.ext hab

/-- No `binWitEmb1` slot collides with the `y₁` slot. -/
theorem binWitEmb1_ne_outSlot1 {w1 w2 : ℕ} (k : Fin w1) :
    binWitEmb1 (w2 := w2) k ≠ binOutSlot1 := by
  rw [binWitEmb1, binOutSlot1, Ne, Fin.ext_iff]
  simp only [Fin.val_castSucc, Fin.val_castAdd, Fin.val_last]
  exact k.isLt.ne

/-- `binWitEmb2` is injective. -/
theorem binWitEmb2_injective {w1 w2 : ℕ} :
    Function.Injective (binWitEmb2 (w1 := w1) (w2 := w2)) := by
  intro a b hab
  rw [binWitEmb2, binWitEmb2, Fin.ext_iff] at hab
  simp only [Fin.val_castSucc, Fin.val_natAdd] at hab
  exact Fin.ext (Nat.add_left_cancel hab)

/-- No `binWitEmb2` slot collides with the `y₂` slot. -/
theorem binWitEmb2_ne_outSlot2 {w1 w2 : ℕ} (k : Fin w2) :
    binWitEmb2 (w1 := w1) k ≠ binOutSlot2 := by
  rw [binWitEmb2, binOutSlot2, Ne, Fin.ext_iff]
  simp only [Fin.val_castSucc, Fin.val_natAdd, Fin.val_last]
  omega

/-- Case analysis on a compound witness slot of a binary combine: every
`i : Fin (w1 + 1 + w2 + 1)` is one of the four slot kinds — a `sub1`-witness
`binWitEmb1 k`, the `y₁` slot `binOutSlot1`, a `sub2`-witness `binWitEmb2 k`, or
the `y₂` slot `binOutSlot2`. -/
theorem binLayoutCases {w1 w2 : ℕ} {motive : Fin (w1 + 1 + w2 + 1) → Prop}
    (hwit1 : ∀ k, motive (binWitEmb1 k)) (hout1 : motive binOutSlot1)
    (hwit2 : ∀ k, motive (binWitEmb2 k)) (hout2 : motive binOutSlot2)
    (i : Fin (w1 + 1 + w2 + 1)) : motive i := by
  refine Fin.lastCases hout2 (fun j => ?_) i
  refine Fin.addCases (fun a => ?_) (fun b => hwit2 b) j
  exact Fin.lastCases hout1 (fun k => hwit1 k) a

/-- Assemble the four data of a binary combine — the `sub1`-witness data `f1`,
the `y₁` datum `a1`, the `sub2`-witness data `f2`, and the `y₂` datum `a2` — into
a single map over the compound layout `Fin (w1 + 1 + w2 + 1)`, by nesting
`Fin.snoc`/`Fin.append`. Used both for the per-witness bound map (`α = ETm n`)
and for the assembled witness tuple (`α = ℕ`). -/
def binAssemble {α : Type} {w1 w2 : ℕ} (f1 : Fin w1 → α) (a1 : α) (f2 : Fin w2 → α)
    (a2 : α) : Fin (w1 + 1 + w2 + 1) → α :=
  Fin.snoc (Fin.append (Fin.snoc f1 a1) f2) a2

/-- `binAssemble` at a `sub1`-witness slot reads `f1`. -/
@[simp]
theorem binAssemble_witEmb1 {α : Type} {w1 w2 : ℕ} (f1 : Fin w1 → α) (a1 : α)
    (f2 : Fin w2 → α) (a2 : α) (k : Fin w1) :
    binAssemble f1 a1 f2 a2 (binWitEmb1 k) = f1 k := by
  rw [binAssemble, binWitEmb1, Fin.snoc_castSucc, Fin.append_left, Fin.snoc_castSucc]

/-- `binAssemble` at the `y₁` slot reads `a1`. -/
@[simp]
theorem binAssemble_outSlot1 {α : Type} {w1 w2 : ℕ} (f1 : Fin w1 → α) (a1 : α)
    (f2 : Fin w2 → α) (a2 : α) :
    binAssemble f1 a1 f2 a2 binOutSlot1 = a1 := by
  rw [binAssemble, binOutSlot1, Fin.snoc_castSucc, Fin.append_left, Fin.snoc_last]

/-- `binAssemble` at a `sub2`-witness slot reads `f2`. -/
@[simp]
theorem binAssemble_witEmb2 {α : Type} {w1 w2 : ℕ} (f1 : Fin w1 → α) (a1 : α)
    (f2 : Fin w2 → α) (a2 : α) (k : Fin w2) :
    binAssemble f1 a1 f2 a2 (binWitEmb2 k) = f2 k := by
  rw [binAssemble, binWitEmb2, Fin.snoc_castSucc, Fin.append_right]

/-- `binAssemble` at the `y₂` slot reads `a2`. -/
@[simp]
theorem binAssemble_outSlot2 {α : Type} {w1 w2 : ℕ} (f1 : Fin w1 → α) (a1 : α)
    (f2 : Fin w2 → α) (a2 : α) :
    binAssemble f1 a1 f2 a2 binOutSlot2 = a2 := by
  rw [binAssemble, binOutSlot2, Fin.snoc_last]

/-- The per-witness bound map of a binary combine over `sub1`, `sub2`: each
sub-witness keeps its own input-only bound, the `y₁` slot is bounded by
`sub1.valBound`, and the `y₂` slot by `sub2.valBound`. -/
def binBound {n : ℕ} (sub1 sub2 : DiophEnc n) :
    Fin (sub1.witArity + 1 + sub2.witArity + 1) → ETm n :=
  binAssemble sub1.bound sub1.valBound sub2.bound sub2.valBound

/-- The spliced system of a binary combine over `sub1`, `sub2`: `sub1.sys`
spliced with its output at the `y₁` slot and its witnesses below it, followed by
`sub2.sys` spliced with its output at the `y₂` slot and its witnesses between the
two output slots. The combinators append a single connecting atom. -/
def binSplicedSys {n : ℕ} (sub1 sub2 : DiophEnc n) :
    SosSystem (n + 1 + (sub1.witArity + 1 + sub2.witArity + 1)) :=
  sub1.sys.spliceWeaken binOutSlot1 binWitEmb1 ++
    sub2.sys.spliceWeaken binOutSlot2 binWitEmb2

/-- The binary spliced system vanishes additively into the two sub-systems
evaluated at their recovered contexts: the first reads its output from the `y₁`
slot and its witnesses from the low block, the second from the `y₂` slot and the
middle block. -/
theorem binSplicedSys_eval {n : ℕ} (sub1 sub2 : DiophEnc n) (ρ : Fin n → ℕ) (y : ℕ)
    (w : Fin (sub1.witArity + 1 + sub2.witArity + 1) → ℕ) :
    SosSystem.eval (binSplicedSys sub1 sub2) (Fin.append (Fin.snoc ρ y) w) =
      SosSystem.eval sub1.sys
          (sub1.ctx ρ (w binOutSlot1) (fun k => w (binWitEmb1 k))) +
        SosSystem.eval sub2.sys
          (sub2.ctx ρ (w binOutSlot2) (fun k => w (binWitEmb2 k))) := by
  rw [binSplicedSys, SosSystem.eval_append,
    SosSystem.eval_spliceWeaken sub1.sys binOutSlot1 binWitEmb1
      binWitEmb1_injective binWitEmb1_ne_outSlot1,
    SosSystem.eval_spliceWeaken sub2.sys binOutSlot2 binWitEmb2
      binWitEmb2_injective binWitEmb2_ne_outSlot2]
  rw [DiophEnc.ctx, DiophEnc.ctx, append_snoc_comp_spliceEmb, append_snoc_comp_spliceEmb]

/-- The encoding of `fun ρ => g1 ρ + g2 ρ` from encodings `sub1` of `g1` and
`sub2` of `g2`. Two new witnesses `y₁`, `y₂` hold the two sub-outputs: `sub1.sys`
and `sub2.sys` are spliced so their outputs become the `y₁` and `y₂` slots and
their witnesses occupy disjoint blocks; an added squared-distance atom forces
`y₁ + y₂ = y`. Each sub-witness keeps its input-only sub-bound; `y₁` is bounded
by `sub1.valBound` and `y₂` by `sub2.valBound`. The value majorant is
`sub1.valBound + sub2.valBound`. -/
def diophAdd {n : ℕ} (sub1 sub2 : DiophEnc n) : DiophEnc n where
  witArity := sub1.witArity + 1 + sub2.witArity + 1
  sys :=
    binSplicedSys sub1 sub2 ++
      [.sqDist
        [SimpleMonomial.var (Fin.natAdd (n + 1) binOutSlot1),
          SimpleMonomial.var (Fin.natAdd (n + 1) binOutSlot2)]
        [SimpleMonomial.var (Fin.castAdd (sub1.witArity + 1 + sub2.witArity + 1) (Fin.last n))]]
  bound := binBound sub1 sub2
  valBound := sub1.valBound +ᵉ sub2.valBound

/-- The `diophAdd sub1 sub2` system vanishes at `ctx ρ y w` exactly when both
sub-systems vanish at their recovered contexts and the two output witnesses
satisfy `y₁ + y₂ = y`. -/
theorem diophAdd_eval_eq_zero_iff {n : ℕ} (sub1 sub2 : DiophEnc n) (ρ : Fin n → ℕ) (y : ℕ)
    (w : Fin (sub1.witArity + 1 + sub2.witArity + 1) → ℕ) :
    SosSystem.eval (diophAdd sub1 sub2).sys ((diophAdd sub1 sub2).ctx ρ y w) = 0 ↔
      SosSystem.eval sub1.sys (sub1.ctx ρ (w binOutSlot1) (fun k => w (binWitEmb1 k))) = 0 ∧
        SosSystem.eval sub2.sys (sub2.ctx ρ (w binOutSlot2) (fun k => w (binWitEmb2 k))) = 0 ∧
          w binOutSlot1 + w binOutSlot2 = y := by
  change SosSystem.eval
      (binSplicedSys sub1 sub2 ++
        [SosTerm.sqDist
          [SimpleMonomial.var (Fin.natAdd (n + 1) binOutSlot1),
            SimpleMonomial.var (Fin.natAdd (n + 1) binOutSlot2)]
          [SimpleMonomial.var
            (Fin.castAdd (sub1.witArity + 1 + sub2.witArity + 1) (Fin.last n))]])
      (Fin.append (Fin.snoc ρ y) w) = 0 ↔ _
  rw [SosSystem.eval_append, binSplicedSys_eval]
  simp only [SosSystem.eval, SosTerm.eval, SimpleSum.eval, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Nat.add_zero, SimpleMonomial.var_eval, Fin.append_right,
    Fin.append_left, Fin.snoc_last]
  rw [Nat.add_eq_zero_iff, Nat.add_eq_zero_iff, Nat.add_eq_zero_iff, Nat.pow_eq_zero,
    Nat.pow_eq_zero, Nat.sub_eq_zero_iff_le, Nat.sub_eq_zero_iff_le]
  omega

/-- The `diophAdd` bound map is `binBound`. -/
@[simp]
theorem diophAdd_bound {n : ℕ} (sub1 sub2 : DiophEnc n) :
    (diophAdd sub1 sub2).bound = binBound sub1 sub2 := rfl

/-- `diophAdd sub1 sub2` encodes `fun ρ => g1 ρ + g2 ρ` whenever `sub1` encodes
`g1` and `sub2` encodes `g2`. -/
theorem diophAdd_encodes {n : ℕ} {sub1 sub2 : DiophEnc n} {g1 g2 : (Fin n → ℕ) → ℕ}
    (h1 : sub1.Encodes g1) (h2 : sub2.Encodes g2) :
    (diophAdd sub1 sub2).Encodes (fun ρ => g1 ρ + g2 ρ) := by
  obtain ⟨hsound1, huniq1, hbound1, hval1⟩ := h1
  obtain ⟨hsound2, huniq2, hbound2, hval2⟩ := h2
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ρ y w hzero
    rw [diophAdd_eval_eq_zero_iff] at hzero
    obtain ⟨hz1, hz2, hy⟩ := hzero
    rw [hsound1 ρ (w binOutSlot1) (fun k => w (binWitEmb1 k)) hz1,
      hsound2 ρ (w binOutSlot2) (fun k => w (binWitEmb2 k)) hz2] at hy
    exact hy.symm
  · intro ρ
    obtain ⟨wsub1, hwsub1, hwsubuniq1⟩ := huniq1 ρ
    obtain ⟨wsub2, hwsub2, hwsubuniq2⟩ := huniq2 ρ
    refine ⟨binAssemble wsub1 (g1 ρ) wsub2 (g2 ρ), ?_, ?_⟩
    · change (diophAdd sub1 sub2).sys.eval
        ((diophAdd sub1 sub2).ctx ρ (g1 ρ + g2 ρ) (binAssemble wsub1 (g1 ρ) wsub2 (g2 ρ))) = 0
      rw [diophAdd_eval_eq_zero_iff]
      simp only [binAssemble_witEmb1, binAssemble_outSlot1, binAssemble_witEmb2,
        binAssemble_outSlot2]
      exact ⟨hwsub1, hwsub2, trivial⟩
    · intro w' hw'
      have hw'' : (diophAdd sub1 sub2).sys.eval
        ((diophAdd sub1 sub2).ctx ρ (g1 ρ + g2 ρ) w') = 0 := hw'
      rw [diophAdd_eval_eq_zero_iff] at hw''
      obtain ⟨hz1', hz2', _⟩ := hw''
      have hg1 : w' binOutSlot1 = g1 ρ :=
        hsound1 ρ (w' binOutSlot1) (fun k => w' (binWitEmb1 k)) hz1'
      have hg2 : w' binOutSlot2 = g2 ρ :=
        hsound2 ρ (w' binOutSlot2) (fun k => w' (binWitEmb2 k)) hz2'
      have he1 : (fun k => w' (binWitEmb1 k)) = wsub1 :=
        hwsubuniq1 (fun k => w' (binWitEmb1 k)) (by rw [← hg1]; exact hz1')
      have he2 : (fun k => w' (binWitEmb2 k)) = wsub2 :=
        hwsubuniq2 (fun k => w' (binWitEmb2 k)) (by rw [← hg2]; exact hz2')
      refine funext (binLayoutCases (fun k => ?_) ?_ (fun k => ?_) ?_)
      · rw [binAssemble_witEmb1]; exact congrFun he1 k
      · rw [binAssemble_outSlot1]; exact hg1
      · rw [binAssemble_witEmb2]; exact congrFun he2 k
      · rw [binAssemble_outSlot2]; exact hg2
  · intro ρ y w hzero i
    rw [diophAdd_eval_eq_zero_iff] at hzero
    obtain ⟨hz1, hz2, hy⟩ := hzero
    have hg1 : w binOutSlot1 = g1 ρ :=
      hsound1 ρ (w binOutSlot1) (fun k => w (binWitEmb1 k)) hz1
    have hg2 : w binOutSlot2 = g2 ρ :=
      hsound2 ρ (w binOutSlot2) (fun k => w (binWitEmb2 k)) hz2
    rw [diophAdd_bound]
    induction i using binLayoutCases with
    | hwit1 k =>
      rw [binBound, binAssemble_witEmb1]
      exact hbound1 ρ (g1 ρ) (fun k => w (binWitEmb1 k)) (by rw [← hg1]; exact hz1) k
    | hout1 =>
      rw [binBound, binAssemble_outSlot1, hg1]
      exact hval1 ρ
    | hwit2 k =>
      rw [binBound, binAssemble_witEmb2]
      exact hbound2 ρ (g2 ρ) (fun k => w (binWitEmb2 k)) (by rw [← hg2]; exact hz2) k
    | hout2 =>
      rw [binBound, binAssemble_outSlot2, hg2]
      exact hval2 ρ
  · intro ρ
    simp only [diophAdd, eadd_eval, eraInterp, fcons]
    exact Nat.add_lt_add (hval1 ρ) (hval2 ρ)

/-- The encoding of `fun ρ => g1 ρ * g2 ρ` from encodings `sub1` of `g1` and
`sub2` of `g2`. The binary splice is as for `diophAdd`: two new witnesses `y₁`,
`y₂` hold the two sub-outputs, and an added squared-distance atom forces
`y₁ * y₂ = y`. Each sub-witness keeps its input-only sub-bound; `y₁` is bounded
by `sub1.valBound` and `y₂` by `sub2.valBound`. The value majorant is
`sub1.valBound * sub2.valBound`. -/
def diophMul {n : ℕ} (sub1 sub2 : DiophEnc n) : DiophEnc n where
  witArity := sub1.witArity + 1 + sub2.witArity + 1
  sys :=
    binSplicedSys sub1 sub2 ++
      [.sqDist
        [SimpleMonomial.mulVars (Fin.natAdd (n + 1) binOutSlot1)
          (Fin.natAdd (n + 1) binOutSlot2)]
        [SimpleMonomial.var (Fin.castAdd (sub1.witArity + 1 + sub2.witArity + 1) (Fin.last n))]]
  bound := binBound sub1 sub2
  valBound := sub1.valBound *ᵉ sub2.valBound

/-- The `diophMul sub1 sub2` system vanishes at `ctx ρ y w` exactly when both
sub-systems vanish at their recovered contexts and the two output witnesses
satisfy `y₁ * y₂ = y`. -/
theorem diophMul_eval_eq_zero_iff {n : ℕ} (sub1 sub2 : DiophEnc n) (ρ : Fin n → ℕ) (y : ℕ)
    (w : Fin (sub1.witArity + 1 + sub2.witArity + 1) → ℕ) :
    SosSystem.eval (diophMul sub1 sub2).sys ((diophMul sub1 sub2).ctx ρ y w) = 0 ↔
      SosSystem.eval sub1.sys (sub1.ctx ρ (w binOutSlot1) (fun k => w (binWitEmb1 k))) = 0 ∧
        SosSystem.eval sub2.sys (sub2.ctx ρ (w binOutSlot2) (fun k => w (binWitEmb2 k))) = 0 ∧
          w binOutSlot1 * w binOutSlot2 = y := by
  change SosSystem.eval
      (binSplicedSys sub1 sub2 ++
        [SosTerm.sqDist
          [SimpleMonomial.mulVars (Fin.natAdd (n + 1) binOutSlot1)
            (Fin.natAdd (n + 1) binOutSlot2)]
          [SimpleMonomial.var
            (Fin.castAdd (sub1.witArity + 1 + sub2.witArity + 1) (Fin.last n))]])
      (Fin.append (Fin.snoc ρ y) w) = 0 ↔ _
  rw [SosSystem.eval_append, binSplicedSys_eval]
  simp only [SosSystem.eval, SosTerm.eval, SimpleSum.eval, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Nat.add_zero, SimpleMonomial.mulVars_eval,
    SimpleMonomial.var_eval, Fin.append_right, Fin.append_left, Fin.snoc_last]
  rw [Nat.add_eq_zero_iff, Nat.add_eq_zero_iff, Nat.add_eq_zero_iff, Nat.pow_eq_zero,
    Nat.pow_eq_zero, Nat.sub_eq_zero_iff_le, Nat.sub_eq_zero_iff_le]
  omega

/-- The `diophMul` bound map is `binBound`. -/
@[simp]
theorem diophMul_bound {n : ℕ} (sub1 sub2 : DiophEnc n) :
    (diophMul sub1 sub2).bound = binBound sub1 sub2 := rfl

/-- `diophMul sub1 sub2` encodes `fun ρ => g1 ρ * g2 ρ` whenever `sub1` encodes
`g1` and `sub2` encodes `g2`. The value clause is strict monotonicity of `ℕ`
multiplication (`Nat.mul_lt_mul''`) applied to the two strict value bounds. -/
theorem diophMul_encodes {n : ℕ} {sub1 sub2 : DiophEnc n} {g1 g2 : (Fin n → ℕ) → ℕ}
    (h1 : sub1.Encodes g1) (h2 : sub2.Encodes g2) :
    (diophMul sub1 sub2).Encodes (fun ρ => g1 ρ * g2 ρ) := by
  obtain ⟨hsound1, huniq1, hbound1, hval1⟩ := h1
  obtain ⟨hsound2, huniq2, hbound2, hval2⟩ := h2
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ρ y w hzero
    rw [diophMul_eval_eq_zero_iff] at hzero
    obtain ⟨hz1, hz2, hy⟩ := hzero
    rw [hsound1 ρ (w binOutSlot1) (fun k => w (binWitEmb1 k)) hz1,
      hsound2 ρ (w binOutSlot2) (fun k => w (binWitEmb2 k)) hz2] at hy
    exact hy.symm
  · intro ρ
    obtain ⟨wsub1, hwsub1, hwsubuniq1⟩ := huniq1 ρ
    obtain ⟨wsub2, hwsub2, hwsubuniq2⟩ := huniq2 ρ
    refine ⟨binAssemble wsub1 (g1 ρ) wsub2 (g2 ρ), ?_, ?_⟩
    · change (diophMul sub1 sub2).sys.eval
        ((diophMul sub1 sub2).ctx ρ (g1 ρ * g2 ρ) (binAssemble wsub1 (g1 ρ) wsub2 (g2 ρ))) = 0
      rw [diophMul_eval_eq_zero_iff]
      simp only [binAssemble_witEmb1, binAssemble_outSlot1, binAssemble_witEmb2,
        binAssemble_outSlot2]
      exact ⟨hwsub1, hwsub2, trivial⟩
    · intro w' hw'
      have hw'' : (diophMul sub1 sub2).sys.eval
        ((diophMul sub1 sub2).ctx ρ (g1 ρ * g2 ρ) w') = 0 := hw'
      rw [diophMul_eval_eq_zero_iff] at hw''
      obtain ⟨hz1', hz2', _⟩ := hw''
      have hg1 : w' binOutSlot1 = g1 ρ :=
        hsound1 ρ (w' binOutSlot1) (fun k => w' (binWitEmb1 k)) hz1'
      have hg2 : w' binOutSlot2 = g2 ρ :=
        hsound2 ρ (w' binOutSlot2) (fun k => w' (binWitEmb2 k)) hz2'
      have he1 : (fun k => w' (binWitEmb1 k)) = wsub1 :=
        hwsubuniq1 (fun k => w' (binWitEmb1 k)) (by rw [← hg1]; exact hz1')
      have he2 : (fun k => w' (binWitEmb2 k)) = wsub2 :=
        hwsubuniq2 (fun k => w' (binWitEmb2 k)) (by rw [← hg2]; exact hz2')
      refine funext (binLayoutCases (fun k => ?_) ?_ (fun k => ?_) ?_)
      · rw [binAssemble_witEmb1]; exact congrFun he1 k
      · rw [binAssemble_outSlot1]; exact hg1
      · rw [binAssemble_witEmb2]; exact congrFun he2 k
      · rw [binAssemble_outSlot2]; exact hg2
  · intro ρ y w hzero i
    rw [diophMul_eval_eq_zero_iff] at hzero
    obtain ⟨hz1, hz2, hy⟩ := hzero
    have hg1 : w binOutSlot1 = g1 ρ :=
      hsound1 ρ (w binOutSlot1) (fun k => w (binWitEmb1 k)) hz1
    have hg2 : w binOutSlot2 = g2 ρ :=
      hsound2 ρ (w binOutSlot2) (fun k => w (binWitEmb2 k)) hz2
    rw [diophMul_bound]
    induction i using binLayoutCases with
    | hwit1 k =>
      rw [binBound, binAssemble_witEmb1]
      exact hbound1 ρ (g1 ρ) (fun k => w (binWitEmb1 k)) (by rw [← hg1]; exact hz1) k
    | hout1 =>
      rw [binBound, binAssemble_outSlot1, hg1]
      exact hval1 ρ
    | hwit2 k =>
      rw [binBound, binAssemble_witEmb2]
      exact hbound2 ρ (g2 ρ) (fun k => w (binWitEmb2 k)) (by rw [← hg2]; exact hz2) k
    | hout2 =>
      rw [binBound, binAssemble_outSlot2, hg2]
      exact hval2 ρ
  · intro ρ
    simp only [diophMul, emul_eval, eraInterp, fcons]
    exact Nat.mul_lt_mul'' (hval1 ρ) (hval2 ρ)

/-- The encoding of `fun ρ => 2 ^ g ρ` from an encoding `sub` of `g`. As in
`diophSucc`, a new witness `y₁` holds the sub-output: `sub.sys` is spliced so its
output becomes the `y₁` slot and its witnesses occupy the first `sub.witArity`
slots; an added squared-distance atom forces `2 ^ y₁ = y`. The new witness `y₁`
is bounded by `sub.valBound`; each sub-witness keeps its input-only sub-bound.
The value majorant is `2 ^ sub.valBound`. -/
def diophPow2 {n : ℕ} (sub : DiophEnc n) : DiophEnc n where
  witArity := sub.witArity + 1
  sys :=
    sub.sys.spliceWeaken (Fin.last sub.witArity) succWitEmb ++
      [.sqDist
        [SimpleMonomial.pow2Var (Fin.natAdd (n + 1) (Fin.last sub.witArity))]
        [SimpleMonomial.var (Fin.castAdd (sub.witArity + 1) (Fin.last n))]]
  bound := Fin.snoc sub.bound sub.valBound
  valBound := epow2 sub.valBound

/-- The `diophPow2 sub` system vanishes at `ctx ρ y w` exactly when the
sub-system vanishes at its recovered context and the new witness satisfies
`2 ^ y₁ = y`. -/
theorem diophPow2_eval_eq_zero_iff {n : ℕ} (sub : DiophEnc n) (ρ : Fin n → ℕ) (y : ℕ)
    (w : Fin (sub.witArity + 1) → ℕ) :
    SosSystem.eval (diophPow2 sub).sys ((diophPow2 sub).ctx ρ y w) = 0 ↔
      SosSystem.eval sub.sys (sub.ctx ρ (w (Fin.last sub.witArity))
          (fun k => w k.castSucc)) = 0 ∧
        2 ^ w (Fin.last sub.witArity) = y := by
  have hsplice :
      SosSystem.eval ((diophPow2 sub).sys) ((diophPow2 sub).ctx ρ y w) =
        SosSystem.eval sub.sys (sub.ctx ρ (w (Fin.last sub.witArity))
            (fun k => w k.castSucc)) +
          SosTerm.eval (.sqDist
            [SimpleMonomial.pow2Var (Fin.natAdd (n + 1) (Fin.last sub.witArity))]
            [SimpleMonomial.var (Fin.castAdd (sub.witArity + 1) (Fin.last n))])
            ((diophPow2 sub).ctx ρ y w) := by
    change SosSystem.eval
        (sub.sys.spliceWeaken (Fin.last sub.witArity) succWitEmb ++
          [SosTerm.sqDist
            [SimpleMonomial.pow2Var (Fin.natAdd (n + 1) (Fin.last sub.witArity))]
            [SimpleMonomial.var (Fin.castAdd (sub.witArity + 1) (Fin.last n))]])
        ((diophPow2 sub).ctx ρ y w) = _
    rw [SosSystem.eval_append, SosSystem.eval, SosSystem.eval,
      SosSystem.eval_spliceWeaken sub.sys (Fin.last sub.witArity) succWitEmb
        succWitEmb_injective succWitEmb_ne_last]
    refine congrArg₂ (· + ·) ?_ (Nat.add_zero _)
    exact congrArg (SosSystem.eval sub.sys) (ctx_comp_succSpliceEmb sub ρ y w)
  rw [hsplice, Nat.add_eq_zero_iff, SosTerm.sqDist_eval_eq_zero_iff]
  simp only [SimpleSum.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Nat.add_zero, SimpleMonomial.pow2Var_eval, SimpleMonomial.var_eval, DiophEnc.ctx]
  erw [Fin.append_right, Fin.append_left, Fin.snoc_last]

/-- The `diophPow2` bound at the new `y₁` slot is the sub-encoding's value
majorant. -/
theorem diophPow2_bound_last {n : ℕ} (sub : DiophEnc n) :
    (diophPow2 sub).bound (Fin.last sub.witArity) = sub.valBound := by
  change (Fin.snoc sub.bound sub.valBound :
      Fin (sub.witArity + 1) → ETm n) (Fin.last sub.witArity) = sub.valBound
  rw [Fin.snoc_last]

/-- The `diophPow2` bound at a sub-witness slot is the sub-encoding's bound. -/
theorem diophPow2_bound_castSucc {n : ℕ} (sub : DiophEnc n) (k : Fin sub.witArity) :
    (diophPow2 sub).bound (Fin.castSucc k) = sub.bound k := by
  change (Fin.snoc sub.bound sub.valBound :
      Fin (sub.witArity + 1) → ETm n) (Fin.castSucc k) = sub.bound k
  rw [Fin.snoc_castSucc]

/-- `diophPow2 sub` encodes `fun ρ => 2 ^ g ρ` whenever `sub` encodes `g`. The
value clause uses `2 ^ g ρ < 2 ^ sub.valBound` from `g ρ < sub.valBound` and the
strict monotonicity of `2 ^ ·`. -/
theorem diophPow2_encodes {n : ℕ} {sub : DiophEnc n} {g : (Fin n → ℕ) → ℕ}
    (h : sub.Encodes g) : (diophPow2 sub).Encodes (fun ρ => 2 ^ g ρ) := by
  obtain ⟨hsound, huniq, hbound, hval⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ρ y w hzero
    rw [diophPow2_eval_eq_zero_iff] at hzero
    obtain ⟨hsub, hy⟩ := hzero
    rw [hsound ρ (w (Fin.last sub.witArity)) (fun k => w k.castSucc) hsub] at hy
    exact hy.symm
  · intro ρ
    obtain ⟨wsub, hwsub, hwsubuniq⟩ := huniq ρ
    refine ⟨Fin.snoc wsub (g ρ), ?_, ?_⟩
    · change (diophPow2 sub).sys.eval
        ((diophPow2 sub).ctx ρ (2 ^ g ρ) (Fin.snoc wsub (g ρ))) = 0
      rw [diophPow2_eval_eq_zero_iff, Fin.snoc_last]
      refine ⟨?_, rfl⟩
      simp only [Fin.snoc_castSucc]
      exact hwsub
    · intro w' hw'
      have hw'' : (diophPow2 sub).sys.eval ((diophPow2 sub).ctx ρ (2 ^ g ρ) w') = 0 := hw'
      rw [diophPow2_eval_eq_zero_iff] at hw''
      obtain ⟨hsub', hlast'⟩ := hw''
      have hlast : w' (Fin.last sub.witArity) = g ρ :=
        Nat.pow_right_injective (Nat.le_refl 2) hlast'
      rw [hlast] at hsub'
      have hinit : (fun k => w' k.castSucc) = wsub := hwsubuniq (fun k => w' k.castSucc) hsub'
      refine funext (fun j => ?_)
      refine Fin.lastCases ?_ ?_ j
      · rw [Fin.snoc_last, hlast]
      · intro k
        rw [Fin.snoc_castSucc]
        exact congrFun hinit k
  · intro ρ y w hzero i
    rw [diophPow2_eval_eq_zero_iff] at hzero
    obtain ⟨hsub, hy⟩ := hzero
    have hg : w (Fin.last sub.witArity) = g ρ :=
      hsound ρ (w (Fin.last sub.witArity)) (fun k => w k.castSucc) hsub
    refine Fin.lastCases ?_ ?_ i
    · rw [diophPow2_bound_last, hg]
      exact hval ρ
    · intro k
      rw [diophPow2_bound_castSucc]
      exact hbound ρ (g ρ) (fun k => w k.castSucc) (by rw [← hg]; exact hsub) k
  · intro ρ
    simp only [diophPow2, epow2_eval, eraInterp, fcons]
    exact Nat.pow_lt_pow_right Nat.one_lt_two (hval ρ)

/-- The variable embedding extending the binary layout `Fin (n + 1 + wbin)` to a
layout `Fin (n + 1 + (wbin + k))` carrying `k` extra local witnesses: the `n + 1`
inputs and output are fixed, and the binary witness block `Fin wbin` is sent to
the prefix of the extended witness block `Fin (wbin + k)`, leaving the last `k`
slots for the local witnesses. -/
def binExtEmb {n wbin k : ℕ} : Fin (n + 1 + wbin) → Fin (n + 1 + (wbin + k)) :=
  Fin.addCases (fun i => Fin.castAdd (wbin + k) i)
    (fun j => Fin.natAdd (n + 1) (Fin.castAdd k j))

/-- `binExtEmb` is injective: it fixes the input/output prefix and embeds the
binary witness block injectively into the extended witness block. -/
theorem binExtEmb_injective {n wbin k : ℕ} :
    Function.Injective (binExtEmb (n := n) (wbin := wbin) (k := k)) := by
  intro a b hab
  unfold binExtEmb at hab
  induction a using Fin.addCases with
  | left ia =>
    induction b using Fin.addCases with
    | left ib =>
      simp only [Fin.addCases_left] at hab
      exact congrArg _ (Fin.castAdd_injective _ _ hab)
    | right kb =>
      simp only [Fin.addCases_left, Fin.addCases_right, Fin.ext_iff, Fin.val_castAdd,
        Fin.val_natAdd] at hab
      omega
  | right ka =>
    induction b using Fin.addCases with
    | left ib =>
      simp only [Fin.addCases_left, Fin.addCases_right, Fin.ext_iff, Fin.val_castAdd,
        Fin.val_natAdd] at hab
      omega
    | right kb =>
      simp only [Fin.addCases_right] at hab
      have := Fin.natAdd_injective _ _ hab
      exact congrArg _ (Fin.castAdd_injective _ _ this)

/-- The extended context, precomposed with `binExtEmb`, recovers the binary
context: the inputs and output are unchanged, and the binary witnesses read the
prefix `Fin.castAdd k` of the extended witness block. -/
theorem append_snoc_comp_binExtEmb {n wbin k : ℕ} (ρ : Fin n → ℕ) (y : ℕ)
    (w : Fin (wbin + k) → ℕ) :
    (Fin.append (Fin.snoc ρ y) w) ∘ binExtEmb (n := n) (wbin := wbin) (k := k) =
      Fin.append (Fin.snoc ρ y) (fun j => w (Fin.castAdd k j)) := by
  refine funext (fun a => ?_)
  simp only [Function.comp_apply, binExtEmb]
  refine Fin.addCases ?_ ?_ a
  · intro io
    simp only [Fin.addCases_left, Fin.append_left]
  · intro j
    simp only [Fin.addCases_right, Fin.append_right]

/-- The binary spliced system of `sub1`, `sub2`, weakened into the extended
layout `Fin (n + 1 + (sub1.witArity + 1 + sub2.witArity + 1 + k))` carrying `k`
local witnesses. -/
def binExtSplicedSys {n : ℕ} (sub1 sub2 : DiophEnc n) (k : ℕ) :
    SosSystem (n + 1 + (sub1.witArity + 1 + sub2.witArity + 1 + k)) :=
  (binSplicedSys sub1 sub2).weaken binExtEmb

/-- The first sub-output slot in the extended layout, holding `sub1`'s output. -/
def binExtOutSlot1 {w1 w2 k : ℕ} : Fin (w1 + 1 + w2 + 1 + k) :=
  Fin.castAdd k binOutSlot1

/-- The second sub-output slot in the extended layout, holding `sub2`'s output. -/
def binExtOutSlot2 {w1 w2 k : ℕ} : Fin (w1 + 1 + w2 + 1 + k) :=
  Fin.castAdd k binOutSlot2

/-- The first sub-encoding's witness embedding in the extended layout. -/
def binExtWitEmb1 {w1 w2 k : ℕ} (j : Fin w1) : Fin (w1 + 1 + w2 + 1 + k) :=
  Fin.castAdd k (binWitEmb1 j)

/-- The second sub-encoding's witness embedding in the extended layout. -/
def binExtWitEmb2 {w1 w2 k : ℕ} (j : Fin w2) : Fin (w1 + 1 + w2 + 1 + k) :=
  Fin.castAdd k (binWitEmb2 j)

/-- The `i`-th local witness slot in the extended layout: the `i`-th of the `k`
slots appended after the binary block. -/
def binExtLocalSlot {w1 w2 k : ℕ} (i : Fin k) : Fin (w1 + 1 + w2 + 1 + k) :=
  Fin.natAdd (w1 + 1 + w2 + 1) i

/-- The extended binary spliced system vanishes additively into the two
sub-systems evaluated at their recovered contexts, reading their outputs and
witnesses through the extended slot embeddings. -/
theorem binExtSplicedSys_eval {n : ℕ} (sub1 sub2 : DiophEnc n) (k : ℕ) (ρ : Fin n → ℕ)
    (y : ℕ) (w : Fin (sub1.witArity + 1 + sub2.witArity + 1 + k) → ℕ) :
    SosSystem.eval (binExtSplicedSys sub1 sub2 k) (Fin.append (Fin.snoc ρ y) w) =
      SosSystem.eval sub1.sys
          (sub1.ctx ρ (w binExtOutSlot1) (fun j => w (binExtWitEmb1 j))) +
        SosSystem.eval sub2.sys
          (sub2.ctx ρ (w binExtOutSlot2) (fun j => w (binExtWitEmb2 j))) := by
  rw [binExtSplicedSys,
    SosSystem.eval_weaken (binSplicedSys sub1 sub2) binExtEmb binExtEmb_injective,
    append_snoc_comp_binExtEmb, binSplicedSys_eval]
  rfl

/-- Assemble the binary data of a combine — `sub1`-witness data `f1`, the `y₁`
datum `a1`, `sub2`-witness data `f2`, the `y₂` datum `a2` — together with the `k`
local data `loc`, into a single map over the extended layout
`Fin (w1 + 1 + w2 + 1 + k)`, by appending the local block after the binary block.
Used both for the per-witness bound map (`α = ETm n`) and for the assembled
witness tuple (`α = ℕ`). -/
def binExtAssemble {α : Type} {w1 w2 k : ℕ} (f1 : Fin w1 → α) (a1 : α) (f2 : Fin w2 → α)
    (a2 : α) (loc : Fin k → α) : Fin (w1 + 1 + w2 + 1 + k) → α :=
  Fin.append (binAssemble f1 a1 f2 a2) loc

/-- `binExtAssemble` at a `sub1`-witness slot reads `f1`. -/
@[simp]
theorem binExtAssemble_witEmb1 {α : Type} {w1 w2 k : ℕ} (f1 : Fin w1 → α) (a1 : α)
    (f2 : Fin w2 → α) (a2 : α) (loc : Fin k → α) (j : Fin w1) :
    binExtAssemble f1 a1 f2 a2 loc (binExtWitEmb1 j) = f1 j := by
  rw [binExtAssemble, binExtWitEmb1, Fin.append_left, binAssemble_witEmb1]

/-- `binExtAssemble` at the `y₁` slot reads `a1`. -/
@[simp]
theorem binExtAssemble_outSlot1 {α : Type} {w1 w2 k : ℕ} (f1 : Fin w1 → α) (a1 : α)
    (f2 : Fin w2 → α) (a2 : α) (loc : Fin k → α) :
    binExtAssemble f1 a1 f2 a2 loc binExtOutSlot1 = a1 := by
  rw [binExtAssemble, binExtOutSlot1, Fin.append_left, binAssemble_outSlot1]

/-- `binExtAssemble` at a `sub2`-witness slot reads `f2`. -/
@[simp]
theorem binExtAssemble_witEmb2 {α : Type} {w1 w2 k : ℕ} (f1 : Fin w1 → α) (a1 : α)
    (f2 : Fin w2 → α) (a2 : α) (loc : Fin k → α) (j : Fin w2) :
    binExtAssemble f1 a1 f2 a2 loc (binExtWitEmb2 j) = f2 j := by
  rw [binExtAssemble, binExtWitEmb2, Fin.append_left, binAssemble_witEmb2]

/-- `binExtAssemble` at the `y₂` slot reads `a2`. -/
@[simp]
theorem binExtAssemble_outSlot2 {α : Type} {w1 w2 k : ℕ} (f1 : Fin w1 → α) (a1 : α)
    (f2 : Fin w2 → α) (a2 : α) (loc : Fin k → α) :
    binExtAssemble f1 a1 f2 a2 loc binExtOutSlot2 = a2 := by
  rw [binExtAssemble, binExtOutSlot2, Fin.append_left, binAssemble_outSlot2]

/-- `binExtAssemble` at a local slot reads `loc`. -/
@[simp]
theorem binExtAssemble_localSlot {α : Type} {w1 w2 k : ℕ} (f1 : Fin w1 → α) (a1 : α)
    (f2 : Fin w2 → α) (a2 : α) (loc : Fin k → α) (i : Fin k) :
    binExtAssemble f1 a1 f2 a2 loc (binExtLocalSlot i) = loc i := by
  rw [binExtAssemble, binExtLocalSlot, Fin.append_right]

/-- Case analysis on a slot of the extended layout: every
`i : Fin (w1 + 1 + w2 + 1 + k)` is one of the five slot kinds — a `sub1`-witness
`binExtWitEmb1 j`, the `y₁` slot, a `sub2`-witness `binExtWitEmb2 j`, the `y₂`
slot, or a local slot `binExtLocalSlot i`. -/
theorem binExtLayoutCases {w1 w2 k : ℕ} {motive : Fin (w1 + 1 + w2 + 1 + k) → Prop}
    (hwit1 : ∀ j, motive (binExtWitEmb1 j)) (hout1 : motive binExtOutSlot1)
    (hwit2 : ∀ j, motive (binExtWitEmb2 j)) (hout2 : motive binExtOutSlot2)
    (hloc : ∀ i, motive (binExtLocalSlot i)) (i : Fin (w1 + 1 + w2 + 1 + k)) : motive i := by
  refine Fin.addCases (fun a => ?_) (fun b => hloc b) i
  exact binLayoutCases (motive := fun a => motive (Fin.castAdd k a)) hwit1 hout1 hwit2 hout2 a

/-- The per-witness bound map of a binary combine over `sub1`, `sub2` extended by
`k` local witnesses bounded by `loc`: each sub-witness keeps its own input-only
bound, `y₁` is bounded by `sub1.valBound`, `y₂` by `sub2.valBound`, and each local
slot by `loc`. -/
def binExtBound {n k : ℕ} (sub1 sub2 : DiophEnc n) (loc : Fin k → ETm n) :
    Fin (sub1.witArity + 1 + sub2.witArity + 1 + k) → ETm n :=
  binExtAssemble sub1.bound sub1.valBound sub2.bound sub2.valBound loc

/-- The encoding of `fun ρ => g1 ρ - g2 ρ` (truncated subtraction) from encodings
`sub1` of `g1` and `sub2` of `g2`. Beyond the two sub-outputs `y₁`, `y₂`, one local
witness `s` holds the opposite monus `g2 ∸ g1`. Two squared-distance atoms force
`y + y₂ = y₁ + s` and `y · s = 0`; together these pin `(y, s)` uniquely as
`(g1 ∸ g2, g2 ∸ g1)`. Each sub-witness keeps its input-only sub-bound; `y₁` is
bounded by `sub1.valBound`, `y₂` and `s` by `sub2.valBound`. The value majorant is
`sub1.valBound`. -/
def diophTsub {n : ℕ} (sub1 sub2 : DiophEnc n) : DiophEnc n where
  witArity := sub1.witArity + 1 + sub2.witArity + 1 + 1
  sys :=
    binExtSplicedSys sub1 sub2 1 ++
      [.sqDist
        [SimpleMonomial.var (Fin.castAdd (sub1.witArity + 1 + sub2.witArity + 1 + 1) (Fin.last n)),
          SimpleMonomial.var (Fin.natAdd (n + 1) binExtOutSlot2)]
        [SimpleMonomial.var (Fin.natAdd (n + 1) binExtOutSlot1),
          SimpleMonomial.var (Fin.natAdd (n + 1) (binExtLocalSlot 0))],
      .sqDist
        [SimpleMonomial.mulVars
          (Fin.castAdd (sub1.witArity + 1 + sub2.witArity + 1 + 1) (Fin.last n))
          (Fin.natAdd (n + 1) (binExtLocalSlot 0))]
        []]
  bound := binExtBound sub1 sub2 (fun _ => sub2.valBound)
  valBound := sub1.valBound

/-- The `diophTsub sub1 sub2` system vanishes at `ctx ρ y w` exactly when both
sub-systems vanish at their recovered contexts and the witnesses satisfy
`y + y₂ = y₁ + s` and `y · s = 0`. -/
theorem diophTsub_eval_eq_zero_iff {n : ℕ} (sub1 sub2 : DiophEnc n) (ρ : Fin n → ℕ) (y : ℕ)
    (w : Fin (sub1.witArity + 1 + sub2.witArity + 1 + 1) → ℕ) :
    SosSystem.eval (diophTsub sub1 sub2).sys ((diophTsub sub1 sub2).ctx ρ y w) = 0 ↔
      SosSystem.eval sub1.sys
          (sub1.ctx ρ (w binExtOutSlot1) (fun j => w (binExtWitEmb1 j))) = 0 ∧
        SosSystem.eval sub2.sys
            (sub2.ctx ρ (w binExtOutSlot2) (fun j => w (binExtWitEmb2 j))) = 0 ∧
          y + w binExtOutSlot2 = w binExtOutSlot1 + w (binExtLocalSlot 0) ∧
            y * w (binExtLocalSlot 0) = 0 := by
  change SosSystem.eval
      (binExtSplicedSys sub1 sub2 1 ++
        [SosTerm.sqDist
          [SimpleMonomial.var
              (Fin.castAdd (sub1.witArity + 1 + sub2.witArity + 1 + 1) (Fin.last n)),
            SimpleMonomial.var (Fin.natAdd (n + 1) binExtOutSlot2)]
          [SimpleMonomial.var (Fin.natAdd (n + 1) binExtOutSlot1),
            SimpleMonomial.var (Fin.natAdd (n + 1) (binExtLocalSlot 0))],
        SosTerm.sqDist
          [SimpleMonomial.mulVars
            (Fin.castAdd (sub1.witArity + 1 + sub2.witArity + 1 + 1) (Fin.last n))
            (Fin.natAdd (n + 1) (binExtLocalSlot 0))]
          []])
      (Fin.append (Fin.snoc ρ y) w) = 0 ↔ _
  rw [SosSystem.eval_append, binExtSplicedSys_eval, SosSystem.eval, SosSystem.eval,
    SosSystem.eval]
  simp only [Nat.add_zero, Nat.add_eq_zero_iff, SosTerm.sqDist_eval_eq_zero_iff, SimpleSum.eval,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, SimpleMonomial.var_eval,
    SimpleMonomial.mulVars_eval, Fin.append_right, Fin.append_left, Fin.snoc_last]
  omega

/-- The `diophTsub` bound map is the extended binary bound with the local slot
bounded by `sub2.valBound`. -/
@[simp]
theorem diophTsub_bound {n : ℕ} (sub1 sub2 : DiophEnc n) :
    (diophTsub sub1 sub2).bound = binExtBound sub1 sub2 (fun _ => sub2.valBound) := rfl

/-- `diophTsub sub1 sub2` encodes `fun ρ => g1 ρ - g2 ρ` whenever `sub1` encodes
`g1` and `sub2` encodes `g2`. The two equations `y + y₂ = y₁ + s` and `y · s = 0`
over `ℕ`, with `y₁ = g1 ρ` and `y₂ = g2 ρ`, pin `y = g1 ρ ∸ g2 ρ` and the slack
`s = g2 ρ ∸ g1 ρ` uniquely (`omega`). -/
theorem diophTsub_encodes {n : ℕ} {sub1 sub2 : DiophEnc n} {g1 g2 : (Fin n → ℕ) → ℕ}
    (h1 : sub1.Encodes g1) (h2 : sub2.Encodes g2) :
    (diophTsub sub1 sub2).Encodes (fun ρ => g1 ρ - g2 ρ) := by
  obtain ⟨hsound1, huniq1, hbound1, hval1⟩ := h1
  obtain ⟨hsound2, huniq2, hbound2, hval2⟩ := h2
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ρ y w hzero
    rw [diophTsub_eval_eq_zero_iff] at hzero
    obtain ⟨hz1, hz2, hsum, hmul⟩ := hzero
    have e1 := hsound1 ρ (w binExtOutSlot1) (fun j => w (binExtWitEmb1 j)) hz1
    have e2 := hsound2 ρ (w binExtOutSlot2) (fun j => w (binExtWitEmb2 j)) hz2
    change y = g1 ρ - g2 ρ
    rcases Nat.mul_eq_zero.mp hmul with h | h <;> omega
  · intro ρ
    obtain ⟨wsub1, hwsub1, hwsubuniq1⟩ := huniq1 ρ
    obtain ⟨wsub2, hwsub2, hwsubuniq2⟩ := huniq2 ρ
    refine ⟨binExtAssemble wsub1 (g1 ρ) wsub2 (g2 ρ) (fun _ => g2 ρ - g1 ρ), ?_, ?_⟩
    · change (diophTsub sub1 sub2).sys.eval
        ((diophTsub sub1 sub2).ctx ρ (g1 ρ - g2 ρ)
          (binExtAssemble wsub1 (g1 ρ) wsub2 (g2 ρ) (fun _ => g2 ρ - g1 ρ))) = 0
      rw [diophTsub_eval_eq_zero_iff]
      simp only [binExtAssemble_witEmb1, binExtAssemble_outSlot1, binExtAssemble_witEmb2,
        binExtAssemble_outSlot2, binExtAssemble_localSlot]
      refine ⟨hwsub1, hwsub2, by omega, ?_⟩
      rcases Nat.le_total (g2 ρ) (g1 ρ) with h | h
      · rw [Nat.sub_eq_zero_of_le h, Nat.mul_zero]
      · rw [Nat.sub_eq_zero_of_le h, Nat.zero_mul]
    · intro w' hw'
      have hw'' : (diophTsub sub1 sub2).sys.eval
        ((diophTsub sub1 sub2).ctx ρ (g1 ρ - g2 ρ) w') = 0 := hw'
      rw [diophTsub_eval_eq_zero_iff] at hw''
      obtain ⟨hz1', hz2', hsum', hmul'⟩ := hw''
      have hg1 : w' binExtOutSlot1 = g1 ρ :=
        hsound1 ρ (w' binExtOutSlot1) (fun j => w' (binExtWitEmb1 j)) hz1'
      have hg2 : w' binExtOutSlot2 = g2 ρ :=
        hsound2 ρ (w' binExtOutSlot2) (fun j => w' (binExtWitEmb2 j)) hz2'
      have he1 : (fun j => w' (binExtWitEmb1 j)) = wsub1 :=
        hwsubuniq1 (fun j => w' (binExtWitEmb1 j)) (by rw [← hg1]; exact hz1')
      have he2 : (fun j => w' (binExtWitEmb2 j)) = wsub2 :=
        hwsubuniq2 (fun j => w' (binExtWitEmb2 j)) (by rw [← hg2]; exact hz2')
      have hslack : w' (binExtLocalSlot 0) = g2 ρ - g1 ρ := by
        rcases Nat.eq_zero_or_pos (w' (binExtLocalSlot 0)) with hs | hs
        · rw [hg1, hg2] at hsum'; omega
        · have : g1 ρ - g2 ρ = 0 := by
            rcases Nat.mul_eq_zero.mp hmul' with h | h
            · exact h
            · omega
          rw [hg1, hg2] at hsum'; omega
      refine funext (binExtLayoutCases (fun j => ?_) ?_ (fun j => ?_) ?_ (fun i => ?_))
      · rw [binExtAssemble_witEmb1]; exact congrFun he1 j
      · rw [binExtAssemble_outSlot1]; exact hg1
      · rw [binExtAssemble_witEmb2]; exact congrFun he2 j
      · rw [binExtAssemble_outSlot2]; exact hg2
      · rw [binExtAssemble_localSlot, Fin.fin_one_eq_zero i]; exact hslack
  · intro ρ y w hzero i
    rw [diophTsub_eval_eq_zero_iff] at hzero
    obtain ⟨hz1, hz2, hsum, hmul⟩ := hzero
    have hg1 : w binExtOutSlot1 = g1 ρ :=
      hsound1 ρ (w binExtOutSlot1) (fun j => w (binExtWitEmb1 j)) hz1
    have hg2 : w binExtOutSlot2 = g2 ρ :=
      hsound2 ρ (w binExtOutSlot2) (fun j => w (binExtWitEmb2 j)) hz2
    rw [diophTsub_bound]
    induction i using binExtLayoutCases with
    | hwit1 j =>
      rw [binExtBound, binExtAssemble_witEmb1]
      exact hbound1 ρ (g1 ρ) (fun j => w (binExtWitEmb1 j)) (by rw [← hg1]; exact hz1) j
    | hout1 =>
      rw [binExtBound, binExtAssemble_outSlot1, hg1]
      exact hval1 ρ
    | hwit2 j =>
      rw [binExtBound, binExtAssemble_witEmb2]
      exact hbound2 ρ (g2 ρ) (fun j => w (binExtWitEmb2 j)) (by rw [← hg2]; exact hz2) j
    | hout2 =>
      rw [binExtBound, binExtAssemble_outSlot2, hg2]
      exact hval2 ρ
    | hloc i =>
      rw [binExtBound, binExtAssemble_localSlot]
      have hle : w (binExtLocalSlot i) ≤ w binExtOutSlot2 := by
        rw [Fin.fin_one_eq_zero i]
        rcases Nat.mul_eq_zero.mp hmul with h | h <;> omega
      exact Nat.lt_of_le_of_lt (hle.trans_eq hg2) (hval2 ρ)
  · intro ρ
    have := hval1 ρ
    simp only [diophTsub]
    omega

/-- The encoding of `fun ρ => g1 ρ % g2 ρ` (natural-number remainder, with the
`Nat.mod` convention `g1 % 0 = g1`) from encodings `sub1` of `g1` and `sub2` of
`g2`. Beyond the two sub-outputs `y₁`, `y₂`, two local witnesses `y₃` and `q` hold
the predecessor slack `y₂ ∸ (y + 1)` and the quotient `y₁ / y₂`. The gadget is a
single product atom of two bracket sub-systems: the first bracket (`bracketA`)
encodes the division-with-remainder branch `y₁ = q · y₂ + y ∧ y₂ = y₃ + y + 1`
(so `y < y₂`), valid when `y₂ ≠ 0`; the second (`bracketB`) encodes the branch
`y₂ = 0 ∧ y₃ = 0 ∧ y = y₁ ∧ q = 0`, valid when `y₂ = 0` (where `g1 % 0 = g1`).
Both brackets pin `y₃` and `q`, which the product zero-set needs for uniqueness.
Each sub-witness keeps its input-only sub-bound; `y₁` and `q` are bounded by
`sub1.valBound`, `y₂` and `y₃` by `sub2.valBound`. The value majorant is
`sub1.valBound`. -/
def diophMod {n : ℕ} (sub1 sub2 : DiophEnc n) : DiophEnc n where
  witArity := sub1.witArity + 1 + sub2.witArity + 1 + 2
  sys :=
    binExtSplicedSys sub1 sub2 2 ++
      [.prod
        [.sqDist
          [SimpleMonomial.var (Fin.natAdd (n + 1) binExtOutSlot1)]
          [SimpleMonomial.mulVars (Fin.natAdd (n + 1) (binExtLocalSlot 1))
              (Fin.natAdd (n + 1) binExtOutSlot2),
            SimpleMonomial.var (Fin.castAdd (sub1.witArity + 1 + sub2.witArity + 1 + 2)
              (Fin.last n))],
        .sqDist
          [SimpleMonomial.var (Fin.natAdd (n + 1) binExtOutSlot2)]
          [SimpleMonomial.var (Fin.natAdd (n + 1) (binExtLocalSlot 0)),
            SimpleMonomial.var (Fin.castAdd (sub1.witArity + 1 + sub2.witArity + 1 + 2)
              (Fin.last n)),
            SimpleMonomial.one]]
        [.sqDist
          [SimpleMonomial.var (Fin.natAdd (n + 1) binExtOutSlot2)] [],
        .sqDist
          [SimpleMonomial.var (Fin.natAdd (n + 1) (binExtLocalSlot 0))] [],
        .sqDist
          [SimpleMonomial.var (Fin.castAdd (sub1.witArity + 1 + sub2.witArity + 1 + 2)
            (Fin.last n))]
          [SimpleMonomial.var (Fin.natAdd (n + 1) binExtOutSlot1)],
        .sqDist
          [SimpleMonomial.var (Fin.natAdd (n + 1) (binExtLocalSlot 1))] []]]
  bound := binExtBound sub1 sub2 (Fin.cons sub2.valBound (fun _ => sub1.valBound))
  valBound := sub1.valBound

/-- The `diophMod sub1 sub2` system vanishes at `ctx ρ y w` exactly when both
sub-systems vanish at their recovered contexts and the witnesses satisfy the
disjunction of the two bracket branches: either `y₁ = q · y₂ + y ∧ y₂ = y₃ + y + 1`
(the `y₂ ≠ 0` branch) or `y₂ = 0 ∧ y₃ = 0 ∧ y = y₁ ∧ q = 0` (the `y₂ = 0`
branch). -/
theorem diophMod_eval_eq_zero_iff {n : ℕ} (sub1 sub2 : DiophEnc n) (ρ : Fin n → ℕ) (y : ℕ)
    (w : Fin (sub1.witArity + 1 + sub2.witArity + 1 + 2) → ℕ) :
    SosSystem.eval (diophMod sub1 sub2).sys ((diophMod sub1 sub2).ctx ρ y w) = 0 ↔
      SosSystem.eval sub1.sys
          (sub1.ctx ρ (w binExtOutSlot1) (fun j => w (binExtWitEmb1 j))) = 0 ∧
        SosSystem.eval sub2.sys
            (sub2.ctx ρ (w binExtOutSlot2) (fun j => w (binExtWitEmb2 j))) = 0 ∧
          ((w binExtOutSlot1 = w (binExtLocalSlot 1) * w binExtOutSlot2 + y ∧
              w binExtOutSlot2 = w (binExtLocalSlot 0) + y + 1) ∨
            (w binExtOutSlot2 = 0 ∧ w (binExtLocalSlot 0) = 0 ∧
              y = w binExtOutSlot1 ∧ w (binExtLocalSlot 1) = 0)) := by
  change SosSystem.eval
      (binExtSplicedSys sub1 sub2 2 ++
        [SosTerm.prod
          [SosTerm.sqDist
            [SimpleMonomial.var (Fin.natAdd (n + 1) binExtOutSlot1)]
            [SimpleMonomial.mulVars (Fin.natAdd (n + 1) (binExtLocalSlot 1))
                (Fin.natAdd (n + 1) binExtOutSlot2),
              SimpleMonomial.var (Fin.castAdd (sub1.witArity + 1 + sub2.witArity + 1 + 2)
                (Fin.last n))],
          SosTerm.sqDist
            [SimpleMonomial.var (Fin.natAdd (n + 1) binExtOutSlot2)]
            [SimpleMonomial.var (Fin.natAdd (n + 1) (binExtLocalSlot 0)),
              SimpleMonomial.var (Fin.castAdd (sub1.witArity + 1 + sub2.witArity + 1 + 2)
                (Fin.last n)),
              SimpleMonomial.one]]
          [SosTerm.sqDist
            [SimpleMonomial.var (Fin.natAdd (n + 1) binExtOutSlot2)] [],
          SosTerm.sqDist
            [SimpleMonomial.var (Fin.natAdd (n + 1) (binExtLocalSlot 0))] [],
          SosTerm.sqDist
            [SimpleMonomial.var (Fin.castAdd (sub1.witArity + 1 + sub2.witArity + 1 + 2)
              (Fin.last n))]
            [SimpleMonomial.var (Fin.natAdd (n + 1) binExtOutSlot1)],
          SosTerm.sqDist
            [SimpleMonomial.var (Fin.natAdd (n + 1) (binExtLocalSlot 1))] []]])
      (Fin.append (Fin.snoc ρ y) w) = 0 ↔ _
  rw [SosSystem.eval_append]
  rw [binExtSplicedSys_eval sub1 sub2 2 ρ y w]
  simp only [SosSystem.eval, Nat.add_zero, Nat.add_eq_zero_iff, SosTerm.prod_eval_eq_zero_iff,
    SosTerm.sqDist_eval_eq_zero_iff, SimpleSum.eval, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, SimpleMonomial.var_eval, SimpleMonomial.mulVars_eval,
    SimpleMonomial.one_eval, Fin.append_right, Fin.append_left, Fin.snoc_last]
  omega

/-- Either bracket branch, together with `y₁ = g1` and `y₂ = g2`, forces
`y = g1 % g2` (with the `Nat.mod` convention `g1 % 0 = g1`). -/
private theorem diophMod_branch_mod {y₁ y₂ y₃ q y : ℕ}
    (h : (y₁ = q * y₂ + y ∧ y₂ = y₃ + y + 1) ∨
      (y₂ = 0 ∧ y₃ = 0 ∧ y = y₁ ∧ q = 0)) :
    y = y₁ % y₂ := by
  rcases h with ⟨he, hlt⟩ | ⟨h0, _, hy, _⟩
  · have hylt : y < y₂ := by omega
    rw [he, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hylt]
  · rw [h0, hy, Nat.mod_zero]

/-- The `diophMod` bound map. -/
@[simp]
theorem diophMod_bound {n : ℕ} (sub1 sub2 : DiophEnc n) :
    (diophMod sub1 sub2).bound =
      binExtBound sub1 sub2 (Fin.cons sub2.valBound (fun _ => sub1.valBound)) := rfl

/-- `diophMod sub1 sub2` encodes `fun ρ => g1 ρ % g2 ρ` whenever `sub1` encodes
`g1` and `sub2` encodes `g2`. The two bracket branches reduce, via the
division-with-remainder identity (`Nat.add_mul_mod_self_right`, `Nat.mod_eq_of_lt`)
and the `g1 % 0 = g1` convention, to `y = g1 ρ % g2 ρ`, with the local witnesses
`y₃ = g2 ρ ∸ (y + 1)` and `q = g1 ρ / g2 ρ` pinned by both brackets. -/
theorem diophMod_encodes {n : ℕ} {sub1 sub2 : DiophEnc n} {g1 g2 : (Fin n → ℕ) → ℕ}
    (h1 : sub1.Encodes g1) (h2 : sub2.Encodes g2) :
    (diophMod sub1 sub2).Encodes (fun ρ => g1 ρ % g2 ρ) := by
  obtain ⟨hsound1, huniq1, hbound1, hval1⟩ := h1
  obtain ⟨hsound2, huniq2, hbound2, hval2⟩ := h2
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ρ y w hzero
    rw [diophMod_eval_eq_zero_iff] at hzero
    obtain ⟨hz1, hz2, hbr⟩ := hzero
    have e1 := hsound1 ρ (w binExtOutSlot1) (fun j => w (binExtWitEmb1 j)) hz1
    have e2 := hsound2 ρ (w binExtOutSlot2) (fun j => w (binExtWitEmb2 j)) hz2
    rw [e1, e2] at hbr
    exact diophMod_branch_mod hbr
  · intro ρ
    obtain ⟨wsub1, hwsub1, hwsubuniq1⟩ := huniq1 ρ
    obtain ⟨wsub2, hwsub2, hwsubuniq2⟩ := huniq2 ρ
    refine ⟨binExtAssemble wsub1 (g1 ρ) wsub2 (g2 ρ)
        (Fin.cons (g2 ρ - (g1 ρ % g2 ρ) - 1) (fun _ => g1 ρ / g2 ρ)), ?_, ?_⟩
    · change (diophMod sub1 sub2).sys.eval
        ((diophMod sub1 sub2).ctx ρ (g1 ρ % g2 ρ)
          (binExtAssemble wsub1 (g1 ρ) wsub2 (g2 ρ)
            (Fin.cons (g2 ρ - (g1 ρ % g2 ρ) - 1) (fun _ => g1 ρ / g2 ρ)))) = 0
      rw [diophMod_eval_eq_zero_iff]
      simp only [binExtAssemble_witEmb1, binExtAssemble_outSlot1, binExtAssemble_witEmb2,
        binExtAssemble_outSlot2, binExtAssemble_localSlot, Fin.cons_zero, Fin.cons_one]
      refine ⟨hwsub1, hwsub2, ?_⟩
      rcases Nat.eq_zero_or_pos (g2 ρ) with h0 | hpos
      · right
        rw [h0, Nat.mod_zero, Nat.div_zero, Nat.zero_sub, Nat.zero_sub]
        exact ⟨rfl, rfl, rfl, rfl⟩
      · left
        refine ⟨?_, ?_⟩
        · rw [Nat.mul_comm, Nat.div_add_mod]
        · have hlt : g1 ρ % g2 ρ < g2 ρ := Nat.mod_lt _ hpos
          omega
    · intro w' hw'
      have hw'' : (diophMod sub1 sub2).sys.eval
        ((diophMod sub1 sub2).ctx ρ (g1 ρ % g2 ρ) w') = 0 := hw'
      rw [diophMod_eval_eq_zero_iff] at hw''
      obtain ⟨hz1', hz2', hbr'⟩ := hw''
      have hg1 : w' binExtOutSlot1 = g1 ρ :=
        hsound1 ρ (w' binExtOutSlot1) (fun j => w' (binExtWitEmb1 j)) hz1'
      have hg2 : w' binExtOutSlot2 = g2 ρ :=
        hsound2 ρ (w' binExtOutSlot2) (fun j => w' (binExtWitEmb2 j)) hz2'
      have he1 : (fun j => w' (binExtWitEmb1 j)) = wsub1 :=
        hwsubuniq1 (fun j => w' (binExtWitEmb1 j)) (by rw [← hg1]; exact hz1')
      have he2 : (fun j => w' (binExtWitEmb2 j)) = wsub2 :=
        hwsubuniq2 (fun j => w' (binExtWitEmb2 j)) (by rw [← hg2]; exact hz2')
      rw [hg1, hg2] at hbr'
      have hslack0 : w' (binExtLocalSlot 0) = g2 ρ - (g1 ρ % g2 ρ) - 1 := by
        rcases hbr' with ⟨he, hlt⟩ | ⟨h0, hy3, hy, _⟩
        · omega
        · rw [h0, Nat.mod_zero]; omega
      have hq : w' (binExtLocalSlot 1) = g1 ρ / g2 ρ := by
        rcases hbr' with ⟨he, hlt⟩ | ⟨h0, _, _, hq0⟩
        · have hpos : 0 < g2 ρ := by omega
          have hdiv : g1 ρ / g2 ρ = (g1 ρ % g2 ρ + w' (binExtLocalSlot 1) * g2 ρ) / g2 ρ := by
            rw [Nat.add_comm, ← he]
          rw [hdiv, Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt (Nat.mod_lt _ hpos)]
          omega
        · rw [h0, Nat.div_zero]; exact hq0
      refine funext (binExtLayoutCases (fun j => ?_) ?_ (fun j => ?_) ?_ (fun i => ?_))
      · rw [binExtAssemble_witEmb1]; exact congrFun he1 j
      · rw [binExtAssemble_outSlot1]; exact hg1
      · rw [binExtAssemble_witEmb2]; exact congrFun he2 j
      · rw [binExtAssemble_outSlot2]; exact hg2
      · rw [binExtAssemble_localSlot]
        refine Fin.cases ?_ (fun j => ?_) i
        · rw [Fin.cons_zero]; exact hslack0
        · rw [Fin.cons_succ, Fin.fin_one_eq_zero j]; exact hq
  · intro ρ y w hzero i
    rw [diophMod_eval_eq_zero_iff] at hzero
    obtain ⟨hz1, hz2, hbr⟩ := hzero
    have hg1 : w binExtOutSlot1 = g1 ρ :=
      hsound1 ρ (w binExtOutSlot1) (fun j => w (binExtWitEmb1 j)) hz1
    have hg2 : w binExtOutSlot2 = g2 ρ :=
      hsound2 ρ (w binExtOutSlot2) (fun j => w (binExtWitEmb2 j)) hz2
    rw [hg1, hg2] at hbr
    rw [diophMod_bound]
    induction i using binExtLayoutCases with
    | hwit1 j =>
      rw [binExtBound, binExtAssemble_witEmb1]
      exact hbound1 ρ (g1 ρ) (fun j => w (binExtWitEmb1 j)) (by rw [← hg1]; exact hz1) j
    | hout1 =>
      rw [binExtBound, binExtAssemble_outSlot1, hg1]
      exact hval1 ρ
    | hwit2 j =>
      rw [binExtBound, binExtAssemble_witEmb2]
      exact hbound2 ρ (g2 ρ) (fun j => w (binExtWitEmb2 j)) (by rw [← hg2]; exact hz2) j
    | hout2 =>
      rw [binExtBound, binExtAssemble_outSlot2, hg2]
      exact hval2 ρ
    | hloc i =>
      rw [binExtBound, binExtAssemble_localSlot]
      refine Fin.cases ?_ (fun j => ?_) i
      · rw [Fin.cons_zero]
        have hle : w (binExtLocalSlot 0) ≤ g2 ρ := by
          rcases hbr with ⟨_, hlt⟩ | ⟨_, hy3, _, _⟩ <;> omega
        exact Nat.lt_of_le_of_lt hle (hval2 ρ)
      · rw [Fin.cons_succ, Fin.fin_one_eq_zero j]
        have hle : w (binExtLocalSlot 1) ≤ g1 ρ := by
          rcases hbr with ⟨he, hlt⟩ | ⟨_, _, _, hq0⟩
          · rcases Nat.eq_zero_or_pos (w (binExtLocalSlot 1)) with hq | hq
            · omega
            · have : w (binExtLocalSlot 1) * g2 ρ ≤ g1 ρ := by omega
              have hg2pos : 0 < g2 ρ := by omega
              calc w (binExtLocalSlot 1) ≤ w (binExtLocalSlot 1) * g2 ρ :=
                    Nat.le_mul_of_pos_right _ hg2pos
                _ ≤ g1 ρ := this
          · omega
        exact Nat.lt_of_le_of_lt hle (hval1 ρ)
  · intro ρ
    have := hval1 ρ
    have hmod : g1 ρ % g2 ρ ≤ g1 ρ := Nat.mod_le _ _
    simp only [diophMod]
    omega

/-- The encoding of `fun ρ => g1 ρ / g2 ρ` (natural-number division, with the
`Nat.div` convention `g1 / 0 = 0`) from encodings `sub1` of `g1` and `sub2` of
`g2`. Beyond the two sub-outputs `y₁`, `y₂`, two local witnesses `r` and `y₃` hold
the remainder `y₁ % y₂` and the predecessor slack `y₂ ∸ (r + 1)`. The gadget is a
single product atom of two bracket sub-systems: the first bracket (`branchA`)
encodes the division-with-remainder branch `y · y₂ + r = y₁ ∧ y₂ = r + y₃ + 1`
(so `r < y₂`), valid when `y₂ ≠ 0`; the second (`branchB`) encodes the branch
`y₂ = 0 ∧ y = 0 ∧ r = 0 ∧ y₃ = 0`, valid when `y₂ = 0` (where `g1 / 0 = 0`). Both
brackets pin `r` and `y₃`, which the product zero-set needs for uniqueness. Each
sub-witness keeps its input-only sub-bound; `y₁` is bounded by `sub1.valBound`, and
`y₂`, `r`, `y₃` by `sub2.valBound`. The value majorant is `sub1.valBound`. -/
def diophDiv {n : ℕ} (sub1 sub2 : DiophEnc n) : DiophEnc n where
  witArity := sub1.witArity + 1 + sub2.witArity + 1 + 2
  sys :=
    binExtSplicedSys sub1 sub2 2 ++
      [.prod
        [.sqDist
          [SimpleMonomial.mulVars (Fin.castAdd (sub1.witArity + 1 + sub2.witArity + 1 + 2)
              (Fin.last n)) (Fin.natAdd (n + 1) binExtOutSlot2),
            SimpleMonomial.var (Fin.natAdd (n + 1) (binExtLocalSlot 0))]
          [SimpleMonomial.var (Fin.natAdd (n + 1) binExtOutSlot1)],
        .sqDist
          [SimpleMonomial.var (Fin.natAdd (n + 1) binExtOutSlot2)]
          [SimpleMonomial.var (Fin.natAdd (n + 1) (binExtLocalSlot 0)),
            SimpleMonomial.var (Fin.natAdd (n + 1) (binExtLocalSlot 1)),
            SimpleMonomial.one]]
        [.sqDist
          [SimpleMonomial.var (Fin.natAdd (n + 1) binExtOutSlot2)] [],
        .sqDist
          [SimpleMonomial.var (Fin.castAdd (sub1.witArity + 1 + sub2.witArity + 1 + 2)
            (Fin.last n))] [],
        .sqDist
          [SimpleMonomial.var (Fin.natAdd (n + 1) (binExtLocalSlot 0))] [],
        .sqDist
          [SimpleMonomial.var (Fin.natAdd (n + 1) (binExtLocalSlot 1))] []]]
  bound := binExtBound sub1 sub2 (Fin.cons sub2.valBound (fun _ => sub2.valBound))
  valBound := sub1.valBound

/-- The `diophDiv sub1 sub2` system vanishes at `ctx ρ y w` exactly when both
sub-systems vanish at their recovered contexts and the witnesses satisfy the
disjunction of the two bracket branches: either `y · y₂ + r = y₁ ∧ y₂ = r + y₃ + 1`
(the `y₂ ≠ 0` branch) or `y₂ = 0 ∧ y = 0 ∧ r = 0 ∧ y₃ = 0` (the `y₂ = 0`
branch). -/
theorem diophDiv_eval_eq_zero_iff {n : ℕ} (sub1 sub2 : DiophEnc n) (ρ : Fin n → ℕ) (y : ℕ)
    (w : Fin (sub1.witArity + 1 + sub2.witArity + 1 + 2) → ℕ) :
    SosSystem.eval (diophDiv sub1 sub2).sys ((diophDiv sub1 sub2).ctx ρ y w) = 0 ↔
      SosSystem.eval sub1.sys
          (sub1.ctx ρ (w binExtOutSlot1) (fun j => w (binExtWitEmb1 j))) = 0 ∧
        SosSystem.eval sub2.sys
            (sub2.ctx ρ (w binExtOutSlot2) (fun j => w (binExtWitEmb2 j))) = 0 ∧
          ((y * w binExtOutSlot2 + w (binExtLocalSlot 0) = w binExtOutSlot1 ∧
              w binExtOutSlot2 = w (binExtLocalSlot 0) + w (binExtLocalSlot 1) + 1) ∨
            (w binExtOutSlot2 = 0 ∧ y = 0 ∧ w (binExtLocalSlot 0) = 0 ∧
              w (binExtLocalSlot 1) = 0)) := by
  change SosSystem.eval
      (binExtSplicedSys sub1 sub2 2 ++
        [SosTerm.prod
          [SosTerm.sqDist
            [SimpleMonomial.mulVars (Fin.castAdd (sub1.witArity + 1 + sub2.witArity + 1 + 2)
                (Fin.last n)) (Fin.natAdd (n + 1) binExtOutSlot2),
              SimpleMonomial.var (Fin.natAdd (n + 1) (binExtLocalSlot 0))]
            [SimpleMonomial.var (Fin.natAdd (n + 1) binExtOutSlot1)],
          SosTerm.sqDist
            [SimpleMonomial.var (Fin.natAdd (n + 1) binExtOutSlot2)]
            [SimpleMonomial.var (Fin.natAdd (n + 1) (binExtLocalSlot 0)),
              SimpleMonomial.var (Fin.natAdd (n + 1) (binExtLocalSlot 1)),
              SimpleMonomial.one]]
          [SosTerm.sqDist
            [SimpleMonomial.var (Fin.natAdd (n + 1) binExtOutSlot2)] [],
          SosTerm.sqDist
            [SimpleMonomial.var (Fin.castAdd (sub1.witArity + 1 + sub2.witArity + 1 + 2)
              (Fin.last n))] [],
          SosTerm.sqDist
            [SimpleMonomial.var (Fin.natAdd (n + 1) (binExtLocalSlot 0))] [],
          SosTerm.sqDist
            [SimpleMonomial.var (Fin.natAdd (n + 1) (binExtLocalSlot 1))] []]])
      (Fin.append (Fin.snoc ρ y) w) = 0 ↔ _
  rw [SosSystem.eval_append]
  rw [binExtSplicedSys_eval sub1 sub2 2 ρ y w]
  simp only [SosSystem.eval, Nat.add_zero, Nat.add_eq_zero_iff, SosTerm.prod_eval_eq_zero_iff,
    SosTerm.sqDist_eval_eq_zero_iff, SimpleSum.eval, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, SimpleMonomial.var_eval, SimpleMonomial.mulVars_eval,
    SimpleMonomial.one_eval, Fin.append_right, Fin.append_left, Fin.snoc_last]
  omega

/-- Either bracket branch, together with `y₁ = g1` and `y₂ = g2`, forces
`y = g1 / g2` (with the `Nat.div` convention `g1 / 0 = 0`). -/
private theorem diophDiv_branch_div {y₁ y₂ y₃ r y : ℕ}
    (h : (y * y₂ + r = y₁ ∧ y₂ = r + y₃ + 1) ∨
      (y₂ = 0 ∧ y = 0 ∧ r = 0 ∧ y₃ = 0)) :
    y = y₁ / y₂ := by
  rcases h with ⟨he, hlt⟩ | ⟨h0, hy, _, _⟩
  · have hrlt : r < y₂ := by omega
    have hpos : 0 < y₂ := by omega
    rw [← he, Nat.add_comm, Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hrlt,
      Nat.zero_add]
  · rw [h0, hy, Nat.div_zero]

/-- The `diophDiv` bound map. -/
@[simp]
theorem diophDiv_bound {n : ℕ} (sub1 sub2 : DiophEnc n) :
    (diophDiv sub1 sub2).bound =
      binExtBound sub1 sub2 (Fin.cons sub2.valBound (fun _ => sub2.valBound)) := rfl

/-- `diophDiv sub1 sub2` encodes `fun ρ => g1 ρ / g2 ρ` whenever `sub1` encodes
`g1` and `sub2` encodes `g2`. The two bracket branches reduce, via the
division-with-remainder identity (`Nat.add_mul_div_right`, `Nat.div_eq_of_lt`) and
the `g1 / 0 = 0` convention, to `y = g1 ρ / g2 ρ`, with the local witnesses
`r = g1 ρ % g2 ρ` and `y₃ = g2 ρ ∸ (r + 1)` pinned by both brackets. -/
theorem diophDiv_encodes {n : ℕ} {sub1 sub2 : DiophEnc n} {g1 g2 : (Fin n → ℕ) → ℕ}
    (h1 : sub1.Encodes g1) (h2 : sub2.Encodes g2) :
    (diophDiv sub1 sub2).Encodes (fun ρ => g1 ρ / g2 ρ) := by
  obtain ⟨hsound1, huniq1, hbound1, hval1⟩ := h1
  obtain ⟨hsound2, huniq2, hbound2, hval2⟩ := h2
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ρ y w hzero
    rw [diophDiv_eval_eq_zero_iff] at hzero
    obtain ⟨hz1, hz2, hbr⟩ := hzero
    have e1 := hsound1 ρ (w binExtOutSlot1) (fun j => w (binExtWitEmb1 j)) hz1
    have e2 := hsound2 ρ (w binExtOutSlot2) (fun j => w (binExtWitEmb2 j)) hz2
    rw [e1, e2] at hbr
    exact diophDiv_branch_div hbr
  · intro ρ
    obtain ⟨wsub1, hwsub1, hwsubuniq1⟩ := huniq1 ρ
    obtain ⟨wsub2, hwsub2, hwsubuniq2⟩ := huniq2 ρ
    refine ⟨binExtAssemble wsub1 (g1 ρ) wsub2 (g2 ρ)
        (Fin.cons (if g2 ρ = 0 then 0 else g1 ρ % g2 ρ)
          (fun _ => g2 ρ - (g1 ρ % g2 ρ) - 1)), ?_, ?_⟩
    · change (diophDiv sub1 sub2).sys.eval
        ((diophDiv sub1 sub2).ctx ρ (g1 ρ / g2 ρ)
          (binExtAssemble wsub1 (g1 ρ) wsub2 (g2 ρ)
            (Fin.cons (if g2 ρ = 0 then 0 else g1 ρ % g2 ρ)
              (fun _ => g2 ρ - (g1 ρ % g2 ρ) - 1)))) = 0
      rw [diophDiv_eval_eq_zero_iff]
      simp only [binExtAssemble_witEmb1, binExtAssemble_outSlot1, binExtAssemble_witEmb2,
        binExtAssemble_outSlot2, binExtAssemble_localSlot, Fin.cons_zero, Fin.cons_one]
      refine ⟨hwsub1, hwsub2, ?_⟩
      rcases Nat.eq_zero_or_pos (g2 ρ) with h0 | hpos
      · right
        rw [if_pos h0, h0, Nat.div_zero, Nat.mod_zero, Nat.zero_sub, Nat.zero_sub]
        exact ⟨rfl, rfl, rfl, rfl⟩
      · left
        rw [if_neg (by omega : ¬ g2 ρ = 0)]
        have hdm : g1 ρ / g2 ρ * g2 ρ + g1 ρ % g2 ρ = g1 ρ := by
          rw [Nat.mul_comm, Nat.div_add_mod]
        have hlt : g1 ρ % g2 ρ < g2 ρ := Nat.mod_lt _ hpos
        refine ⟨by omega, by omega⟩
    · intro w' hw'
      have hw'' : (diophDiv sub1 sub2).sys.eval
        ((diophDiv sub1 sub2).ctx ρ (g1 ρ / g2 ρ) w') = 0 := hw'
      rw [diophDiv_eval_eq_zero_iff] at hw''
      obtain ⟨hz1', hz2', hbr'⟩ := hw''
      have hg1 : w' binExtOutSlot1 = g1 ρ :=
        hsound1 ρ (w' binExtOutSlot1) (fun j => w' (binExtWitEmb1 j)) hz1'
      have hg2 : w' binExtOutSlot2 = g2 ρ :=
        hsound2 ρ (w' binExtOutSlot2) (fun j => w' (binExtWitEmb2 j)) hz2'
      have he1 : (fun j => w' (binExtWitEmb1 j)) = wsub1 :=
        hwsubuniq1 (fun j => w' (binExtWitEmb1 j)) (by rw [← hg1]; exact hz1')
      have he2 : (fun j => w' (binExtWitEmb2 j)) = wsub2 :=
        hwsubuniq2 (fun j => w' (binExtWitEmb2 j)) (by rw [← hg2]; exact hz2')
      rw [hg1, hg2] at hbr'
      have hrem : w' (binExtLocalSlot 0) = if g2 ρ = 0 then 0 else g1 ρ % g2 ρ := by
        rcases hbr' with ⟨he, hlt⟩ | ⟨h0, _, hr, _⟩
        · have hrlt : w' (binExtLocalSlot 0) < g2 ρ := by omega
          have hmod : g1 ρ % g2 ρ = w' (binExtLocalSlot 0) := by
            rw [← he, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hrlt]
          rw [if_neg (by omega : ¬ g2 ρ = 0)]; omega
        · rw [if_pos h0]; exact hr
      have hslack : w' (binExtLocalSlot 1) = g2 ρ - (g1 ρ % g2 ρ) - 1 := by
        rcases hbr' with ⟨he, hlt⟩ | ⟨h0, _, _, _⟩
        · have hrlt : w' (binExtLocalSlot 0) < g2 ρ := by omega
          have hmod : g1 ρ % g2 ρ = w' (binExtLocalSlot 0) := by
            rw [← he, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hrlt]
          rw [hmod]; omega
        · rw [h0, Nat.mod_zero]; omega
      refine funext (binExtLayoutCases (fun j => ?_) ?_ (fun j => ?_) ?_ (fun i => ?_))
      · rw [binExtAssemble_witEmb1]; exact congrFun he1 j
      · rw [binExtAssemble_outSlot1]; exact hg1
      · rw [binExtAssemble_witEmb2]; exact congrFun he2 j
      · rw [binExtAssemble_outSlot2]; exact hg2
      · rw [binExtAssemble_localSlot]
        refine Fin.cases ?_ (fun j => ?_) i
        · rw [Fin.cons_zero]; exact hrem
        · rw [Fin.cons_succ, Fin.fin_one_eq_zero j]; exact hslack
  · intro ρ y w hzero i
    rw [diophDiv_eval_eq_zero_iff] at hzero
    obtain ⟨hz1, hz2, hbr⟩ := hzero
    have hg1 : w binExtOutSlot1 = g1 ρ :=
      hsound1 ρ (w binExtOutSlot1) (fun j => w (binExtWitEmb1 j)) hz1
    have hg2 : w binExtOutSlot2 = g2 ρ :=
      hsound2 ρ (w binExtOutSlot2) (fun j => w (binExtWitEmb2 j)) hz2
    rw [hg1, hg2] at hbr
    rw [diophDiv_bound]
    induction i using binExtLayoutCases with
    | hwit1 j =>
      rw [binExtBound, binExtAssemble_witEmb1]
      exact hbound1 ρ (g1 ρ) (fun j => w (binExtWitEmb1 j)) (by rw [← hg1]; exact hz1) j
    | hout1 =>
      rw [binExtBound, binExtAssemble_outSlot1, hg1]
      exact hval1 ρ
    | hwit2 j =>
      rw [binExtBound, binExtAssemble_witEmb2]
      exact hbound2 ρ (g2 ρ) (fun j => w (binExtWitEmb2 j)) (by rw [← hg2]; exact hz2) j
    | hout2 =>
      rw [binExtBound, binExtAssemble_outSlot2, hg2]
      exact hval2 ρ
    | hloc i =>
      rw [binExtBound, binExtAssemble_localSlot]
      refine Fin.cases ?_ (fun j => ?_) i
      · rw [Fin.cons_zero]
        have hle : w (binExtLocalSlot 0) ≤ g2 ρ := by
          rcases hbr with ⟨_, hlt⟩ | ⟨_, _, hr, _⟩ <;> omega
        exact Nat.lt_of_le_of_lt hle (hval2 ρ)
      · rw [Fin.cons_succ, Fin.fin_one_eq_zero j]
        have hle : w (binExtLocalSlot 1) ≤ g2 ρ := by
          rcases hbr with ⟨_, hlt⟩ | ⟨_, _, _, hy3⟩ <;> omega
        exact Nat.lt_of_le_of_lt hle (hval2 ρ)
  · intro ρ
    have := hval1 ρ
    have hdiv : g1 ρ / g2 ρ ≤ g1 ρ := Nat.div_le_self _ _
    simp only [diophDiv]
    omega

/-- Transport `Encodes` along an equality of encoded functions. -/
theorem DiophEnc.Encodes_congr {n : ℕ} {e : DiophEnc n} {g g' : (Fin n → ℕ) → ℕ}
    (h : g = g') (he : e.Encodes g) : e.Encodes g' := h ▸ he

/-- The constant-`1` combinator: the successor of the constant-zero encoding. -/
def diophOne {n : ℕ} : DiophEnc n := diophSucc diophZero

/-- The general-power combinator, encoding `fun ρ => g1 ρ ^ g2 ρ`. It is a
composition of existing combinators along Marchenkov's identity
`pow_eq_two_pow_mod`: writing `A := g1 * g2 + g1 + 1`, the power equals
`2 ^ (A * g2) % (2 ^ A - g1)`, assembled from `diophMul`, `diophAdd`, `diophOne`,
`diophPow2`, `diophTsub`, and `diophMod`. -/
def diophPow {n : ℕ} (sub1 sub2 : DiophEnc n) : DiophEnc n :=
  let A := diophAdd (diophAdd (diophMul sub1 sub2) sub1) diophOne
  diophMod (diophPow2 (diophMul A sub2)) (diophTsub (diophPow2 A) sub1)

/-- `diophPow sub1 sub2` encodes the pointwise power `fun ρ => g1 ρ ^ g2 ρ`,
via Marchenkov's identity `pow_eq_two_pow_mod`. -/
theorem diophPow_encodes {n : ℕ} {sub1 sub2 : DiophEnc n} {g1 g2 : (Fin n → ℕ) → ℕ}
    (h1 : sub1.Encodes g1) (h2 : sub2.Encodes g2) :
    (diophPow sub1 sub2).Encodes (fun ρ => g1 ρ ^ g2 ρ) := by
  have hA := diophAdd_encodes (diophAdd_encodes (diophMul_encodes h1 h2) h1)
    (diophSucc_encodes diophZero_encodes)
  have hbody := diophMod_encodes (diophPow2_encodes (diophMul_encodes hA h2))
    (diophTsub_encodes (diophPow2_encodes hA) h1)
  refine DiophEnc.Encodes_congr ?_ hbody
  funext ρ
  exact (pow_eq_two_pow_mod (g1 ρ) (g2 ρ)).symm

/-- The term-to-Diophantine reduction: structurally recurse over an `ETm n`,
dispatching each constructor to the matching combinator. The variable, zero, and
successor terms map to `diophVar`, `diophZero`, and `diophSucc`; each basis
application maps to the combinator for its operation, applied to the encodings of
its argument terms. -/
def diophOf {n : ℕ} : ETm n → DiophEnc n
  | .var i => diophVar i
  | .zero => diophZero
  | .succ s => diophSucc (diophOf s)
  | .app b ts => match b with
    | .add => diophAdd (diophOf (ts ⟨0, by decide⟩)) (diophOf (ts ⟨1, by decide⟩))
    | .mul => diophMul (diophOf (ts ⟨0, by decide⟩)) (diophOf (ts ⟨1, by decide⟩))
    | .pow2 => diophPow2 (diophOf (ts ⟨0, by decide⟩))
    | .tsub => diophTsub (diophOf (ts ⟨0, by decide⟩)) (diophOf (ts ⟨1, by decide⟩))
    | .div => diophDiv (diophOf (ts ⟨0, by decide⟩)) (diophOf (ts ⟨1, by decide⟩))
    | .mod => diophMod (diophOf (ts ⟨0, by decide⟩)) (diophOf (ts ⟨1, by decide⟩))
    | .pow => diophPow (diophOf (ts ⟨0, by decide⟩)) (diophOf (ts ⟨1, by decide⟩))

theorem diophOf_encodes {n : ℕ} (t : ETm n) :
    (diophOf t).Encodes (Tm.eval eraInterp t) := by
  induction t with
  | var i => exact diophVar_encodes i
  | zero => exact diophZero_encodes
  | succ s ih =>
    refine DiophEnc.Encodes_congr ?_ (diophSucc_encodes ih)
    rfl
  | app b ts ih =>
    cases b with
    | add =>
      refine DiophEnc.Encodes_congr ?_
        (diophAdd_encodes (ih ⟨0, by decide⟩) (ih ⟨1, by decide⟩))
      rfl
    | mul =>
      refine DiophEnc.Encodes_congr ?_
        (diophMul_encodes (ih ⟨0, by decide⟩) (ih ⟨1, by decide⟩))
      rfl
    | pow2 =>
      refine DiophEnc.Encodes_congr ?_ (diophPow2_encodes (ih ⟨0, by decide⟩))
      rfl
    | tsub =>
      refine DiophEnc.Encodes_congr ?_
        (diophTsub_encodes (ih ⟨0, by decide⟩) (ih ⟨1, by decide⟩))
      rfl
    | div =>
      refine DiophEnc.Encodes_congr ?_
        (diophDiv_encodes (ih ⟨0, by decide⟩) (ih ⟨1, by decide⟩))
      rfl
    | mod =>
      refine DiophEnc.Encodes_congr ?_
        (diophMod_encodes (ih ⟨0, by decide⟩) (ih ⟨1, by decide⟩))
      rfl
    | pow =>
      refine DiophEnc.Encodes_congr ?_
        (diophPow_encodes (ih ⟨0, by decide⟩) (ih ⟨1, by decide⟩))
      rfl

/-- Graph characterisation of the reduction: the sum-of-squares system of
`diophOf t` vanishes for some witness assignment at output `y` exactly when the
term `t` evaluates to `y` under `eraInterp`. -/
theorem diophOf_graph_iff {n : ℕ} (t : ETm n) (ρ : Fin n → ℕ) (y : ℕ) :
    (∃ w, SosSystem.eval (diophOf t).sys ((diophOf t).ctx ρ y w) = 0) ↔
      Tm.eval eraInterp t ρ = y := by
  obtain ⟨hsound, hcomplete, _, _⟩ := diophOf_encodes t
  constructor
  · rintro ⟨w, hw⟩
    exact (hsound ρ y w hw).symm
  · rintro rfl
    obtain ⟨w, hw, _⟩ := hcomplete ρ
    exact ⟨w, hw⟩

/-- Witness uniqueness of the reduction: at the correct output
`y = Tm.eval eraInterp t ρ` there is exactly one witness assignment making the
sum-of-squares system of `diophOf t` vanish. -/
theorem diophOf_unique {n : ℕ} (t : ETm n) (ρ : Fin n → ℕ) (y : ℕ)
    (hy : Tm.eval eraInterp t ρ = y) :
    ∃! w, SosSystem.eval (diophOf t).sys ((diophOf t).ctx ρ y w) = 0 := by
  obtain ⟨_, hcomplete, _, _⟩ := diophOf_encodes t
  rw [← hy]
  exact hcomplete ρ

/-- Witness boundedness of the reduction: every witness assignment making the
sum-of-squares system of `diophOf t` vanish has each component strictly below the
corresponding input-only bound term, evaluated at the inputs `ρ`. -/
theorem diophOf_bound {n : ℕ} (t : ETm n) (ρ : Fin n → ℕ) (y : ℕ)
    (w : Fin (diophOf t).witArity → ℕ)
    (hw : SosSystem.eval (diophOf t).sys ((diophOf t).ctx ρ y w) = 0) :
    ∀ i, w i < Tm.eval eraInterp ((diophOf t).bound i) ρ := by
  obtain ⟨_, _, hbound, _⟩ := diophOf_encodes t
  exact hbound ρ y w hw

end GebLean
