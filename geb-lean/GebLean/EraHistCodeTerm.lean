import GebLean.EraCompleteness
import GebLean.Utilities.EraHypercube
import GebLean.Utilities.EraRecurrence
import GebLean.Utilities.EraSepReduce

/-!
# The Section-4 count read-off as an `Era` term

This module realises the count read-off of arXiv:2407.12928 (Lemma 3.3 /
Theorem 3.4) — the number of cube points where a predicate vanishes equals
`HW(packM) / w − tᵏ` — as an `Era` arithmetic term. The read-off layer is
factored from the packed-witness construction: given a term `packMTerm`
whose value is the packed witness `packM` of arXiv:2407.12928, Lemma 3.3,
the combinator `eraCountOfPack packMTerm tTerm wTerm` evaluates to the count.

The packed witness `packM k w t P` is a sum over the side-`t` cube and so is
not itself an arithmetic term; the cube-sum factorisation of
arXiv:2407.12928, Lemma 3.2 (`GebLean.EraHypercube.cubeSum_factor`) is what
turns it into a closed term for a simple-exponential-polynomial predicate `P`
of per-coordinate degree at most `2`. That factorisation (the construction of
`packMTerm` from a degree-certified predicate) is a separate obligation; this
module supplies the read-off that consumes its output.

## Main definitions

* `eraCountOfPack` — the read-off term `(HW(packMTerm) / w) − tᵏ`, with `HW`
  the binary Hamming weight realised by `GebLean.EraCompleteness.eraSigma`.
* `ZMonomial.cubeConst`, `ZMonomial.cubeBase` — the parameter-only constant and
  the per-cube-coordinate geometric base of the separable normal form of a
  `ZMonomial (p + k)` whose cube coordinates are the last `k` slots, both
  evaluated at the cube-zero reference context `Fin.append ctx 0`.
* `packM_term` — the packed-witness term for the reduced system `sepReduce s`,
  assembled from `eraConstPart` and per-monomial `eraMonoTerm` contributions.
* `eraCount` — the count of vanishing reduced-predicate cube points as an `Era`
  term: `eraCountOfPack` applied to `packM_term` at cube width `k + (sepReduce s).1`.
* `eraConstPart`, `eraMonoTerm` — the constant part `C(ε, k)` (arXiv:2407.12928,
  Eq (7)) and the unsigned per-monomial cube-sum product `Aᵤ(m, k)` (Eq (8)) that
  assemble `packM_term`.
* `eraListProd`, `eraListSum` — the `*ᵉ`/`+ᵉ` folds of a list of `ETm` terms.
* `eraTheta`, `eraW`, `eraBaseBound` — the enlarged cube side (chain-witness
  bound), the modulus bound on the reduced predicate, and the uniform base side
  dominating every `diophOf` solution coordinate, all as `Era` terms.
* `reindexEmb`, `reindexCtx`, `reindexSys` — the slot-moving reconciliation taking
  a `diophOf` system's output-on-parameter-side layout to the cube-side `(p + k)`
  split that the count machinery consumes.
* `eraCountPred` — the public combinator: for a `diophOf`-encoded predicate `τ`, the
  `Era` term counting the assignments (output slot plus witnesses) at which the
  Diophantine system vanishes (arXiv:2407.12928, Corollary 3.6).

## Main statements

* `deltaBlock_affine` — on the cube bound `P < 2 ^ w`, the digit-block
  indicator is the affine form `δ(P, w) = (2^w − 1)(2^w + 1) − (2^w − 1) · P`,
  the form consumed by the cube-sum factorisation of `packM`.
* `one_le_packM` — the packed witness is positive when the cube is non-empty
  (`0 < t`) and the block bound holds, so its Hamming weight is its binary
  digit sum.
* `eraCountOfPack_eval` — the read-off identity: `eraCountOfPack` evaluates to
  the count of vanishing cube points, chaining `eraSigma_eval` (the Hamming
  weight) with `count_zeros_eq` (the read-off of arXiv:2407.12928, Lemma 3.3).
* `ZMonomial.cubeFactor` — the separable normal form: under the hypotheses that
  the coefficient and every exponential-coefficient evaluation are independent of
  the cube point, `evalNat (Fin.append ctx a)` factors as `cubeConst ctx` times
  `∏ c, (a c) ^ polyExp (natAdd p c) · (cubeBase ctx c) ^ (a c)`, the summand
  shape consumed by `GebLean.EraHypercube.cubeSum_factor` (arXiv:2407.12928,
  Lemma 3.2).
* `GebLean.EraHypercube.weight_mixedRadix_factor` — the base-`2 ^ (2 * w)`
  position weight factors over cube coordinates:
  `2 ^ (2 * w * mixedRadix k t a) = ∏ c, (2 ^ (2 * w * t ^ c)) ^ (a c)`.
* `ZMonomial.eraMonoCubeSum` — the weighted cube-sum of a single separable
  `ZMonomial`'s magnitude factors, via `GebLean.EraHypercube.cubeSum_factor`,
  into `cubeConst ctx` times a product over cube coordinates of per-coordinate
  inner geometric sums with bases `cubeBase ctx c · 2 ^ (2 * w * t ^ c)`
  (arXiv:2407.12928, Lemma 3.2).
* `packM_term_eval` — the packed-witness term evaluates to `packM` of the
  reduced predicate at the extended cube width (arXiv:2407.12928, Lemma 3.3).
* `eraCount_eval` — `eraCount` evaluates to the count of vanishing reduced-predicate
  cube points (arXiv:2407.12928, Lemma 3.3 / Cor 3.6).
* `eraConstPart_eval`, `eraMonoTerm_eval` — the constant part and the per-monomial
  term evaluate to their Eq (7)/Eq (8) weighted cube-sums.
* `eraTheta_spec`, `eraW_spec` — the chain witness `x c ^ (i + 1)` is below
  `eraTheta`, and the reduced predicate is below `2 ^ eraW`, so `eraW` discharges the
  block bound the count read-off requires.
* `reducedCount_eq` — the Lemma-3.5 fibre collapse: the enlarged-cube count of the
  reduced predicate equals the base-cube count of the original predicate (the unique
  chain witness makes each solution fibre a singleton, `sepReduce_sound`/`unique`).
* `predCount_side_eq` — the shell-empty bridge: under the solution-coordinate bound,
  the count at the enlarged side equals the count at the base side.
* `reindexSys_eval` — the reconciliation bridge: `reindexSys τ` evaluated at
  `Fin.append ctx a` equals `(diophOf τ).sys` evaluated at `reindexCtx τ ctx a`.
* `eraCountPred_eval` — `eraCountPred τ` evaluates to the count of vanishing
  (output slot plus witnesses) assignments of the `diophOf` system at the uniform
  base side (arXiv:2407.12928, Corollary 3.6 / Theorem 3.4).

## Implementation notes

The combinator is stated against a supplied packed-witness term `packMTerm`
together with the hypothesis that it evaluates to `packM`. The cube-sum
factorisation that constructs `packM_term` from a degree-≤2 simple exponential
polynomial predicate (arXiv:2407.12928, Eqs (7), (8)) is realised in this
module; `eraCount` chains the two layers.

## References

* M. Prunescu and L. Sauras-Altuzarra, *On the representation of
  number-theoretic functions by arithmetic terms*, arXiv:2407.12928,
  Lemma 3.2 (cube-sum factorisation), Lemma 3.3 / Theorem 3.4 (the count
  read-off), Eqs (7), (8) (the `δ` monomial expansion).
* Local copy:
  `/home/terence/wingeb/representation-number-theoretic-functions-arithmetic-terms.pdf`.

## Tags

elementary recursive, Diophantine, count, hypercube, arithmetic term
-/

namespace GebLean.EraHistCodeTerm

open Era
open GebLean.EraCompleteness
open GebLean.EraHypercube

/-- The digit-block indicator as an affine function of the predicate value on
the cube bound: for `0 < w` and `a < 2 ^ w`,
`δ(a, w) = (2^w − 1)(2^w + 1) − (2^w − 1) · a`. The truncated subtraction in
`deltaBlock` is exact under `a < 2 ^ w`, giving the affine form whose two
constant coefficients the cube-sum factorisation distributes over the
separable monomials of `a` (arXiv:2407.12928, Eqs (7), (8)). -/
theorem deltaBlock_affine {a w : ℕ} (ha : a < 2 ^ w) :
    GebLean.deltaBlock a w = (2 ^ w - 1) * (2 ^ w + 1) - (2 ^ w - 1) * a := by
  unfold GebLean.deltaBlock
  have hfac : 2 ^ w - a + 1 = (2 ^ w + 1) - a := by omega
  rw [hfac, Nat.mul_sub]

/-- The packed witness is positive when the cube is non-empty and every block
value fits, hence its binary digit sum is computed by the Hamming-weight
closed form `hwClosed`. -/
theorem one_le_packM {k w t : ℕ} (ht : 0 < t) (hw : 0 < w)
    (P : (Fin k → ℕ) → ℕ) (hP : ∀ a ∈ cubePoints k t, P a < 2 ^ w) :
    1 ≤ packM k w t P := by
  have hne : (cubePoints k t).Nonempty := by
    rw [← Finset.card_pos, card_cubePoints]
    exact Nat.pow_pos ht
  obtain ⟨a, ha⟩ := hne
  rw [packM]
  have hterm : 1 ≤ 2 ^ (2 * w * mixedRadix k t a) * GebLean.deltaBlock (P a) w := by
    have hd := (deltaBlock_pos_lt hw (hP a ha)).1
    have hpow : 0 < 2 ^ (2 * w * mixedRadix k t a) := Nat.pow_pos (by norm_num)
    exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hpow.ne' hd.ne')
  refine le_trans hterm ?_
  exact Finset.single_le_sum
    (f := fun a => 2 ^ (2 * w * mixedRadix k t a) * GebLean.deltaBlock (P a) w)
    (fun b _ => Nat.zero_le _) ha

/-- The natural-number literal `k` as an `Era` term over any scope: `k`
applications of `succ` to `zero`. -/
def eraNumeral {p : ℕ} : ℕ → ETm p
  | 0 => .zero
  | k + 1 => .succ (eraNumeral k)

/-- `eraNumeral k` evaluates to `k` in every context. -/
@[simp]
theorem eraNumeral_eval {p : ℕ} (k : ℕ) (ctx : Fin p → ℕ) :
    Tm.eval eraInterp (eraNumeral k) ctx = k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [eraNumeral, Tm.eval, ih]

/-- The Section-4 count read-off as an `Era` term, parameterised on a packed
witness term `packMTerm` (whose value is the packed witness `packM` of
arXiv:2407.12928, Lemma 3.3): `(HW(packMTerm) / w) − tᵏ`, with `HW` the binary
Hamming weight realised by `eraSigma` and `tᵏ` the cube cardinality. -/
def eraCountOfPack {p : ℕ} (k : ℕ) (packMTerm tTerm wTerm : ETm p) : ETm p :=
  etsub (ediv (eraSigma.subst ![packMTerm]) wTerm) (epow tTerm (eraNumeral k))

/-- The read-off identity (arXiv:2407.12928, Lemma 3.3 / Theorem 3.4):
`eraCountOfPack packMTerm tTerm wTerm` evaluates to the count of cube points
where `P` vanishes, provided `packMTerm` evaluates to the packed witness
`packM k w t P`, the cube is non-empty, the modulus is positive, and the block
bound holds on the cube. -/
theorem eraCountOfPack_eval {p : ℕ} (k : ℕ) (packMTerm tTerm wTerm : ETm p)
    (ctx : Fin p → ℕ) (P : (Fin k → ℕ) → ℕ)
    (ht : 0 < Tm.eval eraInterp tTerm ctx)
    (hw : 0 < Tm.eval eraInterp wTerm ctx)
    (hP : ∀ a ∈ cubePoints k (Tm.eval eraInterp tTerm ctx),
            P a < 2 ^ Tm.eval eraInterp wTerm ctx)
    (hpack : Tm.eval eraInterp packMTerm ctx =
      packM k (Tm.eval eraInterp wTerm ctx) (Tm.eval eraInterp tTerm ctx) P) :
    Tm.eval eraInterp (eraCountOfPack k packMTerm tTerm wTerm) ctx =
      ((cubePoints k (Tm.eval eraInterp tTerm ctx)).filter
        (fun a => P a = 0)).card := by
  set t := Tm.eval eraInterp tTerm ctx with ht_def
  set w := Tm.eval eraInterp wTerm ctx with hw_def
  have hpos : 1 ≤ packM k w t P := one_le_packM ht hw P hP
  have hsigma : Tm.eval eraInterp (eraSigma.subst ![packMTerm]) ctx =
      (Nat.digits 2 (packM k w t P)).sum := by
    rw [Tm.eval_subst]
    have hctx : (fun i => Tm.eval eraInterp (![packMTerm] i) ctx)
        = ![packM k w t P] := by
      funext i
      refine i.cases ?_ (fun j => j.elim0)
      simp only [Matrix.cons_val_zero, hpack]
    rw [hctx, eraSigma_eval _ hpos, GebLean.hwClosed_eq _ hpos]
  rw [eraCountOfPack]
  simp only [etsub_eval, ediv_eval, epow_eval, eraNumeral_eval, hsigma, ← ht_def, ← hw_def,
    eraInterp, fcons]
  rw [count_zeros_eq k w t hw P hP]

end GebLean.EraHistCodeTerm

namespace GebLean

open Era
open GebLean.EraHistCodeTerm (eraNumeral eraNumeral_eval)

/-- The parameter-only constant of the separable normal form of a
`ZMonomial (p + k)` whose cube coordinates are the last `k` slots: the
coefficient times the parameter-slot exponential and polynomial factors,
evaluated at the cube-zero reference context `Fin.append ctx 0`. Under the
separability hypotheses of `ZMonomial.cubeFactor` this value is independent of
the cube point. -/
def ZMonomial.cubeConst {p k : ℕ} (mon : ZMonomial (p + k)) (ctx : Fin p → ℕ) : ℕ :=
  Tm.eval eraInterp mon.coeff (Fin.append ctx (fun _ => 0))
    * (∏ i : Fin p, 2 ^ (Tm.eval eraInterp (mon.expCoeff (Fin.castAdd k i))
          (Fin.append ctx (fun _ => 0)) * ctx i))
    * (∏ i : Fin p, ctx i ^ mon.polyExp (Fin.castAdd k i))

/-- The per-cube-coordinate geometric base of the separable normal form of a
`ZMonomial (p + k)`: the base-`2` exponential at cube slot `c`, with the
exponential coefficient evaluated at the cube-zero reference context. Under the
separability hypotheses of `ZMonomial.cubeFactor` this value is independent of
the cube point, matching the fixed `vbase` vector of
`GebLean.EraHypercube.cubeSum_factor`. -/
def ZMonomial.cubeBase {p k : ℕ} (mon : ZMonomial (p + k)) (ctx : Fin p → ℕ)
    (c : Fin k) : ℕ :=
  2 ^ Tm.eval eraInterp (mon.expCoeff (Fin.natAdd p c)) (Fin.append ctx (fun _ => 0))

/-- Separable normal form of a `ZMonomial (p + k)` whose cube coordinates are the
last `k` slots (`Fin.natAdd p c`). Under the separability hypotheses that the
coefficient evaluation and every exponential-coefficient evaluation are
independent of the cube point, the natural-number magnitude factors as the
parameter-only constant `mon.cubeConst ctx` times the cube product
`∏ c, (a c) ^ polyExp (natAdd p c) · (mon.cubeBase ctx c) ^ (a c)`. This is the
summand shape consumed by `GebLean.EraHypercube.cubeSum_factor`, with
`u c = mon.polyExp (Fin.natAdd p c)` and `vbase c = mon.cubeBase ctx c`. -/
theorem ZMonomial.cubeFactor {p k : ℕ} (mon : ZMonomial (p + k)) (ctx : Fin p → ℕ)
    (hcoeff : ∀ a a', Tm.eval eraInterp mon.coeff (Fin.append ctx a)
        = Tm.eval eraInterp mon.coeff (Fin.append ctx a'))
    (hparamExp : ∀ (i : Fin p) (a a'), Tm.eval eraInterp (mon.expCoeff (Fin.castAdd k i))
          (Fin.append ctx a)
        = Tm.eval eraInterp (mon.expCoeff (Fin.castAdd k i)) (Fin.append ctx a'))
    (hcubeExp : ∀ (c : Fin k) (a a'), Tm.eval eraInterp (mon.expCoeff (Fin.natAdd p c))
          (Fin.append ctx a)
        = Tm.eval eraInterp (mon.expCoeff (Fin.natAdd p c)) (Fin.append ctx a'))
    (a : Fin k → ℕ) :
    mon.evalNat (Fin.append ctx a)
      = mon.cubeConst ctx * ∏ c : Fin k,
          (a c) ^ mon.polyExp (Fin.natAdd p c) * (mon.cubeBase ctx c) ^ (a c) := by
  rw [ZMonomial.evalNat, ZMonomial.cubeConst, Fin.prod_univ_add, Fin.prod_univ_add]
  simp only [Fin.append_left, Fin.append_right, ZMonomial.cubeBase]
  rw [hcoeff a (fun _ => 0)]
  have hparam : (∏ i : Fin p, 2 ^ (Tm.eval eraInterp (mon.expCoeff (Fin.castAdd k i))
        (Fin.append ctx a) * ctx i))
      = ∏ i : Fin p, 2 ^ (Tm.eval eraInterp (mon.expCoeff (Fin.castAdd k i))
        (Fin.append ctx (fun _ => 0)) * ctx i) :=
    Finset.prod_congr rfl (fun i _ => by rw [hparamExp i a (fun _ => 0)])
  have hcube : (∏ c : Fin k, 2 ^ (Tm.eval eraInterp (mon.expCoeff (Fin.natAdd p c))
        (Fin.append ctx a) * a c))
      = ∏ c : Fin k, (2 ^ Tm.eval eraInterp (mon.expCoeff (Fin.natAdd p c))
        (Fin.append ctx (fun _ => 0))) ^ (a c) :=
    Finset.prod_congr rfl (fun c _ => by rw [hcubeExp c a (fun _ => 0), pow_mul])
  rw [hparam, hcube, Finset.prod_mul_distrib]
  ring

/-- The base-`2 ^ (2 * w)` weight of a cube point factors over coordinates: the
`mixedRadix`-positioned weight `2 ^ (2 * w * mixedRadix k t a)` is the product
over cube coordinates `c` of `(2 ^ (2 * w * t ^ c)) ^ (a c)`. This distributes
the cube-sum weight into the per-coordinate geometric base
`2 ^ (2 * w * t ^ c)` consumed by `GebLean.EraHypercube.cubeSum_factor`. -/
theorem EraHypercube.weight_mixedRadix_factor (k w t : ℕ) (a : Fin k → ℕ) :
    2 ^ (2 * w * EraHypercube.mixedRadix k t a)
      = ∏ c : Fin k, (2 ^ (2 * w * t ^ (c : ℕ))) ^ (a c) := by
  rw [EraHypercube.mixedRadix, Finset.mul_sum, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl (fun c _ => ?_)
  rw [← pow_mul]
  ring_nf

/-- The weighted cube-sum of a single separable degree-`≤ 2` `ZMonomial`'s
magnitude factors, via `GebLean.EraHypercube.cubeSum_factor`, into the
parameter-only constant `mon.cubeConst ctx` times a product over cube
coordinates of per-coordinate inner geometric sums. The base-`2 ^ (2 * w)`
position weight `2 ^ (2 * w * mixedRadix k t a)` is absorbed into each
coordinate's geometric base, giving inner bases
`mon.cubeBase ctx c * 2 ^ (2 * w * t ^ c)` and inner exponents
`mon.polyExp (Fin.natAdd p c)`. This is the natural-number identity the term
realisation matches against the `Era` geometric-sum evaluation lemmas
(arXiv:2407.12928, Lemma 3.2). -/
theorem ZMonomial.eraMonoCubeSum {p k : ℕ} (mon : ZMonomial (p + k)) (ctx : Fin p → ℕ)
    (w t : ℕ)
    (hcoeff : ∀ a a', Tm.eval eraInterp mon.coeff (Fin.append ctx a)
        = Tm.eval eraInterp mon.coeff (Fin.append ctx a'))
    (hparamExp : ∀ (i : Fin p) (a a'), Tm.eval eraInterp (mon.expCoeff (Fin.castAdd k i))
          (Fin.append ctx a)
        = Tm.eval eraInterp (mon.expCoeff (Fin.castAdd k i)) (Fin.append ctx a'))
    (hcubeExp : ∀ (c : Fin k) (a a'), Tm.eval eraInterp (mon.expCoeff (Fin.natAdd p c))
          (Fin.append ctx a)
        = Tm.eval eraInterp (mon.expCoeff (Fin.natAdd p c)) (Fin.append ctx a')) :
    (∑ a ∈ GebLean.EraHypercube.cubePoints k t,
        2 ^ (2 * w * GebLean.EraHypercube.mixedRadix k t a)
          * mon.evalNat (Fin.append ctx a))
      = mon.cubeConst ctx
        * ∏ c : Fin k,
            (∑ j ∈ Finset.range t,
              j ^ mon.polyExp (Fin.natAdd p c)
                * (mon.cubeBase ctx c * 2 ^ (2 * w * t ^ (c : ℕ))) ^ j) := by
  -- substitute the weight factorisation and the monomial's separable normal form
  have hsummand : ∀ a ∈ GebLean.EraHypercube.cubePoints k t,
      2 ^ (2 * w * GebLean.EraHypercube.mixedRadix k t a) * mon.evalNat (Fin.append ctx a)
        = mon.cubeConst ctx
          * ∏ c : Fin k, (a c) ^ mon.polyExp (Fin.natAdd p c)
              * (mon.cubeBase ctx c * 2 ^ (2 * w * t ^ (c : ℕ))) ^ (a c) := by
    intro a _
    rw [EraHypercube.weight_mixedRadix_factor,
      mon.cubeFactor ctx hcoeff hparamExp hcubeExp a]
    rw [mul_comm, mul_assoc, ← Finset.prod_mul_distrib]
    refine congrArg (mon.cubeConst ctx * ·) (Finset.prod_congr rfl (fun c _ => ?_))
    rw [mul_pow]
    ring
  rw [Finset.sum_congr rfl hsummand, ← Finset.mul_sum]
  refine congrArg (mon.cubeConst ctx * ·) ?_
  exact GebLean.EraHypercube.cubeSum_factor k (fun c => mon.polyExp (Fin.natAdd p c))
    (fun c => mon.cubeBase ctx c * 2 ^ (2 * w * t ^ (c : ℕ))) t

open GebLean.EraCompleteness in
/-- A finite product of `Era` terms: the right fold of multiplication with unit
`Era.one`. Used with `List.ofFn` to realise `∏ c : Fin n` over an `Era`-term
family. -/
def eraListProd {p : ℕ} (L : List (ETm p)) : ETm p :=
  L.foldr (· *ᵉ ·) Era.one

/-- `eraListProd L` evaluates to the product of the evaluations of its factors. -/
theorem eraListProd_eval {p : ℕ} (L : List (ETm p)) (ctx : Fin p → ℕ) :
    Tm.eval eraInterp (eraListProd L) ctx
      = (L.map (fun e => Tm.eval eraInterp e ctx)).prod := by
  induction L with
  | nil => simp [eraListProd, Era.one, Tm.eval]
  | cons e L ih =>
    rw [eraListProd, List.foldr_cons]
    simp only [List.map_cons, List.prod_cons]
    rw [← ih, eraListProd, emul, Tm.eval, eraInterp]
    simp only [fcons]

open GebLean.EraCompleteness in
/-- A finite sum of `Era` terms: the right fold of addition with unit
`Era.zero`. The `+ᵉ` analogue of `eraListProd`, used with `List.map` to realise a
sum over an `Era`-term family. -/
def eraListSum {p : ℕ} (L : List (ETm p)) : ETm p :=
  L.foldr (· +ᵉ ·) .zero

/-- `eraListSum L` evaluates to the sum of the evaluations of its summands. -/
theorem eraListSum_eval {p : ℕ} (L : List (ETm p)) (ctx : Fin p → ℕ) :
    Tm.eval eraInterp (eraListSum L) ctx
      = (L.map (fun e => Tm.eval eraInterp e ctx)).sum := by
  induction L with
  | nil => simp [eraListSum, Tm.eval]
  | cons e L ih =>
    rw [eraListSum, List.foldr_cons]
    simp only [List.map_cons, List.sum_cons]
    rw [← ih, eraListSum, eadd, Tm.eval, eraInterp]
    simp only [fcons]

/-- Drop a cube-independent term to the parameter scope: substitute the `k`
cube slots by `.zero`, keeping the `p` parameter slots as variables. -/
def ETm.paramProject {p k : ℕ} (e : ETm (p + k)) : ETm p :=
  e.subst (fun j => Fin.addCases (fun i : Fin p => (.var i : ETm p))
    (fun _ : Fin k => .zero) j)

/-- For a term whose value at the parameter context is independent of the cube
point, `ETm.paramProject` evaluates to the original term's value at any cube
point (with the cube slots filled by `Fin.append ctx a`). -/
theorem ETm.paramProject_eval {p k : ℕ} (e : ETm (p + k)) (ctx : Fin p → ℕ)
    (hindep : ∀ a a', Tm.eval eraInterp e (Fin.append ctx a)
        = Tm.eval eraInterp e (Fin.append ctx a')) (a : Fin k → ℕ) :
    Tm.eval eraInterp (ETm.paramProject e) ctx
      = Tm.eval eraInterp e (Fin.append ctx a) := by
  rw [ETm.paramProject, Tm.eval_subst]
  have htuple : (fun j => Tm.eval eraInterp
      (Fin.addCases (fun i : Fin p => (.var i : ETm p)) (fun _ : Fin k => .zero) j) ctx)
      = Fin.append ctx (fun _ => 0) := by
    funext j
    refine Fin.addCases (fun i => ?_) (fun c => ?_) j
    · rw [Fin.addCases_left, Fin.append_left, Tm.eval]
    · rw [Fin.addCases_right, Fin.append_right, Tm.eval]
  rw [htuple, hindep (fun _ => 0) a]

open GebLean.EraCompleteness in
/-- The parameter-only constant `mon.cubeConst` realised as an `ETm p`: the
projected coefficient times the parameter-slot exponential and polynomial
products (arXiv:2407.12928, Eq (8), the `α` factor). -/
def cubeConstTerm {p k : ℕ} (mon : ZMonomial (p + k)) : ETm p :=
  ETm.paramProject mon.coeff
    *ᵉ eraListProd (List.ofFn (fun i : Fin p =>
        eraNumeral 2 ^ᵉ (ETm.paramProject (mon.expCoeff (Fin.castAdd k i)) *ᵉ .var i)))
    *ᵉ eraListProd (List.ofFn (fun i : Fin p =>
        (.var i : ETm p) ^ᵉ eraNumeral (mon.polyExp (Fin.castAdd k i))))

open GebLean.EraCompleteness in
/-- The per-cube-coordinate geometric base `mon.cubeBase` (without the position
weight) realised as an `ETm p`: the base-`2` exponential whose exponent is the
projected cube-slot exponential coefficient (arXiv:2407.12928, Eq (8), the
`vbase` factor). -/
def cubeBaseTerm {p k : ℕ} (mon : ZMonomial (p + k)) (c : Fin k) : ETm p :=
  eraNumeral 2 ^ᵉ ETm.paramProject (mon.expCoeff (Fin.natAdd p c))

open GebLean.EraCompleteness in
/-- `cubeConstTerm mon` evaluates to `mon.cubeConst ctx`, given that the
coefficient and every parameter-slot exponential coefficient are independent of
the cube point. -/
theorem cubeConstTerm_eval {p k : ℕ} (mon : ZMonomial (p + k)) (ctx : Fin p → ℕ)
    (hcoeff : ∀ a a', Tm.eval eraInterp mon.coeff (Fin.append ctx a)
        = Tm.eval eraInterp mon.coeff (Fin.append ctx a'))
    (hparamExp : ∀ (i : Fin p) (a a'),
        Tm.eval eraInterp (mon.expCoeff (Fin.castAdd k i)) (Fin.append ctx a)
          = Tm.eval eraInterp (mon.expCoeff (Fin.castAdd k i)) (Fin.append ctx a')) :
    Tm.eval eraInterp (cubeConstTerm mon) ctx = mon.cubeConst ctx := by
  rw [cubeConstTerm, ZMonomial.cubeConst]
  simp only [emul, Tm.eval, eraInterp, fcons]
  rw [eraListProd_eval, eraListProd_eval]
  simp only [List.map_ofFn, Function.comp_def]
  rw [List.prod_ofFn, List.prod_ofFn]
  rw [ETm.paramProject_eval mon.coeff ctx hcoeff (fun _ => 0)]
  congr 1
  · congr 1
    refine Finset.prod_congr rfl (fun i _ => ?_)
    simp only [epow, Tm.eval, eraInterp, fcons]
    rw [eraNumeral_eval, ETm.paramProject_eval _ ctx (hparamExp i) (fun _ => 0)]
  · refine Finset.prod_congr rfl (fun i _ => ?_)
    simp only [epow, Tm.eval, eraInterp, fcons]
    rw [eraNumeral_eval]

open GebLean.EraCompleteness in
/-- `cubeBaseTerm mon c` evaluates to `mon.cubeBase ctx c`, given that the
cube-slot exponential coefficient at `c` is independent of the cube point. -/
theorem cubeBaseTerm_eval {p k : ℕ} (mon : ZMonomial (p + k)) (ctx : Fin p → ℕ)
    (hcubeExp : ∀ (c : Fin k) (a a'),
        Tm.eval eraInterp (mon.expCoeff (Fin.natAdd p c)) (Fin.append ctx a)
          = Tm.eval eraInterp (mon.expCoeff (Fin.natAdd p c)) (Fin.append ctx a'))
    (c : Fin k) :
    Tm.eval eraInterp (cubeBaseTerm mon c) ctx = mon.cubeBase ctx c := by
  rw [cubeBaseTerm, ZMonomial.cubeBase]
  simp only [epow, Tm.eval, eraInterp, fcons]
  rw [eraNumeral_eval, ETm.paramProject_eval _ ctx (hcubeExp c) (fun _ => 0)]

open GebLean.EraCompleteness in
/-- The weighted cube base of coordinate `c` as an `ETm p`:
`mon.cubeBase ctx c · 2 ^ (2 · w · t ^ c)`, the geometric-sum base of the
`c`-th inner sum (arXiv:2407.12928, Eq (8)). -/
def cubeWeightedBaseTerm {p k : ℕ} (mon : ZMonomial (p + k)) (tTerm wTerm : ETm p)
    (c : Fin k) : ETm p :=
  cubeBaseTerm mon c
    *ᵉ eraNumeral 2 ^ᵉ (eraNumeral 2 *ᵉ wTerm *ᵉ tTerm ^ᵉ eraNumeral (c : ℕ))

open GebLean.EraCompleteness in
/-- The `c`-th inner geometric-sum factor of `eraMonoTerm`, selected by the
cube-coordinate polynomial exponent `mon.polyExp (Fin.natAdd p c)`: the
unweighted (`u = 0`), linear (`u = 1`), or square-weighted (`u = 2`, also the
fallback) geometric sum over the weighted base, realised by substituting the
weighted base and the bound `tTerm` into `eraGeomSum`/`eraLinGeomSum`/
`eraSqGeomSum` (arXiv:2407.12928, Eq (8), the inner sums `G_u`). -/
def eraGFactor {p k : ℕ} (mon : ZMonomial (p + k)) (tTerm wTerm : ETm p)
    (c : Fin k) : ETm p :=
  match mon.polyExp (Fin.natAdd p c) with
  | 0 => eraGeomSum.subst ![cubeWeightedBaseTerm mon tTerm wTerm c, tTerm]
  | 1 => eraLinGeomSum.subst ![cubeWeightedBaseTerm mon tTerm wTerm c, tTerm]
  | _ => eraSqGeomSum.subst ![cubeWeightedBaseTerm mon tTerm wTerm c, tTerm]

open GebLean.EraCompleteness in
/-- The unsigned per-monomial term `Aᵤ(m,k) = α · ∏_c G_{u_c}(vbase_c, t)` of
arXiv:2407.12928, Eq (8): the parameter-only constant `cubeConstTerm mon` times
the product over cube coordinates of the inner geometric-sum factors
`eraGFactor`. Its evaluation is the weighted cube-sum of `mon` over the side-`t`
cube (Cor 3.6). -/
def eraMonoTerm {p k : ℕ} (mon : ZMonomial (p + k)) (tTerm wTerm : ETm p) : ETm p :=
  cubeConstTerm mon
    *ᵉ eraListProd (List.ofFn (fun c : Fin k => eraGFactor mon tTerm wTerm c))

open GebLean.EraCompleteness in
/-- `cubeWeightedBaseTerm mon tTerm wTerm c` evaluates to the weighted geometric
base `mon.cubeBase ctx c · 2 ^ (2 · w · t ^ c)`, given that the cube-slot
exponential coefficient at `c` is independent of the cube point. -/
theorem cubeWeightedBaseTerm_eval {p k : ℕ} (mon : ZMonomial (p + k)) (ctx : Fin p → ℕ)
    (tTerm wTerm : ETm p)
    (hcubeExp : ∀ (c : Fin k) (a a'),
        Tm.eval eraInterp (mon.expCoeff (Fin.natAdd p c)) (Fin.append ctx a)
          = Tm.eval eraInterp (mon.expCoeff (Fin.natAdd p c)) (Fin.append ctx a'))
    (c : Fin k) :
    Tm.eval eraInterp (cubeWeightedBaseTerm mon tTerm wTerm c) ctx
      = mon.cubeBase ctx c
        * 2 ^ (2 * Tm.eval eraInterp wTerm ctx
            * Tm.eval eraInterp tTerm ctx ^ (c : ℕ)) := by
  rw [cubeWeightedBaseTerm]
  simp only [epow, emul, Tm.eval, eraInterp, fcons, eraNumeral_eval]
  rw [cubeBaseTerm_eval mon ctx hcubeExp c]

open GebLean.EraCompleteness in
/-- Positivity of the weighted geometric base: at least `2` when the bound `t`
and modulus `w` are positive, so the `Era` geometric-sum evaluation lemmas
apply. -/
theorem two_le_cubeWeightedBase {p k : ℕ} (mon : ZMonomial (p + k)) (ctx : Fin p → ℕ)
    (tTerm wTerm : ETm p) (ht : 0 < Tm.eval eraInterp tTerm ctx)
    (hw : 0 < Tm.eval eraInterp wTerm ctx) (c : Fin k) :
    2 ≤ mon.cubeBase ctx c
      * 2 ^ (2 * Tm.eval eraInterp wTerm ctx
          * Tm.eval eraInterp tTerm ctx ^ (c : ℕ)) := by
  set t := Tm.eval eraInterp tTerm ctx
  set w := Tm.eval eraInterp wTerm ctx
  have hbase : 1 ≤ mon.cubeBase ctx c := by
    rw [ZMonomial.cubeBase]
    exact Nat.one_le_two_pow
  have hexp : 1 ≤ 2 * w * t ^ (c : ℕ) := by
    have : 0 < t ^ (c : ℕ) := Nat.pow_pos ht
    calc 1 ≤ 2 * w := by omega
      _ ≤ 2 * w * t ^ (c : ℕ) := Nat.le_mul_of_pos_right _ this
  calc 2 = 1 * 2 ^ 1 := by norm_num
    _ ≤ mon.cubeBase ctx c * 2 ^ (2 * w * t ^ (c : ℕ)) :=
      Nat.mul_le_mul hbase (Nat.pow_le_pow_right (by norm_num) hexp)

open GebLean.EraCompleteness in
/-- The `c`-th geometric-sum factor evaluates to the `c`-th inner sum of the
cube-sum factorisation: `∑ j ∈ range t, j ^ (polyExp) · (weighted base) ^ j`,
for cube-coordinate degree at most `2` and positive bound and modulus
(arXiv:2407.12928, Eq (8), the inner sums `G_u`). -/
theorem eraGFactor_eval {p k : ℕ} (mon : ZMonomial (p + k)) (ctx : Fin p → ℕ)
    (tTerm wTerm : ETm p) (c : Fin k) (hdeg : mon.polyExp (Fin.natAdd p c) ≤ 2)
    (hcubeExp : ∀ (c : Fin k) (a a'),
        Tm.eval eraInterp (mon.expCoeff (Fin.natAdd p c)) (Fin.append ctx a)
          = Tm.eval eraInterp (mon.expCoeff (Fin.natAdd p c)) (Fin.append ctx a'))
    (ht : 0 < Tm.eval eraInterp tTerm ctx) (hw : 0 < Tm.eval eraInterp wTerm ctx) :
    Tm.eval eraInterp (eraGFactor mon tTerm wTerm c) ctx
      = ∑ j ∈ Finset.range (Tm.eval eraInterp tTerm ctx),
          j ^ mon.polyExp (Fin.natAdd p c)
            * (mon.cubeBase ctx c
                * 2 ^ (2 * Tm.eval eraInterp wTerm ctx
                    * Tm.eval eraInterp tTerm ctx ^ (c : ℕ))) ^ j := by
  set t := Tm.eval eraInterp tTerm ctx with ht_def
  set V := mon.cubeBase ctx c
    * 2 ^ (2 * Tm.eval eraInterp wTerm ctx * t ^ (c : ℕ)) with hV_def
  have hV2 : 2 ≤ V := two_le_cubeWeightedBase mon ctx tTerm wTerm ht hw c
  have hVeval : Tm.eval eraInterp (cubeWeightedBaseTerm mon tTerm wTerm c) ctx = V :=
    cubeWeightedBaseTerm_eval mon ctx tTerm wTerm hcubeExp c
  have hsub : ∀ (e : ETm 2),
      Tm.eval eraInterp (e.subst ![cubeWeightedBaseTerm mon tTerm wTerm c, tTerm]) ctx
        = Tm.eval eraInterp e ![V, t] := by
    intro e
    rw [Tm.eval_subst]
    congr 1
    funext i
    refine i.cases ?_ (fun j => ?_)
    · simpa using hVeval
    · refine j.cases ?_ (fun l => l.elim0)
      simp [ht_def]
  -- branch on the cube-coordinate polynomial exponent (degree ≤ 2)
  have hcases : mon.polyExp (Fin.natAdd p c) = 0 ∨ mon.polyExp (Fin.natAdd p c) = 1
      ∨ mon.polyExp (Fin.natAdd p c) = 2 := by omega
  rcases hcases with hu | hu | hu
  · rw [eraGFactor, hu]
    rw [hsub eraGeomSum, eraGeomSum_natBSum V t hV2, natBSum_eq_sum]
    simp only [pow_zero, one_mul]
  · rw [eraGFactor, hu]
    rw [hsub eraLinGeomSum, eraLinGeomSum_eval V t hV2]
    simp only [pow_one]
  · rw [eraGFactor, hu]
    rw [hsub eraSqGeomSum, eraSqGeomSum_eval V t hV2]

open GebLean.EraCompleteness in
/-- The unsigned per-monomial term evaluates to the weighted cube-sum of the
monomial's magnitude over the side-`t` cube (arXiv:2407.12928, Cor 3.6,
Eq (8)). The hypotheses are the cube-coordinate degree bound (`hdeg`), the three
separability conjuncts of `EraSepReduce.sepReduce_separable` (`hcoeff`,
`hparamExp`, `hcubeExp`), and positivity of the bound and modulus (`ht`, `hw`);
they are the discharge-ready forms a `sepReduce`/`cubeRegroup` instantiation
supplies. -/
theorem eraMonoTerm_eval {p k : ℕ} (mon : ZMonomial (p + k)) (tTerm wTerm : ETm p)
    (ctx : Fin p → ℕ) (hdeg : ∀ i, mon.polyExp i ≤ 2)
    (hcoeff : ∀ a a', Tm.eval eraInterp mon.coeff (Fin.append ctx a)
        = Tm.eval eraInterp mon.coeff (Fin.append ctx a'))
    (hparamExp : ∀ (i : Fin p) (a a'),
        Tm.eval eraInterp (mon.expCoeff (Fin.castAdd k i)) (Fin.append ctx a)
          = Tm.eval eraInterp (mon.expCoeff (Fin.castAdd k i)) (Fin.append ctx a'))
    (hcubeExp : ∀ (c : Fin k) (a a'),
        Tm.eval eraInterp (mon.expCoeff (Fin.natAdd p c)) (Fin.append ctx a)
          = Tm.eval eraInterp (mon.expCoeff (Fin.natAdd p c)) (Fin.append ctx a'))
    (ht : 0 < Tm.eval eraInterp tTerm ctx) (hw : 0 < Tm.eval eraInterp wTerm ctx) :
    Tm.eval eraInterp (eraMonoTerm mon tTerm wTerm) ctx
      = ∑ a ∈ GebLean.EraHypercube.cubePoints k (Tm.eval eraInterp tTerm ctx),
          2 ^ (2 * Tm.eval eraInterp wTerm ctx
              * GebLean.EraHypercube.mixedRadix k (Tm.eval eraInterp tTerm ctx) a)
            * mon.evalNat (Fin.append ctx a) := by
  rw [mon.eraMonoCubeSum ctx (Tm.eval eraInterp wTerm ctx) (Tm.eval eraInterp tTerm ctx)
    hcoeff hparamExp hcubeExp]
  rw [eraMonoTerm, emul, Tm.eval, eraInterp]
  simp only [fcons]
  rw [cubeConstTerm_eval mon ctx hcoeff hparamExp, eraListProd_eval]
  simp only [List.map_ofFn, Function.comp_def]
  rw [List.prod_ofFn]
  refine congrArg (mon.cubeConst ctx * ·) (Finset.prod_congr rfl (fun c _ => ?_))
  exact eraGFactor_eval mon ctx tTerm wTerm c (hdeg _) hcubeExp ht hw

open GebLean.EraCompleteness in
/-- The unit `ZMonomial (p + k)`: coefficient `Era.one`, all exponential
coefficients `.zero`, all polynomial exponents `0`. Its magnitude is the constant
`1` at every context, so its weighted cube-sum is the bare position-weight sum
`∑_a 2 ^ (2 · w · v(a))` — the geometric factor of the Eq (7) constant
(arXiv:2407.12928, Eq (7)). -/
def unitCubeMon (p k : ℕ) : ZMonomial (p + k) where
  sign := false
  coeff := Era.one
  expCoeff := fun _ => .zero
  polyExp := fun _ => 0

/-- The unit monomial's magnitude is `1` at every context. -/
theorem unitCubeMon_evalNat (p k : ℕ) (ρ : Fin (p + k) → ℕ) :
    (unitCubeMon p k).evalNat ρ = 1 := by
  simp only [ZMonomial.evalNat, unitCubeMon, Era.one, Tm.eval, Nat.zero_mul, pow_zero,
    Finset.prod_const_one, mul_one, Nat.zero_add]

open GebLean.EraCompleteness in
/-- The constant part `C(ε, k)` of the packed witness (arXiv:2407.12928, Eq (7)):
`(2^w − 1) · (2^w − ε + 1) · ∑_a 2 ^ (2 · w · v(a))`, with the geometric factor
`∑_a 2 ^ (2 · w · v(a))` realised by `eraMonoTerm` on the unit monomial. The two
`a`-independent affine factors come from splitting the constant `ε` off the
`δ`-affine form `(2^w − 1)(2^w + 1) − (2^w − 1)·P` of `deltaBlock_affine`. -/
def eraConstPart {p : ℕ} (epsTerm tTerm wTerm : ETm p) (k : ℕ) : ETm p :=
  ((eraNumeral 2 ^ᵉ wTerm) ∸ᵉ eraNumeral 1)
    *ᵉ (((eraNumeral 2 ^ᵉ wTerm) ∸ᵉ epsTerm) +ᵉ eraNumeral 1)
    *ᵉ eraMonoTerm (unitCubeMon p k) tTerm wTerm

open GebLean.EraCompleteness in
/-- `eraConstPart` evaluates to the Eq (7) constant `C(ε, k)` distributed over the
side-`t` cube: `∑_a 2 ^ (2 · w · v(a)) · (2^w − 1) · (2^w − ε + 1)`
(arXiv:2407.12928, Eq (7)). The two affine factors are `a`-independent, so they
distribute into the cube-sum. The identity holds for the truncated subtraction
`2^w − ε` unconditionally; the `ε ≤ 2^w` bound that makes this subtraction exact
is supplied by the consumers in the packed-witness assembly (arXiv:2407.12928,
Lemma 3.3), not needed here. -/
theorem eraConstPart_eval {p : ℕ} (epsTerm tTerm wTerm : ETm p) (k : ℕ)
    (ctx : Fin p → ℕ) (ht : 0 < Tm.eval eraInterp tTerm ctx)
    (hw : 0 < Tm.eval eraInterp wTerm ctx) :
    Tm.eval eraInterp (eraConstPart epsTerm tTerm wTerm k) ctx
      = ∑ a ∈ GebLean.EraHypercube.cubePoints k (Tm.eval eraInterp tTerm ctx),
          2 ^ (2 * Tm.eval eraInterp wTerm ctx
                * GebLean.EraHypercube.mixedRadix k (Tm.eval eraInterp tTerm ctx) a)
            * (2 ^ Tm.eval eraInterp wTerm ctx - 1)
            * (2 ^ Tm.eval eraInterp wTerm ctx - Tm.eval eraInterp epsTerm ctx + 1) := by
  set w := Tm.eval eraInterp wTerm ctx with hw_def
  set eps := Tm.eval eraInterp epsTerm ctx with heps_def
  have hmono : Tm.eval eraInterp (eraMonoTerm (unitCubeMon p k) tTerm wTerm) ctx
      = ∑ a ∈ GebLean.EraHypercube.cubePoints k (Tm.eval eraInterp tTerm ctx),
          2 ^ (2 * w * GebLean.EraHypercube.mixedRadix k (Tm.eval eraInterp tTerm ctx) a) := by
    rw [eraMonoTerm_eval (unitCubeMon p k) tTerm wTerm ctx
      (fun _ => Nat.zero_le _) (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl) ht hw]
    exact Finset.sum_congr rfl (fun a _ => by rw [unitCubeMon_evalNat]; ring)
  rw [eraConstPart]
  simp only [emul, epow, etsub, eadd, Tm.eval, eraInterp, fcons, eraNumeral_eval,
    ← hw_def, ← heps_def]
  rw [hmono, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun a _ => by ring)

/-- The reduced-system eval-sum over the regrouped monomials at a cube point is
non-negative: by `ZMonomial.cubeRegroup_eval` it equals the native reduced
eval-sum at a re-associated context, which `sepReduce_eval_split` exhibits as a
sum of squares of integers. -/
theorem reducedCubeEval_nonneg {p k : ℕ} (s : SosSystem (p + k)) (ctx : Fin p → ℕ)
    (a : Fin (k + (sepReduce s).1) → ℕ) :
    0 ≤ (((sepReduce s).2).map
        (fun mon => mon.cubeRegroup.eval (Fin.append ctx a))).sum := by
  have hcongr : (((sepReduce s).2).map
      (fun mon => mon.cubeRegroup.eval (Fin.append ctx a))).sum
      = (((sepReduce s).2).map (fun mon => mon.eval
        (Fin.append ctx a ∘ finCongr (Nat.add_assoc p k (sepReduce s).1)))).sum := by
    refine congrArg List.sum (List.map_congr_left (fun mon _ => ?_))
    exact ZMonomial.cubeRegroup_eval mon (Fin.append ctx a)
  rw [hcongr, sepReduce_eval_split]
  exact add_nonneg
    (List.sum_nonneg (fun x hx => by
      obtain ⟨c, _, rfl⟩ := List.mem_map.mp hx
      exact List.sum_nonneg (fun y hy => by
        obtain ⟨i, _, rfl⟩ := List.mem_map.mp hy
        exact sq_nonneg _)))
    (sq_nonneg _)

/-- The reduced-system eval-sum over the regrouped monomials at a cube point
equals the cast of its `toNat`, since the sum is non-negative
(`reducedCubeEval_nonneg`). This is the integer/natural bridge for the cube
predicate `P a` (arXiv:2407.12928, Lemma 3.3). -/
theorem reducedCubeEval {p k : ℕ} (s : SosSystem (p + k)) (ctx : Fin p → ℕ)
    (a : Fin (k + (sepReduce s).1) → ℕ) :
    (((sepReduce s).2).map
        (fun mon => mon.cubeRegroup.eval (Fin.append ctx a))).sum
      = ((((((sepReduce s).2).map
          (fun (mon : ZMonomial (p + k + (sepReduce s).1)) =>
            mon.cubeRegroup.eval (Fin.append ctx a))).sum).toNat : ℕ) : ℤ) :=
  (Int.toNat_of_nonneg (reducedCubeEval_nonneg s ctx a)).symm

/-- The signed-eval weighted cube-sum of a single regrouped monomial: the
weighted cube-sum of its `ℤ`-valued `eval` equals its sign factor times the
weighted cube-sum of its `ℕ`-valued magnitude, by `ZMonomial.eval_eq`. -/
theorem weightedSignedMonoSum {p K : ℕ} (mon : ZMonomial (p + K)) (ctx : Fin p → ℕ)
    (w t : ℕ) :
    (∑ a ∈ GebLean.EraHypercube.cubePoints K t,
        (2 : ℤ) ^ (2 * w * GebLean.EraHypercube.mixedRadix K t a)
          * mon.eval (Fin.append ctx a))
      = (if mon.sign then -1 else 1)
        * ∑ a ∈ GebLean.EraHypercube.cubePoints K t,
            (2 : ℤ) ^ (2 * w * GebLean.EraHypercube.mixedRadix K t a)
              * (mon.evalNat (Fin.append ctx a) : ℤ) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [ZMonomial.eval_eq]
  split <;> ring

/-- Interchange a `Finset.sum` with a `List.sum` of mapped summands: summing a
list-sum of `a`-indexed summands over a finite index set equals the list-sum of
the per-element index-sums. Proved by induction on the list, distributing the
`Finset.sum` over each `List.sum_cons` by `Finset.sum_add_distrib`. -/
theorem sum_list_map_comm {α β : Type*} [AddCommMonoid β] {ι : Type*}
    (s : Finset ι) (L : List α) (g : ι → α → β) :
    (∑ i ∈ s, (L.map (fun x => g i x)).sum)
      = (L.map (fun x => ∑ i ∈ s, g i x)).sum := by
  induction L with
  | nil => simp only [List.map_nil, List.sum_nil, Finset.sum_const_zero]
  | cons x L ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [Finset.sum_add_distrib, ih]

/-- Split a signed `List.sum` by a `Bool` flag: the sum of `σ(x) · M x` with
`σ(x) = if flag x then -1 else 1` is the unsigned sum over the flag-`false`
sublist minus the unsigned sum over the flag-`true` sublist. Proved by induction,
peeling each head into the matching filtered sublist. -/
theorem signPartition_sum {α : Type*} (L : List α) (flag : α → Bool) (M : α → ℤ) :
    (L.map (fun x => (if flag x then -1 else 1) * M x)).sum
      = ((L.filter (fun x => !flag x)).map M).sum
        - ((L.filter (fun x => flag x)).map M).sum := by
  induction L with
  | nil => simp only [List.map_nil, List.sum_nil, List.filter_nil, sub_zero]
  | cons x L ih =>
    rw [List.map_cons, List.sum_cons, ih]
    cases hx : flag x <;>
      simp only [hx, List.filter_cons, Bool.not_false, Bool.not_true, if_true, if_false,
        Bool.false_eq_true, List.map_cons, List.sum_cons] <;> ring

/-- The load-bearing bridge (arXiv:2407.12928, Lemma 3.3, the `Σⱼ A(mⱼ,k)`
sum): the weighted cube-sum of the reduced predicate `P a` equals the signed
list-sum, over the regrouped reduced monomials, of each monomial's weighted
magnitude cube-sum. The predicate `P a` is `(Σ_{mon} mon.cubeRegroup.eval (append
ctx a)).toNat`; `reducedCubeEval` re-casts it to the `ℤ`-valued eval-sum,
`sum_list_map_comm` swaps the cube-`Finset.sum` past the monomial
`List.sum`, and `weightedSignedMonoSum` splits each monomial's signed eval into
sign factor times magnitude sum. -/
theorem packM_signed_sum {p k : ℕ} (s : SosSystem (p + k)) (ctx : Fin p → ℕ)
    (w t : ℕ) :
    (∑ a ∈ GebLean.EraHypercube.cubePoints (k + (sepReduce s).1) t,
        (2 : ℤ) ^ (2 * w * GebLean.EraHypercube.mixedRadix (k + (sepReduce s).1) t a)
          * ((((sepReduce s).2).map
              (fun (mon : ZMonomial (p + k + (sepReduce s).1)) =>
                mon.cubeRegroup.eval (Fin.append ctx a))).sum.toNat : ℤ))
      = (((sepReduce s).2.map ZMonomial.cubeRegroup).map (fun mon =>
          (if mon.sign then -1 else 1)
            * ∑ a ∈ GebLean.EraHypercube.cubePoints (k + (sepReduce s).1) t,
                (2 : ℤ) ^ (2 * w
                    * GebLean.EraHypercube.mixedRadix (k + (sepReduce s).1) t a)
                  * (mon.evalNat (Fin.append ctx a) : ℤ))).sum := by
  -- per cube point: recast `P a` and distribute the weight into the list-sum
  have hpt : ∀ a, (2 : ℤ) ^ (2 * w
        * GebLean.EraHypercube.mixedRadix (k + (sepReduce s).1) t a)
      * ((((sepReduce s).2).map
          (fun (mon : ZMonomial (p + k + (sepReduce s).1)) =>
            mon.cubeRegroup.eval (Fin.append ctx a))).sum.toNat : ℤ)
      = (((sepReduce s).2.map ZMonomial.cubeRegroup).map
          (fun mon => (2 : ℤ) ^ (2 * w
              * GebLean.EraHypercube.mixedRadix (k + (sepReduce s).1) t a)
            * mon.eval (Fin.append ctx a))).sum := by
    intro a
    rw [← reducedCubeEval s ctx a, List.map_map, ← List.sum_map_mul_left]
    simp only [Function.comp_def]
  rw [Finset.sum_congr rfl (fun a _ => hpt a), sum_list_map_comm]
  refine congrArg List.sum (List.map_congr_left (fun mon _ => ?_))
  exact weightedSignedMonoSum mon ctx w t

/-- The packed witness as an integer affine combination of the weighted cube-sum
of the predicate (arXiv:2407.12928, Eqs (7), (8)): under the block bound,
`deltaBlock_affine` turns each block into `(2^w − 1)(2^w + 1) − (2^w − 1)·P a`,
and distributing the `Finset.sum` over ℤ gives the constant cube-sum minus the
`(2^w − 1)`-weighted predicate cube-sum. -/
theorem packM_affine_int {K w t : ℕ} (P : (Fin K → ℕ) → ℕ) (hw : 0 < w)
    (hP : ∀ a ∈ GebLean.EraHypercube.cubePoints K t, P a < 2 ^ w) :
    (GebLean.EraHypercube.packM K w t P : ℤ)
      = (∑ a ∈ GebLean.EraHypercube.cubePoints K t,
          (2 : ℤ) ^ (2 * w * GebLean.EraHypercube.mixedRadix K t a)
            * ((2 ^ w - 1) * (2 ^ w + 1)))
        - (2 ^ w - 1) * ∑ a ∈ GebLean.EraHypercube.cubePoints K t,
            (2 : ℤ) ^ (2 * w * GebLean.EraHypercube.mixedRadix K t a) * (P a : ℤ) := by
  rw [GebLean.EraHypercube.packM, Nat.cast_sum]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun a ha => ?_)
  have hbound : P a < 2 ^ w := hP a ha
  rw [Nat.cast_mul, GebLean.EraHistCodeTerm.deltaBlock_affine hbound, Nat.cast_sub (by
    have h1 : (2 : ℕ) ^ w - 1 ≥ 1 := by
      have : (2 : ℕ) ≤ 2 ^ w := by
        calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
          _ ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) hw
      omega
    have hle : (2 ^ w - 1) * P a ≤ (2 ^ w - 1) * (2 ^ w + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    exact hle)]
  have h2w : (1 : ℕ) ≤ 2 ^ w := Nat.one_le_two_pow
  push_cast [Nat.cast_sub h2w]
  ring

open GebLean.EraCompleteness in
/-- The packed-witness term for the reduced system `sepReduce s`
(arXiv:2407.12928, Lemma 3.3, Eqs (7), (8)): with uniform `ε = 0`, the constant
part `C(0, k)` plus the `(2^w − 1)`-weighted sum of the negative-sign regrouped
reduced monomials' per-monomial terms, minus the `(2^w − 1)`-weighted sum of the
positive-sign ones. The regrouped reduced monomials are
`(sepReduce s).2.map ZMonomial.cubeRegroup`; `eraMonoTerm` realises each
monomial's weighted cube-sum; `eraListSum` collects each sign block; the single
`∸ᵉ` realises the signed combination `δ = (2^w − 1)(2^w + 1) − (2^w − 1)·P`. -/
def packM_term {p k : ℕ} (s : SosSystem (p + k)) (tTerm wTerm : ETm p) : ETm p :=
  let Rg := (sepReduce s).2.map ZMonomial.cubeRegroup
  let posPart := (Rg.filter (fun mon => !mon.sign)).map (eraMonoTerm · tTerm wTerm)
  let negPart := (Rg.filter (fun mon => mon.sign)).map (eraMonoTerm · tTerm wTerm)
  let factor := eraNumeral 2 ^ᵉ wTerm ∸ᵉ eraNumeral 1
  let minuend := eraConstPart (eraNumeral 0) tTerm wTerm (k + (sepReduce s).1)
    +ᵉ (factor *ᵉ eraListSum negPart)
  let subtrahend := factor *ᵉ eraListSum posPart
  minuend ∸ᵉ subtrahend

open GebLean.EraCompleteness in
/-- Each regrouped reduced monomial's per-monomial term evaluates to its weighted
cube-sum magnitude (arXiv:2407.12928, Cor 3.6): `eraMonoTerm_eval` applied to
`mon.cubeRegroup`, with the degree bound discharged by `sepReduce_degree` and the
three separability conjuncts by `sepReduce_separable`. -/
theorem eraMonoTerm_eval_reduced {p k : ℕ} (s : SosSystem (p + k)) (tTerm wTerm : ETm p)
    (ctx : Fin p → ℕ) (hzero : s.PolyExpZero) (hcoeff : s.CoeffVarProduct)
    (hbase : s.BasePaired) (ht : 0 < Tm.eval eraInterp tTerm ctx)
    (hw : 0 < Tm.eval eraInterp wTerm ctx)
    (mon : ZMonomial (p + k + (sepReduce s).1)) (hmem : mon ∈ (sepReduce s).2) :
    Tm.eval eraInterp (eraMonoTerm mon.cubeRegroup tTerm wTerm) ctx
      = ∑ a ∈ GebLean.EraHypercube.cubePoints (k + (sepReduce s).1)
          (Tm.eval eraInterp tTerm ctx),
          2 ^ (2 * Tm.eval eraInterp wTerm ctx
              * GebLean.EraHypercube.mixedRadix (k + (sepReduce s).1)
                  (Tm.eval eraInterp tTerm ctx) a)
            * mon.cubeRegroup.evalNat (Fin.append ctx a) := by
  obtain ⟨hsc, hsp, hscube⟩ := sepReduce_separable s hcoeff hbase ctx mon hmem
  have hdeg : ∀ i, mon.cubeRegroup.polyExp i ≤ 2 := by
    intro i
    simp only [ZMonomial.cubeRegroup, ZMonomial.weaken]
    cases preimage (finCongr (Nat.add_assoc p k (sepReduce s).1)) i with
    | none => exact Nat.zero_le 2
    | some j => exact sepReduce_degree s hzero mon hmem j
  exact eraMonoTerm_eval mon.cubeRegroup tTerm wTerm ctx hdeg hsc hsp hscube ht hw

open GebLean.EraCompleteness in
/-- The packed-witness term evaluates to the packed witness `packM` of the
reduced predicate (arXiv:2407.12928, Lemma 3.3, Eq (8)). The cube width is
`K = k + (sepReduce s).1`; the predicate is the `toNat` of the regrouped
reduced eval-sum. The hypotheses (`hzero`/`hcoeff`/`hbase` for the
degree/separability discharge, `ht`/`hw` positivity, and `hP` the block bound)
are exactly those the surrounding completeness assembly supplies. -/
theorem packM_term_eval {p k : ℕ} (s : SosSystem (p + k)) (tTerm wTerm : ETm p)
    (ctx : Fin p → ℕ) (hzero : s.PolyExpZero) (hcoeff : s.CoeffVarProduct)
    (hbase : s.BasePaired) (ht : 0 < Tm.eval eraInterp tTerm ctx)
    (hw : 0 < Tm.eval eraInterp wTerm ctx)
    (hP : ∀ a ∈ GebLean.EraHypercube.cubePoints (k + (sepReduce s).1)
            (Tm.eval eraInterp tTerm ctx),
          (((sepReduce s).2).map (fun (mon : ZMonomial (p + k + (sepReduce s).1)) =>
            mon.cubeRegroup.eval (Fin.append ctx a))).sum.toNat
            < 2 ^ Tm.eval eraInterp wTerm ctx) :
    Tm.eval eraInterp (packM_term s tTerm wTerm) ctx
      = GebLean.EraHypercube.packM (k + (sepReduce s).1)
          (Tm.eval eraInterp wTerm ctx) (Tm.eval eraInterp tTerm ctx)
          (fun a => (((sepReduce s).2).map
            (fun (mon : ZMonomial (p + k + (sepReduce s).1)) =>
              mon.cubeRegroup.eval (Fin.append ctx a))).sum.toNat) := by
  set t := Tm.eval eraInterp tTerm ctx with ht_def
  set w := Tm.eval eraInterp wTerm ctx with hw_def
  set K := k + (sepReduce s).1 with hK_def
  set Rg := (sepReduce s).2.map ZMonomial.cubeRegroup with hRg_def
  set P : (Fin K → ℕ) → ℕ := fun a => (((sepReduce s).2).map
    (fun (mon : ZMonomial (p + k + (sepReduce s).1)) =>
      mon.cubeRegroup.eval (Fin.append ctx a))).sum.toNat with hP_def
  -- the per-monomial weighted magnitude cube-sum
  set M : ZMonomial (p + K) → ℕ := fun mon => ∑ a ∈ GebLean.EraHypercube.cubePoints K t,
    2 ^ (2 * w * GebLean.EraHypercube.mixedRadix K t a) * mon.evalNat (Fin.append ctx a)
    with hM_def
  -- uniform: every regrouped monomial's term evaluates to its magnitude cube-sum
  have hmono : ∀ mon ∈ Rg, Tm.eval eraInterp (eraMonoTerm mon tTerm wTerm) ctx = M mon := by
    intro mon hmon
    obtain ⟨mon₀, hmon₀, rfl⟩ := List.mem_map.mp hmon
    exact eraMonoTerm_eval_reduced s tTerm wTerm ctx hzero hcoeff hbase ht hw mon₀ hmon₀
  -- the two sign blocks as ℕ sums of magnitude cube-sums over the filtered sublists
  set posSum := ((Rg.filter (fun mon => !mon.sign)).map M).sum with hpos_def
  set negSum := ((Rg.filter (fun mon => mon.sign)).map M).sum with hneg_def
  -- the constant cube-sum factor `C = ∑_a 2^(2w·v)·(2^w−1)·(2^w+1)`
  set C := ∑ a ∈ GebLean.EraHypercube.cubePoints K t,
    2 ^ (2 * w * GebLean.EraHypercube.mixedRadix K t a) * (2 ^ w - 1) * (2 ^ w + 1) with hC_def
  -- evaluate the two halves of the term
  have heval_factor : Tm.eval eraInterp (eraNumeral 2 ^ᵉ wTerm ∸ᵉ eraNumeral 1) ctx
      = 2 ^ w - 1 := by
    simp only [epow, etsub, Tm.eval, eraInterp, fcons, eraNumeral_eval, ← hw_def]
  -- evaluate an `eraListSum` of per-monomial terms over a filtered sublist
  have hlistsum : ∀ (q : ZMonomial (p + K) → Bool),
      Tm.eval eraInterp
        (eraListSum ((Rg.filter q).map (eraMonoTerm · tTerm wTerm))) ctx
        = ((Rg.filter q).map M).sum := by
    intro q
    rw [eraListSum_eval, List.map_map]
    refine congrArg List.sum (List.map_congr_left (fun mon hmon => ?_))
    exact hmono mon (List.mem_of_mem_filter hmon)
  have hconst : Tm.eval eraInterp (eraConstPart (eraNumeral 0) tTerm wTerm K) ctx = C := by
    rw [eraConstPart_eval (eraNumeral 0) tTerm wTerm K ctx ht hw, hC_def]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    simp only [eraNumeral_eval, Nat.sub_zero, ← hw_def, ← ht_def]
  have heval_minuend : Tm.eval eraInterp
      (eraConstPart (eraNumeral 0) tTerm wTerm K
        +ᵉ ((eraNumeral 2 ^ᵉ wTerm ∸ᵉ eraNumeral 1)
          *ᵉ eraListSum ((Rg.filter (fun mon => mon.sign)).map
            (eraMonoTerm · tTerm wTerm)))) ctx
      = C + (2 ^ w - 1) * negSum := by
    rw [eadd, Tm.eval, eraInterp]
    simp only [fcons]
    rw [emul, Tm.eval, eraInterp]
    simp only [fcons]
    rw [hconst, heval_factor, hlistsum (fun mon => mon.sign), ← hneg_def]
  have heval_subtrahend : Tm.eval eraInterp
      ((eraNumeral 2 ^ᵉ wTerm ∸ᵉ eraNumeral 1)
        *ᵉ eraListSum ((Rg.filter (fun mon => !mon.sign)).map
          (eraMonoTerm · tTerm wTerm))) ctx
      = (2 ^ w - 1) * posSum := by
    rw [emul, Tm.eval, eraInterp]
    simp only [fcons]
    rw [heval_factor, hlistsum (fun mon => !mon.sign), ← hpos_def]
  -- the magnitude cube-sum of a monomial, cast to ℤ
  have hMcast : ∀ mon : ZMonomial (p + K), (M mon : ℤ)
      = ∑ a ∈ GebLean.EraHypercube.cubePoints K t,
          (2 : ℤ) ^ (2 * w * GebLean.EraHypercube.mixedRadix K t a)
            * (mon.evalNat (Fin.append ctx a) : ℤ) := by
    intro mon
    rw [hM_def, Nat.cast_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  -- 1 ≤ 2^w, for casting the truncated factor
  have h2w : (1 : ℕ) ≤ 2 ^ w := Nat.one_le_two_pow
  -- the integer magnitude cube-sum as a function, for the sign partition
  set Mz : ZMonomial (p + K) → ℤ := fun mon => ∑ a ∈ GebLean.EraHypercube.cubePoints K t,
    (2 : ℤ) ^ (2 * w * GebLean.EraHypercube.mixedRadix K t a)
      * (mon.evalNat (Fin.append ctx a) : ℤ) with hMz_def
  -- a filtered list-sum of `Mz` is the ℤ-cast of the same `M`-sum
  have hcastSum : ∀ q : ZMonomial (p + K) → Bool,
      ((Rg.filter q).map Mz).sum = (((Rg.filter q).map M).sum : ℤ) := by
    intro q
    rw [Nat.cast_list_sum, List.map_map]
    refine congrArg List.sum (List.map_congr_left (fun mon _ => ?_))
    simp only [hMz_def, Function.comp_apply]
    exact (hMcast mon).symm
  -- the signed-sum bridge specialised to this `P`, then sign-partitioned
  have hsigned : (∑ a ∈ GebLean.EraHypercube.cubePoints K t,
        (2 : ℤ) ^ (2 * w * GebLean.EraHypercube.mixedRadix K t a) * (P a : ℤ))
      = (posSum : ℤ) - (negSum : ℤ) := by
    rw [hP_def, packM_signed_sum s ctx w t]
    rw [show (List.map ZMonomial.cubeRegroup (sepReduce s).snd) = Rg from hRg_def.symm]
    rw [signPartition_sum Rg (fun mon => mon.sign) Mz]
    rw [hcastSum (fun mon => !mon.sign), hcastSum (fun mon => mon.sign),
      ← hpos_def, ← hneg_def]
  -- the integer identity `eval(minuend) = eval(subtrahend) + packM`
  have hZ : ((C + (2 ^ w - 1) * negSum : ℕ) : ℤ)
      = ((2 ^ w - 1) * posSum : ℕ) + (GebLean.EraHypercube.packM K w t P : ℤ) := by
    rw [packM_affine_int (K := K) (w := w) (t := t) P hw (fun a ha => hP a ha)]
    push_cast [Nat.cast_sub h2w]
    rw [hC_def, hsigned, Nat.cast_sum]
    have hCsum : (∑ a ∈ GebLean.EraHypercube.cubePoints K t,
        ((2 ^ (2 * w * GebLean.EraHypercube.mixedRadix K t a) * (2 ^ w - 1) * (2 ^ w + 1) : ℕ) : ℤ))
        = ∑ a ∈ GebLean.EraHypercube.cubePoints K t,
            (2 : ℤ) ^ (2 * w * GebLean.EraHypercube.mixedRadix K t a)
              * ((2 ^ w - 1) * (2 ^ w + 1)) := by
      refine Finset.sum_congr rfl (fun a _ => ?_)
      push_cast [Nat.cast_sub h2w]
      ring
    rw [hCsum]
    ring
  -- descend to ℕ and discharge the truncated subtraction
  have hN : C + (2 ^ w - 1) * negSum
      = (2 ^ w - 1) * posSum + GebLean.EraHypercube.packM K w t P := by
    have := hZ
    push_cast at this
    exact_mod_cast this
  have hfinal : Tm.eval eraInterp (packM_term s tTerm wTerm) ctx
      = GebLean.EraHypercube.packM K w t P := by
    rw [packM_term, etsub, Tm.eval, eraInterp]
    simp only [fcons]
    rw [heval_minuend, heval_subtrahend, hN, Nat.add_sub_cancel_left]
  exact hfinal

open GebLean.EraHistCodeTerm (eraCountOfPack eraCountOfPack_eval) in
/-- The count of cube points where the reduced predicate vanishes, as an `Era`
term (arXiv:2407.12928, Lemma 3.3 read-off): `eraCountOfPack` applied to the
packed-witness term `packM_term s tTerm wTerm` for the extended cube width
`k + (sepReduce s).1`. -/
def eraCount {p k : ℕ} (s : SosSystem (p + k)) (tTerm wTerm : ETm p) : ETm p :=
  eraCountOfPack (k + (sepReduce s).1) (packM_term s tTerm wTerm) tTerm wTerm

open GebLean.EraCompleteness in
open GebLean.EraHistCodeTerm (eraCountOfPack eraCountOfPack_eval) in
/-- The count read-off identity (arXiv:2407.12928, Lemma 3.3 / Cor 3.6):
`eraCount s tTerm wTerm` evaluates to the number of cube points of the
side-`t` cube `cubePoints (k + (sepReduce s).1) t` where the reduced predicate
`(Σ_{mon} mon.cubeRegroup.eval (append ctx a)).toNat` vanishes. -/
theorem eraCount_eval {p k : ℕ} (s : SosSystem (p + k)) (tTerm wTerm : ETm p)
    (ctx : Fin p → ℕ)
    (hzero : s.PolyExpZero) (hcoeff : s.CoeffVarProduct) (hbase : s.BasePaired)
    (ht : 0 < Tm.eval eraInterp tTerm ctx) (hw : 0 < Tm.eval eraInterp wTerm ctx)
    (hP : ∀ a ∈ GebLean.EraHypercube.cubePoints (k + (sepReduce s).1)
            (Tm.eval eraInterp tTerm ctx),
          (((sepReduce s).2).map (fun (mon : ZMonomial (p + k + (sepReduce s).1)) =>
            mon.cubeRegroup.eval (Fin.append ctx a))).sum.toNat
            < 2 ^ Tm.eval eraInterp wTerm ctx) :
    Tm.eval eraInterp (eraCount s tTerm wTerm) ctx
      = ((GebLean.EraHypercube.cubePoints (k + (sepReduce s).1)
            (Tm.eval eraInterp tTerm ctx)).filter
          (fun a => (((sepReduce s).2).map
            (fun (mon : ZMonomial (p + k + (sepReduce s).1)) =>
              mon.cubeRegroup.eval (Fin.append ctx a))).sum.toNat = 0)).card := by
  rw [eraCount]
  set P : (Fin (k + (sepReduce s).1) → ℕ) → ℕ :=
    fun a => (((sepReduce s).2).map (fun (mon : ZMonomial (p + k + (sepReduce s).1)) =>
      mon.cubeRegroup.eval (Fin.append ctx a))).sum.toNat with hP_def
  exact eraCountOfPack_eval (k + (sepReduce s).1) (packM_term s tTerm wTerm) tTerm wTerm
    ctx P ht hw hP
    (packM_term_eval s tTerm wTerm ctx hzero hcoeff hbase ht hw hP)

/-- The reindexing bridge for the enlarged cube of arXiv:2407.12928, Corollary 3.6:
the regrouped monomial `mon.cubeRegroup` evaluated at the `Fin.append`-context that
reads `ctx` on the `p` parameter slots, the original cube `x` on the next `k` slots,
and the chain witness `b` on the last `f` slots equals the raw monomial `mon`
evaluated at the left-associated `Fin.append (Fin.append ctx x) b`. It is
`ZMonomial.cubeRegroup_eval` composed with the pure `Fin.append`/`finCongr`
re-association `Fin.append_assoc`. -/
theorem cubeRegroup_append_eq {p k f : ℕ} (mon : ZMonomial (p + k + f))
    (ctx : Fin p → ℕ) (x : Fin k → ℕ) (b : Fin f → ℕ) :
    mon.cubeRegroup.eval (Fin.append ctx (Fin.append x b))
      = mon.eval (Fin.append (Fin.append ctx x) b) := by
  rw [ZMonomial.cubeRegroup_eval]
  congr 1
  rw [Fin.append_assoc]
  rfl

/-- An appended cube point of arXiv:2407.12928, Corollary 3.6 lies in the enlarged
side-`tθ` cube exactly when each block lies in its own cube: `Fin.append x b` is a
point of `cubePoints (k + f) tθ` iff `x ∈ cubePoints k tθ` and `b ∈ cubePoints f tθ`.
The forward direction reads the two blocks off `Fin.append_left`/`Fin.append_right`;
the reverse direction splits an arbitrary index with `Fin.addCases`. -/
theorem mem_cubePoints_append {k f tθ : ℕ} (x : Fin k → ℕ) (b : Fin f → ℕ) :
    Fin.append x b ∈ GebLean.EraHypercube.cubePoints (k + f) tθ
      ↔ x ∈ GebLean.EraHypercube.cubePoints k tθ
        ∧ b ∈ GebLean.EraHypercube.cubePoints f tθ := by
  simp only [GebLean.EraHypercube.mem_cubePoints]
  constructor
  · intro h
    refine ⟨fun i => ?_, fun j => ?_⟩
    · have := h (Fin.castAdd f i)
      rwa [Fin.append_left] at this
    · have := h (Fin.natAdd k j)
      rwa [Fin.append_right] at this
  · rintro ⟨hx, hb⟩ i
    induction i using Fin.addCases with
    | left i => rw [Fin.append_left]; exact hx i
    | right j => rw [Fin.append_right]; exact hb j

/-- Every point of an enlarged cube is the `Fin.append` of its two coordinate blocks:
`a = Fin.append (a ∘ Fin.castAdd f) (a ∘ Fin.natAdd k)`. This is the splitting that,
with `mem_cubePoints_append`, decomposes a point of `cubePoints (k + f) tθ` into its
base-cube and chain-cube parts (arXiv:2407.12928, Corollary 3.6). -/
theorem append_castAdd_natAdd {k f : ℕ} (a : Fin (k + f) → ℕ) :
    Fin.append (a ∘ Fin.castAdd f) (a ∘ Fin.natAdd k) = a := by
  funext i
  induction i using Fin.addCases with
  | left i => rw [Fin.append_left]; rfl
  | right j => rw [Fin.append_right]; rfl

/-- The enlarged side-`tθ` cube of arXiv:2407.12928, Corollary 3.6 is the image of the
product of the base cube and the chain cube under `Fin.append`:
`cubePoints (k + f) tθ = (cubePoints k tθ ×ˢ cubePoints f tθ).image (Fin.append ·.1 ·.2)`.
The append map is injective on the product (its inverse is the
`Fin.castAdd`/`Fin.natAdd` decomposition `append_castAdd_natAdd`), and its image is
characterised by `mem_cubePoints_append`. This is the cube-product split consumed by
the fibre collapse `reducedCount_eq`. -/
theorem cubePoints_eq_image_append {k f tθ : ℕ} :
    GebLean.EraHypercube.cubePoints (k + f) tθ
      = (GebLean.EraHypercube.cubePoints k tθ ×ˢ
          GebLean.EraHypercube.cubePoints f tθ).image (fun p => Fin.append p.1 p.2) := by
  ext a
  simp only [Finset.mem_image, Finset.mem_product]
  constructor
  · intro ha
    refine ⟨(a ∘ Fin.castAdd f, a ∘ Fin.natAdd k), ⟨?_, ?_⟩, append_castAdd_natAdd a⟩
    · exact ((mem_cubePoints_append _ _).mp
        ((append_castAdd_natAdd a).symm ▸ ha)).1
    · exact ((mem_cubePoints_append _ _).mp
        ((append_castAdd_natAdd a).symm ▸ ha)).2
  · rintro ⟨⟨x, b⟩, ⟨hx, hb⟩, rfl⟩
    exact (mem_cubePoints_append x b).mpr ⟨hx, hb⟩

/-- The enlarged side `θ` of arXiv:2407.12928, Corollary 3.6 as a concrete `Era`
term over the parameter context: the majorant of `tTerm ^ d`, where
`d = max 1 (ZMonomial.maxCubeDegree (SosSystem.toZ s))` is the chain depth of the
Lemma 3.5 reduction (`(sepReduce s).1 = k · d`). Every Lemma 3.5 chain witness
`(x c) ^ (i + 1)` with `x c < t` and `i + 1 ≤ d` is strictly below this value
(`eraTheta_spec`), so the unique zeroing witness `b₀` of `sepReduce_unique` is a
valid coordinate of the side-`θ` enlarged cube. -/
def eraTheta {p k : ℕ} (s : SosSystem (p + k)) (tTerm : ETm p) : ETm p :=
  eraMajorant (tTerm ^ᵉ eraNumeral (max 1 (ZMonomial.maxCubeDegree (SosSystem.toZ s))))

/-- The chain-witness bound of arXiv:2407.12928, Corollary 3.6 (via Lemma 3.5).
Every chain witness coordinate `(x c) ^ (i + 1)` produced by `sepReduce_unique` at
`ρ = Fin.append ctx x` — where the cube coordinate `x c` is below `t` and the chain
index `i` is below `d = max 1 (ZMonomial.maxCubeDegree (SosSystem.toZ s))` — is
strictly below `Tm.eval eraInterp (eraTheta s tTerm) ctx`. The bound chains
`(x c) ^ (i + 1) ≤ (x c) ^ d < t ^ d` with `eraMajorant_spec`. -/
theorem eraTheta_spec {p k : ℕ} (s : SosSystem (p + k)) (tTerm : ETm p)
    (ctx : Fin p → ℕ) (x : Fin k → ℕ)
    (hx : ∀ c, x c < Tm.eval eraInterp tTerm ctx) (c : Fin k)
    (i : Fin (max 1 (ZMonomial.maxCubeDegree (SosSystem.toZ s)))) :
    x c ^ (i.val + 1) < Tm.eval eraInterp (eraTheta s tTerm) ctx := by
  obtain ⟨iv, hiv⟩ := i
  set t := Tm.eval eraInterp tTerm ctx with ht_def
  have hid : iv + 1 ≤ max 1 (ZMonomial.maxCubeDegree (SosSystem.toZ s)) := hiv
  have hd_pos : 0 < max 1 (ZMonomial.maxCubeDegree (SosSystem.toZ s)) :=
    lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  have hpow_le : x c ^ (iv + 1)
      ≤ x c ^ max 1 (ZMonomial.maxCubeDegree (SosSystem.toZ s)) := by
    rcases Nat.eq_zero_or_pos (x c) with h0 | hpos
    · rw [h0, Nat.zero_pow (by omega : 0 < iv + 1), Nat.zero_pow hd_pos]
    · exact Nat.pow_le_pow_right hpos hid
  have hlt : x c ^ max 1 (ZMonomial.maxCubeDegree (SosSystem.toZ s))
      < t ^ max 1 (ZMonomial.maxCubeDegree (SosSystem.toZ s)) :=
    Nat.pow_lt_pow_left (hx c) hd_pos.ne'
  have hmaj : t ^ max 1 (ZMonomial.maxCubeDegree (SosSystem.toZ s))
      < Tm.eval eraInterp (eraTheta s tTerm) ctx := by
    rw [eraTheta]
    have h := eraMajorant_spec
      (tTerm ^ᵉ eraNumeral (max 1 (ZMonomial.maxCubeDegree (SosSystem.toZ s)))) ctx
    rwa [epow_eval, eraInterp, eraNumeral_eval, ← ht_def] at h
  exact lt_of_le_of_lt (le_trans hpow_le (le_of_lt hlt)) hmaj

/-- A single cube point's monomial magnitude is bounded by the whole weighted
cube-sum (arXiv:2407.12928, Cor 3.6, Eq (8)): for `a₀ ∈ cubePoints K t`,
`mon.evalNat (Fin.append ctx a₀) ≤ ∑_a 2 ^ (2 · w · v(a)) · mon.evalNat (append ctx a)`,
since each position weight is at least `1` and every summand is non-negative. -/
theorem monoEvalNat_le_weightedSum {p K : ℕ} (mon : ZMonomial (p + K)) (ctx : Fin p → ℕ)
    (w t : ℕ) (a₀ : Fin K → ℕ) (ha₀ : a₀ ∈ GebLean.EraHypercube.cubePoints K t) :
    mon.evalNat (Fin.append ctx a₀)
      ≤ ∑ a ∈ GebLean.EraHypercube.cubePoints K t,
          2 ^ (2 * w * GebLean.EraHypercube.mixedRadix K t a)
            * mon.evalNat (Fin.append ctx a) := by
  refine le_trans ?_ (Finset.single_le_sum
    (f := fun a => 2 ^ (2 * w * GebLean.EraHypercube.mixedRadix K t a)
      * mon.evalNat (Fin.append ctx a))
    (fun a _ => Nat.zero_le _) ha₀)
  exact Nat.le_mul_of_pos_left _ (Nat.pow_pos (by norm_num))

/-- The modulus-bound term `w` of arXiv:2407.12928, Corollary 3.6 (discharging the
block bound `hP` of the count read-off): the sum, over the reduced monomials of
`sepReduce s`, of the per-monomial weighted cube-sum terms `eraMonoTerm` at modulus
`1`. Its value dominates the reduced predicate `Pred a` on the side-`t` enlarged
cube (`eraW_spec`), so `Pred a < 2 ^ (eval eraW)` follows from `n < 2 ^ n`. The side
`t` is `Tm.eval eraInterp tTerm ctx`; in the Phase-E assembly `tTerm` is the enlarged
side term `eraTheta s tTerm₀`. -/
def eraW {p k : ℕ} (s : SosSystem (p + k)) (tTerm : ETm p) : ETm p :=
  eraListSum ((sepReduce s).2.map
    (fun mon => eraMonoTerm mon.cubeRegroup tTerm (eraNumeral 1)))

open GebLean.EraCompleteness in
/-- The modulus bound of arXiv:2407.12928, Corollary 3.6: the reduced predicate
`Pred a` at any point `a` of the side-`t` enlarged cube is strictly below
`2 ^ (Tm.eval eraInterp (eraW s tTerm) ctx)`. The value bound `Pred a ≤ eval eraW`
holds because `Pred a` is the `toNat` of the signed reduced eval-sum, hence at most
the sum of the per-monomial magnitudes, each of which is bounded by its weighted
cube-sum `eraMonoTerm` (`monoEvalNat_le_weightedSum`, `eraMonoTerm_eval_reduced`);
`Nat.lt_two_pow_self` then gives the strict `2`-power bound. -/
theorem eraW_spec {p k : ℕ} (s : SosSystem (p + k)) (tTerm : ETm p) (ctx : Fin p → ℕ)
    (hzero : s.PolyExpZero) (hcoeff : s.CoeffVarProduct) (hbase : s.BasePaired)
    (ht : 0 < Tm.eval eraInterp tTerm ctx)
    (a : Fin (k + (sepReduce s).1) → ℕ)
    (ha : a ∈ GebLean.EraHypercube.cubePoints (k + (sepReduce s).1)
        (Tm.eval eraInterp tTerm ctx)) :
    (((sepReduce s).2).map (fun (mon : ZMonomial (p + k + (sepReduce s).1)) =>
        mon.cubeRegroup.eval (Fin.append ctx a))).sum.toNat
      < 2 ^ Tm.eval eraInterp (eraW s tTerm) ctx := by
  set t := Tm.eval eraInterp tTerm ctx with ht_def
  -- the predicate value is bounded by the sum of per-monomial magnitudes
  have hbound : (((sepReduce s).2).map (fun (mon : ZMonomial (p + k + (sepReduce s).1)) =>
      mon.cubeRegroup.eval (Fin.append ctx a))).sum.toNat
      ≤ Tm.eval eraInterp (eraW s tTerm) ctx := by
    -- bound the toNat of the signed sum by the sum of magnitudes
    have hsplit : (((sepReduce s).2).map (fun (mon : ZMonomial (p + k + (sepReduce s).1)) =>
        mon.cubeRegroup.eval (Fin.append ctx a))).sum.toNat
        ≤ ((sepReduce s).2.map (fun (mon : ZMonomial (p + k + (sepReduce s).1)) =>
            mon.cubeRegroup.evalNat (Fin.append ctx a))).sum := by
      rw [← Int.toNat_natCast ((sepReduce s).2.map
          (fun (mon : ZMonomial (p + k + (sepReduce s).1)) =>
            mon.cubeRegroup.evalNat (Fin.append ctx a))).sum]
      refine Int.toNat_le_toNat ?_
      rw [Nat.cast_list_sum, List.map_map]
      refine List.sum_le_sum ?_
      intro z _
      simp only [Function.comp_apply]
      rw [ZMonomial.evalNat_cast]
      exact le_abs_self _
    refine le_trans hsplit ?_
    rw [eraW, eraListSum_eval, List.map_map]
    refine List.sum_le_sum ?_
    intro mon hmon
    simp only [Function.comp_apply]
    rw [eraMonoTerm_eval_reduced s tTerm (eraNumeral 1) ctx hzero hcoeff hbase ht
      (by rw [eraNumeral_eval]; norm_num) mon hmon]
    exact monoEvalNat_le_weightedSum mon.cubeRegroup ctx
      (Tm.eval eraInterp (eraNumeral 1) ctx) t a ha
  exact lt_of_le_of_lt hbound Nat.lt_two_pow_self

/-- The fibre collapse of arXiv:2407.12928, Corollary 3.6 (via Lemma 3.5). At the
enlarged side `tθ`, the number of zeros of the reduced predicate `Pred` over the
enlarged cube `cubePoints (k + (sepReduce s).1) tθ` equals the number of zeros of the
source system `SosSystem.eval s (Fin.append ctx ·)` over the base cube
`cubePoints k tθ`. The chain-witness fibre over each base-zero is a singleton (the
unique zeroing witness of `sepReduce_unique`, valid by the per-coordinate bound `hθ`)
and is empty over each base-non-zero (`sepReduce_sound`). `hθ` is supplied at the
assembly site from `eraTheta_spec`. -/
theorem reducedCount_eq {p k : ℕ} (s : SosSystem (p + k)) (ctx : Fin p → ℕ) (tθ : ℕ)
    (hcoeff : s.CoeffVarProduct) (hbase : s.BasePaired)
    (hθ : ∀ x ∈ GebLean.EraHypercube.cubePoints k tθ,
        SosSystem.eval s (Fin.append ctx x) = 0 →
        ∀ (c : Fin k) (i : Fin (max 1 (ZMonomial.maxCubeDegree (SosSystem.toZ s)))),
          x c ^ (i.val + 1) < tθ) :
    ((GebLean.EraHypercube.cubePoints (k + (sepReduce s).1) tθ).filter
        (fun a => (((sepReduce s).2).map (fun (mon : ZMonomial (p + k + (sepReduce s).1)) =>
          mon.cubeRegroup.eval (Fin.append ctx a))).sum.toNat = 0)).card
      = ((GebLean.EraHypercube.cubePoints k tθ).filter
          (fun x => SosSystem.eval s (Fin.append ctx x) = 0)).card := by
  set f := (sepReduce s).1
  -- the explicit chain-power witness over a base point, as a total function
  set b₀ : (Fin k → ℕ) → Fin f → ℕ :=
    fun x j => x ((finProdFinEquiv.symm j).1) ^ ((finProdFinEquiv.symm j).2.val + 1)
    with hb₀
  -- the `.toNat = 0 ↔ reduced sum = 0` and `cubeRegroup_append_eq` bridge
  have hbridge : ∀ (x : Fin k → ℕ) (b : Fin f → ℕ),
      (((sepReduce s).2).map (fun (mon : ZMonomial (p + k + (sepReduce s).1)) =>
          mon.cubeRegroup.eval (Fin.append ctx (Fin.append x b)))).sum.toNat = 0
        ↔ (((sepReduce s).2).map
            (fun mon => mon.eval (Fin.append (Fin.append ctx x) b))).sum = 0 := by
    intro x b
    have hmap : (((sepReduce s).2).map (fun (mon : ZMonomial (p + k + (sepReduce s).1)) =>
        mon.cubeRegroup.eval (Fin.append ctx (Fin.append x b)))).sum
        = (((sepReduce s).2).map
            (fun mon => mon.eval (Fin.append (Fin.append ctx x) b))).sum := by
      refine congrArg List.sum (List.map_congr_left (fun mon _ => ?_))
      exact cubeRegroup_append_eq mon ctx x b
    have hnn : 0 ≤ (((sepReduce s).2).map
        (fun mon => mon.eval (Fin.append (Fin.append ctx x) b))).sum := by
      rw [← hmap]
      exact reducedCubeEval_nonneg s ctx (Fin.append x b)
    rw [hmap, Int.toNat_eq_zero]
    exact ⟨fun h => le_antisymm h hnn, fun h => le_of_eq h⟩
  -- `ChainHolds` for the explicit witness `b₀ x`, mirroring `sepReduce_unique`
  have hCH₀ : ∀ x : Fin k → ℕ,
      ChainHolds (Fin.append (Fin.append ctx x) (b₀ x)) := by
    intro x c i
    rw [append_chainSlot, append_cubeSlot, hb₀]
    simp only [Fin.append_right]
    rw [show finProdFinEquiv.symm (chainIdx c i) = (c, i) from by
      rw [chainIdx, Equiv.symm_apply_apply]]
  -- the explicit witness `b₀ x` zeros the reduced sum over a base-zero `x`
  have hb₀_zero : ∀ x : Fin k → ℕ, SosSystem.eval s (Fin.append ctx x) = 0 →
      (((sepReduce s).2).map
          (fun mon => mon.eval (Fin.append (Fin.append ctx x) (b₀ x)))).sum = 0 := by
    intro x hx0
    rw [sepReduce_eval_split]
    have hchain : ((List.finRange k).map (fun c =>
        ((List.finRange (max 1 (ZMonomial.maxCubeDegree (SosSystem.toZ s)))).map
          (fun i => (((chainEqList c i).map
            (fun mon => mon.eval (Fin.append (Fin.append ctx x) (b₀ x)))).sum)
            ^ 2)).sum)).sum = 0 := by
      refine List.sum_eq_zero (fun y hy => ?_)
      obtain ⟨c, _, rfl⟩ := List.mem_map.mp hy
      refine List.sum_eq_zero (fun z hz => ?_)
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hz
      rw [chainHolds_imp_chainEqList_zero _ (hCH₀ x) c i]
      ring
    have hpred : ((((SosSystem.toZ s).map
        (fun mon => mon.weaken (Fin.castAdd
          (k * max 1 (ZMonomial.maxCubeDegree (SosSystem.toZ s)))))).map chainSub).map
        (fun mon => mon.eval (Fin.append (Fin.append ctx x) (b₀ x)))).sum ^ 2 = 0 := by
      rw [sepReduce_psub_eval s hcoeff hbase (Fin.append ctx x) (b₀ x) (hCH₀ x), hx0,
        Nat.cast_zero]
      norm_num
    rw [show (0 : ℤ) = 0 + 0 from (add_zero 0).symm]
    exact congrArg₂ (· + ·) hchain hpred
  -- uniqueness: any zeroing witness over a base-zero `x` equals `b₀ x`
  have hb₀_uniq : ∀ (x : Fin k → ℕ) (b : Fin f → ℕ),
      SosSystem.eval s (Fin.append ctx x) = 0 →
      (((sepReduce s).2).map
          (fun mon => mon.eval (Fin.append (Fin.append ctx x) b))).sum = 0 →
        b = b₀ x := by
    intro x b hx0 hb
    obtain ⟨bw, _, hbw_uniq⟩ := sepReduce_unique s hcoeff hbase (Fin.append ctx x) hx0
    rw [hbw_uniq b hb, hbw_uniq (b₀ x) (hb₀_zero x hx0)]
  -- the explicit witness `b₀ x` lies in the chain cube, by the per-coordinate bound `hθ`
  have hb₀_mem : ∀ x ∈ GebLean.EraHypercube.cubePoints k tθ,
      SosSystem.eval s (Fin.append ctx x) = 0 →
      b₀ x ∈ GebLean.EraHypercube.cubePoints f tθ := by
    intro x hx hx0
    rw [GebLean.EraHypercube.mem_cubePoints]
    intro j
    rw [hb₀]
    exact hθ x hx hx0 (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2
  refine Finset.card_nbij' (fun a => a ∘ Fin.castAdd f)
    (fun x => Fin.append x (b₀ x)) ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at ha ⊢
    obtain ⟨ha_mem, ha_pred⟩ := ha
    set x := a ∘ Fin.castAdd f with hx_def
    set b := a ∘ Fin.natAdd k with hb_def
    have ha_split : a = Fin.append x b := (append_castAdd_natAdd a).symm
    refine ⟨((mem_cubePoints_append x b).mp (ha_split ▸ ha_mem)).1, ?_⟩
    refine sepReduce_sound s hcoeff hbase (Fin.append ctx x) b ?_
    rw [← (hbridge x b).mp]
    rw [← ha_split]
    exact ha_pred
  · intro x hx
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at hx ⊢
    obtain ⟨hx_mem, hx0⟩ := hx
    refine ⟨(mem_cubePoints_append x (b₀ x)).mpr ⟨hx_mem, hb₀_mem x hx_mem hx0⟩, ?_⟩
    exact (hbridge x (b₀ x)).mpr (hb₀_zero x hx0)
  · intro a ha
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at ha
    obtain ⟨ha_mem, ha_pred⟩ := ha
    set x := a ∘ Fin.castAdd f with hx_def
    set b := a ∘ Fin.natAdd k with hb_def
    have ha_split : Fin.append x b = a := append_castAdd_natAdd a
    have hx0 : SosSystem.eval s (Fin.append ctx x) = 0 := by
      refine sepReduce_sound s hcoeff hbase (Fin.append ctx x) b ?_
      rw [← (hbridge x b).mp]
      rw [ha_split]
      exact ha_pred
    have hbzero : (((sepReduce s).2).map
        (fun mon => mon.eval (Fin.append (Fin.append ctx x) b))).sum = 0 := by
      rw [← (hbridge x b).mp]
      rw [ha_split]
      exact ha_pred
    change Fin.append x (b₀ x) = a
    rw [← hb₀_uniq x b hx0 hbzero]
    exact ha_split
  · intro x _
    funext i
    exact Fin.append_left x (b₀ x) i

/-- The shell-empty side collapse of arXiv:2407.12928, Corollary 3.6, Condition 9:
the number of base-cube zeros of `SosSystem.eval s (Fin.append ctx ·)` is the same at
the enlarged side `tθ` as at the base side `t`. The shell `[t, tθ)` contributes no
zeros: by `hshell` every base-zero of the side-`tθ` cube already has all coordinates
below `t`, so the two filtered cubes coincide as `Finset`s
(`cubePoints k t ⊆ cubePoints k tθ` by `mem_cubePoints`). `hshell` is supplied at the
assembly site from the per-coordinate solution bound `diophOf_bound`. -/
theorem predCount_side_eq {p k : ℕ} (s : SosSystem (p + k)) (ctx : Fin p → ℕ)
    (t tθ : ℕ) (htθ : t ≤ tθ)
    (hshell : ∀ x ∈ GebLean.EraHypercube.cubePoints k tθ,
        SosSystem.eval s (Fin.append ctx x) = 0 → ∀ c, x c < t) :
    ((GebLean.EraHypercube.cubePoints k tθ).filter
        (fun x => SosSystem.eval s (Fin.append ctx x) = 0)).card
      = ((GebLean.EraHypercube.cubePoints k t).filter
          (fun x => SosSystem.eval s (Fin.append ctx x) = 0)).card := by
  refine congrArg Finset.card (Finset.ext (fun x => ?_))
  simp only [Finset.mem_filter, GebLean.EraHypercube.mem_cubePoints]
  constructor
  · rintro ⟨hx, hzero⟩
    exact ⟨hshell x (GebLean.EraHypercube.mem_cubePoints.mpr hx) hzero, hzero⟩
  · rintro ⟨hx, hzero⟩
    exact ⟨fun c => lt_of_lt_of_le (hx c) htθ, hzero⟩

/-- The slot-moving re-indexing embedding of arXiv:2407.12928, Corollary 3.6:
move the output slot of a `diophOf` encoding from the parameter side
(`Fin.snoc`) to the cube side. It sends the `n` inputs to the input block, the
output index `n` to the first cube slot, and witness `i` to cube slot `1 + i`,
realising `Fin (n + 1 + witArity) → Fin (n + (1 + witArity))`. Built from
`Fin.addCases` / `Fin.lastCases`, so it executes. -/
def reindexEmb (n witArity : ℕ) :
    Fin (n + 1 + witArity) → Fin (n + (1 + witArity)) :=
  Fin.addCases
    (Fin.lastCases (Fin.natAdd n (0 : Fin (1 + witArity)))
      (fun j => Fin.castAdd (1 + witArity) j))
    (fun i => Fin.natAdd n (Fin.natAdd 1 i))

/-- The re-indexed context of arXiv:2407.12928, Corollary 3.6: read a cube point
`a : Fin (1 + witArity) → ℕ` (output slot then witnesses) into the `diophOf`
encoding's context, with the output value `a 0` placed on the `Fin.snoc`
parameter side and the witnesses `a (1 + i)` on the append side. -/
def reindexCtx {n : ℕ} (τ : ETm n) (ctx : Fin n → ℕ)
    (a : Fin (1 + (diophOf τ).witArity) → ℕ) : Fin (n + 1 + (diophOf τ).witArity) → ℕ :=
  (diophOf τ).ctx ctx (a 0) (fun i => a (Fin.natAdd 1 i))

/-- Injectivity of `reindexEmb`: inputs land in the input block, while the output
slot and the witnesses land at distinct cube slots (`0` and `1 + i`). -/
theorem reindexEmb_injective (n witArity : ℕ) :
    Function.Injective (reindexEmb n witArity) := by
  intro a b hab
  unfold reindexEmb at hab
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
          simp only [Fin.lastCases_last, Fin.lastCases_castSucc, Fin.ext_iff, Fin.val_natAdd,
            Fin.val_castAdd] at hab
          omega
      | cast ja =>
        induction ib using Fin.lastCases with
        | last =>
          simp only [Fin.lastCases_last, Fin.lastCases_castSucc, Fin.ext_iff, Fin.val_natAdd,
            Fin.val_castAdd] at hab
          omega
        | cast jb =>
          simp only [Fin.lastCases_castSucc] at hab
          rw [Fin.castAdd_injective _ _ hab]
    | right kb =>
      simp only [Fin.addCases_left, Fin.addCases_right] at hab
      induction ia using Fin.lastCases with
      | last =>
        simp only [Fin.lastCases_last, Fin.ext_iff, Fin.val_natAdd] at hab
        exfalso; simp only [Fin.val_zero] at hab; omega
      | cast ja =>
        simp only [Fin.lastCases_castSucc, Fin.ext_iff, Fin.val_natAdd, Fin.val_castAdd] at hab
        omega
  | right ka =>
    induction b using Fin.addCases with
    | left ib =>
      simp only [Fin.addCases_left, Fin.addCases_right] at hab
      induction ib using Fin.lastCases with
      | last =>
        simp only [Fin.lastCases_last, Fin.ext_iff, Fin.val_natAdd] at hab
        exfalso; simp only [Fin.val_zero] at hab; omega
      | cast jb =>
        simp only [Fin.lastCases_castSucc, Fin.ext_iff, Fin.val_natAdd, Fin.val_castAdd] at hab
        omega
    | right kb =>
      simp only [Fin.addCases_right] at hab
      have h := Fin.natAdd_injective _ _ hab
      have h2 := Fin.natAdd_injective _ _ h
      rw [h2]

/-- The re-indexing identity of arXiv:2407.12928, Corollary 3.6: precomposing the
cube context `Fin.append ctx a` with `reindexEmb` recovers the `diophOf` context
`reindexCtx`. The cube-side block of `Fin.append ctx a` is read at slot `0` for the
output and at slots `1 + i` for the witnesses. -/
theorem append_comp_reindexEmb {n : ℕ} (τ : ETm n) (ctx : Fin n → ℕ)
    (a : Fin (1 + (diophOf τ).witArity) → ℕ) :
    (Fin.append ctx a) ∘ reindexEmb n (diophOf τ).witArity = reindexCtx τ ctx a := by
  refine funext (fun z => ?_)
  simp only [Function.comp_apply, reindexEmb, reindexCtx, DiophEnc.ctx]
  refine Fin.addCases ?_ ?_ z
  · intro io
    refine Fin.lastCases ?_ ?_ io
    · simp only [Fin.addCases_left, Fin.lastCases_last, Fin.append_right, Fin.append_left,
        Fin.snoc_last]
    · intro j
      simp only [Fin.addCases_left, Fin.lastCases_castSucc, Fin.append_left, Fin.snoc_castSucc]
  · intro i
    simp only [Fin.addCases_right, Fin.append_right]

/-- The re-indexed system of arXiv:2407.12928, Corollary 3.6: the `diophOf`
encoding's sum-of-squares system, weakened along `reindexEmb` so that the output
slot and the witnesses become the cube-side coordinates a cube point ranges over.
Phase E (`sepReduce`, `eraCount`) operates on this system. -/
def reindexSys {n : ℕ} (τ : ETm n) : SosSystem (n + (1 + (diophOf τ).witArity)) :=
  (diophOf τ).sys.weaken (reindexEmb n (diophOf τ).witArity)

/-- The re-indexing bridge of arXiv:2407.12928, Corollary 3.6: evaluating the
re-indexed system at the cube context `Fin.append ctx a` equals evaluating the
original `diophOf` system at the re-indexed context `reindexCtx`. An instance of
`SosSystem.eval_weaken` (the embedding `reindexEmb` is injective) composed with
`append_comp_reindexEmb`. -/
theorem reindexSys_eval {n : ℕ} (τ : ETm n) (ctx : Fin n → ℕ)
    (a : Fin (1 + (diophOf τ).witArity) → ℕ) :
    SosSystem.eval (reindexSys τ) (Fin.append ctx a)
      = SosSystem.eval (diophOf τ).sys (reindexCtx τ ctx a) := by
  rw [reindexSys, SosSystem.eval_weaken _ _ (reindexEmb_injective n (diophOf τ).witArity),
    append_comp_reindexEmb]

/-- The re-indexed system inherits the polynomial-exponent-zero invariant of the
`diophOf` encoding (`diophOf_polyExpZero`) through `SosSystem.weaken_polyExpZero`,
so it is a valid input to the Lemma 3.5 reduction (arXiv:2407.12928, Cor 3.6). -/
theorem reindexSys_polyExpZero {n : ℕ} (τ : ETm n) : (reindexSys τ).PolyExpZero :=
  SosSystem.weaken_polyExpZero (diophOf_polyExpZero τ) _

/-- The re-indexed system inherits the coefficient-variable-product invariant of
the `diophOf` encoding (`diophOf_coeffVarProduct`) through
`SosSystem.weaken_coeffVarProduct` (arXiv:2407.12928, Cor 3.6). -/
theorem reindexSys_coeffVarProduct {n : ℕ} (τ : ETm n) : (reindexSys τ).CoeffVarProduct :=
  SosSystem.weaken_coeffVarProduct (diophOf_coeffVarProduct τ) _

/-- The re-indexed system inherits the base-paired invariant of the `diophOf`
encoding (`diophOf_basePaired`) through `SosSystem.weaken_basePaired`
(arXiv:2407.12928, Cor 3.6). -/
theorem reindexSys_basePaired {n : ℕ} (τ : ETm n) : (reindexSys τ).BasePaired :=
  SosSystem.weaken_basePaired (diophOf_basePaired τ) _

/-- The uniform base majorant of arXiv:2407.12928, Corollary 3.6: an input-only
`ETm n` whose value dominates the `diophOf` encoding's value majorant `valBound`
and every per-witness bound `bound i`. Realised as the `eraListSum` of those
terms, so each summand is at most the whole sum. The count of `eraCountPred_eval`
is taken at this base side. -/
def eraBaseBound {n : ℕ} (τ : ETm n) : ETm n :=
  eraListSum ((diophOf τ).valBound ::
    (List.finRange (diophOf τ).witArity).map (diophOf τ).bound)

/-- The base majorant dominates the value majorant `valBound`
(arXiv:2407.12928, Cor 3.6): `valBound` is the head summand of `eraBaseBound`. -/
theorem eraBaseBound_valBound {n : ℕ} (τ : ETm n) (ctx : Fin n → ℕ) :
    Tm.eval eraInterp (diophOf τ).valBound ctx
      ≤ Tm.eval eraInterp (eraBaseBound τ) ctx := by
  rw [eraBaseBound, eraListSum_eval, List.map_cons]
  exact List.le_sum_of_mem (List.mem_cons_self ..)

/-- The base majorant dominates every per-witness bound `bound i`
(arXiv:2407.12928, Cor 3.6): each `bound i` is a tail summand of `eraBaseBound`. -/
theorem eraBaseBound_bound {n : ℕ} (τ : ETm n) (ctx : Fin n → ℕ)
    (i : Fin (diophOf τ).witArity) :
    Tm.eval eraInterp ((diophOf τ).bound i) ctx
      ≤ Tm.eval eraInterp (eraBaseBound τ) ctx := by
  rw [eraBaseBound, eraListSum_eval, List.map_cons, List.map_map]
  refine List.le_sum_of_mem ?_
  refine List.mem_cons_of_mem _ ?_
  exact List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩

/-- The base coordinate bound of arXiv:2407.12928, Corollary 3.6: every cube
point `x` at which the re-indexed system vanishes has all coordinates strictly
below the base majorant `eraBaseBound`. The output coordinate `x 0` equals
`Tm.eval eraInterp τ ctx`, below `valBound` (the value-majorisation conjunct of
`diophOf_encodes`); each witness coordinate `x (1 + i)` is below `bound i`
(`diophOf_bound`); both are dominated by `eraBaseBound`. -/
theorem reindexSys_coord_bound {n : ℕ} (τ : ETm n) (ctx : Fin n → ℕ)
    (x : Fin (1 + (diophOf τ).witArity) → ℕ)
    (hx0 : SosSystem.eval (reindexSys τ) (Fin.append ctx x) = 0) :
    ∀ c, x c < Tm.eval eraInterp (eraBaseBound τ) ctx := by
  rw [reindexSys_eval] at hx0
  have hval : x 0 < Tm.eval eraInterp (eraBaseBound τ) ctx := by
    have hgraph : x 0 = Tm.eval eraInterp τ ctx :=
      (diophOf_encodes τ).1 ctx (x 0) (fun i => x (Fin.natAdd 1 i)) hx0
    calc x 0 = Tm.eval eraInterp τ ctx := hgraph
      _ < Tm.eval eraInterp (diophOf τ).valBound ctx := (diophOf_encodes τ).2.2.2 ctx
      _ ≤ Tm.eval eraInterp (eraBaseBound τ) ctx := eraBaseBound_valBound τ ctx
  have hwit : ∀ i, x (Fin.natAdd 1 i) < Tm.eval eraInterp (eraBaseBound τ) ctx := by
    intro i
    calc x (Fin.natAdd 1 i)
        < Tm.eval eraInterp ((diophOf τ).bound i) ctx :=
          diophOf_bound τ ctx (x 0) (fun i => x (Fin.natAdd 1 i)) hx0 i
      _ ≤ Tm.eval eraInterp (eraBaseBound τ) ctx := eraBaseBound_bound τ ctx i
  intro c
  refine Fin.addCases ?_ ?_ c
  · intro j
    rw [Subsingleton.elim j 0]
    exact hval
  · intro i
    exact hwit i

/-- The input-side re-indexing embedding of arXiv:2407.12928, Corollary 3.6: the
sibling of `reindexEmb` that, additionally to the output, moves the `r` counted
inputs of a `diophOf` encoding from the parameter side to the cube side. It keeps
the `p` parameters in the input block, sends the `r` counted inputs to cube slots
`0 … r-1`, the output index `p + r` to cube slot `r`, and witness `k` to cube slot
`r + 1 + k`, realising `Fin ((p + r) + 1 + witArity) → Fin (p + (r + 1 + witArity))`.
Built from `Fin.addCases` / `Fin.lastCases`, so it executes. -/
def reindexInputEmb (p r witArity : ℕ) :
    Fin ((p + r) + 1 + witArity) → Fin (p + (r + 1 + witArity)) :=
  Fin.addCases
    (Fin.lastCases (Fin.natAdd p (Fin.castAdd witArity (Fin.last r)))
      (Fin.addCases
        (fun ip => Fin.castAdd (r + 1 + witArity) ip)
        (fun ir => Fin.natAdd p (Fin.castAdd witArity (Fin.castAdd 1 ir)))))
    (fun k => Fin.natAdd p (Fin.natAdd (r + 1) k))

/-- The input-side re-indexed context of arXiv:2407.12928, Corollary 3.6: read a
cube point `a : Fin (r + 1 + witArity) → ℕ` (moved inputs, then output, then
witnesses) together with the `p` parameters `ctx` into the `diophOf` encoding's
context. The `diophOf` inputs are `ctx` extended by the moved inputs
`a (castAdd … i)`; the output is `a (castAdd witArity (Fin.last r))`; the witnesses
are `a (natAdd (r + 1) i)`. -/
def reindexInputCtx {p r : ℕ} (pred : ETm (p + r)) (ctx : Fin p → ℕ)
    (a : Fin (r + 1 + (diophOf pred).witArity) → ℕ) :
    Fin ((p + r) + 1 + (diophOf pred).witArity) → ℕ :=
  (diophOf pred).ctx
    (Fin.append ctx (fun i => a (Fin.castAdd (diophOf pred).witArity (Fin.castAdd 1 i))))
    (a (Fin.castAdd (diophOf pred).witArity (Fin.last r)))
    (fun i => a (Fin.natAdd (r + 1) i))

/-- Injectivity of `reindexInputEmb`: the `p` parameters land in the input block,
while the `r` counted inputs, the output slot, and the witnesses land at distinct
cube slots (`0 … r-1`, `r`, and `r + 1 + k`). -/
theorem reindexInputEmb_injective (p r witArity : ℕ) :
    Function.Injective (reindexInputEmb p r witArity) := by
  intro a b hab
  unfold reindexInputEmb at hab
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
          induction jb using Fin.addCases with
          | left ipb =>
            simp only [Fin.lastCases_last, Fin.lastCases_castSucc, Fin.addCases_left,
              Fin.ext_iff, Fin.val_natAdd, Fin.val_castAdd, Fin.val_last] at hab
            omega
          | right irb =>
            simp only [Fin.lastCases_last, Fin.lastCases_castSucc, Fin.addCases_right,
              Fin.ext_iff, Fin.val_natAdd, Fin.val_castAdd, Fin.val_last] at hab
            omega
      | cast ja =>
        induction ja using Fin.addCases with
        | left ipa =>
          induction ib using Fin.lastCases with
          | last =>
            simp only [Fin.lastCases_last, Fin.lastCases_castSucc, Fin.addCases_left,
              Fin.ext_iff, Fin.val_natAdd, Fin.val_castAdd, Fin.val_last] at hab
            omega
          | cast jb =>
            induction jb using Fin.addCases with
            | left ipb =>
              simp only [Fin.lastCases_castSucc, Fin.addCases_left] at hab
              rw [Fin.castAdd_injective _ _ hab]
            | right irb =>
              simp only [Fin.lastCases_castSucc, Fin.addCases_left, Fin.addCases_right,
                Fin.ext_iff, Fin.val_castAdd, Fin.val_natAdd] at hab
              omega
        | right ira =>
          induction ib using Fin.lastCases with
          | last =>
            simp only [Fin.lastCases_last, Fin.lastCases_castSucc, Fin.addCases_right,
              Fin.ext_iff, Fin.val_natAdd, Fin.val_castAdd, Fin.val_last] at hab
            omega
          | cast jb =>
            induction jb using Fin.addCases with
            | left ipb =>
              simp only [Fin.lastCases_castSucc, Fin.addCases_right, Fin.addCases_left,
                Fin.ext_iff, Fin.val_castAdd, Fin.val_natAdd] at hab
              omega
            | right irb =>
              simp only [Fin.lastCases_castSucc, Fin.addCases_right] at hab
              have h := Fin.natAdd_injective _ _ hab
              have h2 := Fin.castAdd_injective _ _ h
              have h3 := Fin.castAdd_injective _ _ h2
              rw [h3]
    | right kb =>
      simp only [Fin.addCases_left, Fin.addCases_right] at hab
      induction ia using Fin.lastCases with
      | last =>
        simp only [Fin.lastCases_last, Fin.ext_iff, Fin.val_natAdd, Fin.val_castAdd,
          Fin.val_last] at hab
        omega
      | cast ja =>
        induction ja using Fin.addCases with
        | left ipa =>
          simp only [Fin.lastCases_castSucc, Fin.addCases_left, Fin.ext_iff, Fin.val_castAdd,
            Fin.val_natAdd] at hab
          omega
        | right ira =>
          simp only [Fin.lastCases_castSucc, Fin.addCases_right, Fin.ext_iff, Fin.val_natAdd,
            Fin.val_castAdd] at hab
          omega
  | right ka =>
    induction b using Fin.addCases with
    | left ib =>
      simp only [Fin.addCases_left, Fin.addCases_right] at hab
      induction ib using Fin.lastCases with
      | last =>
        simp only [Fin.lastCases_last, Fin.ext_iff, Fin.val_natAdd, Fin.val_castAdd,
          Fin.val_last] at hab
        omega
      | cast jb =>
        induction jb using Fin.addCases with
        | left ipb =>
          simp only [Fin.lastCases_castSucc, Fin.addCases_left, Fin.ext_iff, Fin.val_castAdd,
            Fin.val_natAdd] at hab
          omega
        | right irb =>
          simp only [Fin.lastCases_castSucc, Fin.addCases_right, Fin.ext_iff, Fin.val_natAdd,
            Fin.val_castAdd] at hab
          omega
    | right kb =>
      simp only [Fin.addCases_right] at hab
      have h := Fin.natAdd_injective _ _ hab
      have h2 := Fin.natAdd_injective _ _ h
      rw [h2]

/-- The input-side re-indexing identity of arXiv:2407.12928, Corollary 3.6:
precomposing the cube context `Fin.append ctx a` with `reindexInputEmb` recovers
the `diophOf` context `reindexInputCtx`. The cube-side block of `Fin.append ctx a`
is read at slots `0 … r-1` for the moved inputs, slot `r` for the output, and slots
`r + 1 + i` for the witnesses. -/
theorem append_comp_reindexInputEmb {p r : ℕ} (pred : ETm (p + r)) (ctx : Fin p → ℕ)
    (a : Fin (r + 1 + (diophOf pred).witArity) → ℕ) :
    (Fin.append ctx a) ∘ reindexInputEmb p r (diophOf pred).witArity
      = reindexInputCtx pred ctx a := by
  refine funext (fun z => ?_)
  simp only [Function.comp_apply, reindexInputEmb, reindexInputCtx, DiophEnc.ctx]
  refine Fin.addCases ?_ ?_ z
  · intro io
    refine Fin.lastCases ?_ ?_ io
    · simp only [Fin.addCases_left, Fin.lastCases_last, Fin.append_right, Fin.append_left,
        Fin.snoc_last]
    · intro j
      refine Fin.addCases ?_ ?_ j
      · intro ip
        simp only [Fin.addCases_left, Fin.lastCases_castSucc, Fin.append_left, Fin.snoc_castSucc]
      · intro ir
        simp only [Fin.addCases_left, Fin.addCases_right, Fin.lastCases_castSucc,
          Fin.append_right, Fin.snoc_castSucc, Fin.append_left]
  · intro i
    simp only [Fin.addCases_right, Fin.append_right]

/-- The input-side re-indexed system of arXiv:2407.12928, Corollary 3.6: the
`diophOf` encoding's sum-of-squares system, weakened along `reindexInputEmb` so the
moved inputs, the output slot, and the witnesses become the cube-side coordinates,
with an appended `sqDist [output] []` atom pinning the output coordinate to `0`
(the empty `SimpleSum` evaluates to `0`). The mirror image of the `diophZero` atom
`sqDist [] [var]`. Phase E (`sepReduce`, `eraCount`) operates on this system. -/
def reindexInputSys {p r : ℕ} (pred : ETm (p + r)) :
    SosSystem (p + (r + 1 + (diophOf pred).witArity)) :=
  (diophOf pred).sys.weaken (reindexInputEmb p r (diophOf pred).witArity)
    ++ [SosTerm.sqDist
        [SimpleMonomial.var (Fin.natAdd p (Fin.castAdd (diophOf pred).witArity (Fin.last r)))] []]

/-- The input-side re-indexing bridge of arXiv:2407.12928, Corollary 3.6: evaluating
the re-indexed system at the cube context `Fin.append ctx a` equals evaluating the
original `diophOf` system at the re-indexed context `reindexInputCtx`, plus the pin
atom's value (the square of the output coordinate `a outCubeIdx`). Composes
`SosSystem.eval_append`, `SosSystem.eval_weaken` (the embedding `reindexInputEmb` is
injective), and `append_comp_reindexInputEmb`. -/
theorem reindexInputSys_eval {p r : ℕ} (pred : ETm (p + r)) (ctx : Fin p → ℕ)
    (a : Fin (r + 1 + (diophOf pred).witArity) → ℕ) :
    SosSystem.eval (reindexInputSys pred) (Fin.append ctx a)
      = SosSystem.eval (diophOf pred).sys (reindexInputCtx pred ctx a)
        + SosTerm.eval
            (.sqDist
              [SimpleMonomial.var
                (Fin.natAdd p (Fin.castAdd (diophOf pred).witArity (Fin.last r)))] [])
            (Fin.append ctx a) := by
  rw [reindexInputSys, SosSystem.eval_append,
    SosSystem.eval_weaken _ _ (reindexInputEmb_injective p r (diophOf pred).witArity),
    append_comp_reindexInputEmb]
  simp only [SosSystem.eval, Nat.add_zero]

/-- The input-side re-indexing vanishing criterion of arXiv:2407.12928, Corollary
3.6: the re-indexed system vanishes at the cube context exactly when the original
`diophOf` system vanishes at the re-indexed context and the output coordinate
`a outCubeIdx` is `0`, where `outCubeIdx := Fin.castAdd witArity (Fin.last r)` is the
output position within the cube point `a`. From `reindexInputSys_eval`,
`Nat.add_eq_zero_iff`, and `SosTerm.sqDist_eval_eq_zero_iff` (the empty `SimpleSum`
evaluates to `0`, so the pin forces the output coordinate to `0`). -/
theorem reindexInputSys_eval_zero_iff {p r : ℕ} (pred : ETm (p + r)) (ctx : Fin p → ℕ)
    (a : Fin (r + 1 + (diophOf pred).witArity) → ℕ) :
    SosSystem.eval (reindexInputSys pred) (Fin.append ctx a) = 0
      ↔ SosSystem.eval (diophOf pred).sys (reindexInputCtx pred ctx a) = 0
        ∧ a (Fin.castAdd (diophOf pred).witArity (Fin.last r)) = 0 := by
  rw [reindexInputSys_eval, Nat.add_eq_zero_iff,
    SosTerm.sqDist_eval_eq_zero_iff]
  refine and_congr_right (fun _ => ?_)
  simp only [SimpleSum.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Nat.add_zero, SimpleMonomial.var_eval, Fin.append_right]

/-- The input-side re-indexed system inherits the polynomial-exponent-zero
invariant of the `diophOf` encoding (`diophOf_polyExpZero`): the weakened part
through `SosSystem.weaken_polyExpZero`, and the appended `sqDist [output] []` pin
atom (the mirror of the `diophZero` atom `sqDist [] [var]`) through the singleton
sum / atom helpers (arXiv:2407.12928, Cor 3.6). -/
theorem reindexInputSys_polyExpZero {p r : ℕ} (pred : ETm (p + r)) :
    (reindexInputSys pred).PolyExpZero :=
  (SosSystem.polyExpZero_append _ _).mpr
    ⟨SosSystem.weaken_polyExpZero (diophOf_polyExpZero pred) _,
      SosSystem.cons_polyExpZero
        (SosTerm.sqDist_polyExpZero
          (SimpleSum.singleton_polyExpZero (SimpleMonomial.var_polyExpZero _))
          SimpleSum.nil_polyExpZero)
        SosSystem.nil_polyExpZero⟩

/-- The input-side re-indexed system inherits the coefficient-variable-product
invariant of the `diophOf` encoding (`diophOf_coeffVarProduct`): the weakened part
through `SosSystem.weaken_coeffVarProduct`, and the appended `sqDist [output] []`
pin atom (the mirror of the `diophZero` atom `sqDist [] [var]`) through the
singleton sum / atom helpers (arXiv:2407.12928, Cor 3.6). -/
theorem reindexInputSys_coeffVarProduct {p r : ℕ} (pred : ETm (p + r)) :
    (reindexInputSys pred).CoeffVarProduct :=
  (SosSystem.coeffVarProduct_append _ _).mpr
    ⟨SosSystem.weaken_coeffVarProduct (diophOf_coeffVarProduct pred) _,
      SosSystem.cons_coeffVarProduct
        (SosTerm.sqDist_coeffVarProduct
          (SimpleSum.singleton_coeffVarProduct (SimpleMonomial.var_coeffVarProduct _))
          SimpleSum.nil_coeffVarProduct)
        SosSystem.nil_coeffVarProduct⟩

/-- The input-side re-indexed system inherits the base-paired invariant of the
`diophOf` encoding (`diophOf_basePaired`): the weakened part through
`SosSystem.weaken_basePaired`, and the appended `sqDist [output] []` pin atom (the
mirror of the `diophZero` atom `sqDist [] [var]`) through the singleton sum / atom
helpers (arXiv:2407.12928, Cor 3.6). -/
theorem reindexInputSys_basePaired {p r : ℕ} (pred : ETm (p + r)) :
    (reindexInputSys pred).BasePaired :=
  (SosSystem.basePaired_append _ _).mpr
    ⟨SosSystem.weaken_basePaired (diophOf_basePaired pred) _,
      SosSystem.cons_basePaired
        (SosTerm.sqDist_basePaired
          (SimpleSum.singleton_basePaired (SimpleMonomial.var_basePaired _))
          SimpleSum.nil_basePaired)
        SosSystem.nil_basePaired⟩

/-- The input-side base coordinate bound of arXiv:2407.12928, Corollary 3.6: every
cube point `a` at which the input-side re-indexed system vanishes has all
coordinates strictly below the supplied majorant `B`. The output coordinate (cube
slot `r`) is pinned to `0` by `reindexInputSys_eval_zero_iff`; each witness
coordinate (cube slots `r + 1 + k`) is below its bound `bound k`
(`diophOf_bound`) hence below `B` by `hbnd`; each moved-input coordinate (cube
slots `0 … r-1`) is below `B` by the supplied hypothesis `hmoved` (the encoding
does not bound these free inputs). -/
theorem reindexInputSys_coord_bound {p r : ℕ} (pred : ETm (p + r)) (ctx : Fin p → ℕ)
    (B : ℕ) (hpos : 0 < B)
    (a : Fin (r + 1 + (diophOf pred).witArity) → ℕ)
    (h0 : SosSystem.eval (reindexInputSys pred) (Fin.append ctx a) = 0)
    (hbnd : ∀ i : Fin (diophOf pred).witArity,
        Tm.eval eraInterp ((diophOf pred).bound i)
          (Fin.append ctx
            (fun j => a (Fin.castAdd (diophOf pred).witArity (Fin.castAdd 1 j)))) ≤ B)
    (hmoved : ∀ i : Fin r,
        a (Fin.castAdd (diophOf pred).witArity (Fin.castAdd 1 i)) < B) :
    ∀ c, a c < B := by
  rw [reindexInputSys_eval_zero_iff] at h0
  obtain ⟨hsys, hout⟩ := h0
  have hwit : ∀ i : Fin (diophOf pred).witArity, a (Fin.natAdd (r + 1) i) < B := by
    intro i
    have hbi := diophOf_bound pred
      (Fin.append ctx
        (fun j => a (Fin.castAdd (diophOf pred).witArity (Fin.castAdd 1 j))))
      (a (Fin.castAdd (diophOf pred).witArity (Fin.last r)))
      (fun i => a (Fin.natAdd (r + 1) i)) hsys i
    exact lt_of_lt_of_le hbi (hbnd i)
  intro c
  refine Fin.addCases ?_ ?_ c
  · intro io
    refine Fin.lastCases ?_ ?_ io
    · rw [hout]; exact hpos
    · intro j
      exact hmoved j
  · intro i
    exact hwit i

/-- The ambient-parameter slot `2 + i` of the hit-gap context `Fin ((2 + k) + 1)`,
as a `Fin`. The hit-gap context lays out `[x, n, ambient(k), j]`, so ambient
parameter `i` lives at position `2 + i`. -/
def ambIdx {k : ℕ} (i : Fin k) : Fin ((2 + k) + 1) :=
  ⟨2 + (i : ℕ), by omega⟩

/-- The coding-base renaming for the hit-gap predicate: the `1 + k` slots of the
coding-base term `ATerm` (loop bound `n` then the `k` ambient parameters) are sent
into the hit-gap context `[x, n, ambient(k), j]`. Slot `0` (`n`) maps to variable
`1`; ambient slot `1 + i` maps to variable `2 + i` (arXiv:2606.09336, Claim 3). -/
def hitGapBaseSub {k : ℕ} : Fin (1 + k) → ETm ((2 + k) + 1) :=
  Fin.addCases (fun _ : Fin 1 => (Tm.var 1 : ETm ((2 + k) + 1)))
    (fun i : Fin k => Tm.var (ambIdx i))

/-- The recurrence-step renaming for the hit-gap predicate: the `2 + k` slots of
the step term `stepTm` (index `j`, value `v`, then the `k` ambient parameters) are
sent into the hit-gap context. Slot `0` (`j`) maps to `jTerm`; slot `1` (`v`) maps
to `digit` (the `j`-th base-`A` digit of `x`); ambient slot `2 + i` maps to
variable `2 + i` (arXiv:2606.09336, Claim 3). -/
def hitGapStepSub {k : ℕ} (jTerm digit : ETm ((2 + k) + 1)) :
    Fin (2 + k) → ETm ((2 + k) + 1) :=
  Fin.addCases
    (fun i : Fin 2 => if (i : ℕ) = 0 then jTerm else digit)
    (fun i : Fin k => Tm.var (ambIdx i))

/-- The coding base `A` denotation of the hit-gap predicate: the coding-base term
`ATerm` evaluated at the loop bound `n = ctx 1` together with the ambient
parameters read off the hit-gap context (arXiv:2606.09336, Claim 3). -/
def hitGapBaseCtx {k : ℕ} (ctx : Fin ((2 + k) + 1) → ℕ) : Fin (1 + k) → ℕ :=
  Fin.addCases (fun _ : Fin 1 => ctx 1) (fun i : Fin k => ctx (ambIdx i))

/-- The recurrence-step context of the hit-gap predicate: the index `j` and value
`v` together with the ambient parameters read off the hit-gap context, in the slot
order the step term `stepTm` expects (arXiv:2606.09336, Claim 3). -/
def hitGapStepCtx {k : ℕ} (ctx : Fin ((2 + k) + 1) → ℕ) (j v : ℕ) : Fin (2 + k) → ℕ :=
  Fin.addCases (fun i : Fin 2 => if (i : ℕ) = 0 then j else v)
    (fun i : Fin k => ctx (ambIdx i))

/-- The hit-gap predicate of arXiv:2606.09336, Claim 3, as a pure `Era` arithmetic
term over the context `[x, n, ambient(k), j]` (`x` the code, `n` the loop bound, `k`
ambient parameters, `j` the counted index). It evaluates to `0` exactly when index
`j` hits for code `x` (consecutive base-`A` digits `a_j`, `a_{j+1}` satisfy
`a_{j+1} = step j a_j`) and `j < n`. The two truncated-subtraction differences
`(lhs ∸ rhs) + (rhs ∸ lhs)` vanish iff `lhs = rhs`, encoding the digit-step
equation; the range gap `(j + 1) ∸ n` vanishes iff `j < n`. The coding base `A` and
the step are supplied as the terms `ATerm` and `stepTm`. -/
def hitGapTm {k : ℕ} (stepTm : ETm (2 + k)) (ATerm : ETm (1 + k)) :
    ETm ((2 + k) + 1) :=
  let Asub : ETm ((2 + k) + 1) := ATerm.subst hitGapBaseSub
  let jVar : ETm ((2 + k) + 1) := Tm.var (Fin.last (2 + k))
  let xVar : ETm ((2 + k) + 1) := Tm.var 0
  let nVar : ETm ((2 + k) + 1) := Tm.var 1
  let digit : ETm ((2 + k) + 1) := (xVar /ᵉ (Asub ^ᵉ jVar)) %ᵉ Asub
  let lhs : ETm ((2 + k) + 1) := stepTm.subst (hitGapStepSub jVar digit)
  let rhs : ETm ((2 + k) + 1) :=
    (xVar /ᵉ (Asub ^ᵉ (jVar +ᵉ eraNumeral 1))) %ᵉ Asub
  let gap : ETm ((2 + k) + 1) := (lhs ∸ᵉ rhs) +ᵉ (rhs ∸ᵉ lhs)
  let rangeGap : ETm ((2 + k) + 1) := (jVar +ᵉ eraNumeral 1) ∸ᵉ nVar
  gap +ᵉ rangeGap

/-- The hit-gap predicate vanishes exactly at hitting indices below the loop
bound (arXiv:2606.09336, Claim 3): `hitGapTm stepTm ATerm` evaluates to `0` at the
context `[x, n, ambient(k), j]` iff index `j = ctx (Fin.last (2 + k))` hits for code
`x = ctx 0` with respect to the supplied step and coding base, and `j < n = ctx 1`.
The step is `fun j v => Tm.eval eraInterp stepTm (hitGapStepCtx ctx j v)` and the
coding base is `Tm.eval eraInterp ATerm (hitGapBaseCtx ctx)`. -/
theorem hitGapTm_eval_zero_iff {k : ℕ} (stepTm : ETm (2 + k)) (ATerm : ETm (1 + k))
    (ctx : Fin ((2 + k) + 1) → ℕ) :
    Tm.eval eraInterp (hitGapTm stepTm ATerm) ctx = 0
      ↔ GebLean.EraRecurrence.hitsAt
            (fun j v => Tm.eval eraInterp stepTm (hitGapStepCtx ctx j v))
            (Tm.eval eraInterp ATerm (hitGapBaseCtx ctx))
            (ctx 0) (ctx (Fin.last (2 + k)))
        ∧ ctx (Fin.last (2 + k)) < ctx 1 := by
  have hbase : (fun i => Tm.eval eraInterp (hitGapBaseSub i) ctx)
      = hitGapBaseCtx (k := k) ctx := by
    funext i
    refine Fin.addCases (fun a => ?_) (fun a => ?_) i <;>
      simp [hitGapBaseSub, hitGapBaseCtx, Tm.eval]
  have hstep : ∀ jT dT : ETm ((2 + k) + 1),
      (fun i => Tm.eval eraInterp (hitGapStepSub jT dT i) ctx)
        = hitGapStepCtx ctx (Tm.eval eraInterp jT ctx) (Tm.eval eraInterp dT ctx) := by
    intro jT dT
    funext i
    refine Fin.addCases (fun a => ?_) (fun a => ?_) i
    · simp only [hitGapStepSub, hitGapStepCtx, Fin.addCases_left]
      split <;> rfl
    · simp only [hitGapStepSub, hitGapStepCtx, Fin.addCases_right, Tm.eval]
  simp only [hitGapTm, eadd_eval, etsub_eval, ediv_eval, emod_eval, epow_eval, eraInterp,
    fcons, eraNumeral_eval, Tm.eval_subst, hbase, hstep, Tm.eval]
  rw [GebLean.EraRecurrence.hitsAt, Nat.add_eq_zero_iff]
  omega

/-- The `j`-dropping substitution of arXiv:2407.12928, Corollary 3.6 (input-side):
rewrite a term over the hit-gap context `[x, n, ambient(k), j]` to one over the
parameter context `[x, n, ambient(k)]` by replacing the moved input slot `j`
(`Fin.last (2 + k)`) with the loop bound `n` (variable `1`) and keeping every
parameter slot as itself. Used to lift the `j`-dependent witness bounds of the
hit-gap predicate's encoding to `j := n`, the largest value a counted index can
take (`hitGapTm_eval_zero_iff` forces `j < n`). -/
def dropJ {k : ℕ} (t : ETm ((2 + k) + 1)) : ETm (2 + k) :=
  t.subst (Fin.lastCases (Tm.var 1) (fun i => Tm.var i))

/-- The `j`-dropping substitution evaluates a term at `j := n` (arXiv:2407.12928,
Cor 3.6): `dropJ t` at the parameter context `ctx` equals `t` at the hit-gap
context obtained by appending `ctx 1` (the loop bound `n`) in the moved-input
slot, i.e. `Fin.snoc ctx (ctx 1)`. -/
theorem dropJ_eval {k : ℕ} (t : ETm ((2 + k) + 1)) (ctx : Fin (2 + k) → ℕ) :
    Tm.eval eraInterp (dropJ t) ctx = Tm.eval eraInterp t (Fin.snoc ctx (ctx 1)) := by
  rw [dropJ, Tm.eval_subst]
  congr 1
  funext i
  refine Fin.lastCases ?_ ?_ i
  · simp only [Fin.lastCases_last, Fin.snoc_last, Tm.eval]
  · intro j
    simp only [Fin.lastCases_castSucc, Fin.snoc_castSucc, Tm.eval]

/-- The input-side base majorant of arXiv:2407.12928, Corollary 3.6: a
parameter-only `ETm (2 + k)` whose value dominates, at every cube zero of the
hit-gap predicate's input-side re-indexed system, the moved input `j` (forced
`< n`), the pinned output `0`, and each `j`-dependent witness bound `bound i`
lifted to `j := n` (`dropJ`). The head summand `n + 1` dominates `n`; each tail
summand `dropJ (eraMajorant …)` dominates its witness bound for any `j ≤ n` by
`eraMajorant_spec`/`eraMajorant_mono`. The count of `eraHitCount_cubeCount` is
taken at this base side. -/
def eraHitBase {k : ℕ} (stepTm : ETm (2 + k)) (ATerm : ETm (1 + k)) : ETm (2 + k) :=
  eraListSum ((Tm.var 1 +ᵉ eraNumeral 1)
    :: dropJ (eraMajorant (diophOf (hitGapTm stepTm ATerm)).valBound)
    :: (List.finRange (diophOf (hitGapTm stepTm ATerm)).witArity).map
        (fun i => dropJ (eraMajorant ((diophOf (hitGapTm stepTm ATerm)).bound i))))

/-- The input-side base majorant dominates the moved input `n` (arXiv:2407.12928,
Cor 3.6): the loop bound `n = ctx 1` is below the head summand `n + 1` of the
`eraListSum`. -/
theorem eraHitBase_n {k : ℕ} (stepTm : ETm (2 + k)) (ATerm : ETm (1 + k))
    (ctx : Fin (2 + k) → ℕ) :
    Tm.eval eraInterp (Tm.var 1) ctx < Tm.eval eraInterp (eraHitBase stepTm ATerm) ctx := by
  calc Tm.eval eraInterp (Tm.var 1) ctx
      < Tm.eval eraInterp (Tm.var 1 +ᵉ eraNumeral 1) ctx := by
        simp only [eadd_eval, eraNumeral_eval, eraInterp, fcons, Tm.eval]; omega
    _ ≤ Tm.eval eraInterp (eraHitBase stepTm ATerm) ctx := by
        rw [eraHitBase, eraListSum_eval, List.map_cons]
        exact List.le_sum_of_mem (List.mem_cons_self ..)

/-- The input-side base majorant is positive (arXiv:2407.12928, Cor 3.6): its
head summand `n + 1` is at least `1` and is a summand of the `eraListSum`. -/
theorem eraHitBase_pos {k : ℕ} (stepTm : ETm (2 + k)) (ATerm : ETm (1 + k))
    (ctx : Fin (2 + k) → ℕ) :
    0 < Tm.eval eraInterp (eraHitBase stepTm ATerm) ctx :=
  Nat.lt_of_le_of_lt (Nat.zero_le _) (eraHitBase_n stepTm ATerm ctx)

/-- The input-side base majorant dominates each `j`-dependent witness bound at any
`j₀ ≤ n` (arXiv:2407.12928, Cor 3.6): `bound i` at the hit-gap context with moved
input `j₀` is strictly below `eraMajorant (bound i)` there (`eraMajorant_spec`),
which is monotone up to `j := n` (`eraMajorant_mono`), equals the tail summand
`dropJ (eraMajorant (bound i))` (`dropJ_eval`), and is at most the whole
`eraListSum`. -/
theorem eraHitBase_bound {k : ℕ} (stepTm : ETm (2 + k)) (ATerm : ETm (1 + k))
    (ctx : Fin (2 + k) → ℕ) (i : Fin (diophOf (hitGapTm stepTm ATerm)).witArity)
    (j₀ : ℕ) (hj₀ : j₀ ≤ ctx 1) :
    Tm.eval eraInterp ((diophOf (hitGapTm stepTm ATerm)).bound i) (Fin.snoc ctx j₀)
      ≤ Tm.eval eraInterp (eraHitBase stepTm ATerm) ctx := by
  set bnd := (diophOf (hitGapTm stepTm ATerm)).bound i with hbnd
  refine Nat.le_of_lt ?_
  calc Tm.eval eraInterp bnd (Fin.snoc ctx j₀)
      < Tm.eval eraInterp (eraMajorant bnd) (Fin.snoc ctx j₀) := eraMajorant_spec _ _
    _ ≤ Tm.eval eraInterp (eraMajorant bnd) (Fin.snoc ctx (ctx 1)) := by
        refine eraMajorant_mono bnd (fun c => ?_)
        refine Fin.lastCases ?_ ?_ c
        · simp only [Fin.snoc_last]; exact hj₀
        · intro c'; simp only [Fin.snoc_castSucc]; exact Nat.le_refl _
    _ = Tm.eval eraInterp (dropJ (eraMajorant bnd)) ctx := (dropJ_eval _ ctx).symm
    _ ≤ Tm.eval eraInterp (eraHitBase stepTm ATerm) ctx := by
        rw [eraHitBase, eraListSum_eval, List.map_cons, List.map_cons, List.map_map]
        refine List.le_sum_of_mem ?_
        refine List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ?_)
        exact List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩

open GebLean.EraCompleteness in
/-- The inner hit counter of arXiv:2407.12928, Corollary 3.6 and arXiv:2606.09336,
Claim 3: for the hit-gap predicate `hitGapTm stepTm ATerm` over the context
`[x, n, ambient(k)]`, the `Era` term whose value at `ctx` is the number of cube
points — moved input `j`, pinned output, and `diophOf` witnesses — at which the
input-side re-indexed system `reindexInputSys (hitGapTm …)` vanishes, i.e. the
number of indices `j < n` that hit for code `x`. It is the count read-off
`eraCount` of the Lemma 3.5-reduced input-side re-indexed system, taken at the
enlarged side `eraTheta` over the input-side base majorant `eraHitBase` (so the
unique chain witness is a valid cube coordinate) and modulus `eraW + 1`. -/
def eraHitCount {k : ℕ} (stepTm : ETm (2 + k)) (ATerm : ETm (1 + k)) : ETm (2 + k) :=
  eraCount (reindexInputSys (hitGapTm stepTm ATerm))
    (eraTheta (reindexInputSys (hitGapTm stepTm ATerm)) (eraHitBase stepTm ATerm))
    (eraW (reindexInputSys (hitGapTm stepTm ATerm))
        (eraTheta (reindexInputSys (hitGapTm stepTm ATerm)) (eraHitBase stepTm ATerm))
      +ᵉ eraNumeral 1)

open GebLean.EraCompleteness in
/-- The inner hit-counting identity of arXiv:2407.12928, Corollary 3.6 and
arXiv:2606.09336, Claim 3: `eraHitCount stepTm ATerm` evaluates to the number of
cube points — moved input `j`, pinned output, and `diophOf` witnesses — at side
`eraHitBase` at which the input-side re-indexed system vanishes. The proof composes
the count read-off `eraCount_eval` at the enlarged side (its block bound by
`eraW_spec`, its positivity by the `+ 1` modulus), the fibre collapse
`reducedCount_eq` (its chain-witness bound by `eraTheta_spec` over the input-side
coordinate bound `reindexInputSys_coord_bound`), and the shell collapse
`predCount_side_eq` (its shell emptiness by the same coordinate bound). The
input-side coordinate bound is discharged from `eraHitBase`: the output slot is
pinned to `0`, the witnesses are below their `j`-dependent bounds lifted to `j := n`
(`eraHitBase_bound`), and the moved input `j` is forced `< n` by
`hitGapTm_eval_zero_iff` then dominated by `eraHitBase_n`. The system is kept as
`reindexInputSys`, the form consumed downstream via `reindexInputSys_eval_zero_iff`. -/
theorem eraHitCount_cubeCount {k : ℕ} (stepTm : ETm (2 + k)) (ATerm : ETm (1 + k))
    (ctx : Fin (2 + k) → ℕ) :
    Tm.eval eraInterp (eraHitCount stepTm ATerm) ctx
      = ((GebLean.EraHypercube.cubePoints (1 + 1 + (diophOf (hitGapTm stepTm ATerm)).witArity)
            (Tm.eval eraInterp (eraHitBase stepTm ATerm) ctx)).filter
          (fun a => SosSystem.eval (reindexInputSys (hitGapTm stepTm ATerm))
            (Fin.append ctx a) = 0)).card := by
  set pred := hitGapTm stepTm ATerm with hpred
  set sysW := reindexInputSys pred with hsysW
  set tBaseT := eraHitBase stepTm ATerm with htBaseT
  set tθT := eraTheta sysW tBaseT with htθT
  set tBase := Tm.eval eraInterp tBaseT ctx with htBase
  set tθ := Tm.eval eraInterp tθT ctx with htθ
  have hzero : sysW.PolyExpZero := reindexInputSys_polyExpZero pred
  have hcoeff : sysW.CoeffVarProduct := reindexInputSys_coeffVarProduct pred
  have hbase : sysW.BasePaired := reindexInputSys_basePaired pred
  have ht : 0 < tθ := by rw [htθ, htθT, eraTheta]; exact eraMajorant_pos _ ctx
  have hwpos : 0 < Tm.eval eraInterp (eraW sysW tθT +ᵉ eraNumeral 1) ctx := by
    rw [eadd, Tm.eval, eraInterp]
    simp only [fcons, eraNumeral_eval]
    omega
  -- the moved index of any cube zero is forced below the loop bound `n = ctx 1`
  have hmovedlt : ∀ a : Fin (1 + 1 + (diophOf pred).witArity) → ℕ,
      SosSystem.eval sysW (Fin.append ctx a) = 0 →
        a (Fin.castAdd (diophOf pred).witArity (Fin.castAdd 1 (0 : Fin 1))) < ctx 1 := by
    intro a h0
    rw [reindexInputSys_eval_zero_iff] at h0
    obtain ⟨hsys, hout⟩ := h0
    have hgraph := (diophOf_encodes pred).1
      (Fin.append ctx (fun i => a (Fin.castAdd (diophOf pred).witArity (Fin.castAdd 1 i))))
      (a (Fin.castAdd (diophOf pred).witArity (Fin.last 1)))
      (fun i => a (Fin.natAdd (1 + 1) i)) hsys
    rw [hout] at hgraph
    have hpz : Tm.eval eraInterp pred
        (Fin.append ctx
          (fun i => a (Fin.castAdd (diophOf pred).witArity (Fin.castAdd 1 i)))) = 0 :=
      hgraph.symm
    have hsnoc := Fin.append_right_eq_snoc ctx
      (fun i => a (Fin.castAdd (diophOf pred).witArity (Fin.castAdd 1 i)))
    rw [hsnoc] at hpz
    have hjlt := ((hitGapTm_eval_zero_iff stepTm ATerm _).mp hpz).2
    have h1 : (1 : Fin ((2 + k) + 1)) = Fin.castSucc (1 : Fin (2 + k)) := by
      refine Fin.ext ?_
      simp only [Fin.val_castSucc, Fin.val_one']
      rw [Nat.one_mod_eq_one.mpr (by omega), Nat.one_mod_eq_one.mpr (by omega)]
    rwa [Fin.snoc_last, h1, Fin.snoc_castSucc] at hjlt
  -- the input-side base coordinate bound for the re-indexed system's zeros
  have hcoord : ∀ a : Fin (1 + 1 + (diophOf pred).witArity) → ℕ,
      SosSystem.eval sysW (Fin.append ctx a) = 0 → ∀ c, a c < tBase := by
    intro a h0
    refine reindexInputSys_coord_bound pred ctx tBase
      (eraHitBase_pos stepTm ATerm ctx) a h0 ?hbnd ?hmoved
    case hbnd =>
      intro i
      rw [Fin.append_right_eq_snoc ctx
        (fun j => a (Fin.castAdd (diophOf pred).witArity (Fin.castAdd 1 j)))]
      exact eraHitBase_bound stepTm ATerm ctx i _ (Nat.le_of_lt (hmovedlt a h0))
    case hmoved =>
      intro i
      rw [Subsingleton.elim i (0 : Fin 1)]
      exact Nat.lt_trans (hmovedlt a h0) (eraHitBase_n stepTm ATerm ctx)
  -- step 1: the count read-off at the enlarged side
  rw [eraHitCount, eraCount_eval sysW tθT (eraW sysW tθT +ᵉ eraNumeral 1) ctx
    hzero hcoeff hbase ht hwpos ?hP]
  case hP =>
    intro a ha
    refine lt_of_lt_of_le (eraW_spec sysW tθT ctx hzero hcoeff hbase ht a ha) ?_
    refine Nat.pow_le_pow_right (by norm_num) ?_
    rw [eadd, Tm.eval, eraInterp]
    simp only [fcons, eraNumeral_eval]
    omega
  -- step 2: the fibre collapse
  rw [reducedCount_eq sysW ctx tθ hcoeff hbase ?hθ]
  case hθ =>
    intro x hx hx0 c i
    have hxbase : ∀ c, x c < tBase := hcoord x hx0
    exact eraTheta_spec sysW tBaseT ctx x hxbase c i
  -- step 3: the shell collapse to the base side
  rw [predCount_side_eq sysW ctx tBase tθ ?htθ ?hshell]
  case htθ =>
    rw [htθ, htθT, eraTheta]
    refine le_trans ?_ (le_of_lt (eraMajorant_spec _ ctx))
    rw [epow_eval, eraInterp, eraNumeral_eval]
    simp only [fcons]
    exact Nat.le_self_pow (by omega) _
  case hshell =>
    intro x _ hx0 c
    exact hcoord x hx0 c

open GebLean.EraCompleteness in
/-- The Era-term witness counter of arXiv:2407.12928, Corollary 3.6 (via
Theorem 3.4): for a `diophOf`-encoded predicate `τ`, the closed `Era` term whose
value at `ctx` is the number of cube points (output slot together with the
`diophOf` witnesses) at which the encoding's sum-of-squares system vanishes. It is
the count read-off `eraCount` of the Lemma 3.5-reduced re-indexed system
`reindexSys τ`, taken at the enlarged side `eraTheta` (so the unique chain witness
is a valid cube coordinate) and modulus `eraW + 1` (so the modulus is positive and
strictly dominates the reduced predicate). -/
def eraCountPred {n : ℕ} (τ : ETm n) : ETm n :=
  eraCount (reindexSys τ) (eraTheta (reindexSys τ) (eraBaseBound τ))
    (eraW (reindexSys τ) (eraTheta (reindexSys τ) (eraBaseBound τ)) +ᵉ eraNumeral 1)

open GebLean.EraCompleteness in
/-- The witness-counting identity of arXiv:2407.12928, Corollary 3.6 (via
Theorem 3.4): `eraCountPred τ` evaluates to the number of cube points — output
slot together with the `diophOf` witnesses — at side `eraBaseBound` at which the
`diophOf` encoding's system vanishes. The proof composes the count read-off
`eraCount_eval` at the enlarged side (discharging its block bound by `eraW_spec`
and its positivity by the `+ 1` modulus), the fibre collapse `reducedCount_eq`
(its chain-witness bound by `eraTheta_spec` over the base coordinate bound
`reindexSys_coord_bound`), the shell collapse `predCount_side_eq` (its shell
emptiness by the same coordinate bound), and the re-indexing bridge
`reindexSys_eval`. -/
theorem eraCountPred_eval {n : ℕ} (τ : ETm n) (ctx : Fin n → ℕ) :
    Tm.eval eraInterp (eraCountPred τ) ctx
      = ((GebLean.EraHypercube.cubePoints (1 + (diophOf τ).witArity)
            (Tm.eval eraInterp (eraBaseBound τ) ctx)).filter
          (fun a => SosSystem.eval (diophOf τ).sys (reindexCtx τ ctx a) = 0)).card := by
  set sysW := reindexSys τ with hsysW
  set tθT := eraTheta sysW (eraBaseBound τ) with htθT
  set tBase := Tm.eval eraInterp (eraBaseBound τ) ctx with htBase
  set tθ := Tm.eval eraInterp tθT ctx with htθ
  have hzero : sysW.PolyExpZero := reindexSys_polyExpZero τ
  have hcoeff : sysW.CoeffVarProduct := reindexSys_coeffVarProduct τ
  have hbase : sysW.BasePaired := reindexSys_basePaired τ
  have ht : 0 < tθ := by rw [htθ, htθT, eraTheta]; exact eraMajorant_pos _ ctx
  have hwpos : 0 < Tm.eval eraInterp (eraW sysW tθT +ᵉ eraNumeral 1) ctx := by
    rw [eadd, Tm.eval, eraInterp]
    simp only [fcons, eraNumeral_eval]
    omega
  -- the base coordinate bound for the re-indexed system's zeros
  have hcoord : ∀ x : Fin (1 + (diophOf τ).witArity) → ℕ,
      SosSystem.eval sysW (Fin.append ctx x) = 0 → ∀ c, x c < tBase :=
    fun x hx0 => reindexSys_coord_bound τ ctx x hx0
  -- step 1: the count read-off at the enlarged side
  rw [eraCountPred, eraCount_eval sysW tθT (eraW sysW tθT +ᵉ eraNumeral 1) ctx
    hzero hcoeff hbase ht hwpos ?hP]
  case hP =>
    intro a ha
    refine lt_of_lt_of_le (eraW_spec sysW tθT ctx hzero hcoeff hbase ht a ha) ?_
    refine Nat.pow_le_pow_right (by norm_num) ?_
    rw [eadd, Tm.eval, eraInterp]
    simp only [fcons, eraNumeral_eval]
    omega
  -- step 2: the fibre collapse
  rw [reducedCount_eq sysW ctx tθ hcoeff hbase ?hθ]
  case hθ =>
    intro x hx hx0 c i
    have hxbase : ∀ c, x c < tBase := hcoord x hx0
    exact eraTheta_spec sysW (eraBaseBound τ) ctx x hxbase c i
  -- step 3: the shell collapse to the base side
  rw [predCount_side_eq sysW ctx tBase tθ ?htθ ?hshell]
  case htθ =>
    rw [htθ, htθT, eraTheta]
    refine le_trans ?_ (le_of_lt (eraMajorant_spec _ ctx))
    rw [epow_eval, eraInterp, eraNumeral_eval]
    simp only [fcons]
    exact Nat.le_self_pow (by omega) _
  case hshell =>
    intro x _ hx0 c
    exact hcoord x hx0 c
  -- step 4: the re-indexing bridge on the predicate
  refine congrArg Finset.card (Finset.filter_congr (fun x _ => ?_))
  rw [reindexSys_eval]

end GebLean
