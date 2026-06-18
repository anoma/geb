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

## Implementation notes

The combinator is stated against a supplied packed-witness term `packMTerm`
together with the hypothesis that it evaluates to `packM`. The cube-sum
factorisation that constructs such a `packMTerm` from a degree-≤2 simple
exponential polynomial predicate (arXiv:2407.12928, Eqs (7), (8)) is the
remaining piece of the count combinator.

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

end GebLean
