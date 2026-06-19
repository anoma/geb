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
theorem Finset.sum_list_map_comm {α β : Type*} [AddCommMonoid β] {ι : Type*}
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
`Finset.sum_list_map_comm` swaps the cube-`Finset.sum` past the monomial
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
  rw [Finset.sum_congr rfl (fun a _ => hpt a), Finset.sum_list_map_comm]
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
  set f := (sepReduce s).1 with hf
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

end GebLean
