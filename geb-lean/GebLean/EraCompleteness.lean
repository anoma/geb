import GebLean.Era
import GebLean.LawvereER
import GebLean.Utilities.ERArith
import GebLean.Utilities.EraBoundedSum
import GebLean.Utilities.ArithClosedForms

/-!
# Era basis completeness bridge

Relates the denotations of `Era` terms (`Tm.eval eraInterp`) to the
elementary recursive functions as formalised by `ERMor1`
(`GebLean/LawvereER.lean`).

## Main definitions

* `eraOpToER` — the `ERMor1` witness for each basis operation.
* `erOfETm` — translation of an `Era` term to an `ERMor1` term.
* `eraGeomSum` — the closed-form `ETm 2` for `Σ_{i<bound} q^i`.
* `eraCentralBinom` — `centralBinomClosed` realised as an `ETm 1`.
* `eraDelta` — `deltaBlock` realised as an `ETm 2`.
* `eraGcd` — `gcdClosed5` realised as an `ETm 2`.
* `eraPow2Val` — `gcd(n, 2^n)` realised as an `ETm 1`.
* `eraNu2` — `nu2Closed` (the slow `2`-adic valuation) realised as an `ETm 1`.
* `eraSigma` — `hwClosed` (the binary Hamming weight) realised as an `ETm 1`.

## Main statements

* `erOfETm_interp` — `erOfETm` denotes the same function as the term.
* `era_sound_er` — every `ETm` denotes an `ERMor1` function
  (the inclusion `Era ⊆ E³`).
* `eraGeomSum_eval` — raw evaluation of `eraGeomSum`.
* `eraGeomSum_natBSum` — `eraGeomSum` agrees with `natBSum` when the base is at least `2`.
* `eraCentralBinom_eval` — `eraCentralBinom` evaluates to `centralBinomClosed`.
* `eraDelta_eval` — `eraDelta` evaluates to `deltaBlock`.
* `eraGcd_eval` — `eraGcd` evaluates to `Nat.gcd`.
* `eraPow2Val_eval` — `eraPow2Val` evaluates to `Nat.gcd n (2 ^ n)`.
* `eraNu2_eval` — `eraNu2` evaluates to `nu2Closed`.
* `eraSigma_eval` — `eraSigma` evaluates to `hwClosed`.

## References

* Prunescu, Sauras-Altuzarra, Shunia, arXiv:2505.23787.

## Tags

elementary recursive, substitution basis, completeness
-/

namespace GebLean.EraCompleteness

open Era

/-- The `ERMor1` term realising each basis operation. -/
def eraOpToER : (b : EraB) → ERMor1 (eraAr b)
  | .add  => ERMor1.addN
  | .mod  => ERMor1.mod
  | .pow2 => ERMor1.comp ERMor1.powN ![ERMor1.natN 1 2, ERMor1.proj (0 : Fin 1)]
  | .tsub => ERMor1.sub
  | .mul  => ERMor1.mulN
  | .div  => ERMor1.div
  | .pow  => ERMor1.powN

/-- The `ERMor1` witness for each basis operation interprets to that operation's
`Nat` semantics. -/
theorem eraOpToER_interp (b : EraB) (ctx : Fin (eraAr b) → ℕ) :
    (eraOpToER b).interp ctx = eraInterp b ctx := by
  -- Each binary operation has arity-2 context; rewrite `ctx` to the explicit
  -- two-element vector so the literal-vector interp lemmas apply.
  have hctx2 : ∀ (c : Fin 2 → ℕ),
      c = ![c ⟨0, by decide⟩, c ⟨1, by decide⟩] := by
    intro c
    funext i
    match i with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
  cases b with
  | add => rw [hctx2 ctx]; exact ERMor1.interp_addN _
  | mod => rw [hctx2 ctx]; exact ERMor1.interp_mod _ _
  | pow2 =>
      change (ERMor1.comp ERMor1.powN
          ![ERMor1.natN 1 2, ERMor1.proj (0 : Fin 1)]).interp ctx = 2 ^ ctx ⟨0, by decide⟩
      rw [ERMor1.interp_comp]
      simp only [ERMor1.interp_powN, ERMor1.interp_natN, ERMor1.interp_proj,
        Matrix.cons_val_zero, Matrix.cons_val_one]
      rfl
  | tsub => rw [hctx2 ctx]; exact ERMor1.interp_sub _
  | mul => rw [hctx2 ctx]; exact ERMor1.interp_mulN _
  | div => rw [hctx2 ctx]; exact ERMor1.interp_div _ _
  | pow => rw [hctx2 ctx]; exact ERMor1.interp_powN _

/-- Translate an `Era` term to an `ERMor1` term of the same arity. -/
def erOfETm {n : ℕ} : ETm n → ERMor1 n
  | .var i    => ERMor1.proj i
  | .zero     => ERMor1.natN n 0
  | .succ t   => ERMor1.comp ERMor1.succ ![erOfETm t]
  | .app b ts => ERMor1.comp (eraOpToER b) (fun i => erOfETm (ts i))

/-- `erOfETm` denotes the same function as the Era term. -/
theorem erOfETm_interp {n : ℕ} (t : ETm n) (ctx : Fin n → ℕ) :
    (erOfETm t).interp ctx = Tm.eval eraInterp t ctx := by
  induction t with
  | var i => rfl
  | zero => exact ERMor1.interp_natN n 0 ctx
  | succ t ih =>
      rw [erOfETm, ERMor1.interp_comp, ERMor1.interp_succ]
      simp only [Matrix.cons_val_fin_one]
      rw [ih]
      rfl
  | app b ts ih =>
      rw [erOfETm, ERMor1.interp_comp, eraOpToER_interp]
      exact congrArg (eraInterp b) (funext fun i => ih i)

/-- Every `Era` term denotes an `ERMor1` (elementary) function. -/
theorem era_sound_er {n : ℕ} (t : ETm n) :
    ∃ f : ERMor1 n, ∀ ctx, f.interp ctx = Tm.eval eraInterp t ctx :=
  ⟨erOfETm t, fun ctx => erOfETm_interp t ctx⟩

/-- The geometric bounded sum `Σ_{i<bound} q^i` as a closed `Era` term:
`(q^bound - 1) / (q - 1)`, with variable `0` the base and variable `1`
the bound. -/
def eraGeomSum : ETm 2 :=
  ediv
    (etsub (epow (.var 0) (.var 1)) (.succ .zero))
    (etsub (.var 0) (.succ .zero))

/-- Raw evaluation of `eraGeomSum`: the term computes `(q^bound - 1) / (q - 1)`. -/
theorem eraGeomSum_eval (ctx : Fin 2 → ℕ) :
    Tm.eval eraInterp eraGeomSum ctx =
      (ctx 0 ^ ctx 1 - 1) / (ctx 0 - 1) := by
  simp [eraGeomSum, ediv, etsub, epow, Tm.eval, eraInterp, fcons]

/-- `eraGeomSum` computes the geometric bounded sum when the base is at
least `2`. -/
theorem eraGeomSum_natBSum (q bound : ℕ) (hq : 2 ≤ q) :
    Tm.eval eraInterp eraGeomSum ![q, bound] =
      natBSum bound (fun i => q ^ i) := by
  rw [eraGeomSum_eval]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [natBSum_geom q bound hq]

/-- `centralBinomClosed` realised as an `Era` term (variable 0 = n).
The term encodes `((1 + 2^(2n))^(2n) / 2^(2n²)) % 2^(2n)` with
`twoN := n + n = 2n`, `epow2 twoN = 2^(2n)`,
`epow2 (twoN *ᵉ var0) = 2^((2n)*n) = 2^(2n²)`. -/
def eraCentralBinom : ETm 1 :=
  let var0 : ETm 1 := .var 0
  let twoN  := var0 +ᵉ var0
  emod
    (ediv
      (epow (.succ (epow2 twoN)) twoN)
      (epow2 (twoN *ᵉ var0)))
    (epow2 twoN)

/-- `eraCentralBinom` evaluates to `centralBinomClosed`. -/
theorem eraCentralBinom_eval (n : ℕ) :
    Tm.eval eraInterp eraCentralBinom ![n] = centralBinomClosed n := by
  simp [eraCentralBinom, centralBinomClosed, emod, ediv, emul, epow, epow2, eadd,
    Tm.eval, eraInterp, fcons]
  ring_nf

/-- `deltaBlock` realised as an `Era` term (variable 0 = a, 1 = w). -/
def eraDelta : ETm 2 :=
  let a : ETm 2 := .var 0
  let w : ETm 2 := .var 1
  let pw := epow2 w
  emul (etsub pw (.succ .zero)) (.succ (etsub pw a))

/-- `eraDelta` evaluates to `deltaBlock`. -/
theorem eraDelta_eval (a w : ℕ) :
    Tm.eval eraInterp eraDelta ![a, w] = deltaBlock a w := by
  simp [eraDelta, deltaBlock, emul, etsub, epow2, Tm.eval, eraInterp, fcons,
    Matrix.cons_val_zero, Matrix.cons_val_one]

/-- `gcdClosed5` realised as an `ETm 2` (variables `0 = a`, `1 = b`),
built from `epow`/`ediv`/`emod`/`etsub`/`emul`/`eadd` over the constant `5`. -/
def eraGcd : ETm 2 :=
  let a : ETm 2 := .var 0
  let b : ETm 2 := .var 1
  let five : ETm 2 := .succ (.succ (.succ (.succ (.succ .zero))))
  let two : ETm 2 := .succ (.succ .zero)
  let one : ETm 2 := .succ .zero
  let ab := a *ᵉ b
  let num := epow five (ab *ᵉ ((ab +ᵉ a) +ᵉ b))
  let dena := etsub (epow five ((epow a two) *ᵉ b)) one
  let denb := etsub (epow five (a *ᵉ (epow b two))) one
  let base := epow five ab
  etsub (emod (ediv num (dena *ᵉ denb)) base) one

/-- `eraGcd` evaluates to `Nat.gcd`. -/
theorem eraGcd_eval (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    Tm.eval eraInterp eraGcd ![a, b] = Nat.gcd a b := by
  have h : Tm.eval eraInterp eraGcd ![a, b] = gcdClosed5 a b := by
    simp [eraGcd, gcdClosed5, emod, ediv, emul, etsub, epow, eadd, Tm.eval,
      eraInterp, fcons]
  rw [h, gcdClosed5_eq a b ha hb]

/-- `gcd(n, 2^n)` as an `ETm 1`: `eraGcd` substituted at `(var 0, 2^(var 0))`.
Equals `2^(padicValNat 2 n)` (stated in `gcd` form for use by `eraNu2`). -/
def eraPow2Val : ETm 1 :=
  eraGcd.subst ![(.var 0 : ETm 1), epow2 (.var 0)]

/-- `eraPow2Val` evaluates to `Nat.gcd n (2^n)`. -/
theorem eraPow2Val_eval (n : ℕ) (hn : 1 ≤ n) :
    Tm.eval eraInterp eraPow2Val ![n] = Nat.gcd n (2 ^ n) := by
  have hctx : Tm.eval eraInterp eraPow2Val ![n]
      = Tm.eval eraInterp eraGcd ![n, 2 ^ n] := by
    rw [eraPow2Val, Tm.eval_subst]
    congr 1
    funext i
    refine i.cases ?_ (fun j => j.cases ?_ (fun k => k.elim0))
    · simp [Tm.eval]
    · simp [Tm.eval, eraInterp, epow2, fcons]
  rw [hctx, eraGcd_eval n (2 ^ n) hn (Nat.one_le_pow n 2 (by norm_num))]

/-- The slow `2`-adic valuation `nu2Closed` realised as an `ETm 1`
(variable `0 = n`), built around `eraPow2Val` (which evaluates to
`Nat.gcd n (2^n)`). Mirrors `nu2Closed`'s arithmetic
`gcd(n,2ⁿ)^(n+1) % base² / base` with `base = 2^(n+1) − 1`. -/
def eraNu2 : ETm 1 :=
  let n : ETm 1 := .var 0
  let one : ETm 1 := .succ .zero
  let two : ETm 1 := .succ (.succ .zero)
  let base := etsub (epow2 (.succ n)) one
  ediv (emod (epow eraPow2Val (.succ n)) (epow base two)) base

/-- `eraNu2` evaluates to `nu2Closed`. -/
theorem eraNu2_eval (n : ℕ) (hn : 1 ≤ n) :
    Tm.eval eraInterp eraNu2 ![n] = nu2Closed n := by
  have key := eraPow2Val_eval n hn
  unfold nu2Closed
  simp only [eraNu2, ediv, emod, epow, epow2, etsub, Tm.eval, eraInterp, fcons,
    Matrix.cons_val_zero, key]

/-- The binary Hamming weight `hwClosed = nu2Closed ∘ centralBinomClosed`
realised as an `ETm 1` (variable `0 = n`): `eraNu2` composed with
`eraCentralBinom` by substitution. -/
def eraSigma : ETm 1 :=
  eraNu2.subst ![eraCentralBinom]

/-- `eraSigma` evaluates to `hwClosed`. -/
theorem eraSigma_eval (n : ℕ) (hn : 1 ≤ n) :
    Tm.eval eraInterp eraSigma ![n] = hwClosed n := by
  have hcb : 1 ≤ centralBinomClosed n := by
    rw [centralBinomClosed_eq n hn]; exact Nat.centralBinom_pos n
  rw [eraSigma, Tm.eval_subst]
  have hctx : (fun i => Tm.eval eraInterp (![eraCentralBinom] i) ![n])
      = ![centralBinomClosed n] := by
    funext i
    refine i.cases ?_ (fun k => k.elim0)
    simp [eraCentralBinom_eval]
  rw [hctx]
  exact eraNu2_eval (centralBinomClosed n) hcb

end GebLean.EraCompleteness
