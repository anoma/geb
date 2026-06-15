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

## Main statements

* `erOfETm_interp` — `erOfETm` denotes the same function as the term.
* `era_sound_er` — every `ETm` denotes an `ERMor1` function
  (the inclusion `Era ⊆ E³`).
* `eraGeomSum_eval` — raw evaluation of `eraGeomSum`.
* `eraGeomSum_natBSum` — `eraGeomSum` agrees with `natBSum` when the base is at least `2`.
* `eraCentralBinom_eval` — `eraCentralBinom` evaluates to `centralBinomClosed`.
* `eraDelta_eval` — `eraDelta` evaluates to `deltaBlock`.

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

end GebLean.EraCompleteness
