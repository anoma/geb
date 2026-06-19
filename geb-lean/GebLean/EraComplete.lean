import GebLean.EraHistCodeTerm

/-!
# `Era`-term completeness for the elementary functions

This module assembles the recurrence-to-term former and the bounded-sum and
bounded-product combinators on top of the history-code term `eraHistCode`
(`GebLean.EraHistCodeTerm`), and proves that every `ERMor1` (elementary
recursive) function is the denotation of an `Era` arithmetic term.

The recurrence former `eraRec` reads the top base-`A` digit of the history
code: by `GebLean.EraHypercube.recurrence_readoff`, an `A`-bounded recurrence's
`n`-th value is `histCode init step A n / A ^ n` (arXiv:2606.09336, Theorem 2,
`k = 1`). `eraBSum`/`eraBProd` instantiate the former with the
accumulator-plus-summand and accumulator-times-factor steps, under a sum and a
product majorant respectively.

## Main definitions

* `eraRec` — the first-order recurrence-to-term former.
* `eraBSum`, `eraBProd` — bounded summation and bounded product as `Era` terms.

## Main statements

* `eraRec_eval` — `eraRec` evaluates to `recSeq init step (ctx 0)` under the
  trajectory bound.
* `eraBSum_eval`, `eraBProd_eval` — the bounded-sum and bounded-product `eval`
  identities against `natBSum`/`natBProd`.
* `era_complete` — every `ERMor1` function is the denotation of an `Era` term.

## References

* arXiv:2606.09336 (Istrate-Prunescu-Shunia), Theorem 2.
* arXiv:2407.12928 (Prunescu-Sauras-Altuzarra), Section 4.

## Tags

elementary recursive, arithmetic term, bounded recursion, completeness
-/

namespace GebLean

open Era

/-- The first-order recurrence-to-term former (arXiv:2606.09336, Theorem 2, `k = 1`).
Given an `Era` step term `stepTm`, a coding-base term `ATerm`, and an initial value
`init`, `eraRec stepTm ATerm init` is the `Era` term reading the top base-`ATerm` digit
of the history code `eraHistCode stepTm ATerm init`: the value `histCode / ATerm ^ (var 0)`,
which under an `ATerm`-bounded trajectory equals the `(var 0)`-th value of the recurrence
with step `stepTm` and initial digit `init`. -/
def eraRec {k : ℕ} (stepTm : ETm (2 + k)) (ATerm : ETm (1 + k)) (init : ℕ) : ETm (1 + k) :=
  eraHistCode stepTm ATerm init /ᵉ (ATerm ^ᵉ Tm.var 0)

/-- `eraRec` evaluation (arXiv:2606.09336, Theorem 2, `k = 1`): under the trajectory bound
`hbound` (each history value below the coding base `ATerm`), `eraRec stepTm ATerm init`
evaluates to the `(ctx 0)`-th value of the recurrence read off from the history code by
`GebLean.EraHypercube.recurrence_readoff`. -/
theorem eraRec_eval {k : ℕ} (stepTm : ETm (2 + k)) (ATerm : ETm (1 + k)) (init : ℕ)
    (ctx : Fin (1 + k) → ℕ)
    (hbound : ∀ j, j ≤ ctx 0 → GebLean.EraHypercube.recSeq init
        (fun j v => Tm.eval eraInterp stepTm
          (hitGapStepCtx (Fin.snoc (histHitCtx (Fin.append ctx (fun _ : Fin 2 => 0)))
            (histHitCtx (Fin.append ctx (fun _ : Fin 2 => 0)) 1)) j v)) j
        < Tm.eval eraInterp ATerm ctx) :
    Tm.eval eraInterp (eraRec stepTm ATerm init) ctx
      = GebLean.EraHypercube.recSeq init
          (fun j v => Tm.eval eraInterp stepTm
            (hitGapStepCtx (Fin.snoc (histHitCtx (Fin.append ctx (fun _ : Fin 2 => 0)))
              (histHitCtx (Fin.append ctx (fun _ : Fin 2 => 0)) 1)) j v))
          (ctx 0) := by
  rw [eraRec, ediv_eval, epow_eval]
  simp only [eraInterp, fcons, Tm.eval]
  rw [eraHistCode_eval stepTm ATerm init ctx hbound,
    ← GebLean.EraHypercube.recurrence_readoff init _ (Tm.eval eraInterp ATerm ctx) (ctx 0)
      hbound]

end GebLean
