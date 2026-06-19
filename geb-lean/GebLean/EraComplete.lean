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
open GebLean.EraHistCodeTerm (eraNumeral eraNumeral_eval)

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

/-- The slot-renaming carrying the summand `g : ETm (k + 1)` into the step scope
`ETm (2 + k)` of `eraRec` (arXiv:2606.09336, Theorem 2): `g`'s loop slot `0` maps to
the recurrence index variable `0`, and `g`'s parameter slot `1 + j` maps to the
ambient variable `2 + j` of the step scope `[index, accumulator, ambient(k)]`. -/
def eraBSumSub {k : ℕ} : Fin (k + 1) → ETm (2 + k) :=
  Fin.cases (Tm.var 0) (fun j : Fin k => Tm.var ⟨2 + (j : ℕ), by omega⟩)

/-- The step term of bounded summation (arXiv:2606.09336, Theorem 2): over the step
scope `[index, accumulator, ambient(k)]`, the accumulator (variable `1`) plus the
summand `g` re-indexed by `eraBSumSub` so that its loop slot reads the index and its
parameters read the ambient slots. -/
def eraBSumStep {k : ℕ} (g : ETm (k + 1)) : ETm (2 + k) :=
  Tm.var 1 +ᵉ g.subst eraBSumSub

/-- The sum majorant term of bounded summation (arXiv:2606.09336, Theorem 2): the
coding base for the history code, over the scope `[bound, ambient(k)]`. With each
summand strictly below the recast majorant `M` of `g`, every partial sum over the
loop bound `n = var 0` lies below `n * M + 1`, the trajectory bound `eraRec` needs. -/
def eraBSumMajorant {k : ℕ} (g : ETm (k + 1)) : ETm (1 + k) :=
  (Tm.var 0 *ᵉ (eraMajorant g).weaken (finCongr (Nat.add_comm k 1))) +ᵉ eraNumeral 1

/-- The wrapper step of bounded summation (arXiv:2606.09336, Theorem 2): the step
that `eraRec_eval` reads off `eraBSumStep g` adds, at loop index `i` and accumulator
`s`, the summand `g` evaluated at `i` with the ambient parameters `fun j => ctx' ⟨1 + j⟩`
read off the parameter context, recovering the running-sum recurrence. -/
theorem bsumStep_eval {k : ℕ} (g : ETm (k + 1)) (ctx' : Fin (1 + k) → ℕ) (i s : ℕ) :
    Tm.eval eraInterp (eraBSumStep g)
        (hitGapStepCtx (Fin.snoc (histHitCtx (Fin.append ctx' (fun _ : Fin 2 => 0)))
          (histHitCtx (Fin.append ctx' (fun _ : Fin 2 => 0)) 1)) i s)
      = s + Tm.eval eraInterp g
          (Fin.cons i (fun j : Fin k => ctx' ⟨1 + (j : ℕ), by omega⟩)) := by
  set ctxFull : Fin ((2 + k) + 1) → ℕ :=
    Fin.snoc (histHitCtx (Fin.append ctx' (fun _ : Fin 2 => 0)))
      (histHitCtx (Fin.append ctx' (fun _ : Fin 2 => 0)) 1) with hctxFull
  have hslot0 : hitGapStepCtx ctxFull i s 0 = i := by
    rw [show (0 : Fin (2 + k)) = Fin.castAdd k (0 : Fin 2) from rfl]
    simp only [hitGapStepCtx, Fin.addCases_left, Fin.val_zero, if_pos]
  have h1cast : (1 : Fin (2 + k)) = Fin.castAdd k (1 : Fin 2) := by
    apply Fin.ext
    simp only [Fin.val_castAdd, Fin.val_one']
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have hslot1 : hitGapStepCtx ctxFull i s 1 = s := by
    rw [h1cast]
    simp only [hitGapStepCtx, Fin.addCases_left, Fin.val_one, Nat.one_ne_zero, if_neg,
      not_false_iff]
  have hamb : ∀ j : Fin k, hitGapStepCtx ctxFull i s ⟨2 + (j : ℕ), by omega⟩
      = ctx' ⟨1 + (j : ℕ), by omega⟩ := by
    intro j
    rw [show (⟨2 + (j : ℕ), by omega⟩ : Fin (2 + k)) = Fin.natAdd 2 j from by
      apply Fin.ext; simp only [Fin.val_natAdd]]
    simp only [hitGapStepCtx, Fin.addCases_right]
    show ctxFull (ambIdx j) = ctx' ⟨1 + (j : ℕ), by omega⟩
    rw [hctxFull, histHitSnoc_amb]
  have hfun : (fun slot => Tm.eval eraInterp (eraBSumSub slot) (hitGapStepCtx ctxFull i s))
      = Fin.cons i (fun j : Fin k => ctx' ⟨1 + (j : ℕ), by omega⟩) := by
    funext slot
    refine Fin.cases ?_ (fun j => ?_) slot
    · simp only [eraBSumSub, Fin.cases_zero, Tm.eval, hslot0, Fin.cons_zero]
    · simp only [eraBSumSub, Fin.cases_succ, Tm.eval, hamb, Fin.cons_succ]
  rw [eraBSumStep, eadd_eval, eraInterp, Tm.eval_subst]
  simp only [fcons, Tm.eval, hslot1, hfun]

/-- The wrapper recurrence of bounded summation computes the bounded sum
(arXiv:2606.09336, Theorem 2): `recSeq 0 <wrapper-step> y`, the running sum that
`eraRec_eval` reads off `eraBSumStep g`, equals `natBSum y` of the summand `g`
evaluated at each index with the ambient parameters read off `ctx'`. -/
theorem recSeq_eq_natBSum {k : ℕ} (g : ETm (k + 1)) (ctx' : Fin (1 + k) → ℕ) (y : ℕ) :
    GebLean.EraHypercube.recSeq 0
        (fun i s => Tm.eval eraInterp (eraBSumStep g)
          (hitGapStepCtx (Fin.snoc (histHitCtx (Fin.append ctx' (fun _ : Fin 2 => 0)))
            (histHitCtx (Fin.append ctx' (fun _ : Fin 2 => 0)) 1)) i s)) y
      = natBSum y
          (fun i => Tm.eval eraInterp g
            (Fin.cons i (fun j : Fin k => ctx' ⟨1 + (j : ℕ), by omega⟩))) := by
  induction y with
  | zero => rfl
  | succ m ih =>
    rw [GebLean.EraHypercube.recSeq, bsumStep_eval, ih]
    rfl

/-- The trajectory bound of bounded summation (arXiv:2606.09336, Theorem 2): every
partial sum `recSeq 0 <wrapper-step> j` over a loop index `j ≤ ctx' 0` lies strictly
below the sum majorant `eraBSumMajorant g`. Each summand is strictly below the recast
majorant `M` of `g` (`eraMajorant_spec`), monotone up to the loop bound at slot `0`
(`eraMajorant_mono`); the sum of `j ≤ ctx' 0` such summands is at most `ctx' 0 * M`. -/
theorem sumMajorant_bound {k : ℕ} (g : ETm (k + 1)) (ctx' : Fin (1 + k) → ℕ) (j : ℕ)
    (hj : j ≤ ctx' 0) :
    GebLean.EraHypercube.recSeq 0
        (fun i s => Tm.eval eraInterp (eraBSumStep g)
          (hitGapStepCtx (Fin.snoc (histHitCtx (Fin.append ctx' (fun _ : Fin 2 => 0)))
            (histHitCtx (Fin.append ctx' (fun _ : Fin 2 => 0)) 1)) i s)) j
      < Tm.eval eraInterp (eraBSumMajorant g) ctx' := by
  set ctxM : Fin (k + 1) → ℕ := ctx' ∘ finCongr (Nat.add_comm k 1) with hctxM
  set M : ℕ := Tm.eval eraInterp (eraMajorant g) ctxM with hM
  -- the majorant term evaluates to `ctx' 0 * M + 1`
  have hmaj : Tm.eval eraInterp (eraBSumMajorant g) ctx' = ctx' 0 * M + 1 := by
    rw [eraBSumMajorant, eadd_eval, eraInterp, emul_eval, eraInterp]
    simp only [fcons, Tm.eval, eraNumeral_eval, Tm.eval_weaken]
    rw [← hctxM, ← hM]
  -- the summand at index `i`
  set f : ℕ → ℕ := fun i => Tm.eval eraInterp g
    (Fin.cons i (fun a : Fin k => ctx' ⟨1 + (a : ℕ), by omega⟩)) with hf
  -- each summand below the loop bound is at most `M`
  have hfi : ∀ i, i < ctx' 0 → f i ≤ M := by
    intro i hi
    have hspec : f i < Tm.eval eraInterp (eraMajorant g)
        (Fin.cons i (fun a : Fin k => ctx' ⟨1 + (a : ℕ), by omega⟩)) :=
      eraMajorant_spec g _
    have hmono : Tm.eval eraInterp (eraMajorant g)
        (Fin.cons i (fun a : Fin k => ctx' ⟨1 + (a : ℕ), by omega⟩)) ≤ M := by
      rw [hM]
      refine eraMajorant_mono g (fun slot => ?_)
      refine Fin.cases ?_ (fun a => ?_) slot
      · rw [Fin.cons_zero]
        have : ctxM 0 = ctx' 0 := by rw [hctxM]; simp [finCongr]
        rw [this]; omega
      · rw [Fin.cons_succ]
        have hctxMa : ctxM a.succ = ctx' ⟨1 + (a : ℕ), by omega⟩ := by
          rw [hctxM]
          simp only [Function.comp_apply, finCongr_apply]
          congr 1
          apply Fin.ext
          simp only [_root_.Fin.val_cast, Fin.val_succ]
          omega
        rw [hctxMa]
    omega
  rw [recSeq_eq_natBSum, hmaj, natBSum_eq_sum]
  calc ∑ i ∈ Finset.range j, f i
      ≤ ∑ _i ∈ Finset.range j, M := Finset.sum_le_sum (fun i hi =>
        hfi i (Nat.lt_of_lt_of_le (Finset.mem_range.mp hi) hj))
    _ = j * M := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
    _ ≤ ctx' 0 * M := Nat.mul_le_mul_right M hj
    _ < ctx' 0 * M + 1 := Nat.lt_succ_self _

/-- Bounded summation `Σ_{i < bound} g i` as an `Era` arithmetic term
(arXiv:2606.09336, Theorem 2, the bounded-sum instance of the recurrence former):
the `eraRec` instance whose step adds `g` evaluated at the loop index to the running
accumulator, started from `0`, under the sum majorant `eraBSumMajorant g`. The result
is recast from `ETm (1 + k)` back to the summand scope `ETm (k + 1)`. -/
def eraBSum {k : ℕ} (g : ETm (k + 1)) : ETm (k + 1) :=
  (eraRec (eraBSumStep g) (eraBSumMajorant g) 0).weaken (finCongr (Nat.add_comm 1 k))

/-- Bounded summation `eval` identity (arXiv:2606.09336, Theorem 2): `eraBSum g`
evaluates at `ctx` to `Σ_{i < ctx 0} g i`, where `ctx 0` is the loop bound and
`Fin.tail ctx` the ambient parameters, matching `natBSum`. The trajectory bound is
discharged by `sumMajorant_bound`, the recurrence read-off by `eraRec_eval`, and the
running-sum identification by `recSeq_eq_natBSum`. -/
theorem eraBSum_eval {k : ℕ} (g : ETm (k + 1)) (ctx : Fin (k + 1) → ℕ) :
    Tm.eval eraInterp (eraBSum g) ctx
      = natBSum (ctx 0)
          (fun i => Tm.eval eraInterp g (Fin.cons i (Fin.tail ctx))) := by
  set ctx' : Fin (1 + k) → ℕ := ctx ∘ finCongr (Nat.add_comm 1 k) with hctx'
  -- the loop bound is preserved by the context recast
  have hbound0 : ctx' 0 = ctx 0 := by rw [hctx']; simp [finCongr]
  -- the ambient parameters of the recast context are `Fin.tail ctx`
  have hparam : (fun a : Fin k => ctx' ⟨1 + (a : ℕ), by omega⟩) = Fin.tail ctx := by
    funext a
    rw [hctx', Fin.tail]
    simp only [Function.comp_apply, finCongr_apply]
    congr 1
    apply Fin.ext
    simp only [_root_.Fin.val_cast, Fin.val_succ]
    omega
  rw [eraBSum, Tm.eval_weaken, ← hctx',
    eraRec_eval (eraBSumStep g) (eraBSumMajorant g) 0 ctx'
      (fun j hj => sumMajorant_bound g ctx' j (hbound0 ▸ hj)),
    recSeq_eq_natBSum, hbound0, hparam]

end GebLean
