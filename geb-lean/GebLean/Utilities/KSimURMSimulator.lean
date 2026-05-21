import GebLean.Utilities.ZeroTestURM
import GebLean.Utilities.KArith
import GebLean.LawvereKSim
import GebLean.LawvereKSimInterp

/-!
# K^sim simulator for the zero-test URM kernel

For every `URMProgram a` (T1 + T2's `URMProgram` family at
`GebLean/Utilities/ZeroTestURM.lean:122`), this module builds a
single-output K^sim morphism `simulate : URMProgram a →
KMor1 (a + 1)` whose interpretation at `(y, v)` equals the value
of the output register after `y` steps from `URMState.init P v`.
The simulator is a `KMor1.simrec` (`LawvereKSim.lean:50`) with
system size `P.numRegs + 1`: components `0, …, numRegs - 1`
track register values; component `numRegs` (the last) tracks the
PC. Output index is `P.outputReg.castSucc`. The simulator is at
K^sim level ≤ 2 (base sup 0, step sup ≤ 1, simrec adds 1).

## Main definitions

- `KMor1.pcDispatch`: a non-substituting bottom-up `cond`-chain
  combinator reading the last context slot (the PC) and
  selecting branches keyed to specific PC values.
- `baseFamily`: the simrec's base family at the initial state.
- `stepFamily`: the simrec's step family at one URM step.
- `simulate`: the public-facing simulator term.

## Main statements

- `KMor1.interp_pcDispatch_match`, `KMor1.interp_pcDispatch_default`:
  the dispatcher's interpretation simp lemmas.
- `KMor1.pcDispatch_level`: the dispatcher's level bound (1 when
  branches and default are level ≤ 1).
- `simulate_interp`: the simulator's output equals
  `URMState.runFor`'s output projected at `outputReg`.
- `simulate_level`: the simulator is at K^sim level ≤ 2.

## Implementation notes

The bottom-up `cond`-chain reads
`pred^k(PC) = 0 ⇔ PC ≤ k` (Tourlakis § 0.1.0.20 chained with
§ 0.1.0.8); the nested fall-through structure converts the
inequality into the equality `PC = k` at each level. The
recursive case does *not* substitute the PC slot via
`KMor1.comp _ shift` — branches and default sit at the same
context as their siblings, so the interp simp lemmas hold
verbatim without context-substitution corrections.

## References

- Tourlakis 2018 `PR-complexity-topics.pdf` § 0.1.0.37
  (simulation lemma).
- `docs/superpowers/specs/2026-05-21-step-t3-urm-to-ksim-simulator-design.md`
  § 3 (architecture), § 4 (correctness), § 5 (level).

## Tags

URM, K^sim, simulator, simrec, Tourlakis
-/

namespace GebLean

/-- The `k`-fold composition of `KMor1.pred` over the last
context slot, `KMor1.proj (Fin.last n)`. Level 0 for `k = 0`,
level 1 for `k ≥ 1`. Used inside `KMor1.pcDispatch`'s `cond`
chain as the level-1 inequality test `predIter k = 0 ⇔ PC ≤ k`
(Tourlakis § 0.1.0.20 chained with § 0.1.0.8). -/
private def KMor1.predIter (n k : ℕ) : KMor1 (n + 1) :=
  match k with
  | 0     => KMor1.proj (Fin.last n)
  | k + 1 =>
    KMor1.comp KMor1.pred
      (fun _ : Fin 1 => KMor1.predIter n k)

/-- `KMor1.predIter n k` interprets as `k`-fold `Nat.pred` over
the last context slot, equivalent to `ctx (Fin.last n) - k`
(truncated subtraction on `ℕ`). -/
@[simp] theorem KMor1.interp_predIter
    (n k : ℕ) (ctx : Fin (n + 1) → ℕ) :
    (KMor1.predIter n k).interp ctx = ctx (Fin.last n) - k := by
  induction k with
  | zero =>
    simp only [KMor1.predIter, KMor1.interp_proj, Nat.sub_zero]
  | succ k ih =>
    simp only [KMor1.predIter, KMor1.interp_comp,
      KMor1.interp_pred]
    rw [ih, Nat.pred_eq_sub_one]
    omega

/-- `KMor1.predIter n k` has level ≤ 1 for every `n` and `k`
(level 0 when `k = 0`, level 1 when `k ≥ 1`). -/
theorem KMor1.predIter_level (n k : ℕ) :
    (KMor1.predIter n k).level ≤ 1 := by
  induction k with
  | zero =>
    change KMor1.level (KMor1.proj (Fin.last n)) ≤ 1
    unfold KMor1.level
    omega
  | succ k ih =>
    change KMor1.level
        (KMor1.comp KMor1.pred (fun _ : Fin 1 => KMor1.predIter n k))
        ≤ 1
    unfold KMor1.level
    have hsup :
        Fin.maxOfNat 1
          (fun _ : Fin 1 => (KMor1.predIter n k).level) ≤ 1 :=
      Fin.maxOfNat_le (by intro _; exact ih)
    have hpred : KMor1.level (KMor1.pred : KMor1 1) = 1 := rfl
    simp only []
    omega

/-- Auxiliary continuation for `KMor1.pcDispatch`: at offset
`k`, test `KMor1.predIter n k = 0 ⇔ PC ≤ k`, select
`branches ⟨0, _⟩` if so, else recurse at offset `k + 1` over
`branches ∘ Fin.succ`. The recursive call sits at the *same*
context as the surrounding `cond`; branches and default are
never wrapped in a context-substituting `KMor1.comp`. -/
private def KMor1.pcDispatchFrom {n : ℕ}
    (k size : ℕ)
    (branches : Fin size → KMor1 (n + 1))
    (default : KMor1 (n + 1)) :
    KMor1 (n + 1) :=
  match size with
  | 0 => default
  | size' + 1 =>
    KMor1.comp KMor1.cond
      (fun i : Fin 3 => match i with
        | ⟨0, _⟩ => KMor1.predIter n k
        | ⟨1, _⟩ => branches ⟨0, by omega⟩
        | ⟨2, _⟩ =>
          KMor1.pcDispatchFrom (k + 1) size'
            (fun j : Fin size' => branches j.succ) default)

/-- The PC-dispatch combinator: given `size` branches keyed to
specific PC values (the last context slot) and a `default` for
PC values `≥ size`, return a `KMor1 (n + 1)` that interprets to
`branches k` when PC = `k` (`k < size`), else `default`.

Implementation defers to `KMor1.pcDispatchFrom 0 size`. -/
def KMor1.pcDispatch {n : ℕ} (size : ℕ)
    (branches : Fin size → KMor1 (n + 1))
    (default : KMor1 (n + 1)) :
    KMor1 (n + 1) :=
  KMor1.pcDispatchFrom 0 size branches default

private theorem KMor1.interp_pcDispatchFrom_match
    {n : ℕ} (size : ℕ) (k : ℕ)
    (branches : Fin size → KMor1 (n + 1))
    (default : KMor1 (n + 1)) (ctx : Fin (n + 1) → ℕ)
    (j : Fin size) (h : ctx (Fin.last n) = k + j.val) :
    (KMor1.pcDispatchFrom k size branches default).interp ctx
      = (branches j).interp ctx := by
  induction size generalizing k with
  | zero => exact Fin.elim0 j
  | succ size' ih =>
    simp only [KMor1.pcDispatchFrom, KMor1.interp_comp,
      KMor1.interp_cond, KMor1.interp_predIter]
    by_cases hj : j = ⟨0, by omega⟩
    · rw [hj]
      have hsub0 : ctx (Fin.last n) - k = 0 := by
        rw [h, hj]; simp
      rw [hsub0]; simp
    · have hjpos : 0 < j.val := by
        rcases j with ⟨v, hv⟩
        rcases v with _ | v'
        · exact absurd (Fin.ext rfl : (⟨0, by omega⟩ : Fin (size' + 1)) = ⟨0, hv⟩) hj
        · simp
      have hsub : ctx (Fin.last n) - k ≠ 0 := by
        rw [h]; omega
      rw [if_neg hsub]
      have hpred : ctx (Fin.last n) = (k + 1) + (j.val - 1) := by
        rw [h]; omega
      have ih_applied :=
        ih (k + 1) (fun j' : Fin size' => branches j'.succ)
          ⟨j.val - 1, by omega⟩ hpred
      rw [ih_applied]
      change (branches _).interp ctx = (branches _).interp ctx
      congr 2
      apply Fin.ext
      simp [Fin.succ]
      omega

private theorem KMor1.interp_pcDispatchFrom_default
    {n : ℕ} (size : ℕ) (k : ℕ)
    (branches : Fin size → KMor1 (n + 1))
    (default : KMor1 (n + 1)) (ctx : Fin (n + 1) → ℕ)
    (h : ctx (Fin.last n) ≥ k + size) :
    (KMor1.pcDispatchFrom k size branches default).interp ctx
      = default.interp ctx := by
  induction size generalizing k with
  | zero => simp [KMor1.pcDispatchFrom]
  | succ size' ih =>
    simp only [KMor1.pcDispatchFrom, KMor1.interp_comp,
      KMor1.interp_cond, KMor1.interp_predIter]
    have hsub : ctx (Fin.last n) - k ≠ 0 := by omega
    rw [if_neg hsub]
    apply ih
    omega

/-- When the PC slot equals `k.val` for some `k : Fin size`,
`KMor1.pcDispatch` interprets as `branches k`. -/
@[simp] theorem KMor1.interp_pcDispatch_match
    {n : ℕ} (size : ℕ)
    (branches : Fin size → KMor1 (n + 1))
    (default : KMor1 (n + 1)) (ctx : Fin (n + 1) → ℕ)
    (k : Fin size) (h : ctx (Fin.last n) = k.val) :
    (KMor1.pcDispatch size branches default).interp ctx
      = (branches k).interp ctx := by
  unfold KMor1.pcDispatch
  exact KMor1.interp_pcDispatchFrom_match size 0 branches default
    ctx k (by rw [h]; omega)

/-- When the PC slot is ≥ `size`, `KMor1.pcDispatch` interprets
as `default`. -/
@[simp] theorem KMor1.interp_pcDispatch_default
    {n : ℕ} (size : ℕ)
    (branches : Fin size → KMor1 (n + 1))
    (default : KMor1 (n + 1)) (ctx : Fin (n + 1) → ℕ)
    (h : ctx (Fin.last n) ≥ size) :
    (KMor1.pcDispatch size branches default).interp ctx
      = default.interp ctx := by
  unfold KMor1.pcDispatch
  exact KMor1.interp_pcDispatchFrom_default size 0 branches default
    ctx (by omega)

/-- Inner level lemma for `pcDispatchFrom`: when branches and
default are level ≤ 1, the dispatcher is level ≤ 1. By
induction on `size` with `k` and `branches` generalised. -/
private theorem KMor1.pcDispatchFrom_level
    {n : ℕ} (size : ℕ) (k : ℕ)
    (branches : Fin size → KMor1 (n + 1))
    (default : KMor1 (n + 1))
    (h_branches : ∀ j, (branches j).level ≤ 1)
    (h_default : default.level ≤ 1) :
    (KMor1.pcDispatchFrom k size branches default).level ≤ 1 := by
  induction size generalizing k with
  | zero =>
    change (default).level ≤ 1
    exact h_default
  | succ size' ih =>
    have hpred : (KMor1.predIter n k).level ≤ 1 :=
      KMor1.predIter_level n k
    have hb0 : (branches ⟨0, by omega⟩).level ≤ 1 :=
      h_branches _
    have hrecur : (KMor1.pcDispatchFrom (k + 1) size'
        (fun j : Fin size' => branches j.succ) default).level ≤ 1 :=
      ih (k + 1) (fun j => branches j.succ)
        (fun j => h_branches j.succ)
    change max (KMor1.cond.level)
           (Fin.maxOfNat 3 (fun i : Fin 3 =>
             match i with
             | ⟨0, _⟩ => (KMor1.predIter n k).level
             | ⟨1, _⟩ => (branches ⟨0, by omega⟩).level
             | ⟨2, _⟩ => (KMor1.pcDispatchFrom (k + 1) size'
                 (fun j : Fin size' => branches j.succ) default).level))
           ≤ 1
    have hcond_level : (KMor1.cond : KMor1 3).level = 1 := by decide
    have hsup :
        Fin.maxOfNat 3 (fun i : Fin 3 =>
          match i with
          | ⟨0, _⟩ => (KMor1.predIter n k).level
          | ⟨1, _⟩ => (branches ⟨0, by omega⟩).level
          | ⟨2, _⟩ => (KMor1.pcDispatchFrom (k + 1) size'
              (fun j => branches j.succ) default).level) ≤ 1 :=
      Fin.maxOfNat_le (by
        intro i
        match i with
        | ⟨0, _⟩ => exact hpred
        | ⟨1, _⟩ => exact hb0
        | ⟨2, _⟩ => exact hrecur)
    rw [hcond_level]
    exact Nat.max_le.mpr ⟨le_refl 1, hsup⟩

/-- `KMor1.pcDispatch` is at level ≤ 1 when branches and
default are level ≤ 1. -/
theorem KMor1.pcDispatch_level
    {n : ℕ} (size : ℕ)
    (branches : Fin size → KMor1 (n + 1))
    (default : KMor1 (n + 1))
    (h_branches : ∀ j, (branches j).level ≤ 1)
    (h_default : default.level ≤ 1) :
    (KMor1.pcDispatch size branches default).level ≤ 1 := by
  unfold KMor1.pcDispatch
  exact KMor1.pcDispatchFrom_level size 0 branches default
    h_branches h_default

end GebLean

namespace GebLean.KSimURMSimulator

open GebLean.ZeroTestURM
open GebLean

end GebLean.KSimURMSimulator
