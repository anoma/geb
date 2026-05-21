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

end GebLean

namespace GebLean.KSimURMSimulator

open GebLean.ZeroTestURM
open GebLean

end GebLean.KSimURMSimulator
