import GebLean.LawvereERKSim.BProd

/-!
# LawvereERKSim — top-level `compileER` correctness

Top-level correctness theorems for the ER → K^sim_2 compiler. The
two statements below assemble the per-constructor pre-stop and
`≤ t'`-form correctness results from the prior submodules into the
user-facing output-equality theorem for arbitrary `ERMor1 a` terms.

## Main statements

- `compileER_pre_stop_correct`: structural induction over `ERMor1`
  producing the 4-conjunct pre-stop existential (witness `T0` with
  `T0 ≤ compileER_runtime e v`, terminal PC at step `T0`, output
  register equal to `e.interp v`, and strict PC bound on every
  earlier step). Atom cases dispatch to the
  `compileER_pre_stop_correct_atom_*` lemmas in `Atoms.lean`; the
  compositional cases dispatch to `compileER_pre_stop_correct_comp`,
  `compileER_pre_stop_correct_bsum`, and
  `compileER_pre_stop_correct_bprod` (in `Comp.lean`, `BSum.lean`,
  `BProd.lean`).
- `compileER_runFor`: user-facing `≤ t'`-form output-equality. For
  any `t' ≥ compileER_runtime e v`, running the compiled program for
  `t'` steps from `URMState.init` produces `e.interp v` in the
  output register. Follows from `compileER_pre_stop_correct` via the
  constructor-agnostic bridge `compileER_pre_stop_to_runFor`
  (`Embedding.lean`).

## References

- Tourlakis 2018 `PR-complexity-topics.pdf` §0.1.0.37 (URM kernel,
  p. 15–16), §0.1.0.43 (Ritchie–Cobham, p. 21), §0.1.0.44 (proof,
  p. 22).
- Spec:
  `docs/superpowers/specs/2026-05-16-er-to-k-via-cslib-urm-design.md`.
-/

namespace GebLean
namespace LawvereERKSim

open GebLean.ZeroTestURM

/-- Pre-stop correctness of `compileER` by structural induction over
`ERMor1`. For every `e : ERMor1 a` and `v : Fin a → ℕ` there exists
a step count `T0 ≤ compileER_runtime e v` at which the URM has
reached its terminal `.stop` instruction (PC = `instrs.size - 1`)
with the output register equal to `e.interp v`, and on every step
strictly before `T0` the PC is strictly less than `instrs.size - 1`.
Atom cases delegate to the four `compileER_pre_stop_correct_atom_*`
lemmas; the compositional cases delegate to
`compileER_pre_stop_correct_comp`, `compileER_pre_stop_correct_bsum`,
and `compileER_pre_stop_correct_bprod`, each consuming exactly the
structural induction hypothesis produced here. -/
theorem compileER_pre_stop_correct
    {a : ℕ} (e : ERMor1 a) (v : Fin a → ℕ) :
    ∃ T0 : ℕ,
      T0 ≤ compileER_runtime e v ∧
      (URMState.runFor (compileER e)
            (URMState.init (compileER e) v) T0).pc
          = (compileER e).instrs.size - 1 ∧
      (URMState.runFor (compileER e)
            (URMState.init (compileER e) v) T0).regs
          (compileER e).outputReg
        = e.interp v ∧
      (∀ k' < T0,
        (URMState.runFor (compileER e)
            (URMState.init (compileER e) v) k').pc
          < (compileER e).instrs.size - 1) := by
  induction e with
  | zero => exact compileER_pre_stop_correct_atom_zero v
  | succ => exact compileER_pre_stop_correct_atom_succ v
  | proj i => exact compileER_pre_stop_correct_atom_proj i v
  | sub => exact compileER_pre_stop_correct_atom_sub v
  | comp f gs ih_f ih_gs =>
    exact compileER_pre_stop_correct_comp f gs ih_f
      (fun i => ih_gs i) v
  | bsum f ih_f =>
    exact compileER_pre_stop_correct_bsum f ih_f v
  | bprod f ih_f =>
    exact compileER_pre_stop_correct_bprod f ih_f v

/-- Top-level correctness of `compileER` in `≤ t'`-form: for every
`e : ERMor1 a`, `v : Fin a → ℕ`, and `t' ≥ compileER_runtime e v`,
running `compileER e` for `t'` steps from `URMState.init` produces
`e.interp v` in the output register. Combines the pre-stop
existential from `compileER_pre_stop_correct` with the
constructor-agnostic bridge `compileER_pre_stop_to_runFor`. -/
theorem compileER_runFor
    {a : ℕ} (e : ERMor1 a) (v : Fin a → ℕ) (t' : ℕ)
    (ht' : compileER_runtime e v ≤ t') :
    (URMState.runFor (compileER e)
        (URMState.init (compileER e) v) t').regs
        (compileER e).outputReg
      = e.interp v := by
  obtain ⟨T0, hT0, h_pc, h_out, _⟩ := compileER_pre_stop_correct e v
  exact compileER_pre_stop_to_runFor _ v t' ht' ⟨T0, hT0, h_pc, h_out⟩

end LawvereERKSim
end GebLean
