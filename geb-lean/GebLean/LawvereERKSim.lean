import GebLean.LawvereERKSim.Compiler
import GebLean.LawvereERKSim.Embedding
import GebLean.LawvereERKSim.Loops
import GebLean.LawvereERKSim.Atoms
import GebLean.LawvereERKSim.Comp
import GebLean.LawvereERKSim.BSum

/-!
# erToK: ER → K^sim_2 via zero-test URM simulation

The compiler half of the erToK construction: emit a `URMProgram` from an
`ERMor1 a` term such that running the URM long enough produces `e.interp v` in
the output register. This file re-exports the five submodules under
`GebLean/LawvereERKSim/`:

- `Compiler`: raw and bounded instructions, fragment emission for each ER
  constructor, top-level `compileER` and `compileER_runtime`.
- `Embedding`: step lemmas, the program-embedding framework,
  well-boundedness, and the constructor-agnostic
  `compileER_pre_stop_to_runFor` bridge.
- `Loops`: correctness of `URMRaw.transferLoop`, `URMRaw.preservingTransfer`,
  and the inner loop of `compileFrag_sub`.
- `Atoms`: per-constructor correctness for `zero`, `succ`, `proj`, `sub`
  (both `_runFor_*` and `_pre_stop_correct_atom_*` forms).
- `Comp`: comp m-step machinery, outer iteration, final pre-stop assembly,
  and the comp `_runFor` wrapper.

Future submodules `BSum`, `BProd`, and `Top` (for the top-level structural
induction `compileER_runFor`) follow once Tasks 11f, 11g, 11h land.

## References

- Tourlakis 2018 `PR-complexity-topics.pdf` §0.1.0.37 (URM kernel,
  p. 15–16), §0.1.0.43 (Ritchie–Cobham, p. 21), §0.1.0.44 (proof, p. 22).
- Spec:
  `docs/superpowers/specs/2026-05-16-er-to-k-via-cslib-urm-design.md`.
- File-split spec:
  `docs/superpowers/specs/2026-05-19-lawvere-er-k-sim-file-split-design.md`.
-/
