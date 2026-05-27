import GebLean.LawvereERKSim.Compiler
import GebLean.LawvereERKSim.Embedding
import GebLean.LawvereERKSim.Loops
import GebLean.LawvereERKSim.Atoms
import GebLean.LawvereERKSim.Comp
import GebLean.LawvereERKSim.BSum
import GebLean.LawvereERKSim.BProd
import GebLean.LawvereERKSim.Top
import GebLean.LawvereERKSim.RuntimeBound
import GebLean.LawvereERKSim.ErToK
import GebLean.LawvereERKSim.ErToKFunctor
import GebLean.LawvereERKSim.Equivalence

/-!
# erToK: ER → K^sim_2 via zero-test URM simulation

The compiler half of the erToK construction: emit a `URMProgram` from an
`ERMor1 a` term such that running the URM long enough produces `e.interp v` in
the output register. This file re-exports the submodules under
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
- `BSum`: bsum PC-layout infrastructure, per-iteration phase preservation,
  the outer iteration `i = 0 .. v 0` induction, and the bsum pre-stop
  correctness theorem `compileER_pre_stop_correct_bsum`.
- `BProd`: bprod PC-layout infrastructure for `compileFrag_bprod`, and
  the size-relation lemma `bprod_exitPC_eq_size_pred`.
- `Top`: structural-induction top-level `compileER_pre_stop_correct` and
  the user-facing `compileER_runFor` output-equality theorem.
- `RuntimeBound`: per-ER-constructor recipe `boundExprKParams`
  realising Tourlakis 2018 Corollary 0.1.0.27 specialised to `compileER`.
- `ErToK`: single-output ER-to-K^sim translator `erToK`, with
  `erToK_level` (level ≤ 2) and `erToK_interp` (interp-faithfulness),
  realising the ⊇ direction of Tourlakis 2018 Corollary 0.1.0.44
  at `n = 2`.
- `ErToKFunctor`: multi-output ER-to-K^sim translator `erToKN`
  with per-slot `erToKN_interp` / `erToKN_level` and the
  ext-eq compatibility lemma `erToKN_compat_extEq`; the
  morphism component `erToKFunctor_map`, functor laws
  `erToKFunctor_map_id` and `erToKFunctor_map_comp`, the
  assembled functor
  `erToKFunctor : LawvereERCat ⥤ LawvereKSimDCat 2`, the
  morphism-level interp preservation
  `erToKFunctor_map_interp`, and the functor-level interp
  equality `erToKFunctor_comp_kInterpFunctor`.
- `Equivalence`: strict functor equalities for the
  round-trip composites
  `erToKFunctor ⋙ kToERFunctor = 𝟭 LawvereERCat` and dual;
  their `eqToIso` natural isomorphisms `erToKKToErIso` and
  `kToErErToKIso`; the packaged equivalence
  `erKSimEquiv : LawvereERCat ≌ LawvereKSimDCat 2` via
  `Equivalence.mk'`; explicit `IsEquivalence` instances on
  `erToKFunctor` and `kToERFunctor`.

## References

- Tourlakis 2018 `PR-complexity-topics.pdf` §0.1.0.37 (URM kernel,
  p. 15–16), §0.1.0.43 (Ritchie–Cobham, p. 21), §0.1.0.44 (proof, p. 22).
- Spec:
  `docs/superpowers/specs/2026-05-16-er-to-k-via-cslib-urm-design.md`.
- File-split spec:
  `docs/superpowers/specs/2026-05-19-lawvere-er-k-sim-file-split-design.md`.
-/
