# Adversarial review 1: Ramified-on-vendored-stack plan

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Blockers](#blockers)
- [Majors](#majors)
- [Minors](#minors)
- [Disposition](#disposition)
- [Overall](#overall)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

Round 1, 2026-07-19. Three fresh-context reviewers (signature
verification, proof-route feasibility, style/process/coverage) against
source at branch `feat/ramified-polynomial`. Every claim below was
re-verified against source before entry; one reviewer claim was found
incorrect and is marked.

## Blockers

- B1 (A.2 forward map). The stated motive `fun {x} _ => (toSlice P).W`
  cannot build a `W.mk` node. `W.mk` takes
  `x : F.toSliceDomPFunctor.Obj F.wIndex`, whose compatibility field
  requires each child's `wIndex` to equal the parent's prescribed
  direction-input; a bare `W` child does not carry that equation. Fix:
  fold into the fiber motive `fun {x} _ => { w // wIndex w = x }` (the
  codomain `polyFixSliceEquiv` already targets); then
  `wIndex_toSliceW` is the `.2` projection, not a separate `PolyFix.ind`.
  Re-sequence A.2 Steps 3-6. Legacy precedent: `polyFixFoldAtWithProof`
  (`GebLean/PolyAlg.lean`) folds into `{ y // … }` for exactly this.
- B2 (A.4 Prop predicates). `RType'.IsTower` / `RType'.IsSimple` are
  recursive `Prop` predicates (`RType.lean`), but `W.elim` (hence
  `FreeAlg'.recurse`) binds `(Y : Type uY)` and cannot target `Prop`.
  They must use `W.RecProp` (the `Prop` paramorphism). The plan's
  blanket "each operation via `FreeAlg'.recurse`" is a type error for
  these.

## Majors

- M1 (A.3 / A.4 recursion shape). `FreeAlg.recurse` is a paramorphism:
  its step sees the raw subterms and the recursive results
  (`AlgSig.lean:102-108`), realized via `PolyFix.ind`. `W.elim` is a
  catamorphism: its algebra sees only folded child values. Verified
  paramorphic consumers: `RType.objTarget` and `RType.domains` both
  read the raw subterm `childx` (`OmegaShift.lean:264-300`). Building
  `FreeAlg'.recurse` with the same signature therefore needs the
  tupling encoding (fold into `C × FreeAlg' A`, reconstruct the
  subterm, project), with its own `recurse_mk`. The plan omits this;
  the `freeAlgToNat'` test masks it (that fold ignores subterms).
- M2 (A.4 `interp`). `RType.interp` is `Type`-valued
  (`RType.lean:218`), and `Type : Type 1 ∉ Type 0`, so it cannot
  instantiate `FreeAlg'.recurse`'s `C : Type`. It needs a direct
  `W.elim` at `Y := Type` (`uY = 1`), `p` into `PUnit`. The legacy
  `interp` likewise uses `PolyFix.ind` directly, not `FreeAlg.recurse`.
- M3 (A.2 backward map). The algebra `g` as written does not typecheck:
  `(node.1.2 e).2 : PolyFix P (p (node.1.2 e))`, whereas `PolyFix.mk`
  demands `PolyFix P ((polyBetweenFamily …).hom e)`; these agree only
  propositionally, via the node's compatibility plus `toSlice_r`, so an
  `Eq.rec` transport of each child is required and omitted. The
  round-trip `toSliceW_ofSliceW` (by `W.induction`, the correct
  combinator) must then manage those casts against the IH; this is more
  than "rewriting with `W.elim_mk`."
- M4 (Phase C ill-posed — decision required). `ramified_definability`
  and `ramified_definability_kSim` (`Characterization.lean:161-165,
  195-199`) conclude `collapseDenotation g = arityCongr … f.interp`;
  neither statement contains `FreeAlg natAlgSig`. So "restate with
  `FreeAlg'` in place of `FreeAlg`, obtained by composing
  `natFreeAlgEquiv'`" has no referent to substitute and is vacuous as
  written. (The reviewer claim that `ramifiedDenotation` does not exist
  is incorrect — it is at `Definability/Top.lean:154`; but it is the
  definability-side numeric denotation, whereas the endpoints use
  `collapseDenotation`, `Soundness/Collapse.lean:134`.) Phase C must be
  reframed; the meaningful non-vacuous reading (rebuilding
  `SynCatFO` / `collapseDenotation` on the primed carrier) is out of
  the agreed scope. Requires a user decision before Task C.0.
- M5 (test registration). New test modules under
  `GebLeanTests/PolyBridge/` and `GebLeanTests/Ramified/Polynomial/`
  are not reachable from the `testDriver = "GebLeanTests"` aggregators
  (`GebLeanTests.lean`, `GebLeanTests/Ramified.lean` are explicit
  `import` lists), so `lake test` (and the pre-commit gate) would
  silently skip them. Add: create `GebLeanTests/PolyBridge.lean` and
  `GebLeanTests/Ramified/Polynomial.lean` index modules and register
  them in the respective aggregators (Task A.5, or per creating task).
- M6 (unnamed lemmas). Task A.4 leaves the ten per-operation
  compatibility lemmas unnamed, contradicting the plan's own "name
  exact declarations" rule. Enumerate them with a fixed scheme (for
  example `rTypeSliceEquiv_shape`, `_omegaShift`, `_objTarget`,
  `_domains`, `_interp`, `_ord`, `_tower`, `_isObj`, `_isTower`,
  `_isSimple`).

## Minors

- N1 (A.2 `hg`). `SlicePFunctor.obj p = fun z => F.q z.1.1`
  (`Slice/Basic.lean:200-202`); with `g`'s first component
  `(toSlice P).q node.1.1`, `hg` is `funext (fun _ => rfl)` (and, since
  `cod = PUnit`, trivial regardless). Attribution to `toSlice_q` is
  inaccurate.
- N2 (A.3 defeq). `freeAlgSliceEquiv := polyFixSliceEquiv A.polyEndo
  PUnit.unit` typechecks by unfolding two `def`s; there is no `Eq.rec`
  transport. Drop "transported through the definitional equality."
- N3 (A.1 universes). Consistent at `u = 0` for `X = PUnit.{1}`
  (`AlgSig.polyEndo : PolyEndo PUnit`), so the fiberwise `Equiv` is
  homogeneous. Verify `polyBetweenIndex X X P x` lands in `Type u`
  (not `Type (u+1)`) before committing the `SlicePFunctor.{u,u,u,u}`
  signature in A.1.
- N4 (A.4 operation homes). Name explicitly: `omegaShift`,
  `objTarget`, `domains` are in `OmegaShift.lean`; `ord` is in
  `Soundness/Normalization.lean`; `shape`, `interp`, `tower`, `IsObj`,
  `IsTower`, `IsSimple` in `RType.lean`.
- N5 (A.4 non-recursive ops). Not every op is a tree recursion:
  `shape` is one level (`PolyFix.index`), `IsObj` is shape-based, and
  `tower : Nat → RType` recurses on `Nat` (built from constructors via
  `Nat.rec`, not over the tree). The recursor-only constraint governs
  the tree datatypes; `Nat.rec` is a permitted recursor. State this so
  `tower'` is not forced through a tree recursor.
- N6 (A.4 compatibility proofs). Proved by `W.induction` (Prop motive),
  not "by `RecProp`" (which defines a predicate, not an equation
  proof); `interp`'s is a `Type` equality needing arrow-former
  congruence on the arrow case.
- N7 (commit subjects). Task A.2-A.5 commit subjects are noun phrases;
  mathlib `commit.html` requires an imperative verb. Prepend `add` /
  `implement` / `list` (A.1 is the correct model).
- N8 (module docstrings). Add an explicit module-docstring step to
  A.2 / A.3 / A.4 (only A.1 has one); each with `## Main definitions`
  and `## References`, no novelty claim.
- N9 (spec s2.2). The vendored-API inventory omits `W.induction`,
  `W.RecProp` uses, and `recProp_mk`, which the plan relies on. Align
  the spec summary.

## Disposition

- Fix now (unambiguous): B1, B2, M1, M2, M3, M5, M6, N1-N9. These
  re-specify the Phase A construction routes and the test wiring; none
  changes the agreed scope.
- User decision (blocks Task C.0): M4. Phase C is near-vacuous as
  written; options are (a) drop Phase C, keeping only
  `natFreeAlgEquiv'` from Phase A with a note that the ER endpoints are
  carrier-agnostic; (b) reframe Phase C as an internal transport of the
  carrier where it enters the denotation machinery
  (`ramifiedDenotation` / `n`-denotation on the definability side); (c)
  expand scope to rebuild `SynCatFO'` on the primed carrier (large;
  beyond the agreed "two data structures" scope).

## Overall

Goal remains achievable. The bridge and `FreeAlg'` layers are sound
once the forward fold uses the fiber motive and the paramorphic /
`Prop` / `Type` operations are routed through the correct combinators
(`W.RecProp`, tupling `W.elim`, `Type`-universe `W.elim`). Recommend a
short spike ahead of A.2/A.3 to de-risk the child-transport cast
management (M3) and the tupling paramorphism (M1), and a Phase C
decision (M4) before Task C.0.
