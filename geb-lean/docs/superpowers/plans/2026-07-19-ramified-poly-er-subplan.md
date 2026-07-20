# Phase C sub-plan: inter-definability on the primed type system

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Global constraints](#global-constraints)
- [Task C.1: validation spike](#task-c1-validation-spike)
- [Task C.2: `SlicePFunctor.reindex` and the W-equivalence](#task-c2-slicepfunctorreindex-and-the-w-equivalence)
- [Task C.3: `FreeM.elim` with computation rules](#task-c3-freemelim-with-computation-rules)
- [Task C.4: `Tm'.eval`, the primed quotient layer, and eval agreement](#task-c4-tmeval-the-primed-quotient-layer-and-eval-agreement)
- [Task C.5: primed syntactic category (category and evaluation)](#task-c5-primed-syntactic-category-category-and-evaluation)
- [Task C.6: primed finite products](#task-c6-primed-finite-products)
- [Task C.7: the term-layer equivalence (step 1)](#task-c7-the-term-layer-equivalence-step-1)
- [Task C.8: sorted-signature equivalences and the term translation](#task-c8-sorted-signature-equivalences-and-the-term-translation)
- [Task C.9: presentation equivalences and step 2](#task-c9-presentation-equivalences-and-step-2)
- [Task C.10: primed identifier data (`Ident.lean`, formers)](#task-c10-primed-identifier-data-identlean-formers)
- [Task C.11: `RIdent'.interp`](#task-c11-ridentinterp)
- [Task C.12: Phase A additive agreement lemmas](#task-c12-phase-a-additive-agreement-lemmas)
- [Task C.13: the identifier bridge equivalence](#task-c13-the-identifier-bridge-equivalence)
- [Task C.14: identifier interp agreement](#task-c14-identifier-interp-agreement)
- [Task C.15: the primed higher-order presentation](#task-c15-the-primed-higher-order-presentation)
- [Task C.16: the composite category equivalence](#task-c16-the-composite-category-equivalence)
- [Task C.17: first-order sub-theory replacement](#task-c17-first-order-sub-theory-replacement)
- [Task C.18: collapse packaging and the restriction equivalence](#task-c18-collapse-packaging-and-the-restriction-equivalence)
- [Task C.19: endpoints and documentation](#task-c19-endpoints-and-documentation)
- [Task C.20: whole-branch verification](#task-c20-whole-branch-verification)

<!-- END doctoc generated TOC -->

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> superpowers:subagent-driven-development (recommended) or
> superpowers:executing-plans to implement this plan task-by-task.
> Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Rebuild the presentation layer on the primed types —
`Tm'.eval` and the interpretative quotient, the `Tm'`-based syntactic
category, the `RIdent'` identifier layer, `higherOrder'`, and the
first-order sub-theory replacement — establish
`RMRecCat' ≌ RMRecCat`, and transfer `ramified_definability` /
`ramified_definability_kSim` to the primed stack.

**Architecture:** Per the approved design
([../specs/2026-07-20-ramified-poly-er-design.md](../specs/2026-07-20-ramified-poly-er-design.md)):
generic vendored-side machinery (`reindex`, `FreeM.elim`); a primed
term-evaluation and quotient layer; a primed syntactic category
generic over `Presentation`; a generic signature-translation layer
over legacy `Tm`; the identifier rebuild with its bridge equivalence;
the primed presentation; the two-step composite equivalence; the
first-order replacement; and the collapse packaging with the
transferred endpoints.

**Tech Stack:** Lean 4 + mathlib; vendored
`Geb.Mathlib.Data.PFunctor.Slice.{Basic,W}`; Phase A/B modules
(`GebLean/PolyBridge/`, `GebLean/SliceW/`,
`GebLean/Ramified/Polynomial/`); `lake build` / `lake test`; `jj`
commits.

## Global constraints

- No `noncomputable`; `Classical.choice` in proofs only; the axiom
  gate (`lake build GebLeanAxiomChecks`) accepts only `propext` /
  `Quot.sound` / `Classical.choice`.
- Recursor-only elimination of tree types: `SlicePFunctor.W.elim` /
  `W.induction` / `W.RecProp` / `FreeM.elim` / the free-monad bind on
  the vendored side; `PolyFix.ind` only where a bridge consumes the
  legacy side (here: `SortedSigEquiv.tmMap` and its lemmas,
  `RType.interpCongr`, and the legacy
  halves of agreement proofs). Forbidden on tree types: `induction` /
  `cases` tactics, structural `match` with self-calls,
  `termination_by`, well-founded recursion, `WType.rec` in
  computational content. Non-recursive `match` on a finite shape is
  permitted; `Nat.rec` / `List.foldr` on non-tree data are permitted.
- `GebLean/SliceW/*` imports the vendored stack and mathlib only — no
  `GebLean.PolyAlg`, no `GebLean.Ramified.*` (upstream-promotable).
- File headers: plain `import ...` (no `module` keyword), no
  copyright header, mandatory `/-! -/` module docstring (`# Title`,
  summary, `## Main definitions`, `## Main statements`,
  `## References`, `## Tags`); `/-- -/` on every `def`/`theorem`; no
  novelty claims in `.lean` text (citations only).
- `@[simp]` on constructor-compatibility and field-characterization
  lemmas only; operation/naturality/eval compatibility lemmas are NOT
  `@[simp]`.
- Tests route numeric/semantic assertions through proven lemmas, not
  kernel reduction of composite W-trees.
- Universe polymorphism: `SliceW` modules follow the vendored
  `{uA, uB, uI}` scheme; `Ramified` modules stay at `Type` as the
  legacy modules do.
- Known idioms (Phase B learnings, binding here): prove
  `SliceDomPFunctor.Compatible` goals via dot-notation
  `…toSliceDomPFunctor.compatible_iff` pointwise, never by
  definitional unfolding; pin implicits at `FreeM.node` / `W.mk` and
  at statements without an explicit `sig` / `Γ` / `F` occurrence
  (`(F := …)`, `(sig := …)`, `(Γ := …)`); avoid `rw` on
  `.bind`-headed terms (use `exact` / `Eq.trans`, or rewrite in a
  hypothesis); `FreeM.bind_transport` is oriented
  `(h ▸ t).bind f = h ▸ (t.bind f)`; the `W.induction` closing shape
  is `congrArg W.mk (Subtype.ext (Sigma.ext rfl (heq_of_eq (funext
  …))))`; re-orient `.symm`-defined equivalences' naturality through
  `Equiv.symm_apply_eq`.
- Build with `lake build <Module>` / `lake test` only; never
  `lake env lean`, never `lake clean`. Pre-commit gate for every
  task: `bash scripts/pre-commit.sh`.
- Commits with `jj commit -m "<type>(<scope>): <imperative lowercase
  subject>"` (no trailing period, subject ≤ 72 characters). No
  `jj git push` without user line-by-line review.
- References for transcriptions: D. Leivant, "Ramified recurrence and
  computational complexity III", APAL 96 (1999), DOI
  `10.1016/S0168-0072(98)00040-2` (sections 2.1, 2.3, 2.4, 2.7);
  N. Gambino, J. Kock, "Polynomial functors and polynomial monads",
  Math. Proc. Camb. Phil. Soc. 154 (2013), DOI
  `10.1017/S0305004112000394` (base change, section 1); D. Sannella,
  A. Tarlecki, "Foundations of Algebraic Specification and Formal
  Software Development", Springer, 2012, DOI
  `10.1007/978-3-642-17336-3`, Chapter 1 (signature morphisms and
  reducts); D. Leivant, "Ramified recurrence and computational
  complexity I", Feasible Mathematics II, 1995, DOI
  `10.1007/978-1-4612-2566-9_11` (first-order poly-time context,
  design decision 6).

---

## Task C.1: validation spike

A scratch-module spike (deleted before any commit) validating the
constructions the design marks hardest, sorry-free, before real
tasks depend on them.

- [ ] **Step 1:** In a scratch module importing
  `Geb.Mathlib.Data.PFunctor.Slice.W`, define
  `SlicePFunctor.reindex` for a toy index equivalence
  `e : Bool ≃ Bool` (e.g. `Equiv.boolNot`) over a toy
  `SlicePFunctor Bool Bool`, and build the `W`-equivalence
  `(reindex e F).W ≃ F.W` — confirming, sorry-free, that the
  underlying `PFunctor.W` trees coincide and that admissibility
  transfers by a `Prop`-valued induction (`W.induction` or
  `RecProp`), with `wIndex` conjugating by `e`.
- [ ] **Step 2:** Define `FreeM.elim` (fold into `C : I → Type` with
  a leaf function and a node algebra) via `W.elim` at the sigma
  carrier `Σ i, C i` with index map `Sigma.fst` (the Phase A
  `tupleFold` idiom), and check its computation rules `elim_pure` /
  `elim_node` on the Phase B toy translate functor — sorry-free.
- [ ] **Step 3:** For a two-operation toy `SortedSig Bool` and a toy
  sort equivalence, build the `DefnShape'`-style term-translation
  composite: a `SortedSigEquiv.tmMap`-style forward map by
  `PolyFix.ind` with `get`-of-`map` transports (the C.8 `get_map`
  helper, stated locally in the scratch), composed with
  `tmSliceEquiv` — confirming, sorry-free, the reindex transports
  at variable and operation nodes.
- [ ] **Step 4:** Validate the `defn'`-case agreement shape on the
  toy data: evaluation of the translated term in a model matched by
  a carrier equivalence equals that equivalence applied to the
  primed evaluation (the `tmMap_eval`-plus-`tmSliceEquiv_eval`
  composite on one operation node) — sorry-free.
- [ ] **Step 5:** Record working term shapes (motives, transport
  idioms, `hg` discharges) as notes in the corresponding task steps
  if they differ from what is written there; delete the scratch
  module.

## Task C.2: `SlicePFunctor.reindex` and the W-equivalence

**Files:**

- Create: `GebLean/SliceW/Reindex.lean`
- Create: `GebLeanTests/SliceW/Reindex.lean`
- Modify: `GebLean/SliceW.lean` (`import` this module)
- Modify: `GebLeanTests.lean` (add
  `import GebLeanTests.SliceW.Reindex`)

**Interfaces:**

- Consumes: `SlicePFunctor` fields `A`/`B`/`q`/`r`, `rCurried`,
  `toSliceDomPFunctor.compatible_iff`
  (`Geb.Mathlib.Data.PFunctor.Slice.Basic`); `W`, `wIndex`, `W.mk`,
  `W.wIndex_mk`, `W.induction`, `W.dest`
  (`Geb.Mathlib.Data.PFunctor.Slice.W`); `Equiv` (mathlib).
- Produces:
  - `def SlicePFunctor.reindex (e : I ≃ J)`
    `(F : SlicePFunctor I I) : SlicePFunctor J J` — underlying
    `PFunctor` unchanged (`A := F.A`, `B := F.B`), `q := e ∘ F.q`,
    `r := e ∘ F.r`.
  - `@[simp]` characterization lemmas `reindex_A`, `reindex_B`,
    `reindex_q` (`= e (F.q a)`), `reindex_r` (`= e (F.r ⟨a, b⟩)`),
    each by `rfl`.
  - `def SlicePFunctor.reindex.wMap (e : I ≃ J) (F) :`
    `F.W → (reindex e F).W` — the identity on underlying trees with
    admissibility transferred: realized by `W.elim F
    ((reindex e F).W) (fun w' => e.symm ((reindex e F).wIndex w'))
    g hg` where `g` rebuilds each node by `W.mk` with the same shape
    and children and the conjugated compatibility (pointwise via
    `compatible_iff`, `reindex_r`, and `e.symm_apply_apply`), or —
    if the spike's Step 1 found the subtype-transfer form cheaper —
    as a `Subtype.map`-style validity transfer; the spike's recorded
    shape wins.
  - `theorem SlicePFunctor.reindex.wIndex_wMap (e F)`
    `(z : F.W) : (reindex e F).wIndex (wMap e F z) = e (F.wIndex z)`.
  - `theorem SlicePFunctor.reindex.wMap_mk` (`@[simp]`) —
    constructor naturality of `wMap` at `W.mk`.
  - `def SlicePFunctor.reindex.wEquiv (e F) :`
    `F.W ≃ (reindex e F).W` — `wMap` for `e` against the `wMap` of
    the inverse reading (`reindex e⁻¹ (reindex e F) = F` holds only
    propositionally, so the inverse leg is its own `W.elim` back
    into `F.W`, mirroring `wMap` with `e.symm` conjugations); round
    trips by `W.induction` with the standard closing shape.
  - `def SlicePFunctor.reindex.wEquivFiber (e F) (j : J) :`
    `{ w : F.W // F.wIndex w = e.symm j } ≃`
    `{ w' : (reindex e F).W // (reindex e F).wIndex w' = j }` —
    `wEquiv` restricted along `wIndex_wMap` (both directions;
    `e.apply_symm_apply` closes the index legs).

**Steps:**

- [ ] **Step 1: Write the failing test.** In
  `GebLeanTests/SliceW/Reindex.lean`, with the spike's toy functor
  and `Equiv.boolNot`: assert `reindex_q`/`reindex_r` by `simp`, the
  index law `wIndex_wMap` on a sample `W.mk` tree, and one round
  trip via `Equiv.symm_apply_apply`.
- [ ] **Step 2: Run to verify it fails.** Run
  `lake build GebLeanTests.SliceW.Reindex`. Expected: failure,
  `reindex` not found.
- [ ] **Step 3: Implement** the definitions in interface order, one
  at a time (module docstring cites Gambino–Kock 2013, section 1,
  base change).
- [ ] **Step 4: Run to verify it passes.** Run
  `lake build GebLeanTests.SliceW.Reindex`. Expected: success.
- [ ] **Step 5: Gate.** Run `bash scripts/pre-commit.sh`.
- [ ] **Step 6: Commit.**

```bash
jj commit -m "feat(slicew): add base change along an index equivalence"
```

## Task C.3: `FreeM.elim` with computation rules

**Files:**

- Modify: `GebLean/SliceW/FreeM.lean`
- Modify: `GebLeanTests/SliceW/FreeM.lean`

**Interfaces:**

- Consumes: `FreeM`, `FreeM.pure`, `FreeM.node`, `translate` and its
  `@[simp]` lemmas (Phase B); `W.elim`, `W.elim_mk`, `W.comp_elim`
  (vendored stack).
- Produces:
  - `def SlicePFunctor.FreeM.elim {v : Y → I} {F} (C : I → Type u)`
    `(leaf : ∀ i, { y : Y // v y = i } → C i)`
    `(node : ∀ a : F.A, (∀ b : F.B a, C (F.rCurried a b)) → C (F.q a))`
    `{i : I} (t : FreeM v F i) : C i` — one
    `W.elim (translate v F) (Σ i, C i) Sigma.fst g hg` on `t.1`,
    with `g` splitting the node shape: at `Sum.inl y` return
    `⟨v y, leaf (v y) ⟨y, rfl⟩⟩`; at `Sum.inr a` with folded
    children `c` (each a sigma with index component pinned by the
    algebra's over-`I` condition to `F.rCurried a b`) return
    `⟨F.q a, node a (fun b => cast (congrArg C (child index eq))
    (c b).2)⟩`; the final value is the sigma's second component
    transported along `t.2` (the Phase A `tupleFold` idiom; the
    spike's Step 2 recorded shape wins on the cast plumbing).
  - `theorem SlicePFunctor.FreeM.elim_pure (C leaf node) {i}`
    `(a : { y : Y // v y = i }) :`
    `(FreeM.pure a).elim C leaf node = leaf i a` — by
    `obtain ⟨y, hy⟩ := a; subst hy`, then `W.elim_mk` (expected
    `rfl` after the subst).
  - `theorem SlicePFunctor.FreeM.elim_node (C leaf node) (a : F.A)`
    `(c : (b : F.B a) → FreeM v F (F.rCurried a b)) :`
    `(FreeM.node a c).elim C leaf node =`
    `node a (fun b => (c b).elim C leaf node)` — `W.elim_mk` at the
    node shape, then `congrArg` on the children family with the
    cast-elimination at the pinned indices.
  - `theorem SlicePFunctor.FreeM.elim_transport (C leaf node)`
    `{i i'} (h : i = i') (t : FreeM v F i) :`
    `(h ▸ t).elim C leaf node = h ▸ (t.elim C leaf node)` — by
    `subst h; rfl`.

  Computation rules are NOT `@[simp]` (operation-level policy).

**Steps:**

- [ ] **Step 1: Write the failing test.** On the Phase B toy
  translate functor: fold a leaf and a one-node tree into a constant
  family and assert the values by rewriting with `elim_pure` /
  `elim_node` only.
- [ ] **Step 2: Run to verify it fails.** Run
  `lake build GebLeanTests.SliceW.FreeM`. Expected: failure, `elim`
  not found.
- [ ] **Step 3: Implement** `elim`, `elim_pure`, `elim_node`,
  `elim_transport`, one at a time (docstring cites Gambino–Kock 2013,
  the free monad's fold).
- [ ] **Step 4: Run to verify it passes.** Run
  `lake build GebLeanTests.SliceW.FreeM`. Expected: success.
- [ ] **Step 5: Gate.** Run `bash scripts/pre-commit.sh`.
- [ ] **Step 6: Commit.**

```bash
jj commit -m "feat(slicew): add the free-monad fold with computation rules"
```

## Task C.4: `Tm'.eval`, the primed quotient layer, and eval agreement

**Files:**

- Create: `GebLean/Ramified/Polynomial/Interp.lean`
- Create: `GebLeanTests/Ramified/Polynomial/Interp.lean`
- Modify: `GebLean/Ramified/Polynomial/Term.lean` (add
  `Tm'.reind_symm`, `Tm'.reind_symm'`)
- Modify: `GebLean/Ramified/Polynomial.lean` (`import` the new
  module)
- Modify: `GebLeanTests/Ramified/Polynomial.lean` (`import` the
  test)

**Interfaces:**

- Consumes: `Tm'`, `Tm'.var`, `Tm'.op`, `Tm'.subst`, `Tm'.reind`,
  `tmSliceEquiv`, `tmSliceEquiv_var`, `tmSliceEquiv_op`,
  `tmSliceEquiv_subst` (Phase B); `FreeM.elim`, `elim_pure`,
  `elim_node`, `elim_transport` (Task C.3); `SortedModel`,
  `SortedModel.Env`, `Presentation`, `standardModel`, `Tm.eval`,
  `Tm.eval_transport` (`GebLean/Ramified/Interp.lean`).
- Produces:
  - `theorem Tm'.reind_symm {sig} {Γ} {a b : S} (h : a = b)`
    `(t : Tm' sig Γ a) : Tm'.reind h.symm (Tm'.reind h t) = t` and
    `theorem Tm'.reind_symm'` (the reverse composite) — each by
    `subst h; rfl`, in `Polynomial/Term.lean`.
  - `def Tm'.eval {sig : SortedSig S} {Γ : Ctx S}`
    `(M : SortedModel sig) (ρ : M.Env Γ) {s : S}`
    `(t : Tm' sig Γ s) : M.carrier s` — `FreeM.elim M.carrier` with
    leaf `fun _ a => cast (congrArg M.carrier a.2) (ρ a.1)` and node
    reading the `toSlice`-shape's operation and result equality:
    `fun ⟨s, o, h⟩ ih => cast (congrArg M.carrier h)
    (M.interpOp o ih)` (shape split is non-recursive; the arity
    positions coerce definitionally as in `Tm'.op`).
  - `theorem Tm'.eval_var {sig Γ} (M ρ) (i : Fin Γ.length) :`
    `(Tm'.var (sig := sig) i).eval M ρ = ρ i` — from `elim_pure`
    (the `rfl`-cast vanishes).
  - `theorem Tm'.eval_op {sig Γ} (M ρ) (o : sig.Op) (args) :`
    `(Tm'.op o args).eval M ρ =`
    `M.interpOp o (fun i => (args i).eval M ρ)` — from `elim_node`.
  - `theorem Tm'.eval_transport (M ρ) {x y : S} (h : x = y)`
    `(t : Tm' sig Γ x) : (Tm'.reind h t).eval M ρ =`
    `cast (congrArg M.carrier h) (t.eval M ρ)` — `subst h; rfl`.
  - `theorem Tm'.eval_subst {sig} {Γ Δ} {s} (M : SortedModel sig)`
    `(t : Tm' sig Γ s) (σ : ∀ i, Tm' sig Δ (Γ.get i)) (ρ : M.Env Δ) :`
    `(t.subst σ).eval M ρ = t.eval M (fun i => (σ i).eval M ρ)` —
    raw lemma over the underlying trees by `W.induction` with the
    `Sum` shape split (leaf: `elim_transport` and `pure`-leaf
    reduction; node: `bind_node`, `elim_node`, `congrArg` with the
    induction hypotheses), then wrapped; mirrors the legacy
    `Tm.eval_subst`.
  - `structure QuotRel' (sig : SortedSig S)` — fields
    `rel : (Γ : Ctx S) → (s : S) → Setoid (Tm' sig Γ s)` and
    `subst_congr : ∀ {Γ Δ s} (t t' : Tm' sig Γ s)`
    `(σ σ' : ∀ i, Tm' sig Δ (Γ.get i)), (rel Γ s) t t' →`
    `(∀ i, (rel Δ _) (σ i) (σ' i)) →`
    `(rel Δ s) (t.subst σ) (t'.subst σ')`; plus
    `theorem QuotRel'.rel_reind` (mirror of `QuotRel.rel_reind`, by
    `subst h`).
  - `def interpSetoid' (P : Presentation) (Γ : Ctx P.S) (s : P.S) :`
    `Setoid (Tm' P.sig Γ s)` — extensional equality of `Tm'.eval` at
    `standardModel P` under every environment (mirror of
    `interpSetoid`).
  - `def interpQuotRel' (P : Presentation) : QuotRel' P.sig` — the
    family with `subst_congr` by `Tm'.eval_subst` (mirror of
    `interpQuotRel`).
  - `theorem tmSliceEquiv_eval {sig : SortedSig S} {Γ : Ctx S} {s}`
    `(M : SortedModel sig) (ρ : M.Env Γ) (t : Tm' sig Γ s) :`
    `(tmSliceEquiv Γ s t).eval M ρ = t.eval M ρ` — raw
    `W.induction` over `t`'s underlying tree with the `Sum` shape
    split: the leaf case reduces both sides through
    `tmSliceEquiv`-of-`pure` (a transported `tmSliceEquiv_var`,
    via `FreeM.pure_transport` and the legacy `Tm.eval_transport` /
    primed `Tm'.eval_transport`); the node case through
    `tmSliceEquiv_op`, `Tm.eval`'s operation reduction, and
    `Tm'.eval_op` with the induction hypotheses. NOT `@[simp]`.

**Steps:**

- [ ] **Step 1: Write the failing test.** Reuse the Phase B
  two-sorted toy signature: define a two-element model, assert
  `Tm'.eval_var` / `Tm'.eval_op` values on a small term, one
  `Tm'.eval_subst` instance, and one `tmSliceEquiv_eval` instance —
  all through the named lemmas.
- [ ] **Step 2: Run to verify it fails.** Run
  `lake build GebLeanTests.Ramified.Polynomial.Interp`. Expected:
  failure, `Tm'.eval` not found.
- [ ] **Step 3: Implement** in interface order (reind lemmas in
  `Term.lean` first, then the new module: eval, computation rules,
  eval_subst, `QuotRel'`, `interpSetoid'` / `interpQuotRel'`,
  `tmSliceEquiv_eval`), one declaration at a time. Module docstring
  cites Leivant 1999 section 2.7 (as the legacy `Interp.lean` does).
- [ ] **Step 4: Run to verify it passes.** Run
  `lake build GebLeanTests.Ramified.Polynomial.Interp`. Expected:
  success.
- [ ] **Step 5: Gate.** Run `bash scripts/pre-commit.sh`.
- [ ] **Step 6: Commit.**

```bash
jj commit -m "feat(ramified): add primed evaluation and interpretative quotient"
```

## Task C.5: primed syntactic category (category and evaluation)

**Files:**

- Create: `GebLean/Ramified/Polynomial/SynCat.lean`
- Create: `GebLeanTests/Ramified/Polynomial/SynCat.lean`
- Modify: `GebLean/Ramified/Polynomial.lean`,
  `GebLeanTests/Ramified/Polynomial.lean` (imports)

**Interfaces:**

- Consumes: Task C.4's layer; `Tm'` clone laws (Phase B);
  `piSetoid` (mathlib); `Category` (mathlib).
- Produces (all mirroring `GebLean/Ramified/SynCat.lean` with `Tm'`
  in place of `Tm` and `QuotRel'` in place of `QuotRel`):
  - `theorem Tm'.reind_index` (mirror of `Tm.reind_index`).
  - `def HomTuple' (P : Presentation) (Γ Δ : Ctx P.S) : Type :=`
    `∀ i : Fin Δ.length, Tm' P.sig Γ (Δ.get i)`; `HomTuple'.id`
    (variable tuple), `HomTuple'.comp` (componentwise `Tm'.subst`).
  - `def homSetoid' (P) (r : QuotRel' P.sig) (Γ Δ) :`
    `Setoid (HomTuple' P Γ Δ)` (pointwise closure via `piSetoid`);
    `def Hom' (P) (r) (Γ Δ) : Type := Quotient (homSetoid' P r Γ Δ)`;
    `Hom'.id`, `Hom'.comp` (lifted; well-defined by `subst_congr`);
    `Hom'.id_comp` / `comp_id` / `assoc` from `Tm'.subst_id` /
    `Tm'.var_subst` / `Tm'.subst_subst`.
  - `def HomTuple'.eval` (componentwise `Tm'.eval`), `def Hom'.eval`
    (lift over `interpQuotRel'`), `@[simp] theorem Hom'.eval_mk`,
    `theorem Hom'.eval_comp` (from `Tm'.eval_subst`), and
    `theorem Hom'.eval_id` (mirror of the legacy `Hom.eval_id` in
    `Soundness/Collapse.lean`, placed here with the primed layer).
  - `@[nolint unusedArguments] def SynCat' (P : Presentation)`
    `(_r : QuotRel' P.sig) : Type := Ctx P.S` with
    `instance SynCat'.instCategory (P) (r) : Category (SynCat' P r)`
    (fields from the `Hom'` layer).

**Steps:**

- [ ] **Step 1: Write the failing test.** On the toy signature
  packaged as a toy `Presentation` (sorts `Bool`, the Task C.4 toy
  model as `std`, `IsObj := fun _ => True`, `alg := natAlgSig`):
  assert `Hom'.id_comp` / `Hom'.assoc` instances on sample tuples
  and one `Hom'.eval_comp` instance.
- [ ] **Step 2: Run to verify it fails.** Run
  `lake build GebLeanTests.Ramified.Polynomial.SynCat`. Expected:
  failure, `Hom'` not found.
- [ ] **Step 3: Implement** in interface order, one declaration at a
  time (docstring mirrors the legacy `SynCat.lean` references —
  Leivant 1999 section 2.1 and the `LawvereERCat` precedent).
- [ ] **Step 4: Run to verify it passes.** Run
  `lake build GebLeanTests.Ramified.Polynomial.SynCat`. Expected:
  success.
- [ ] **Step 5: Gate.** Run `bash scripts/pre-commit.sh`.
- [ ] **Step 6: Commit.**

```bash
jj commit -m "feat(ramified): add the primed syntactic category"
```

## Task C.6: primed finite products

**Files:**

- Modify: `GebLean/Ramified/Polynomial/SynCat.lean`
- Modify: `GebLeanTests/Ramified/Polynomial/SynCat.lean`

**Interfaces:**

- Consumes: Task C.5; `finAppL`, `finAppR`, `get_finAppL`,
  `get_finAppR`, `get_append_lt`, `get_append_ge`, `finApp_cases`
  (legacy `SynCat.lean` — sort-generic, reused as-is);
  `Tm'.reind_symm` / `reind_symm'` (Task C.4); `Tm'.subst_reind`
  (Phase B); `CartesianMonoidalCategory`,
  `ofChosenFiniteProducts`, `BinaryFan.IsLimit.mk`,
  `IsTerminal.ofUniqueHom` (mathlib).
- Produces (mirrors of the legacy product layer):
  - `def joinTuple'`, `def fstTuple'`, `def sndTuple'`;
    `theorem joinTuple'_finAppL` / `joinTuple'_finAppR`;
    `theorem fst_join'` / `snd_join'` (via `Tm'.subst_reind`,
    `Tm'.var_subst`, `Tm'.reind_symm'`);
    `theorem joinTuple'_rel` (via `QuotRel'.rel_reind` and
    `finApp_cases`).
  - `def SynProd'.fst` / `SynProd'.snd` / `SynProd'.lift`;
    `theorem SynProd'.lift_fst` / `lift_snd` / `lift_uniq`.
  - `def terminalTuple'`, `def Hom'.terminal`,
    `theorem Hom'.terminal_uniq`; `def synTerminalCone'`,
    `def synProdCone'`;
    `instance SynCat'.instCartesianMonoidalCategory`.

**Steps:**

- [ ] **Step 1: Write the failing test.** Assert
  `SynProd'.lift_fst` / `lift_snd` instances on sample tuples over
  the toy presentation, and the terminal uniqueness on a sample hom.
- [ ] **Step 2: Run to verify it fails.** Run
  `lake build GebLeanTests.Ramified.Polynomial.SynCat`. Expected:
  failure, `SynProd'` not found.
- [ ] **Step 3: Implement** in interface order (raw tuple layer,
  then quotient layer, then the instance).
- [ ] **Step 4: Run to verify it passes.** Run
  `lake build GebLeanTests.Ramified.Polynomial.SynCat`. Expected:
  success.
- [ ] **Step 5: Gate.** Run `bash scripts/pre-commit.sh`.
- [ ] **Step 6: Commit.**

```bash
jj commit -m "feat(ramified): add finite products to the primed syntactic category"
```

## Task C.7: the term-layer equivalence (step 1)

**Files:**

- Create: `GebLean/Ramified/Polynomial/SynCatEquiv.lean`
- Create: `GebLeanTests/Ramified/Polynomial/SynCatEquiv.lean`
- Modify: `GebLean/Ramified/Polynomial.lean`,
  `GebLeanTests/Ramified/Polynomial.lean` (imports)

**Interfaces:**

- Consumes: Tasks C.4–C.5; `tmSliceEquiv` and its three naturality
  lemmas (Phase B); `tmSliceEquiv_eval` (Task C.4); `SynCat`,
  `Hom`, `interpQuotRel` (legacy); `CategoryTheory.Equivalence`,
  `eqToIso` (mathlib).
- Produces:
  - `theorem tmSliceEquiv_rel (P : Presentation) {Γ s}`
    `(t u : Tm' P.sig Γ s) :`
    `(interpSetoid' P Γ s) t u ↔`
    `(interpSetoid P Γ s) (tmSliceEquiv Γ s t) (tmSliceEquiv Γ s u)`
    — both directions from `tmSliceEquiv_eval`.
  - `def synCatSliceFunctor (P : Presentation) :`
    `SynCat' P (interpQuotRel' P) ⥤ SynCat P (interpQuotRel P)` —
    identity on objects; on homs, `Quotient.lift` of componentwise
    `tmSliceEquiv` (well-defined by `tmSliceEquiv_rel`); `map_id`
    from `tmSliceEquiv_var`, `map_comp` from `tmSliceEquiv_subst`
    (each by `Quotient.ind` and `congrArg (Quotient.mk _)` on a
    `funext`).
  - `def synCatSliceInverse (P)` — the same with
    `(tmSliceEquiv Γ s).symm` componentwise (well-definedness from
    `tmSliceEquiv_rel` read backward; functor laws through
    `Equiv.symm_apply_eq` from the forward naturality).
  - `def synCatSliceEquiv (P : Presentation) :`
    `SynCat' P (interpQuotRel' P) ≌ SynCat P (interpQuotRel P)` —
    functor and inverse as above; `unitIso` / `counitIso` by
    `NatIso.ofComponents` at `Iso.refl` (objects are fixed;
    naturality squares reduce by `Quotient.ind` and the `Equiv`
    round trips `Equiv.symm_apply_apply` / `apply_symm_apply`).

**Steps:**

- [ ] **Step 1: Write the failing test.** On the toy presentation:
  assert the functor's `map` on a sample hom equals the expected
  legacy hom class (through `tmSliceEquiv_op`), and a round trip
  `(synCatSliceEquiv P).inverse.map ((synCatSliceEquiv P).functor.map
  f) = f` instance via the equivalence laws.
- [ ] **Step 2: Run to verify it fails.** Run
  `lake build GebLeanTests.Ramified.Polynomial.SynCatEquiv`.
  Expected: failure, names not found.
- [ ] **Step 3: Implement** in interface order.
- [ ] **Step 4: Run to verify it passes.** Run
  `lake build GebLeanTests.Ramified.Polynomial.SynCatEquiv`.
  Expected: success.
- [ ] **Step 5: Gate.** Run `bash scripts/pre-commit.sh`.
- [ ] **Step 6: Commit.**

```bash
jj commit -m "feat(ramified): relate the primed and legacy syntactic categories"
```

## Task C.8: sorted-signature equivalences and the term translation

**Files:**

- Create: `GebLean/Ramified/SigEquiv.lean`
- Create: `GebLeanTests/Ramified/SigEquiv.lean`
- Modify: `GebLean/Ramified.lean`, `GebLeanTests/Ramified.lean`
  (imports; after their dependencies, per the file's import order)

**Interfaces:**

- Consumes: `SortedSig` (`GebLean/Ramified/SortedSig.lean`); `Ctx`,
  `Tm`, `Tm.var`, `Tm.op`, `Tm.subst`, `Tm.reind`
  (`GebLean/Ramified/Term.lean`); `PolyFix.ind`
  (`GebLean/PolyAlg.lean`); `List.getElem_map`,
  `List.get_eq_getElem`, `List.map_map`, `Equiv` (mathlib / core).
- Produces (structure named `SortedSigEquiv`, top-level in the
  `GebLean.Ramified` namespace — not `SortedSig.Equiv` — to avoid
  shadowing mathlib's `Equiv` inside the namespace):
  - `theorem get_map {S S' : Type} (f : S → S') (Γ : Ctx S)`
    `(i : Fin (Γ.map f).length) : (Γ.map f).get i =`
    `f (Γ.get (Fin.cast (by simp) i))` — the `get`-of-`map` reading
    (no such lemma exists in core or mathlib, which carry only
    `List.getElem_map`); by `List.get_eq_getElem` and
    `List.getElem_map`. The shared transport helper every later
    translation cites.
  - `structure SortedSigEquiv {S S' : Type} (sig : SortedSig S)`
    `(sig' : SortedSig S')` with fields
    `sortEquiv : S ≃ S'`, `opEquiv : sig.Op ≃ sig'.Op`,
    `arity_comm : ∀ o, sig'.arity (opEquiv o) =`
    `(sig.arity o).map sortEquiv`,
    `result_comm : ∀ o, sig'.result (opEquiv o) =`
    `sortEquiv (sig.result o)`.
  - `def SortedSigEquiv.symm : SortedSigEquiv sig sig' →`
    `SortedSigEquiv sig' sig` — reversed equivalences;
    `arity_comm` / `result_comm` re-derived by applying the forward
    fields at `opEquiv.symm o'` and cancelling with
    `Equiv.apply_symm_apply` and
    `List.map_map`-plus-`sortEquiv.symm_comp_self` (route:
    rewrite the forward equation, then `List.map_id` after the
    composite collapses).
  - `def SortedSigEquiv.tmMap (e : SortedSigEquiv sig sig')`
    `{Γ : Ctx S} {s : S} (t : Tm sig Γ s) :`
    `Tm sig' (Γ.map e.sortEquiv) (e.sortEquiv s)` — by
    `PolyFix.ind`: a variable `⟨i, h⟩` becomes
    `Tm.reind (by rw [get_map, h]) (Tm.var (Fin.cast
    (List.length_map …).symm i))` (index re-typed along
    `List.length_map`); an operation node `o` with translated
    children becomes `Tm.reind (e.result_comm o).symm ▸ …`-free
    form: `Tm.reind ((e.result_comm o).symm) (Tm.op (e.opEquiv o)
    (fun i => Tm.reind (by rw [e.arity_comm]; exact (get_map
    …).symm) (child at the re-typed position)))` — the exact
    transport spelling from the spike's Step 3 notes.
  - `theorem SortedSigEquiv.tmMap_var`, `tmMap_op` — the
    constructor-naturality statements of the two cases (NOT
    `@[simp]`; they carry reindex transports).
  - `theorem SortedSigEquiv.tmMap_reind` — commutation with
    `Tm.reind` (`subst h; rfl`).
  - `theorem SortedSigEquiv.tmMap_subst (e) (t) (σ) :`
    `e.tmMap (t.subst σ) = (e.tmMap t).subst (fun j => Tm.reind …`
    `(e.tmMap (σ (re-typed j))))` — by `PolyFix.ind` with
    `Tm.subst_reind` and `Tm.var_subst` at the leaf case (statement
    fixes the substitution tuple as the `get_map`-transported
    translate of `σ`).
  - `theorem SortedSigEquiv.tmMap_symm_tmMap (e) (t) :`
    `(transport along List.map_map and sortEquiv round trip of`
    `(e.symm.tmMap (e.tmMap t))) = t` and the reverse — by
    `PolyFix.ind`; the statement is up to `Tm.reind` and a context
    cast along `(Γ.map e.sortEquiv).map e.sortEquiv.symm = Γ`
    (`List.map_map` plus `Equiv.symm_comp_self` plus `List.map_id`);
    package the two as
    `def SortedSigEquiv.tmEquiv (e) (Γ) (s) : Tm sig Γ s ≃`
    `Tm sig' (Γ.map e.sortEquiv) (e.sortEquiv s)`.

**Steps:**

- [ ] **Step 1: Write the failing test.** Define two toy two-sorted
  signatures related by a nontrivial sort equivalence (`Bool` with
  `Equiv.boolNot`), build the `SortedSigEquiv`, and assert:
  `tmMap_var` and `tmMap_op` on samples, one `tmMap_subst` instance,
  and one `tmEquiv` round trip.
- [ ] **Step 2: Run to verify it fails.** Run
  `lake build GebLeanTests.Ramified.SigEquiv`. Expected: failure,
  `SortedSigEquiv` not found.
- [ ] **Step 3: Implement** in interface order, one declaration at a
  time (docstring cites Sannella–Tarlecki 2012, Chapter 1).
- [ ] **Step 4: Run to verify it passes.** Run
  `lake build GebLeanTests.Ramified.SigEquiv`. Expected: success.
- [ ] **Step 5: Gate.** Run `bash scripts/pre-commit.sh`.
- [ ] **Step 6: Commit.**

```bash
jj commit -m "feat(ramified): add sorted-signature equivalences with term translation"
```

## Task C.9: presentation equivalences and step 2

**Files:**

- Create: `GebLean/Ramified/PresentationEquiv.lean`
- Create: `GebLeanTests/Ramified/PresentationEquiv.lean`
- Modify: `GebLean/Ramified.lean`, `GebLeanTests/Ramified.lean`
  (imports)

**Interfaces:**

- Consumes: Task C.8; `Presentation`, `standardModel`,
  `SortedModel`, `Tm.eval`, `Tm.eval_transport`, `Tm.eval_subst`
  (`GebLean/Ramified/Interp.lean`); `SynCat`, `Hom`,
  `interpQuotRel`, `interpSetoid` (`GebLean/Ramified/SynCat.lean`,
  `Interp.lean`); `Equivalence`, `eqToIso`, `NatIso.ofComponents`
  (mathlib).
- Produces:
  - `structure PresentationEquiv (P P' : Presentation)` with fields
    `sigEquiv : SortedSigEquiv P.sig P'.sig`,
    `carrierEquiv : ∀ s, (standardModel P).carrier s ≃`
    `(standardModel P').carrier (sigEquiv.sortEquiv s)` (an
    equivalence, not an equality: at the Phase C instantiation the
    base carriers `FreeAlg' A` and `FreeAlg A` are related only by
    `freeAlgSliceEquiv`), and
    `interpOp_comm : ∀ o args, (standardModel P').interpOp`
    `(sigEquiv.opEquiv o) (matched args) = carrierEquiv _`
    `((standardModel P).interpOp o args)` — the argument matching
    reads each position through `carrierEquiv` and the `Tm.reind`
    transports along `arity_comm` (spelling fixed as in
    `stdConstructorInterp`'s cast idiom, with `Equiv.cast` where a
    sort-level equality supplies the transport).
  - `theorem PresentationEquiv.tmMap_eval (e : PresentationEquiv P`
    `P') {Γ s} (t : Tm P.sig Γ s) (ρ : (standardModel P).Env Γ) :`
    `(e.sigEquiv.tmMap t).eval (standardModel P')`
    `(matched environment) = e.carrierEquiv s (t.eval (standardModel`
    `P) ρ)` — by `PolyFix.ind` (the `foTm_eval` pattern with
    `carrierEquiv` in place of the value casts); the matched
    environment pushes `ρ` forward along `get_map` and
    `carrierEquiv`.
  - `def PresentationEquiv.synCatFunctor (e) : SynCat P`
    `(interpQuotRel P) ⥤ SynCat P' (interpQuotRel P')` — object map
    `List.map e.sigEquiv.sortEquiv`; hom map by `Quotient.lift` of
    the componentwise `get_map`-transported `tmMap`;
    well-definedness and `map_id` / `map_comp` by `Quotient.sound`
    from `tmMap_eval` (the `foInclusion` pattern: interpretative
    equality, no syntactic identities needed).
  - `def PresentationEquiv.symm : PresentationEquiv P P' →`
    `PresentationEquiv P' P` (via `SortedSigEquiv.symm`; carrier
    and interp fields re-derived through the forward ones).
  - `def PresentationEquiv.synCatEquiv (e) : SynCat P (interpQuotRel`
    `P) ≌ SynCat P' (interpQuotRel P')` — `synCatFunctor` of `e` and
    of `e.symm`; `unitIso` / `counitIso` by `NatIso.ofComponents`
    at `eqToIso` on the object round trips (`List.map_map`,
    `Equiv.symm_comp_self`, `List.map_id`), naturality squares by
    `Quotient.ind` and `Quotient.sound` from `tmMap_eval` both ways.

**Steps:**

- [ ] **Step 1: Write the failing test.** Package the Task C.8 toy
  signatures as two toy `Presentation`s with matched models; build
  the `PresentationEquiv`; assert one `tmMap_eval` instance and one
  functor `map_comp` instance.
- [ ] **Step 2: Run to verify it fails.** Run
  `lake build GebLeanTests.Ramified.PresentationEquiv`. Expected:
  failure, names not found.
- [ ] **Step 3: Implement** in interface order (docstring cites
  Sannella–Tarlecki 2012, Chapter 1, reduct/translation functors).
- [ ] **Step 4: Run to verify it passes.** Run
  `lake build GebLeanTests.Ramified.PresentationEquiv`. Expected:
  success.
- [ ] **Step 5: Gate.** Run `bash scripts/pre-commit.sh`.
- [ ] **Step 6: Commit.**

```bash
jj commit -m "feat(ramified): relate syntactic categories of equivalent presentations"
```

## Task C.10: primed identifier data (`Ident.lean`, formers)

**Files:**

- Create: `GebLean/Ramified/Polynomial/Ident.lean`
- Create: `GebLeanTests/Ramified/Polynomial/Ident.lean`
- Modify: `GebLean/Ramified/Polynomial.lean`,
  `GebLeanTests/Ramified/Polynomial.lean` (imports)

**Interfaces:**

- Consumes: `RType'`, `RType'.o` / `arrow` / `omega`,
  `RType'.IsObj` (Phase A); `Tm'` (Phase B); `constructorSig`,
  `SortedSig.sum` (`GebLean/Ramified/SortedSig.lean`); `toSlice`
  (Phase A); `W`, `W.mk`, `wIndex`, `W.wIndex_mk` (vendored);
  `PolyEndo` (`GebLean/PolyAlg.lean`), `ccrObjMk`
  (`GebLean/Utilities/Families.lean`), `Over.mk` (mathlib — as
  non-recursive signature data only); `FreeAlg'`,
  `FreeAlg'.recurse` (Phase A); `RType'.interp` (Phase A).
- Produces (mirrors of the legacy `HigherOrder.lean` up to
  `RIdent'.interp`'s prerequisites; `interp` itself is Task C.11):
  - `def appSig' : SortedSig RType'` (`Op := RType' × RType'`,
    `arity op := [RType'.arrow op.1 op.2, op.1]`,
    `result op := op.2`).
  - `def stdConstructorInterp' (A)` and `def stdAppInterp' (A)` —
    mirrors over carriers `RType'.interp (FreeAlg' A)`, with the
    object-sort cast through `RType'.interp_isObj` (Task C.12
    provides it if Phase A lacks it — if so, this task declares its
    statement locally as a `have`-free forward reference is NOT
    possible: instead Task C.12 is ordered BEFORE this task's
    implementation step; see the task-order note below).
  - `def RType'.curried (Γ : List RType') (τ : RType') : RType' :=`
    `Γ.foldr RType'.arrow τ` with `@[simp] curried_nil` /
    `curried_cons`; `def curryInterp' (A)` — the `List`-recursive
    mirror (permitted: recursion on `List`, not on a tree type).
  - `theorem rTypeSliceEquiv_curried (Γ' : List RType')`
    `(τ' : RType') : rTypeSliceEquiv (RType'.curried Γ' τ') =`
    `RType.curried (Γ'.map rTypeSliceEquiv) (rTypeSliceEquiv τ')`
    — by `List.foldr` induction with `rTypeSliceEquiv_arrow`
    (moved here from the additive-lemma task: it consumes
    `RType'.curried`, defined in this task).
  - `def holeSig'` / `holeConstSig'` (over
    `Fin n → List RType' × RType'`), `def defnSig' (A) (n)`
    `(holeIdx')` — the four-summand sum mirror.
  - `structure DefnShape' (A) (Γ' : List RType') (τ' : RType')`
    (`numHoles`, `holeIdx'`, `body : Tm' (defnSig' A numHoles`
    `holeIdx') Γ' τ'`); `structure MrecShape'` (`params`,
    `hΓ : Γ' = params ++ [RType'.omega τ']`); `structure FrecShape'`
    (`params`, `hΓ : Γ' = params ++ [RType'.o]`);
    `def IdentShape' (A) (Γ') (τ') : Type` (the triple sum);
    `def IdentDir'` (mirror); `def identTarget'` (mirror);
    `def identEndo' (A) : PolyEndo (List RType' × RType')` (via
    `ccrObjMk` / `Over.mk`, non-recursive data).
  - `def RIdent' (A) (Γ' : List RType') (τ' : RType') : Type :=`
    `{ w : (toSlice (identEndo' A)).W // wIndex w = (Γ', τ') }`
    (the `FreeAlg'` fiber idiom).
  - `def RIdent'.defn (d : DefnShape' A Γ' τ') (children) :`
    `RIdent' A Γ' τ'`, `def RIdent'.mrec (params τ' steps)`,
    `def RIdent'.frec (params τ' clauses)` — `W.mk` at the three
    shapes with children's fiber proofs via `compatible_iff`;
    `@[simp]` val-characterization lemmas `val_defn` / `val_mrec` /
    `val_frec` (the `FreeM.val_pure` naming pattern).

**Task-order note:** `RType'.interp_isObj` is absent from Phase A
(verified at review 1), so the execution order is fixed:
C.12 → C.10 → C.11. The plan lists C.10–C.12 in dependency-narrative
order only.

**Steps:**

- [ ] **Step 1: Write the failing test.** Build, over `natAlgSig`: a
  `frec'`-former identifier with trivial clauses referencing
  `defn'`-formed children (e.g. a constant-zero explicit definition
  with no holes), and assert the `val_*` characterization lemmas and
  the index fiber properties.
- [ ] **Step 2: Run to verify it fails.** Run
  `lake build GebLeanTests.Ramified.Polynomial.Ident`. Expected:
  failure, `RIdent'` not found.
- [ ] **Step 3: Implement** in interface order, one declaration at a
  time (docstring cites Leivant 1999 section 2.3 — the schema, eqs.
  (4)/(5) — and section 2.7; the Swierstra data-types-a-la-carte
  citation as in the legacy module).
- [ ] **Step 4: Run to verify it passes.** Run
  `lake build GebLeanTests.Ramified.Polynomial.Ident`. Expected:
  success.
- [ ] **Step 5: Gate.** Run `bash scripts/pre-commit.sh`.
- [ ] **Step 6: Commit.**

```bash
jj commit -m "feat(ramified): add the primed schema identifiers on the slice W-type"
```

## Task C.11: `RIdent'.interp`

**Files:**

- Modify: `GebLean/Ramified/Polynomial/Ident.lean`
- Modify: `GebLeanTests/Ramified/Polynomial/Ident.lean`

**Interfaces:**

- Consumes: Task C.10; `Tm'.eval` (Task C.4); `FreeAlg'.recurse`,
  `FreeAlg'.recurse_mk` (Phase A); `W.elim` (vendored);
  `get_append_lt` / `get_append_ge` (legacy `SynCat.lean`,
  sort-generic).
- Produces:
  - `def defnModel' (A) (n) (holeIdx') (ih) :`
    `SortedModel (defnSig' A n holeIdx')` — carrier
    `RType'.interp (FreeAlg' A)`; the four-way operation match
    mirroring `defnModel` (holes read `ih`, curried holes
    `curryInterp'` of `ih`).
  - `def childEnv'` / `envHead'` / `envLast'` — primed mirrors of
    the legacy environment helpers (same `cast`-along-`get` shapes,
    at `C : RType' → Type`).
  - `def RIdent'.interpStep (A Γ' τ') (shape) (ih) : (Env at Γ') →`
    `RType'.interp (FreeAlg' A) τ'` — the three-case mirror: `defn'`
    folds `d.body` by `Tm'.eval` against `defnModel'`; `mrec'` /
    `frec'` recurse by `FreeAlg'.recurse` with the monotonic / flat
    step through `childEnv'`, `envHead'`, `envLast'`.
  - `def RIdent'.interp {A Γ' τ'} (f : RIdent' A Γ' τ') :`
    `(∀ i : Fin Γ'.length, RType'.interp (FreeAlg' A) (Γ'.get i)) →`
    `RType'.interp (FreeAlg' A) τ'` — a `W.elim` at the sigma-of-
    interp-function carrier over the index `(Γ', τ')` (the
    `FreeM.elim` idiom of Task C.3 applied at the identifier
    endofunctor: carrier `Σ p : List RType' × RType', (Env at p.1) →
    RType'.interp (FreeAlg' A) p.2`, index map `Sigma.fst`),
    applying `interpStep` at each node; the fiber proof transports
    the final sigma.
  - `theorem RIdent'.interp_defn` / `interp_mrec` / `interp_frec` —
    the computation rules at the three formers (from the `W.elim`
    computation on the `val_*` forms; NOT `@[simp]`).

**Steps:**

- [ ] **Step 1: Write the failing test.** Interpret the Task C.10
  sample identifiers over `natAlgSig`: assert, through
  `interp_defn` / `interp_frec` and `FreeAlg'.recurse_mk`, the
  value of the constant-zero definition and one clause selection of
  the `frec'` sample.
- [ ] **Step 2: Run to verify it fails.** Run
  `lake build GebLeanTests.Ramified.Polynomial.Ident`. Expected:
  failure, `interp` not found.
- [ ] **Step 3: Implement** in interface order, one declaration at a
  time.
- [ ] **Step 4: Run to verify it passes.** Run
  `lake build GebLeanTests.Ramified.Polynomial.Ident`. Expected:
  success.
- [ ] **Step 5: Gate.** Run `bash scripts/pre-commit.sh`.
- [ ] **Step 6: Commit.**

```bash
jj commit -m "feat(ramified): add the primed identifier interpretation"
```

## Task C.12: Phase A additive agreement lemmas

**Files:**

- Modify: `GebLean/Ramified/RType.lean` (additive:
  `RType.interpCongr`)
- Modify: `GebLean/Ramified/Polynomial/FreeAlg.lean`
- Modify: `GebLean/Ramified/Polynomial/RType.lean`
- Modify: `GebLeanTests/Ramified/RType.lean`,
  `GebLeanTests/Ramified/Polynomial/FreeAlg.lean`,
  `GebLeanTests/Ramified/Polynomial/RType.lean`

**Interfaces:**

- Consumes: `FreeAlg'`, `FreeAlg'.mk`, `FreeAlg'.recurse`,
  `recurse_mk`, `freeAlgSliceEquiv`, `freeAlgSliceEquiv_mk`,
  `natFreeAlgEquiv'` (Phase A, `Polynomial/FreeAlg.lean`);
  `FreeAlg'.induction` (Phase A, `Polynomial/RType.lean`); the
  legacy `FreeAlg.recurse` (`GebLean/Ramified/AlgSig.lean`) and
  `natFreeAlgEquiv` (`GebLean/Ramified/Algebras.lean`).
  (`rTypeSliceEquiv_curried` is produced by Task C.10, which
  defines `RType'.curried`; C.12 runs first and does not touch
  it.)
- Produces:
  - `theorem freeAlgSliceEquiv_recurse {A : AlgSig} {P C : Type}`
    `(g) (p : P) (x : FreeAlg' A) :`
    `FreeAlg'.recurse g p x = FreeAlg.recurse g p`
    `(freeAlgSliceEquiv A x)` — hosted in `Polynomial/RType.lean`,
    where `FreeAlg'.induction` is in scope (`FreeAlg.lean` is its
    upstream and cannot use it). Statement shape: the two
    paramorphisms agree when fed the same step function `g` up to
    the equivalence on the subterm argument (the step's subterm
    tuple on the legacy side is the image tuple; the precise
    statement quantifies over a legacy-typed `g` and inserts
    `(freeAlgSliceEquiv A).symm` on the primed side's subterm
    reads, or dually — fix the orientation that makes Task C.14's
    `mrec'`/`frec'` cases direct, and record it); by
    `FreeAlg'.induction` with `recurse_mk` on both sides and
    `freeAlgSliceEquiv_mk`.
  - `theorem natFreeAlgEquiv'_slice :`
    `natFreeAlgEquiv' = (freeAlgSliceEquiv natAlgSig).trans`
    `natFreeAlgEquiv` — in `Polynomial/FreeAlg.lean`, by `rfl`:
    Phase A defines `natFreeAlgEquiv'` as exactly this composite
    (verified at review 1); the lemma names the fact for Task
    C.18's `objToNat` correspondence.
  - `theorem RType'.interp_isObj (C : Type) {t : RType'}`
    `(h : t.IsObj) : RType'.interp C t = C` — mirror of the legacy
    `RType.interp_isObj`, by the shape reading of `IsObj` (absent
    from Phase A, verified at review 1; in
    `Polynomial/RType.lean`).
  - `def RType.interpCongr {C D : Type} (e : C ≃ D) (t : RType) :`
    `RType.interp C t ≃ RType.interp D t` — the congruence of the
    legacy denotation along a base-carrier equivalence (in the
    legacy `GebLean/Ramified/RType.lean`, additive): the base and
    `Omega` cases are `e`, the arrow case is `Equiv.arrowCongr` of
    the recursive equivalences; realized by the same legacy
    recursion device `RType.interp` itself uses (legacy-side
    elimination, permitted as bridge consumption).
  - `def carrierSliceEquiv (A : AlgSig) (t' : RType') :`
    `RType'.interp (FreeAlg' A) t' ≃`
    `RType.interp (FreeAlg A) (rTypeSliceEquiv t')` — the composite
    `Equiv.cast (rTypeSliceEquiv_interp (FreeAlg' A) t')` then
    `RType.interpCongr (freeAlgSliceEquiv A) _` (in
    `Polynomial/RType.lean`); the single named carrier bridge
    consumed by Tasks C.14, C.16, C.18.
  - `theorem carrierSliceEquiv_isObj {A} {t' : RType'}`
    `(h : t'.IsObj) (x) : carrierSliceEquiv A t' x` computes to
    `freeAlgSliceEquiv A` applied to `x` read through the
    object-sort interp equalities (`RType'.interp_isObj`,
    `RType.interp_isObj`, `rTypeSliceEquiv_isObj`) — the statement
    fixes the cast spelling; by shape reading of `IsObj` and
    `Equiv.cast` computation. Consumed by Task C.18's
    `objToNat`-correspondence.

**Steps:**

- [ ] **Step 1: Write the failing tests** for the new lemmas
  (statement-level `example`s on `natAlgSig` samples), in the
  `RType` and `FreeAlg` test mirrors.
- [ ] **Step 2: Run to verify they fail.** Run
  `lake build GebLeanTests.Ramified.Polynomial.FreeAlg`
  (and `…RType`). Expected: failure, names not found.
- [ ] **Step 3: Implement** the new lemmas, one at a time.
- [ ] **Step 4: Run to verify they pass.** Run the two test builds.
  Expected: success.
- [ ] **Step 5: Gate.** Run `bash scripts/pre-commit.sh`.
- [ ] **Step 6: Commit.**

```bash
jj commit -m "feat(ramified): add bridge agreement lemmas for recurrence and interp"
```

## Task C.13: the identifier bridge equivalence

**Files:**

- Create: `GebLean/Ramified/Polynomial/IdentEquiv.lean`
- Create: `GebLeanTests/Ramified/Polynomial/IdentEquiv.lean`
- Modify: `GebLean/Ramified/Polynomial.lean`,
  `GebLeanTests/Ramified/Polynomial.lean` (imports)

**Interfaces:**

- Consumes: Tasks C.2, C.8, C.10; `SlicePFunctor.Iso`,
  `Iso.wEquivFiber`, `Iso.wMap_mk` (Phase B); `polyFixSliceEquiv`
  (Phase A); `RIdent`, `IdentShape`, `identEndo`, `DefnShape`,
  `MrecShape`, `FrecShape`, `defnSig`
  (`GebLean/Ramified/HigherOrder.lean`); `tmSliceEquiv` (Phase B);
  `Equiv.listEquivOfEquiv` (mathlib, forward map `List.map e`);
  `rTypeSliceEquiv_omega`, `rTypeSliceEquiv_o` (Phase A),
  `rTypeSliceEquiv_curried` (Task C.12).
- Produces:
  - `def identCtxEquiv : List RType' × RType' ≃`
    `List RType × RType` — `Equiv.prodCongr`
    `(Equiv.listEquivOfEquiv rTypeSliceEquiv) rTypeSliceEquiv`.
  - `def defnSigEquiv (A) (n) (holeIdx') : SortedSigEquiv`
    `(defnSig' A n holeIdx') (defnSig A n (translated holeIdx))` —
    the summand-wise `SortedSigEquiv` at sort equivalence
    `rTypeSliceEquiv`: constructor summand by
    `Equiv.prodCongr` of the `IsObj` subtype congruence
    (`Equiv.subtypeEquiv rTypeSliceEquiv` at
    `rTypeSliceEquiv_isObj`) and `Equiv.refl A.B`; `appSig'` by
    `Equiv.prodCongr`; hole summands by `Equiv.refl (Fin n)` with
    `arity_comm` / `result_comm` from the translated `holeIdx` and
    `rTypeSliceEquiv_curried`.
  - `def defnShapeEquiv (A Γ' τ') : DefnShape' A Γ' τ' ≃`
    `DefnShape A (Γ'.map rTypeSliceEquiv) (rTypeSliceEquiv τ')` —
    `numHoles` and translated `holeIdx` componentwise; the body
    through `(tmSliceEquiv …).trans`-free composite: first
    `tmSliceEquiv` (primed to legacy terms over `defnSig'`), then
    `(defnSigEquiv …).tmEquiv` (legacy terms across the signature
    equivalence).
  - `def identShapeEquiv (A Γ' τ') : IdentShape' A Γ' τ' ≃`
    `IdentShape A (Γ'.map rTypeSliceEquiv) (rTypeSliceEquiv τ')` —
    sum of `defnShapeEquiv` and the `MrecShape'` / `FrecShape'`
    congruences (context equations transported by
    `List.map_append`, `rTypeSliceEquiv_omega` /
    `rTypeSliceEquiv_o`).
  - `def identEndoIso (A) : SlicePFunctor.Iso`
    `(toSlice (identEndo' A))`
    `(SlicePFunctor.reindex identCtxEquiv.symm (toSlice (identEndo`
    `A)))` — shapes by the sigma congruence over `identShapeEquiv`;
    positions by the `IdentDir` congruences (identity at `defn`
    holes and at `A.B`); `q_comm` / `r_comm` by shape split with
    `identTarget` translated through `identCtxEquiv`.
  - `def identSliceEquiv {A Γ' τ'} : RIdent' A Γ' τ' ≃`
    `RIdent A (Γ'.map rTypeSliceEquiv) (rTypeSliceEquiv τ')` — the
    composite: `(identEndoIso A).wEquivFiber` at `(Γ', τ')`, then
    `reindex.wEquivFiber identCtxEquiv.symm …` re-read (Task C.2's
    fiber form), then `(polyFixSliceEquiv (identEndo A) _).symm`.
  - `theorem identSliceEquiv_defn` / `_mrec` / `_frec` — former
    naturality (via `Iso.wMap_mk`, the `val_*` lemmas, and
    `polyFixSliceEquiv_mk`; NOT `@[simp]`).

**Steps:**

- [ ] **Step 1: Write the failing test.** Translate the Task C.10
  sample identifiers and assert, through the naturality lemmas,
  that the images are the legacy `RIdent.defn` / `RIdent.frec`
  forms of the translated data; assert one round trip via
  `Equiv.symm_apply_apply`.
- [ ] **Step 2: Run to verify it fails.** Run
  `lake build GebLeanTests.Ramified.Polynomial.IdentEquiv`.
  Expected: failure, names not found.
- [ ] **Step 3: Implement** in interface order, one declaration at
  a time.
- [ ] **Step 4: Run to verify it passes.** Run
  `lake build GebLeanTests.Ramified.Polynomial.IdentEquiv`.
  Expected: success.
- [ ] **Step 5: Gate.** Run `bash scripts/pre-commit.sh`.
- [ ] **Step 6: Commit.**

```bash
jj commit -m "feat(ramified): relate the primed identifiers to the legacy identifiers"
```

## Task C.14: identifier interp agreement

**Files:**

- Modify: `GebLean/Ramified/Polynomial/IdentEquiv.lean`
- Modify: `GebLeanTests/Ramified/Polynomial/IdentEquiv.lean`

**Interfaces:**

- Consumes: Tasks C.4, C.9 (`tmMap_eval` at `defnSigEquiv` read as
  a `PresentationEquiv` on the defn-body models — state the body
  agreement as its own lemma below rather than instantiating the
  full structure), C.11, C.12, C.13; `RIdent.interp`,
  `RIdent.interpStep`, `defnModel`, `childEnv`, `envHead`,
  `envLast` (`GebLean/Ramified/HigherOrder.lean`);
  `rTypeSliceEquiv_interp` (Phase A); `W.induction` (vendored).
- Produces:
  - `theorem defnModel_agree` — the defn-body evaluation agreement:
    for matched hole interpretations (`ih'` primed, `ih` legacy,
    related pointwise by `carrierSliceEquiv` at the translated
    `holeIdx`), the `Tm'.eval` of a `DefnShape'` body at
    `defnModel'` maps by `carrierSliceEquiv` to the legacy
    `Tm.eval` of the translated body at `defnModel` — the composite
    of `tmSliceEquiv_eval` (Task C.4) and a `tmMap_eval`-shaped
    lemma at `defnSigEquiv` (Task C.9's proof pattern instantiated
    at the defn-body models with `carrierEquiv :=
    carrierSliceEquiv`; the model-matching hypotheses are exactly
    the hole/`curryInterp'` cases plus `stdConstructorInterp'` /
    `stdAppInterp'` agreement, the constructor case through
    `freeAlgSliceEquiv_mk` and `carrierSliceEquiv_isObj`, the
    application case definitional through `RType.interpCongr`'s
    arrow equation).
  - `theorem curryInterp'_agree` — `curryInterp'` agrees with the
    legacy `curryInterp` under `carrierSliceEquiv` and
    `rTypeSliceEquiv_curried` (by `List` induction on the context;
    consumed by `defnModel_agree`'s curried-hole case and later by
    Task C.16's constant-summand case).
  - `theorem identSliceEquiv_interp {A Γ' τ'}`
    `(f : RIdent' A Γ' τ')`
    `(ρ' : ∀ i : Fin Γ'.length, RType'.interp (FreeAlg' A)`
    `(Γ'.get i)) : (identSliceEquiv f).interp (matched legacy`
    `environment) = carrierSliceEquiv A τ' (f.interp ρ')` — the
    matched legacy environment pushes `ρ'` forward through
    `get_map` and `carrierSliceEquiv`; by
    `W.induction` on `f`'s underlying tree with the three-former
    shape split: `defn'` by `identSliceEquiv_defn`,
    `RIdent'.interp_defn`, the legacy `interp` reduction, and
    `defnModel_agree` with the induction hypotheses; `mrec'` /
    `frec'` by `identSliceEquiv_mrec` / `_frec`, `interp_mrec` /
    `_frec`, `freeAlgSliceEquiv_recurse` (Task C.12), and
    `childEnv'` / `envHead'` / `envLast'`-versus-legacy matching
    (each a `cast`-computation lemma by `Fin` case split, stated
    inline as `have`s or as three small private lemmas). NOT
    `@[simp]`.

**Steps:**

- [ ] **Step 1: Write the failing test.** Assert
  `identSliceEquiv_interp` instances on the Task C.10 samples
  (constant-zero `defn'`, the `frec'` sample) at concrete
  environments, evaluated through the computation rules of both
  sides.
- [ ] **Step 2: Run to verify it fails.** Run
  `lake build GebLeanTests.Ramified.Polynomial.IdentEquiv`.
  Expected: failure, `identSliceEquiv_interp` not found.
- [ ] **Step 3: Implement** `curryInterp'_agree`, then
  `defnModel_agree`, then `identSliceEquiv_interp`, one at a time.
- [ ] **Step 4: Run to verify it passes.** Run
  `lake build GebLeanTests.Ramified.Polynomial.IdentEquiv`.
  Expected: success.
- [ ] **Step 5: Gate.** Run `bash scripts/pre-commit.sh`.
- [ ] **Step 6: Commit.**

```bash
jj commit -m "feat(ramified): prove identifier interp agreement across the bridge"
```

## Task C.15: the primed higher-order presentation

**Files:**

- Create: `GebLean/Ramified/Polynomial/HigherOrder.lean`
- Create: `GebLeanTests/Ramified/Polynomial/HigherOrder.lean`
- Modify: `GebLean/Ramified/Polynomial.lean`,
  `GebLeanTests/Ramified/Polynomial.lean` (imports)

**Interfaces:**

- Consumes: Tasks C.4, C.5, C.10, C.11; `Presentation`
  (`GebLean/Ramified/Interp.lean`); `SortedSig.sum`.
- Produces (mirrors of the legacy `HigherOrder.lean` from
  `appChain` onward):
  - `def appChain' (A) : (Γ : List RType') → (τ : RType') → …` (the
    `List`-recursive mirror) with
    `theorem appChain_curryInterp'` and
    `theorem RIdent'.interp_eq_appChain_curryInterp'`.
  - `def identSig' (A) : SortedSig RType'`
    (`Op := Σ Γ' : List RType', Σ τ' : RType', RIdent' A Γ' τ'`,
    arity `op.1`, result `op.2.1`); `def identConstSig' (A)`
    (nullary, result `RType'.curried op.1 op.2.1`).
  - `def higherOrderModel' (A) : SortedModel ((((constructorSig A`
    `RType'.IsObj).sum appSig').sum (identSig' A)).sum`
    `(identConstSig' A))` — carrier `RType'.interp (FreeAlg' A)`;
    the four-way match reading identifiers by `RIdent'.interp` and
    constants by `curryInterp'`.
  - `def higherOrder' (A) : Presentation` — `S := RType'`, the
    four-summand `sig`, `IsObj := RType'.IsObj`, `alg := A`,
    `std := higherOrderModel' A`.
  - `abbrev RMRecCat' (A) := SynCat' (higherOrder' A)`
    `(interpQuotRel' (higherOrder' A))`.
  - `def identHom' {A Γ' τ'} (f : RIdent' A Γ' τ') :`
    `Hom' (higherOrder' A) (interpQuotRel' (higherOrder' A)) Γ'`
    `[τ']` with `theorem identHom_eval'` (mirror).

**Steps:**

- [ ] **Step 1: Write the failing test.** Assert
  `appChain_curryInterp'` on a two-sort context sample;
  `identHom_eval'` on the Task C.10 constant-zero identifier.
- [ ] **Step 2: Run to verify it fails.** Run
  `lake build GebLeanTests.Ramified.Polynomial.HigherOrder`.
  Expected: failure, names not found.
- [ ] **Step 3: Implement** in interface order (docstring citations
  as the legacy module: Leivant 1999 sections 2.1, 2.3, 2.7;
  Swierstra 2008).
- [ ] **Step 4: Run to verify it passes.** Run
  `lake build GebLeanTests.Ramified.Polynomial.HigherOrder`.
  Expected: success.
- [ ] **Step 5: Gate.** Run `bash scripts/pre-commit.sh`.
- [ ] **Step 6: Commit.**

```bash
jj commit -m "feat(ramified): assemble the primed higher-order presentation"
```

## Task C.16: the composite category equivalence

**Files:**

- Create: `GebLean/Ramified/Polynomial/HigherOrderEquiv.lean`
- Create: `GebLeanTests/Ramified/Polynomial/HigherOrderEquiv.lean`
- Modify: `GebLean/Ramified/Polynomial.lean`,
  `GebLeanTests/Ramified/Polynomial.lean` (imports)

**Interfaces:**

- Consumes: Tasks C.7, C.8, C.9, C.12, C.13, C.14, C.15;
  `higherOrder`,
  `higherOrderModel`, `RMRecCat`
  (`GebLean/Ramified/HigherOrder.lean`); `Equiv.sigmaCongr` /
  `Equiv.prodCongr` / `Equiv.sumCongr` / `Equiv.subtypeEquiv`
  (mathlib).
- Produces:
  - `def higherOrderSigEquiv (A) : SortedSigEquiv`
    `(higherOrder' A).sig (higherOrder A).sig` — sort equivalence
    `rTypeSliceEquiv`; op equivalence summand-wise
    (`Equiv.sumCongr` stack): constructor summand
    `Equiv.prodCongr (Equiv.subtypeEquiv rTypeSliceEquiv (by`
    `simpa using rTypeSliceEquiv_isObj)) (Equiv.refl A.B)`;
    application `Equiv.prodCongr rTypeSliceEquiv rTypeSliceEquiv`;
    identifier summands
    `Equiv.sigmaCongr (Equiv.listEquivOfEquiv rTypeSliceEquiv)`
    `(… Equiv.sigmaCongr rTypeSliceEquiv (… identSliceEquiv))`;
    `arity_comm` by summand split (`List.map` of `replicate`,
    `rTypeSliceEquiv_arrow` at application, definitional at
    identifier arities via the sigma components); `result_comm` by
    summand split (`rTypeSliceEquiv_curried` at the constant
    summand).
  - `def higherOrderPresEquiv (A) : PresentationEquiv`
    `(higherOrder' A) (higherOrder A)` — `sigEquiv :=`
    `higherOrderSigEquiv A`; `carrierEquiv := carrierSliceEquiv A`
    (Task C.12; this is why `PresentationEquiv` carries an
    equivalence rather than an equality — the base carriers
    `FreeAlg' A` and `FreeAlg A` are related only by
    `freeAlgSliceEquiv`); `interpOp_comm` by the four-way summand
    split: constructors by `freeAlgSliceEquiv_mk` (Phase A) with
    `carrierSliceEquiv_isObj` at the object-sort readings,
    application definitionally through `RType.interpCongr`'s arrow
    equation, saturated identifiers by `identSliceEquiv_interp`
    (Task C.14), identifier constants by `curryInterp'_agree`
    (Task C.14).
  - `def rmRecCatSliceEquiv (A) : RMRecCat' A ≌ RMRecCat A` —
    `(synCatSliceEquiv (higherOrder' A)).trans`
    `((higherOrderPresEquiv A).synCatEquiv)`.

**Steps:**

- [ ] **Step 1: Write the failing test.** Assert the object map of
  `rmRecCatSliceEquiv natAlgSig` on a sample primed context, and
  the hom map on `identHom'` of the constant-zero identifier
  (through the naturality lemmas and `Hom.eval` at a sample
  environment).
- [ ] **Step 2: Run to verify it fails.** Run
  `lake build GebLeanTests.Ramified.Polynomial.HigherOrderEquiv`.
  Expected: failure, names not found.
- [ ] **Step 3: Implement** `higherOrderSigEquiv`, then
  `higherOrderPresEquiv`, then the composite, one at a time
  (`RType.interpCongr` and `carrierSliceEquiv` come from Task
  C.12).
- [ ] **Step 4: Run to verify it passes.** Run
  `lake build GebLeanTests.Ramified.Polynomial.HigherOrderEquiv`.
  Expected: success.
- [ ] **Step 5: Gate.** Run `bash scripts/pre-commit.sh`.
- [ ] **Step 6: Commit.**

```bash
jj commit -m "feat(ramified): establish the primed-to-legacy category equivalence"
```

## Task C.17: first-order sub-theory replacement

**Files:**

- Delete: `GebLean/Ramified/FirstOrder.lean`,
  `GebLeanTests/Ramified/FirstOrder.lean`
- Create: `GebLean/Ramified/Polynomial/FirstOrder.lean`
- Create: `GebLeanTests/Ramified/Polynomial/FirstOrder.lean`
- Modify: `GebLean/Ramified.lean` (drop the legacy import),
  `GebLeanTests/Ramified.lean` (drop the legacy test import),
  `GebLean/Ramified/Polynomial.lean`,
  `GebLeanTests/Ramified/Polynomial.lean` (add the new imports)

**Interfaces:**

- Consumes: Tasks C.4, C.5, C.10, C.11, C.15; `W.RecProp` and its
  computation lemma (vendored stack; the Phase A `IsTower`
  pattern in `GebLean/Ramified/Polynomial/RType.lean`);
  `RType'.IsTower` (Phase A).
- Produces (legacy names freed by the deletion; namespace-membered
  where the subject is a primed type):
  - `def Tm'.TowerSorts {sig : SortedSig RType'} {Γ} {s}`
    `(t : Tm' sig Γ s) : Prop` — via `W.RecProp` over the
    underlying tree with the `Sum` shape split (leaf: the
    variable's sort is a tower sort; node: the result sort is a
    tower sort and all children satisfy the predicate), with
    `@[simp]` unfolding lemmas `towerSorts_var` / `towerSorts_op`
    (mirroring the legacy statements at `Tm'.var` / `Tm'.op`).
  - `def RIdent'.ShapeFO : IdentShape' A Γ' τ' → Prop` (defn body
    `TowerSorts`; recurrences `True`).
  - `def RIdent'.FirstOrder (f : RIdent' A Γ' τ') : Prop` — via
    `W.RecProp` (context and result tower sorts, `ShapeFO`,
    children first-order), with `@[simp]` unfolding at the three
    formers.
  - `def foIdentSig (A)`, `def foIdentConstSig (A)` (subtype
    `{ f : RIdent' A Γ' τ' // f.FirstOrder }`),
    `def firstOrderSig (A)`, `def firstOrderModel (A)`,
    `def firstOrderPresentation (A) : Presentation` — primed
    mirrors of the deleted module's definitions.
  - `def foOp (A)` (the operation translation into
    `(higherOrder' A).sig`), `def foTm (A)` (by `FreeM.elim`),
    `theorem foOp_eval`, `theorem foTm_eval` (via `Tm'.eval`'s
    computation rules), `def foHomMap`, `def foInclusion (A) :`
    `SynCat' (firstOrderPresentation A) (interpQuotRel' …) ⥤`
    `RMRecCat' A` — mirrors of the deleted module's proofs with
    the primed vocabulary (`Quotient.sound` from `foTm_eval` and
    `Tm'.eval_subst`).

**Steps:**

- [ ] **Step 1: Write the failing test.** Port the deleted test
  module's assertions to the primed vocabulary: `TowerSorts` on
  tower and arrow-sorted samples, `FirstOrder` on a first-order
  and a non-first-order identifier, `foTm_eval` on a sample body,
  and a `foInclusion.map` instance.
- [ ] **Step 2: Run to verify it fails.** Run
  `lake build GebLeanTests.Ramified.Polynomial.FirstOrder`.
  Expected: failure, names not found.
- [ ] **Step 3: Delete** the two legacy files and their aggregator
  imports; run `lake build GebLean` to confirm nothing else broke
  (the brainstorming measurement found zero consumers).
- [ ] **Step 4: Implement** the replacement in interface order
  (docstring cites Leivant 1999 section 2.4(3) and 2.4(2), the
  DLMZ tier-vector convention, and — for the deferred poly-time
  context — Leivant 1995, DOI `10.1007/978-1-4612-2566-9_11`).
- [ ] **Step 5: Run to verify it passes.** Run
  `lake build GebLeanTests.Ramified.Polynomial.FirstOrder` and
  `lake test`. Expected: success.
- [ ] **Step 6: Gate.** Run `bash scripts/pre-commit.sh`.
- [ ] **Step 7: Commit.**

```bash
jj commit -m "refactor(ramified): move the first-order sub-theory to the primed stack"
```

## Task C.18: collapse packaging and the restriction equivalence

**Files:**

- Create: `GebLean/Ramified/Polynomial/Collapse.lean`
- Create: `GebLeanTests/Ramified/Polynomial/Collapse.lean`
- Modify: `GebLean/Ramified/Polynomial.lean`,
  `GebLeanTests/Ramified/Polynomial.lean` (imports)

**Interfaces:**

- Consumes: Tasks C.15, C.16; the legacy `isObjCtx`, `SynCatFO`,
  `collapseDenotation` (`GebLean/Ramified/Soundness/Collapse.lean`),
  `ramifiedDenotation` (`Definability/Top.lean`), `objToNat` /
  `objFromNat` (`GebLean/Ramified/Examples.lean`), `arityCongr`
  (`Characterization.lean`);
  `natFreeAlgEquiv'` and Task C.12's agreement;
  `RType'.interp_isObj` (Task C.12); `rTypeSliceEquiv_isObj`,
  `rTypeSliceEquiv_o` (Phase A); `ObjectProperty.FullSubcategory`
  (mathlib).
- Produces:
  - `def isObjCtx' : ObjectProperty (RMRecCat' natAlgSig)`;
    `abbrev SynCatFO' := isObjCtx'.FullSubcategory`;
    `def ObjCtx' (n : ℕ) : Type := Fin n → { s : RType' //`
    `s.IsObj }`; `def ObjCtx'.toCtx`, `@[simp] toCtx_length`,
    `toCtx_get`, `toCtx_get_isObj`; `def oObj'`
    (`⟨RType'.o, proof⟩`), `def oCtx' (m) : ObjCtx' m`;
    `def SynCatFO'.toObjCtx'`, `def objLen'`,
    `theorem SynCatFO'.toObjCtx'_toCtx`;
    `def ObjCtx'.toSynCatFO'`, `@[simp] objLen'_toSynCatFO'` —
    mirrors of the legacy packaging.
  - `def objToNat' {s : RType'} (hs : s.IsObj) :`
    `RType'.interp (FreeAlg' natAlgSig) s → ℕ` and
    `def objFromNat'` — through `RType'.interp_isObj` and
    `natFreeAlgEquiv'`; round-trip lemmas mirroring
    `objFromNat_objToNat` / `objToNat_objFromNat`.
  - `def ramifiedEnv'`, `def ramifiedDenotation'`,
    `def collapseHom'`, `def collapseDenotation'`,
    `theorem ramifiedDenotation'_apply`, `_id`, `_comp`,
    `theorem collapseDenotation'_id` / `_comp` — mirrors (the
    `cast_hom_id` / `cast_hom_comp` helpers of the legacy module
    are `Presentation`-generic and reused as-is if their
    statements apply to `Hom'`; where they do not — they are
    stated over legacy `Hom` — add primed mirrors
    `cast_hom'_id` / `cast_hom'_comp`).
  - `def synCatFOSliceEquiv : SynCatFO' ≌ SynCatFO` — the
    restriction of `rmRecCatSliceEquiv natAlgSig` along the object
    properties: functor and inverse by
    `ObjectProperty.lift` of the composed
    projections (property transfer by `rTypeSliceEquiv_isObj`
    through the `List.map` object action, and its converse for
    the inverse), unit/counit induced from the parent equivalence
    (assembled manually if no mathlib restriction lemma applies;
    the executor searches mathlib for a
    full-subcategory-equivalence lift first and records the
    outcome).
  - `theorem collapseDenotation_sliceEquiv {Γ' Δ' : SynCatFO'}`
    `(g' : Γ' ⟶ Δ') : collapseDenotation`
    `(synCatFOSliceEquiv.functor.map g') = arityCongr h₁ h₂`
    `(collapseDenotation' g')` — with `h₁ : objLen' Γ' = objLen`
    `(synCatFOSliceEquiv.functor.obj Γ')` and `h₂` likewise (by
    `List.length_map`); proof by unfolding both denotations to
    evaluations (`ramifiedDenotation_apply` both sides), the
    functor's hom action (componentwise translation), the eval
    agreements (`tmSliceEquiv_eval`, `tmMap_eval` through
    `higherOrderPresEquiv`), and the `objToNat`-versus-`objToNat'`
    correspondence (`carrierSliceEquiv_isObj` composed with Task
    C.12's `natFreeAlgEquiv'_slice`).

**Steps:**

- [ ] **Step 1: Write the failing test.** Assert `objToNat'` /
  `objFromNat'` round trips at sample values;
  `collapseDenotation'_comp` on sample homs; one
  `collapseDenotation_sliceEquiv` instance on a variable-tuple hom
  between `oCtx'`-style objects.
- [ ] **Step 2: Run to verify it fails.** Run
  `lake build GebLeanTests.Ramified.Polynomial.Collapse`.
  Expected: failure, names not found.
- [ ] **Step 3: Implement** in interface order (packaging, then the
  restriction, then the agreement), one declaration at a time.
- [ ] **Step 4: Run to verify it passes.** Run
  `lake build GebLeanTests.Ramified.Polynomial.Collapse`.
  Expected: success.
- [ ] **Step 5: Gate.** Run `bash scripts/pre-commit.sh`.
- [ ] **Step 6: Commit.**

```bash
jj commit -m "feat(ramified): add primed collapse packaging and denotation agreement"
```

## Task C.19: endpoints and documentation

**Files:**

- Create: `GebLean/Ramified/Polynomial/Characterization.lean`
- Create: `GebLeanTests/Ramified/Polynomial/Characterization.lean`
- Modify: `GebLean/Ramified/Polynomial.lean`,
  `GebLeanTests/Ramified/Polynomial.lean` (imports)
- Modify: `docs/areas/polynomial-functors.md`,
  `docs/areas/ramified-recurrence.md` (area inventories: the Phase
  C modules and the FirstOrder replacement)

**Interfaces:**

- Consumes: Task C.18; the legacy `ramified_definability`,
  `ramified_definability_kSim`, `arityCongr`, `arityCongr_apply`,
  `ObjCtx.toSynCatFO`, `synCatFOHom`
  (`GebLean/Ramified/Characterization.lean`); `collapseFunctor`
  (`GebLean/Ramified/Soundness/Collapse.lean`); `erToKFunctor`
  (`GebLean/LawvereERKSim/ErToKFunctor.lean`); `kToERFunctor`,
  `kToERFunctor_map_interp` (`GebLean/LawvereKSimER.lean`);
  `LawvereERCat` (`GebLean/LawvereERQuot.lean`); `LawvereKSimDCat`
  (`GebLean/LawvereKSimQuot.lean`); `erKSimEquiv`
  (`GebLean/LawvereERKSim/Equivalence.lean`); `eqToHom`, `Equivalence`
  laws (mathlib).
- Produces:
  - `def synCatFOHom'` — the primed mirror of `synCatFOHom`.
  - `def ObjCtx.toObjCtx' {n} (Γ : ObjCtx n) : ObjCtx' n` — the
    objectwise preimage (`fun i => ⟨rTypeSliceEquiv.symm (Γ i).val,
    (transport of (Γ i).2 by rTypeSliceEquiv_isObj and`
    `apply_symm_apply)⟩`), with
    `theorem toObjCtx'_map : (Γ.toObjCtx'.toCtx).map rTypeSliceEquiv`
    `= Γ.toCtx` (by `List.map_ofFn` and `apply_symm_apply`) and
    `theorem oCtx_toObjCtx' : (oCtx m).toObjCtx' = oCtx' m`-shaped
    correspondence (via `rTypeSliceEquiv_o` read backward; state
    at the `toSynCatFO'` objects where the endpoint needs it).
  - `theorem collapseDenotation'_eqToHom` — conjugation of
    `collapseDenotation'` by `eqToHom`s is `arityCongr` of the
    denotation (the primed mirror of the legacy
    `ramifiedDenotation_cast` pattern; by `subst` on the object
    equalities).
  - `theorem arityCongr_trans` — `arityCongr h₁ h₂ ∘`-free
    composition identity: `arityCongr h₁' h₂' (arityCongr h₁ h₂ F)`
    `= arityCongr (h₁.trans h₁') (h₂.trans h₂') F` (by `subst`;
    consumed by the endpoint proofs to collapse the stacked
    congruences).
  - `def collapseFunctor' : SynCatFO' ⥤ LawvereERCat :=`
    `synCatFOSliceEquiv.functor ⋙ collapseFunctor` with
    `instance : collapseFunctor'.Faithful` (composite; the
    equivalence functor's faithfulness instance is supplied by
    mathlib's `Equivalence.faithful_functor` or the local
    `inferInstanceAs` route the legacy `collapseKFunctor` uses);
    `def collapseKFunctor' := collapseFunctor' ⋙ erToKFunctor`
    with its `Faithful` instance.
  - `theorem ramified_definability' {n m : LawvereERCat}`
    `(f : n ⟶ m) : ∃ (Γ' : ObjCtx' n) (g' : Γ'.toSynCatFO' ⟶`
    `(oCtx' m).toSynCatFO'), collapseDenotation' g' = arityCongr`
    `Γ'.objLen'_toSynCatFO'.symm ((oCtx' m).objLen'_toSynCatFO').symm`
    `f.interp` — proof route: obtain the legacy witnesses
    `⟨Γ, g, hg⟩ := ramified_definability f`; take
    `Γ' := Γ.toObjCtx'`; set `g'` as
    `eqToHom … ≫ synCatFOSliceEquiv.inverse.map g ≫ eqToHom …`
    (object identifications from `toObjCtx'_map` and the `oCtx'`
    correspondence); conclude by
    `collapseDenotation_sliceEquiv` read backward through the
    equivalence's counit (`functor.map (inverse.map g) ≅ g`
    conjugated — the hom-level equality after `eqToHom` absorption,
    by `Equivalence.counitIso` naturality and
    `collapseDenotation'_eqToHom` / the legacy
    denotation-respects-`eqToHom` mirror), then `hg` and
    `arityCongr_trans` to collapse the congruence stack.
  - `theorem ramified_definability_kSim' {n m : LawvereKSimDCat 2}`
    `(f : n ⟶ m)` — the same statement shape at `f.hom.interp`;
    from `ramified_definability'` at `kToERFunctor.map f` and
    `kToERFunctor_map_interp` (mirroring the legacy derivation).

**Steps:**

- [ ] **Step 1: Write the failing test.** Instantiate
  `ramified_definability'` at a concrete `LawvereERCat` morphism
  (mirror the legacy `Characterization` test's sample) and destruct
  the existential; assert `collapseFunctor'.Faithful` resolves by
  `inferInstance`.
- [ ] **Step 2: Run to verify it fails.** Run
  `lake build GebLeanTests.Ramified.Polynomial.Characterization`.
  Expected: failure, names not found.
- [ ] **Step 3: Implement** in interface order (helpers, functors,
  endpoints), one declaration at a time (docstring cites Leivant
  1999 Theorem 14, section 6.1; Tourlakis 2018 Corollary 0.1.0.44
  as the legacy module does).
- [ ] **Step 4: Update the two area documents**; run
  `doctoc --update-only .` and `markdownlint-cli2` on the touched
  files.
- [ ] **Step 5: Run to verify it passes.** Run
  `lake build GebLeanTests.Ramified.Polynomial.Characterization`
  and `lake test`. Expected: success.
- [ ] **Step 6: Gate.** Run `bash scripts/pre-commit.sh`.
- [ ] **Step 7: Commit.**

```bash
jj commit -m "feat(ramified): transfer the characterization to the primed stack"
```

## Task C.20: whole-branch verification

- [ ] **Step 1:** Run `bash scripts/pre-push.sh`. Expected: every
  stage passes (Lean triad, markdownlint, doctoc, axiom-linter
  test).
- [ ] **Step 2:** Whole-branch review per
  superpowers:requesting-code-review against the design document
  (`docs/superpowers/specs/2026-07-20-ramified-poly-er-design.md`);
  address findings; re-run the gate after any change.
- [ ] **Step 3:** Hand off to the user for the push / PR decision
  (no `jj git push` without user line-by-line review).
