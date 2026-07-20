# Phase B sub-plan: native slice free monad and `Tm'`

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Global constraints](#global-constraints)
- [Task B.1: validation spike (iso-induced W-map and native bind)](#task-b1-validation-spike-iso-induced-w-map-and-native-bind)
- [Task B.2: `SlicePFunctor` isomorphisms and the induced W-equivalence](#task-b2-slicepfunctor-isomorphisms-and-the-induced-w-equivalence)
- [Task B.3: the `translate` augmentation](#task-b3-the-translate-augmentation)
- [Task B.4: `FreeM` carrier and constructors](#task-b4-freem-carrier-and-constructors)
- [Task B.5: `FreeM.bind` and its computation rules](#task-b5-freembind-and-its-computation-rules)
- [Task B.6: free-monad laws and transport lemmas](#task-b6-free-monad-laws-and-transport-lemmas)
- [Task B.7: the augmentation isomorphism and `polyFreeMSliceEquiv`](#task-b7-the-augmentation-isomorphism-and-polyfreemsliceequiv)
- [Task B.8: bridge naturality (`pure`, `node`, `bind`)](#task-b8-bridge-naturality-pure-node-bind)
- [Task B.9: the `Tm'` term layer with clone laws](#task-b9-the-tm-term-layer-with-clone-laws)
- [Task B.10: `tmSliceEquiv`, compatibility, and documentation](#task-b10-tmsliceequiv-compatibility-and-documentation)
- [Task B.11: whole-branch verification](#task-b11-whole-branch-verification)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> superpowers:subagent-driven-development (recommended) or
> superpowers:executing-plans to implement this plan task-by-task.
> Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Build the free monad natively on the vendored slice W-type
(`translate`, `FreeM`, monad laws), bridge it to the legacy
`PolyFreeM`, and rebuild the sorted term layer as `Tm'` with clone
laws and compatibility across the bridge.

**Architecture:** Per the approved design
([../specs/2026-07-20-ramified-poly-freemonad-design.md](../specs/2026-07-20-ramified-poly-freemonad-design.md)):
a legacy-free `GebLean/SliceW/` layer (isomorphisms with induced
W-equivalence; the `translate` augmentation; the `FreeM` free monad
with laws by `W.induction`), a bridge module instantiating a generic
iso-to-W-equivalence at the concrete augmentation isomorphism, and a
term module instantiating `FreeM` at `(Γ.get, toSlice sig.polyEndo)`.

**Tech Stack:** Lean 4 + mathlib; vendored
`Geb.Mathlib.Data.PFunctor.Slice.{Basic,W}`; `lake build` / `lake
test`; `jj` commits.

## Global constraints

- No `noncomputable`; `Classical.choice` in proofs only; the axiom
  gate (`lake build GebLeanAxiomChecks`) accepts only `propext` /
  `Quot.sound` / `Classical.choice`.
- Recursor-only elimination of tree types: `SlicePFunctor.W.elim` /
  `W.induction` / `W.RecProp` on the vendored side; `PolyFix.ind` only
  in the bridge. Forbidden on tree types: `induction` / `cases`
  tactics, structural `match` with self-calls, `termination_by`,
  well-founded recursion, `WType.rec` in computational content. A
  non-recursive `match` on a finite shape (e.g. a `Sum` split) is
  permitted.
- `GebLean/SliceW/*` imports the vendored stack only — no
  `GebLean.PolyAlg`, no `GebLean.Ramified.*` (upstream-promotable).
- File headers: plain `import ...` (no `module` keyword), no
  copyright header, mandatory `/-! -/` module docstring (`# Title`,
  summary, `## Main definitions`, `## Main statements`,
  `## References`, `## Tags`); `/-- -/` on every `def`/`theorem`; no
  novelty claims in `.lean` text (citations only).
- `@[simp]` on constructor-compatibility and field-characterization
  lemmas only; operation/naturality compatibility lemmas are NOT
  `@[simp]` (Phase A `simpNF` finding).
- Tests route numeric/semantic assertions through proven lemmas, not
  kernel reduction of composite W-trees.
- Universe polymorphism as far as it compiles: `SliceW` modules follow
  the vendored `{uA, uB, uI}` scheme; the bridge and term modules may
  fix `{u, u, u, u}` as Phase A does.
- Build with `lake build <Module>` / `lake test` only; never
  `lake env lean`, never `lake clean`. Pre-commit gate for every task:
  `bash scripts/pre-commit.sh`.
- Commits with `jj commit -m "<type>(<scope>): <imperative lowercase
  subject>"` (no trailing period, subject ≤ 72 characters). No
  `jj git push` without user line-by-line review.
- References for transcriptions: N. Gambino, J. Kock, "Polynomial
  functors and polynomial monads", Math. Proc. Camb. Phil. Soc. 154
  (2013), DOI `10.1017/S0305004112000394` (free monad as the initial
  algebra of the translation); M. Abbott, T. Altenkirch, N. Ghani,
  "Containers: constructing strictly positive types", TCS 342 (2005),
  DOI `10.1016/j.tcs.2005.06.002` (container isomorphisms);
  D. Leivant, "Ramified recurrence and computational complexity III",
  APAL 96 (1999), DOI `10.1016/S0168-0072(98)00040-2`, section 2.1
  (term layer).

---

## Task B.1: validation spike (iso-induced W-map and native bind)

A short spike (scratch file, deleted before any commit) validating
the two constructions the design marks hardest, sorry-free, before
real tasks depend on them.

- [ ] **Step 1:** In a scratch module importing
  `Geb.Mathlib.Data.PFunctor.Slice.W`, define a toy pair of isomorphic
  `SlicePFunctor PUnit PUnit`s (e.g. shapes `Bool` versus
  `Unit ⊕ Unit`, positions `Fin 2` at one shape) and build the induced
  W-map by `SlicePFunctor.W.elim` into the target `(W, wIndex)`
  algebra, confirming — sorry-free — the `Compatible` re-indexing
  across the position equivalence and the `hg` side condition
  discharge.
- [ ] **Step 2:** Define a toy `translate`-style augmented functor
  (leaf shapes `Bool` over `PUnit`, node shapes from the toy functor)
  and build `bind` as a single `W.elim` with a `Sum` shape split,
  confirming — sorry-free — the leaf case's `hg` discharge from the
  substituted tree's fiber property, and the node case's `Compatible`
  transfer (the target functor has identical `B`/`r` at `Sum.inr`).
- [ ] **Step 3:** Record working term shapes (motives, `hg` proofs,
  transport idioms) as notes in the Task B.2 and B.5 implementation
  steps if they differ from what is written there; delete the scratch
  module.

## Task B.2: `SlicePFunctor` isomorphisms and the induced W-equivalence

**Files:**

- Create: `GebLean/SliceW/Iso.lean`
- Create: `GebLeanTests/SliceW/Iso.lean`
- Create: `GebLean/SliceW.lean` (directory index; `import` this
  module)
- Modify: `GebLean.lean` (add `import GebLean.SliceW` in alphabetical
  position)
- Modify: `GebLeanTests.lean` (add
  `import GebLeanTests.SliceW.Iso`)

**Interfaces:**

- Consumes: `SlicePFunctor` fields `A`/`B`/`q`/`r`,
  `toSliceDomPFunctor`, `obj`, and the `SliceDomPFunctor`
  declarations `Compatible`, `compatible_iff`, `rCurried` (reached by
  dot notation through `toSliceDomPFunctor`)
  (`Geb.Mathlib.Data.PFunctor.Slice.Basic`); `W`, `wIndex`, `W.mk`,
  `W.elim`, `W.elim_mk`, `W.comp_elim`, `W.wIndex_mk`, `W.induction`
  (`Geb.Mathlib.Data.PFunctor.Slice.W`); `Equiv` (mathlib).
- Produces:
  - `structure SlicePFunctor.Iso (F G : SlicePFunctor I I)` with
    fields `shapeEquiv : F.A ≃ G.A`,
    `posEquiv : ∀ a, F.B a ≃ G.B (shapeEquiv a)`,
    `q_comm : ∀ a, G.q (shapeEquiv a) = F.q a`,
    `r_comm : ∀ a b, G.r ⟨shapeEquiv a, posEquiv a b⟩ = F.r ⟨a, b⟩`.
  - `def SlicePFunctor.Iso.symm : Iso F G → Iso G F` — the shape
    equivalence reversed; the position field is NOT a bare reversal:
    at `a' : G.A` it must land in `F.B (shapeEquiv.symm a')`, while
    the reversed forward field has domain
    `G.B (shapeEquiv (shapeEquiv.symm a'))`, so it is the reversal
    composed with the transport (`Equiv.cast` of
    `congrArg G.B (shapeEquiv.apply_symm_apply a')`, or an equivalent
    `▸` re-typing); the same transport threads through `symm`'s
    `q_comm`/`r_comm` proofs (rewriting along the forward fields) and
    later through the round trips.
  - `def SlicePFunctor.Iso.wMap (e : Iso F G) : F.W → G.W` — a single
    `W.elim` into the algebra `(G.W, G.wIndex)`: at a node
    `⟨⟨a, c⟩, hc⟩` build
    `W.mk ⟨⟨e.shapeEquiv a, fun b' => c ((e.posEquiv a).symm b')⟩, _⟩`,
    with the compatibility from `hc` pointwise (`compatible_iff`) and
    `r_comm` at `(e.posEquiv a).symm b'` (rewriting through
    `(e.posEquiv a).apply_symm_apply`); `hg` by `funext`, `wIndex_mk`,
    and `q_comm`.
  - `theorem SlicePFunctor.Iso.wIndex_wMap (e : Iso F G) (z : F.W) :`
    `G.wIndex (e.wMap z) = F.wIndex z` — the pointwise application of
    `W.comp_elim`, whose conclusion is exactly
    `G.wIndex ∘ e.wMap = F.wIndex` (`q_comm` is consumed inside `hg`,
    not here).
  - `theorem SlicePFunctor.Iso.wMap_mk` (`@[simp]`) — constructor
    naturality: `e.wMap (W.mk ⟨⟨a, c⟩, hc⟩)` equals the `W.mk` node at
    `e.shapeEquiv a` with children `fun b' => e.wMap (c ((e.posEquiv
    a).symm b'))`; from `W.elim_mk`.
  - `theorem SlicePFunctor.Iso.symm_wMap_wMap (e : Iso F G) (z : F.W) :`
    `e.symm.wMap (e.wMap z) = z` and
    `theorem SlicePFunctor.Iso.wMap_symm_wMap (e : Iso F G) (z : G.W) :`
    `e.wMap (e.symm.wMap z) = z` — both by `W.induction`, using
    `wMap_mk` and the `Equiv` round-trip lemmas
    (`Equiv.symm_apply_apply`, `Equiv.apply_symm_apply`); expect
    `Subtype.ext`/`Sigma.ext`-with-`heq_of_eq` closing shapes as in
    Phase A's `toSliceW_ofSliceW`.
  - `def SlicePFunctor.Iso.wEquiv (e : Iso F G) : F.W ≃ G.W` —
    packaging `wMap`/`symm.wMap` with the two round trips.
  - `def SlicePFunctor.Iso.wEquivFiber (e : Iso F G) (i : I) :`
    `{ w : F.W // F.wIndex w = i } ≃ { w' : G.W // G.wIndex w' = i }`
    — `wEquiv` restricted along `wIndex_wMap` (both directions use
    `wIndex_wMap` of `e` and `e.symm`).

**Steps:**

- [ ] **Step 1: Write the failing test.** In
  `GebLeanTests/SliceW/Iso.lean`, define the spike's toy isomorphic
  pair and assert: `wIndex_wMap` on a sample tree built by `W.mk`, and
  the round trip `e.wEquiv.symm (e.wEquiv t) = t` via
  `Equiv.symm_apply_apply`.
- [ ] **Step 2: Run to verify it fails.** Run
  `lake build GebLeanTests.SliceW.Iso`. Expected: failure,
  `SlicePFunctor.Iso` not found.
- [ ] **Step 3: Implement.** Write the module docstring (references:
  Abbott–Altenkirch–Ghani 2005 for container isomorphisms;
  Gambino–Kock 2013 for the W-type as initial algebra). Define the
  structure and declarations in the interface order above (one at a
  time, building between declarations). Create `GebLean/SliceW.lean`
  with a module docstring naming the directory's purpose, and wire the
  aggregator imports.
- [ ] **Step 4: Run to verify it passes.** Run
  `lake build GebLeanTests.SliceW.Iso`. Expected: success.
- [ ] **Step 5: Gate.** Run `bash scripts/pre-commit.sh`. Expected:
  all three stages pass.
- [ ] **Step 6: Commit.**

```bash
jj commit -m "feat(slicew): add slice-functor isomorphisms with W-type transport"
```

## Task B.3: the `translate` augmentation

**Files:**

- Create: `GebLean/SliceW/Translate.lean`
- Create: `GebLeanTests/SliceW/Translate.lean`
- Modify: `GebLean/SliceW.lean` (`import` this module)
- Modify: `GebLeanTests.lean` (add
  `import GebLeanTests.SliceW.Translate`)

**Interfaces:**

- Consumes: `SlicePFunctor` (`Geb.Mathlib.Data.PFunctor.Slice.Basic`);
  `PEmpty`.
- Produces:
  - `def SlicePFunctor.translate (v : Y → I) (F : SlicePFunctor I I) :`
    `SlicePFunctor I I` with underlying `PFunctor`
    `⟨Y ⊕ F.A, fun a => match a with | .inl _ => PEmpty | .inr a => F.B a⟩`,
    `q := Sum.elim v F.q`,
    `r := fun x => match x with`
    `| ⟨.inl _, e⟩ => e.elim | ⟨.inr a, b⟩ => F.r ⟨a, b⟩`.
    (The `match`es are non-recursive shape splits, permitted. Let the
    elaborator place `PEmpty`'s universe; annotate only if unification
    fails.)
  - `@[simp]` characterization lemmas `translate_A`,
    `translate_B_inl` (`= PEmpty`), `translate_B_inr` (`= F.B a`),
    `translate_q_inl` (`= v y`), `translate_q_inr` (`= F.q a`),
    `translate_r_inr` (`= F.r ⟨a, b⟩`), each by `rfl`. No
    `translate_r_inl` (the position type is empty).

**Steps:**

- [ ] **Step 1: Write the failing test.** Assert, for a toy
  `v : Bool → PUnit` and the Task B.2 toy functor, that
  `(translate v F).q (.inl true) = v true` and
  `(translate v F).q (.inr a) = F.q a` by `simp`/`rfl` through the
  characterization lemmas.
- [ ] **Step 2: Run to verify it fails.** Run
  `lake build GebLeanTests.SliceW.Translate`. Expected: failure,
  `translate` not found.
- [ ] **Step 3: Implement** the definition and the six `@[simp]`
  lemmas, with the module docstring citing Gambino–Kock 2013 (the
  translation `Y + F(−)`).
- [ ] **Step 4: Run to verify it passes.** Run
  `lake build GebLeanTests.SliceW.Translate`. Expected: success.
- [ ] **Step 5: Gate.** Run `bash scripts/pre-commit.sh`.
- [ ] **Step 6: Commit.**

```bash
jj commit -m "feat(slicew): add the translate augmentation of a slice endofunctor"
```

## Task B.4: `FreeM` carrier and constructors

**Files:**

- Create: `GebLean/SliceW/FreeM.lean`
- Create: `GebLeanTests/SliceW/FreeM.lean`
- Modify: `GebLean/SliceW.lean` (`import` this module)
- Modify: `GebLeanTests.lean` (add `import GebLeanTests.SliceW.FreeM`)

**Interfaces:**

- Consumes: `translate` and its `@[simp]` lemmas (Task B.3); `W`,
  `wIndex`, `W.mk`, `W.wIndex_mk` (vendored stack);
  `SliceDomPFunctor.compatible_iff` (dot notation through
  `toSliceDomPFunctor`).
- Produces:
  - `def SlicePFunctor.FreeM (v : Y → I) (F : SlicePFunctor I I)`
    `(i : I) := { w : (translate v F).W // (translate v F).wIndex w = i }`.
  - `def SlicePFunctor.FreeM.pure {v : Y → I} {F} {i}`
    `(a : { y : Y // v y = i }) : FreeM v F i` — the subtype pair of
    `W.mk ⟨⟨Sum.inl a.1, fun e => e.elim⟩, funext fun e => e.elim⟩`
    with fiber proof by `wIndex_mk` then `a.2`.
  - `def SlicePFunctor.FreeM.node {v : Y → I} {F} (a : F.A)`
    `(c : (b : F.B a) → FreeM v F (F.rCurried a b)) : FreeM v F (F.q a)`
    — the subtype pair of
    `W.mk ⟨⟨Sum.inr a, fun b => (c b).1⟩, _⟩` where the compatibility
    is `(compatible_iff …).mpr fun b => (c b).2` (children's fiber
    proofs), and the fiber proof is `wIndex_mk` then `translate_q_inr`.
  - `@[simp] theorem SlicePFunctor.FreeM.val_pure` and
    `val_node` — the underlying-tree characterizations (`(pure a).1 =
    W.mk …`, `(node a c).1 = W.mk …`), each `rfl`, named
    projection-first per the mathlib convention (`Fin.val_mk`
    precedent); these are the constructor-level lemmas later tasks
    rewrite with.

**Steps:**

- [ ] **Step 1: Write the failing test.** With the toy translate
  functor from Task B.3's test: build `FreeM.pure ⟨true, rfl⟩` and a
  `FreeM.node` with leaf children; assert their `.2` fiber properties
  and the `val_pure`/`val_node` equations by `simp`/`rfl`.
- [ ] **Step 2: Run to verify it fails.** Run
  `lake build GebLeanTests.SliceW.FreeM`. Expected: failure, `FreeM`
  not found.
- [ ] **Step 3: Implement** the three definitions and two lemmas, one
  at a time; module docstring cites Gambino–Kock 2013 (free monad as
  the W-type of the translation).
- [ ] **Step 4: Run to verify it passes.** Run
  `lake build GebLeanTests.SliceW.FreeM`. Expected: success.
- [ ] **Step 5: Gate.** Run `bash scripts/pre-commit.sh`.
- [ ] **Step 6: Commit.**

```bash
jj commit -m "feat(slicew): add the free-monad carrier and constructors"
```

## Task B.5: `FreeM.bind` and its computation rules

**Files:**

- Modify: `GebLean/SliceW/FreeM.lean`
- Modify: `GebLeanTests/SliceW/FreeM.lean`

**Interfaces:**

- Consumes: Task B.4's declarations; `W.elim`, `W.elim_mk`,
  `W.comp_elim` (vendored stack).
- Produces (leaf families `v : Y → I`, `v' : Y' → I` throughout — the
  target family has its own leaf type):
  - `def SlicePFunctor.FreeM.bindW {v : Y → I} {v' : Y' → I} {F}`
    `(f : ∀ j, { a : Y // v a = j } → FreeM v' F j) :`
    `(translate v F).W → (translate v' F).W` — a single
    `W.elim (translate v F) ((translate v' F).W) (translate v' F).wIndex g hg`
    where `g` splits the node's shape:
    at `⟨⟨Sum.inl y, _⟩, _⟩` return `(f (v y) ⟨y, rfl⟩).1`; at
    `⟨⟨Sum.inr a, c⟩, hc⟩` return
    `W.mk ⟨⟨Sum.inr a, c⟩, hc'⟩` where `hc'` re-reads `hc` as
    compatibility for `translate v' F` (`B` and `r` agree at `Sum.inr`
    by `translate_B_inr` / `translate_r_inr`; expect this to be
    definitional, else pointwise via `compatible_iff`); `hg` by
    `funext` and the same split — leaf: `(f (v y) ⟨y, rfl⟩).2`; node:
    `wIndex_mk`.
  - `def SlicePFunctor.FreeM.bind {v : Y → I} {v' : Y' → I} {F} {i}`
    `(t : FreeM v F i)`
    `(f : ∀ j, { a : Y // v a = j } → FreeM v' F j) : FreeM v' F i` —
    `⟨bindW f t.1, _⟩` with the fiber proof from
    `congrFun (W.comp_elim …) t.1` (the `wIndex`-preservation of the
    fold) transported along `t.2`.
  - `theorem SlicePFunctor.FreeM.pure_bind {v : Y → I} {v' : Y' → I}`
    `{F} {i} (a : { y : Y // v y = i }) (f) :`
    `(FreeM.pure a).bind f = f i a` — by
    `obtain ⟨y, hy⟩ := a; subst hy`, then `Subtype.ext` and the
    `W.elim_mk` computation at the leaf shape (expected `rfl` after
    the subst).
  - `theorem SlicePFunctor.FreeM.bind_node {v : Y → I} {v' : Y' → I}`
    `{F} (a : F.A) (c) (f) :`
    `(FreeM.node a c).bind f = FreeM.node a (fun b => (c b).bind f)` —
    `Subtype.ext`, `W.elim_mk` at the node shape, then `congrArg` on
    the children family.

  Neither computation rule is `@[simp]` (operation-level; Phase A
  policy).

**Steps:**

- [ ] **Step 1: Write the failing test.** On the toy signature:
  substitute a leaf into a one-node tree and assert the result equals
  the expected tree by rewriting with `pure_bind` and `bind_node`
  only (no kernel reduction of trees).
- [ ] **Step 2: Run to verify it fails.** Run
  `lake build GebLeanTests.SliceW.FreeM`. Expected: failure, `bind`
  not found.
- [ ] **Step 3: Implement** `bindW`, `bind`, `pure_bind`, `bind_node`,
  one at a time.
- [ ] **Step 4: Run to verify it passes.** Run
  `lake build GebLeanTests.SliceW.FreeM`. Expected: success.
- [ ] **Step 5: Gate.** Run `bash scripts/pre-commit.sh`.
- [ ] **Step 6: Commit.**

```bash
jj commit -m "feat(slicew): add free-monad bind with computation rules"
```

## Task B.6: free-monad laws and transport lemmas

**Files:**

- Modify: `GebLean/SliceW/FreeM.lean`
- Modify: `GebLeanTests/SliceW/FreeM.lean`

**Interfaces:**

- Consumes: Tasks B.4–B.5; `W.induction` (vendored stack).
- Produces:
  - `theorem SlicePFunctor.FreeM.bindW_pure {v : Y → I} {F}`
    `(z : (translate v F).W) :`
    `bindW (fun _ a => FreeM.pure a) z = z` — by `W.induction` with a
    `Sum` shape split: leaf nodes reduce to the `pure` tree (children
    families into `PEmpty` are equal by `funext` + elimination); node
    case by `congrArg` with the induction hypotheses (the
    `Sigma.ext rfl (heq_of_eq …)` closing shape of Phase A).
  - `theorem SlicePFunctor.FreeM.bind_pure {v : Y → I} {F} {i}`
    `(t : FreeM v F i) : t.bind (fun _ a => FreeM.pure a) = t` —
    `Subtype.ext (bindW_pure t.1)`.
  - `theorem SlicePFunctor.FreeM.bindW_bindW {v : Y → I} {v' : Y' → I}`
    `{v'' : Y'' → I} {F} (f : ∀ j, { a : Y // v a = j } → FreeM v' F j)`
    `(g : ∀ j, { b : Y' // v' b = j } → FreeM v'' F j)`
    `(z : (translate v F).W) :`
    `bindW g (bindW f z) = bindW (fun j a => (f j a).bind g) z` — by
    `W.induction` with the shape split: leaf reduces both sides to
    `((f (v y) ⟨y, rfl⟩).bind g).1`; node by `congrArg` with the
    induction hypotheses.
  - `theorem SlicePFunctor.FreeM.bind_assoc {v : Y → I} {v' : Y' → I}`
    `{v'' : Y'' → I} {F} {i} (t : FreeM v F i) (f) (g) :`
    `(t.bind f).bind g = t.bind (fun j a => (f j a).bind g)` —
    `Subtype.ext (bindW_bindW f g t.1)`.
  - `theorem SlicePFunctor.FreeM.pure_transport {v : Y → I} {F}`
    `{i i' : I} (h : i = i') (y : Y) (hy : v y = i) :`
    `h ▸ (FreeM.pure ⟨y, hy⟩ : FreeM v F i) = FreeM.pure ⟨y, hy.trans h⟩`
    — by `subst h; rfl`.
  - `theorem SlicePFunctor.FreeM.bind_transport {v : Y → I}`
    `{v' : Y' → I} {F} {i i' : I} (h : i = i') (t : FreeM v F i) (f) :`
    `(h ▸ t).bind f = h ▸ (t.bind f)` — by `subst h; rfl`.

**Steps:**

- [ ] **Step 1: Write the failing test.** Assert `bind_pure` and
  `bind_assoc` instances on the Task B.5 sample trees (statement-level
  `example`s applying the theorems, not tree computation).
- [ ] **Step 2: Run to verify it fails.** Run
  `lake build GebLeanTests.SliceW.FreeM`. Expected: failure, law names
  not found.
- [ ] **Step 3: Implement** the six lemmas in the order above (raw
  `bindW` lemmas first, wrapped forms second, transports last).
- [ ] **Step 4: Run to verify it passes.** Run
  `lake build GebLeanTests.SliceW.FreeM`. Expected: success.
- [ ] **Step 5: Gate.** Run `bash scripts/pre-commit.sh`.
- [ ] **Step 6: Commit.**

```bash
jj commit -m "feat(slicew): prove the free-monad laws and transport lemmas"
```

## Task B.7: the augmentation isomorphism and `polyFreeMSliceEquiv`

**Files:**

- Create: `GebLean/PolyBridge/FreeMEquiv.lean`
- Create: `GebLeanTests/PolyBridge/FreeMEquiv.lean`
- Modify: `GebLean/PolyBridge.lean` (`import` this module)
- Modify: `GebLeanTests.lean` (add
  `import GebLeanTests.PolyBridge.FreeMEquiv`)

**Interfaces:**

- Consumes: `SlicePFunctor.Iso`, `Iso.wEquivFiber` (Task B.2);
  `translate` (Task B.3); `FreeM` (Task B.4); `toSlice`, `toSlice_*`
  (Phase A); `polyFixSliceEquiv` (Phase A); `polyTranslate`,
  `polyTranslateIndex`, `polyTranslateFamily`, `overEmpty`,
  `PolyFreeM` (`GebLean/PolyAlg.lean`); the mathlib equivalences
  `Equiv.sigmaSumDistrib`
  (`(Σ i, α i ⊕ β i) ≃ (Σ i, α i) ⊕ (Σ i, β i)`), `Equiv.sumCongr`,
  and `Equiv.sigmaFiberEquiv` (`(Σ y, { x // f x = y }) ≃ α`) — all
  three verified present in this checkout
  (`Mathlib/Logic/Equiv/Sum.lean`); do not use
  `Equiv.sumSigmaDistrib` (the sigma-indexed-by-a-sum variant, which
  does not fit).
- Produces:
  - `def translateSliceIso {X : Type u} (V : Over X) (P : PolyEndo X) :`
    `SlicePFunctor.Iso (toSlice (polyTranslate V P))`
    `(SlicePFunctor.translate V.hom (toSlice P))` — shapes:
    `Σ x, ({ a : V.left // V.hom a = x } ⊕ polyBetweenIndex X X P x)`
    `≃ V.left ⊕ Σ x, polyBetweenIndex X X P x` (distribute the sigma
    over the sum, contract `Σ x, { a // V.hom a = x } ≃ V.left`);
    positions: `PEmpty ≃ PEmpty` at leaves (identity), identity at
    nodes; `q_comm`: definitional at nodes and at leaf positions, by
    the leaf's stored fiber witness at leaf shapes; `r_comm`:
    definitional at nodes, vacuous at leaves (`PEmpty` positions).
  - `def polyFreeMSliceEquiv {X : Type u} (V : Over X) (P : PolyEndo X)`
    `(x : X) : PolyFreeM V P x ≃ SlicePFunctor.FreeM V.hom (toSlice P) x`
    — `(polyFixSliceEquiv (polyTranslate V P) x).trans`
    `((translateSliceIso V P).wEquivFiber x)` (the second leg lands in
    the `FreeM` subtype definitionally; insert an `Equiv.cast`-free
    `show`/`change` re-typing if the elaborator needs the `FreeM`
    name).

**Steps:**

- [ ] **Step 1: Write the failing test.** For `natAlgSig.polyEndo`
  with a two-element variable family over `PUnit`, assert the round
  trip `(polyFreeMSliceEquiv …).symm ((polyFreeMSliceEquiv …) t) = t`
  on a small `polyFreeMPure` tree, via `Equiv.symm_apply_apply`.
- [ ] **Step 2: Run to verify it fails.** Run
  `lake build GebLeanTests.PolyBridge.FreeMEquiv`. Expected: failure,
  names not found.
- [ ] **Step 3: Implement `translateSliceIso`.** Compose the shape
  equivalence as `Equiv.sigmaSumDistrib` followed by
  `Equiv.sumCongr (Equiv.sigmaFiberEquiv V.hom) (Equiv.refl _)` (or
  write the explicit `toFun`/`invFun` pair if the composite's
  definitional behaviour obstructs the later `q_comm`/`r_comm`
  proofs; both directions are `rfl`-inverse case splits). Prove
  `q_comm`/`r_comm` by shape split.
- [ ] **Step 4: Implement `polyFreeMSliceEquiv`** as the two-leg
  composite.
- [ ] **Step 5: Run to verify it passes.** Run
  `lake build GebLeanTests.PolyBridge.FreeMEquiv`. Expected: success.
- [ ] **Step 6: Gate.** Run `bash scripts/pre-commit.sh`.
- [ ] **Step 7: Commit.**

```bash
jj commit -m "feat(polybridge): relate the legacy free monad to the slice free monad"
```

## Task B.8: bridge naturality (`pure`, `node`, `bind`)

**Files:**

- Modify: `GebLean/PolyBridge/FreeMEquiv.lean`
- Modify: `GebLeanTests/PolyBridge/FreeMEquiv.lean`

**Interfaces:**

- Consumes: Task B.7; `polyFixSliceEquiv_mk` (Phase A);
  `Iso.wMap_mk` (Task B.2); `FreeM.pure`/`node`/`bind`,
  `pure_bind`, `bind_node` (Tasks B.4–B.5); `polyFreeMPure`,
  `polyFreeMBind`, `PolyFix.ind` (`GebLean/PolyAlg.lean`).
- Produces (none `@[simp]`; operation-level):
  - `theorem polyFreeMSliceEquiv_transport (V P) {x x' : X}`
    `(h : x = x') (t : PolyFreeM V P x) :`
    `polyFreeMSliceEquiv V P x' (h ▸ t) = h ▸ polyFreeMSliceEquiv V P x t`
    — by `subst h; rfl` (the transport-naturality of the equivalence,
    mirroring Phase A's `toSliceW_transport`; consumed by Task B.10's
    `tmSliceEquiv_subst`).
  - `theorem polyFreeMSliceEquiv_pure (V P x)`
    `(a : { v : V.left // V.hom v = x }) :`
    `polyFreeMSliceEquiv V P x (polyFreeMPure V P a) = FreeM.pure a` —
    unfold the two legs on the leaf node: `polyFixSliceEquiv_mk` then
    `Iso.wMap_mk` at the leaf shape; close with `Subtype.ext` and a
    `funext` on `PEmpty` children.
  - `theorem polyFreeMSliceEquiv_node (V P x)`
    `(p : polyBetweenIndex X X P x) (ch) :`
    `polyFreeMSliceEquiv V P x (PolyFix.mk x (Sum.inr p) ch) =`
    `FreeM.node ⟨x, p⟩ (fun e => polyFreeMSliceEquiv V P _ (ch e))` —
    same two-lemma unfolding at the node shape.
  - `theorem polyFreeMSliceEquiv_bind (V B P x) (t : PolyFreeM V P x)`
    `(f : ∀ y, { a : V.left // V.hom a = y } → PolyFreeM B P y) :`
    `polyFreeMSliceEquiv B P x (polyFreeMBind V B P t f) =`
    `(polyFreeMSliceEquiv V P x t).bind`
    `(fun y a => polyFreeMSliceEquiv B P y (f y a))` — by
    `PolyFix.ind` on `t`: the leaf case is
    `polyFreeMSliceEquiv_pure` + `FreeM.pure_bind`; the node case is
    `polyFreeMSliceEquiv_node` + `FreeM.bind_node` + the induction
    hypotheses under `congrArg`.

**Steps:**

- [ ] **Step 1: Write the failing test.** `example`s applying each
  naturality lemma at the Task B.7 sample data.
- [ ] **Step 2: Run to verify it fails.** Run
  `lake build GebLeanTests.PolyBridge.FreeMEquiv`. Expected: failure.
- [ ] **Step 3: Implement** the four lemmas in order (transport
  first; each later lemma consumes earlier ones).
- [ ] **Step 4: Run to verify it passes.** Run
  `lake build GebLeanTests.PolyBridge.FreeMEquiv`. Expected: success.
- [ ] **Step 5: Gate.** Run `bash scripts/pre-commit.sh`.
- [ ] **Step 6: Commit.**

```bash
jj commit -m "feat(polybridge): prove free-monad naturality across the bridge"
```

## Task B.9: the `Tm'` term layer with clone laws

**Files:**

- Create: `GebLean/Ramified/Polynomial/Term.lean`
- Create: `GebLeanTests/Ramified/Polynomial/Term.lean`
- Modify: `GebLean/Ramified/Polynomial.lean` (`import` this module)
- Modify: `GebLeanTests/Ramified/Polynomial.lean` (`import` the test)

**Interfaces:**

- Consumes: `FreeM` and all Task B.4–B.6 declarations; `toSlice`
  (Phase A); `SortedSig`, `SortedSig.polyEndo`, `Ctx`, `varOver`
  (`GebLean/Ramified/{SortedSig,Term}.lean`).
- Produces (all mirroring `GebLean/Ramified/Term.lean` signatures):
  - `def Tm' (sig : SortedSig S) (Γ : Ctx S) : S → Type :=`
    `SlicePFunctor.FreeM Γ.get (toSlice sig.polyEndo)`.
  - `def Tm'.var {sig} {Γ} (i : Fin Γ.length) : Tm' sig Γ (Γ.get i) :=`
    `SlicePFunctor.FreeM.pure ⟨i, rfl⟩`.
  - `def Tm'.op {sig} {Γ} (o : sig.Op)`
    `(args : ∀ i : Fin (sig.arity o).length, Tm' sig Γ ((sig.arity o).get i)) :`
    `Tm' sig Γ (sig.result o) :=`
    `SlicePFunctor.FreeM.node ⟨sig.result o, ⟨o, rfl⟩⟩ args` (the
    shape of `toSlice sig.polyEndo` at the result sort; `args`
    coerces along the definitional `B`/`rCurried` unfoldings — insert
    a `show`/`change` re-typing if needed).
  - `def Tm'.subst {sig} {Γ Δ} {s} (t : Tm' sig Γ s)`
    `(σ : ∀ i : Fin Γ.length, Tm' sig Δ (Γ.get i)) : Tm' sig Δ s :=`
    `t.bind (fun _ a => a.2 ▸ σ a.1)`.
  - `def Tm'.reind` (`h ▸ t`), `@[simp] theorem Tm'.reind_rfl`,
    `def Tm'.weaken` — verbatim mirrors of the legacy forms.
  - `theorem Tm'.var_subst (i) (σ) : (Tm'.var i).subst σ = σ i` — from
    `FreeM.pure_bind` (the transport at `rfl` vanishes).
  - `theorem Tm'.subst_id (t) : t.subst Tm'.var = t` — mirror of the
    legacy proof: reduce to `FreeM.bind_pure` after rewriting the leaf
    function with `FreeM.pure_transport` (`congr 1; funext y a;`
    `obtain ⟨v, hv⟩ := a; exact FreeM.pure_transport …`).
  - `theorem Tm'.subst_subst (t) (σ) (τ) :`
    `(t.subst σ).subst τ = t.subst (fun i => (σ i).subst τ)` — mirror
    of the legacy proof via `FreeM.bind_assoc` and
    `FreeM.bind_transport`.
  - `theorem Tm'.subst_reind` — `subst h; rfl` mirror.

**Steps:**

- [ ] **Step 1: Write the failing test.** Define a two-sorted toy
  signature in the test file (`SortedSig Bool`, one operation per
  sort with mixed-arity arguments), a two-entry context, and assert:
  `Tm'.var_subst` at each position, one `Tm'.subst_id` instance, and
  one `Tm'.subst_subst` instance — all via the clone-law theorems.
- [ ] **Step 2: Run to verify it fails.** Run
  `lake build GebLeanTests.Ramified.Polynomial.Term`. Expected:
  failure, `Tm'` not found.
- [ ] **Step 3: Implement** the definitions in interface order, then
  the clone laws (module docstring cites Leivant 1999 section 2.1, as
  `GebLean/Ramified/Term.lean` does).
- [ ] **Step 4: Run to verify it passes.** Run
  `lake build GebLeanTests.Ramified.Polynomial.Term`. Expected:
  success.
- [ ] **Step 5: Gate.** Run `bash scripts/pre-commit.sh`.
- [ ] **Step 6: Commit.**

```bash
jj commit -m "feat(ramified): add the sorted term layer on the slice free monad"
```

## Task B.10: `tmSliceEquiv`, compatibility, and documentation

**Files:**

- Modify: `GebLean/Ramified/Polynomial/Term.lean`
- Modify: `GebLeanTests/Ramified/Polynomial/Term.lean`
- Modify: `docs/areas/polynomial-functors.md` (add `GebLean/SliceW/`
  and `PolyBridge/FreeMEquiv.lean` to the area inventory)
- Modify: `docs/areas/ramified-recurrence.md` (add
  `GebLean/Ramified/Polynomial/Term.lean`)

**Interfaces:**

- Consumes: Task B.9; `polyFreeMSliceEquiv` and the three naturality
  lemmas (Tasks B.7–B.8); `Tm`, `Tm.var`, `Tm.op`, `Tm.subst`
  (`GebLean/Ramified/Term.lean`).
- Produces:
  - `def tmSliceEquiv {sig} (Γ : Ctx S) (s : S) :`
    `Tm' sig Γ s ≃ Tm sig Γ s :=`
    `(polyFreeMSliceEquiv (varOver Γ) sig.polyEndo s).symm` (the
    `.symm` re-orients the bridge so the primed carrier is the
    source; `(varOver Γ).hom = Γ.get` definitionally).
  - `theorem tmSliceEquiv_var (i) :`
    `tmSliceEquiv Γ _ (Tm'.var i) = Tm.var i` — from
    `polyFreeMSliceEquiv_pure` via the equivalence laws
    (`Equiv.symm_apply_eq`, as in Phase A's `freeAlgSliceEquiv_mk`
    derivation).
  - `theorem tmSliceEquiv_op (o) (args) :`
    `tmSliceEquiv Γ _ (Tm'.op o args) =`
    `Tm.op o (fun i => tmSliceEquiv Γ _ (args i))` — from
    `polyFreeMSliceEquiv_node` the same way.
  - `theorem tmSliceEquiv_subst (t) (σ) :`
    `tmSliceEquiv Γ _ (t.subst σ) =`
    `(tmSliceEquiv Γ _ t).subst (fun i => tmSliceEquiv Γ _ (σ i))` —
    from `polyFreeMSliceEquiv_bind` via the equivalence laws, moving
    the leaf-function transport with `polyFreeMSliceEquiv_transport`
    (Task B.8) — the legacy and primed leaf functions both transport
    by `a.2 ▸ σ a.1`, and the transport must be commuted past the
    equivalence to match them.
- None of the three are `@[simp]`.

**Steps:**

- [ ] **Step 1: Write the failing test.** On the Task B.9 toy
  signature: assert `tmSliceEquiv_var`, `tmSliceEquiv_op`, and one
  `tmSliceEquiv_subst` instance, plus one transported round trip
  `(tmSliceEquiv …).symm (tmSliceEquiv … t) = t`.
- [ ] **Step 2: Run to verify it fails.** Run
  `lake build GebLeanTests.Ramified.Polynomial.Term`. Expected:
  failure, `tmSliceEquiv` not found.
- [ ] **Step 3: Implement** the equivalence and the three lemmas.
- [ ] **Step 4: Update the two area documents**; run
  `doctoc --update-only docs/` and
  `markdownlint-cli2 'docs/**/*.md'` on the touched files.
- [ ] **Step 5: Run to verify it passes.** Run
  `lake build GebLeanTests.Ramified.Polynomial.Term` and `lake test`.
  Expected: success.
- [ ] **Step 6: Gate.** Run `bash scripts/pre-commit.sh`.
- [ ] **Step 7: Commit.**

```bash
jj commit -m "feat(ramified): relate the primed term layer to Tm and document it"
```

## Task B.11: whole-branch verification

- [ ] **Step 1:** Run `bash scripts/pre-push.sh`. Expected: every
  stage passes (Lean triad, markdownlint, doctoc, axiom-linter test).
- [ ] **Step 2:** Whole-branch review per
  superpowers:requesting-code-review against the design document;
  address findings; re-run the gate after any change.
- [ ] **Step 3:** Hand off to the user for the push / PR decision (no
  `jj git push` without user line-by-line review).
